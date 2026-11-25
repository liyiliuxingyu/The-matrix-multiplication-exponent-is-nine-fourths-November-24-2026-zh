-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Travel
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Answer
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary

/-!
# 在每个宿主上一次性计算还原掩码

**英文原文**

Computing the restoration masks once per host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Neighborhood

-- 读法：在后续公式中，`Raw` 是 `Format.pair (Rows m d) (.vec m (Group.Flags d))` 的缩写。
abbrev Raw (m d : ℕ) := Format.pair (Rows m d) (.vec m (Group.Flags d))

variable {m d t : ℕ}

-- 读法：`inspect` 的取值由 `let walk := walks 2 r.1 v (fun i j => decide (walk i = walk j), fun i => r.2 (walk i))` 给出。
def inspect (r : (Raw m d).obj) (v : B m) : (Preview d).obj :=
  let walk := walks 2 r.1 v
  (fun i j => decide (walk i = walk j), fun i => r.2 (walk i))

-- 读法：`(Group.Flags d).width` 等于 `2 ^ (d + 1)`。
private theorem flags_width : (Group.Flags d).width = 2 ^ (d + 1) := by
  rw [Group.Flags, Format.width_vec, Format.width_pair, Format.width_bit, pow_succ]

-- 读法：`m ≤ t` 与 `2 ^ d ≤ t ∧ (Group.Flags d).width ≤ t` 同时成立。
private theorem scales (h : m + 2 ^ radius d ≤ t) : m ≤ t ∧ 2 ^ d ≤ t ∧ (Group.Flags d).width ≤ t := by
  have hh : 2 ^ (d + 1) ≤ t := (Nat.pow_le_pow_right (by decide : 0 < 2) (show d + 1 ≤ radius d by unfold radius; omega)).trans
    ((Nat.le_add_left _ _).trans h)
  rw [flags_width]
  exact ⟨(Nat.le_add_right _ _).trans h, (Nat.pow_le_pow_right (by decide) (by omega)).trans hh, hh⟩

-- 读法：`(Raw m d).width` 不超过 `2 ^ m * (100 + t) ^ 3`。这里调用 `Nat.mul_le_mul_left`。
theorem rawWidth (h : m + 2 ^ radius d ≤ t) : (Raw m d).width ≤ 2 ^ m * (100 + t) ^ 3 := by
  obtain ⟨hm, hd, hf⟩ := scales h
  simp only [Raw, Format.width_pair, Format.width_vec, Neighborhood.Rows, Format.width_addr, ← mul_add]
  apply Nat.mul_le_mul_left
  rw [Format.width_bit]
  have := Nat.mul_le_mul hd hm
  ring_nf at this ⊢
  omega

variable (F : Type) [Field F]

-- 读法：映射 `inspect` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (m) * (100 + (t)) ^ (60)` 为上界。
theorem cheap_preview (h : m + 2 ^ radius d ≤ t) :
    Cheap F m t (Raw m d) (.vec m (Preview d)) inspect 60 := by
  obtain ⟨hm, _, hf⟩ := scales h
  let q := radius d
  have hq : 2 ^ q ≤ t := (Nat.le_add_left _ _).trans h
  have base := Cheap.id F (rawWidth h)
  have route := base.fst.comp ((cheap_walks F m d 2 (by decide)).widen h)
  have bits := route.comp (cheap_equal F hm hq)
  have take := Cheap.lookup F m t (Group.Flags d) hm hf
  have all := Cheap.share _ (fun i => (base.snd.pair (route.comp (column F hm hq i))).comp take) hq
  let X := Format.vec q (.vec m (Group.Flags d))
  let Y := Format.vec m (.vec q (Group.Flags d))
  -- 推导：记下中间结论 `hb`：`Y.width ≤ 2 ^ m * (100 + t) ^ 2`。
  have hb : Y.width ≤ 2 ^ m * (100 + t) ^ 2 := by
    rw [show Y.width = 2 ^ m * (2 ^ q * (Group.Flags d).width) by unfold Y; rw [Format.width_vec, Format.width_vec]]
    apply Nat.mul_le_mul_left
    nlinarith only [Nat.mul_le_mul hq hf]
  have hc : X.width = Y.width := by simp only [X, Y, Format.width_vec]; ring
  have copy : Cheap F m t X Y (fun a x i => a i x) 3 :=
    Cheap.project F (hc.le.trans hb) hb (fun z => (z.2.1, z.1, z.2.2)) fun _ _ => rfl
  exact (bits.pair (all.comp copy)).zip.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 由掩码与邻近字母提取相匹配的视图

**英文原文**

Extracting a matched view from the masks and nearby letters
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
local notation "d" => D.scheme.d

-- 读法：在后续公式中，`Letters` 是 `Window.Walks 2 d (.addr A.ℓ)` 的缩写。
abbrev Letters := Window.Walks 2 d (.addr A.ℓ)
-- 读法：在后续公式中，`Question` 是 `Format.pair .bit (.pair (Preview d) (Letters A))` 的缩写。
abbrev Question := Format.pair .bit (.pair (Preview d) (Letters A))

-- 读法：`query` 的取值由 `(D.live raw.1 v, preview D raw.1 v, (Window.reads 2 (A.rows raw) v).2 k)` 给出。
def query (raw : A.format.obj) (v : B D.scheme.m) (k : B D.scheme.h) : (Question A).obj :=
  (D.live raw.1 v, preview D raw.1 v, (Window.reads 2 (A.rows raw) v).2 k)

namespace Data
variable {A} {N r s u : ℕ} {a b : Wire} (X Y : Data A N r s u a b)
  {v : X.G.V} {w : Y.G.V} {k : Cell D.scheme.h}

-- 读法：在后续公式中，`word` 是 `query A X.raw (X.host v) (cellIndex _ k)` 的缩写。
abbrev word (v : X.G.V) (k : Cell D.scheme.h) := query A X.raw (X.host v) (cellIndex _ k)

-- 读法：`(X.word v k).2.2 (address i none)` 等于 `X.letter (hop X.q.core v i) k`。
theorem letter_at (i : Option (B d)) :
    (X.word v k).2.2 (address i none) = X.letter (hop X.q.core v i) k := by
  change X.raw.2 (Neighborhood.walks 2 (D.nav X.raw.1) (X.host v) (address i none)) _ = _
  rw [follows]; rfl

-- 读法：要证明的命题是 `Agree X.q.core Y.q.core v w`。
theorem agree_at (hh : X.word v k = Y.word w k) : Agree X.q.core Y.q.core v w :=
  agree _ _ _ _ (congrArg (fun t => t.2.1) hh)

-- 读法：用字段 `sees`、`self`、`nav`、`letter` 构造 `X.View Y v w k`。
def observe (hh : X.word v k = Y.word w k) : X.View Y v w k where
  sees x y := ∃ i, hop X.q.core v i = x ∧ hop Y.q.core w i = y
  self := ⟨none, rfl, rfl⟩
  nav j := ⟨some j, rfl, rfl⟩
  letter := by
    rintro _ _ ⟨i, rfl, rfl⟩
    rw [← X.letter_at, ← Y.letter_at, hh]
  labels := by
    rintro _ _ ⟨i, rfl, rfl⟩ j
    exact (X.agree_at Y hh).code X.q.full i i (some j)
  pair := by
    rintro _ _ _ _ ⟨i, rfl, rfl⟩ ⟨j, rfl, rfl⟩
    exact (X.agree_at Y hh).pair X.q.full i j

end Data
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 为还原后的邻居作规范编号

邻居由一条父宿主信道及另一父宿主硬件中的一个后缀指定，其中信道允许停留原地。在至多四个实际邻居所对应的有序对中求各对的序号。

**英文原文**

Canonical numbering of restored neighbors

A neighbor is described by a parent channel, possibly stationary,
and the suffix in the other parent's hardware. Rank these pairs
inside the set of at most four actual neighbors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)
local notation "W" => Tether.width N r s
local notation "Z" => Tether.Host Unit r s W

-- 读法：在后续公式中，`parent` 是 `(cells v).1` 的缩写。
abbrev parent (v : X.e.Space) := (cells v).1
-- 读法：在后续公式中，`seatAt` 是 `(cells v).2` 的缩写。
abbrev seatAt (v : X.e.Space) := (cells v).2
-- 读法：在后续公式中，`child` 是 `cells.symm (v, t)` 的缩写。
abbrev child (v : X.G.V) (t : Z) : X.e.Space := cells.symm (v, t)
-- 读法：在后续公式中，`shell` 是 `X.e.adj v` 的缩写。
abbrev shell (v : X.e.Space) := X.e.adj v

-- 读法：`X.parent (X.child v t)` 等于 `v`。
theorem child_parent (v : X.G.V) (t : Z) : X.parent (X.child v t) = v :=
  congrArg Prod.fst (cells.apply_symm_apply (v, t))

-- 读法：`X.seatAt (X.child v t)` 等于 `t`。
theorem child_seat (v : X.G.V) (t : Z) : X.seatAt (X.child v t) = t :=
  congrArg Prod.snd (cells.apply_symm_apply (v, t))

-- 读法：`X.child (X.parent v) (X.seatAt v)` 等于 `v`。使用 `cells.symm_apply_apply` 给出的结论。
theorem eq_child (v : X.e.Space) : X.child (X.parent v) (X.seatAt v) = v := cells.symm_apply_apply _

-- 读法：`X.parent y` 属于 `insert (X.parent v) (X.G.N (X.parent v))`。
theorem project_edge {v y : X.e.Space} (h : y ∈ X.shell v) :
    X.parent y ∈ insert (X.parent v) (X.G.N (X.parent v)) :=
  project X.q.chart X.G.ns X.e.degree X.G.sub h

-- 读法：在后续公式中，`Key` 是 `Option (B d) × B t` 的缩写。
abbrev Key (d t : ℕ) := Option (B d) × B t

-- 读法：`key` 的取值由 `(X.q.chart.label (X.parent v) (X.parent y), suffix r s W (X.seatAt y))` 给出。
def key (v y : X.e.Space) : Key D.scheme.d (bits r s W) :=
  (X.q.chart.label (X.parent v) (X.parent y), suffix r s W (X.seatAt y))

-- 读法：用字段 `toFun`、`inj'`、`obtain`、`have` 构造 `↥(X.shell v) ↪ Key D.scheme.d (bits r s W)`。
def keys (v : X.e.Space) : ↥(X.shell v) ↪ Key D.scheme.d (bits r s W) where
  toFun y := X.key v y
  inj' y z he := by
    obtain ⟨hh, hr⟩ := Prod.mk.inj he
    have eq := X.q.chart.inj _ (X.project_edge y.property) (X.project_edge z.property) hh
    exact Subtype.ext (cells.injective (Prod.ext eq ((suffix ..).injective hr)))

-- 读法：`rank` 的结果类型为 `↥(X.shell v) ↪ B 3`。
def rank (v : X.e.Space) : ↥(X.shell v) ↪ B 3 :=
  History.Reset.rank (X.keys v) (by
    rw [Fintype.card_coe]; exact (Tether.adj_degree X.e.sw X.G.C X.core v).trans (by decide : 4 ≤ 2 ^ 3))

-- 读法：当 `h : w ∈ X.shell v` 成立时取 `X.rank v ⟨w, h⟩`，否则取 `0`。
def index (v w : X.e.Space) := if h : w ∈ X.shell v then X.rank v ⟨w, h⟩ else 0

-- 读法：`hop X.q.core (X.parent v) (X.key v w).1` 等于 `X.parent w`。这里调用 `History.Reset.label_spec`。
theorem decode {v w : X.e.Space} (h : w ∈ X.shell v) :
    hop X.q.core (X.parent v) (X.key v w).1 = X.parent w := by
  apply History.Reset.label_spec
  rcases mem_insert.mp (X.project_edge h) with he|he
  · exact .inl he
  right
  have hh : X.parent w ∈ D.adj X.G (X.parent v) := by simp [Template.adj, X.q.full, he]
  obtain ⟨j, hj, _⟩ := (X.q.core.edge _ _).mp hh
  exact ⟨j, X.host.injective ((X.q.core.host_nav _ _).trans hj)⟩

variable {X Y} {v : X.e.Space} {w : Y.e.Space}
    (h : Agree X.q.core Y.q.core (X.parent v) (Y.parent w))
    (eq : X.seatAt v = Y.seatAt w)

include h eq in
-- 读法：存在 `t : ↥(Y.shell w)`，`X.keys v z` 等于 `Y.keys w t`。
theorem neighbors (z : ↥(X.shell v)) : ∃ t : ↥(Y.shell w), X.keys v z = Y.keys w t := by
  let j := (X.key v z.val).1
  let w' := hop Y.q.core (Y.parent w) j
  let t := Y.child w' (X.seatAt z.val)
  have hv : hop X.q.core (X.parent v) j = X.parent z.val := X.decode z.property
  have l := h.pair X.q.full none j
  have l' := h.pair X.q.full j none
  have c := h.core none j
  rw [hv] at l l' c
  have mem := links_eq X.q.chart X.G.ns X.e.degree Y.q.chart Y.G.ns Y.e.degree l l' c
    (X.seatAt v) (X.seatAt z.val)
  change X.child (X.parent z.val) (X.seatAt z.val) ∈ X.shell (X.child (X.parent v) (X.seatAt v)) ↔
    t ∈ Y.shell (Y.child (Y.parent w) (X.seatAt v)) at mem
  rw [X.eq_child, X.eq_child, eq, Y.eq_child] at mem
  refine ⟨⟨t, mem.mp z.property⟩, ?_⟩
  change X.key v z.val = Y.key w t
  unfold key t
  rw [Y.child_parent, Y.child_seat]
  exact Prod.ext l.label rfl

include h eq in
-- 读法：`X.index v z` 等于 `Y.index w t`。这里调用 `History.Reset.rank_eq`。
theorem index_eq {z : X.e.Space} {t : Y.e.Space} (hz : z ∈ X.shell v) (ht : t ∈ Y.shell w)
    (same : X.key v z = Y.key w t) : X.index v z = Y.index w t := by
  simp only [index, dite_eq_left hz, dite_eq_left ht]
  exact History.Reset.rank_eq (neighbors h eq) (neighbors h.symm eq.symm) same

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-!
# 为所有还原记录选取同一张响应表

**英文原文**

Choosing a single response table for all restored records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)
local notation "W" => Tether.width N r s
local notation "L" => bits r s W
local notation "m" => D.scheme.m
local notation "Z" => Tether.Host Unit r s W

-- 读法：在后续公式中，`hostOut` 是 `Restore.host X.host r s W` 的缩写。
abbrev hostOut := Restore.host X.host r s W

-- 读法：`directory` 的取值由 `Directory.numbered X.e.adj (Tether.adj_symm X.e.sw X.G.C X.G.cs) X.hostOut X.rank` 给出。
def directory : Directory X.e.adj (m + L) :=
  Directory.numbered X.e.adj (Tether.adj_symm X.e.sw X.G.C X.G.cs) X.hostOut X.rank

-- 读法：在后续公式中，`frame` 是 `display X.q X.e X.loopless X.directory` 的缩写。
abbrev frame := display X.q X.e X.loopless X.directory
-- 读法：在后续公式中，`pres` 是 `presents X.q X.e X.loopless X.directory` 的缩写。
abbrev pres := presents X.q X.e X.loopless X.directory
-- 读法：在后续公式中，`record` 是 `tape X.q X.e X.loopless X.directory` 的缩写。
abbrev record := tape X.q X.e X.loopless X.directory

-- 读法：`combine` 的取值由 `(Match.rowIndex m L).symm (i, j)` 给出。
def combine (i : B m) (j : B L) := (Match.rowIndex m L).symm (i, j)

-- 读法：`X.hostOut (X.child v j)` 等于 `combine (X.host v) (suffix r s W j)`。这里调用 `Match.rowIndex`。
theorem child_address (v : X.G.V) (j : Z) :
    X.hostOut (X.child v j) = combine (X.host v) (suffix r s W j) := by
  unfold combine
  apply (Match.rowIndex m L).eq_symm_apply.mpr
  rw [hostOut, host_parts, cells.apply_symm_apply]

-- 读法：`combine v j ∈ Set.range X.hostOut` 与 `D.live X.raw.1 v = true ∧ j ∈ Set.range (suffix r s W)` 等价。
theorem child_active (v : B m) (j : B L) :
    combine v j ∈ Set.range X.hostOut ↔ D.live X.raw.1 v = true ∧ j ∈ Set.range (suffix r s W) := by
  rw [X.q.core.live]
  constructor
  · rintro ⟨y, hy⟩
    rw [← X.eq_child y, X.child_address] at hy
    obtain ⟨hv, hj⟩ := Prod.mk.inj ((Match.rowIndex m L).symm.injective hy)
    exact ⟨⟨_, hv⟩, _, hj⟩
  · rintro ⟨⟨v, rfl⟩, ⟨j, rfl⟩⟩
    exact ⟨X.child v j, X.child_address ..⟩

-- 读法：`X.record v k` 等于 `Script.vacant A.scheme`。这里调用 `Function.extend_apply'`。
theorem record_idle (v : B (m + L)) (k : B D.scheme.h) (hv : v ∉ Set.range X.hostOut) :
    X.record v k = Script.vacant A.scheme := by
  have hh : (v, k, 0) ∉ Set.range (name X.e X.directory) := by
    rintro ⟨z, hz⟩; exact hv ⟨z.2, congrArg Prod.fst hz⟩
  exact Function.extend_apply' (dataAt X.q X.e X.loopless X.directory) (fun _ => Script.vacant A.scheme) _ hh

-- 读法：`X.directory.index` 等于 `X.index`。用函数外延性比较等号两侧在 `v w` 处的取值。
theorem directory_index : X.directory.index = X.index := by
  funext v w
  unfold directory Directory.numbered index
  dsimp only
  split_ifs <;> rfl

-- 读法：`X.record (combine (X.host v) (suffix r s W j)) (cellIndex _ k)` 等于 `X.f.encode X.p (fun i j => X.index i.2 j.2) (k, X.child v j)`。这里调用 `tape_at`。
theorem record_at (v : X.G.V) (j : Z) (k : Cell D.scheme.h) :
    X.record (combine (X.host v) (suffix r s W j)) (cellIndex _ k) =
    X.f.encode X.p (fun i j => X.index i.2 j.2) (k, X.child v j) := by
  rw [← X.child_address]
  rw [← X.directory_index]
  exact tape_at X.q X.e X.loopless X.directory (k, X.child v j)

-- 读法：`X.record (combine (X.host v) (suffix r s W j)) (cellIndex _ k)` 等于 `Y.record (combine (Y.host w) (suffix r s W j)) (cellIndex _ k)`。这里调用 `f.answer`。
theorem agree_record {v : X.G.V} {w : Y.G.V} (k : Cell D.scheme.h)
    (h : X.word v k = Y.word w k) (j : Z) :
    X.record (combine (X.host v) (suffix r s W j)) (cellIndex _ k) =
      Y.record (combine (Y.host w) (suffix r s W j)) (cellIndex _ k) := by
  rw [X.record_at, Y.record_at]
  let f := X.observe Y h
  have hx : X.home (k, X.child v j) = v := X.child_parent v j
  have hy : Y.home (k, Y.child w j) = w := Y.child_parent w j
  have eq : X.seatAt (X.child v j) = Y.seatAt (Y.child w j) := (X.child_seat ..).trans (Y.child_seat ..).symm
  have hs : f.sites (k, X.child v j) (k, Y.child w j) := ⟨rfl, rfl, by rw [hx, hy]; exact f.self, eq⟩
  apply f.answer _ _ hs hx
  intro z t ht ha hb
  have hc : Agree X.q.core Y.q.core (X.parent (X.child v j)) (Y.parent (Y.child w j)) := by
    rw [X.child_parent, Y.child_parent]; exact X.agree_at Y h
  exact index_eq hc eq ha hb (Prod.ext (f.pair _ _ _ _ hs.2.2.1 ht.2.2.1).label
    (congrArg (suffix r s W) ht.2.2.2))

-- 读法：`X.record (combine v j) k` 等于 `Y.record (combine w j) k`。按 `combine v j ∈ Set.range X.hostOut` 成立与否分情况。
theorem uniform {v w : B m} {k : B D.scheme.h} (h : query A X.raw v k = query A Y.raw w k) (j : B L) :
    X.record (combine v j) k = Y.record (combine w j) k := by
  have hh : D.live X.raw.1 v = D.live Y.raw.1 w := congrArg (fun t : (Question A).obj => t.1) h
  have hv : combine v j ∈ Set.range X.hostOut ↔ combine w j ∈ Set.range Y.hostOut := by
    rw [X.child_active, Y.child_active, hh]
  by_cases he : combine v j ∈ Set.range X.hostOut
  · obtain ⟨hl, i, rfl⟩ := (X.child_active ..).mp he
    obtain ⟨v, rfl⟩ := (X.q.core.live _).mp hl
    obtain ⟨w, rfl⟩ := (Y.q.core.live _).mp (hh.symm.trans hl)
    obtain ⟨k, rfl⟩ := (cellIndex _).surjective k
    exact X.agree_record Y k h i
  · rw [X.record_idle _ _ he, Y.record_idle _ _ (mt hv.mpr he)]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-!
# 新导航行的简短描述

**英文原文**

A short description of the new navigation rows
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X Y : Data A N r s u a b)
local notation "W" => Tether.width N r s
local notation "L" => bits r s W
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d

-- 读法：`Next` 表示以下条件：存在 `w`，`X.hostOut w = v` 与 `t ∈ X.shell w ∧ X.directory.index w t = i` 同时成立。
def Next (v : B (m + L)) (i : B 3) (t : X.e.Space) : Prop :=
  ∃ w, X.hostOut w = v ∧ t ∈ X.shell w ∧ X.directory.index w t = i

-- 读法：当 `h : ∃ y, X.Next v i y` 成立时取 `some (X.key h.choose_spec.choose h.choose)`，否则取 `none`。
def jump (v : B (m + L)) (i : B 3) : Option (Key d L) :=
  if h : ∃ y, X.Next v i y then some (X.key h.choose_spec.choose h.choose) else none

-- 读法：`X.jump (X.hostOut v) i` 等于 `some (X.key v w)`。
theorem next_eq {v w : X.e.Space} {i : B 3} (h : w ∈ X.shell v) (hi : X.index v w = i) :
    X.jump (X.hostOut v) i = some (X.key v w) := by
  have ht : ∃ y, X.Next (X.hostOut v) i y := ⟨w, v, rfl, h, by rw [X.directory_index, hi]⟩
  unfold jump
  rw [dite_eq_left ht]
  have hu := ht.choose_spec.choose_spec
  have hv := X.hostOut.injective hu.1
  rw [hv] at hu ⊢
  have he := hu.2.2.trans hi.symm
  rw [X.directory_index, index, index, dite_eq_left hu.2.1, dite_eq_left h] at he
  exact congrArg (fun w => some (X.key v w)) (congrArg Subtype.val ((X.rank v).injective he))

-- 读法：`X.jump (X.hostOut v) i` 等于 `Y.jump (Y.hostOut w) i`。
theorem jump_eq {v : X.e.Space} {w : Y.e.Space} (h : Agree X.q.core Y.q.core (X.parent v) (Y.parent w))
    (eq : X.seatAt v = Y.seatAt w) (i : B 3) : X.jump (X.hostOut v) i = Y.jump (Y.hostOut w) i := by
  have transfer (X Y : Data A N r s u a b) (v : X.e.Space) (w : Y.e.Space)
      (h : Agree X.q.core Y.q.core (X.parent v) (Y.parent w)) (eq : X.seatAt v = Y.seatAt w)
      (ht : ∃ t, X.Next (X.hostOut v) i t) : X.jump (X.hostOut v) i = Y.jump (Y.hostOut w) i := by
    obtain ⟨z, t, he, hz, hi⟩ := ht
    have := X.hostOut.injective he
    subst t
    rw [X.directory_index] at hi
    obtain ⟨t, ht⟩ := neighbors h eq ⟨z, hz⟩
    have hm := index_eq h eq hz t.property ht
    rw [X.next_eq hz hi, Y.next_eq t.property (hm.symm.trans hi)]
    exact congrArg some ht
  by_cases ha : ∃ t, X.Next (X.hostOut v) i t
  · exact transfer _ _ _ _ h eq ha
  by_cases hb : ∃ t, Y.Next (Y.hostOut w) i t
  · exact (transfer _ _ _ _ h.symm eq.symm hb).symm
  rw [jump, jump, dite_eq_right ha, dite_eq_right hb]

-- 读法：`X.jump v i` 等于 `none`。使用 `dite_eq_right` 给出的结论。
theorem jump_idle {v : B (m + L)} (hv : v ∉ Set.range X.hostOut) (i : B 3) :
    X.jump v i = none := dite_eq_right fun ⟨_, t, h, _⟩ => hv ⟨t, h⟩

-- 读法：结论为 `let w := combine v j X.directory.nav w i = (X.jump w i).elim w (fun z => combine (step (D.nav X.raw.1) v z.1) z.2) ∧ X.directory.flags w i = (X.jump w i).isSome`。按 `∃ t, X.Next w i t` 成立与否分情况。
theorem navigate (v : B m) (j : B L) (i : B 3) :
    let w := combine v j
    X.directory.nav w i = (X.jump w i).elim w (fun z => combine (step (D.nav X.raw.1) v z.1) z.2) ∧
      X.directory.flags w i = (X.jump w i).isSome := by
  let w := combine v j
  change X.directory.nav w i = _ ∧ _
  have flags : X.directory.flags w i = true ↔ ∃ t, X.Next w i t := by
    exact @decide_eq_true_iff _ (Classical.propDecidable _)
  by_cases ht : ∃ t, X.Next w i t
  · obtain ⟨z, t, he, hz, hi⟩ := ht
    have hj := X.next_eq hz (X.directory_index ▸ hi)
    rw [he] at hj
    change X.directory.nav w i = (X.jump w i).elim w _ ∧ X.directory.flags w i = (X.jump w i).isSome
    rw [hj]
    refine ⟨?_, flags.mpr ⟨z, t, he, hz, hi⟩⟩
    have hv := X.directory.nav_link t z hz
    change X.directory.nav (X.hostOut t) (X.directory.index t z) = X.hostOut z at hv
    rw [he, hi] at hv
    rw [hv]
    -- 推导：记下中间结论 `hp`：`X.host (X.parent t) = v`。
    have hp : X.host (X.parent t) = v := by
      rw [← X.eq_child t, X.child_address] at he
      exact (Prod.mk.inj ((Match.rowIndex m L).symm.injective he)).1
    have hs : step (D.nav X.raw.1) v (X.key t z).1 = X.host (X.parent z) := by
      rw [← hp, ← X.decode hz]
      cases (X.key t z).1 <;> first | rfl | exact (X.q.core.host_nav ..).symm
    change X.hostOut z = combine (step (D.nav X.raw.1) v (X.key t z).1) _
    rw [hs]
    exact ((congrArg X.hostOut (X.eq_child z)).symm.trans (X.child_address ..))
  · have hj : X.jump w i = none := dite_eq_right ht
    change X.directory.nav w i = (X.jump w i).elim w _ ∧ X.directory.flags w i = (X.jump w i).isSome
    rw [hj]
    refine ⟨?_, Bool.eq_false_iff.mpr (mt flags.mp ht)⟩
    exact dite_eq_right ht

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-!
# 通过一次局部查找取得子首部与块记录

**英文原文**

A single local lookup for the child header and the block record
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Packing Coloring
open scoped Classical

-- 读法：在后续公式中，`Hint` 是 `Format.pair .bit (.pair .bit (.pair (.addr d) (.addr l)))` 的缩写。
abbrev Hint (d l : ℕ) := Format.pair .bit (.pair .bit (.pair (.addr d) (.addr l)))
-- 读法：在后续公式中，`Output` 是 `Format.pair (.addr ℓ) (.pair .bit (.vec 3 (Hint d l)))` 的缩写。
abbrev Output (ℓ d l : ℕ) := Format.pair (.addr ℓ) (.pair .bit (.vec 3 (Hint d l)))

-- 读法：逐一匹配以下输入模式：`none`、`some (none, k)`、`some (some i, k)`。
def hint {d l : ℕ} (j : B l) : Option (Data.Key d l) → (Hint d l).obj
  | none => (false, false, 0, j)
  | some (none, k) => (true, false, 0, k)
  | some (some i, k) => (true, true, i, k)

-- 读法：`follow` 的取值由 `(Match.rowIndex m l).symm (if q.2.1 then g v q.2.2.1 else v, q.2.2.2)` 给出。
def follow {m d l : ℕ} (g : B m → B d → B m) (v : B m) (q : (Hint d l).obj) :=
  (Match.rowIndex m l).symm (if q.2.1 then g v q.2.2.1 else v, q.2.2.2)

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "W" => Tether.width N r s
local notation "L" => bits r s W
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h
local notation "d" => D.scheme.d

-- 读法：在后续公式中，`Query` 是 `Format.pair (.addr h) (.pair (.addr L) (Question A))` 的缩写。
abbrev Query := Format.pair (.addr h) (.pair (.addr L) (Question A))
-- 读法：在后续公式中，`Reply` 是 `Output (script A.scheme).width d L` 的缩写。
abbrev Reply := Output (script A.scheme).width d L
-- 读法：在后续公式中，`Replies` 是 `Format.vec (m + L) (.vec h (Reply A N r s))` 的缩写。
abbrev Replies := Format.vec (m + L) (.vec h (Reply A N r s))

-- 读法：`ask` 的取值由 `(k, (Match.rowIndex m L i).2, query A x (Match.rowIndex m L i).1 k)` 给出。
def ask (x : A.format.obj) (i : B (m + L)) (k : B h) : (Query A N r s).obj :=
  (k, (Match.rowIndex m L i).2, query A x (Match.rowIndex m L i).1 k)

namespace Data
variable {A N r s} {u : ℕ} {a b : Wire} (X Y : Data A N r s u a b)

-- 读法：`respond` 的结果类型为 `(Replies A N r s).obj`。
def respond : (Replies A N r s).obj := fun i k =>
  ((script A.scheme).serial (X.record i k), decide (i ∈ Set.range X.hostOut),
    fun j => hint (Match.rowIndex m L i).2 (X.jump i j))

-- 读法：`X.jump (combine v j) i` 等于 `Y.jump (combine w j) i`。按 `combine v j ∈ Set.range X.hostOut` 成立与否分情况。
theorem same_jump {v w : B m} {k : B h} (he : query A X.raw v k = query A Y.raw w k) (j : B L) (i : B 3) :
    X.jump (combine v j) i = Y.jump (combine w j) i := by
  have hh : D.live X.raw.1 v = D.live Y.raw.1 w := congrArg (fun t : (Question A).obj => t.1) he
  have hv : combine v j ∈ Set.range X.hostOut ↔ combine w j ∈ Set.range Y.hostOut := by
    rw [X.child_active, Y.child_active, hh]
  by_cases hx : combine v j ∈ Set.range X.hostOut
  · obtain ⟨hl, z, rfl⟩ := (X.child_active ..).mp hx
    obtain ⟨v, rfl⟩ := (X.q.core.live _).mp hl
    obtain ⟨w, rfl⟩ := (Y.q.core.live _).mp (hh.symm.trans hl)
    obtain ⟨k, rfl⟩ := (cellIndex _).surjective k
    rw [← X.child_address, ← Y.child_address]
    apply X.jump_eq Y
    · rw [X.child_parent, Y.child_parent]; exact X.agree_at Y he
    · rw [X.child_seat, Y.child_seat]
  · rw [X.jump_idle hx, Y.jump_idle (mt hv.mpr hx)]

-- 读法：`X.respond v j` 等于 `Y.respond w k`。
theorem consistent {v w : B (m + L)} {j k : B h} (he : ask A N r s X.raw v j = ask A N r s Y.raw w k) :
    X.respond v j = Y.respond w k := by
  obtain ⟨⟨x, i⟩, rfl⟩ := (Match.rowIndex m L).symm.surjective v
  obtain ⟨⟨y, l⟩, rfl⟩ := (Match.rowIndex m L).symm.surjective w
  simp only [ask, Equiv.apply_symm_apply, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, he⟩ := he
  have hv : combine x i ∈ Set.range X.hostOut ↔ combine y i ∈ Set.range Y.hostOut := by
    have hh : D.live X.raw.1 x = D.live Y.raw.1 y := congrArg (fun t : (Question A).obj => t.1) he
    rw [X.child_active, Y.child_active, hh]
  simp only [respond, Equiv.apply_symm_apply]
  exact Prod.ext (congrArg (script A.scheme).serial (X.uniform Y he i)) (Prod.ext (decide_eq_decide.mpr hv)
    (funext fun t => congrArg (hint i) (X.same_jump Y he i t)))

end Data

-- 读法：`render` 的结果类型为 `(template A.scheme (m + L) h u).format.obj`。
def render {u : ℕ} (g : B m → B d → B m) (x : (Replies A N r s).obj) :
    (template A.scheme (m + L) h u).format.obj :=
  let lab i k := (x i k).1
  let z i j := (x i 0).2.2 j
  (fun i => (fun j => follow g (Match.rowIndex m L i).1 (z i j), lab i),
   fun i => (((x i 0).2.1, false), fun j => ((z i j).1, (z i j).1), lab i))

variable {A N r s} {u : ℕ} {a b : Wire}
-- 读法：`render A N r s (D.nav X.raw.1) X.respond` 等于 `X.frame`。
theorem Data.rendered (X : Data A N r s u a b) : render A N r s (D.nav X.raw.1) X.respond = X.frame := by
  have hr (i : B (m + L)) (j : B 3) :
      follow (D.nav X.raw.1) (Match.rowIndex m L i).1 ((X.respond i 0).2.2 j) = X.directory.nav i j ∧
      ((X.respond i 0).2.2 j).1 = X.directory.flags i j := by
    obtain ⟨⟨v, l⟩, rfl⟩ := (Match.rowIndex m L).symm.surjective i
    simp only [Data.respond, Equiv.apply_symm_apply]
    change follow _ _ (hint l (X.jump (Data.combine v l) j)) = X.directory.nav (Data.combine v l) j ∧
      (hint l (X.jump (Data.combine v l) j)).1 = X.directory.flags (Data.combine v l) j
    rw [(X.navigate v l j).1, (X.navigate v l j).2]
    rcases X.jump (Data.combine v l) j with _|⟨_|_, k⟩ <;> exact ⟨rfl, rfl⟩
  exact Prod.ext (funext fun v => Prod.ext (funext fun j => (hr v j).1) rfl)
    (funext fun v => Prod.ext rfl (Prod.ext (funext fun j => Prod.ext (hr v j).2 (hr v j).2) rfl))

-- 读法：存在 `g : (Query A N r s).obj → (Reply A N r s).obj`，对每个 `(X : Data A N r s u a b) v j`，`g (ask A N r s X.raw v j)` 等于 `X.respond v j`。这里调用 `dite_eq_left`。
theorem lookup_exists :
    ∃ g : (Query A N r s).obj → (Reply A N r s).obj,
      ∀ (X : Data A N r s u a b) v j, g (ask A N r s X.raw v j) = X.respond v j := by
  let rel q z := ∃ X : Data A N r s u a b, ∃ v j, ask A N r s X.raw v j = q ∧ X.respond v j = z
  let g q := if t : ∃ z, rel q z then t.choose else (Reply A N r s).serial.symm 0
  refine ⟨g, fun X v j => ?_⟩
  have e : ∃ z, rel (ask A N r s X.raw v j) z := ⟨_, X, v, j, rfl, rfl⟩
  obtain ⟨Y, w, k, hq, he⟩ := e.choose_spec
  exact (dite_eq_left e).trans (he.symm.trans (Y.consistent X hq))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 为还原字典汇集短标签

**英文原文**

Gathering short labels for the restoration dictionary
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "W" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "h" => D.scheme.h

-- 读法：在后续公式中，`Queries` 是 `Format.vec (m + W) (.vec h (Query A N r s))` 的缩写。
abbrev Queries := Format.vec (m + W) (.vec h (Query A N r s))
-- 读法：在后续公式中，`ReadyQueries` 是 `Format.pair (Neighborhood.Rows m d) (Queries A N r s)` 的缩写。
abbrev ReadyQueries := Format.pair (Neighborhood.Rows m d) (Queries A N r s)
-- 读法：在后续公式中，`Source` 是 `Format.pair (.vec m .bit) (.pair (Raw m d) A.scheme.format)` 的缩写。
abbrev Source := Format.pair (.vec m .bit) (.pair (Raw m d) A.scheme.format)
-- 读法：在后续公式中，`Gathered` 是 `Format.pair (.vec m .bit) (.pair (.vec m (Preview d)) (Fmt.groups m d h (Letters A)))` 的缩写。
abbrev Gathered := Format.pair (.vec m .bit) (.pair (.vec m (Preview d)) (Fmt.groups m d h (Letters A)))

-- 读法：`collect` 的取值由 `(D.live x.1, (D.nav x.1, D.flags x.1), A.rows x)` 给出。
def collect (x : A.format.obj) : (Source A).obj :=
  (D.live x.1, (D.nav x.1, D.flags x.1), A.rows x)

-- 读法：`gathered` 的取值由 `(D.live x.1, preview D x.1, Window.reads 2 (A.rows x))` 给出。
def gathered (x : A.format.obj) : (Gathered A).obj :=
  (D.live x.1, preview D x.1, Window.reads 2 (A.rows x))

-- 读法：`spread` 的取值由 `(fun v => (x.2.2 v).1, fun v k => let w := Match.rowIndex m W v (k, w.2, x.1 w.1, x.2.1 w.1, (x.2.2 w.1).2 k))` 给出。
def spread (x : (Gathered A).obj) : (ReadyQueries A N r s).obj :=
  (fun v => (x.2.2 v).1, fun v k =>
    let w := Match.rowIndex m W v
    (k, w.2, x.1 w.1, x.2.1 w.1, (x.2.2 w.1).2 k))

-- 读法：在 `F` 上按格式 `A.format`、`(Source A)` 编码输入输出，映射 `(collect A)` 的电路规模至多为 `(A.format.width + 2 * (Source A).width)`。这里调用 `Circuit.project`。
theorem collect_net : Circuit F A.format (Source A) (collect A) (A.format.width + 2 * (Source A).width) := by
  let tap : (Source A).pins → A.format.pins
    | .inl (v, i) => .inl (.inr (v, .inl (.inl i)))
    | .inr (.inl (.inl (v, j))) => .inl (.inl (v, .inl j))
    | .inr (.inl (.inr (v, j))) => .inl (.inr (v, .inr (.inl j)))
    | .inr (.inr (v, .inl j)) => .inl (.inl (v, .inl j))
    | .inr (.inr (v, .inr j)) => .inr (v, j)
  exact Circuit.project tap (by rintro x (⟨v, i⟩|(⟨v, j⟩|⟨v, j⟩)|⟨v, j|j⟩) <;> rfl)

-- 读法：在 `F` 上按格式 `(Gathered A)`、`(ReadyQueries A N r s)` 编码输入输出，映射 `(spread A N r s)` 的电路规模至多为 `((Gathered A).width + 34 * (ReadyQueries A N r s).width)`。这里调用 `Window.Tile.project_const`。
theorem spread_net : Circuit F (Gathered A) (ReadyQueries A N r s) (spread A N r s)
    ((Gathered A).width + 34 * (ReadyQueries A N r s).width) := by
  apply Window.Tile.project_const
  rintro (⟨v, i⟩|⟨v, k, i|i|i|i|i⟩)
  · exact .inl ⟨.inr (.inr (v, .inl i)), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr h).code k i, fun _ => rfl⟩
  · exact .inr ⟨(Format.addr W).code (Match.rowIndex m W v).2 i, fun _ => rfl⟩
  · exact .inl ⟨.inl ((Match.rowIndex m W v).1, i), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inl ((Match.rowIndex m W v).1, i)), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr ((Match.rowIndex m W v).1, .inr (k, i))), fun _ => rfl⟩

-- 读法：`queryCost` 的构造用到 `A.format.width`、`Format.vec`、`Window.readCost`。
def queryCost (v z : ℕ) :=
  4 * (A.format.width + 2 * (Source A).width)+
    (4 * (Format.vec m .bit).width + (4 * (2 ^ m * (100 + (m + 2 ^ radius d)) ^ 60) + 3 * Window.readCost m d v z))+
    4 * ((Gathered A).width + 34 * (ReadyQueries A N r s).width)

variable {A N r s} {u w v z : ℕ} {a b : Wire} {P : Set (Table F)}

-- 读法：结论为 `Computes F w P A.format (ReadyQueries A N r s) (fun X : Data A N r s u a b => X.raw) (fun X => (D.nav X.raw.1, ask A N r s X.raw)) (fun _ => 1) (queryCost A N r s v z)`。
theorem queries (hw : 3 ≤ w) (ht : Access F w P (m + d) v z)
    (cap : 2 ^ h * (Letters A).width ≤ v) :
    Computes F w P A.format (ReadyQueries A N r s) (fun X : Data A N r s u a b => X.raw)
      (fun X => (D.nav X.raw.1, ask A N r s X.raw)) (fun _ => 1) (queryCost A N r s v z) := by
  let I := Data A N r s u a b
  let live := Format.vec m .bit
  have start := Computes.of_map (L := P) (x := fun X : I => X.raw)
    (Map.circuit hw (collect_net A)) (fun _ => rfl)
  have keep := Computes.of_map (L := P) (x := fun X : I => D.live X.raw.1)
    (Map.circuit hw (Circuit.id F live)) (fun _ => rfl)
  -- 推导：从 `cheap_preview F («m» := m) («d» := d) le_rfl` 中取出 `t, hg, hb`。
  obtain ⟨t, hg, hb⟩ := cheap_preview F («m» := m) («d» := d) le_rfl
  have hc : Circuit F (Raw m d) (.vec m (Preview d)) inspect (2 ^ m * (100 + (m + 2 ^ radius d)) ^ 60) :=
    hg.mono (by omega)
  have scan := Computes.of_map (L := P) (x := fun X : I => (collect A X.raw).2.1)
    (Map.circuit hw hc) (fun _ => rfl)
  have move := Window.reads_net hw ht (fun X : I => A.rows X.raw) (fun X => X.q.core.reciprocal) cap
  have stop := Computes.of_map (L := P) (x := fun X : I => gathered A X.raw)
    (Map.circuit hw (spread_net A N r s)) (fun _ => rfl)
  have done := (start.comp (keep.par (scan.par move))).comp stop
  simp only [one_mul] at done
  exact done

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 由有界选择器重建长地址

**英文原文**

Reconstructing long addresses from bounded selectors
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing Finset
open scoped Classical

variable {F : Type} [Field F]

-- 读法：在 `F` 上按格式 `P`、`Q` 编码输入输出，映射 `g` 的电路规模至多为 `(P.width + Install.localCost R * Q.width)`。这里调用 `h.bnet`。
theorem local_map {P Q : Format} {g : P.obj → Q.obj} {R : ℕ}
    (hp : ∀ j : Q.pins, ∃ z : Finset P.pins, z.card ≤ R ∧ ∀ x y,
      (∀ k ∈ z, P.code x k = P.code y k) → Q.code (g x) j = Q.code (g y) j) :
    Circuit F P Q g (P.width + Install.localCost R * Q.width) := by
  have h : Install.Depends (Q.code ∘ g ∘ P.code.symm) R := by
    intro j
    obtain ⟨z, hz, he⟩ := hp j
    refine ⟨z, hz, fun x y h => he _ _ ?_⟩
    simpa only [Equiv.apply_symm_apply] using h
  exact h.bnet F

-- 读法：在后续公式中，`Before` 是 `Format.pair (Neighborhood.Rows m d) (.vec (m + l) (.vec h (Output ℓ d l)))` 的缩写。
private abbrev Before (m d h l ℓ : ℕ) :=
  Format.pair (Neighborhood.Rows m d) (.vec (m + l) (.vec h (Output ℓ d l)))

-- 读法：`After` 的构造用到 `Format.pair`、`Fmt.rows`、`Group.Flags`。
private abbrev After (m _d h l ℓ : ℕ) :=
  Format.pair (Fmt.rows (m + l) 3 h (.addr ℓ))
    (.vec (m + l) (.pair (.pair .bit .bit) (.pair (Group.Flags 3) (.vec h (.addr ℓ)))))

-- 读法：`rr` 的结果类型为 `(After m d h l ℓ).obj`。
private def rr {m d h l ℓ : ℕ} (x : (Before m d h l ℓ).obj) : (After m d h l ℓ).obj :=
  let lab i k := (x.2 i k).1
  let z i j := (x.2 i 0).2.2 j
  (fun i => (fun j => follow x.1 (Match.rowIndex m l i).1 (z i j), lab i),
   fun i => (((x.2 i 0).2.1, false), fun j => ((z i j).1, (z i j).1), lab i))

-- 读法：结论为 `Circuit F (Before m d h L ℓ) (After m d h L ℓ) rr ((Before m d h L ℓ).width + Install.localCost (2 ^ d + (Hint d L).width) * (After m d h L ℓ).width)`。
private theorem build (m d h L ℓ : ℕ) :
    Circuit F (Before m d h L ℓ) (After m d h L ℓ) rr
      ((Before m d h L ℓ).width + Install.localCost (2 ^ d + (Hint d L).width) * (After m d h L ℓ).width) := by
  let P := Before m d h L ℓ
  let Q := After m d h L ℓ
  let g : P.obj → Q.obj := rr
  let R := 2 ^ d + (Hint d L).width
  have hr : 1 ≤ R := (Nat.two_pow_pos d).trans_le (Nat.le_add_right _ _)
  let ok (j : Q.pins) := ∃ z : Finset P.pins, z.card ≤ R ∧ ∀ x y,
    (∀ k ∈ z, P.code x k = P.code y k) → Q.code (g x) j = Q.code (g y) j
  have pick {j : Q.pins} (i : P.pins) (eq : ∀ x, Q.code (g x) j = P.code x i) : ok j :=
    ⟨{i}, by simpa using hr, fun x y he => (eq _).trans ((he i (by simp)).trans (eq _).symm)⟩
  apply local_map
  change ∀ j, ok j
  rintro (⟨v, ⟨j, b⟩|⟨k, b⟩⟩|⟨v, (b|b)|⟨j, b|b⟩|⟨k, b⟩⟩)
  -- 推导：从 `Match.append_pin m L b` 中取出 `z, hz`。
  · obtain ⟨z, hz⟩ := Match.append_pin m L b
    let v₀ := (Match.rowIndex m L v).1
    let tick (x : P.obj) := (x.2 v 0).2.2 j
    let lift : (Hint d L).pins → P.pins := fun i => .inr (v, 0, .inr (.inr (j, i)))
    have eq (x : P.obj) : Q.code (g x) (.inl (v, .inl (j, b))) =
        z.elim ((Format.addr m).code (if (tick x).2.1 then x.1 v₀ (tick x).2.2.1 else v₀))
          ((Format.addr L).code (tick x).2.2.2) := by
      change (Format.addr (m + L)).code (follow x.1 v₀ (tick x)) b = _
      unfold follow
      rw [hz]
    rcases z with k|k
    -- 推导：记下中间结论 `src`：`B d → P.pins`。
    · let src : B d → P.pins := fun i => .inl (v₀, i, k)
      refine ⟨univ.image src ∪ univ.image lift, ?_, ?_⟩
      · exact (card_union_le _ _).trans (Nat.add_le_add (card_image_le.trans_eq (by simp)) card_image_le)
      · intro x y he
        have ht : tick x = tick y := by
          apply (Hint d L).code.injective
          funext i
          exact he _ (mem_union_right _ (mem_image_of_mem lift (mem_univ i)))
        rw [eq, eq, ht]
        simp only [Sum.elim_inl]
        split
        · exact he _ (mem_union_left _ (mem_image_of_mem src (mem_univ _)))
        · rfl
    · exact pick (lift (.inr (.inr (.inr k)))) (fun x => eq x)
  · exact pick (.inr (v, k, .inl b)) (fun _ => rfl)
  · exact pick (.inr (v, 0, .inr (.inl b))) (fun _ => rfl)
  · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  · exact pick (.inr (v, 0, .inr (.inr (j, .inl b)))) (fun _ => rfl)
  · exact pick (.inr (v, 0, .inr (.inr (j, .inl b)))) (fun _ => rfl)
  · exact pick (.inr (v, k, .inl b)) (fun _ => rfl)

variable {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "L" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "h" => D.scheme.h

-- 读法：在后续公式中，`RawReply` 是 `Format.pair (Neighborhood.Rows m d) (Replies A N r s)` 的缩写。
abbrev RawReply := Format.pair (Neighborhood.Rows m d) (Replies A N r s)
-- 读法：在后续公式中，`result` 是 `template A.scheme (m + L) h u` 的缩写。
abbrev result (u : ℕ) := template A.scheme (m + L) h u
-- 读法：`readsBound` 的取值由 `2 ^ d + (Hint d (bits r s (Tether.width N r s))).width` 给出。
def readsBound (_ : Attachment D) (N r s : ℕ) := 2 ^ d + (Hint d (bits r s (Tether.width N r s))).width

-- 读法：结论为 `Circuit F (RawReply A N r s) (result A N r s u).format (fun x => render A N r s x.1 x.2) ((RawReply A N r s).width + Install.localCost (readsBound A N r s) * (result A N r s u).format.width)`。
theorem render_circuit (u : ℕ) :
    Circuit F (RawReply A N r s) (result A N r s u).format
      (fun x => render A N r s x.1 x.2)
      ((RawReply A N r s).width + Install.localCost (readsBound A N r s) * (result A N r s u).format.width) :=
  build m d h L (script A.scheme).width

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 由挂接格式写出还原后的板所需的成本

**英文原文**

Cost of writing a restored board from the attachment format
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "B'" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "h" => D.scheme.h

-- 读法：`gateWidth` 的取值由 `(Query A N r s).width + (Reply A N r s).width` 给出。
def gateWidth := (Query A N r s).width + (Reply A N r s).width

-- 读法：`cost` 的构造用到 `Neighborhood.Rows`、`Install.localCost`、`format.width`。
def cost (u v z : ℕ) :=
  queryCost A N r s v z +
    (4 * (Neighborhood.Rows m d).width + 2 ^ (m + B') * (2 ^ h * (1 + (Query A N r s).width + (Reply A N r s).width))) +
    4 * ((RawReply A N r s).width + Install.localCost (readsBound A N r s) * (result A N r s u).format.width)

variable {A N r s} {u : ℕ} {a b : Wire}

-- 读法：证明中先建立 `keep`，即 `= Map.circuit (L`。
theorem control :
    ∃ gate : Table F, ∀ {w v z : ℕ} {P : Set (Table F)}, 3 ≤ w → gate ∈ P →
      gateWidth A N r s ≤ w → Access F w P (m + d) v z → 2 ^ h * (Letters A).width ≤ v →
      Computes F w P A.format (result A N r s u).format
        (fun X : Data A N r s u a b => X.raw) (fun X => X.frame) (fun _ => 1) (cost A N r s u v z) := by
  let I := Data A N r s u a b
  obtain ⟨g, hg⟩ := lookup_exists (A := A) (N := N) (r := r) (s := s) (a := a) (b := b) (u := u)
  let gate := lookup F (Query A N r s) (Reply A N r s) (fun x y => @ite F (g x = y) (Classical.propDecidable _) 1 0)
  refine ⟨gate, ?_⟩
  intro w v z P hw allowed wide ht cap
  have one : Map F w P (Query A N r s) (Reply A N r s) g
      (1 + (Query A N r s).width + (Reply A N r s).width) := Kernel.lookup wide allowed
  have all := Map.vec _ (fun _ : B (m + B') => Map.vec _ (fun _ : B h => one))
  -- 推导：记下中间结论 `keep`：`= Map.circuit (L`。
  have keep := Map.circuit (L := P) hw (Circuit.id F (Neighborhood.Rows m d))
  have start := queries (a := a) (b := b) (u := u) (N := N) (r := r) (s := s) hw ht cap
  have go := Computes.of_map (A := ReadyQueries A N r s) (B := RawReply A N r s) (x := fun X : I => (D.nav X.raw.1, ask A N r s X.raw))
    (y := fun X : I => (D.nav X.raw.1, X.respond)) (keep.par all)
    (fun X => Prod.ext rfl (funext fun i => funext fun j => hg X i j))
  have finish := Computes.of_map (A := RawReply A N r s) (B := (result A N r s u).format) (L := P) (x := fun X : I => (D.nav X.raw.1, X.respond))
    (Map.circuit hw (render_circuit A N r s u)) (fun X => X.rendered)
  have run := (start.comp go).comp finish
  simp only [one_mul] at run
  exact run

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# 在还原后定位各外露区段

后缀由原字母和站点索引确定。每个比特在获分配的区段中保留自身偏移量。

**英文原文**

Locating each exposed span after restoration

The suffix is determined by the old letter and the station index.
Every bit keeps its offset in the assigned span.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s u : ℕ)
local notation "W" => Tether.width N r s

-- 读法：在后续公式中，`Occupied` 是 `{i : B A.k // A.live l i = true ∧ i ≠ 0}` 的缩写。
abbrev Occupied (l : B A.ℓ) := {i : B A.k // A.live l i = true ∧ i ≠ 0}

-- 读法：`destination` 的结果类型为 `B (bits r s W)`。
def destination (l : B A.ℓ) (i : B A.k) : B (bits r s W) :=
  if he : A.live l i = true ∧ i ≠ 0 then
    if h : Fintype.card (Occupied A l) ≤ r then
      suffix r s W (Tether.member ((), History.Reset.rank (Function.Embedding.subtype _) h ⟨i, he⟩))
    else 0
  else 0

-- 读法：`shift` 的结果类型为 `(result A N r s u).scheme.Span`。
def shift (raw : A.format.obj) (t : A.scheme.Span) : (result A N r s u).scheme.Span :=
  ((Data.combine t.1.1 (destination A N r s (raw.2 t.1.1 t.1.2.1) t.1.2.2), t.1.2.1, 0),
    Chain.Frame.pair A.e (A.scheme.direction (A.rows raw) t, t.2))

namespace Data
variable {A N r s u} {a b : Wire} (X : Data A N r s u a b)

-- 读法：`occupied` 的结果类型为 `Attachment.Encloses.Members z ≃ Occupied A (X.letter z.1 z.2)`。
private def occupied (z : X.G.V × Cell D.scheme.h) :
    Attachment.Encloses.Members z ≃ Occupied A (X.letter z.1 z.2) := by
  let f (t : Attachment.Encloses.Members z) : Occupied A (X.letter z.1 z.2) :=
    ⟨X.q.slot t.val, (X.exists_iff ..).mp ⟨.inr t.val, t.property, rfl⟩, X.q.positive t.val⟩
  refine Equiv.ofBijective f ⟨fun i j he => (X.q.memberKey z).injective (congrArg Subtype.val he), ?_⟩
  rintro ⟨j, hj, h0⟩
  obtain ⟨w, hw, he⟩ := (X.exists_iff ..).mpr hj
  rcases w with w|t
  · exact (h0 he.symm).elim
  · exact ⟨⟨t, hw⟩, Subtype.ext he⟩

-- 读法：`destination A N r s (X.tag (.inr t)).1 (X.tag (.inr t)).2` 等于 `suffix r s W (Tether.member ((), X.e.slot t))`。这里调用 `Fintype.card_le_of_injective`。
theorem destination_eq (t : X.T) :
    destination A N r s (X.tag (.inr t)).1 (X.tag (.inr t)).2 =
      suffix r s W (Tether.member ((), X.e.slot t)) := by
  let z := X.G.park t
  let l := X.letter z.1 z.2
  let v := X.occupied z
  have hv : ∀ i, (v i).val = X.q.memberKey z i := fun _ => rfl
  have hc : Fintype.card (Occupied A l) ≤ r := by
    rw [← Fintype.card_congr v]
    refine LE.le.trans ?_ (Fintype.card_fin r).le
    apply Fintype.card_le_of_injective (fun i => X.e.slot i.val)
    exact fun i j h => Subtype.ext (X.e.unique (Prod.ext (i.property.trans j.property.symm) h))
  -- 推导：记下中间结论 `hi`：`A.live l (X.q.slot t) = true ∧ X.q.slot t ≠ 0`。
  have hi : A.live l (X.q.slot t) = true ∧ X.q.slot t ≠ 0 := (v ⟨t, rfl⟩).property
  unfold tag
  rw [X.token]
  change destination A N r s l (X.q.slot t) = _
  rw [destination, dite_eq_left hi, dite_eq_left hc]
  apply congrArg (fun i => suffix r s W (Tether.member ((), i)))
  change _ = X.q.number X.allocation t
  rw [X.q.number_at X.allocation t z rfl]
  exact History.Reset.rank_eq (fun i => ⟨v.symm i, (congrArg Subtype.val (v.apply_symm_apply i)).symm.trans (hv _)⟩)
    (fun i => ⟨v i, (hv i).symm⟩) rfl

-- 读法：结论为 `let x := (X.p.boundary i).val let y := (X.pres.pres.boundary i).val y.1 = shift A N r s u X.raw x.1 ∧ y.2.val = x.2.val ∧ (result A N r s u).scheme.width X.frame.1 y.1 = A.scheme.width (A.rows X.raw) x.1`。
theorem boundary_shift (i : slots a ⊕ slots b) :
    let x := (X.p.boundary i).val
    let y := (X.pres.pres.boundary i).val
    y.1 = shift A N r s u X.raw x.1 ∧ y.2.val = x.2.val ∧
      (result A N r s u).scheme.width X.frame.1 y.1 = A.scheme.width (A.rows X.raw) x.1 := by
  let g := written X.q X.e X.loopless X.directory
  let t := boundaryEnd X.route.graph i
  let j := boundaryEnd X.old i
  have hx : (X.p.boundary i).val = X.p.toSeating.ends j := by cases i <;> rfl
  have hy : (X.pres.pres.boundary i).val = g.seating.ends t := by cases i <;> rfl
  -- 推导：记下中间结论 `he`：`X.f.old X.p t = X.p.toSeating.ends j`。
  have he : X.f.old X.p t = X.p.toSeating.ends j := X.f.old_boundary X.p i
  have ord : (g.seating.ends t).2.val = (X.p.toSeating.ends j).2.val :=
    (g.ends _).2.trans (congrArg (fun q => q.2.val) he)
  have sz : (result A N r s u).scheme.width X.frame.1 (g.seating.ends t).1 =
      A.scheme.width (A.rows X.raw) (X.p.toSeating.ends j).1 := by rw [(g.ends _).1, g.size, he]
  rw [hx, hy]
  refine ⟨(g.ends _).1.trans ?_, ord, sz⟩
  have eqt : t = X.route.original j := by cases i <;> rfl
  obtain ⟨u', hu⟩ : ∃ u' : X.T, X.old.station j = .inr u' := by
    cases i <;> exact ⟨_, rfl⟩
  have site := (X.span_at j).trans (congrArg (fun v => (X.p.vertex v, X.port j)) hu)
  have dir := X.q.directed j
  unfold Written.span shift
  change (g.vertex (X.route.graph.station t), X.f.lane X.p t) = _
  rw [Chain.Frame.lane, he, eqt, X.route.station_original, X.route.side_original, dir, site, hu]
  change ((X.hostOut (Tether.member ((X.G.park u').1, X.e.slot u')), cellIndex _ (X.G.park u').2, 0), _) =
    ((combine (X.p.vertex (.inr u')).1 (destination A N r s (X.tag (.inr u')).1 (X.tag (.inr u')).2),
      (X.p.vertex (.inr u')).2.1, 0), _)
  rw [X.destination_eq, X.vertex]
  exact congrArg (fun y => ((y, cellIndex _ (X.G.park u').2, (0 : B 0)), _))
    (X.child_address (X.G.park u').1 (Tether.member ((), X.e.slot u')))

end Data
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end
