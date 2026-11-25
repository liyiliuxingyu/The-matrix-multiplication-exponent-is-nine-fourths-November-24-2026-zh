-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames

/-!
# 从挂接边界中提出标量因子

**英文原文**

Pulling a scalar factor through the attached border
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Border

variable {F T : Type} [Field F] [Fintype T] {a b x y : Wire}
  (Z : Border F T x y a b) {G : Diagram F a b}
  {S : Assembly.Scheme F} {r : S.format.obj}

-- 读法：`(Z.attach G).eval v w` 等于 `Assembly.Fmt.weight S.scalar r * (Z.attach G.sweep).eval v w`。
theorem attach_factor (q : S.Presentation r G) (v : Val x) (w : Val y) :
    (Z.attach G).eval v w = Assembly.Fmt.weight S.scalar r * (Z.attach G.sweep).eval v w := by
  rw [Z.eval_attach, Z.eval_attach]
  simp only [q.sweep_eval, Finset.mul_sum, mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Packing.Border
end

/-!
# 更换宿主后冻结站点的地址

某个子宿主的所有块共用同一父宿主。在块内，只需两个短索引即可还原原表及其引脚。未使用的候选位置与核心站点无须保存冻结记录。

**英文原文**

Addresses of the frozen stations after a change of host

The parent host is shared by all blocks of a child. Within a block,
a short pair of indices suffices to recover the old table and pins.
Unused candidates and the core station require no frozen record.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring
open scoped Classical

variable {F T : Type} {D : Template F} (A : Attachment D) (Y : Template F) (k : ℕ)

-- 读法：在后续公式中，`Place` 是 `B Y.scheme.m × B Y.scheme.h × B k` 的缩写。
abbrev Place (Y : Template F) (k : ℕ) := B Y.scheme.m × B Y.scheme.h × B k

-- 读法：在后续公式中，`pointer` 是 `Format.pair .bit (.pair (.addr D.scheme.h) (.addr A.k))` 的缩写。
abbrev pointer := Format.pair .bit (.pair (.addr D.scheme.h) (.addr A.k))

-- 读法：逐一匹配以下输入模式：`none`、`some t`。
def tag : Option (B D.scheme.h × B A.k) → A.pointer.obj
  | none => (false, 0, 0)
  | some t => (true, t)

-- 读法：当 `x.1` 成立时取 `some x.2`，否则取 `none`。
def untag (x : A.pointer.obj) := if x.1 then some x.2 else none

-- 读法：`A.untag (A.tag x)` 等于 `x`。
theorem untag_tag (x : Option (B D.scheme.h × B A.k)) : A.untag (A.tag x) = x := by
  cases x <;> rfl

-- 读法：结构的字段包括 `parent`、`prev`。
structure Relocation where
  parent : B Y.scheme.m → B D.scheme.m
  prev : B Y.scheme.m → B Y.scheme.h → B k → Option (B D.scheme.h × B A.k)

namespace Relocation
variable {A Y k} (R : A.Relocation Y k)

-- 读法：输入 `i j l` 时返回 `A.tag (R.prev i j l)`。
def flags : (Format.vec Y.scheme.m (.vec Y.scheme.h (.vec k A.pointer))).obj :=
  fun i j l => A.tag (R.prev i j l)

-- 读法：`back` 的取值由 `(R.prev j.1 j.2.1 j.2.2).map (Prod.mk (R.parent j.1))` 给出。
def back (j : Place Y k) : Option A.scheme.Vtx :=
  (R.prev j.1 j.2.1 j.2.2).map (Prod.mk (R.parent j.1))

-- 读法：`kept` 的取值由 `(R.back j).filter (fun u => A.live (r.2 u.1 u.2.1) u.2.2 && decide (u.2.2 ≠ 0))` 给出。
def kept (r : A.format.obj) (j : Place Y k) :=
  (R.back j).filter (fun u => A.live (r.2 u.1 u.2.1) u.2.2 && decide (u.2.2 ≠ 0))

variable [Field F] [Fintype T] {x y a b : Wire} {u v : ℕ} {L : Fringe x y T}
  {G : HostNet F L D.scheme.h u} {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y}
  {r : A.format.obj} {s : Y.format.obj}
  (q : A.Encloses r G Z) (p : Y.Encodes s H) (slot : T → B k)

-- 读法：结构的字段包括 `positive`、`iff`。
structure Moves : Prop where
  positive : ∀ t, slot t ≠ 0
  iff : ∀ j t, R.back j = some (q.pres.vertex (.inr t)) ↔
    j = (p.post.host (H.park t).1, p.post.block (H.park t).2, slot t)

-- 读法：存在 `t`，`w` 等于 `q.pres.vertex (.inr t)`。这里调用 `h.2.2`。
theorem active (j : Place Y k) (w : A.scheme.Vtx) (h : R.kept r j = some w) :
    ∃ t, w = q.pres.vertex (.inr t) := by
  simp only [kept, Option.filter_eq_some_iff, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨t|t, ht⟩ := (q.occupied w).mp h.2.1
  · exact (h.2.2 (by rw [← ht, q.internal])).elim
  · exact ⟨t, ht.symm⟩

-- 读法：`R.kept r j = some (q.pres.vertex (.inr t))` 与 `j = (p.post.host (H.park t).1, p.post.block (H.park t).2, slot t)` 等价。这里调用 `and_iff_left`。
theorem kept_iff (h : R.Moves q p slot) (j : Place Y k) (t : T) :
    R.kept r j = some (q.pres.vertex (.inr t)) ↔
      j = (p.post.host (H.park t).1, p.post.block (H.park t).2, slot t) := by
  have he := (q.occupied _).mpr ⟨.inr t, rfl⟩
  have hn : (q.pres.vertex (.inr t)).2.2 ≠ 0 := by rw [q.frozen]; exact q.positive t
  simp only [kept, Option.filter_eq_some_iff, Bool.and_eq_true, decide_eq_true_eq, he, true_and, h.iff]
  exact and_iff_left hn

end Relocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 单个出现位置上有效冻结站点的数量上界

**英文原文**

Bounding the number of live frozen stations at one occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment

open Coloring Packing Finset
open scoped Classical

-- 读法：`occupiedSeats` 的取值由 `univ.filter fun j => j ≠ 0 ∧ live j = true` 给出。
def occupiedSeats {k : ℕ} (live : B k → Bool) : Finset (B k) :=
  univ.filter fun j => j ≠ 0 ∧ live j = true

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D : Template F}
  {A : Attachment D} {r : A.format.obj} {u N : ℕ} {L : Fringe x y T}
  {G : HostNet F L D.scheme.h u} {Z : Border F T a b x y} {δ : ℝ}

-- 读法：`(occupiedSeats (A.live (r.2 v i))).card` 不超过 `N`。
/-- 核心以外的每个已占位置至少承担一项大小为 `δ` 的开销，且该位置的所有开销都归入同一停放点。

英文原文：Every occupied seat apart from the core pays at least one charge
of size `δ`, and all its charges occur at the same parked location.
-/
theorem Encloses.slot_count (q : A.Encloses r G Z) (hd : 0 < δ)
    (charge : ∀ t, δ ≤ L.scale * L.charge t)
    (bound : ∀ v i, G.load v i ≤ (N : ℝ) * δ) (v : B D.scheme.m) (i : B D.scheme.h) :
    (occupiedSeats (A.live (r.2 v i))).card ≤ N := by
  let seats := occupiedSeats (A.live (r.2 v i))
  have image (j) (hj : j ∈ seats) :
      ∃ t, q.core.post.host (G.park t).1 = v ∧ q.core.post.block (G.park t).2 = i ∧ q.slot t = j := by
    obtain ⟨hn, hl⟩ := (mem_filter.mp hj).2
    obtain ⟨t | t, ht⟩ := (q.occupied (v, i, j)).mp hl
    · rw [q.internal] at ht
      exact (hn (congrArg (fun p => p.2.2) ht).symm).elim
    · rw [q.frozen] at ht
      exact ⟨t, (Prod.mk.inj ht).1, Prod.mk.inj (Prod.mk.inj ht).2⟩
  change seats.card ≤ N
  by_cases he : seats.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp he]
  -- 推导：从 `he` 中取出 `j, hj`。
  obtain ⟨j, hj⟩ := he
  obtain ⟨t, ht, ht', _⟩ := image j hj
  let p := G.park t
  let s := univ.filter fun y => G.park y = p
  have hsub : seats ⊆ s.image q.slot := by
    intro k hk
    obtain ⟨y, hy, hy', hslot⟩ := image k hk
    have hp : G.park y = p := Prod.ext (q.core.post.host.injective (hy.trans ht.symm))
      (q.core.post.block.injective (hy'.trans ht'.symm))
    exact mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hp⟩, hslot⟩
  refine ((card_le_card hsub).trans card_image_le).trans ?_
  -- 推导：记下中间结论 `hcost`：`(s.card : ℝ) * δ ≤ (N : ℝ) * δ`。
  have hcost : (s.card : ℝ) * δ ≤ (N : ℝ) * δ := calc
    _ = ∑ _ ∈ s, δ := by simp
    _ ≤ ∑ y ∈ s, L.scale * L.charge y := sum_le_sum fun y _ => charge y
    _ = L.scale * push G.park L.charge p := by
      rw [← mul_sum, push]
      simp only [s, sum_filter]
      congr 1
      apply sum_congr rfl
      intro i _
      split <;> rfl
    _ ≤ G.load p.1 p.2 := by
      unfold HostNet.load
      have := G.rate_nonneg
      exact (le_add_of_nonneg_left (by positivity)).trans (le_add_of_nonneg_right (by positivity))
    _ ≤ _ := bound _ _
  exact_mod_cast le_of_mul_le_mul_right hcost hd

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 在保持所有端口次序的条件下重标记挂接记录

**英文原文**

Relabeling attachment records without changing any port order
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment

open Coloring Packing

variable {F T : Type} {D : Template F} (A : Attachment D) (n : ℕ) (read : B n → B A.ℓ)

-- 读法：在后续公式中，`recode` 是 `k := A.k e := A.e ℓ := n decode := A.decode ∘ read live := A.live ∘ read charge := A.charge ∘ read coreSpan := A.coreSpan` 的缩写。
/-- 只有标签编码发生变化；所有局部站点索引和区段索引均予保留。

英文原文：Only the label code changes. All local station and span indices are preserved.
-/
abbrev recode : Attachment D where
  k := A.k
  e := A.e
  ℓ := n
  decode := A.decode ∘ read
  live := A.live ∘ read
  charge := A.charge ∘ read
  coreSpan := A.coreSpan

variable [Field F] [Fintype T] {x y a b : Wire} {u : ℕ} {L : Fringe x y T}
  {G : HostNet F L D.scheme.h u} {Z : Border F T a b x y} {A n read}
  {core : D.format.obj} {old : A.label.obj} {fresh : (A.recode n read).label.obj}

-- 读法：`Encloses.recode` 的结果类型为 `(A.recode n read).Encloses (core, fresh) G Z`。
def Encloses.recode (q : A.Encloses (core, old) G Z) (h : old = fun i j => read (fresh i j)) :
    (A.recode n read).Encloses (core, fresh) G Z := by
  subst old
  exact {
    full := q.full
    tether := q.tether
    core := q.core
    pres := {
      vertex := q.pres.vertex
      pin := q.pres.pin
      cover := q.pres.cover
      sample := q.pres.sample
      vacant := q.pres.vacant
      proper := q.pres.proper
      internal := q.pres.internal
      input := q.pres.input
      output := q.pres.output }
    directed := q.directed
    occupied := q.occupied
    slot := q.slot
    positive := q.positive
    internal := q.internal
    frozen := q.frozen
    charge := q.charge
    ordered := q.ordered }

variable (q : A.Encloses (core, old) G Z) (h : old = fun i j => read (fresh i j))

-- 读法：`(q.recode h).pres.vertex` 等于 `q.pres.vertex`。
-- 读法：`(q.recode h).slot` 等于 `q.slot`。
-- 读法：`(q.recode h).core` 等于 `q.core`。
@[simp] theorem Encloses.recode_core : (q.recode h).core = q.core := by subst old; rfl
@[simp] theorem Encloses.recode_slot : (q.recode h).slot = q.slot := by subst old; rfl
@[simp] theorem Encloses.recode_vertex : (q.recode h).pres.vertex = q.pres.vertex := by subst old; rfl

variable {width height : ℕ}

omit [Field F] in
include h in
-- 读法：要证明的命题是 `(A.recode n read).scheme.Fits ((A.recode n read).rows (core, fresh)) width height`。
theorem recode_fits (fit : A.scheme.Fits (A.rows (core, old)) width height) :
    (A.recode n read).scheme.Fits ((A.recode n read).rows (core, fresh)) width height := by
  subst old
  exact fit

-- 读法：`(A.recode n read).scheme.store _ (recode_fits h fit) ((q.recode h).pres.exterior i j)` 等于 `A.scheme.store _ fit (q.pres.exterior i j)`。
theorem Encloses.recode_store (fit : A.scheme.Fits (A.rows (core, old)) width height)
    (i : Val a) (j : Val b) :
    (A.recode n read).scheme.store _ (recode_fits h fit) ((q.recode h).pres.exterior i j) =
      A.scheme.store _ fit (q.pres.exterior i j) := by
  subst old
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 扩大站点的区段索引范围并保持其比特和值

**英文原文**

Enlarging a station's span index without changing its bits or value
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring
open scoped Classical

-- 读法：结构的字段包括 `width`、`value`。
structure Station (F : Type) (e : ℕ) where
  width : B e → ℕ
  value : ((Σ j, Fin (width j)) → Bool) → F

namespace Station
variable {F : Type} {d k e f : ℕ}

-- 读法：`ofPattern` 的取值由 `⟨p.width t, fun x => p.value t (fun s i => x ⟨s, i⟩)⟩` 给出。
def ofPattern (p : Pattern F d k e) (t : B k) : Station F e :=
  ⟨p.width t, fun x => p.value t (fun s i => x ⟨s, i⟩)⟩

-- 读法：`blank` 的取值由 `⟨fun _ => 0, fun _ => 1⟩` 给出。
def blank [One F] : Station F e := ⟨fun _ => 0, fun _ => 1⟩

-- 读法：在后续公式中，`Pins` 是 `Σ j, Fin (s.width j)` 的缩写。
abbrev Pins (s : Station F e) := Σ j, Fin (s.width j)

variable (s : Station F e) (index : B e ↪ B f)

-- 读法：`size` 的取值由 `Function.extend index s.width (fun _ => 0)` 给出。
private def size := Function.extend index s.width (fun _ => 0)

-- 读法：`s.size index (index i)` 等于 `s.width i`。使用 `index.injective.extend_apply` 给出的结论。
private theorem size_at (i : B e) : s.size index (index i) = s.width i :=
  index.injective.extend_apply _ _ _

-- 读法：`embed` 的结果类型为 `s.Pins ≃ (Σ j, Fin (s.size index j))`。
private def embed : s.Pins ≃ (Σ j, Fin (s.size index j)) := by
  let g : s.Pins ↪ (Σ j, Fin (s.size index j)) :=
    Function.Embedding.sigmaMap index (fun i => (finCongr (s.size_at index i).symm).toEmbedding)
  refine Equiv.ofBijective g ⟨g.injective, ?_⟩
  rintro ⟨j, i⟩
  by_cases h : j ∈ Set.range index
  · obtain ⟨t, rfl⟩ := h
    exact ⟨⟨t, i.cast (s.size_at index t)⟩, rfl⟩
  · have hz : s.size index j = 0 := Function.extend_apply' _ _ _ h
    exact Fin.elim0 (i.cast hz)

-- 读法：`enlarge` 的取值由 `⟨s.size index, fun x => s.value (x ∘ s.embed index)⟩` 给出。
def enlarge : Station F f := ⟨s.size index, fun x => s.value (x ∘ s.embed index)⟩

variable {s index} {t : Station F f} (h : t = s.enlarge index)

-- 读法：`ports` 的取值由 `h.symm ▸ s.embed index` 给出。
def ports : s.Pins ≃ t.Pins := h.symm ▸ s.embed index

-- 读法：`(ports h j).1 = index j.1` 与 `(ports h j).2.val = j.2.val` 同时成立。
theorem ports_at (j : s.Pins) :
    (ports h j).1 = index j.1 ∧ (ports h j).2.val = j.2.val := by
  subst t
  exact ⟨rfl, rfl⟩

-- 读法：`t.value x` 等于 `s.value (x ∘ ports h)`。
theorem eval_at (x : t.Pins → Bool) : t.value x = s.value (x ∘ ports h) := by
  subst t
  rfl

include h in
-- 读法：`t.width (index j)` 等于 `s.width j`。
theorem width_at (j : B e) : t.width (index j) = s.width j := by rw [h]; exact s.size_at index j

end Station
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 重新挂接后的出现位置标签

每个出现位置选取一张核心表。每个冻结站点保留原来的表选择器和站点编号。新的对端索引指向公共邻居列表，自身不携带全局宿主名称。

**英文原文**

The label of a reattached occurrence

One core table is selected per occurrence. Each frozen station keeps
its old table selector and station number. New peer indices refer to
a common neighbor list and carry no global host names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing
open scoped Classical

variable {F : Type} {D : Template F} (A : Attachment D) (Y : Template F) (k : ℕ)

-- 读法：在后续公式中，`spanBits` 是 `max A.e Y.scheme.e` 的缩写。
abbrev spanBits := max A.e Y.scheme.e
-- 读法：`inner` 的取值由 `Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (le_max_right ..))` 给出。
def inner : B Y.scheme.e ↪ B (A.spanBits Y) := Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (le_max_right ..))
-- 读法：`outer` 的取值由 `Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (le_max_left ..))` 给出。
def outer : B A.e ↪ B (A.spanBits Y) := Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (le_max_left ..))

-- 读法：在后续公式中，`member` 是 `Format.pair .bit (.pair (.addr A.ℓ) (.addr A.k))` 的缩写。
abbrev member := Format.pair .bit (.pair (.addr A.ℓ) (.addr A.k))
-- 读法：在后续公式中，`endpoint` 是 `Format.pair (.addr Y.scheme.d) (.pair (.addr k) (.addr (A.spanBits Y)))` 的缩写。
abbrev endpoint := Format.pair (.addr Y.scheme.d) (.pair (.addr k) (.addr (A.spanBits Y)))
-- 读法：在后续公式中，`contact` 是 `Format.pair .bit (.pair .bit (A.endpoint Y k))` 的缩写。
abbrev contact := Format.pair .bit (.pair .bit (A.endpoint Y k))
-- 读法：在后续公式中，`record` 是 `Format.pair (.addr Y.scheme.ℓ) (.vec k (A.member.pair (.vec (A.spanBits Y) (A.contact Y k))))` 的缩写。
abbrev record := Format.pair (.addr Y.scheme.ℓ) (.vec k (A.member.pair (.vec (A.spanBits Y) (A.contact Y k))))

-- 读法：在后续公式中，`Links` 是 `Place Y k × B (A.spanBits Y) → Bool × Option (A.endpoint Y k).obj` 的缩写。
abbrev Links := Place Y k × B (A.spanBits Y) → Bool × Option (A.endpoint Y k).obj

-- 读法：`point` 的取值由 `(p.1, p.2.isSome, p.2.getD (0, 0, 0))` 给出。
def point (p : Bool × Option (A.endpoint Y k).obj) : (A.contact Y k).obj :=
  (p.1, p.2.isSome, p.2.getD (0, 0, 0))

variable [Field F]

-- 读法：`station` 的结果类型为 `Station F (A.spanBits Y)`。
def station (r : (A.record Y k).obj) (j : B k) : Station F (A.spanBits Y) :=
  let t := (r.2 j).1
  if t.1 then
    if j = 0 then (Station.ofPattern (Y.scheme.decode r.1) 0).enlarge (A.inner Y)
    else (Station.ofPattern (A.decode t.2.1) t.2.2).enlarge (A.outer Y)
  else Station.blank

-- 读法：用字段 `width`、`direction`、`peer`、`value` 构造 `Pattern F Y.scheme.d k (A.spanBits Y)`。
def pattern (r : (A.record Y k).obj) : Pattern F Y.scheme.d k (A.spanBits Y) where
  width j := (A.station Y k r j).width
  direction j l := ((r.2 j).2 l).1
  peer j l :=
    let p := (r.2 j).2 l
    if p.2.1 ∧ 0 < (A.station Y k r j).width l then some p.2.2 else none
  value j x := (A.station Y k r j).value (fun p => x p.1 p.2)

-- 读法：用字段 `k`、`e`、`ℓ`、`decode` 构造 `Attachment Y`。
abbrev transport : Attachment Y where
  k := k
  e := A.spanBits Y
  ℓ := (A.record Y k).width
  decode := A.pattern Y k ∘ (A.record Y k).serial.symm
  live i j := (((A.record Y k).serial.symm i).2 j).1.1
  charge i j :=
    let t := (((A.record Y k).serial.symm i).2 j).1
    if j ≠ 0 ∧ t.1 then A.charge t.2.1 t.2.2 else 0
  coreSpan := A.inner Y

namespace Relocation
variable {A Y k} (R : A.Relocation Y k) (r : A.format.obj) (s : Y.format.obj)
    (active : B Y.scheme.m → B Y.scheme.h → Bool) (links : A.Links Y k)

-- 读法：`origin` 的取值由 `if j.2.2 = 0 then (active j.1 j.2.1, 0, 0) else (R.kept r j).elim (false, 0, 0) (fun v => (true, r.2 v.1 v.2.1, v.2.2))` 给出。
def origin (j : Place Y k) : A.member.obj :=
  if j.2.2 = 0 then (active j.1 j.2.1, 0, 0) else
    (R.kept r j).elim (false, 0, 0) (fun v => (true, r.2 v.1 v.2.1, v.2.2))

-- 读法：`localRecord` 的取值由 `((s.1 i).2 t, fun j => (R.origin r active (i, t, j), fun l => A.point Y k (links ((i, t, j), l))))` 给出。
def localRecord (i : B Y.scheme.m) (t : B Y.scheme.h) : (A.record Y k).obj :=
  ((s.1 i).2 t, fun j => (R.origin r active (i, t, j), fun l => A.point Y k (links ((i, t, j), l))))

-- 读法：`write` 的取值由 `(s, fun i t => (A.record Y k).serial (R.localRecord r s active links i t))` 给出。
def write : (A.transport Y k).format.obj :=
  (s, fun i t => (A.record Y k).serial (R.localRecord r s active links i t))

local notation "U" => A.transport Y k
local notation "w" => R.write r s active links
local notation "out" => rows U w

-- 读法：`Station.ofPattern ((U).scheme.pattern out j) j.2.2` 等于 `A.station Y k (R.localRecord r s active links j.1 j.2.1) j.2.2`。
theorem shape (j : Place Y k) :
    Station.ofPattern ((U).scheme.pattern out j) j.2.2 =
      A.station Y k (R.localRecord r s active links j.1 j.2.1) j.2.2 := by
  change Station.ofPattern (A.pattern Y k ((A.record Y k).serial.symm ((A.record Y k).serial _))) _ = _
  rw [Equiv.symm_apply_apply]
  rfl

-- 读法：`(U).live ((w).2 j.1 j.2.1) j.2.2` 等于 `(R.origin r active j).1`。
theorem live_at (j : Place Y k) :
    (U).live ((w).2 j.1 j.2.1) j.2.2 = (R.origin r active j).1 := by
  simp only [transport, write, Equiv.symm_apply_apply]
  rfl

-- 读法：`(U).scheme.direction out j` 等于 `(links j).1`。
theorem direction_at (j : (U).scheme.Span) : (U).scheme.direction out j = (links j).1 := by
  simp only [Scheme.direction, Scheme.pattern, scheme, rows, transport, write, Function.comp_apply, Equiv.symm_apply_apply]
  rfl

-- 读法：`resolve` 的取值由 `((Y.nav s j.1 p.1, j.2.1, p.2.1), p.2.2)` 给出。
def resolve (j : Place Y k) (p : (A.endpoint Y k).obj) : (U).scheme.Span :=
  ((Y.nav s j.1 p.1, j.2.1, p.2.1), p.2.2)

-- 读法：`(U).scheme.peer out j` 等于 `if 0 < (U).scheme.width out j then (links j).2.map (resolve s j.1) else none`。
theorem peer_at (j : (U).scheme.Span) : (U).scheme.peer out j =
    if 0 < (U).scheme.width out j then (links j).2.map (resolve s j.1) else none := by
  simp only [Scheme.peer, Scheme.width, Scheme.pattern, scheme, rows, transport, write, Function.comp_apply, Equiv.symm_apply_apply]
  let u := A.station Y k (R.localRecord r s active links j.1.1 j.1.2.1) j.1.2.2
  change (if (links j).2.isSome ∧ 0 < u.width j.2 then some ((links j).2.getD (0, 0, 0)) else none).map
    (resolve s j.1) = if 0 < u.width j.2 then (links j).2.map (resolve s j.1) else none
  cases (links j).2 <;> by_cases h : 0 < u.width j.2 <;> simp [h]

end Relocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 寻找系接线的新对端

核心的外部区段指向其原核心区段。冻结区段则指向其原站点并保留区段编号。沿新的邻居列表，将这些名称与原对端名称比较。

**英文原文**

Finding the new peer of a tether

A core exterior span points to its previous core span. A frozen
span points to its previous station and keeps its span number.
Compare these names to the old peer name over the new neighbor list.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} {D Y : Template F} (A : Attachment D) {k m : ℕ}

-- 读法：`fromCore` 的取值由 `((j.1.1, j.1.2.1, 0), A.coreSpan j.2)` 给出。
def fromCore (j : D.scheme.Span) : A.scheme.Span :=
  ((j.1.1, j.1.2.1, 0), A.coreSpan j.2)

namespace Relocation
variable [Field F] {A} (R : A.Relocation Y k) (r : A.format.obj) (s : Y.format.obj)
    (M : Trail.Move D.scheme Y.scheme m)

local notation "U" => A.transport Y k
local notation "Sp" => Scheme.Span (scheme U)

-- 读法：`previous` 的结果类型为 `Option A.scheme.Span`。
def previous (j : Sp) : Option A.scheme.Span :=
  if j.1.2.2 = 0 then
    Function.extend (A.inner Y) (fun t => (M.previous ((j.1.1, j.1.2.1, 0), t)).map A.fromCore)
      (fun _ => none) j.2
  else Function.extend (A.outer Y) (fun t => (R.kept r j.1).map (fun z => (z, t))) (fun _ => none) j.2

-- 读法：当 `h : ∃ i, test i = true` 成立时取 `some h.choose`，否则取 `none`。
def seek {X : Type} (test : X → Bool) : Option X :=
  if h : ∃ i, test i = true then some h.choose else none

-- 读法：`internal` 的结果类型为 `Bool × Option (A.endpoint Y k).obj`。
def internal (j : Sp) : Bool × Option (A.endpoint Y k).obj :=
  let p := Y.scheme.decode ((s.1 j.1.1).2 j.1.2.1)
  Function.extend (A.inner Y) (fun t =>
    (p.direction 0 t, (p.peer 0 t).map (fun x => (x.1, 0, A.inner Y x.2.2)))) (fun _ => (false, none)) j.2

-- 读法：`links` 的结果类型为 `A.Links Y k`。
def links : A.Links Y k := fun j =>
  match R.previous r M j with
  | none => internal s j
  | some w => (A.scheme.direction (A.rows r) w, (A.scheme.peer (A.rows r) w).bind fun v =>
      seek (fun i => decide (R.previous r M (resolve s j.1 i) = some v)))

-- 读法：`R.previous r M ((U).fromCore j)` 等于 `(M.previous j).map A.fromCore`。
theorem previous_core (j : Y.scheme.Span) (h : j.1.2.2 = 0) :
    R.previous r M ((U).fromCore j) = (M.previous j).map A.fromCore := by
  rcases j with ⟨⟨x, y, z⟩, t⟩
  change z = 0 at h
  subst z
  simp only [previous, fromCore, ↓reduceIte, transport, (A.inner Y).injective.extend_apply]

-- 读法：`R.previous r M (j, A.outer Y t)` 等于 `(R.kept r j).map (fun z => (z, t))`。
theorem previous_frozen (j : Place Y k) (t : B A.e) (h : j.2.2 ≠ 0) :
    R.previous r M (j, A.outer Y t) = (R.kept r j).map (fun z => (z, t)) := by
  unfold previous
  rw [ite_eq_right h, (A.outer Y).injective.extend_apply]

-- 读法：结论为 `let p := (U).fromCore j (R.links r s M p).1 = Y.scheme.direction s.1 j ∧ (R.links r s M p).2.map (resolve s p.1) = (Y.scheme.peer s.1 j).map (U).fromCore`。
theorem native (j : Y.scheme.Span) (hz : j.1.2.2 = 0) (he : M.previous j = none) :
    let p := (U).fromCore j
    (R.links r s M p).1 = Y.scheme.direction s.1 j ∧
      (R.links r s M p).2.map (resolve s p.1) = (Y.scheme.peer s.1 j).map (U).fromCore := by
  intro p
  have hp : R.previous r M p = none := by rw [show p = (U).fromCore j from rfl, previous_core _ _ _ _ hz, he]; rfl
  simp only [links, hp, internal]
  rcases j with ⟨⟨x, y, z⟩, t⟩
  change z = 0 at hz
  subst z
  simp only [p, fromCore, transport, (A.inner Y).injective.extend_apply, Scheme.direction, Scheme.pattern, Scheme.peer]
  cases (Y.scheme.decode ((s.1 x).2 y)).peer 0 t <;> exact ⟨True.intro, rfl⟩

-- 读法：`R.links r s M j` 等于 `(A.scheme.direction (A.rows r) w, none)`。
theorem detached {j : Sp} {w : A.scheme.Span} (hj : R.previous r M j = some w)
    (he : A.scheme.peer (A.rows r) w = none) :
    R.links r s M j = (A.scheme.direction (A.rows r) w, none) := by
  simp only [links, hj, he, Option.bind_none]

-- 读法：`(R.links r s M j).1 = A.scheme.direction (A.rows r) w` 与 `(R.links r s M j).2.map (resolve s j.1) = some l` 同时成立。
theorem linked {j l : Sp} {w v : A.scheme.Span} (hj : R.previous r M j = some w)
    (he : A.scheme.peer (A.rows r) w = some v)
    (hl : ∀ x, R.previous r M x = some v ↔ x = l)
    (reach : ∃ i, resolve s j.1 i = l) :
    (R.links r s M j).1 = A.scheme.direction (A.rows r) w ∧
      (R.links r s M j).2.map (resolve s j.1) = some l := by
  simp only [links, hj, he, Option.bind_some, true_and]
  have hit : ∃ i, decide (R.previous r M (resolve s j.1 i) = some v) = true := by
    simpa only [decide_eq_true_eq, hl] using reach
  rw [seek, dite_eq_left hit, Option.map_some]
  exact congrArg some ((hl _).mp (of_decide_eq_true hit.choose_spec))

end Relocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 移动挂接后被占用的站点槽位

**英文原文**

Occupied station slots in a moved attachment
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {D Y : Template F} {A : Attachment D} {k : ℕ}
  {x y a b : Wire} {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} (p : Y.Encodes s H) (slot : T → B k)

-- 读法：`WriteActive` 表示以下条件：对每个 `i j`，`live i j = true` 与 `(i, j, 0) ∈ Set.range p.post.vertex` 等价。
def WriteActive (live : B Y.scheme.m → B Y.scheme.h → Bool) : Prop :=
  ∀ i j, live i j = true ↔ (i, j, 0) ∈ Set.range p.post.vertex

-- 读法：`core` 的取值由 `(p.post.host (H.units.place i).1, p.post.block (H.units.place i).2, 0)` 给出。
def core (i : H.diagram.V) : Place Y k := (p.post.host (H.units.place i).1, p.post.block (H.units.place i).2, 0)
-- 读法：`frozen` 的取值由 `(p.post.host (H.park t).1, p.post.block (H.park t).2, slot t)` 给出。
def frozen (t : T) : Place Y k := (p.post.host (H.park t).1, p.post.block (H.park t).2, slot t)

namespace Moves
variable {p slot} (h : R.Moves q p slot)

include h in
-- 读法：`R.kept r (frozen p slot t)` 等于 `some (q.pres.vertex (.inr t))`。使用 `R.kept_iff` 给出的结论。
theorem kept_at (t : T) : R.kept r (frozen p slot t) = some (q.pres.vertex (.inr t)) :=
  (R.kept_iff q p slot h _ t).mpr rfl

-- 读法：用字段 `toFun`、`inj'` 构造 `(Z.attach H.diagram).V ↪ Place Y k`。
def vertex : (Z.attach H.diagram).V ↪ Place Y k where
  toFun := Sum.elim (core p) (frozen p slot)
  inj' := by
    rintro (i|t) (j|w) he
    · have hi := congrArg (fun x : Place Y k => (x.1, x.2.1, (0 : B Y.scheme.k))) he
      exact congrArg Sum.inl (p.post.vertex.injective ((p.post.vertex_eq i).trans (hi.trans (p.post.vertex_eq j).symm)))
    · exact (h.positive w (congrArg (fun x => x.2.2) he).symm).elim
    · exact (h.positive t (congrArg (fun x => x.2.2) he)).elim
    · exact congrArg Sum.inr (Sum.inr.inj (q.pres.vertex.injective (Option.some.inj
        ((h.kept_at t).symm.trans ((congrArg (R.kept r) he).trans (h.kept_at w))))))

variable {live : B Y.scheme.m → B Y.scheme.h → Bool} (ok : WriteActive p live)
  (links : A.Links Y k)

include ok in
-- 读法：`R.origin r live (h.vertex (.inl i))` 等于 `(true, 0, 0)`。
theorem core_origin (i : H.diagram.V) : R.origin r live (h.vertex (.inl i)) = (true, 0, 0) := by
  have he := (ok _ _).mpr ⟨i, p.post.vertex_eq i⟩
  change R.origin r live (core p i) = _
  simp only [origin, core, ↓reduceIte, he]

-- 读法：`R.origin r live (h.vertex (.inr t))` 等于 `(true, r.2 (q.pres.vertex (.inr t)).1 (q.pres.vertex (.inr t)).2.1, (q.pres.vertex (.inr t)).2.2)`。
theorem frozen_origin (t : T) :
    R.origin r live (h.vertex (.inr t)) =
      (true, r.2 (q.pres.vertex (.inr t)).1 (q.pres.vertex (.inr t)).2.1, (q.pres.vertex (.inr t)).2.2) := by
  change R.origin r live (frozen p slot t) = _
  rw [origin, ite_eq_right (show (frozen p slot t).2.2 ≠ 0 from h.positive t), h.kept_at]
  rfl

include ok in
-- 读法：`(R.origin r live j).1 = true` 与 `j ∈ Set.range h.vertex` 等价。按 `j.2.2 = 0` 成立与否分情况。
theorem in_range (j : Place Y k) : (R.origin r live j).1 = true ↔ j ∈ Set.range h.vertex := by
  constructor
  · intro hj
    by_cases hz : j.2.2 = 0
    · rw [origin, ite_eq_left hz] at hj
      obtain ⟨i, hi⟩ := (ok _ _).mp hj
      rw [p.post.vertex_eq] at hi
      have hi₁ := congrArg Prod.fst hi
      have hi₂ := congrArg (fun x => x.2.1) hi
      exact ⟨.inl i, Prod.ext hi₁ (Prod.ext hi₂ hz.symm)⟩
    · rw [origin, ite_eq_right hz] at hj
      cases he : R.kept r j with
      | none => rw [he] at hj; cases hj
      | some z =>
        obtain ⟨t, rfl⟩ := R.active q j z he
        exact ⟨.inr t, ((R.kept_iff q p slot h j t).mp he).symm⟩
  · rintro ⟨i|t, rfl⟩
    · rw [h.core_origin ok]
    · rw [h.frozen_origin]

include h in
-- 读法：要证明的命题是 `(A.transport Y k).charge ((R.write r s live links).2 (p.post.host (H.park t).1) (p.post.block (H.park t).2)) (slot t) = L.charge t`。这里调用 `q.charge`。
theorem charge (t : T) : (A.transport Y k).charge ((R.write r s live links).2
    (p.post.host (H.park t).1) (p.post.block (H.park t).2)) (slot t) = L.charge t := by
  simp only [transport, write, Equiv.symm_apply_apply, localRecord]
  have he := h.frozen_origin (live := live) t
  rw [q.frozen] at he
  change R.origin r live (_, _, _) = _ at he
  rw [he, ite_eq_left ⟨h.positive t, rfl⟩]
  exact q.charge t

end Moves
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation
end

/-!
# 针对原挂接记录的短查询

每个新核心区段和每个候选冻结站点至多读取一个原标签。查询中的宿主索引指向一份公共来源列表，其中包括父宿主自身。

**英文原文**

Short queries for the old attachment records

Each new core span and each candidate frozen station reads at most
one old label. A host index on a query refers to a shared list of
sources, including the parent itself.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} {D Y : Template F} (A : Attachment D) (Y : Template F) (k p : ℕ)

-- 读法：在后续公式中，`depth` 是 `max Y.scheme.e k + 1` 的缩写。
abbrev depth := max Y.scheme.e k + 1
-- 读法：在后续公式中，`Item` 是 `B Y.scheme.e ⊕ B k` 的缩写。
abbrev Item := B Y.scheme.e ⊕ B k

-- 读法：`request` 的结果类型为 `Item Y k ↪ B (depth Y k)`。
def request : Item Y k ↪ B (depth Y k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simp only [Fintype.card_sum, Fintype.card_fin, depth, pow_succ]
    rw [Nat.mul_two]
    exact Nat.add_le_add (Nat.pow_le_pow_right (by decide) (le_max_left ..))
      (Nat.pow_le_pow_right (by decide) (le_max_right ..))))

-- 读法：在后续公式中，`orders` 是 `Format.pair (.vec Y.scheme.e (Trail.pointer D.scheme p)) (.vec k A.pointer)` 的缩写。
abbrev orders := Format.pair (.vec Y.scheme.e (Trail.pointer D.scheme p)) (.vec k A.pointer)
-- 读法：在后续公式中，`ticket` 是 `Format.pair (.addr Y.scheme.ℓ) (.pair .bit (A.orders Y k p))` 的缩写。
abbrev ticket := Format.pair (.addr Y.scheme.ℓ) (.pair .bit (A.orders Y k p))
-- 读法：在后续公式中，`ask` 是 `Format.vec (depth Y k) (.pair (.addr p) (.addr D.scheme.h))` 的缩写。
abbrev ask := Format.vec (depth Y k) (.pair (.addr p) (.addr D.scheme.h))
-- 读法：在后续公式中，`bundle` 是 `(A.ticket Y k p).pair (.vec (depth Y k) (.addr A.ℓ))` 的缩写。
abbrev bundle := (A.ticket Y k p).pair (.vec (depth Y k) (.addr A.ℓ))

variable {Y k p}

-- 读法：`question` 的结果类型为 `(ask (D := D) Y k p).obj`。
def question (self : B p) (x : (A.ticket Y k p).obj) : (ask (D := D) Y k p).obj :=
  Function.extend (request Y k) (Sum.elim
    (fun i => ((x.2.2.1 i).2.1, (x.2.2.1 i).2.2.1))
    (fun j => (self, (x.2.2.2 j).2.1))) (fun _ => (self, 0))

variable {A}

-- 读法：结构的字段包括 `R`、`M`、`old`、`fresh`、`active`。
structure Query (A : Attachment D) (Y : Template F) (k p : ℕ) where
  R : A.Relocation Y k
  M : Trail.Move D.scheme Y.scheme p
  old : A.format.obj
  fresh : Y.format.obj
  active : B Y.scheme.m → B Y.scheme.h → Bool

namespace Query
variable (q : Query A Y k p) (self : B p) (i : B Y.scheme.m) (j : B Y.scheme.h)

-- 读法：`ticketAt` 的取值由 `((q.fresh.1 i).2 j, q.active i j, q.M.commands i j 0, q.R.flags i j)` 给出。
def ticketAt : (A.ticket Y k p).obj :=
  ((q.fresh.1 i).2 j, q.active i j, q.M.commands i j 0, q.R.flags i j)

-- 读法：`received` 的取值由 `(q.ticketAt i j, fun a => let b := A.question self (q.ticketAt i j) a q.old.2 (q.M.nav i b.1) b.2)` 给出。
def received : (A.bundle Y k p).obj :=
  (q.ticketAt i j, fun a =>
    let b := A.question self (q.ticketAt i j) a
    q.old.2 (q.M.nav i b.1) b.2)

-- 读法：`(q.received self i j).2 (request Y k (.inl l))` 等于 `q.old.2 (q.M.nav i w.1) w.2.1`。
theorem answer_core (l : B Y.scheme.e) (w : B p × Trail.Stub D.scheme)
    (hw : q.M.read ((i, j, 0), l) = some w) :
    (q.received self i j).2 (request Y k (.inl l)) = q.old.2 (q.M.nav i w.1) w.2.1 := by
  simp only [received, question, (request Y k).injective.extend_apply, Sum.elim_inl, ticketAt, Trail.Move.commands, hw]
  rfl

-- 读法：`(q.received self i j).2 (request Y k (.inr l))` 等于 `q.old.2 (q.R.parent i) w.1`。
theorem answer_slot (hl : q.M.nav i self = q.R.parent i) (l : B k) (w : B D.scheme.h × B A.k)
    (hw : q.R.prev i j l = some w) :
    (q.received self i j).2 (request Y k (.inr l)) = q.old.2 (q.R.parent i) w.1 := by
  simp only [received, question, (request Y k).injective.extend_apply, Sum.elim_inr, ticketAt, Relocation.flags, hw, hl]
  rfl

end Query
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 保留边界和新核心各自的引脚双射

**英文原文**

Pin bijections for the retained border and the new core
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing
open scoped Classical

-- 读法：`atVertex` 的取值由 `Station.ofPattern (S.pattern s i) i.2.2` 给出。
def atVertex {F : Type} (S : Scheme F) (s : S.format.obj) (i : S.Vtx) :=
  Station.ofPattern (S.pattern s i) i.2.2

namespace Relocation.Moves
variable {F T : Type} [Field F] [Fintype T] {D Y : Template F} {A : Attachment D} {k : ℕ}
  {x y a b : Wire} {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}
  (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) (links : A.Links Y k)

local notation "W" => scheme (A.transport Y k)
local notation "out" => rows (A.transport Y k) (R.write r s live links)

include ok in
-- 读法：`atVertex W out (h.vertex (.inl i))` 等于 `(atVertex Y.scheme s.1 (p.post.vertex i)).enlarge (A.inner Y)`。
theorem core_shape (i : H.diagram.V) :
    atVertex W out (h.vertex (.inl i)) =
      (atVertex Y.scheme s.1 (p.post.vertex i)).enlarge (A.inner Y) := by
  unfold atVertex
  rw [R.shape, p.post.vertex_eq]
  simp only [station, localRecord, Prod.mk.eta, h.core_origin ok, ↓reduceIte]
  rfl

-- 读法：`atVertex W out (h.vertex (.inr i))` 等于 `(atVertex A.scheme (A.rows r) (q.pres.vertex (.inr i))).enlarge (A.outer Y)`。
theorem outer_shape (i : T) :
    atVertex W out (h.vertex (.inr i)) =
      (atVertex A.scheme (A.rows r) (q.pres.vertex (.inr i))).enlarge (A.outer Y) := by
  unfold atVertex
  rw [R.shape]
  have hi : (h.vertex (.inr i)).2.2 ≠ 0 := h.positive i
  simp only [station, localRecord, Prod.mk.eta, h.frozen_origin, ite_eq_right hi, ↓reduceIte]
  rfl

include ok in
-- 读法：`atVertex W out j` 等于 `Station.blank`。
theorem blank_shape (j : Place Y k) (hj : j ∉ Set.range h.vertex) :
    atVertex W out j = Station.blank := by
  unfold atVertex
  rw [R.shape]
  have hf := mt (h.in_range ok j).mp hj
  simp only [station, localRecord, Prod.mk.eta, ite_eq_right hf]

-- 读法：用字段 `vertex`、`cover`、`have`、`sample` 构造 `(W).Seating out (Z.attach H.diagram)`。
def seating : (W).Seating out (Z.attach H.diagram) where
  vertex := h.vertex
  pin
    | .inl i => (p.post.pin i).trans (Station.ports (h.core_shape ok links i))
    | .inr i => (q.pres.pin (.inr i)).trans (Station.ports (h.outer_shape links i))
  cover j := by
    by_contra! he
    have ht := h.blank_shape ok links j.1.1 (by rintro ⟨a, ha⟩; exact he a ha)
    have hw : (W).width out j.1 = 0 := congrArg (fun c => c.width j.1.2) ht
    exact Fin.elim0 (j.2.cast hw)
  sample := by
    rintro (v|t) q'
    · exact (Station.eval_at (h.core_shape ok links v) q').trans (p.post.sample v _)
    · exact (Station.eval_at (h.outer_shape links t) q').trans (q.pres.sample (.inr t) _)
  vacant j hj := by
    change ∀ t, (atVertex W out j).value t = 1
    rw [h.blank_shape ok links j hj]
    exact fun _ => rfl

-- 读法：`((h.seating ok links).pin (.inl i) j).1 = A.inner Y (p.post.pin i j).1` 与 `((h.seating ok links).pin (.inl i) j).2.val = (p.post.pin i j).2.val` 同时成立。使用 `Station.ports_at` 给出的结论。
theorem core_pin (i : H.diagram.V) (j : H.diagram.Port i) :
    ((h.seating ok links).pin (.inl i) j).1 = A.inner Y (p.post.pin i j).1 ∧
    ((h.seating ok links).pin (.inl i) j).2.val = (p.post.pin i j).2.val :=
  Station.ports_at (h.core_shape ok links i) (p.post.pin i j)

-- 读法：`((h.seating ok links).pin (.inr i) j).1 = A.outer Y (q.pres.pin (.inr i) j).1` 与 `((h.seating ok links).pin (.inr i) j).2.val = (q.pres.pin (.inr i) j).2.val` 同时成立。使用 `Station.ports_at` 给出的结论。
theorem outer_pin (i : T) (j : (Z.attach G.diagram).Port (.inr i)) :
    ((h.seating ok links).pin (.inr i) j).1 = A.outer Y (q.pres.pin (.inr i) j).1 ∧
    ((h.seating ok links).pin (.inr i) j).2.val = (q.pres.pin (.inr i) j).2.val :=
  Station.ports_at (h.outer_shape links i) (q.pres.pin (.inr i) j)

end Relocation.Moves
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 从挂接处两侧追踪有序比特

**英文原文**

Following the ordered bits from both sides of an attachment
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Coloring Packing
open scoped Classical

variable {F T : Type} [Fintype T] {x y a b : Wire}

namespace Packing.Border
variable (Z : Border F T a b x y) (G : Diagram F x y)

-- 读法：逐一匹配以下输入模式：`.inl (.inl i)`、`.inr (.inl i)`、`.inl (.inr e)`、`.inr (.inr e)`。
def coreEnd : G.End → (Z.attach G).End
  | .inl (.inl i) => .inl (.inr (.inr (.inl i)))
  | .inr (.inl i) => .inr (.inr (.inr (.inr i)))
  | .inl (.inr e) => .inl (.inr (.inl e))
  | .inr (.inr e) => .inr (.inr (.inl e))

-- 读法：`Z.coreEnd G (G.portEquiv ⟨i, j⟩)` 等于 `(Z.attach G).portEquiv ⟨.inl i, j⟩`。
theorem core_port (i : G.V) (j : G.Port i) :
    Z.coreEnd G (G.portEquiv ⟨i, j⟩) = (Z.attach G).portEquiv ⟨.inl i, j⟩ := by
  rcases j with j|j
  · change Z.coreEnd G (.inl (G.src ⟨i, j⟩)) = .inl (merge _ _ _ _ (.inl (G.src ⟨i, j⟩)))
    cases G.src ⟨i, j⟩ <;> rfl
  · change Z.coreEnd G (.inr (G.dst ⟨i, j⟩)) =
      .inr (Sum.map id (Sum.map id Sum.swap) (merge _ _ _ _ (.inl (G.dst ⟨i, j⟩))))
    cases G.dst ⟨i, j⟩ <;> rfl

-- 读法：在后续公式中，`Ends` 是 `(slots a ⊕ slots y) ⊕ (slots b ⊕ slots x)` 的缩写。
abbrev Ends (a b x y : Wire) := (slots a ⊕ slots y) ⊕ (slots b ⊕ slots x)

-- 读法：逐一匹配以下输入模式：`.inl (.inl i)`、`.inr (.inl i)`、`.inl (.inr i)`、`.inr (.inr i)`。
def outerEnd : Ends a b x y → (Z.attach G).End
  | .inl (.inl i) => .inl (.inl i)
  | .inr (.inl i) => .inr (.inl i)
  | .inl (.inr i) => .inl (.inr (.inr (.inr i)))
  | .inr (.inr i) => .inr (.inr (.inr (.inl i)))

-- 读法：`ports` 的取值由 `(Equiv.sigmaSumDistrib _ _).trans (Z.src.sumCongr Z.dst)` 给出。
def ports : (Σ i, Transcript.Ports (Z.table i)) ≃ Ends a b x y :=
  (Equiv.sigmaSumDistrib _ _).trans (Z.src.sumCongr Z.dst)

-- 读法：`owner` 的取值由 `(Z.ports.symm i).1` 给出。
def owner (i : Ends a b x y) := (Z.ports.symm i).1

-- 读法：`Z.outerEnd G (Z.ports ⟨i, j⟩)` 等于 `(Z.attach G).portEquiv ⟨.inr i, j⟩`。
theorem outer_port (i : T) (j : Transcript.Ports (Z.table i)) :
    Z.outerEnd G (Z.ports ⟨i, j⟩) = (Z.attach G).portEquiv ⟨.inr i, j⟩ := by
  rcases j with j|j
  · change Z.outerEnd G (.inl (Z.src ⟨i, j⟩)) = .inl (merge _ _ _ _ (.inr (Z.src ⟨i, j⟩)))
    cases Z.src ⟨i, j⟩ <;> rfl
  · change Z.outerEnd G (.inr (Z.dst ⟨i, j⟩)) =
      .inr (Sum.map id (Sum.map id Sum.swap) (merge _ _ _ _ (.inr (Z.dst ⟨i, j⟩))))
    cases Z.dst ⟨i, j⟩ <;> rfl

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr i`。
def other : slots x ⊕ slots y → Ends a b x y
  | .inl i => .inr (.inr i)
  | .inr i => .inl (.inr i)

omit [Fintype T] in
-- 读法：`Z.owner (other i)` 等于 `Z.tensor i`。
theorem owner_other (i : slots x ⊕ slots y) : Z.owner (other i) = Z.tensor i := by cases i <;> rfl

end Packing.Border

namespace Assembly.Attachment
variable [Field F] {D Y : Template F} {A : Attachment D} {k : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} (q : A.Encloses r G Z) {p : Y.Encodes s H} {slot : T → B k}

-- 读法：结论为 `let e := q.pres.toSeating.ends (Z.coreEnd G.diagram i) let f := q.core.post.toSeating.ends i e.1 = A.fromCore f.1 ∧ e.2.val = f.2.val`。
theorem Encloses.core_end (i : G.diagram.End) :
    let e := q.pres.toSeating.ends (Z.coreEnd G.diagram i)
    let f := q.core.post.toSeating.ends i
    e.1 = A.fromCore f.1 ∧ e.2.val = f.2.val := by
  obtain ⟨⟨w, j⟩, rfl⟩ := G.diagram.portEquiv.surjective i
  erw [Z.core_port, q.pres.toSeating.ends_at, q.core.post.toSeating.ends_at]
  have hv := q.internal w
  have hp := q.core.post.vertex_eq w
  exact ⟨Prod.ext (hv.trans (congrArg (fun z => (z.1, z.2.1, (0 : B A.k))) hp.symm))
    (q.ordered w j).1, (q.ordered w j).2⟩

-- 读法：`(q.pres.toSeating.ends (Z.outerEnd G.diagram i)).1.1` 等于 `q.pres.vertex (.inr (Z.owner i))`。
theorem Encloses.outer_end (i : Border.Ends a b x y) :
    (q.pres.toSeating.ends (Z.outerEnd G.diagram i)).1.1 = q.pres.vertex (.inr (Z.owner i)) := by
  obtain ⟨⟨w, j⟩, rfl⟩ := Z.ports.surjective i
  erw [Z.outer_port, q.pres.toSeating.ends_at, Border.owner, Equiv.symm_apply_apply]
  rfl

namespace Relocation.Moves
variable {q} (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) (links : A.Links Y k)

-- 读法：结论为 `let e := (h.seating ok links).ends (Z.coreEnd H.diagram i) let f := p.post.toSeating.ends i e.1 = (A.transport Y k).fromCore f.1 ∧ e.2.val = f.2.val`。
theorem core_end (i : H.diagram.End) :
    let e := (h.seating ok links).ends (Z.coreEnd H.diagram i)
    let f := p.post.toSeating.ends i
    e.1 = (A.transport Y k).fromCore f.1 ∧ e.2.val = f.2.val := by
  obtain ⟨⟨w, j⟩, rfl⟩ := H.diagram.portEquiv.surjective i
  erw [Z.core_port, (h.seating ok links).ends_at, p.post.toSeating.ends_at]
  have hv := congrArg (fun z => (z.1, z.2.1, (0 : B k))) (p.post.vertex_eq w).symm
  exact ⟨Prod.ext hv (h.core_pin ok links w j).1, (h.core_pin ok links w j).2⟩

-- 读法：结论为 `let e := (h.seating ok links).ends (Z.outerEnd H.diagram i) let f := q.pres.toSeating.ends (Z.outerEnd G.diagram i) e.1 = (frozen p slot (Z.owner i), A.outer Y f.1.2) ∧ e.2.val = f.2.val`。
theorem outer_end (i : Border.Ends a b x y) :
    let e := (h.seating ok links).ends (Z.outerEnd H.diagram i)
    let f := q.pres.toSeating.ends (Z.outerEnd G.diagram i)
    e.1 = (frozen p slot (Z.owner i), A.outer Y f.1.2) ∧ e.2.val = f.2.val := by
  obtain ⟨⟨w, j⟩, rfl⟩ := Z.ports.surjective i
  erw [Z.outer_port, Z.outer_port, (h.seating ok links).ends_at, q.pres.toSeating.ends_at, Border.owner, Equiv.symm_apply_apply]
  exact ⟨Prod.ext rfl (h.outer_pin ok links w j).1, (h.outer_pin ok links w j).2⟩

end Relocation.Moves
end Assembly.Attachment
end OAI.LinearAlgebra.MatrixExponent
end
