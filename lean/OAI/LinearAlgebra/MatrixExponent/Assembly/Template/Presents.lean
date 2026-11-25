-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.Model
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths

/-!
# 中间核心网络的统一表示

方案包含表与端口数据。每个宿主的公共首部记录占用情况、冻结状态与图掩码。每个块另有一个短字段编码其负载和历史计数器。本阶段所有分支共用解码器及测量标签长度所用的次序。

**英文原文**

A uniform representation of intermediate core networks

The scheme contains the table and port data. At each host a common
header records occupancy, frozen status and graph masks. A short
second field in each block encodes its load and history counters.
The decoder and the ordering for measuring tag lengths are shared
by all branches at this stage.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

-- 读法：结构的字段包括 `scheme`、`count`、`load`、`park`、`past`。
structure Template (F : Type) where
  scheme : Scheme F
  count : ℕ
  load : B count → ℝ
  park : B count → ℝ
  past : B count → ℕ
  order : B scheme.ℓ ≃ B scheme.ℓ
  full : Bool := true

namespace Template
variable {F T : Type} (D : Template F)

-- 读法：在后续公式中，`header` 是 `Format.pair (.pair .bit .bit) (.pair (Group.Flags D.scheme.d) (.vec D.scheme.h (.addr D.count)))` 的缩写。
abbrev header := Format.pair (.pair .bit .bit)
  (.pair (Group.Flags D.scheme.d) (.vec D.scheme.h (.addr D.count)))

-- 读法：在后续公式中，`format` 是 `D.scheme.format.pair (.vec D.scheme.m D.header)` 的缩写。
abbrev format := D.scheme.format.pair (.vec D.scheme.m D.header)

-- 读法：`D.format.width` 等于 `2 ^ D.scheme.m * (2 ^ D.scheme.d * (D.scheme.m + 2) + 2 + 2 ^ D.scheme.h * (D.scheme.ℓ + D.count))`。
theorem width : D.format.width = 2 ^ D.scheme.m *
    (2 ^ D.scheme.d * (D.scheme.m + 2) + 2 + 2 ^ D.scheme.h * (D.scheme.ℓ + D.count)) := by
  simp only [format, header, Scheme.format, Fmt.rows, Group.Flags, Format.width_pair, Format.width_vec,
    Format.width_addr]
  rw [Format.width_bit]
  ring

variable (r : D.format.obj)

-- 读法：在后续公式中，`nav` 是 `(r.1 i).1` 的缩写。
abbrev nav (i : B D.scheme.m) := (r.1 i).1
-- 读法：在后续公式中，`live` 是 `(r.2 i).1.1` 的缩写。
abbrev live (i : B D.scheme.m) := (r.2 i).1.1
-- 读法：在后续公式中，`frozen` 是 `(r.2 i).1.2` 的缩写。
abbrev frozen (i : B D.scheme.m) := (r.2 i).1.2
-- 读法：在后续公式中，`flags` 是 `(r.2 i).2.1` 的缩写。
abbrev flags (i : B D.scheme.m) := (r.2 i).2.1
-- 读法：在后续公式中，`counter` 是 `(r.2 i).2.2` 的缩写。
abbrev counter (i : B D.scheme.m) := (r.2 i).2.2

variable [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  (G : HostNet F L D.scheme.h u)

-- 读法：在后续公式中，`adj` 是 `if D.full then G.N else G.C` 的缩写。
/-- 若非核心部分的传播过慢，无法在一个阶段内跨过一条边，则控制器只需存储核心图。

英文原文：If noncore propagation is too slow to cross an edge in one
phase, the controller need only store the core graph.
-/
abbrev adj := if D.full then G.N else G.C

-- 读法：结构的字段包括 `post`、`block`、`live`、`frozen`、`closed`。
structure Encodes where
  post : D.scheme.Posting r.1 G
  block : ∀ i, post.block i = cellIndex _ i
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range post.host
  frozen : ∀ v, D.frozen r (post.host v) = true ↔ G.frozen v
  closed : ∀ v j, D.nav r (post.host v) j ∈ Set.range post.host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ D.adj G v ↔ ∃ j, D.nav r (post.host v) j = post.host w ∧
    (D.flags r (post.host v) j).1 = true
  core : ∀ v w, w ∈ G.C v ↔ ∃ j, D.nav r (post.host v) j = post.host w ∧
    (D.flags r (post.host v) j).2 = true
  load : ∀ v i, D.load (D.counter r (post.host v) (post.block i)) = G.load v i
  park : ∀ v i, D.park (D.counter r (post.host v) (post.block i)) = push G.park L.charge (v, i)
  past : ∀ v i, D.past (D.counter r (post.host v) (post.block i)) = G.past (v, i)

-- 读法：`tagLength` 的取值由 `History.Dense.used (D.order ((r.1 i).2 t)).val` 给出。
def tagLength (i : B D.scheme.m) (t : B D.scheme.h) :=
  History.Dense.used (D.order ((r.1 i).2 t)).val

end Template
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 每个位置实例恰有一个站点的网络板

**英文原文**

A board with one station per occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing Rounds

variable {F : Type} [Field F] {x y : Wire} (D : Template F)
  (r : D.format.obj) (P : Rounds.Board F x y D.scheme.h)

-- 读法：结构的字段包括 `pres`、`host`、`vertex`、`directed`、`live`。
structure Presents where
  pres : D.scheme.Presentation r.1 P.diagram
  host : P.V ↪ B D.scheme.m
  vertex : ∀ v, pres.vertex v = (host (P.place v).1, cellIndex _ (P.place v).2, 0)
  directed : pres.Directed
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range host
  closed : ∀ v j, D.nav r (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ P.adj v ↔ ∃ j, D.nav r (host v) j = host w ∧
    (D.flags r (host v) j).1 = true
  core : ∀ v w, w ∈ P.adj v ↔ ∃ j, D.nav r (host v) j = host w ∧
    (D.flags r (host v) j).2 = true
  load : ∀ v i, D.load (D.counter r (host v) (cellIndex _ i)) = push P.place P.charge (v, i)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 切去边界前一个集中项的表示

**英文原文**

A presentation of one concentrated term before cutting off its border
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing Rounds
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {u : ℕ}

-- 读法：结构的字段包括 `pres`、`host`、`vertex`、`directed`、`uniform`。
structure Shows (D : Template F) (r : D.format.obj) (Q : LocalTerm F x y D.scheme.h u) where
  pres : D.scheme.Presentation r.1 Q.diagram
  host : Q.V ↪ B D.scheme.m
  vertex : ∀ v, pres.vertex v = (host (Q.frame.place v).1, cellIndex _ (Q.frame.place v).2, 0)
  directed : pres.Directed
  uniform : pres.Uniform u
  index : Q.V → Q.V → B D.scheme.d
  neighbor : ∀ v w i j, D.scheme.peer r.1 (pres.vertex v, i) = some (pres.vertex w, j) →
    (D.scheme.pattern r.1 (pres.vertex v)).peer 0 i =
      some (index (Q.frame.place v).1 (Q.frame.place w).1, 0, j)
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range host
  frozen : ∀ v, D.frozen r (host v) = true ↔ Q.frame.frozen v
  closed : ∀ v j, D.nav r (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ Q.frame.N v ↔ ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).1 = true
  core : ∀ v w, w ∈ Q.frame.C v ↔ ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).2 = true
  charge : ∀ v, Q.charge v = Q.diagram.arity v + (u : ℝ)
  amount : ∀ i j, D.load (D.counter r i j) =
    ∑ v, if (pres.vertex v).1 = i ∧ (pres.vertex v).2.1 = j then Q.charge v else 0

variable (D : Template F)

-- 读法：在后续公式中，`cutCounter` 是 `Format.pair .bit (.addr D.count)` 的缩写。
abbrev cutCounter := Format.pair .bit (.addr D.count)

-- 读法：用字段 `scheme`、`count`、`load`、`park` 构造 `Template F`。
abbrev cut (u : ℕ) (scale : ℝ) : Template F where
  scheme := D.scheme.cut
  count := D.cutCounter.width
  load j :=
    let x := D.cutCounter.serial.symm j
    if x.1 then scale * D.load x.2 else max 0 (D.load x.2 - u)
  park j :=
    let x := D.cutCounter.serial.symm j
    if x.1 then D.load x.2 else 0
  past _ := 0
  order := Equiv.refl _
  full := true

-- 读法：`mobile` 的取值由 `!(D.frozen r i)` 给出。
def mobile (r : D.format.obj) (i : B D.scheme.m) := !(D.frozen r i)

-- 读法：`remove` 的结果类型为 `(D.cut u scale).format.obj`。
def remove (u : ℕ) (scale : ℝ) (r : D.format.obj) : (D.cut u scale).format.obj :=
  (D.scheme.remove r.1 (D.mobile r), fun i =>
    ((r.2 i).1, (D.flags r i, fun j => D.cutCounter.serial (D.frozen r i, D.counter r i j))))

namespace Shows
variable {D} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u} (s : D.Shows r Q)

-- 读法：`D.mobile r (s.pres.vertex v).1 = true` 与 `¬ Q.freeze.frozen v` 等价。
theorem kept (v : Q.diagram.V) : D.mobile r (s.pres.vertex v).1 = true ↔ ¬ Q.freeze.frozen v := by
  rw [s.vertex]
  have h := (s.frozen (Q.frame.place v).1).trans (Q.frame.keep v)
  simp only [mobile, Bool.not_eq_true', ← h, Bool.eq_false_iff]

-- 读法：在后续公式中，`presentation` 是 `s.pres.freeze Q.freeze (D.mobile r) s.kept` 的缩写。
abbrev presentation := s.pres.freeze Q.freeze (D.mobile r) s.kept
-- 读法：在后续公式中，`oriented` 是 `s.pres.freeze_directed Q.freeze (D.mobile r) s.kept s.directed` 的缩写。
abbrev oriented := s.pres.freeze_directed Q.freeze (D.mobile r) s.kept s.directed
-- 读法：在后续公式中，`sizes` 是 `s.pres.freeze_uniform Q.freeze (D.mobile r) s.kept (fun e => s.uniform e.val)` 的缩写。
abbrev sizes := s.pres.freeze_uniform Q.freeze (D.mobile r) s.kept (fun e => s.uniform e.val)
-- 读法：在后续公式中，`packets` 是 `s.presentation.packets s.oriented s.sizes` 的缩写。
abbrev packets := s.presentation.packets s.oriented s.sizes

-- 读法：`posting` 的结果类型为 `D.scheme.cut.Posting (D.scheme.remove r.1 (D.mobile r)) (Q.frame.hostOf hu L hL s.packets)`。
abbrev posting (hu : 0 < u) (L : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed)
    (hL : L.tensor = Q.freeze.border.tensor) :
    D.scheme.cut.Posting (D.scheme.remove r.1 (D.mobile r)) (Q.frame.hostOf hu L hL s.packets) :=
  s.pres.freezePosting Q.freeze (D.mobile r) s.kept s.directed (fun e => s.uniform e.val)
    Q.frame hu L hL s.host (cellIndex _).toEmbedding s.index s.vertex s.neighbor

end Shows
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 从宿主的编码中读取负载并选出分组

**英文原文**

Reading loads and electing a grouping from the encoded host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F T : Type} (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h)
local notation "M" => D.scheme.m
local notation "d" => D.scheme.d
local notation "n" => (D.scheme.h - a)

-- 读法：`position` 的取值由 `cellIndex _ ((splitCell a ha).symm ((cellIndex a).symm u, (cellIndex _).symm v))` 给出。
def position (u : B a) (v : B n) : B D.scheme.h :=
  cellIndex _ ((splitCell a ha).symm ((cellIndex a).symm u, (cellIndex _).symm v))

-- 读法：在后续公式中，`groupInput` 是 `Group.Input M d a n D.count` 的缩写。
abbrev groupInput := Group.Input M d a n D.count

-- 读法：输入 `i` 时返回 `(D.nav r i, D.live r i, D.flags r i, fun x y => D.counter r i (D.position a ha x y))`。
def groups (r : D.format.obj) : (D.groupInput a).obj :=
  fun i => (D.nav r i, D.live r i, D.flags r i, fun x y => D.counter r i (D.position a ha x y))

-- 读法：`relative` 的取值由 `D.load v / ((2 : ℝ) ^ k * b)` 给出。
def relative (k : ℕ) (b : ℝ) (v : B D.count) := D.load v / ((2 : ℝ) ^ k * b)

variable [Field F]

-- 读法：在 `F` 上按格式 `D.format`、`(D.groupInput a)` 编码输入输出，映射 `(D.groups a ha)` 的电路规模至多为 `(D.format.width + 2 * (D.groupInput a).width)`。这里调用 `Circuit.project`。
theorem groups_circuit : Circuit F D.format (D.groupInput a) (D.groups a ha)
    (D.format.width + 2 * (D.groupInput a).width) := by
  let f : (D.groupInput a).pins → D.format.pins
    | (i, .inl j) => .inl (i, .inl j)
    | (i, .inr (.inl j)) => .inr (i, .inl (.inl j))
    | (i, .inr (.inr (.inl j))) => .inr (i, .inr (.inl j))
    | (i, .inr (.inr (.inr (x, y, j)))) => .inr (i, .inr (.inr (D.position a ha x y, j)))
  exact Circuit.project f (by rintro _ ⟨_, _ | (_ | (_ | ⟨_, _, _⟩))⟩ <;> rfl)

variable [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G) (k : ℕ) (b : ℝ)

-- 读法：要证明的命题是 `Group.Presents (D.groups a ha r) p.post.host (D.adj G) G.C (Packing.relative k b (G.regroup a ha).load) (D.relative k b)`。
theorem presents :
    Group.Presents (D.groups a ha r) p.post.host (D.adj G) G.C
      (Packing.relative k b (G.regroup a ha).load) (D.relative k b) := by
  refine ⟨p.live, p.closed, p.edge, p.core, ?_⟩
  intro v i j
  let q := (splitCell a ha).symm (i, j)
  have he : splitAddr G.V a ha (v, q) = ((v, i), j) := by
    unfold splitAddr
    simp [q]
  have hl := G.regroup_load a ha (v, q)
  rw [he] at hl
  have ht := p.load v q
  rw [p.block] at ht
  have hh : D.position a ha (cellIndex a i) (cellIndex n j) = cellIndex _ q := by
    simp [position, q]
  change D.load (D.counter r (p.post.host v) (D.position a ha _ _)) / _ = _
  rw [hh, ht]
  exact congrArg (fun a => a / ((2 : ℝ) ^ k * b)) hl.symm

variable (Δ C : ℕ)
-- 读法：`intervals` 的取值由 `Group.labels Δ C (D.relative k b) (D.groups a ha r)` 给出。
def intervals (r : D.format.obj) := Group.labels Δ C (D.relative k b) (D.groups a ha r)

-- 读法：结论为 `∃ g : Grouping (inGroup a G.N) (inGroup a G.C) Δ C k b (G.regroup a ha).load, ∀ v i, D.intervals a ha k b Δ C r (Group.embed p.post.host a v) (cellIndex n i) = intervalCode n (g.here v i).2`。
theorem grouping (hΔ : 0 < Δ) (hC : 0 < C) (hk : 1 ≤ k) (hn : k ≤ n) (hb : 0 < b)
    (hG : G.Bounded Δ C b) (delayed : D.full = false → n ≤ 32 * Nat.clog 2 (2 * C)) :
    ∃ g : Grouping (inGroup a G.N) (inGroup a G.C) Δ C k b (G.regroup a ha).load,
      ∀ v i, D.intervals a ha k b Δ C r (Group.embed p.post.host a v) (cellIndex n i) =
        intervalCode n (g.here v i).2 := by
  have hg := G.regroup_bounded a ha hG
  have hs : ∀ v w, w ∈ D.adj G v → v ∈ D.adj G w := by
    unfold adj
    split
    · exact G.ns
    · exact G.cs
  have hc : ∀ v, G.C v ⊆ D.adj G v := by
    unfold adj
    split
    · exact G.sub
    · exact fun _ => Finset.Subset.rfl
  -- 推导：记下中间结论 `hsize`：`∀ v, (D.adj G v).card ≤ C`。
  have hsize : ∀ v, (D.adj G v).card ≤ C := by
    unfold adj
    split
    · exact hG.2.1
    · exact fun v => (Finset.card_le_card (G.sub v)).trans (hG.2.1 v)
  obtain ⟨q, hq⟩ := (D.presents a ha p k b).grouping hΔ hC hk hn hb hs G.cs hc hsize hG.1
    (fun v i => ⟨(G.regroup a ha).load_nonneg _ _, hg.2.2 _ _⟩)
  refine ⟨{ q with edge := ?_ }, hq⟩
  intro v w hw i
  by_cases e : w ∈ inGroup a (D.adj G) v
  · exact q.edge v w e i
  -- 推导：记下中间结论 `hf`：`D.full = false`。
  have hf : D.full = false := Bool.eq_false_iff.mpr (by
    intro h
    exact e (by simpa only [adj, ite_eq_left h] using hw))
  have e' : w ∉ inGroup a G.C v := by simpa [adj, hf] using e
  rw [ite_eq_right e']
  have h := (q.part w _ (q.mem w i)).1
  have hd := delayed hf
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 子宿主的公共地址

在仅使用核心的模式下，所存邻居字段的宽度取决于核心度数。具有延迟的非核心接触项单独追踪。

**英文原文**

Common addresses of child hosts

In core-only mode the stored neighbor width depends on the core
degree. Delayed noncore contacts are tracked separately.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F T : Type} (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (Δ C : ℕ)
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d

-- 读法：在后续公式中，`bound` 是 `if D.full then C else Δ` 的缩写。
abbrev bound := if D.full then C else Δ
-- 读法：在后续公式中，`size` 是 `m + (n + 1)` 的缩写。
abbrev size := m + (n + 1)
-- 读法：在后续公式中，`degree` 是 `Child.nextWidth n (D.bound Δ C) d` 的缩写。
abbrev degree := Child.nextWidth n (D.bound Δ C) d
-- 读法：在后续公式中，`Graph` 是 `Neighborhood.Rows (D.size a) (D.degree a Δ C)` 的缩写。
abbrev Graph := Neighborhood.Rows (D.size a) (D.degree a Δ C)
-- 读法：在后续公式中，`Status` 是 `Format.vec (D.size a) .bit` 的缩写。
abbrev Status := Format.vec (D.size a) .bit

-- 读法：`childNav` 的取值由 `Child.neighbors n (D.bound Δ C) (Child.fromGroup (D.groups a ha r) false)` 给出。
def childNav (r : D.format.obj) : (D.Graph a Δ C).obj :=
  Child.neighbors n (D.bound Δ C) (Child.fromGroup (D.groups a ha r) false)

-- 读法：`childCore` 的取值由 `Child.neighbors n Δ (Child.fromGroup (D.groups a ha r) true)` 给出。
def childCore (r : D.format.obj) :=
  Child.neighbors n Δ (Child.fromGroup (D.groups a ha r) true)

-- 读法：`childLive` 的取值由 `let t := Match.rowIndex m (n + 1) j D.live r t.1 && decide (t.2 ∈ Set.range (intervalCode n))` 给出。
def childLive (r : D.format.obj) (j : B (D.size a)) :=
  let t := Match.rowIndex m (n + 1) j
  D.live r t.1 && decide (t.2 ∈ Set.range (intervalCode n))

-- 读法：`childFrozen` 的取值由 `D.frozen r (Match.rowIndex m (n + 1) j).1` 给出。
def childFrozen (r : D.format.obj) (j : B (D.size a)) :=
  D.frozen r (Match.rowIndex m (n + 1) j).1

-- 读法：`D.childNav a ha Δ C r j 0` 等于 `j`。使用 `Neighborhood.origin` 给出的结论。
theorem childSelf (r : D.format.obj) (j : B (D.size a)) : D.childNav a ha Δ C r j 0 = j :=
  Neighborhood.origin

variable [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G)

-- 读法：`D.childLive a r j = true` 与 `j ∈ Set.range (Child.host p.post.host n)` 等价。这里调用 `Prod.ext`。
theorem child_live (j : B (D.size a)) :
    D.childLive a r j = true ↔ j ∈ Set.range (Child.host p.post.host n) := by
  simp only [childLive, Bool.and_eq_true, decide_eq_true_eq, p.live]
  constructor
  · rintro ⟨⟨v, hv⟩, ⟨t, ht⟩⟩
    refine ⟨(v, t), (Match.rowIndex m (n + 1)).injective ?_⟩
    rw [Child.host_parts]
    exact Prod.ext hv ht
  · rintro ⟨v, rfl⟩
    rw [Child.host_parts]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

-- 读法：要证明的命题是 `Child.Presents (D.adj G) p.post.host (Child.fromGroup (D.groups a ha r) false)`。使用 `Child.presents` 给出的结论。
theorem child_presents :
    Child.Presents (D.adj G) p.post.host (Child.fromGroup (D.groups a ha r) false) :=
  Child.presents (D.presents a ha p 0 1) false

-- 读法：要证明的命题是 `Child.Presents G.C p.post.host (Child.fromGroup (D.groups a ha r) true)`。使用 `Child.presents` 给出的结论。
theorem core_presents :
    Child.Presents G.C p.post.host (Child.fromGroup (D.groups a ha r) true) :=
  Child.presents (D.presents a ha p 0 1) true

omit [Field F] in
-- 读法：`0` 严格小于 `D.bound Δ C`。
theorem bound_pos (hd : 0 < Δ) (hc : Δ ≤ C) : 0 < D.bound Δ C := by
  unfold bound
  split <;> omega

include p in
-- 读法：要证明的命题是 `Fmt.Reciprocal A (fun i => (D.childNav a ha Δ C r i, f i))`。
theorem child_reciprocal (hd : 0 < Δ) (hc : Δ ≤ C) (A : Format) (f : B (D.size a) → A.obj) :
    Fmt.Reciprocal A (fun i => (D.childNav a ha Δ C r i, f i)) := by
  refine (D.child_presents a ha p).reciprocal (D.bound_pos Δ C hd hc) ?_ A f
  unfold adj
  split
  · exact G.ns
  · exact G.cs

-- 读法：结论为 `let nav := D.childNav a ha Δ C r let H := Child.host p.post.host n nav (H v) (Child.index nav (H v) (H w)) = H w`。这里调用 `D.child_presents`。
theorem child_hop (hd : 0 < Δ) (hc : Δ ≤ C) (v w : Site G.V n)
    (hw : w ∈ (G.project a ha Δ C hc).C v) :
    let nav := D.childNav a ha Δ C r
    let H := Child.host p.post.host n
    nav (H v) (Child.index nav (H v) (H w)) = H w := by
  apply (D.child_presents a ha p).nav (D.bound_pos Δ C hd hc)
  by_cases h : D.full = true
  · rw [adj, bound, ite_eq_left h, ite_eq_left h]
    exact (G.project a ha Δ C hc).sub v hw
  · rw [adj, bound, ite_eq_right h, ite_eq_right h]
    exact hw

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 计算子宿主公共地址和掩码的成本

**英文原文**

Cost of the common child address and mask computations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h)
  (Δ C : ℕ)
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "j" => D.size a
local notation "v" => D.degree a Δ C

-- 读法：`navCost` 的取值由 `D.format.width + 3 * (D.groupInput a).width + 68 * (Child.Input m d).width + 2 ^ j * (100 + (j + 2 ^ degree)) ^ 201` 给出。
def navCost (degree : ℕ) :=
  D.format.width + 3 * (D.groupInput a).width + 68 * (Child.Input m d).width +
    2 ^ j * (100 + (j + 2 ^ degree)) ^ 201

-- 读法：在 `F` 上按格式 `D.format`、`(Neighborhood.Rows j (Child.nextWidth n deg d))` 编码输入输出，映射 `(fun r => Child.neighbors n deg (Child.fromGroup (D.groups a ha r) core))` 的电路规模至多为 `(D.navCost a (Child.nextWidth n deg d))`。
theorem nav_net (core : Bool) (deg : ℕ) :
    Circuit F D.format (Neighborhood.Rows j (Child.nextWidth n deg d))
      (fun r => Child.neighbors n deg (Child.fromGroup (D.groups a ha r) core))
      (D.navCost a (Child.nextWidth n deg d)) := by
  let prep := (D.groups_circuit a ha).comp (Child.fromGroup_circuit F core)
  obtain ⟨k, hk, h⟩ := Child.cheap F m d n deg
  refine (prep.comp hk).mono ?_
  change _ + _ + k ≤ 2 ^ j * (100 + (j + 2 ^ Child.nextWidth n deg d)) ^ 201 at h
  unfold navCost
  change D.format.width + 2 * (D.groupInput a).width +
    ((D.groupInput a).width + 68 * (Child.Input m d).width) + k ≤ _
  omega

-- 读法：`statusCost` 的取值由 `D.format.width + 34 * (D.Status a).width` 给出。
def statusCost := D.format.width + 34 * (D.Status a).width

-- 读法：在 `F` 上按格式 `D.format`、`(D.Status a)` 编码输入输出，映射 `(D.childLive a)` 的电路规模至多为 `(D.statusCost a)`。这里调用 `h.bnet`。
theorem status_net :
    Circuit F D.format (D.Status a) (D.childLive a) (D.statusCost a) := by
  have h : Install.Depends ((D.Status a).code ∘ D.childLive a ∘ D.format.code.symm) 1 := by
    rintro ⟨i, ⟨⟩⟩
    let p := (Match.rowIndex m (n + 1) i).1
    let pin : D.format.pins := .inr (p, .inl (.inl ()))
    refine ⟨{pin}, by simp, fun x y he => ?_⟩
    change (x pin && _) = (y pin && _)
    rw [he pin (by simp)]
  exact h.bnet F

-- 读法：`childCost` 的取值由 `4 * (5 * D.format.width + D.statusCost a + D.navCost a v)` 给出。
def childCost := 4 * (5 * D.format.width + D.statusCost a + D.navCost a v)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `D.format` 到 `((D.Status a).pair (D.Graph a Δ C))` 实现映射 `(fun r => (D.childLive a r, D.childNav a ha Δ C r))` 的开销至多为 `(D.childCost a Δ C)`。使用 `Map.circuit` 给出的结论。
theorem child_map {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) :
    Map F u L D.format ((D.Status a).pair (D.Graph a Δ C))
      (fun r => (D.childLive a r, D.childNav a ha Δ C r)) (D.childCost a Δ C) :=
  Map.circuit hu ((D.status_net a).pair (D.nav_net a ha false (D.bound Δ C)))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end
