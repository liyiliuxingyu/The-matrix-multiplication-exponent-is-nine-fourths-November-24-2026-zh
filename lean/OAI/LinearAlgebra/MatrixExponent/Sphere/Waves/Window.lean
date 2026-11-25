-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Update
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial

/-!
# 与宿主图大小无关的固定波动次数

第一次着色用于安排互不相交的移动区域，第二次着色在整个传播半径范围内区分键名。站点槽位缺失不会影响构造。在相邻两轮之间，移动过程不会在新位置创建待处理站点。

**英文原文**

A fixed number of waves independent of the host size

The first coloring schedules disjoint motion regions. A second
coloring separates key names over the entire propagation radius.
An absent station slot is harmless. Motion never creates a pending
station at a new position between waves.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open scoped Classical
variable {F V E : Type} {m d h U q W : ℕ} {a : Atlas V E m d h}

-- 读法：`horizon` 的取值由 `4 * U * (W - i) + 1` 给出。
/-- 经过 `i` 轮波操作后仍需保持的间隔。

英文原文：Separation still needed after `i` waves.
-/
def horizon (U W i : ℕ) := 4 * U * (W - i) + 1

-- 读法：`1` 不超过 `horizon U W i`。
theorem horizon_one (U W i : ℕ) : 1 ≤ horizon U W i := by unfold horizon; omega

-- 读法：`2 * U + horizon U W (i.val + 1) + 2 * U` 等于 `horizon U W i.val`。
theorem horizon_step (U : ℕ) (i : Fin W) :
    2 * U + horizon U W (i.val + 1) + 2 * U = horizon U W i.val := by
  unfold horizon
  rw [show W - i.val = (W - (i.val + 1)) + 1 by omega]
  ring

-- 读法：结构的字段包括 `count`、`root`、`pos`、`same`。
structure Plan (F : Type) (π : Palette a (2 * U + 2) q) (W : ℕ) where
  count : Fin W → ℕ
  root : ∀ i, Fin (count i) ↪ V
  pos : ∀ i, Fin (count i) → F
  same : ∀ i j k, π.mark (root i j) = π.mark (root i k)

namespace Plan

variable {π : Palette a (2 * U + 2) q} (p : Plan F π W)

-- 读法：`targets` 的取值由 `Set.range (fun j => (p.root i j, p.pos i j))` 给出。
def targets (i : Fin W) : Set (V × F) := Set.range (fun j => (p.root i j, p.pos i j))

-- 读法：`remaining` 的取值由 `{x | ∃ i : Fin W, j ≤ i.val ∧ x ∈ p.targets i}` 给出。
def remaining (j : ℕ) : Set (V × F) := {x | ∃ i : Fin W, j ≤ i.val ∧ x ∈ p.targets i}

-- 读法：`p.remaining W` 等于 `∅`。这里调用 `Nat.not_le_of_gt`。
theorem exhausted : p.remaining W = ∅ := by
  ext x
  simp only [remaining, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, h, _⟩
  exact Nat.not_le_of_gt i.isLt h

-- 读法：`p.remaining i.val \ p.targets i` 包含于 `p.remaining (i.val + 1)`。
theorem remove (i : Fin W) : p.remaining i.val \ p.targets i ⊆ p.remaining (i.val + 1) := by
  rintro x ⟨⟨j, h, hx⟩, hi⟩
  have hn : j ≠ i := by rintro rfl; exact hi hx
  exact ⟨j, by have := Fin.val_injective.ne hn; omega, hx⟩

end Plan

namespace Palette

variable [Fintype V] (π : Palette a (2 * U + 2) q) {M : ℕ}

-- 读法：在后续公式中，`group` 是 `{v // π.mark v = i}` 的缩写。
abbrev group (i : Fin q) := {v // π.mark v = i}

-- 读法：`roots` 的取值由 `(Fintype.equivFin (π.group i)).symm.toEmbedding.trans (Function.Embedding.subtype _)` 给出。
def roots (i : Fin q) : Fin (Fintype.card (π.group i)) ↪ V :=
  (Fintype.equivFin (π.group i)).symm.toEmbedding.trans (Function.Embedding.subtype _)

-- 读法：`v ∈ Set.range (π.roots i)` 与 `π.mark v = i` 等价。
theorem mem_roots (i : Fin q) (v : V) : v ∈ Set.range (π.roots i) ↔ π.mark v = i := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Fintype.equivFin (π.group i)).symm j).2
  · intro h
    exact ⟨Fintype.equivFin (π.group i) ⟨v, h⟩, by simp [roots]⟩

-- 读法：用字段 `count`、`root`、`pos`、`same` 构造 `Plan F π (q * M)`。
/-- 每一对颜色与初始局部槽位对应一个阶段。

英文原文：One phase per color and initial local slot.
-/
def plan (name : V → Fin M → F) : Plan F π (q * M) where
  count i := Fintype.card (π.group (finProdFinEquiv.symm i).1)
  root i := π.roots (finProdFinEquiv.symm i).1
  pos i j := name (π.roots (finProdFinEquiv.symm i).1 j) (finProdFinEquiv.symm i).2
  same _ j k := ((π.mem_roots _ _).mp ⟨j, rfl⟩).trans ((π.mem_roots _ _).mp ⟨k, rfl⟩).symm

-- 读法：`(v, name v i)` 属于 `(π.plan name).remaining 0`。这里调用 `Prod.ext`。
theorem plan_covers (name : V → Fin M → F) (v : V) (i : Fin M) :
    (v, name v i) ∈ (π.plan name).remaining 0 := by
  let j := finProdFinEquiv (π.mark v, i)
  have he : finProdFinEquiv.symm j = (π.mark v, i) := finProdFinEquiv.symm_apply_apply _
  obtain ⟨k, hk⟩ := (π.mem_roots (finProdFinEquiv.symm j).1 v).mpr (by rw [he])
  refine ⟨j, Nat.zero_le _, k, ?_⟩
  change (_, name _ _) = _
  exact Prod.ext hk (congrArg₂ name hk (congrArg Prod.snd he))

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 局部化曲面展开的一个阶段

每一帧都携带当前数学构造的阶段和一条短名称记录。计算下一条记录时，只使用当前记录、各目录和所选项的索引。实际的数学阶段为收缩恒等式提供见证。

**英文原文**

One phase of a localized surface expansion

A frame carries the mathematical stage as well as a short-name record.
Only the record, catalogs and choice indices are used to compute the
next record. The actual stage witnesses the contraction identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open scoped Classical
variable {F V E T X N J L : Type} [Field F] {r t m d h U R Q W : ℕ}
  {a : Atlas V E m d h} {π : Palette a (2 * U + 2) R}

-- 读法：结构的字段包括 `stage`、`address`、`record`、`match`、`clean`。
structure Frame (plan : Plan F π W) (ref : Reference J L N V E T X)
    (origin : Stage F r t T V E X) (P g H Q i : ℕ) where
  stage : Stage F r t T V E X
  address : V ⊕ ℕ → Stamp Q W U
  record : Record F r t V E (Stamp Q W U) N
  match' : Matches ref.world address stage record
  clean : Clean (a.near (horizon U W i)) stage address i
  reach : origin.Reach P g H U stage
  layout : stage.Layout a.src a.dst g
  valid : stage.Valid U
  calm : Calm stage
  todo : pending stage ⊆ plan.remaining i

namespace Frame

variable {plan : Plan F π W} {ref : Reference J L N V E T X}
  {origin : Stage F r t T V E X} {P g H i : ℕ}

-- 读法：要证明的命题是 `x.stage.Stopped`。
theorem stopped (x : Frame plan ref origin P g H Q W) : x.stage.Stopped := by
  intro v s hs n hn
  have he := x.todo (show (v, s.pos) ∈ pending x.stage from ⟨s, hs, rfl, n, hn⟩)
  rw [plan.exhausted] at he
  exact he

-- 读法：`info` 的取值由 `catalog size x.address x.stage` 给出。
def info (size : V → ℕ) (x : Frame plan ref origin P g H Q i) := catalog size x.address x.stage

variable [Fintype V] [Fintype E] [Fintype F]
  (c : Palette a (horizon U W 0) Q) (p l : ℕ) [ExpChar F p] {M D : ℕ}
  (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin W)
  (x : Frame plan ref origin (p ^ l) g H Q j.val)

-- 读法：`commands` 的取值由 `π.wave le_rfl x.record (x.match'.incident x.layout) ref p l g H M D hF (plan.root j) (plan.pos j) (created c.mark j)` 给出。
def commands := π.wave le_rfl x.record (x.match'.incident x.layout)
  ref p l g H M D hF (plan.root j) (plan.pos j) (created c.mark j)

local notation "C" => commands c p l hF j x

-- 读法：`Fintype (C i).vertices` 的取值由 `inferInstanceAs (Fintype (π.vertices U (plan.root j i)))` 给出。
instance (i : Fin (plan.count j)) : Fintype (C i).vertices :=
  inferInstanceAs (Fintype (π.vertices U (plan.root j i)))

-- 读法：要证明的命题是 `Wave.Prepared C x.record ref`。使用 `π.prepared` 给出的结论。
theorem prepared : Wave.Prepared C x.record ref :=
  π.prepared _ _ _ _ _ _ _ _ _ _ _ _ _ _ (plan.same j)

-- 读法：要证明的命题是 `a.near (2 * U) v w`。这里调用 `he.symm.join`。
theorem extent (v w : V) (h : Wave.Together C v w) : a.near (2 * U) v w := by
  rcases h with rfl|⟨i, hv, hw⟩
  · exact .refl _ _ _
  · have he := (π.vertex_range le_rfl).mp hv
    have hf := (π.vertex_range le_rfl).mp hw
    simpa [two_mul] using he.symm.join hf

-- 读法：要证明的命题是 `a.near (horizon U W j.val) s t`。
theorem space (v w s t : V) (e : a.near (horizon U W (j.val + 1)) v w)
    (hv : Wave.Together C v s) (hw : Wave.Together C w t) :
    a.near (horizon U W j.val) s t := by
  rw [← horizon_step U j]
  exact ((extent c p l hF j x _ _ hv).symm.join e).join (extent c p l hF j x _ _ hw)

-- 读法：要证明的命题是 `(C i).action.Ordered (created c.mark j (plan.root j i)) 0 U`。使用 `π.wave_ordered` 给出的结论。
theorem weight_ordered (i : Fin (plan.count j)) :
    (C i).action.Ordered (created c.mark j (plan.root j i)) 0 U :=
  π.wave_ordered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

-- 读法：`Set.range (Command.target ∘ C)` 等于 `plan.targets j`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem targets : Set.range (Command.target ∘ C) = plan.targets j := by
  unfold Plan.targets
  congr 1
  funext i
  exact π.wave_target _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Frame
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 以彼此独立的局部指令推进一个干净框架

**英文原文**

Advancing a clean frame by independent local scripts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame

open scoped Classical
variable {F V E T X N J L : Type} [Field F] {r t m d h U R Q W : ℕ}
  {a : Atlas V E m d h} {π : Palette a (2 * U + 2) R}
  {plan : Plan F π W} {ref : Reference J L N V E T X}
  {origin : Stage F r t T V E X} {g H : ℕ}

variable [Fintype V] [Fintype E] [Fintype F]
  (c : Palette a (horizon U W 0) Q) (p l : ℕ) [ExpChar F p] {M D : ℕ}
  (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin W)
  (x : Frame plan ref origin (p ^ l) g H Q j.val)

local notation "C" => commands c p l hF j x

omit [Fintype V] [Fintype E] [Fintype F] [ExpChar F p] in
-- 读法：要证明的命题是 `Known x.stage`。
private theorem known : Known x.stage := fun v k h => x.match'.known v k h

-- 读法：要证明的命题是 `Clean (a.near (horizon U W (j.val + 1))) s β (j.val + 1)`。这里调用 `ho.clean`。
private theorem advance_clean {s : Stage F r t T V E X} {β : V ⊕ ℕ → Stamp Q W U}
    {i : Wave.Index C} (ho : Wave.Origins C i x.stage s x.address β) :
    Clean (a.near (horizon U W (j.val + 1))) s β (j.val + 1) := by
  apply ho.clean c.mark j x.clean ?_ (space c p l hF j x)
    (plan.root j) ?_ (weight_ordered c p l hF j x)
  · intro v w e
    apply c.distinguish (e.mono ?_)
    unfold horizon
    gcongr
    omega
  · intro i
    exact (π.vertex_range le_rfl).mpr (.refl _ _ _)

-- 读法：`pending s` 包含于 `plan.remaining (j.val + 1)`。这里调用 `Set.Subset.trans`。
private theorem advance_todo {s : Stage F r t T V E X} {β : V ⊕ ℕ → Stamp Q W U}
    {i : Wave.Index C} (h : Wave.Finish C x.stage s x.address β i) :
    pending s ⊆ plan.remaining (j.val + 1) := by
  apply Set.Subset.trans _ (plan.remove j)
  intro v hv
  obtain ⟨hp, hn⟩ := h.pending hv
  rw [targets] at hn
  exact ⟨x.todo hp, hn⟩

-- 读法：`advance` 的证明用到 `Wave.execute`、`hp.separate`、`x.stage`。
/-- 对每组区域选择，下一框架的记录和键目录可由相互独立的更新算出。其收缩带有各局部分支权重的乘积。

英文原文：For each tuple of regional choices, the next frame has a record
and key catalogs computed by independent updates. Its contraction
has the product of the local branch weights.
-/
theorem advance {keys : V → X → X → Prop} {ext : T → X → X → Prop}
    (ctrl : origin.Controls keys ext) (room : ∀ y, origin.Reach (p ^ l) g H U y → y.Room M D) :
    ∃ f : Wave.Index C → Frame plan ref origin (p ^ l) g H Q (j.val + 1),
      (∀ i, (f i).record = Wave.update C x.record i) ∧
      (∀ i size, info size (f i) = Wave.carryInfo C i (info size x)) ∧
      ∀ y, x.stage.value (p ^ l) y = ∑ i, (∏ v, (C v).action.weight (i v)) * (f i).stage.value (p ^ l) y := by
  have hp := prepared c p l hF j x
  obtain ⟨s, β, h, he⟩ := Wave.execute C hp.separate x.stage x.address (hp.inputs x.match')
    x.layout x.valid (fun y hy => room _ (x.reach.trans hy)) x.calm
  have o i := (h i).history.origins hp.separate (x.reach.controls ctrl) (known p l j x)
  let f (i : Wave.Index C) : Frame plan ref origin (p ^ l) g H Q (j.val + 1) :=
    { stage := s i, address := β i, record := Wave.update C x.record i
      match' := hp.outputs x.match' (h i)
      clean := advance_clean c p l hF j x (o i)
      reach := x.reach.trans (h i).reach
      layout := ⟨x.layout.loopless, (h i).reach.ports_eq.symm ▸ x.layout.incident,
        (h i).reach.ports_eq.symm ▸ x.layout.unique, (h i).reach.ports_eq.symm ▸ x.layout.degree⟩
      valid := (h i).valid, calm := (h i).calm, todo := advance_todo c p l hF j x (h i) }
  refine ⟨f, fun _ => rfl, fun i size => ?_, he⟩
  exact (h i).catalog hp.separate (o i) c.mark j x.clean
    (fun v a b => space c p l hF j x _ _ _ _ (.refl _ _ v)) (plan.root j)
    (weight_ordered c p l hF j x) (known p l j x) size

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame
end

/-!
# 从原始位置初始化波动计划

**英文原文**

Initializing a wave schedule from the original positions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open scoped Classical
variable {F V E T X N K J L : Type} [Field F] {r t m d h U R Q M P g H : ℕ}
  {a : Atlas V E m d h} (π : Palette a (2 * U + 2) R)
  (c : Palette a (horizon U (R * M) 0) Q)

-- 读法：逐一匹配以下输入模式：`.inl v`、`.inr _`。
def startName [NeZero Q] : V ⊕ ℕ → Stamp Q (R * M) U
  | .inl v => (c.mark v, none)
  | .inr _ => (0, none)

-- 读法：`Record.positions` 的取值由 `(((G.rows v)[i.val]?).map Entry.pos).getD 0` 给出。
def Record.positions (G : Record F r t V E K N) (v : V) (i : Fin M) : F :=
  (((G.rows v)[i.val]?).map Entry.pos).getD 0

variable {ref : Reference J L N V E T X} {origin : Stage F r t T V E X}
  {G : Record F r t V E (Stamp Q (R * M) U) N}

-- 读法：用字段 `stage`、`address`、`record`、`match'` 构造 `Frame (π.plan (G.positions (M := M))) ref origin P g H Q 0`。
/-- 方案将每个原始槽位都尝试一次。元数据的匹配保证覆盖所有初始活动位置。

英文原文：The plan tries every original slot once. Matching the metadata
ensures that all initial active positions are covered.
-/
def Frame.initial [Fintype V] [NeZero Q] (h : Matches ref.world (startName c) origin G)
    (single : ∀ v, origin.footprint v = {.inl v}) (hcount : ∀ v, (origin.scene.cell v).stations.length ≤ M)
    (layout : origin.Layout a.src a.dst g) (hv : origin.Valid U) (hc : Calm origin) :
    Frame (π.plan (G.positions (M := M))) ref origin P g H Q 0 where
  stage := origin
  address := startName c
  record := G
  match' := h
  clean := by
    constructor
    · intro v w hv j hj k hk he
      simp only [single, Finset.mem_singleton] at hj hk
      subst j k
      exact congrArg Sum.inl (c.distinguish hv (congrArg Prod.fst he))
    · intro v j hj
      have e : j = .inl v := by simpa [single] using hj
      simp [e, earlier, startName]
  reach := .refl
  layout := layout
  valid := hv
  calm := hc
  todo := by
    rintro ⟨v, z⟩ ⟨b, hb, eq, hact⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hb
    let j : Fin M := ⟨i.val, i.isLt.trans_le (hcount v)⟩
    have hlen : i.val < (G.rows v).length := (h.rows v).length_eq ▸ i.isLt
    have pos := ((h.rows v).get i.isLt hlen).pos
    change ((origin.scene.cell v).stations.get i).pos = _ at pos
    rw [hi, eq] at pos
    have he : G.positions v j = z := by
      simp only [Record.positions, j, List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some]
      exact pos.symm
    rw [← he]
    exact π.plan_covers (G.positions (M := M)) v j

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 输出一组区域指令的输入

接缝的每一端都记录其颜色对和能量。即使邻域枚举多次访问同一个单元，仍可由带颜色的单元记录集合唯一恢复局部面板。

**英文原文**

Printing a regional script input

Each end of a seam carries its pair of colors and energy. A panel
can be recovered uniquely from the set of colored cell records,
even if a neighborhood enumeration visits a cell repeatedly.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical
variable {F K N J L V E : Type} {r t q U : ℕ}

-- 读法：结构的字段包括 `rows`、`ports`、`footprint`。
structure Body (F : Type) (r t q : ℕ) (K N : Type) where
  rows : List (Entry F r t K N)
  ports : List ((Fin q × Fin q) × F × ℕ)
  footprint : Finset K

-- 读法：结构的字段包括 `catalog`。
structure Tile (F : Type) (r t q : ℕ) (K N : Type) extends Body F r t q K N where
  catalog : Catalog K

-- 读法：`Record.body` 的取值由 `⟨a.rows i, (a.ports i).map fun v => (tag v.1, v.2, a.level v.1), a.footprint i⟩` 给出。
def Record.body (a : Record F r t J L K N) (tag : L → Fin q × Fin q) (i : J) : Body F r t q K N :=
  ⟨a.rows i, (a.ports i).map fun v => (tag v.1, v.2, a.level v.1), a.footprint i⟩

namespace View
variable {a : Record F r t J L K N} {b : Record F r t V E K N} {f : J ↪ V} {g : L ↪ E}

-- 读法：`b.body tag (f i)` 等于 `a.body (tag ∘ g) i`。
theorem body (h : View b f g a) (tag : E → Fin q × Fin q) (i : J) :
    b.body tag (f i) = a.body (tag ∘ g) i := by
  simp [Record.body, h.rows, h.footprint, h.ports, h.level, Function.comp_def]

end View
namespace Panel

variable (p : Panel F r t q U K N)

-- 读法：`printed` 的取值由 `univ.image (fun i : p.vertices => (i.val, p.input.body Subtype.val i))` 给出。
def printed := univ.image (fun i : p.vertices => (i.val, p.input.body Subtype.val i))

-- 读法：`complete` 表示以下条件：对每个 `j : p.edges`，存在 `i u`，`(j, u)` 属于 `p.input.ports i`。
/-- 面板中的每条边都出现在某个端口列表中。

英文原文：Every edge in the panel occurs in a port list.
-/
def complete : Prop := ∀ j : p.edges, ∃ i u, (j, u) ∈ p.input.ports i

-- 读法：`p.printed.image Prod.fst` 等于 `p.vertices`。
theorem colors : p.printed.image Prod.fst = p.vertices := by
  ext i
  simp [printed]

-- 读法：`j ∈ p.edges` 与 `∃ i ∈ p.printed, ∃ x ∈ i.2.ports, x.1 = j` 等价。这里调用 `j.property`。
theorem endpoints (hc : p.complete) (j : Fin q × Fin q) :
    j ∈ p.edges ↔ ∃ i ∈ p.printed, ∃ x ∈ i.2.ports, x.1 = j := by
  constructor
  · intro hj
    obtain ⟨i, u, hu⟩ := hc ⟨j, hj⟩
    refine ⟨_, mem_image_of_mem _ (mem_univ i), _, List.mem_map_of_mem hu, rfl⟩
  · rintro ⟨i, hi, x, hx, rfl⟩
    obtain ⟨i, _, rfl⟩ := mem_image.mp hi
    obtain ⟨⟨j, z⟩, _, rfl⟩ := List.mem_map.mp hx
    exact j.property

-- 读法：`a` 等于 `b`。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem input_eq {S : Finset (Fin q)} {T : Finset (Fin q × Fin q)}
    (a b : Record F r t ↥S ↥T K N) (eq : ∀ i, a.body Subtype.val i = b.body Subtype.val i)
    (hc : ∀ j : T, ∃ i x, (j, x) ∈ a.ports i) : a = b := by
  obtain ⟨ar, ap, al, af⟩ := a
  obtain ⟨br, bp, bl, bf⟩ := b
  have hp (i : S) := congrArg Body.ports (eq i)
  change ∀ i : S, (ap i).map (fun x => (x.1.val, x.2, al x.1)) =
    (bp i).map (fun x => (x.1.val, x.2, bl x.1)) at hp
  congr 1
  · exact funext fun i => congrArg Body.rows (eq i)
  · funext i
    have he := congrArg (List.map (fun t => (t.1, t.2.1))) (hp i)
    apply (Subtype.val_injective.prodMap Function.injective_id).list_map
    simp only [List.map_map, Function.comp_def] at he
    exact he
  · funext j
    -- 推导：从 `hc j` 中取出 `i, z, h`。
    obtain ⟨i, z, h⟩ := hc j
    have hi : (j.val, z, al j) ∈ (bp i).map (fun x => (x.1.val, x.2, bl x.1)) := by
      rw [← hp]; exact List.mem_map_of_mem h
    obtain ⟨⟨k, y⟩, _, he⟩ := List.mem_map.mp hi
    have hk : k = j := Subtype.ext (congrArg Prod.fst he)
    subst k
    exact (congrArg (fun u => u.2.2) he).symm
  · exact funext fun i => congrArg Body.footprint (eq i)

-- 读法：`p` 等于 `v`。
/-- 对完整面板作输出时不丢失任何信息。

英文原文：Printing loses no information on complete panels.
-/
theorem unique (v : Panel F r t q U K N) (hc : p.complete) (hc' : v.complete)
    (hv : p.printed = v.printed) (h₁ : p.center.val = v.center.val)
    (h₂ : p.pos = v.pos) (h₃ : p.fresh = v.fresh) : p = v := by
  have ha : p.vertices = v.vertices := by rw [← p.colors, ← v.colors, hv]
  have hb : p.edges = v.edges := by ext j; rw [p.endpoints hc, v.endpoints hc', hv]
  obtain ⟨A, B, c, a, y, g⟩ := p
  obtain ⟨A', B', c', a', y', g'⟩ := v
  dsimp only at ha hb h₁ h₂ h₃
  subst A' B' y' g'
  have eq : c = c' := Subtype.ext h₁
  subst c'
  congr 1
  apply input_eq a a' _ hc
  intro i
  -- 推导：记下中间结论 `h`：`(i.val, a.body Subtype.val i) ∈ (Panel.mk A B c a' y g).printed`。
  have h : (i.val, a.body Subtype.val i) ∈ (Panel.mk A B c a' y g).printed := by
    rw [← hv]; exact mem_image_of_mem _ (mem_univ i)
  obtain ⟨j, _, he⟩ := mem_image.mp h
  have hj : j = i := Subtype.ext (congrArg Prod.fst he)
  subst j
  exact (congrArg Prod.snd he).symm

end Panel
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 用短颜色编码读取几何邻域

**英文原文**

Reading the geometric neighborhood in short colors
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical
variable {F V E K N : Type} {r t m d h U q : ℕ} [Fintype V] [Fintype E]

-- 读法：`Atlas.ball` 的取值由 `univ.filter (a.near U v)` 给出。
def Atlas.ball (a : Atlas V E m d h) (U : ℕ) (v : V) := univ.filter (a.near U v)

namespace Palette
variable {a : Atlas V E m d h} (π : Palette a (2 * U + 2) q)
    (G : Record F r t V E K N) (hG : Incident G a) (v : V) (z : F) (ν : ℕ → K)

include hG in
-- 读法：要证明的命题是 `(π.panel U G v z ν).complete`。
theorem panel_complete : (π.panel U G v z ν).complete := by
  intro j
  let e := π.seam U v j
  have inc : ∃ w, a.near U v w ∧ e ∈ (G.ports w).map Prod.fst := by
    rcases (π.seam_spec U v j).1 with h|h
    · exact ⟨a.src e, h, (hG.endpoints _ _).mpr (.inl rfl)⟩
    · exact ⟨a.dst e, h, (hG.endpoints _ _).mpr (.inr rfl)⟩
  obtain ⟨w, hw, he⟩ := inc
  obtain ⟨i, rfl⟩ := (π.vertex_range le_rfl).mpr hw
  rw [(π.view le_rfl hG).ports i, List.map_map] at he
  obtain ⟨⟨k, l⟩, hk, eq⟩ := List.mem_map.mp he
  have : k = j := (π.seam U v).injective eq
  subst k
  exact ⟨i, l, hk⟩

include hG in
-- 读法：`(π.panel U G v z ν).printed` 等于 `(a.ball U v).image (fun i => (π.mark i, G.body π.edge i))`。
theorem panel_printed : (π.panel U G v z ν).printed =
    (a.ball U v).image (fun i => (π.mark i, G.body π.edge i)) := by
  have eq : π.edge ∘ π.seam U v = Subtype.val := funext fun i => (π.seam_spec U v i).2
  have body (i : π.vertices U v) :
      (π.extract U v G).body Subtype.val i = G.body π.edge (π.vertex U v i) := by
    rw [(π.view le_rfl hG).body, eq]
  change univ.image (fun i : π.vertices U v => (i.val, (π.extract U v G).body Subtype.val i)) = _
  ext p
  simp only [mem_image, mem_univ, true_and, Atlas.ball, mem_filter_univ]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨π.vertex U v i, (π.vertex_spec U v i).1,
      Prod.ext (π.vertex_spec U v i).2 (body i).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := (π.vertex_range le_rfl).mpr hw
    exact ⟨i, Prod.ext (π.vertex_spec U v i).2.symm (body i)⟩

omit [Fintype E] in
-- 读法：`π.mark w = i.val` 与 `w = π.vertex U v i` 等价。这里调用 `π.injective_at`。
theorem vertex_at {w : V} (hv : a.near (U + 1) v w) (i : π.vertices U v) :
    π.mark w = i.val ↔ w = π.vertex U v i := by
  refine ⟨fun e => ?_, fun e => e ▸ (π.vertex_spec U v i).2⟩
  apply π.injective_at (by omega) hv ((π.vertex_spec U v i).1.mono (by omega))
  exact e.trans (π.vertex_spec U v i).2.symm

omit [Fintype V] in
-- 读法：`π.edge e = i.val` 与 `e = π.seam U v i` 等价。这里调用 `a.links`。
theorem seam_at {w : V} (hv : a.near (U + 1) v w) (e : E) (he : a.src e = w ∨ a.dst e = w)
    (i : π.labels U v) : π.edge e = i.val ↔ e = π.seam U v i := by
  let j := π.seam U v i
  have ht := (π.seam_spec U v i).1.near
  refine ⟨fun h => ?_, fun e => e ▸ (π.seam_spec U v i).2⟩
  have both : π.edge e = π.edge j := h.trans (π.seam_spec U v i).2.symm
  obtain ⟨hs, hd⟩ := Prod.mk.inj both
  apply a.links
  rcases he with rfl|rfl
  · have hu : a.src e = a.src j := π.injective_at (by omega) hv ht.1 hs
    have hnear : a.near 1 (a.src e) (a.dst j) := by rw [hu]; exact a.near_edge j
    exact Prod.ext hu (π.injective_at (by omega) (a.near_edge e) hnear hd)
  · have hu : a.dst e = a.dst j := π.injective_at (by omega) hv ht.2 hd
    have hnear : a.near 1 (a.dst e) (a.src j) := by rw [hu]; exact (a.near_edge j).symm
    exact Prod.ext (π.injective_at (by omega) (a.near_edge e).symm hnear hs) hu

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 一次局部查表所得的回复

应答按颜色列出有变更的站点行、键目录和接缝能级。接收方保留原有端口顺序。

**英文原文**

Replies from one local lookup

The reply lists the changed station rows, key catalogs and seam
levels by color. Receivers keep their original port order.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical
variable {F K N J L V E : Type} {r t m d h U q : ℕ}

-- 读法：在后续公式中，`TileSet` 是 `Finset (Fin q × Tile F r t q K N)` 的缩写。
abbrev TileSet (F : Type) (r t q : ℕ) (K N : Type) := Finset (Fin q × Tile F r t q K N)

-- 读法：`Record.tile` 的取值由 `⟨G.body tag v, info v⟩` 给出。
def Record.tile (G : Record F r t V E K N) (tag : E → Fin q × Fin q)
    (info : V → Catalog K) (v : V) : Tile F r t q K N := ⟨G.body tag v, info v⟩

-- 读法：结构的字段包括 `weight`、`cell`、`level`。
structure Reply (F : Type) (r t q : ℕ) (K N : Type) where
  weight : F
  cell : Fin q → Option (List (Entry F r t K N) × Finset K × Catalog K)
  level : Fin q × Fin q → Option ℕ

-- 读法：`Reply.apply` 的结果类型为 `Tile F r t q K N`。
def Reply.apply (x : Reply F r t q K N) (v : Fin q) (y : Tile F r t q K N) : Tile F r t q K N :=
  let data := (x.cell v).getD (y.rows, y.footprint, y.catalog)
  ⟨⟨data.1, y.ports.map (fun i => (i.1, i.2.1, (x.level i.1).getD i.2.2)), data.2.1⟩, data.2.2⟩

-- 读法：用字段 `weight`、`cell`、`let`、`let` 构造 `Reply F r t q K N`。
def Panel.reply (x : Panel F r t q U K N) (action : Script F r t x.vertices x.edges K N)
    (choice : action.I) (input : TileSet F r t q K N) : Reply F r t q K N where
  weight := action.weight choice
  cell v := if hv : v ∈ x.vertices then
      let i := ⟨v, hv⟩
      let seen := (action.result choice).footprint i
      some ((action.result choice).rows i, seen,
        collect seen (fun j : input => j.val.2.catalog) (action.fresh choice))
    else none
  level v := if hv : v ∈ x.edges then some ((action.result choice).level ⟨v, hv⟩) else none

-- 读法：`TileSet.bodies` 的取值由 `s.image (fun i => (i.1, i.2.toBody))` 给出。
def TileSet.bodies (s : TileSet F r t q K N) :=
  s.image (fun i => (i.1, i.2.toBody))

-- 读法：`TileSet.get` 的结果类型为 `Option (Reply F r t q K N)`。
/-- 查表操作对任意输入都有定义。若描述格式错误或选择器越界，则不返回应答。

英文原文：The lookup is defined on arbitrary inputs. A malformed description
or an out-of-range selector gives no reply.
-/
def TileSet.get [Field F] [Fintype F] (s : TileSet F r t q K N)
    (p l g H M D : ℕ) [ExpChar F p] (hF : M * (2 * D + 1) < Fintype.card F)
    (i : Fin q) (z : F) (f : Fin (U + 1) → K) (j : ℕ) : Option (Reply F r t q K N) :=
  if h : ∃ a : Panel F r t q U K N,
      a.complete ∧ a.printed = s.bodies ∧ a.center.val = i ∧ a.pos = z ∧ a.fresh = f then
    let a := h.choose
    let u := a.action p l g H M D hF
    if hj : j < Fintype.card u.I then
      some (a.reply u ((Fintype.equivFin u.I).symm ⟨j, hj⟩) s) else none
  else none

-- 读法：结论为 `let u := x.action p l g H M D hF s.get p l g H M D hF x.center.val x.pos x.fresh j = if hj : j < Fintype.card u.I then some (x.reply u ((Fintype.equivFin u.I).symm ⟨j, hj⟩) s) else none`。
theorem TileSet.get_spec [Field F] [Fintype F] (s : TileSet F r t q K N)
    (p l g H M D : ℕ) [ExpChar F p] (hF : M * (2 * D + 1) < Fintype.card F)
    (x : Panel F r t q U K N) (hc : x.complete) (he : x.printed = s.bodies) (j : ℕ) :
    let u := x.action p l g H M D hF
    s.get p l g H M D hF x.center.val x.pos x.fresh j =
      if hj : j < Fintype.card u.I then
        some (x.reply u ((Fintype.equivFin u.I).symm ⟨j, hj⟩) s) else none := by
  have ex : ∃ a : Panel F r t q U K N,
      a.complete ∧ a.printed = s.bodies ∧ a.center.val = x.center.val ∧ a.pos = x.pos ∧ a.fresh = x.fresh :=
    ⟨x, hc, he, rfl, rfl, rfl⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ex.choose_spec
  have eq := ex.choose.unique x h₁ hc (h₂.trans he.symm) h₃ h₄ h₅
  rw [TileSet.get, dite_eq_left ex, eq]

namespace Palette
variable [Fintype V] {a : Atlas V E m d h} (π : Palette a (2 * U + 2) q)
    (G : Record F r t V E K N) (info : V → Catalog K) (v : V)

-- 读法：`tiles` 的取值由 `(a.ball U v).image fun i => (π.mark i, G.tile π.edge info i)` 给出。
def tiles : TileSet F r t q K N :=
  (a.ball U v).image fun i => (π.mark i, G.tile π.edge info i)

-- 读法：`(π.panel U G v z ν).printed` 等于 `(π.tiles G info v).bodies`。
theorem bodies [Fintype E] (hG : Incident G a) (z : F) (ν : ℕ → K) :
    (π.panel U G v z ν).printed = (π.tiles G info v).bodies := by
  rw [panel_printed π G hG, TileSet.bodies, tiles, image_image]
  rfl

-- 读法：`collect seen (fun i : π.tiles G info v => i.val.2.catalog) fresh` 等于 `collect seen (info ∘ π.vertex U v) fresh`。
theorem collect_eq (seen : Finset K) (fresh : List (K × ℕ)) :
    collect seen (fun i : π.tiles G info v => i.val.2.catalog) fresh =
      collect seen (info ∘ π.vertex U v) fresh := by
  ext ⟨k, d⟩
  simp only [mem_collect]
  have eq : (∃ i : π.tiles G info v, (k, d) ∈ i.val.2.catalog) ↔
      (∃ i, (k, d) ∈ (info ∘ π.vertex U v) i) := by
    constructor
    · rintro ⟨⟨_, h⟩, he⟩
      obtain ⟨w, hw, rfl⟩ := mem_image.mp h
      obtain ⟨j, rfl⟩ := (π.vertex_range le_rfl).mpr (mem_filter.mp hw).2
      exact ⟨j, he⟩
    · rintro ⟨j, h⟩
      let w := π.vertex U v j
      have hw : w ∈ a.ball U v := mem_filter_univ _ |>.mpr (π.vertex_spec U v j).1
      exact ⟨⟨_, mem_image_of_mem _ hw⟩, h⟩
  rw [eq]

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# 一个单元在一次波动中至多收到一个回复

**英文原文**

A cell receives at most one reply in a wave
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame
open scoped Classical
variable {F V E T X N J L : Type} [Field F] {r t m d h U R Q W : ℕ}
  {a : Atlas V E m d h} {π : Palette a (2 * U + 2) R}
  {plan : Plan F π W} {ref : Reference J L N V E T X}
  {origin : Stage F r t T V E X} {g H : ℕ}
  [Fintype V] [Fintype E] [Fintype F]
  (c : Palette a (horizon U W 0) Q) (p l : ℕ) [ExpChar F p] {M D : ℕ}
  (hF : M * (2 * D + 1) < Fintype.card F) (j : Fin W)
  (x : Frame plan ref origin (p ^ l) g H Q j.val)

local notation "C" => commands c p l hF j x
local notation "root" => plan.root j
variable (sel : Wave.Index (commands c p l hF j x)) (size : V → ℕ)

-- 读法：`panel` 的取值由 `π.panel U x.record (root i) (plan.pos j i) (created (U := U) c.mark j (root i))` 给出。
def panel (i : Fin (plan.count j)) :=
  π.panel U x.record (root i) (plan.pos j i) (created (U := U) c.mark j (root i))

-- 读法：`reply` 的取值由 `(panel c p l j x i).reply (C i).action (sel i) (π.tiles x.record (info size x) (root i))` 给出。
def reply (i : Fin (plan.count j)) :=
  (panel c p l j x i).reply (C i).action (sel i) (π.tiles x.record (info size x) (root i))

local notation "ans" => reply c p l hF j x sel size
local notation "G" => Wave.update C x.record sel
local notation "Q'" => Wave.carryInfo C sel (info size x)

omit [Field F] [Fintype V] [Fintype E] [Fintype F] in
-- 读法：`i` 等于 `k`。使用 `plan.root` 给出的结论。
theorem sole {i k : Fin (plan.count j)} {v : V}
    (hi : a.near (U + 1) (root i) v) (hk : a.near (U + 1) (root k) v) : i = k :=
  (plan.root j).injective (π.distinguish ((hi.join hk.symm).mono (by omega)) (plan.same j i k))

-- 读法：`v` 不属于 `Wave.vertices C`。
private theorem no_vertex {v : V} (h : ∀ i, ¬a.near U (root i) v) :
    v ∉ Wave.vertices C := by
  rintro ⟨i, hi⟩
  exact h i ((π.vertex_range le_rfl).mp hi)

-- 读法：`e` 不属于 `Wave.edges C`。
private theorem no_seam {e : E} (h : ∀ i, ¬a.touches U (root i) e) :
    e ∉ Wave.edges C := by
  rintro ⟨i, hi⟩
  exact h i ((π.seam_range le_rfl).mp hi)

-- 读法：`((G).rows v, (G).footprint v, Q' v)` 等于 `((ans i).cell (π.mark v)).getD (x.record.rows v, x.record.footprint v, info size x v)`。按 `π.mark v ∈ π.vertices U u` 成立与否分情况。
private theorem local_data (v : V) (i : Fin (plan.count j)) (hv : a.near (U + 1) (root i) v) :
    ((G).rows v, (G).footprint v, Q' v) =
      ((ans i).cell (π.mark v)).getD (x.record.rows v, x.record.footprint v, info size x v) := by
  have sep := (prepared c p l hF j x).separate.vertex
  let u := root i
  by_cases h : π.mark v ∈ π.vertices U u
  · let w : (C i).vertices := ⟨π.mark v, h⟩
    have he : v = (C i).ref.vertex w := (π.vertex_at u hv w).mp rfl
    simp only [Wave.update, Wave.carryInfo]
    conv_lhs => rw [he]
    simp only [Wave.write_at _ _ _ sep i w]
    unfold reply Panel.reply
    simp only [panel, Palette.panel, show π.mark v ∈ π.vertices U (root i) from h,
      ↓reduceDIte, Option.getD_some, Palette.collect_eq]
    rfl
  · have hn : v ∉ Wave.vertices C := by
      apply no_vertex
      intro k hk
      have e := sole j hv (hk.mono (by omega))
      subst k
      -- 推导：从 `(π.vertex_range le_rfl).mpr hk` 中取出 `w, hw`。
      obtain ⟨w, hw⟩ := (π.vertex_range le_rfl).mpr hk
      exact h (hw ▸ (π.vertex_spec U _ w).2.symm ▸ w.property)
    simp only [Wave.update, Wave.carryInfo, Wave.write_away _ _ _ v hn]
    simp only [reply, Panel.reply, panel, Palette.panel, show π.mark v ∉ π.vertices U (root i) from h,
      ↓reduceDIte, Option.getD_none]

-- 读法：`(G).level e` 等于 `((ans i).level (π.edge e)).getD (x.record.level e)`。按 `π.edge e ∈ π.labels U u` 成立与否分情况。
private theorem local_level (v : V) (i : Fin (plan.count j)) (hv : a.near (U + 1) (root i) v)
    (e : E) (he : a.src e = v ∨ a.dst e = v) :
    (G).level e = ((ans i).level (π.edge e)).getD (x.record.level e) := by
  let u := root i
  by_cases h : π.edge e ∈ π.labels U u
  · let w : (C i).edges := ⟨π.edge e, h⟩
    have hw : e = (C i).ref.edge w := (π.seam_at u hv e he w).mp rfl
    simp only [Wave.update]
    conv_lhs => rw [hw]
    rw [Wave.write_at _ _ _ (prepared c p l hF j x).separate.edge i w]
    simp only [reply, Panel.reply, panel, Palette.panel, show π.edge e ∈ π.labels U (root i) from h,
      ↓reduceDIte, Option.getD_some]
    rfl
  · have hn : e ∉ Wave.edges C := by
      apply no_seam
      intro k hk
      have near : a.near (U + 1) (root k) v := he.elim (fun t => t ▸ hk.near.1) (fun t => t ▸ hk.near.2)
      have eq := sole j hv near
      subst k
      -- 推导：从 `(π.seam_range le_rfl).mpr hk` 中取出 `w, hw`。
      obtain ⟨w, hw⟩ := (π.seam_range le_rfl).mpr hk
      exact h (hw ▸ (π.seam_spec U _ w).2.symm ▸ w.property)
    simp only [Wave.update, Wave.write_away _ _ _ e hn]
    simp only [reply, Panel.reply, panel, Palette.panel, show π.edge e ∉ π.labels U (root i) from h,
      ↓reduceDIte, Option.getD_none]

omit [Fintype V] [Fintype E] [Fintype F] [ExpChar F p] in
-- 读法：`a.src k.1 = v`、`a.dst k.1 = v` 至少有一项成立。
private theorem incidents (v : V) (k : E × F) (hk : k ∈ x.record.ports v) :
    a.src k.1 = v ∨ a.dst k.1 = v :=
  ((x.match'.incident x.layout).endpoints _ _).mp (List.mem_map_of_mem hk)

-- 读法：`(G).tile π.edge Q' v` 等于 `(ans i).apply (π.mark v) (x.record.tile π.edge (info size x) v)`。这里调用 `List.map_congr_left`。
theorem receive (v : V) (i : Fin (plan.count j)) (hv : a.near (U + 1) (root i) v) :
    (G).tile π.edge Q' v = (ans i).apply (π.mark v) (x.record.tile π.edge (info size x) v) := by
  have h := local_data c p l hF j x sel size v i hv
  unfold Record.tile Record.body Reply.apply
  dsimp only
  rw [← h]
  congr 2
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  have e := local_level c p l hF j x sel size v i hv k.1 (incidents p l j x v k hk)
  exact congrArg (fun n => (π.edge k.1, k.2, n)) e

-- 读法：`(G).tile π.edge Q' v` 等于 `x.record.tile π.edge (info size x) v`。这里调用 `Wave.write_away`。
theorem untouched (v : V) (hv : ∀ i, ¬a.near (U + 1) (root i) v) :
    (G).tile π.edge Q' v = x.record.tile π.edge (info size x) v := by
  have hn : v ∉ Wave.vertices C :=
    no_vertex c p l hF j x (fun i h => hv i (h.mono (by omega)))
  have level (k : E × F) (hk : k ∈ x.record.ports v) : (G).level k.1 = x.record.level k.1 := by
    simp only [Wave.update]
    apply Wave.write_away
    apply no_seam c p l hF j x
    intro i hit
    rcases incidents p l j x v k hk with hl|hr
    · exact hv i (hl ▸ hit.near.1)
    · exact hv i (hr ▸ hit.near.2)
  simp only [Record.tile, Record.body, Wave.update, Wave.carryInfo, Wave.write_away _ _ _ v hn]
  congr 2
  apply List.map_congr_left
  intro k hk
  exact congrArg (fun n => (π.edge k.1, k.2, n)) (level k hk)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Frame
end

/-!
# 短记录上的一次波动

每一对宿主与块的组合对应一条记录。两种颜色和初始位置始终不变。空单元中没有图块。

**英文原文**

A wave on short records

There is one record per host and block. The two colors and the
original positions never change. Vacant cells have no tile.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Coloring Assembly
open scoped Classical
variable {F V E T X J L N : Type} {m d h r t U R Q M : ℕ}

-- 读法：在后续公式中，`Metadata` 是 `Option (Fin R × Fin Q × (Fin M → F) × Tile F r t R (Stamp Q (R * M) U) N)` 的缩写。
abbrev Metadata (F : Type) (r t R Q U M : ℕ) (N : Type) :=
  Option (Fin R × Fin Q × (Fin M → F) × Tile F r t R (Stamp Q (R * M) U) N)


namespace Atlas
variable (a : Atlas V E m d h)

-- 读法：`fill` 的取值由 `Function.extend a.coord (some ∘ f) (fun _ => none)` 给出。
/-- 未被占用的地址被显式标为空位。

英文原文：An unoccupied address is explicitly vacant.
-/
def fill {α : Type} (f : V → α) : B m × B h → Option α :=
  Function.extend a.coord (some ∘ f) (fun _ => none)

-- 读法：`a.fill f (a.coord i)` 等于 `some (f i)`。使用 `a.coord.injective.extend_apply` 给出的结论。
theorem fill_at {α : Type} (f : V → α) (i : V) : a.fill f (a.coord i) = some (f i) :=
  a.coord.injective.extend_apply _ _ _

-- 读法：`a.fill f i` 等于 `none`。使用 `Function.extend_apply'` 给出的结论。
theorem fill_away {α : Type} (f : V → α) {i : B m × B h} (hi : i ∉ Set.range a.coord) :
    a.fill f i = none := Function.extend_apply' _ _ _ hi

-- 读法：`around` 的取值由 `(Neighborhood.expand k a.graph v.1 i, v.2)` 给出。
def around (k : ℕ) (v : B m × B h) (i : B ((d + 1) * k)) : B m × B h :=
  (Neighborhood.expand k a.graph v.1 i, v.2)

-- 读法：`a.around k v 0` 等于 `v`。使用 `Prod.ext` 给出的结论。
@[simp] theorem around_zero (k : ℕ) (v : B m × B h) : a.around k v 0 = v :=
  Prod.ext (Neighborhood.origin) rfl

-- 读法：`(∃ i, a.around k (a.coord x) i = a.coord y)` 与 `a.near k x y` 等价。
theorem around_iff (k : ℕ) (x y : V) :
    (∃ i, a.around k (a.coord x) i = a.coord y) ↔ a.near k x y := by
  constructor
  · rintro ⟨i, e⟩
    have hb := congrArg Prod.snd e
    have hc := congrArg Prod.fst e
    exact ⟨hb, Neighborhood.mem.mp ⟨i, hc⟩⟩
  · rintro ⟨hb, hh⟩
    obtain ⟨i, hi⟩ := Neighborhood.mem.mpr hh
    exact ⟨i, Prod.ext hi hb⟩

end Atlas

-- 读法：`visible` 的取值由 `univ.biUnion fun i => (f i).elim ∅ (fun v => {(v.1, v.2.2.2)})` 给出。
/-- 查询面板前先去掉额外字段。

英文原文：Erase the extra fields before looking up a panel.
-/
def visible {I : Type} [Fintype I] (f : I → Metadata F r t R Q U M N) :
    TileSet F r t R (Stamp Q (R * M) U) N :=
  univ.biUnion fun i => (f i).elim ∅ (fun v => {(v.1, v.2.2.2)})

namespace Palette

variable {a : Atlas V E m d h} (π : Palette a (2 * U + 2) R)
  (c : Palette a (horizon U (R * M) 0) Q) (pos : V → Fin M → F)
  (G : Record F r t V E (Stamp Q (R * M) U) N) (info : V → Catalog (Stamp Q (R * M) U))

-- 读法：`records` 的取值由 `a.fill (fun v => (π.mark v, c.mark v, pos v, G.tile π.edge info v))` 给出。
def records : B m × B h → Metadata F r t R Q U M N :=
  a.fill (fun v => (π.mark v, c.mark v, pos v, G.tile π.edge info v))

-- 读法：`π.records c pos G info (a.coord v)` 等于 `some (π.mark v, c.mark v, pos v, G.tile π.edge info v)`。使用 `a.fill_at` 给出的结论。
theorem records_at (v : V) :
    π.records c pos G info (a.coord v) = some (π.mark v, c.mark v, pos v, G.tile π.edge info v) :=
  a.fill_at _ _

-- 读法：`π.records c pos G info i` 等于 `none`。使用 `a.fill_away` 给出的结论。
theorem records_away {i : B m × B h} (hi : i ∉ Set.range a.coord) :
    π.records c pos G info i = none := a.fill_away _ hi

-- 读法：`visible (π.records c pos G info ∘ a.around U (a.coord v))` 等于 `π.tiles G info v`。按 `a.around U (a.coord v) i ∈ Set.range a.coord` 成立与否分情况。
theorem window [Fintype V] (v : V) :
    visible (π.records c pos G info ∘ a.around U (a.coord v)) = π.tiles G info v := by
  ext z
  simp only [visible, mem_biUnion, mem_univ, true_and, Function.comp_apply, tiles, mem_image,
    Atlas.ball, mem_filter_univ]
  constructor
  · rintro ⟨i, hi⟩
    by_cases he : a.around U (a.coord v) i ∈ Set.range a.coord
    · obtain ⟨w, hw⟩ := he
      rw [← hw, records_at] at hi
      exact ⟨w, (a.around_iff U v w).mp ⟨i, hw.symm⟩, (mem_singleton.mp hi).symm⟩
    · rw [records_away _ _ _ _ _ he] at hi
      simp at hi
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := (a.around_iff U v w).mpr hw
    exact ⟨i, by rw [hi, records_at]; simp⟩

end Palette
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end
