-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Replay
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Broadcast

/-!
# 原有各站的一份副本所用的固定模板

标签比特选出属于某工作单元的所有可能标签中的那些标签。其余比特由每个包的一对块及各副本的外部比特组成。这种格式不会向控制部分提供任何表内取值。

**英文原文**

A fixed template for one copy of the original stations

The label bits select which of the possible labels belong to a worker.
The remaining bits are one pair of blocks per packet, and the exterior
bits of the copies. This format exposes no table values to the controls.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h : ℕ} (L : Layout G n r h)

-- 读法：在后续公式中，`Tape` 是 `Label n r ⊕ (Position n r L.d h × Bool) ⊕ slots a ⊕ slots b` 的缩写。
abbrev Tape := Label n r ⊕ (Position n r L.d h × Bool) ⊕ slots a ⊕ slots b
-- 读法：在后续公式中，`Gate` 是 `G.normalized.V ⊕ Position n r L.d h` 的缩写。
abbrev Gate := G.normalized.V ⊕ Position n r L.d h

-- 读法：逐一匹配以下输入模式：`.inl z`、`.inr (.inl (p, s))`、`.inr (.inr (.inl i))`、`.inr (.inr (.inr j))`。
def which : L.Tape → Label n r
  | .inl z => z
  | .inr (.inl (p, s)) => Expansion.endpoint p s
  | .inr (.inr (.inl i)) => L.color (.inr (.inl i))
  | .inr (.inr (.inr j)) => L.color (.inr (.inr (.inl j)))

-- 读法：逐一匹配以下输入模式：`.inl v`、`.inr p`。
def whereAt : L.Gate → Label n r
  | .inl v => L.color v
  | .inr p => Expansion.endpoint p false

-- 读法：逐一匹配以下输入模式：`.inl v`、`.inr p`。
def op : L.Gate → Table F
  | .inl v => G.normalized.table v
  | .inr p => ⟨.bit, .unit, fun x _ => if x = false ∨ ∃ e, L.assign e = p then 1 else 0⟩

-- 读法：`fromPort` 的取值由 `.inr (.inl (L.assign e, s))` 给出。
private def fromPort (s : Bool) (e : G.End) : L.Tape := .inr (.inl (L.assign e, s))

-- 读法：逐一匹配输入模式，例如 `.inl (.inl v), i`、`.inl (.inr (.inl i)), .inl _`、`.inl (.inr (.inl i)), .inr _`、`.inl (.inr (.inr (.inl j))), .inl _`。
def arg : (g : L.Gate) → PortsOf (L.op g) → L.Tape
  | .inl (.inl v), i => L.fromPort false (G.portEquiv ⟨v, i⟩)
  | .inl (.inr (.inl i)), .inl _ => .inr (.inr (.inl i))
  | .inl (.inr (.inl i)), .inr _ => L.fromPort true (.inl (.inl i))
  | .inl (.inr (.inr (.inl j))), .inl _ => L.fromPort true (.inr (.inl j))
  | .inl (.inr (.inr (.inl j))), .inr _ => .inr (.inr (.inr j))
  | .inl (.inr (.inr (.inr e))), .inl _ => L.fromPort true (.inr (.inr e))
  | .inl (.inr (.inr (.inr e))), .inr _ => L.fromPort true (.inl (.inr e))
  | .inr p, _ => .inr (.inl (p, false))

-- 读法：`L.which (L.fromPort false e)` 等于 `L.color (.inl (G.station e))`。
private theorem which_station (e : G.End) :
    L.which (L.fromPort false e) = L.color (.inl (G.station e)) :=
  congrArg Prod.fst (L.follows e)

-- 读法：`L.which (L.fromPort true e)` 等于 `L.color (.inr (G.junction e))`。
private theorem which_joint (e : G.End) :
    L.which (L.fromPort true e) = L.color (.inr (G.junction e)) :=
  congrArg Prod.snd (L.follows e)

-- 读法：`L.which (L.arg v i)` 等于 `L.whereAt v`。这里调用 `L.which_station`。
theorem arg_local (v : L.Gate) (i : PortsOf (L.op v)) : L.which (L.arg v i) = L.whereAt v := by
  rcases v with (v | p | q | e) | p
  · exact (L.which_station _).trans (congrArg (fun j => L.color (.inl j)) (G.station_port _))
  · cases i
    · rfl
    · exact L.which_joint _
  · cases i
    · exact L.which_joint _
    · rfl
  · cases i <;> exact L.which_joint _
  · rfl

-- 读法：在后续公式中，`LocalTape` 是 `{p : L.Tape // L.which p i = g}` 的缩写。
abbrev LocalTape (i : Fin n) (g : Fin r) := {p : L.Tape // L.which p i = g}
-- 读法：在后续公式中，`LocalGate` 是 `{p : L.Gate // L.whereAt p i = g}` 的缩写。
abbrev LocalGate (i : Fin n) (g : Fin r) := {p : L.Gate // L.whereAt p i = g}

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr p`。
def route (i : Fin n) (g : Fin r) (v : L.LocalGate i g) :
    Unit ⊕ PortsOf (L.op v.1) → L.LocalTape i g
  | .inl _ => ⟨.inl (L.whereAt v.1), v.2⟩
  | .inr p => ⟨L.arg v.1 p, by rw [L.arg_local]; exact v.2⟩

-- 读法：当 `x (.inl ())` 成立时取 `weight T (x ∘ Sum.inr)`，否则取 `1`。
def enabled (T : Table F) (x : Unit ⊕ PortsOf T → Bool) :=
  if x (.inl ()) then weight T (x ∘ Sum.inr) else 1

-- 读法：`kernel` 的取值由 `∏ v : L.LocalGate i g, enabled (L.op v.1) (x ∘ L.route i g v)` 给出。
def kernel (i : Fin n) (g : Fin r) (x : L.LocalTape i g → Bool) : F :=
  ∏ v : L.LocalGate i g, enabled (L.op v.1) (x ∘ L.route i g v)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

section
/-!
# 工作单元模板的输入数与逻辑门数上界

在报告指出应启用哪些逻辑门之前，先对一个标签坐标中的所有候选门计数。原有各站按关联的端点计费。接合点为二元，填充引脚为一元。

**英文原文**

Input and gate bounds for a worker template

Count all candidate gates in one label coordinate, before the
report specifies which ones to enable. The original stations are
charged by incident ends. Junctions are binary and padding pins unary.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
open Finset
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r d h M : ℕ} (L : Layout G n r h)

-- 读法：`(∑ p : {v // f v = g}, k p.val)` 等于 `∑ v, if f v = g then k v else 0`。这里调用 `sum_subtype`。
private theorem sum_at {X : Type} [Fintype X] (f : X → Fin r) (g : Fin r) (k : X → ℕ) :
    (∑ p : {v // f v = g}, k p.val) = ∑ v, if f v = g then k v else 0 := by
  rw [← sum_filter]
  exact (sum_subtype _ (by simp) _).symm

-- 读法：`(∑ v, if f v = g then k else 0)` 等于 `multiplicity f g * k`。
private theorem sum_count {X : Type} [Fintype X] (f : X → Fin r) (g : Fin r) (k : ℕ) :
    (∑ v, if f v = g then k else 0) = multiplicity f g * k := by
  rw [← sum_at f g (fun _ => k)]
  simp [multiplicity]

-- 读法：`multiplicity (fun x : Position n r d h × Bool => Expansion.endpoint x.1 x.2 i) g * r` 等于 `2 * Fintype.card (Position n r d h)`。
private theorem both_endpoints (i : Fin n) (g : Fin r) :
    multiplicity (fun x : Position n r d h × Bool => Expansion.endpoint x.1 x.2 i) g * r =
      2 * Fintype.card (Position n r d h) := by
  let f (x : Position n r d h × Bool) := Expansion.endpoint x.1 x.2 i
  have he := sum_count f g 1
  rw [mul_one, Fintype.sum_prod_type, sum_comm] at he
  change multiplicity f g * r = _
  rw [← he, sum_mul]
  have e (s : Bool) : (∑ p, if f (p, s) = g then 1 else 0) * r =
      Fintype.card (Position n r d h) := by
    rw [sum_count (fun p => f (p, s)), mul_one]
    exact endpoint_uniform s i g
  simp only [e, sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_id]

variable (hv : ∀ z, multiplicity L.color z * r ^ n ≤ 16 * M)
  (hp : Fintype.card (Position n r L.d h) ≤ 13 * M)

include hv hp in
-- 读法：`Fintype.card (L.LocalTape i g) * r` 不超过 `100 * M`。这里调用 `Fintype.card_le_of_injective`。
theorem tape_bound (hl : r ^ n ≤ M) (i : Fin n) (g : Fin r) :
    Fintype.card (L.LocalTape i g) * r ≤ 100 * M := by
  let f := fun v => L.color v i
  let ext : slots a ⊕ slots b → G.normalized.V := Sum.elim
    (fun p => .inr (.inl p)) (fun p => .inr (.inr (.inl p)))
  have hi : Function.Injective ext := by rintro (x|x) (y|y) <;> simp [ext]
  have hE : multiplicity (f ∘ ext) g ≤ multiplicity f g := by
    let lift : {v // (f ∘ ext) v = g} → {v // f v = g} := fun v => ⟨ext v.1, v.2⟩
    exact Fintype.card_le_of_injective lift (fun _ _ h => Subtype.ext (hi (congrArg Subtype.val h)))
  have hE' := (Nat.mul_le_mul_right r hE).trans (L.vertex_bound hv i g)
  -- 推导：记下中间结论 `he`：`(fun p : slots a ⊕ slots b => L.which (.inr (.inr p)) i) = f ∘ ext`。
  have he : (fun p : slots a ⊕ slots b => L.which (.inr (.inr p)) i) = f ∘ ext := by
    funext p; cases p <;> rfl
  change multiplicity (fun v => L.which v i) g * r ≤ _
  rw [multiplicity_sum, multiplicity_sum]
  change (multiplicity (fun z : Label n r => z i) g +
    (multiplicity (fun x : Position n r L.d h × Bool => Expansion.endpoint x.1 x.2 i) g +
     multiplicity (fun p : slots a ⊕ slots b => L.which (.inr (.inr p)) i) g)) * r ≤ _
  rw [add_mul, add_mul, he, label_uniform, both_endpoints]
  omega

omit [Field F] in
-- 读法：`(∑ v, if f v = g then 1 + G.arity v else 0)` 等于 `multiplicity f g + multiplicity (f ∘ G.station) g`。这里调用 `sum_congr`。
private theorem station_cost (f : G.V → Fin r) (g : Fin r) :
    (∑ v, if f v = g then 1 + G.arity v else 0) =
      multiplicity f g + multiplicity (f ∘ G.station) g := by
  have count {X : Type} [Fintype X] (k : X → Fin r) :
      multiplicity k g = ∑ v, if k v = g then 1 else 0 := by
    rw [sum_count, mul_one]
  rw [count f, count (f ∘ G.station), ← G.portEquiv.sum_comp, Fintype.sum_sigma,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  simp only [Function.comp_apply, G.station_port]
  by_cases he : f v = g <;> simp [he, Diagram.Port, Diagram.arity]

include hv hp in
-- 读法：`(∑ v : L.LocalGate i g, (1 + Processor.arity (L.op v.val))) * r` 不超过 `100 * M`。这里调用 `L.vertex_bound`。
theorem gate_bound (i : Fin n) (g : Fin r) :
    (∑ v : L.LocalGate i g, (1 + Processor.arity (L.op v.val))) * r ≤ 100 * M := by
  let f := fun v => L.color v i
  let fs := f ∘ Sum.inl
  let fj := f ∘ Sum.inr
  let fp := fun p : Position n r L.d h => Expansion.endpoint p false i
  have h₁ : (multiplicity fs g + multiplicity fj g) * r ≤ 16 * M := by
    rw [← multiplicity_sum f]
    exact L.vertex_bound hv i g
  have h₂ : multiplicity (fs ∘ G.station) g * r ≤ 26 * M :=
    (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)).trans (L.end_bound hp i g)
  have h₃ : multiplicity fp g * r ≤ 13 * M := (endpoint_uniform false i g).le.trans hp
  rw [sum_at (fun v => L.whereAt v i) g (fun v => 1 + Processor.arity (L.op v)),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  change ((∑ v, if fs v = g then 1 + G.arity v else 0) +
    (∑ v, if fj v = g then 3 else 0) + (∑ v, if fp v = g then 2 else 0)) * r ≤ 100 * M
  rw [station_cost fs g, sum_count fj, sum_count fp]
  nlinarith only [h₁, h₂, h₃, Nat.zero_le (multiplicity fs g * r)]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 用一批物理指派为站模板提供输入

**英文原文**

Feeding a station template from one batch of physical assignments
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h B : ℕ} (L : Layout G n r h)

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Fin B × Position n r L.d h ≃ Position n r (B * L.d) h`。
def batches (B : ℕ) : Fin B × Position n r L.d h ≃ Position n r (B * L.d) h where
  toFun t := ((t.2.1.1, finProdFinEquiv (t.1, t.2.1.2)), t.2.2)
  invFun t := ((finProdFinEquiv.symm t.1.2).1, (t.1.1, (finProdFinEquiv.symm t.1.2).2), t.2)
  left_inv _ := by simp only [Equiv.symm_apply_apply]
  right_inv _ := by simp only [Prod.mk.eta, Equiv.apply_symm_apply]

-- 读法：`L.pos t e` 等于 `L.batches B (t, L.assign e)`。两端由定义化简为同一项。
theorem pos_batches (t : Fin B) (e : G.End) : L.pos t e = L.batches B (t, L.assign e) := rfl

-- 读法：逐一匹配以下输入模式：`.inl z`、`.inr (.inl (p, u))`、`.inr (.inr (.inl i))`、`.inr (.inr (.inr i))`。
def values (mask : Label n r → Bool) (x : Fin B → Val a) (y : Fin B → Val b)
    (s : Bool → L.Slots B) (j : Fin B) : L.Tape → Bool
  | .inl z => mask z
  | .inr (.inl (p, u)) => (s u) (L.batches B (j, p)).1 (L.batches B (j, p)).2
  | .inr (.inr (.inl i)) => bits a (x j) i
  | .inr (.inr (.inr i)) => bits b (y j) i

variable (mask : Label n r → Bool) (x : Fin B → Val a) (y : Fin B → Val b)
    (s : Bool → L.Slots B) (j : Fin B)

-- 读法：`weight (L.op (.inl v)) (L.values mask x y s j ∘ L.arg (.inl v))` 等于 `G.normalized.vertex (x j) (y j) (L.read (s v.isRight) j) v`。
theorem weight_vertex (v : G.normalized.V) :
    weight (L.op (.inl v)) (L.values mask x y s j ∘ L.arg (.inl v)) =
      G.normalized.vertex (x j) (y j) (L.read (s v.isRight) j) v := by
  rcases v with v | i | p | e <;> rfl

-- 读法：`weight (L.op (.inr p)) (L.values mask x y s j ∘ L.arg (.inr p))` 等于 `L.pin (s false) (L.batches B (j, p))`。
theorem weight_pin (p : Position n r L.d h) :
    weight (L.op (.inr p)) (L.values mask x y s j ∘ L.arg (.inr p)) =
      L.pin (s false) (L.batches B (j, p)) := by
  have he : (∃ (k : Fin B) (e : G.End), L.pos k e = L.batches B (j, p)) ↔ ∃ e, L.assign e = p := by
    simp only [pos_batches, (L.batches B).injective.eq_iff, Prod.mk.injEq]
    simp
  unfold pin
  simp only [he]
  rfl

-- 读法：`L.kernel i g (fun t => L.values mask x y s j t.1)` 等于 `∏ v : L.Gate, if mask (L.whereAt v) then weight (L.op v) (L.values mask x y s j ∘ L.arg v) else 1`。这里调用 `Finset.prod_subset`。
/-- 先限于可能激活的逻辑门，再取其乘积。

英文原文：Restrict to the potentially active gates before taking their product.
-/
theorem kernel_values (i : Fin n) (g : Fin r) (hm : ∀ z, mask z = true → z i = g) :
    L.kernel i g (fun t => L.values mask x y s j t.1) =
      ∏ v : L.Gate, if mask (L.whereAt v) then
        weight (L.op v) (L.values mask x y s j ∘ L.arg v) else 1 := by
  let f (v : L.Gate) := if mask (L.whereAt v) then
    weight (L.op v) (L.values mask x y s j ∘ L.arg v) else 1
  change (∏ v : L.LocalGate i g, f v.1) = ∏ v, f v
  rw [← Finset.prod_subtype (Finset.univ.filter (fun v => L.whereAt v i = g))
    (p := fun v => L.whereAt v i = g) (by simp) f]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro v _ hv
  exact ite_eq_right (fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hm _ h⟩))

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 单个工作单元的站模板成本

**英文原文**

Cost of one worker's station template
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor Install
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h : ℕ} (L : Layout G n r h) {K q D : ℕ}

omit [Field F] in
-- 读法：`Fintype.card (PortsOf T)` 等于 `arity T`。
private theorem card_ports (T : Table F) : Fintype.card (PortsOf T) = arity T := by
  simp [PortsOf, arity]

-- 读法：要证明的命题是 `Weight F (enabled (L.op v)) ((1 + arity (L.op v)) * (1000 * (rate K q (D + 2) + 1)))`。这里调用 `weight_cheap`。
private theorem enabled_net (hG : G.Admits D (Cheap F K q)) (v : L.Gate) :
    Weight F (enabled (L.op v))
      ((1 + arity (L.op v)) * (1000 * (rate K q (D + 2) + 1))) := by
  have hd : arity (L.op v) ≤ D + 2 ∧ (arity (L.op v) ≤ 3 ∨ L.op v ∈ Cheap F K q) := by
    rcases v with (v|v)|v
    · exact ⟨(hG v).1.trans (Nat.le_add_right _ _), (hG v).2⟩
    · change 2 ≤ D + 2 ∧ (2 ≤ 3 ∨ _)
      exact ⟨by omega, .inl (by decide)⟩
    · change 1 ≤ D + 2 ∧ (1 ≤ 3 ∨ _)
      exact ⟨by omega, .inl (by decide)⟩
  apply (weight_cheap hd.1 hd.2).branch.mono
  rw [card_ports]
  exact le_of_eq (by ring)

-- 读法：`instructions` 的取值由 `∑ v : L.LocalGate i g, (1 + arity (L.op v.val))` 给出。
def instructions (i : Fin n) (g : Fin r) :=
  ∑ v : L.LocalGate i g, (1 + arity (L.op v.val))

-- 读法：`bill` 的取值由 `Fintype.card (L.LocalTape i g) + L.instructions i g * (1002 + 1000 * rate K q (D + 2))` 给出。
def bill (i : Fin n) (g : Fin r) (K q D : ℕ) :=
  Fintype.card (L.LocalTape i g) + L.instructions i g * (1002 + 1000 * rate K q (D + 2))

-- 读法：要证明的命题是 `Weight F (L.kernel i g) (L.bill i g K q D)`。这里调用 `Finset.sum_congr`。
theorem kernel_net (hG : G.Admits D (Cheap F K q)) (i : Fin n) (g : Fin r) :
    Weight F (L.kernel i g) (L.bill i g K q D) := by
  let I (v : L.LocalGate i g) := Unit ⊕ PortsOf (L.op v.val)
  have hp := Weight.sigma_prod (I := I) (fun v => enabled (L.op v.val))
    (fun v => L.enabled_net hG v.val)
  have hp' := hp.pull (fun p : Σ v, I v => L.route i g p.1 p.2)
  refine hp'.mono ?_
  have hsize : Fintype.card (Σ v, I v) = L.instructions i g := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro v _
    change Fintype.card (Unit ⊕ PortsOf (L.op v.val)) = _
    rw [Fintype.card_sum, Fintype.card_unit, card_ports]
  rw [hsize, ← Finset.sum_mul]
  change Fintype.card (L.LocalTape i g) + 2 * L.instructions i g +
    L.instructions i g * (1000 * (rate K q (D + 2) + 1)) ≤ L.bill i g K q D
  unfold bill
  exact le_of_eq (by ring)

-- 读法：存在 `code`，对每个 `x`，`template F w (Sum.elim x code)` 等于 `L.kernel i g (x ∘ idx)`。使用 `weight_program` 给出的结论。
/-- 每次重复计算均可对任意输入数据使用同一二进制脚本，标签激活标志也可任意指定。

英文原文：The same binary script works on arbitrary input data for every
repetition, including arbitrary label activation flags.
-/
theorem kernel_script [Fintype F] (hG : G.Admits D (Cheap F K q)) (i : Fin n) (g : Fin r)
    {w : ℕ} (hw : 2 * L.bill i g K q D ≤ 2 ^ w) (idx : L.LocalTape i g → Fin (2 ^ w)) :
    ∃ code, ∀ x, template F w (Sum.elim x code) = L.kernel i g (x ∘ idx) :=
  weight_program (L.kernel_net hG i g) hw idx

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 一组固定的可编程网络模板

不同行可使用不同大小的模板和不同的重复次数。每行只需提供一份脚本，并在该行的所有输入上重复使用。

**英文原文**

A fixed bank of programmable network templates

Rows can have different template sizes and repetition counts. A single
script is supplied for each row and is reused on all its inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Install Classical

-- 读法：结构的字段包括 `width`、`repetitions`。
structure Bank (I : Type) where
  width : I → ℕ
  repetitions : I → ℕ

namespace Bank
variable {I : Type} [Fintype I] (b : Bank I) (F : Type) [Field F] [Fintype F]

-- 读法：在后续公式中，`Data` 是 `Σ i, Fin (2 ^ b.repetitions i) × Fin (2 ^ b.width i)` 的缩写。
abbrev Data := Σ i, Fin (2 ^ b.repetitions i) × Fin (2 ^ b.width i)
-- 读法：在后续公式中，`Bits` 是 `Σ i, Script F (b.width i + 1)` 的缩写。
abbrev Bits := Σ i, Script F (b.width i + 1)

-- 读法：`result` 的取值由 `∏ i, repeated F (b.width i) (b.repetitions i) (Sum.elim (fun p => s (.inl ⟨i, p⟩)) (fun j => s (.inr ⟨i, j⟩)))` 给出。
def result (s : b.Data ⊕ b.Bits F → Bool) : F :=
  ∏ i, repeated F (b.width i) (b.repetitions i)
    (Sum.elim (fun p => s (.inl ⟨i, p⟩)) (fun j => s (.inr ⟨i, j⟩)))

-- 读法：`budget` 的取值由 `∑ i, templateCost F * 2 ^ (b.repetitions i) * 2 ^ (b.width i) * (b.width i + 2) ^ 3` 给出。
def budget : ℕ := ∑ i, templateCost F * 2 ^ (b.repetitions i) * 2 ^ (b.width i) * (b.width i + 2) ^ 3

-- 读法：要证明的命题是 `Weight F (b.result F) (b.budget F)`。用函数外延性比较等号两侧在 `s` 处的取值。
theorem net : Weight F (b.result F) (b.budget F) := by
  have t := Weight.sigma_prod (fun i => repeated F (b.width i) (b.repetitions i))
    (fun i => repeated_net F (b.width i) (b.repetitions i))
  let e := Equiv.sigmaSumDistrib (fun i => Fin (2 ^ b.repetitions i) × Fin (2 ^ b.width i))
    (fun i => Script F (b.width i + 1))
  unfold budget
  convert t.rename e using 1
  funext s
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (repeated F _ _)
  funext j
  cases j <;> rfl

-- 读法：存在 `c : b.Bits F → Bool`，对每个 `s : b.Data → Bool`，`b.result F (Sum.elim s c)` 等于 `∏ i, ∏ j : Fin (2 ^ b.repetitions i), f i (fun k => s ⟨i, j, src i k⟩)`。这里调用 `Finset.prod_congr`。
/-- 函数的选择及其布线只影响脚本。

英文原文：The choice of the functions and their wiring affects only the scripts.
-/
theorem programs {X : I → Type} [∀ i, Fintype (X i)] (f : (i : I) → (X i → Bool) → F)
    (m : I → ℕ) (hf : ∀ i, Weight F (f i) (m i)) (hm : ∀ i, 2 * m i ≤ 2 ^ b.width i)
    (src : ∀ i, X i → Fin (2 ^ b.width i)) :
    ∃ c : b.Bits F → Bool, ∀ s : b.Data → Bool, b.result F (Sum.elim s c) =
      ∏ i, ∏ j : Fin (2 ^ b.repetitions i), f i (fun k => s ⟨i, j, src i k⟩) := by
  choose code hcode using fun i => weight_program (hf i) (hm i) (src i)
  refine ⟨fun z => code z.1 z.2, fun s => ?_⟩
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact hcode i (fun k => s ⟨i, j, k⟩)

end Bank
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# 模板组的字面编码比特

全零串表示填充。程序的第一位为一，随后每个工作单元占一个比特，以此标识活动工作单元，最后接上脚本。

**英文原文**

Literal bits for a bank of templates

The zero string marks padding. A program starts with a set bit, then
one bit per worker identifying the active worker, then the script.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Bank

variable {n : ℕ} (b : Bank (Fin n)) (F : Type) [Fintype F] (l r : ℕ)
  (hl : 1 + 3 * r + Fintype.card (b.Bits F) ≤ l)

-- 读法：在后续公式中，`LiteralSlot` 是 `Unit ⊕ Fin (3 * r) ⊕ b.Bits F` 的缩写。
abbrev LiteralSlot := Unit ⊕ Fin (3 * r) ⊕ b.Bits F

-- 读法：`literalPort` 的结果类型为 `b.LiteralSlot F r ↪ Fin l`。
def literalPort : b.LiteralSlot F r ↪ Fin l := by
  let row := ((Equiv.refl (Fin (3 * r))).sumCongr (Fintype.equivFin (b.Bits F))).trans finSumFinEquiv
  let head := ((Equiv.ofUnique Unit (Fin 1)).sumCongr row).trans finSumFinEquiv
  exact head.toEmbedding.trans (Fin.castLEEmb (by omega))

-- 读法：在后续公式中，`Literal` 是 `Option (Fin (3 * r) × (b.Bits F → Bool))` 的缩写。
-- 读法：`(b.literalPort F l r hl (.inl ())).val` 等于 `0`。两端由定义化简为同一项。
@[simp] theorem literalPort_zero : (b.literalPort F l r hl (.inl ())).val = 0 := rfl

abbrev Literal := Option (Fin (3 * r) × (b.Bits F → Bool))

-- 读法：逐一匹配以下输入模式：`none, _`、`some _, .inl _`、`some p, .inr (.inl j)`、`some p, .inr (.inr j)`。
private def fields : b.Literal F r → b.LiteralSlot F r → Bool
  | none, _ => false
  | some _, .inl _ => true
  | some p, .inr (.inl j) => decide (p.1 = j)
  | some p, .inr (.inr j) => p.2 j

omit [Fintype F] in
-- 读法：`(b.fields F r)` 是单射。这里调用 `Bool.false_ne_true`。
private theorem fields_inj : Function.Injective (b.fields F r) := by
  rintro (_|p) (_|q) he
  · rfl
  · exact (Bool.false_ne_true (congrFun he (.inl ()))).elim
  · exact (Bool.false_ne_true (congrFun he (.inl ())).symm).elim
  · apply congrArg some
    apply Prod.ext
    · simpa [fields] using congrFun he (.inr (.inl q.1))
    · exact funext fun j => congrFun he (.inr (.inr j))

-- 读法：`literalCode` 的结果类型为 `b.Literal F r ↪ (Fin l → Bool)`。
def literalCode : b.Literal F r ↪ (Fin l → Bool) := by
  let e := b.literalPort F l r hl
  refine ⟨fun p => Function.extend e (b.fields F r p) (fun _ => false), ?_⟩
  intro p q he
  apply b.fields_inj F r
  funext i
  exact ((e.injective.extend_apply _ _ i).symm.trans (congrFun he (e i))).trans
    (e.injective.extend_apply _ _ i)

-- 读法：`b.literalCode F l r hl p (b.literalPort F l r hl i)` 等于 `b.fields F r p i`。使用 `b.literalPort` 给出的结论。
private theorem literalCode_at (p : b.Literal F r) (i : b.LiteralSlot F r) :
    b.literalCode F l r hl p (b.literalPort F l r hl i) = b.fields F r p i :=
  (b.literalPort F l r hl).injective.extend_apply (b.fields F r p) (fun _ => false) i

-- 读法：`b.literalCode F l r hl p i` 等于 `false`。使用 `Function.extend_apply'` 给出的结论。
theorem literalCode_pad (p : b.Literal F r) (i : Fin l)
    (hi : i ∉ Set.range (b.literalPort F l r hl)) :
    b.literalCode F l r hl p i = false :=
  Function.extend_apply' (b.fields F r p) (fun _ => false) i hi

-- 读法：`b.literalCode F l r hl none i` 等于 `false`。按 `i ∈ Set.range (b.literalPort F l r hl)` 成立与否分情况。
@[simp] theorem literalCode_none (i : Fin l) : b.literalCode F l r hl none i = false := by
  by_cases hi : i ∈ Set.range (b.literalPort F l r hl)
  · obtain ⟨j, rfl⟩ := hi
    exact b.literalCode_at F l r hl none j
  · exact b.literalCode_pad F l r hl none i hi

variable (p : Fin (3 * r) × (b.Bits F → Bool))

-- 读法：`b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inl ()))` 等于 `true`。使用 `b.literalCode_at` 给出的结论。
@[simp] theorem literalCode_flag :
    b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inl ())) = true :=
  b.literalCode_at F l r hl (some p) (.inl ())

-- 读法：`b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inr (.inl j)))` 等于 `decide (p.1 = j)`。使用 `b.literalCode_at` 给出的结论。
@[simp] theorem literalCode_worker (j : Fin (3 * r)) :
    b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inr (.inl j))) = decide (p.1 = j) :=
  b.literalCode_at F l r hl (some p) (.inr (.inl j))

-- 读法：`b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inr (.inr j)))` 等于 `p.2 j`。使用 `b.literalCode_at` 给出的结论。
@[simp] theorem literalCode_script (j : b.Bits F) :
    b.literalCode F l r hl (some p) (b.literalPort F l r hl (.inr (.inr j))) = p.2 j :=
  b.literalCode_at F l r hl (some p) (.inr (.inr j))

end OAI.LinearAlgebra.MatrixExponent.Processor.Bank
end

/-!
# 在同一站点的各副本中复用一份站脚本

**英文原文**

Reusing one station script in all copies at a site
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h B : ℕ} (L : Layout G n r h) (A : Expansion F n h)
  {hn : 2 ≤ n} {N : ℕ} {R : A.Report r (B * L.d)}

-- 读法：`siteMask` 的取值由 `decide (A.owner hn N R z = u)` 给出。
def siteMask (u : Worker r) (z : Label n r) : Bool := decide (A.owner hn N R z = u)

-- 读法：`L.base A x y s u` 等于 `∏ j, L.kernel i g (fun t => L.values (siteMask L A (hn := hn) (N := N) (R := R) u) x y (A.rows s) j t.1)`。
theorem base_kernel (u : Worker r) (i : Fin n) (g : Fin r)
    (ho : ∀ z, A.owner hn N R z = u → z i = g)
    (x : Fin B → Val a) (y : Fin B → Val b) (s : A.Assignment hn N R) :
    L.base A x y s u = ∏ j, L.kernel i g
      (fun t => L.values (siteMask L A (hn := hn) (N := N) (R := R) u) x y (A.rows s) j t.1) := by
  let f := siteMask L A (hn := hn) (N := N) (R := R) u
  have hf : ∀ z, f z = true → z i = g := fun z h => ho _ (of_decide_eq_true h)
  let v (j : Fin B) (q : G.normalized.V) :=
    if A.owner hn N R (L.color q) = u then
      G.normalized.vertex (x j) (y j) (L.read (A.rows s q.isRight) j) q else 1
  let p (t : Position n r (B * L.d) h) :=
    if A.owner hn N R (Expansion.endpoint t false) = u then L.pin (A.rows s false) t else 1
  have hw (j : Fin B) : L.kernel i g (fun t => L.values f x y (A.rows s) j t.1) =
      (∏ q, v j q) * (∏ t, p (L.batches B (j, t))) := by
    rw [kernel_values _ _ _ _ _ _ _ _ hf, Fintype.prod_sum_type]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro q _
      rw [L.weight_vertex f x y (A.rows s) j q]
      simp only [f, siteMask, decide_eq_true_eq, whereAt, v]
    · apply Finset.prod_congr rfl
      intro t _
      rw [L.weight_pin f x y (A.rows s) j t]
      simp only [f, siteMask, decide_eq_true_eq, whereAt]
      rfl
  change L.base A x y s u = ∏ j, L.kernel i g (fun t => L.values f x y (A.rows s) j t.1)
  simp_rw [hw]
  rw [Finset.prod_mul_distrib, base, Fintype.prod_sum_type, Fintype.prod_prod_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    rintro (q|q) _ <;> rfl
  · change (∏ t, p t) = _
    rw [← (L.batches B).prod_comp p, Fintype.prod_prod_type]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 为工作单元选出活动标签与批次副本

**英文原文**

Selecting a worker's active labels and batch copies
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor Finset
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h B : ℕ} (L : Layout G n r h)

-- 读法：当 `mask (L.which t)` 成立时取 `y t`，否则取 `false`。
/-- 不活动的数据可直接置零，无需远程读取。

英文原文：Inactive data can be replaced by zero instead of being read remotely.
-/
def active (mask : Label n r → Bool) (y : L.Tape → Bool) (t : L.Tape) : Bool :=
  if mask (L.which t) then y t else false

-- 读法：`L.kernel i g (fun _ => false)` 等于 `1`。这里调用 `prod_eq_one`。
theorem kernel_zero (i : Fin n) (g : Fin r) : L.kernel i g (fun _ => false) = 1 := by
  unfold kernel
  apply prod_eq_one
  intro v _
  rfl

-- 读法：`L.kernel i g (fun t => L.active mask (L.values mask x y s j) t.val)` 等于 `L.kernel i g (fun t => L.values mask x y s j t.val)`。这里调用 `prod_congr`。
private theorem kernel_active (i : Fin n) (g : Fin r) (mask : Label n r → Bool)
    (x : Fin B → Val a) (y : Fin B → Val b) (s : Bool → L.Slots B) (j : Fin B) :
    L.kernel i g (fun t => L.active mask (L.values mask x y s j) t.val) =
      L.kernel i g (fun t => L.values mask x y s j t.val) := by
  unfold kernel
  apply prod_congr rfl
  intro v _
  by_cases hv : mask (L.whereAt v.val) = true
  · apply congrArg (enabled (L.op v.val))
    funext q
    cases q with
    | inl k => exact ite_eq_left hv
    | inr k => exact ite_eq_left ((congrArg mask (L.arg_local v.val k)).trans hv)
  · have he : mask (L.whereAt v.val) = false := Bool.eq_false_of_not_eq_true hv
    simp [enabled, route, active, which, values, he]

variable (A : Expansion F n h) {hn : 2 ≤ n} {N : ℕ} {R : A.Report r (B * L.d)}

-- 读法：`symbol` 的取值由 `| .home g | .station g | .packet g => g` 给出。
def symbol : Worker r → Fin r
  | .home g | .station g | .packet g => g

-- 读法：逐一匹配以下输入模式：`.home _ | .packet _`、`.station _`。
def axis (hn : 2 ≤ n) (i : Fin n) : Worker r → Fin n
  | .home _ | .packet _ => i
  | .station _ => other hn i

-- 读法：`z (axis hn R.1 u)` 等于 `symbol u`。
private theorem owner_here (u : Worker r) (z : Label n r)
    (he : A.owner hn N R z = u) : z (axis hn R.1 u) = symbol u := by
  subst u
  unfold Expansion.owner
  split <;> rfl

-- 读法：`entry` 的结果类型为 `Bool`。
/-- 工作单元数据的一行中指定比特的内容。

英文原文：Contents of a named bit in one row of the worker's data.
-/
def entry (u : Worker r) (x : Fin B → Val a) (y : Fin B → Val b)
    (s : A.Assignment hn N R) (i : Fin n) (j : ℕ) (t : L.LocalTape i (symbol u)) : Bool :=
  if hj : j < B ∧ i = axis hn R.1 u then
    let mask := L.siteMask A (hn := hn) (N := N) (R := R) u
    L.active mask (L.values mask x y (A.rows s) ⟨j, hj.1⟩) t.1
  else false

-- 读法：`L.base A x y s u` 等于 `∏ i, ∏ j : Fin (len i), L.kernel i (symbol u) (L.entry A u x y s i j.val)`。
theorem base_entries (u : Worker r) (x : Fin B → Val a) (y : Fin B → Val b)
    (s : A.Assignment hn N R) (len : Fin n → ℕ) (hl : ∀ i, B ≤ len i) :
    L.base A x y s u =
      ∏ i, ∏ j : Fin (len i), L.kernel i (symbol u) (L.entry A u x y s i j.val) := by
  let i := axis hn R.1 u
  rw [Fintype.prod_eq_single i]
  · rw [L.base_kernel A u i (symbol u) (L.owner_here A u) x y s]
    symm
    rw [prod_padded (Fin.castLEEmb (hl i))]
    · refine prod_congr rfl (fun t _ => ?_)
      -- 推导：记下中间结论 `he`：`(Fin.castLEEmb (hl i) t).val < B ∧ i = axis hn R.1 u`。
      have he : (Fin.castLEEmb (hl i) t).val < B ∧ i = axis hn R.1 u := ⟨t.2, rfl⟩
      unfold entry
      simp only [dite_eq_left he]
      exact L.kernel_active _ _ _ _ _ _ _
    · intro j hj
      have he : ¬ (j.val < B ∧ i = axis hn R.1 u) := fun h => hj ⟨⟨j, h.1⟩, rfl⟩
      unfold entry
      simp only [dite_eq_right he, kernel_zero]
  · intro k hk
    apply prod_eq_one
    intro j _
    -- 推导：记下中间结论 `he`：`¬ (j.val < B ∧ k = axis hn R.1 u)`。
    have he : ¬ (j.val < B ∧ k = axis hn R.1 u) := fun h => hk h.2
    unfold entry
    simp only [dite_eq_right he, kernel_zero]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 供所有报告与所有副本共用的一套脚本

**英文原文**

One set of scripts for all reports and all copies
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Processor
variable {F : Type} [Field F] [Fintype F] {a b : Wire} {G : Diagram F a b}
  {n r h B K q D : ℕ} (L : Layout G n r h)
  (M : Bank (Fin n)) (u : Worker r)

-- 读法：在后续公式中，`Index` 是 `(i : Fin n) → L.LocalTape i (symbol u) → Fin (2 ^ M.width i)` 的缩写。
/-- 地址选择是脚本的一部分。选取地址时不必保持顺序，可以按控制器的数据布局选择。

英文原文：The choice of addresses is part of the script. It need not preserve
order, and can be chosen to match the controller's data layout.
-/
abbrev Index := (i : Fin n) → L.LocalTape i (symbol u) → Fin (2 ^ M.width i)

-- 读法：`station_scripts` 的证明用到 `M.programs`、`L.kernel`、`L.kernel_net`。
theorem station_scripts (hG : G.Admits D (Cheap F K q))
    (hw : ∀ i, 2 * L.bill i (symbol u) K q D ≤ 2 ^ M.width i)
    (hl : ∀ i, B ≤ 2 ^ M.repetitions i) (idx : L.Index M u) :
    ∃ c : M.Bits F → Bool, ∀ (A : Expansion F n h) (hn : 2 ≤ n) (N : ℕ)
      (R : A.Report r (B * L.d)) (x : Fin B → Val a) (y : Fin B → Val b)
      (s : A.Assignment hn N R) (z : M.Data → Bool),
      (∀ i j v, z ⟨i, j, idx i v⟩ = L.entry A u x y s i j.val v) →
      M.result F (Sum.elim z c) = L.base A x y s u := by
  obtain ⟨c, hc⟩ := M.programs F (fun i => L.kernel i (symbol u)) _
    (fun i => L.kernel_net hG i (symbol u)) hw idx
  refine ⟨c, fun A hn N R x y s z hz => ?_⟩
  rw [hc, L.base_entries A u x y s _ hl]
  simp only [hz]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 与替换图无关的公开数据

处理器需要知道外部着色和包数。内部顶点的分配及其表完全由该处理器的站脚本编码。

**英文原文**

Public data independent of the replacement graph

A processor needs to know the exterior coloring and the number of
packets. The assignment to interior vertices and their tables is
entirely encoded by its station script.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Classical
variable {F : Type} [Field F] {N l d B n r h : ℕ}

-- 读法：在后续公式中，`Tape` 是 `Label n r ⊕ (Position n r t h × Bool) ⊕ slots (copies (Machine.tape N l l) d) ⊕ slots (copies .unit d)` 的缩写。
abbrev Tape (N l d n r h t : ℕ) :=
  Label n r ⊕ (Position n r t h × Bool) ⊕ slots (copies (Machine.tape N l l) d) ⊕ slots (copies .unit d)

-- 读法：结构的字段包括 `count`、`colors`、`which`。
structure Format (N l d n r h : ℕ) where
  count : ℕ
  colors : Machine.Ports N l l → Label n r
  which : Tape N l d n r h count → Label n r

namespace Format

-- 读法：`ofScheme` 的取值由 `⟨S.layout.d, S.colors, S.layout.which⟩` 给出。
def ofScheme {G : MachineDiagram F N l l d} {A : Expansion F n h} {hn : 2 ≤ n}
    (S : Scheme A hn G r B) : Format N l d n r h :=
  ⟨S.layout.d, S.colors, S.layout.which⟩

-- 读法：用字段 `count`、`colors` 构造 `Format N l d n r h`。
def prescribed (d h t : ℕ) (fa : Machine.Ports N l l → Label n r) : Format N l d n r h where
  count := t
  colors := fa
  which
    | .inl z => z
    | .inr (.inl (p, s)) => Expansion.endpoint p s
    | .inr (.inr (.inl i)) => fa (Machine.address N l l (port (Machine.tape N l l) d i).2)
    | .inr (.inr (.inr i)) => (port .unit d i).2.elim

-- 读法：`ofScheme S` 等于 `prescribed d h t fa`。用函数外延性比较等号两侧在 `u` 处的取值。
theorem ofScheme_eq {G : MachineDiagram F N l l d} {A : Expansion F n h} {hn : 2 ≤ n}
    (S : Scheme A hn G r B) {fa : Machine.Ports N l l → Label n r} {t : ℕ}
    (hf : S.colors = fa) (ht : S.layout.d = t) : ofScheme S = prescribed d h t fa := by
  subst fa t
  unfold ofScheme prescribed
  congr 1
  funext u
  rcases u with z | ⟨p, s⟩ | i | i
  · rfl
  · rfl
  · exact S.exterior i
  · exact (port .unit d i).2.elim

variable (P : Format N l d n r h) (M : Bank (Fin n))

-- 读法：在后续公式中，`LocalTape` 是 `{u : Tape N l d n r h P.count // P.which u i = g}` 的缩写。
abbrev LocalTape (i : Fin n) (g : Fin r) := {u : Tape N l d n r h P.count // P.which u i = g}
-- 读法：在后续公式中，`Index` 是 `(i : Fin n) → (g : Fin r) → P.LocalTape i g ↪ Fin (2 ^ M.width i)` 的缩写。
abbrev Index := (i : Fin n) → (g : Fin r) → P.LocalTape i g ↪ Fin (2 ^ M.width i)

variable (A : Expansion F n h) (hn : 2 ≤ n) (B : ℕ)

-- 读法：在后续公式中，`Reports` 是 `A.Accepted (r := r) (d := B * P.count) hn (A.budget hn N)` 的缩写。
abbrev Reports := A.Accepted (r := r) (d := B * P.count) hn (A.budget hn N)

-- 读法：`route` 的取值由 `A.owner hn N R.val ∘ P.colors` 给出。
def route (R : P.Reports A hn B) := A.owner hn N R.val ∘ P.colors

-- 读法：在后续公式中，`Serial` 是 `A.ExtraSerial hn N R.val (Worker.index r) (Pin.src (P.route A hn B R)) (Pin.dst (P.route A hn B R))` 的缩写。
abbrev Serial (R : P.Reports A hn B) := A.ExtraSerial hn N R.val (Worker.index r)
  (Pin.src (P.route A hn B R)) (Pin.dst (P.route A hn B R))

variable (R : P.Reports A hn B) (s : A.Assignment hn N R.val)
  (x : Fin B → Val (copies (Machine.tape N l l) d)) (u : Worker r)

-- 读法：逐一匹配以下输入模式：`.inl z`、`.inr (.inl (p, v))`、`.inr (.inr (.inl i))`、`.inr (.inr (.inr i))`。
def raw (j : Fin B) : Tape N l d n r h P.count → Bool
  | .inl z => decide (A.owner hn N R.val z = u)
  | .inr (.inl (p, v)) => A.rows s v (p.1.1, finProdFinEquiv (j, p.1.2)) p.2
  | .inr (.inr (.inl i)) => bits (copies (Machine.tape N l l) d) (x j) i
  | .inr (.inr (.inr i)) => bits (copies .unit d) (unitCopies d) i

-- 读法：`fill` 的结果类型为 `Bool`。
def fill (idx : P.Index M) (z : M.Data) : Bool :=
  if hv : z.2.1.val < B ∧ z.1 = Layout.axis hn R.val.1 u then
    Function.extend (idx z.1 (Layout.symbol u)) (fun t =>
      if A.owner hn N R.val (P.which t.1) = u then P.raw A hn B R s x u ⟨z.2.1.val, hv.1⟩ t.1
      else false) (fun _ => false) z.2.2
  else false

end Format
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# 在程序站点读取与站点无关的地址格式

**英文原文**

Reading a site-independent address format at a program site
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Format

open Classical Diagonal
variable {F : Type} [Field F] {N l d B n r h : ℕ}
  {G : MachineDiagram F N l l d} {A : Expansion F n h} {hn : 2 ≤ n}
  (S : Scheme A hn G r B) (M : Bank (Fin n)) (idx : (ofScheme S).Index M)
  (R : S.Report) (s : A.Assignment hn N R.val)
  (x : Fin B → Val (copies (Machine.tape N l l) d)) (u : Worker r)

-- 读法：`(ofScheme S).raw A hn B R s x u j p` 等于 `S.layout.values (S.layout.siteMask A (hn := hn) (N := N) (R := R.val) u) x (fun _ => unitCopies d) (A.rows s) j p`。
private theorem raw_eq (j : Fin B) (p : S.layout.Tape) :
    (ofScheme S).raw A hn B R s x u j p = S.layout.values
      (S.layout.siteMask A (hn := hn) (N := N) (R := R.val) u) x (fun _ => unitCopies d) (A.rows s) j p := by
  rcases p with z|⟨p, b⟩|i|j <;> rfl

-- 读法：`(ofScheme S).fill M A hn B R s x u idx ⟨i, j, idx i (Layout.symbol u) p⟩` 等于 `S.layout.entry A u x (fun _ => unitCopies d) s i j.val p`。按 `j.val < B ∧ i = Layout.axis hn R.val.1 u` 成立与否分情况。
theorem fill_entry (i : Fin n) (j : Fin (2 ^ M.repetitions i))
    (p : S.layout.LocalTape i (Layout.symbol u)) :
    (ofScheme S).fill M A hn B R s x u idx ⟨i, j, idx i (Layout.symbol u) p⟩ =
      S.layout.entry A u x (fun _ => unitCopies d) s i j.val p := by
  unfold fill Layout.entry
  by_cases hv : j.val < B ∧ i = Layout.axis hn R.val.1 u
  · simp only [dite_eq_left hv]
    let g (t : (ofScheme S).LocalTape i (Layout.symbol u)) :=
      if A.owner hn N R.val ((ofScheme S).which t.1) = u then (ofScheme S).raw A hn B R s x u ⟨j.val, hv.1⟩ t.1 else false
    refine ((idx i (Layout.symbol u)).injective.extend_apply g (fun _ => false) p).trans ?_
    unfold Layout.active Layout.siteMask
    simp only [decide_eq_true_eq]
    exact congrArg (fun t => if A.owner hn N R.val (S.layout.which p.1) = u then t else false)
      (raw_eq S R s x u _ p.1)
  · simp only [dite_eq_right hv]

end OAI.LinearAlgebra.MatrixExponent.Processor.Format
end

/-!
# 与图的内部结构无关的解释器

唯一随图而变的输入是一个字面值，由一个处理器编号与一组脚本构成。连线编号可以依赖于公开报告。在给出任何压缩图式前便固定各比特长度。

**英文原文**

An interpreter independent of the interior of the graph

The only graph-specific input is the literal, consisting of a processor
number and one bank of scripts. Wire numbering may depend on the public
report. The bit lengths are fixed before any compressed diagram is given.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Classical Machine
variable {F : Type} [Field F] [Fintype F] {N l d B n r h : ℕ}

-- 读法：结构的字段包括 `index`、`number`、`links`、`packets`、`pins`。
structure Controller (P : Format N l d n r h) (A : Expansion F n h)
    (hn : 2 ≤ n) (M : Bank (Fin n)) (B : ℕ) where
  index : P.Index M
  number : (R : P.Reports A hn B) → P.Serial A hn B R
  links : 64 * (3 * r) ^ 2 ≤ N
  packets : ∀ s : Packet n r (B * P.count) → A.I, A.budget hn N (A.report hn s)
  pins : ∀ (R : A.Report r (B * P.count)) (u : Worker r),
    let f := A.owner hn N R ∘ P.colors
    128 * Fintype.card {e : Pin N l l r // Pin.src f e ≠ Pin.dst f e ∧
      (Pin.src f e = u ∨ Pin.dst f e = u)} ≤ N
  fits : Nat.clog 2 n + r ^ 3 * Fintype.card A.I * Nat.clog 2 (Fintype.card (Packet n r (B * P.count)) + 1)
    + 1 ≤ l
  literal : 1 + 3 * r + Fintype.card (M.Bits F) ≤ l

namespace Controller

variable {P : Format N l d n r h} {A : Expansion F n h} {hn : 2 ≤ n} {M : Bank (Fin n)}
  (C : Controller P A hn M B)

-- 读法：在后续公式中，`code` 是 `M.literalCode F l r C.literal` 的缩写。
abbrev code := M.literalCode F l r C.literal

-- 读法：`pad` 的取值由 `feed (C.code none) (fun _ => false) (fun _ => false)` 给出。
def pad : Val (tape N l l) := feed (C.code none) (fun _ => false) (fun _ => false)

-- 读法：`joint` 的取值由 `let x := P.fill M A hn B R s (Pin.input C.pad y) u C.index Pin.mask F u ξ y * (M.result F (Sum.elim x c) * A.factor s u)` 给出。
/-- 私有指派同时提供原有外部值以及原有各站所需的包槽位。

英文原文：The private assignment supplies both the old exterior values and
the packet slots required by the original stations.
-/
def joint (R : P.Reports A hn B) (c : M.Bits F → Bool) (ξ : Fin l → Bool) (u : Worker r)
    (y : Pin N l l r → Bool) (s : A.Assignment hn N R.1) : F :=
  let x := P.fill M A hn B R s (Pin.input C.pad y) u C.index
  Pin.mask F u ξ y * (M.result F (Sum.elim x c) * A.factor s u)

-- 读法：`site` 的构造用到 `A.extraProcessor`、`Worker.index`、`R.2.2`。
def site (i : Fin (3 * r)) (c : M.Bits F → Bool) (R : P.Reports A hn B) (y : Fin (N / 4) → Bool) :=
  A.extraProcessor hn N R.1 (Worker.index r) R.2.2 C.links
    (Pin.src (P.route A hn B R)) (Pin.dst (P.route A hn B R)) (C.pins R.1)
    (C.joint R c (C.code (some (i, c)))) (C.number R) i y

-- 读法：`run` 的取值由 `branch (A.encodeReport hn N r (B * P.count) l C.fits) (C.site i c) z y` 给出。
/-- 解释器的表在一个合法脚本字面值处的内容。

英文原文：The contents of an interpreter table at a valid script literal.
-/
def run (i : Fin (3 * r)) (c : M.Bits F → Bool) (z : Fin l → Bool) (y : Fin (N / 4) → Bool) :=
  branch (A.encodeReport hn N r (B * P.count) l C.fits) (C.site i c) z y

-- 读法：`Agrees` 表示以下条件：`U C.pad () = 1` 与 `∀ i c z y, U (feed (C.code (some (i, c))) z y) () = C.run i c z y` 同时成立。
def Agrees (U : Val (tape N l l) → Val .unit → F) : Prop :=
  U C.pad () = 1 ∧ ∀ i c z y, U (feed (C.code (some (i, c))) z y) () = C.run i c z y

end Controller
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# 用各站的局部脚本为替换操作编程

**英文原文**

Programming a replacement with its local station scripts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal Machine

variable {F : Type} [Field F] [Fintype F] {N l d B n r h K q D : ℕ}
  {G : MachineDiagram F N l l d} {A : Expansion F n h} {hn : 2 ≤ n}
  {P : Format N l d n r h} {M : Bank (Fin n)} (C : Controller P A hn M B)
  (S : Scheme A hn G r B) (hP : Format.ofScheme S = P)
  (hG : G.Admits D (Cheap F K q))
  (hw : ∀ i g, 2 * S.layout.bill i g K q D ≤ 2 ^ M.width i)
  (hl : ∀ i, B ≤ 2 ^ M.repetitions i)

include hP hG hw hl in
-- 读法：要证明的命题是 `S.Programs C.pad U (S.encodeReport hf)`。
/-- 图专用的脚本很短，在获知任何报告、输入指派或物理链路上的取值前就已固定。

英文原文：The graph-specific script is short and fixed before any report,
input assignment or physical-link value is known.
-/
theorem programs (hf : S.fits) (U : Val (tape N l l) → Val .unit → F) (hu : C.Agrees U) :
    S.Programs C.pad U (S.encodeReport hf) := by
  subst P
  refine ⟨C.number, fun u => ?_⟩
  let v := (Worker.index r).symm u
  obtain ⟨c, hc⟩ := S.layout.station_scripts M v hG (fun i => hw i _) hl
    (fun i => C.index i (Layout.symbol v))
  let ξ := C.code (some (u, c))
  refine ⟨ξ, fun z y => ?_⟩
  have he (R : S.Report) : C.joint R c ξ v = S.joint C.pad R ξ v := by
    funext p a
    unfold joint Scheme.joint Layout.localWeight
    refine congrArg (fun x => Pin.mask F v ξ p * (x * A.factor a v)) ?_
    apply hc A hn N R.1 (Pin.input C.pad p) (fun _ => unitCopies d) a
    exact Format.fill_entry S M C.index R a _ v
  -- 推导：记下中间结论 `ht`：`C.site u c = fun R => S.simulate C.pad R (C.number R) u ξ`。
  have ht : C.site u c = fun R => S.simulate C.pad R (C.number R) u ξ := by
    funext R
    exact A.extraProcessor_congr hn N R.1 (Worker.index r) R.2.2 C.links _ _ (C.pins R.1)
      (C.number R) u (he R)
  rw [hu.2 u c z y, run, ht]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 给定尺度下的脚本容量与数据容量

**英文原文**

Script and data capacity at a fixed scale
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l d B n r h K q D C : ℕ}
  {G : MachineDiagram F N l l d} {A : Expansion F n h} {hn : 2 ≤ n}
  (S : Scheme A hn G r B) (M : Bank (Fin n))

omit [Fintype F] in
-- 读法：`2 * S.layout.bill i g K q D` 不超过 `2 ^ (M.width i)`。
theorem bill_bound (hc : S.compact C) (hd : D ^ 2 ≤ N) (hr : 0 < r) (hm : r ^ n ≤ C * N * d)
    (hw : ∀ i, 1000000 * C * N * d * rate K q (N + 2) ≤ 2 ^ (M.width i) * r) (i : Fin n) (g : Fin r) :
    2 * S.layout.bill i g K q D ≤ 2 ^ (M.width i) := by
  let t := C * N * d
  have hp : Fintype.card (Position n r S.layout.d h) ≤ 13 * t := by simpa [t, mul_assoc] using hc.1
  have hv : ∀ z, multiplicity S.layout.color z * r ^ n ≤ 16 * t := by simpa [t, mul_assoc] using hc.2
  have hT := S.layout.tape_bound hv hp hm i g
  have hG : S.layout.instructions i g * r ≤ 100 * t := S.layout.gate_bound hv hp i g
  have hD : D ≤ N := (Nat.le_pow (by decide : 0 < 2)).trans hd
  let R := rate K q (N + 2)
  -- 推导：记下中间结论 `hr'`：`2 ≤ R`。
  have hr' : 2 ≤ R := Nat.le_add_right _ _
  have hh : rate K q (D + 2) ≤ R := by unfold R rate; gcongr
  apply (Nat.mul_le_mul_right_iff hr).1
  refine le_trans ?_ (hw i)
  calc
    _ = 2 * (Fintype.card (S.layout.LocalTape i g) * r +
          (S.layout.instructions i g * r) * (1002 + 1000 * rate K q (D + 2))) := by unfold Layout.bill; ring
    _ ≤ 2 * (100 * t + 100 * t * (1002 + 1000 * R)) := by gcongr
    _ = t * (200 + 200 * (1002 + 1000 * R)) := by ring
    _ ≤ t * (1000000 * R) := by gcongr; omega
    _ = _ := by unfold t R; ring

-- 读法：`(Controller (Format.ofScheme S) A hn M B)` 有元素。这里调用 `Function.Embedding.nonempty_of_card_le`。
theorem controller_exists (hf : S.fits) (hl : 1 + 3 * r + Fintype.card (M.Bits F) ≤ l)
    (hw : ∀ i g, 2 * S.layout.bill i g K q D ≤ 2 ^ M.width i) :
    Nonempty (Controller (Format.ofScheme S) A hn M B) := by
  have h (i : Fin n) (g : Fin r) :
      Nonempty (S.layout.LocalTape i g ↪ Fin (2 ^ M.width i)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    have := hw i g
    unfold Layout.bill at this
    omega
  exact ⟨⟨fun i g => (h i g).some, fun _ _ _ => (Fintype.equivFin _).symm,
    S.links, S.packets, S.pins, hf, hl⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Processor
end
