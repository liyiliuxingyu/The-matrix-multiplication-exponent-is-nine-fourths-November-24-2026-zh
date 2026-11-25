-- 本文件所属证明环节：给不同处理器和独立副本分配地址、切口、信道和广播资源，把虚拟连线送上实际网络，控制由固定模板带来的额外开销。
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import OAI.LinearAlgebra.MatrixExponent.Diagram.Normalize

section
/-!
# 平衡有限多个权重类别

对所有颜色、所有类别的偏差平方求和。在每个顶点，都能选到一个使交叉项总和非正的颜色。

**英文原文**

Balancing finitely many weight classes

The squared discrepancies are summed over every color and class.
At each vertex some color makes the total cross term nonpositive.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Finset
variable {X Z I : Type*} [Fintype Z] [Nonempty Z] [DecidableEq Z]

-- 读法：`dev` 的取值由 `∑ x ∈ s, ((if f x = z then w x else 0) - w x / Fintype.card Z)` 给出。
private noncomputable def dev (s : Finset X) (f : X → Z) (w : X → ℝ) (z : Z) : ℝ :=
  ∑ x ∈ s, ((if f x = z then w x else 0) - w x / Fintype.card Z)

-- 读法：结论为 `∑ z, dev s f w z = 0`。这里调用 `sum_eq_zero`。
private theorem sum_dev (s : Finset X) (f : X → Z) (w : X → ℝ) :
    ∑ z, dev s f w z = 0 := by
  unfold dev
  rw [sum_comm]
  apply sum_eq_zero
  intro x _
  simp [sum_sub_distrib, mul_div_cancel₀, Fintype.card_ne_zero]

-- 读法：结论为 `∑ z, (d z + ((if c = z then u else 0) - u / Fintype.card Z)) ^ 2 ≤ (∑ z, (d z) ^ 2) + 2 * u * d c + u ^ 2`。
private theorem step (d : Z → ℝ) (hd : ∑ z, d z = 0) (u : ℝ) (c : Z) :
    ∑ z, (d z + ((if c = z then u else 0) - u / Fintype.card Z)) ^ 2 ≤
      (∑ z, (d z) ^ 2) + 2 * u * d c + u ^ 2 := by
  let k : ℝ := Fintype.card Z
  have hk : 0 < k := by unfold k; exact_mod_cast Fintype.card_pos (α := Z)
  have expand (z : Z) : (d z + ((if c = z then u else 0) - u / k)) ^ 2 =
      (d z) ^ 2 + (if c = z then 2 * u * d z + u ^ 2 - 2 * u * (u / k) else 0) +
        (u / k) ^ 2 - 2 * (u / k) * d z := by split <;> ring
  change (∑ z, (d z + ((if c = z then u else 0) - u / k)) ^ 2) ≤ _
  simp only [expand, sum_sub_distrib, sum_add_distrib, sum_ite_eq, mem_univ, ite_true,
    sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hd, mul_zero, sub_zero]
  have he : k * (u / k) ^ 2 - 2 * u * (u / k) = -(u ^ 2 / k) := by field_simp; ring
  dsimp only [k] at he hk ⊢
  linarith [div_nonneg (sq_nonneg u) hk.le]

variable [Fintype I]

-- 读法：存在 `f : X → Z`，结论为 `∑ i, ∑ z, (dev s f (w i) z) ^ 2 ≤ ∑ i, ∑ x ∈ s, (w i x) ^ 2`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
private theorem energy (w : I → X → ℝ) (s : Finset X) :
    ∃ f : X → Z, ∑ i, ∑ z, (dev s f (w i) z) ^ 2 ≤ ∑ i, ∑ x ∈ s, (w i x) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp [dev]⟩
  | @insert x s hx ih =>
    obtain ⟨f, hf⟩ := ih
    have hsum : ∑ z, (∑ i, 2 * w i x * dev s f (w i) z) ≤ ∑ _z : Z, (0 : ℝ) := by
      rw [sum_comm]
      simp [← mul_sum, sum_dev]
    -- 推导：从 `exists_le_of_sum_le univ_nonempty hsum` 中取出 `c, _, hc`。
    obtain ⟨c, _, hc⟩ := exists_le_of_sum_le univ_nonempty hsum
    let g (y : X) := if y = x then c else f y
    have hg (i : I) (z : Z) : dev (insert x s) g (w i) z =
        dev s f (w i) z + ((if c = z then w i x else 0) - w i x / Fintype.card Z) := by
      unfold dev
      rw [sum_insert hx, add_comm, show g x = c by simp [g]]
      congr 1
      apply sum_congr rfl
      intro y hy
      rw [show g y = f y by simp [g, show y ≠ x by rintro rfl; exact hx hy]]
    refine ⟨g, ?_⟩
    simp only [hg, sum_insert hx]
    -- 推导：记下中间结论 `hb`：`= sum_le_sum (s`。
    have hb := sum_le_sum (s := univ) (fun i _ => step _ (sum_dev s f (w i)) (w i x) c)
    simp only [sum_add_distrib] at hb ⊢
    linarith

-- 读法：存在 `f : X → Z`，对每个 `i z`，`((∑ x, if f x = z then w i x else 0) - (∑ x, w i x) / Fintype.card Z) ^ 2` 不超过 `∑ j, ∑ x, (w j x) ^ 2`。
/-- 每一类别与颜色对应的偏差平方，至多为所有类别的权重平方和。权重可正可负。

英文原文：Every class and color has squared discrepancy at most the sum of
squared weights across all classes. Weights may have either sign.
-/
theorem color [Fintype X] (w : I → X → ℝ) :
    ∃ f : X → Z, ∀ i z,
      ((∑ x, if f x = z then w i x else 0) - (∑ x, w i x) / Fintype.card Z) ^ 2 ≤
        ∑ j, ∑ x, (w j x) ^ 2 := by
  obtain ⟨f, hf⟩ := energy (Z := Z) w univ
  refine ⟨f, fun i z => ?_⟩
  rw [sum_div, ← sum_sub_distrib]
  calc
    _ ≤ ∑ y, (dev univ f (w i) y) ^ 2 := single_le_sum (fun _ _ => sq_nonneg _) (mem_univ z)
    _ ≤ _ := (single_le_sum (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_univ i)).trans hf

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 为二分图的一侧着色

按远端的指定颜色对边分组。一个顶点在任一类中的负载至多为其度数，故负载平方和至多为最大度数与边数之积。

**英文原文**

Coloring one side of a bipartite graph

Group edges by the prescribed color of their far endpoint. The load of
a vertex in any class is at most its degree, so the sum of squared
loads is at most the maximum degree times the number of edges.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Finset
variable {V E Z : Type*} [Fintype V] [Fintype E] [Fintype Z] [DecidableEq V] [DecidableEq Z]

-- 读法：`load` 的取值由 `Fintype.card {e // src e = v ∧ col e = y}` 给出。
private def load (src : E → V) (col : E → Z) (y : Z) (v : V) : ℝ :=
  Fintype.card {e // src e = v ∧ col e = y}

omit [Fintype Z] in
-- 读法：结论为 `∑ v, (if p v then load src col y v else 0) = Fintype.card {e // p (src e) ∧ col e = y}`。
private theorem load_sum (src : E → V) (col : E → Z) (y : Z) (p : V → Prop) [DecidablePred p] :
    ∑ v, (if p v then load src col y v else 0) = Fintype.card {e // p (src e) ∧ col e = y} := by
  rw [← sum_filter]
  have h := sum_card_fiberwise_eq_card_filter (univ.filter (fun e => col e = y))
    (univ.filter p) src
  simp only [load, Fintype.card_subtype, ← Nat.cast_sum]
  congr 1
  simpa only [filter_filter, mem_filter, mem_univ, true_and, and_comm] using h

omit [Fintype Z] in
-- 读法：结论为 `∑ v, load src col y v = Fintype.card {e // col e = y}`。这里调用 `load_sum`。
private theorem load_total (src : E → V) (col : E → Z) (y : Z) :
    ∑ v, load src col y v = Fintype.card {e // col e = y} := by
  simpa using load_sum src col y (fun _ => True)

-- 读法：结论为 `∑ y, ∑ v, (load src col y v) ^ 2 ≤ (D : ℝ) * Fintype.card E`。这里调用 `sum_le_sum`。
private theorem load_sq (src : E → V) (col : E → Z) {D : ℕ}
    (hd : ∀ v, Fintype.card {e // src e = v} ≤ D) :
    ∑ y, ∑ v, (load src col y v) ^ 2 ≤ (D : ℝ) * Fintype.card E := by
  calc
    _ ≤ ∑ y, ∑ v, (D : ℝ) * load src col y v := by
      apply sum_le_sum
      intro y _
      apply sum_le_sum
      intro v _
      have h := (Fintype.card_subtype_mono (fun e => src e = v ∧ col e = y)
        (fun e => src e = v) (fun _ h => h.1)).trans (hd v)
      rw [pow_two, load]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← mul_sum, load_total, Fintype.card_subtype, ← Nat.cast_sum]
      rw [sum_card_fiberwise_eq_card_filter]
      simp

-- 读法：`x * k ^ 2` 不超过 `y * k + m`。
private theorem scaled {x y d k m : ℝ} (hm : 0 ≤ m) (hk : 0 < k)
    (h : (x - y / k) ^ 2 ≤ (d + 1) * m) (hsize : (d + 1) * k ^ 4 ≤ m) :
    x * k ^ 2 ≤ y * k + m := by
  have hsq : (x * k ^ 2 - y * k) ^ 2 ≤ m ^ 2 := calc
    _ = (x - y / k) ^ 2 * k ^ 4 := by field_simp
    _ ≤ (d + 1) * m * k ^ 4 := mul_le_mul_of_nonneg_right h (by positivity)
    _ = ((d + 1) * k ^ 4) * m := by ring
    _ ≤ m ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hsize hm
  linarith only [le_of_sq_le_sq hsq hm]

-- 读法：结论为 `∃ f : V → Z, (∀ z, Fintype.card {v // f v = z} * Fintype.card Z ≤ 2 * M) ∧ (∀ z y, Fintype.card {e // f (src e) = z ∧ col e = y} * (Fintype.card Z) ^ 2 ≤ 2 * M)`。
/-- 对自由端点着色，同时控制各颜色的顶点数，以及各有序颜色对的边数。

英文原文：Color the free endpoints, controlling both the number of vertices
in each color and the number of edges of each ordered color pair.
-/
theorem bipartite [Nonempty Z] (src : E → V) (col : E → Z) {M D : ℕ}
    (hv : Fintype.card V ≤ M) (he : Fintype.card E ≤ M)
    (hd : ∀ v, Fintype.card {e // src e = v} ≤ D)
    (hc : ∀ y, Fintype.card {e // col e = y} * Fintype.card Z ≤ M)
    (hsize : (D + 1) * (Fintype.card Z) ^ 4 ≤ M) :
    ∃ f : V → Z,
      (∀ z, Fintype.card {v // f v = z} * Fintype.card Z ≤ 2 * M) ∧
      (∀ z y, Fintype.card {e // f (src e) = z ∧ col e = y} * (Fintype.card Z) ^ 2 ≤ 2 * M) := by
  let w : Option Z → V → ℝ
    | none, _ => 1
    | some y, v => load src col y v
  -- 推导：记下中间结论 `hsq`：`∑ i, ∑ v, (w i v) ^ 2 ≤ ((D : ℝ) + 1) * M`。
  have hsq : ∑ i, ∑ v, (w i v) ^ 2 ≤ ((D : ℝ) + 1) * M := by
    rw [Fintype.sum_option]
    simp only [w, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one]
    calc
      _ ≤ (Fintype.card V : ℝ) + D * Fintype.card E := add_le_add_right (load_sq src col hd) _
      _ ≤ (M : ℝ) + D * M := by gcongr
      _ = _ := by ring
  obtain ⟨f, hf⟩ := color (Z := Z) w
  have hk : 0 < Fintype.card Z := Fintype.card_pos
  have h (i : Option Z) (z : Z) :
      (∑ v, if f v = z then w i v else 0) * (Fintype.card Z : ℝ) ^ 2 ≤
        (∑ v, w i v) * Fintype.card Z + M :=
    scaled (by positivity) (by exact_mod_cast hk) ((hf i z).trans hsq) (by exact_mod_cast hsize)
  refine ⟨f, ?_, ?_⟩
  · intro z
    have hh := h none z
    simp only [w, sum_boole, sum_const, card_univ, nsmul_eq_mul, mul_one,
      ← Fintype.card_subtype] at hh
    have hh' : Fintype.card {v // f v = z} * (Fintype.card Z) ^ 2 ≤
        Fintype.card V * Fintype.card Z + M := by exact_mod_cast hh
    apply Nat.le_of_mul_le_mul_right _ hk
    rw [mul_assoc, ← pow_two]
    exact hh'.trans (by nlinarith)
  · intro z y
    have hh := h (some y) z
    simp only [w, load_sum, load_total] at hh
    have hh' : Fintype.card {e // f (src e) = z ∧ col e = y} * (Fintype.card Z) ^ 2 ≤
        Fintype.card {e // col e = y} * Fintype.card Z + M := by exact_mod_cast hh
    have := hc y
    omega

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 将连线分配到有限多个标签上

**英文原文**

Distributing wires among finitely many labels
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z] [DecidableEq Z]

-- 读法：`multiplicity` 的取值由 `Fintype.card {a // f a = z}` 给出。
/-- 统计携带指定标签的位点数。

英文原文：Count sites carrying the specified label.
-/
def multiplicity (f : A → Z) (z : Z) := Fintype.card {a // f a = z}

omit [Fintype Z] in
-- 读法：`multiplicity f z` 等于 `multiplicity (f ∘ Sum.inl) z + multiplicity (f ∘ Sum.inr) z`。
theorem multiplicity_sum (f : A ⊕ B → Z) (z : Z) :
    multiplicity f z = multiplicity (f ∘ Sum.inl) z + multiplicity (f ∘ Sum.inr) z := by
  unfold multiplicity
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  rfl

omit [Fintype Z] in
-- 读法：`multiplicity (Sum.elim f g) z` 等于 `multiplicity f z + multiplicity g z`。使用 `multiplicity_sum` 给出的结论。
theorem multiplicity_elim (f : A → Z) (g : B → Z) (z : Z) :
    multiplicity (Sum.elim f g) z = multiplicity f z + multiplicity g z :=
  multiplicity_sum _ z

-- 读法：存在 `f : A → Z`，对每个 `z`，`multiplicity f z * Fintype.card Z` 不超过 `Fintype.card A + Fintype.card Z`。
theorem even_labels [Nonempty Z] :
    ∃ f : A → Z, ∀ z, multiplicity f z * Fintype.card Z ≤ Fintype.card A + Fintype.card Z := by
  let r := Fintype.card Z
  let n := Fintype.card A
  let m := n / r + 1
  have h : n ≤ r * m ∧ r * m ≤ n + r := by
    have : n % r < r := Nat.mod_lt n (Fintype.card_pos (α := Z))
    have := Nat.mod_add_div n r
    simp only [m, Nat.mul_add, mul_one]
    omega
  obtain ⟨e⟩ : Nonempty (A ↪ Z × Fin m) := Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_prod, Fintype.card_fin]; exact h.1)
  refine ⟨fun x => (e x).1, fun z => ?_⟩
  have hinj : Function.Injective (fun x : {x // (e x).1 = z} => (e x.val).2) :=
    fun x y he => Subtype.ext (e.injective (Prod.ext (x.2.trans y.2.symm) he))
  have hm := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at hm
  exact (Nat.mul_le_mul_right r hm).trans (by rw [mul_comm]; exact h.2)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 将有向连线打包进二进立方体

以每个有序标签对为一个模板，允许各个坐标的值重合。给每个角标号时，在每个坐标上从两个符号中择一。固定一个角，从模板到一对对角标签的映射是对合。因此，各项需求出现次数相同，即使某些角的标签重合也如此。

**英文原文**

Packing directed wires into binary cubes

Use every ordered pair of labels as a template, allowing coincidences
in individual coordinates. The corners are labelled by choosing one
symbol or the other in each coordinate. For a fixed corner, the
map from templates to opposite pairs of labels is an involution.
Consequently every demand occurs equally often, even if some of the
corner labels coincide.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {n r d h : ℕ}

-- 读法：在后续公式中，`Label` 是 `Fin n → Fin r` 的缩写。
abbrev Label (n r : ℕ) := Fin n → Fin r
-- 读法：在后续公式中，`Template` 是 `Label n r × Label n r` 的缩写。
abbrev Template (n r : ℕ) := Label n r × Label n r
-- 读法：在后续公式中，`Packet` 是 `Template n r × Fin d` 的缩写。
abbrev Packet (n r d : ℕ) := Template n r × Fin d
-- 读法：在后续公式中，`Position` 是 `Packet n r d × Cube n × Fin h` 的缩写。
abbrev Position (n r d h : ℕ) := Packet n r d × Cube n × Fin h

-- 读法：当 `x i` 成立时取 `p.2 i`，否则取 `p.1 i`。
def corner (p : Template n r) (x : Cube n) : Label n r :=
  fun i => if x i then p.2 i else p.1 i

-- 读法：`opposite` 的取值由 `(corner p x, corner p (Cube.flip Finset.univ x))` 给出。
def opposite (x : Cube n) (p : Template n r) : Template n r :=
  (corner p x, corner p (Cube.flip Finset.univ x))

-- 读法：`opposite x (opposite x p)` 等于 `p`。按 `Prod.ext` 的外延性准则比较各分量。
theorem opposite_opposite (x : Cube n) (p : Template n r) :
    opposite x (opposite x p) = p := by
  apply Prod.ext <;> funext i <;> cases hx : x i <;> simp [opposite, corner, Cube.flip, hx]

-- 读法：`corner p (Cube.flip {j} x) i` 等于 `corner p x i`。
theorem corner_flip (p : Template n r) (x : Cube n) {i j : Fin n} (hij : i ≠ j) :
    corner p (Cube.flip {j} x) i = corner p x i := by
  simp [corner, Cube.flip, hij]

-- 读法：`endpoints` 的取值由 `opposite s.2.1 s.1.1` 给出。
/-- 数据包内某条给定连线所服务的有序对。

英文原文：The ordered pair served by a particular wire in a packet.
-/
def endpoints (s : Position n r d h) : Template n r :=
  opposite s.2.1 s.1.1

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Template n r × (Fin d × Cube n × Fin h) ≃ Position n r d h`。
def positions (n r d h : ℕ) :
    Template n r × (Fin d × Cube n × Fin h) ≃ Position n r d h where
  toFun s := ((opposite s.2.2.1 s.1, s.2.1), s.2.2)
  invFun s := (endpoints s, s.1.2, s.2)
  left_inv _ := by simp [endpoints, opposite_opposite]
  right_inv _ := by simp [endpoints, opposite_opposite]

-- 读法：`endpoints (positions n r d h s)` 等于 `s.1`。使用 `opposite_opposite` 给出的结论。
theorem endpoints_positions (s : Template n r × (Fin d × Cube n × Fin h)) :
    endpoints (positions n r d h s) = s.1 :=
  opposite_opposite _ _

-- 读法：存在 `g : E ↪ Z × Y`，对每个 `e`，`(g e).1` 等于 `f e`。
private theorem place {E Z Y : Type} [Fintype E] [Fintype Y] [DecidableEq Z]
    (f : E → Z) (hf : ∀ z, multiplicity f z ≤ Fintype.card Y) :
    ∃ g : E ↪ Z × Y, ∀ e, (g e).1 = f e := by
  let a (z : Z) : {e // f e = z} ↪ Y :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hf z))
  let g : (Σ z, {e // f e = z}) → Z × Y := fun p => (p.1, a p.1 p.2)
  have hi : Function.Injective g := by
    rintro ⟨z, e⟩ ⟨y, k⟩ he
    have : z = y := congrArg Prod.fst he
    subst y
    have : e = k := (a z).injective (congrArg Prod.snd he)
    rw [this]
  exact ⟨(Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans ⟨g, hi⟩, fun _ => rfl⟩

-- 读法：`rounds` 的取值由 `M / (Fintype.card (Label n r) ^ 2 * Fintype.card (Cube n) * h) + 1` 给出。
/-- 在布置任何图式之前，根据容量确定重复次数。

英文原文：Repetition count fixed from the capacity before laying out any diagram.
-/
def rounds (n r h M : ℕ) :=
  M / (Fintype.card (Label n r) ^ 2 * Fintype.card (Cube n) * h) + 1

-- 读法：结论为 `let d := rounds n r h M Fintype.card (Position n r d h) ≤ M + Fintype.card (Label n r) ^ 2 * Fintype.card (Cube n) * h ∧ ∃ g : E ↪ Position n r d h, ∀ e, endpoints (g e) = f e`。
/-- 统一配置的立方体数据包已经足够。对每一有序标签对，取整误差至多多耗费一个完整数据包。

英文原文：A uniform supply of cube packets suffices. The rounding error
costs at most one full packet for every ordered pair of labels.
-/
theorem pack {E : Type} [Fintype E] {M : ℕ} (f : E → Template n r) (hr : 0 < r) (hh : 0 < h)
    (hb : ∀ p, multiplicity f p * Fintype.card (Label n r) ^ 2 ≤ M) :
    let d := rounds n r h M
    Fintype.card (Position n r d h) ≤
        M + Fintype.card (Label n r) ^ 2 * Fintype.card (Cube n) * h ∧
      ∃ g : E ↪ Position n r d h, ∀ e, endpoints (g e) = f e := by
  let z := Fintype.card (Label n r)
  let B := z ^ 2 * Fintype.card (Cube n) * h
  let d := M / B + 1
  have hz : 0 < z := by simpa [z, Label] using pow_pos hr n
  -- 推导：记下中间结论 `hB`：`0 < B`。
  have hB : 0 < B := mul_pos (mul_pos (pow_pos hz 2) Fintype.card_pos) hh
  have hsize : M ≤ d * B ∧ d * B ≤ M + B := by
    have := Nat.mod_lt M hB
    have := Nat.mod_add_div M B
    rw [mul_comm d, show d = M / B + 1 from rfl, mul_add, mul_one]
    omega
  have hc : Fintype.card (Position n r d h) = d * B := by
    simp only [Position, Packet, Template, Fintype.card_prod, Fintype.card_fin, B, z]
    ring
  refine ⟨hc.le.trans hsize.2, ?_⟩
  obtain ⟨g, hg⟩ := place (Y := Fin d × Cube n × Fin h) f (fun p => by
    apply (Nat.mul_le_mul_right_iff (pow_pos hz 2)).1
    calc
      _ ≤ M := hb p
      _ ≤ d * B := hsize.1
      _ = _ := by simp only [Fintype.card_prod, Fintype.card_fin, B]; ring)
  refine ⟨g.trans (positions n r d h).toEmbedding, fun e => ?_⟩
  exact (endpoints_positions (g e)).trans (hg e)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 为细分后的批次分配标签

外部槽位的标签可以预先规定。先放置剩余接点，再同时平衡站点处的所有关联计数。这样无须假定重复边或自环之间相互独立。

**英文原文**

Assigning labels to a subdivided batch

Exterior slots may have prescribed labels. Place the remaining junctions
first, then simultaneously balance all incidence counts at the stations.
This avoids any independence assumption about repeated edges or loops.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {F : Type} {a b : Wire} (G : Diagram F a b) {Z : Type}
  [Fintype Z] [DecidableEq Z] [Nonempty Z] (fa : slots a → Z) (fb : slots b → Z)

omit [Fintype Z] [Nonempty Z] in
-- 读法：`multiplicity ((Sum.elim fa (Sum.elim fb fe)) ∘ G.junction) z` 等于 `multiplicity fa z + multiplicity fb z + 2 * multiplicity fe z`。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem count_ends (fe : G.E → Z) (z : Z) :
    multiplicity ((Sum.elim fa (Sum.elim fb fe)) ∘ G.junction) z =
      multiplicity fa z + multiplicity fb z + 2 * multiplicity fe z := by
  have he : (Sum.elim fa (Sum.elim fb fe)) ∘ G.junction =
      Sum.elim (Sum.elim fa fe) (Sum.elim fb fe) := by
    funext x
    rcases x with (i|e)|(j|e) <;> rfl
  rw [he, multiplicity_elim, multiplicity_elim, multiplicity_elim]
  omega

-- 读法：证明中先建立 `h`，即 `multiplicity f z * Fintype.card Z ≤ 2 * (6 * M)`。
/-- 将每条细分边定向为从接合点指向其原站点。对每一有序标签对，边的重数有界。

英文原文：Orient each subdivided edge from its junction to its original station.
Every ordered pair of labels has bounded edge multiplicity.
-/
theorem label_diagram [Field F] {M D : ℕ} (hm : G.cost ≤ M)
    (hd : ∀ v, G.arity v ≤ D) (hz : Fintype.card Z ≤ M)
    (ha : ∀ z, multiplicity fa z * Fintype.card Z ≤ M)
    (hb : ∀ z, multiplicity fb z * Fintype.card Z ≤ M)
    (hsize : (D + 1) * Fintype.card Z ^ 4 ≤ M) :
    ∃ f : G.normalized.V → Z,
      (∀ i, f (.inr (.inl i)) = fa i) ∧
      (∀ j, f (.inr (.inr (.inl j))) = fb j) ∧
      (∀ z, multiplicity f z * Fintype.card Z ≤ 16 * M) ∧
      (∀ z y, Fintype.card {e : G.End //
        f (.inl (G.station e)) = z ∧ f (.inr (G.junction e)) = y} *
        Fintype.card Z ^ 2 ≤ 12 * M) := by
  classical
  rw [Diagram.cost_eq] at hm
  -- 推导：从 `even_labels (A := G.E) (Z := Z)` 中取出 `fe, hfe`。
  obtain ⟨fe, hfe⟩ := even_labels (A := G.E) (Z := Z)
  let g : G.Joint → Z := Sum.elim fa (Sum.elim fb fe)
  have hg (z : Z) : multiplicity g z * Fintype.card Z ≤ 4 * M := by
    unfold g
    rw [multiplicity_elim, multiplicity_elim, add_mul, add_mul]
    have := ha z
    have := hb z
    have := hfe z
    omega
  have hge (z : Z) : multiplicity (g ∘ G.junction) z * Fintype.card Z ≤ 6 * M := by
    unfold g
    rw [count_ends, add_mul, add_mul, mul_assoc]
    have := ha z
    have := hb z
    have := hfe z
    omega
  -- 推导：从 `bipartite G.station (g ∘ G.junction) (M := 6 * M) (D := D)` 中取出 `f, hf, hp`。
  obtain ⟨f, hf, hp⟩ := bipartite G.station (g ∘ G.junction) (M := 6 * M) (D := D)
    (by omega) (by rw [Diagram.card_end]; omega) (fun v => (G.degree v).le.trans (hd v))
    hge (by omega)
  refine ⟨Sum.elim f g, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro z
    rw [multiplicity_elim, add_mul]
    have h : multiplicity f z * Fintype.card Z ≤ 2 * (6 * M) := hf z
    have := hg z
    omega
  · intro z y
    exact (hp z y).trans (by omega)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 为最大元数较小的每个网络构造有界立方体布局

**英文原文**

A bounded cube layout for every network of small maximum arity
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b) {n r h : ℕ}

-- 读法：结构的字段包括 `d`、`color`、`assign`、`follows`。
/-- 规范化图式的每条连线占据单独的有向位置。方向约定与局部表无关。

英文原文：Each wire of the normalized diagram occupies its own directed
position. The orientation convention is independent of the local tables.
-/
structure Layout (n r h : ℕ) where
  d : ℕ
  color : G.normalized.V → Label n r
  assign : G.End ↪ Position n r d h
  follows : ∀ e, endpoints (assign e) = (color (.inl (G.station e)), color (.inr (G.junction e)))

-- 读法：这里调用 `Nat.le_pow`。
theorem layout {M D : ℕ} (fa : slots a → Label n r) (fb : slots b → Label n r)
    (hm : G.cost ≤ M) (hd : ∀ v, G.arity v ≤ D) (hr : 0 < r) (hh : 0 < h)
    (ha : ∀ z, multiplicity fa z * r ^ n ≤ M) (hb : ∀ z, multiplicity fb z * r ^ n ≤ M)
    (hsize : (D + 1) * (r ^ n) ^ 4 ≤ M) (hpad : (r ^ n) ^ 2 * 2 ^ n * h ≤ M) :
    ∃ L : Layout G n r h, L.d = rounds n r h (12 * M) ∧ Fintype.card (Position n r L.d h) ≤ 13 * M ∧
      (∀ i, L.color (.inr (.inl i)) = fa i) ∧
      (∀ j, L.color (.inr (.inr (.inl j))) = fb j) ∧
      (∀ z, multiplicity L.color z * r ^ n ≤ 16 * M) := by
  let _ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hz : Fintype.card (Label n r) = r ^ n := by simp [Label]
  -- 推导：记下中间结论 `hc`：`Fintype.card (Cube n) = 2 ^ n`。
  have hc : Fintype.card (Cube n) = 2 ^ n := by simp [Cube]
  have hN : Fintype.card (Label n r) ≤ M := by
    rw [hz]
    exact (Nat.le_pow (by decide : 0 < 4)).trans
      ((Nat.le_mul_of_pos_left _ (Nat.succ_pos D)).trans hsize)
  obtain ⟨f, hfa, hfb, hf, hg⟩ := label_diagram G fa fb hm hd hN
    (by rwa [hz]) (by rwa [hz]) (by rwa [hz])
  let g : G.End → Template n r := fun e => (f (.inl (G.station e)), f (.inr (G.junction e)))
  obtain ⟨hcost, v, hv⟩ := pack (M := 12 * M) g hr hh (by
    rintro ⟨x, y⟩
    simpa [multiplicity, g, Fintype.card_subtype] using hg x y)
  refine ⟨⟨_, f, v, hv⟩, rfl, ?_, hfa, hfb, ?_⟩
  · rw [hz, hc] at hcost
    exact hcost.trans (by omega)
  · rwa [hz] at hf

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 沿各个立方体坐标切割的精确连线恒等式

**英文原文**

Exact wire identities with a cut along every cube coordinate
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

-- 读法：在后续公式中，`Block` 是 `Spectral.Cube n × Fin h → Bool` 的缩写。
abbrev Block (n h : ℕ) := Spectral.Cube n × Fin h → Bool

-- 读法：结构的字段包括 `I`、`weight`、`cross`、`side`、`full`。
/-- 每个角点向其对角点发送一个字，两个字都以各自的发送角点为索引。对任一切分，发送位置与接收位置均分处两侧。

英文原文：Each corner sends a word to the opposite corner. Index both words
by the sending corner. At any cut the sending and receiving positions
belong to opposite sides.
-/
structure Expansion (F : Type) [Field F] (n h : ℕ) where
  I : Type
  [fi : Fintype I]
  weight : I → Block n h → Block n h → F
  cross : I → Fin n → ℕ
  side : (s : I) → (i : Fin n) → Bool → Block n h → Block n h → (Fin (cross s i) → Bool) → F
  full : ∀ x y, (∑ s, weight s x y) = if x = y then 1 else 0
  split : ∀ s i x y, weight s x y = ∑ z, side s i false x y z * side s i true x y z
  depends : ∀ s i b x x' y y' z, (∀ p, p.1 i = b → x p = x' p) →
    (∀ p, p.1 i ≠ b → y p = y' p) → side s i b x y z = side s i b x' y' z

attribute [instance] Expansion.fi

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 按数据包展开精确收缩

在两侧都将未占用位置固定为零。若对这些位置自由求和，在正特征下就可能改变标量值。

**英文原文**

Expanding an exact contraction by packets

Unoccupied positions are pinned to zero on both sides. Summing freely
over them instead could change the scalar in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b} {n r h : ℕ}

namespace Layout

variable (L : Layout G n r h)

-- 读法：输入 `i` 时返回 `Function.extend L.assign x (fun _ => false) (p, i)`。
def load (x : G.End → Bool) (p : Packet n r L.d) : Block n h :=
  fun i => Function.extend L.assign x (fun _ => false) (p, i)

-- 读法：`L.load x (L.assign e).1 (L.assign e).2` 等于 `x e`。使用 `L.assign.injective.extend_apply` 给出的结论。
theorem load_assign (x : G.End → Bool) (e : G.End) :
    L.load x (L.assign e).1 (L.assign e).2 = x e :=
  L.assign.injective.extend_apply _ _ _

-- 读法：`L.load` 是单射。用函数外延性比较等号两侧在 `e` 处的取值。
theorem load_injective : Function.Injective L.load := by
  intro x y he
  funext e
  rw [← L.load_assign x e, ← L.load_assign y e, he]

-- 读法：`L.load x p i` 等于 `L.load y p i`。按 `∃ e, L.assign e = (p, i)` 成立与否分情况。
theorem load_local (x y : G.End → Bool) (p : Packet n r L.d) (i : Cube n × Fin h)
    (he : ∀ e, L.assign e = (p, i) → x e = y e) : L.load x p i = L.load y p i := by
  by_cases ho : ∃ e, L.assign e = (p, i)
  · obtain ⟨e, h⟩ := ho
    simpa [load, ← h, L.assign.injective.extend_apply] using he e h
  · simp [load, Function.extend_apply' _ _ _ ho]

end Layout

-- 读法：`(∑ s : P → A.I, ∏ p, A.weight (s p) (x p) (y p))` 等于 `if x = y then 1 else 0`。按 `x = y` 成立与否分情况。
theorem Expansion.full_product {P : Type} [Fintype P] [DecidableEq P]
    (A : Expansion F n h) (x y : P → Block n h) :
    (∑ s : P → A.I, ∏ p, A.weight (s p) (x p) (y p)) = if x = y then 1 else 0 := by
  rw [← Fintype.prod_sum (fun p j => A.weight j (x p) (y p))]
  simp_rw [A.full]
  by_cases he : x = y
  · simp [he]
  · rw [ite_eq_right he]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

open Classical in
-- 读法：这里调用 `Finset.sum_congr`。
/-- 该网络在每条边的两侧使用独立的槽位比特。对所有数据包选择器完整求和后，各连线的相等约束全部恢复。

英文原文：A network with independent slot bits on the two sides of every edge.
The full sum over packet selectors restores all the wire equalities.
-/
theorem Layout.eval (L : Layout G n r h) (A : Expansion F n h) (x : Val a) (y : Val b) :
    G.eval x y =
      ∑ u : G.End → Bool, ∑ v : G.End → Bool,
        (∏ i : G.V, G.normalized.vertex x y u (.inl i)) *
        (∏ i : G.Joint, G.normalized.vertex x y v (.inr i)) *
        ∑ s : Packet n r L.d → A.I, ∏ p, A.weight (s p) (L.load u p) (L.load v p) := by
  simp only [A.full_product, L.load_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← G.eval_normalized]
  unfold Diagram.eval
  apply Finset.sum_congr
  · ext; simp
  · exact fun _ _ => Fintype.prod_sum_type _

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 坐标切割的局部性与成本

**英文原文**

Locality and cost of a coordinate cut
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b} {n r h : ℕ}

-- 读法：当 `s` 成立时取 `p.2 i`，否则取 `p.1 i`。
/-- 在一个给定坐标处，每个模板至多接触两个组。

英文原文：A template meets at most two groups at a fixed coordinate.
-/
def group (p : Template n r) (i : Fin n) (s : Bool) : Fin r :=
  if s then p.2 i else p.1 i

-- 读法：结论为 `let p := L.assign e L.color (.inl (G.station e)) i = group p.1.1 i (p.2.1 i) ∧ L.color (.inr (G.junction e)) i = group p.1.1 i (!(p.2.1 i))`。
theorem Layout.end_groups (L : Layout G n r h) (e : G.End) (i : Fin n) :
    let p := L.assign e
    L.color (.inl (G.station e)) i = group p.1.1 i (p.2.1 i) ∧
    L.color (.inr (G.junction e)) i = group p.1.1 i (!(p.2.1 i)) := by
  have h := L.follows e
  exact ⟨(congrArg (fun x => x.1 i) h).symm, by
    simpa [endpoints, opposite, corner, group, Cube.flip] using
      (congrArg (fun x => x.2 i) h).symm⟩

-- 读法：`A.side s i b (L.load u p) (L.load v p) z` 等于 `A.side s i b (L.load u' p) (L.load v' p) z`。这里调用 `A.depends`。
/-- 一侧的表无须使用其他组的槽位比特。

英文原文：A side table needs no slot bits from other groups.
-/
theorem Layout.side_local (L : Layout G n r h) (A : Expansion F n h)
    (p : Packet n r L.d) (s : A.I) (i : Fin n) (b : Bool)
    (u u' v v' : G.End → Bool) (z : Fin (A.cross s i) → Bool)
    (hu : ∀ e, L.color (.inl (G.station e)) i = group p.1 i b → u e = u' e)
    (hv : ∀ e, L.color (.inr (G.junction e)) i = group p.1 i b → v e = v' e) :
    A.side s i b (L.load u p) (L.load v p) z = A.side s i b (L.load u' p) (L.load v' p) z := by
  apply A.depends
  · intro q hq
    apply L.load_local
    intro e he
    apply hu
    rw [(L.end_groups e i).1, he, hq]
  · intro q hq
    apply L.load_local
    intro e he
    apply hv
    have heq : (!(q.1 i)) = b := by cases ha : q.1 i <;> cases b <;> simp_all
    rw [(L.end_groups e i).2, he, heq]

variable {P : Type} [Fintype P]

-- 读法：结论为 `∃ i : Fin n, (∀ j, ∑ p, A.cross (s p) i ≤ ∑ p, A.cross (s p) j) ∧ L * (∑ p, (A.cross (s p) i + Nat.clog 2 (Fintype.card A.I))) ≤ 2 * Fintype.card P * Fintype.card (Cube n) * h`。
/-- 切割方式可以依赖整个选择器元组。成本上界对所有这类元组一致成立。

英文原文：The cut may depend on the complete selector tuple. The cost is
bounded uniformly over all such tuples.
-/
theorem Expansion.coordinate (A : Expansion F n h) (hn : 0 < n) (L : ℕ)
    (hc : ∀ s, L * ∑ i, A.cross s i ≤ n * Fintype.card (Cube n) * h)
    (hl : L * Nat.clog 2 (Fintype.card A.I) ≤ h) (s : P → A.I) :
    ∃ i : Fin n, (∀ j, ∑ p, A.cross (s p) i ≤ ∑ p, A.cross (s p) j) ∧
      L * (∑ p, (A.cross (s p) i + Nat.clog 2 (Fintype.card A.I))) ≤
        2 * Fintype.card P * Fintype.card (Cube n) * h := by
  let c (i : Fin n) := ∑ p, A.cross (s p) i
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ c ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsum : n * (L * c i) ≤ n * (Fintype.card P * Fintype.card (Cube n) * h) := by
    calc
      _ = ∑ _ : Fin n, L * c i := by simp
      _ ≤ ∑ j : Fin n, L * c j :=
        Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (hi j hj))
      _ = ∑ p, L * ∑ j, A.cross (s p) j := by
        simp only [c, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _p : P, n * Fintype.card (Cube n) * h := Finset.sum_le_sum (fun p _ => hc (s p))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
  have hcross := (Nat.mul_le_mul_left_iff hn).1 hsum
  refine ⟨i, fun j => hi j (Finset.mem_univ j), ?_⟩
  have hbits := Nat.mul_le_mul_left (Fintype.card P)
    (hl.trans (Nat.le_mul_of_pos_left h (Fintype.card_pos (α := Cube n))))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_add]
  exact (Nat.add_le_add hcross (by simpa only [mul_left_comm, mul_assoc] using hbits)).trans_eq
    (by ring)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 确定选择器后选取要切割的数据包

**英文原文**

Choosing which packets to cut after their selectors are known
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

variable {F : Type} [Field F] {n h : ℕ} (A : Expansion F n h)

-- 读法：当 `b` 成立时取 `A.cross s i`，否则取 `0`。
def width (s : A.I) (i : Fin n) (b : Bool) : ℕ :=
  if b then A.cross s i else 0

-- 读法：逐一匹配以下输入模式：`false, _`、`true, z`。
def value (s : A.I) (i : Fin n) (x y : Block n h) :
    (b : Bool) → (Fin (A.width s i b) → Bool) → F
  | false, _ => A.weight s x y
  | true, z => A.side s i false x y z * A.side s i true x y z

-- 读法：结论为 `∑ z, A.value s i x y b z = A.weight s x y`。对 `b` 分类讨论。
/-- 未切割的数据包只有一种对零个比特的赋值，因此不会在域中引入额外重数。

英文原文：An uncut packet has exactly one assignment of zero bits, avoiding
an extra multiplicity in the field.
-/
theorem sum_value (s : A.I) (i : Fin n) (x y : Block n h) (b : Bool) :
    ∑ z, A.value s i x y b z = A.weight s x y := by
  cases b
  · change (∑ _z : Fin 0 → Bool, A.weight s x y) = _
    simp
  · exact (A.split s i x y).symm

variable {P : Type}

-- 读法：在后续公式中，`Wires` 是 `(p : P) → Fin (A.width (s p) i (b p)) → Bool` 的缩写。
abbrev Wires (s : P → A.I) (i : Fin n) (b : P → Bool) :=
  (p : P) → Fin (A.width (s p) i (b p)) → Bool

variable [Fintype P] [DecidableEq P]

-- 读法：`(∑ z : A.Wires s i b, ∏ p, A.value (s p) i (x p) (y p) (b p) (z p))` 等于 `∏ p, A.weight (s p) (x p) (y p)`。
theorem sum_wires (x y : P → Block n h) (s : P → A.I) (i : Fin n) (b : P → Bool) :
    (∑ z : A.Wires s i b, ∏ p, A.value (s p) i (x p) (y p) (b p) (z p)) =
      ∏ p, A.weight (s p) (x p) (y p) := by
  rw [← Fintype.prod_sum (fun p z => A.value (s p) i (x p) (y p) (b p) z)]
  simp only [sum_value]

-- 读法：结论为 `(∑ s, ∑ z : A.Wires s (cut s) (split s), ∏ p, A.value (s p) (cut s) (x p) (y p) (split s p) (z p)) = if x = y then 1 else 0`。
/-- 切割所沿的坐标和待拆分的数据包子集均可依赖整个选择器元组。

英文原文：Both the coordinate and the subset of packets to split may depend
on the entire selector tuple.
-/
theorem adaptive (x y : P → Block n h) (cut : (P → A.I) → Fin n)
    (split : (P → A.I) → P → Bool) :
    (∑ s, ∑ z : A.Wires s (cut s) (split s),
      ∏ p, A.value (s p) (cut s) (x p) (y p) (split s p) (z p)) =
      if x = y then 1 else 0 := by
  simp only [sum_wires, A.full_product]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end
