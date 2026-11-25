-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.TensorSpectrum.SeparationWeights
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum.Separation

/-!
# 通过局部傅里叶映射作带代价的有限分离

源张量恰为共享第一条腿的张量的 `6 * M` 个完整副本。目标是各分区张量的完整直和，每个分区张量都乘以第二、第三条腿上的一个长度为 `M` 的配对。局部变量的权重可以为负；经过傅里叶投影后，各保留项的总权重均为非负平方，因此所得系数数组为多项式。

**英文原文**

Charged finite separation by local Fourier maps

The source is exactly `6 * M` full copies of the shared-first-leg tensor.
The target is the full direct sum of the sector tensors, each multiplied by
a length-`M` pairing on the second and third legs.  Local variables may have
negative weights; after Fourier projection every surviving total weight is
a nonnegative square, so the resulting coefficient array is polynomial.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation

variable {X Y Z : Type*}

-- 读法：当 `y.1 = z.1` 成立时取 `A y.1 x y.2 z.2`，否则取 `0`。
/-- 分支标签只出现在输入张量的后两条腿上。

英文原文：The branch labels occur only on the last two legs of the input.
-/
def shared {M : ℕ} (A : Fin M → Tensor O X Y Z) :
    Tensor O X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then A y.1 x y.2 z.2 else 0

-- 读法：当 `u = v` 成立时取 `1`，否则取 `0`。
/-- 辅助配对在第一条腿上有一个坐标。

英文原文：The auxiliary pairing has one coordinate on the first leg.
-/
def dotPairingX (U : Type*) [DecidableEq U] : Tensor O Unit U U :=
  fun _ u v => if u = v then 1 else 0

-- 读法：`separated` 的取值由 `Tensor.directSum (fun h => Tensor.product (A h) (dotPairingX (Fin M)))` 给出。
/-- 输出中的每个分支都有自己的第一腿空间。

英文原文：Every branch in this output has its own first-leg space.
-/
def separated {M : ℕ} (A : Fin M → Tensor O X Y Z) :
    Tensor O (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  Tensor.directSum (fun h => Tensor.product (A h) (dotPairingX (Fin M)))

-- 读法：`phase` 的取值由 `(u : ℤ) - (v : ℤ) + 2 * ((g : ℤ) - (h : ℤ))` 给出。
/-- 有限傅里叶平均所投影的整数。此处标签从零开始编号，同时将四个标签加一保持该相位不变。

英文原文：The integer projected by the finite Fourier average. Labels are numbered
from zero here; translating all four labels by one leaves this phase unchanged.
-/
def phase {M : ℕ} (h g u v : Fin M) : ℤ :=
  (u : ℤ) - (v : ℤ) + 2 * ((g : ℤ) - (h : ℤ))

-- 读法：当 `s.2 = f t` 成立时取 `a t s.1`，否则取 `0`。
/-- 复制指定的源坐标，并乘以一个只取决于目标坐标和源在直和中的副本编号的标量。

英文原文：Copy a specified source coordinate with a scalar depending only on the
target coordinate and the source's direct-sum copy number.
-/
def copyLocal {L : ℕ} {S T : Type*} [DecidableEq S]
    (f : T → S) (a : T → Fin L → O) : T → (Fin L × S) → O :=
  fun t s => if s.2 = f t then a t s.1 else 0

section CopyCalculation

variable {L : ℕ} {X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 傅里叶平均来自对完整源副本的求和。求和指标是源副本而非目标坐标标签，三条腿上的源副本索引必须一致。

英文原文：Summing the full source copies, rather than target coordinate labels, is
what produces the Fourier average. All three source copy indices must agree.
-/
theorem restrict_copies (T : Tensor O X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (a : X' → Fin L → O) (b : Y' → Fin L → O) (c : Z' → Fin L → O) :
    Tensor.restrict (copyLocal fx a) (copyLocal fy b) (copyLocal fz c)
      (Tensor.directSum (fun _ : Fin L => T)) =
      fun x y z => (∑ r, a x r * b y r * c z r) * T (fx x) (fy y) (fz z) := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, copyLocal, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, ← Finset.sum_mul]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 按比例缩放每个目标坐标，本身就是一个局部线性运算。

英文原文：Scaling each target coordinate is itself a local linear operation.
-/
theorem restrict_scaled (T : Tensor O X Y Z)
    (a : X' → X → O) (b : Y' → Y → O) (c : Z' → Z → O)
    (u : X' → O) (v : Y' → O) (w : Z' → O) :
    Tensor.restrict (fun x i => u x * a x i)
      (fun y j => v y * b y j) (fun z k => w z * c z k) T =
      fun x y z => u x * v y * w z * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end CopyCalculation

section Projection

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

-- 读法：`fourierX` 的取值由 `copyLocal (fun x => x.2.1) (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))))` 给出。
def fourierX (ζ : O) :
    (Fin M × (X × Unit)) → (Fin (6 * M) × X) → O :=
  copyLocal (fun x => x.2.1)
    (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))))

-- 读法：`fourierY` 的取值由 `copyLocal (fun y => (y.1, y.2.1)) (fun y r => ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))))` 给出。
def fourierY (ζ : O) :
    (Fin M × (Y × Fin M)) → (Fin (6 * M) × (Fin M × Y)) → O :=
  copyLocal (fun y => (y.1, y.2.1))
    (fun y r => ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))))

-- 读法：`fourierZ` 的取值由 `copyLocal (fun z => (z.1, z.2.1)) (fun z r => w r * ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))` 给出。
def fourierZ (ζ : O) (w : Fin (6 * M) → O) :
    (Fin M × (Z × Fin M)) → (Fin (6 * M) × (Fin M × Z)) → O :=
  copyLocal (fun z => (z.1, z.2.1))
    (fun z r => w r *
      ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))

-- 读法：当 `y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0` 成立时取 `A y.1 x.2.1 y.2.1 z.2.1`，否则取 `0`。
def projected (A : Fin M → Tensor O X Y Z) :
    Tensor O (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then A y.1 x.2.1 y.2.1 z.2.1 else 0

-- 读法：要证明的命题是 `Tensor.restrict (fourierX ζ) (fourierY ζ) (fourierZ ζ w) (Tensor.directSum (fun _ : Fin (6 * M) => shared A)) = projected A`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 各个独立的显式局部映射恰好给出投影后的张量。

英文原文：The actual independent local maps give exactly the projected tensor.
-/
theorem fourier_restrict (A : Fin M → Tensor O X Y Z)
    (ζ : O) (w : Fin (6 * M) → O) (hζ : IsUnit ζ)
    (haverage : ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
      (∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0) :
    Tensor.restrict (fourierX ζ) (fourierY ζ) (fourierZ ζ w)
      (Tensor.directSum (fun _ : Fin (6 * M) => shared A)) = projected A := by
  classical
  rw [fourierX, fourierY, fourierZ, restrict_copies]
  funext x y z
  by_cases hyz : y.1 = z.1
  · have hphase : (∑ r : Fin (6 * M),
        ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
          ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))) *
          (w r *
            ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))) =
        if phase y.1 x.1 y.2.2 z.2.2 = 0 then 1 else 0 := by
      calc
        _ = ∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * phase y.1 x.1 y.2.2 z.2.2) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← hyz]
          calc
            _ = w r *
                ((ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
                  ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ)))) *
                  ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (y.1 : ℤ)))) := by ring
            _ = _ := by
              rw [← upow_add hζ, ← upow_add hζ]
              congr 2
              dsimp [phase]
              ring
        _ = _ := by
          apply haverage <;> unfold phase <;> omega
    rw [hphase]
    simp [shared, projected, hyz, ite_mul]
  · simp [shared, projected, hyz]

end Projection

section Polynomial

variable {M : ℕ}

-- 读法：`squareDegree` 的取值由 `squareExponent g h` 给出。
/-- 投影后单项式的次数，已知该数非负。

英文原文：The degree of a projected monomial, already known to be nonnegative.
-/
def squareDegree (h g : Fin M) : ℕ :=
  squareExponent g h

-- 读法：`separationPolynomial` 的结果类型为 `Tensor (Polynomial O) (Fin M × (X × Unit)) (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M))`。
/-- 尽管实现非零参数处取值的个别局部权重可以为负，所得数组的每一项仍是多项式。

英文原文：This is a polynomial array even though the individual local weights used
to realize its nonzero evaluations can be negative.
-/
def separationPolynomial (A : Fin M → Tensor O X Y Z) :
    Tensor (Polynomial O) (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then Polynomial.monomial (squareDegree y.1 x.1) (A y.1 x.2.1 y.2.1 z.2.1)
    else 0

-- 读法：`squareDegree h g = 0` 与 `g = h` 等价。这里调用 `squareExponent_eq_zero_iff`。
theorem squareDegree_eq_zero_iff (h g : Fin M) : squareDegree h g = 0 ↔ g = h := by
  exact squareExponent_eq_zero_iff g h

-- 读法：`(fun x y z => (separationPolynomial A x y z).coeff 0)` 等于 `separated A`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 常数项是带辅助点积的完整直和。

英文原文：The zero coefficient is the full direct sum with an auxiliary dot product.
-/
theorem separationPolynomial_constant (A : Fin M → Tensor O X Y Z) :
    (fun x y z => (separationPolynomial A x y z).coeff 0) = separated A := by
  funext x y z
  by_cases hxy : x.1 = y.1
  · by_cases hyz : y.1 = z.1
    · by_cases huv : y.2.2 = z.2.2
      · simp [separationPolynomial, separated, Tensor.directSum, Tensor.product,
          dotPairingX, phase, squareDegree, squareExponent, hxy, hyz, huv]
      · have hp : phase y.1 x.1 y.2.2 z.2.2 ≠ 0 := by
          intro hp
          have heq : (y.2.2 : ℤ) = (z.2.2 : ℤ) := by
            simpa [phase, hxy, sub_eq_zero] using hp
          exact huv (Fin.ext (by exact_mod_cast heq))
        have hsupport : ¬(y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0) :=
          fun h => hp h.2
        simp only [separationPolynomial, ite_eq_right hsupport]
        simp [separated, Tensor.directSum, Tensor.product, dotPairingX, hxy, hyz, huv]
    · have hxz : x.1 ≠ z.1 := by simpa [hxy] using hyz
      simp [separationPolynomial, separated, Tensor.directSum, hyz, hxz]
  · have hdegree : squareDegree y.1 x.1 ≠ 0 := by
      exact fun h => hxy ((squareDegree_eq_zero_iff y.1 x.1).mp h)
    by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    · simp only [separationPolynomial, ite_eq_left hs]
      simp [separated, Tensor.directSum, hxy,
        Polynomial.coeff_monomial, hdegree]
    · simp [separationPolynomial, hs, separated, Tensor.directSum, hxy]

-- 读法：`(separationPolynomial A x y z).degree` 不超过 `((M - 1) ^ 2 : ℕ)`。这里调用 `Polynomial.degree_le_of_natDegree_le`。
theorem separationPolynomial_degree (A : Fin M → Tensor O X Y Z)
    (x : Fin M × (X × Unit)) (y : Fin M × (Y × Fin M))
    (z : Fin M × (Z × Fin M)) :
    (separationPolynomial A x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold separationPolynomial
  split_ifs
  · exact le_trans (Polynomial.natDegree_monomial_le _)
      (squareExponent_le x.1 y.1)
  · simp

-- 读法：`weightX` 的取值由 `(x.1 : ℤ) ^ 2` 给出。
def weightX (x : Fin M × (X × Unit)) : ℤ := (x.1 : ℤ) ^ 2

-- 读法：`weightY` 的取值由 `(y.1 : ℤ) * (y.2.2 : ℤ) - (y.1 : ℤ) ^ 2` 给出。
def weightY (y : Fin M × (Y × Fin M)) : ℤ :=
  (y.1 : ℤ) * (y.2.2 : ℤ) - (y.1 : ℤ) ^ 2

-- 读法：`weightZ` 的取值由 `-(z.1 : ℤ) * (z.2.2 : ℤ)` 给出。
def weightZ (z : Fin M × (Z × Fin M)) : ℤ :=
  -(z.1 : ℤ) * (z.2.2 : ℤ)

-- 读法：`(fun x y z => (separationPolynomial A x y z).eval t)` 等于 `fun x y z => t ^ weightX x * t ^ weightY y * t ^ weightZ z * projected A x y z`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 在整个投影支集上，局部权重之和等于实际多项式次数；这里也覆盖所有为零和不匹配的系数。

英文原文：On the complete projected support, the local weights add to the actual
polynomial degree, including all zero and mismatched coefficients.
-/
theorem separationPolynomial_eval (A : Fin M → Tensor O X Y Z)
    (t : O) (ht : IsUnit t) :
    (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => t ^ weightX x * t ^ weightY y * t ^ weightZ z * projected A x y z := by
  funext x y z
  by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
  · have hsum : weightX x + weightY y + weightZ z =
        ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 := by
      dsimp [weightX, weightY, weightZ]
      rw [← hs.1]
      have hp := hs.2
      dsimp [phase] at hp
      nlinarith
    -- 推导：记下中间结论 `hcast`：`(squareDegree y.1 x.1 : ℤ) = ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2`。
    have hcast : (squareDegree y.1 x.1 : ℤ) = ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 :=
      Int.toNat_of_nonneg (sq_nonneg _)
    simp only [separationPolynomial, projected, ite_eq_left hs, Polynomial.eval_monomial]
    rw [← upow_add ht, ← upow_add ht, hsum, ← hcast, upow_nat]
    ring
  · simp [separationPolynomial, projected, hs]

end Polynomial

section Realization

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`(fun x y z => (separationPolynomial A x y z).eval t)` 属于 `LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A))`。这里调用 `separationPolynomial_eval`。
/-- 每个非零参数处的特化均由三个显式局部线性映射给出，使用的源副本数恰好等于计入的数量。

英文原文：Every nonzero specialization comes from exactly the charged number of
source copies by three actual local linear maps.
-/
theorem separationPolynomial_specializes (hM : 0 < M)
    (A : Fin M → Tensor O X Y Z) (t : O) (ht : IsUnit t) :
    (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A)) := by
  classical
  obtain ⟨ζ, w, hζ, haverage⟩ := phases hM
  refine ⟨(fun x i => t ^ weightX x * fourierX ζ x i),
    (fun y j => t ^ weightY y * fourierY ζ y j),
    (fun z k => t ^ weightZ z * fourierZ ζ w z k), ?_⟩
  rw [restrict_scaled, fourier_restrict A ζ w hζ haverage]
  exact separationPolynomial_eval A t ht

-- 读法：请注意 `finite_charged_separation` 的完整类型：`∃ P : Tensor (Polynomial O) (Fin M × (X × Unit)) (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)), (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧ (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧ (∀ t : O, IsUnit t → (fun x y z => (P x y z).eval t) ∈ LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A)))`。
/-- 完整的有限构造，无须假设秩或特征标的性质。每个非零参数处的求值都由整个源直和的限制实现，常数张量本身则是各个乘积的完整直和。

英文原文：The complete finite construction, without a rank or character premise.
The nonzero-evaluation witnesses are restrictions of the full source direct
sum; the constant tensor is itself a full direct sum of products.
-/
theorem finite_charged_separation (hM : 0 < M)
    (A : Fin M → Tensor O X Y Z) :
    ∃ P : Tensor (Polynomial O) (Fin M × (X × Unit))
        (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)),
      (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧
      (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t : O, IsUnit t → (fun x y z => (P x y z).eval t) ∈
        LocalTensor.orbit (Tensor.directSum (fun _ : Fin (6 * M) => shared A))) := by
  refine ⟨separationPolynomial A, ?_, separationPolynomial_degree A,
    separationPolynomial_specializes hM A⟩
  intro x y z
  exact congrFun (congrFun (congrFun (separationPolynomial_constant A) x) y) z

end Realization

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation
