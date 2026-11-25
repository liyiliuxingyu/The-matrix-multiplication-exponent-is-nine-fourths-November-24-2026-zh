-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialDegeneration
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# 实现对角权重退化的显式多项式族

对角退化带有一个显式的多项式系数族，其常数项就是保留下来的张量。其次数由支集上的总权重控制。在所有非零参数处，它的值都为源张量的精确限制。利用这些数据可以通过有限插值提取张量幂，无须依赖拓扑极限。

**英文原文**

Explicit polynomial families for diagonal weight degenerations

The diagonal degeneration has a polynomial coefficient family, not merely a
topological limit. Its constant coefficient is the retained tensor. Its degree
is controlled by the supported total weights. At every nonzero parameter its
evaluation is an exact restriction of the source tensor. These are the inputs
needed to extract tensor powers by finite interpolation.
-/

open OAI.MatrixMultiplication.Foundation

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Upper

variable {X Y Z : Type*}

-- 读法：输入 `x y z` 时返回 `Polynomial.monomial (wx x + wy y + wz z).toNat (T x y z)`。
/-- 与三组整数坐标权重相应的单项式族。

英文原文：The monomial family associated to three integer coordinate weights.
-/
def weightedPolynomial (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) :
    Tensor (Polynomial Coeff) X Y Z :=
  fun x y z => Polynomial.monomial (wx x + wy y + wz z).toNat (T x y z)

-- 读法：`(fun x y z => (weightedPolynomial T wx wy wz x y z).eval t)` 等于 `weightedFamily T wx wy wz t`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 多项式求值与退化证明中所用的连续系数族一致，在参数为零处也如此。

英文原文：Polynomial evaluation agrees with the continuous coefficient family used
in the degeneration proof, including at the parameter zero.
-/
theorem weightedPolynomial_eval (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) (t : Coeff) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) =
      weightedFamily T wx wy wz t := by
  funext x y z
  simp [weightedPolynomial, weightedFamily, Polynomial.eval_monomial, mul_comm]

-- 读法：`(weightedPolynomial T wx wy wz x y z).coeff 0` 等于 `weightedLimit T wx wy wz x y z`。
/-- 常数项恰好保留支集中所有权重为零的项。

英文原文：The constant coefficient keeps precisely the supported weight-zero terms.
-/
theorem weightedPolynomial_coeff_zero (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).coeff 0 =
      weightedLimit T wx wy wz x y z := by
  have heq := (weightedPolynomial_eval T wx wy wz 0).trans
    (weightedFamily_zero T wx wy wz h)
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    congrFun (congrFun (congrFun heq x) y) z

-- 读法：`(weightedPolynomial T wx wy wz x y z).natDegree` 不超过 `D`。按 `T x y z = 0` 成立与否分情况。
/-- 只需对支集上的系数给出次数上界。支集以外的坐标无论分配何种权重，都给出零多项式。

英文原文：A degree bound is needed only on supported coefficients. Unsupported
coordinates are the zero polynomial, regardless of their assigned weights.
-/
theorem weightedPolynomial_natDegree_le (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).natDegree ≤ D := by
  by_cases hT : T x y z = 0
  · simp [weightedPolynomial, hT]
  · exact (Polynomial.natDegree_monomial_le (T x y z)).trans (hD x y z hT)

-- 读法：`(weightedPolynomial T wx wy wz x y z).degree` 不超过 `D`。
/-- 将同一次数上界写成多项式插值所用的形式。

英文原文：The same degree bound in the form used by polynomial interpolation.
-/
theorem weightedPolynomial_degree_le (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ D :=
  Polynomial.degree_le_of_natDegree_le
    (weightedPolynomial_natDegree_le T wx wy wz hD x y z)

-- 读法：`(weightedPolynomial T wx wy wz x y z).degree` 不超过 `(1 : ℕ)`。这里调用 `weightedPolynomial_degree_le`。
/-- 若支集按权重分为零和一两部分，次数至多为一。行列式滤过与三分区拆分用的就是这个界。

英文原文：A weight-zero/weight-one support split gives degree at most one. This is
the bound used by the determinant filtration and the three-sector split.
-/
theorem weightedPolynomial_degree_le_one (T : Tensor Coeff X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 →
      wx x + wy y + wz z = 0 ∨ wx x + wy y + wz z = 1)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ (1 : ℕ) := by
  apply weightedPolynomial_degree_le T wx wy wz
  intro u v w hT
  rcases h u v w hT with hw | hw <;> simp [hw]

-- 读法：`(fun x y z => (weightedPolynomial T wx wy wz x y z).eval t)` 属于 `LocalTensor.orbit T`。这里调用 `weightedFamily_mem_restrictionOrbit`。
/-- 任意非零参数处的值都有显式的对角局部限制映射。这个多项式族的构造无需预设特征标或连续性原理。

英文原文：Every nonzero evaluation has actual diagonal local restriction witnesses;
the polynomial family does not assume a character or a continuity principle.
-/
theorem weightedPolynomial_eval_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : Coeff} (ht : t ≠ 0) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) ∈
      LocalTensor.orbit T := by
  rw [weightedPolynomial_eval]
  exact weightedFamily_mem_restrictionOrbit T wx wy wz h ht

-- 读法：`V` 属于 `LocalTensor.orbit T`。
/-- 实现局部限制的显式映射可以直接复合，无需求极限。

英文原文：Actual local restriction witnesses compose without a limiting argument.
-/
theorem restrictionOrbit_trans
    {X' Y' Z' X'' Y'' Z'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor Coeff X Y Z} {U : Tensor Coeff X' Y' Z'} {V : Tensor Coeff X'' Y'' Z''}
    (hTU : U ∈ LocalTensor.orbit T)
    (hUV : V ∈ LocalTensor.orbit U) :
    V ∈ LocalTensor.orbit T := by
  rcases hTU with ⟨A, B, C, rfl⟩
  rcases hUV with ⟨D, E, F, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix D A, Tensor.composeRestrictionMatrix E B,
    Tensor.composeRestrictionMatrix F C, Tensor.restrict_restrict A B C D E F T⟩

end OAI.LinearAlgebra.MatrixExponent.Upper
