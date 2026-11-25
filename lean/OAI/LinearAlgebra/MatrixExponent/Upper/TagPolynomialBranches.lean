-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.TagHeterogeneous
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialFiltration
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Permutations
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.PolynomialValues

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# 异型标记构造中的多项式分支

各个行列式分支保留其实际的输出坐标；通过有限坐标集上的等价可将其张量类与多项式乘法的类等同。三倍化构造的中间分支先交换后两条腿，再对共享第一坐标施行所述的可逆反转。

**英文原文**

Polynomial branches in the heterogeneous tag construction

The determinant branches retain their actual output coordinates; finite
coordinate equivalences identify their classes with polynomial multiplication.
The middle tripling branch is a last-two-leg swap followed by the stated
invertible reversal of the shared first coordinate.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TagHeterogeneous

-- 读法：当 `i.val + j.val = k.val` 成立时取 `1`，否则取 `0`。
/-- 行列式滤过保留下来的较大分支。

英文原文：The larger retained branch of the determinant filtration.
-/
def determinantQuotientTensor (a b : ℕ) :
    Tensor Coeff (Fin (a + 1)) (Fin (b + 3)) (Fin (a + b + 3)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

-- 读法：当 `i.val + j.val = k.val` 成立时取 `1`，否则取 `0`。
/-- 行列式滤过保留下来的较小分支。

英文原文：The smaller retained branch of the determinant filtration.
-/
def determinantKernelTensor (a b : ℕ) :
    Tensor Coeff (Fin (a + 1)) (Fin (b + 1)) (Fin (a + b + 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

-- 读法：`determinantGradedTensor a b` 等于 `sharedTwo (determinantQuotientTensor a b) (determinantKernelTensor a b)`。用函数外延性比较等号两侧在 `i j k` 处的取值。
theorem determinantGradedTensor_eq_sharedTwo (a b : ℕ) :
    determinantGradedTensor a b =
      sharedTwo (determinantQuotientTensor a b) (determinantKernelTensor a b) := by
  funext i j k
  cases j <;> cases k <;> rfl

-- 读法：`TensorClass.ofTensor (determinantQuotientTensor a b)` 等于 `TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3))`。用函数外延性比较等号两侧在 `i j k` 处的取值。
theorem ofTensor_determinantQuotient (a b : ℕ) :
    TensorClass.ofTensor (determinantQuotientTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)) := by
  let e : Fin (a + b + 3) ≃ Fin (a + 1 + (b + 3) - 1) := finCongr (by omega)
  have heq : determinantQuotientTensor a b =
      Tensor.pullback (Equiv.refl _) (Equiv.refl _) e
        (polynomialTensor (a + 1) (b + 3)) := by
    funext i j k
    rfl
  rw [heq]
  exact TensorClass.ofTensor_pullback_equiv _ _ _ _

-- 读法：`TensorClass.ofTensor (determinantKernelTensor a b)` 等于 `TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))`。用函数外延性比较等号两侧在 `i j k` 处的取值。
theorem ofTensor_determinantKernel (a b : ℕ) :
    TensorClass.ofTensor (determinantKernelTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1)) := by
  let e : Fin (a + b + 1) ≃ Fin (a + 1 + (b + 1) - 1) := finCongr (by omega)
  have heq : determinantKernelTensor a b =
      Tensor.pullback (Equiv.refl _) (Equiv.refl _) e
        (polynomialTensor (a + 1) (b + 1)) := by
    funext i j k
    rfl
  rw [heq]
  exact TensorClass.ofTensor_pullback_equiv _ _ _ _

-- 读法：结论为 `TensorClass.ofTensor (Separation.shared (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b))) = TensorClass.ofTensor (determinantGradedTensor a b)`。
/-- 统一分离构造以整个分次行列式张量为输入。

英文原文：The uniform separation input is the whole graded determinant tensor.
-/
theorem ofTensor_determinant_uniform (a b : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b))) =
      TensorClass.ofTensor (determinantGradedTensor a b) := by
  rw [ofTensor_shared_twoFamily, determinantGradedTensor_eq_sharedTwo]

-- 读法：结论为 `TensorClass.ofTensor (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j) = ![TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)), TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))] j`。
/-- 两个原始多项式分支在补零后均精确保留。

英文原文：Both original polynomial branches survive zero padding exactly.
-/
theorem ofTensor_determinant_family (a b : ℕ) (j : Fin 2) :
    TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j) =
      ![TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)),
        TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))] j := by
  rw [ofTensor_twoFamily, ofTensor_determinantQuotient, ofTensor_determinantKernel]

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Fin a ≃ Fin a`。
/-- 这一次序反转构成一个显式等价，也适用于空的有限类型。

英文原文：This reversal is an actual equivalence, including the empty finite type.
-/
def triplingReverseEquiv (a : ℕ) : Fin a ≃ Fin a where
  toFun := triplingReverse
  invFun := triplingReverse
  left_inv := triplingReverse_involutive
  right_inv := triplingReverse_involutive

-- 读法：`TensorClass.ofTensor (triplingMiddleTensor a h)` 等于 `TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h))`。
/-- 用置换后的特征标对中间分支求值。第一坐标的次序反转仅通过一个可逆局部映射消除。

英文原文：The middle branch is evaluated using the permuted character. Its
first-coordinate reversal is removed only by an invertible local map.
-/
theorem ofTensor_triplingMiddle (a h : ℕ) :
    TensorClass.ofTensor (triplingMiddleTensor a h) =
      TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)) := by
  have heq : triplingMiddleTensor a h =
      Tensor.pullback (triplingReverseEquiv a) (Equiv.refl _) (Equiv.refl _)
        (CoefficientTensor.swapYZ (polynomialTensor a h)) := rfl
  rw [heq, TensorClass.ofTensor_pullback_equiv, TensorClass.swapYZ_ofTensor]

-- 读法：请注意 `ofTensor_tripling_family` 的完整类型：`TensorClass.ofTensor (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h) (polynomialTensor a h) j) = ![TensorClass.ofTensor (polynomialTensor a h), TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)), TensorClass.ofTensor (polynomialTensor a h)] j`。
theorem ofTensor_tripling_family (a h : ℕ) (j : Fin 3) :
    TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j) =
      ![TensorClass.ofTensor (polynomialTensor a h),
        TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)),
        TensorClass.ofTensor (polynomialTensor a h)] j := by
  rw [ofTensor_threeFamily, ofTensor_triplingMiddle]

-- 读法：`0` 严格小于 `(f (TensorClass.ofTensor (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j)) : ℝ)`。这里调用 `f.polynomial_value_pos`。
/-- 先前已证各多项式的特征标值为正，由此可知各个补零后的行列式分支也具有正值。

英文原文：Positivity for every padded determinant branch follows from the already
established positive polynomial character values.
-/
theorem determinant_family_value_pos (f : TensorClass.Character) (a b : ℕ) (j : Fin 2) :
    0 < (f (TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j)) : ℝ) := by
  rw [ofTensor_determinant_family]
  fin_cases j <;> simp only
  · exact f.polynomial_value_pos _ _ (by omega) (by omega)
  · exact f.polynomial_value_pos _ _ (by omega) (by omega)

-- 读法：`0` 严格小于 `(f (TensorClass.ofTensor (triplingMiddleTensor a h)) : ℝ)`。
/-- 中间分支的正值由实际置换后的特征标给出。

英文原文：The positive middle value uses the actual permuted character.
-/
theorem tripling_middle_value_pos (f : TensorClass.Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 < (f (TensorClass.ofTensor (triplingMiddleTensor a h)) : ℝ) := by
  rw [ofTensor_triplingMiddle]
  have hp := (f.permuted 2).polynomial_value_pos a h ha hh
  simpa [TensorClass.Character.permuted_apply, TensorClass.permute,
    TensorClass.permuteHom, TensorClass.swapYZHom] using hp

-- 读法：要证明的命题是 `0 < (f (TensorClass.ofTensor (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h) (polynomialTensor a h) j)) : ℝ)`。这里调用 `f.polynomial_value_pos`。
/-- 这些严格正值满足统一标签不等式的假设，补零且反转后的中间分支也包括在内。

英文原文：These strict positive values are the hypotheses of the uniform tag
inequality, including the padded and reversed middle branch.
-/
theorem tripling_family_value_pos (f : TensorClass.Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) (j : Fin 3) :
    0 < (f (TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j)) : ℝ) := by
  rw [ofTensor_threeFamily]
  fin_cases j <;> simp only
  · exact f.polynomial_value_pos _ _ ha hh
  · exact tripling_middle_value_pos f a h ha hh
  · exact f.polynomial_value_pos _ _ ha hh

end OAI.LinearAlgebra.MatrixExponent.Upper.TagHeterogeneous
