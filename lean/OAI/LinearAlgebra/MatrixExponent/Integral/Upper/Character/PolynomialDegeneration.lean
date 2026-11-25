-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Degeneration
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialFiltrationFamily
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialSectorFamily

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# 从两个显式多项式族导出特征标的界

两个不等式都使用显式的有限次数限制映射。在行列式情形中，二维配对的成本也明确计入。

**英文原文**

Character bounds from the two explicit polynomial families

Both inequalities use the actual finite-degree restriction witnesses.  In
the determinant case the two-dimensional pairing is explicitly charged.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

-- 读法：`ofTensor binaryDotTensor` 等于 `dotX 2`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem binaryDotTensor_class : ofTensor binaryDotTensor = dotX 2 := by
  have heq : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      binaryDotTensor = CoefficientTensor.dotXCoeff 2 := by
    funext x y z
    simp [Tensor.pullback, binaryDotTensor, CoefficientTensor.dotXCoeff]
  change ofTensor binaryDotTensor = ofTensor (CoefficientTensor.dotXCoeff 2)
  rw [← heq]
  exact (ofTensor_pullback_equiv _ _ _ _).symm

-- 读法：`(f (ofTensor (determinantGradedTensor a b)) : ℝ)` 不超过 `(2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ)`。
theorem Character.determinant_graded_le (f : Character) (a b : ℕ) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) := by
  have h := f.polynomial_constant_le
    (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor)
    (determinantGradedTensor a b) (determinantPolynomialFamily a b) 1
    (fun i y z => congrFun (congrFun (congrFun
      (determinantPolynomialFamily_coeff_zero a b) i) y) z)
    (determinantPolynomialFamily_degree_le a b)
    (fun t ht => determinantPolynomialFamily_eval_mem_restrictionOrbit a b ht)
  rw [← ofTensor_mul, Character.map_mul, binaryDotTensor_class] at h
  have hr : (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) * f.dotXValue 2 := by
    exact_mod_cast h
  rw [f.dotXValue_eq_rpow 2 (by decide), mul_comm] at hr
  exact hr

-- 读法：`(f (ofTensor (triplingSectorTensor a h)) : ℝ)` 不超过 `(f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ)`。
theorem Character.tripling_graded_le (f : Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) := by
  have hbound := f.polynomial_constant_le
    (polynomialTensor a (triplingWidth a h)) (triplingSectorTensor a h)
    (triplingPolynomialFamily a h ha hh) 1
    (triplingPolynomialFamily_coeff_zero a h ha hh)
    (triplingPolynomialFamily_degree_le a h ha hh)
    (fun t ht => triplingPolynomialFamily_eval_mem_restrictionOrbit a h ha hh ht)
  exact_mod_cast hbound

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
