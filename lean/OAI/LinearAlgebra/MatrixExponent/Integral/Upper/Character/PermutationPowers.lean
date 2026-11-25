-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# 六个置换所得特征标的指数

以下指数恒等式由维数为二处对具体配对求值得到，与如何选取幂律的见证无关。用显式的坐标等价，可将含一个标量输入的多项式乘法与相应的实际配对等同。

**英文原文**

The exponents of the six permuted characters

The exponent identities below follow from evaluating the actual pairings at
dimension two. In particular, they do not depend on how the power-law witnesses
were chosen. Polynomial multiplication with one scalar input is identified
with the corresponding actual pairing by explicit coordinate equivalences.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

-- 读法：`ofTensor (polynomialTensor 1 n)` 等于 `dotX n`。用函数外延性比较等号两侧在 `i j k` 处的取值。
/-- 以标量作为多项式的一个输入并保留完整输出，就得到第一条腿上的配对。第二个输入为空时也成立。

英文原文：Scalar polynomial input and full output give the first-leg pairing,
including the empty second input case.
-/
theorem polynomialTensor_one_left_class (n : ℕ) :
    ofTensor (polynomialTensor 1 n) = dotX n := by
  let u : Fin 1 ≃ Unit := Equiv.ofUnique _ _
  let e : Fin (1 + n - 1) ≃ Fin n := finCongr (by omega)
  have h : polynomialTensor 1 n =
      Tensor.pullback u (Equiv.refl _) e (CoefficientTensor.dotXCoeff n) := by
    funext i j k
    simp [Tensor.pullback, CoefficientTensor.dotXCoeff,
      Fin.ext_iff, e]
  change ofTensor (polynomialTensor 1 n) = ofTensor (CoefficientTensor.dotXCoeff n)
  rw [h]
  exact ofTensor_pullback_equiv _ _ _ _

namespace Character

-- 读法：`p` 等于 `q`。
private theorem rpow_two_injective {p q : ℝ}
    (h : (2 : ℝ) ^ p = (2 : ℝ) ^ q) : p = q := by
  have hlog := congrArg Real.log h
  rw [Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
  have hpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

-- 读法：`(f.permuted i).dotXValue n` 等于 `![f.dotXValue n, f.dotYValue n, f.dotXValue n, f.dotYValue n, f.dotZValue n, f.dotZValue n] i`。
theorem permuted_dotXValue (f : Character) (i : Fin 6) (n : ℕ) :
    (f.permuted i).dotXValue n =
      ![f.dotXValue n, f.dotYValue n, f.dotXValue n,
        f.dotYValue n, f.dotZValue n, f.dotZValue n] i := by
  unfold dotXValue
  rw [f.permuted_dotX]
  fin_cases i <;> rfl

-- 读法：`(f.permuted i).pX` 等于 `![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i`。这里调用 `rpow_two_injective`。
/-- 六个实际特征标在第一条腿上的指数，按重数计。维数为二时的取值已经唯一确定这些指数。

英文原文：The first-leg exponents of the six actual characters, with their
multiplicities. Uniqueness is forced by the value at dimension two.
-/
theorem permuted_pX (f : Character) (i : Fin 6) :
    (f.permuted i).pX = ![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i := by
  apply rpow_two_injective
  have hvalue := (f.permuted i).dotXValue_eq_rpow 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hvalue
  rw [← hvalue, permuted_dotXValue]
  simp only [f.dotXValue_eq_rpow 2 (by norm_num),
    f.dotYValue_eq_rpow 2 (by norm_num), f.dotZValue_eq_rpow 2 (by norm_num),
    Nat.cast_ofNat]
  fin_cases i <;> rfl

-- 读法：`(∑ i : Fin 6, (f.permuted i).pX)` 等于 `2 * (f.pX + f.pY + f.pZ)`。
theorem sum_permuted_pX (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 2 * (f.pX + f.pY + f.pZ) := by
  simp [permuted_pX, Fin.sum_univ_succ]
  ring

-- 读法：`meanExponent` 的取值由 `(f.pX + f.pY + f.pZ) / 3` 给出。
/-- 该特征标的三个配对指数的平均值。

英文原文：The average of the character's three pairing exponents.
-/
def meanExponent (f : Character) : ℝ := (f.pX + f.pY + f.pZ) / 3

-- 读法：`0` 不超过 `f.meanExponent`。使用 `div_nonneg` 给出的结论。
theorem meanExponent_nonneg (f : Character) : 0 ≤ f.meanExponent :=
  div_nonneg f.sum_exponents_nonneg (by norm_num)

-- 读法：`f.meanExponent` 不超过 `1`。
theorem meanExponent_le_one (f : Character) : f.meanExponent ≤ 1 := by
  unfold meanExponent
  linarith [f.sum_exponents_le_three]

-- 读法：`f.pX + f.pY + f.pZ` 等于 `3 * f.meanExponent`。
theorem sum_exponents_eq_three_meanExponent (f : Character) :
    f.pX + f.pY + f.pZ = 3 * f.meanExponent := by
  unfold meanExponent
  ring

-- 读法：`(∑ i : Fin 6, (f.permuted i).pX)` 等于 `6 * f.meanExponent`。
theorem sum_permuted_pX_eq_six_meanExponent (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 6 * f.meanExponent := by
  rw [sum_permuted_pX]
  unfold meanExponent
  ring

-- 读法：`(f.permuted i).pX + (f.permuted i).pY + (f.permuted i).pZ` 等于 `f.pX + f.pY + f.pZ`。这里调用 `rpow_two_injective`。
/-- 每种维数的方阵乘法张量都在置换下保持不变，因此置换保持三个指数的和。

英文原文：A permutation cannot change the sum of the three exponents, since it
preserves the square matrix multiplication tensor at every dimension.
-/
theorem sum_exponents_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).pX + (f.permuted i).pY + (f.permuted i).pZ =
      f.pX + f.pY + f.pZ := by
  apply rpow_two_injective
  have hleft := (f.permuted i).square_value_eq_rpow 2 (by norm_num)
  have hright := f.square_value_eq_rpow 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hleft hright
  rw [← hleft, ← hright, f.permuted_square]

-- 读法：`(f.permuted i).meanExponent` 等于 `f.meanExponent`。
@[simp] theorem meanExponent_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).meanExponent = f.meanExponent := by
  unfold meanExponent
  rw [sum_exponents_permuted]

-- 读法：`(f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ)` 等于 `(n : ℝ) ^ (f.permuted i).pX`。这里调用 `f.permuted`。
theorem permuted_polynomialTensor_one_left_value
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (f.permuted i).pX := by
  rw [polynomialTensor_one_left_class]
  exact (f.permuted i).dotXValue_eq_rpow n hn

-- 读法：`(f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ)` 等于 `(n : ℝ) ^ (![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i)`。
/-- 六个边界值分别是指数为 `pX, pY, pX, pY, pZ, pZ` 的幂。

英文原文：The six boundary values are the powers with exponents
`pX, pY, pX, pY, pZ, pZ`.
-/
theorem permuted_polynomialTensor_one_left_vector
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i) := by
  rw [permuted_polynomialTensor_one_left_value f i n hn, permuted_pX]

-- 读法：`(f.permuted i (ofTensor (polynomialTensor n 1)) : ℝ)` 等于 `(n : ℝ) ^ (f.permuted (permuteSwapXY i)).pX`。这里调用 `f.permuted_polynomialTensor_one_left_value`。
theorem permuted_polynomialTensor_one_right_value
    (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor n 1)) : ℝ) =
      (n : ℝ) ^ (f.permuted (permuteSwapXY i)).pX := by
  rw [← swapXY_polynomialTensor 1 n, f.permuted_swapXY]
  exact f.permuted_polynomialTensor_one_left_value (permuteSwapXY i) n hn

end Character
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
