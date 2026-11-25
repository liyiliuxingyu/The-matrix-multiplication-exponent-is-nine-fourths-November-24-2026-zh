-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import Lean.Elab.Tactic.Omega

open OAI.LinearAlgebra.MatrixExponent

/-!
# 多项式乘法张量

系数张量记录通常的不截断多项式乘法。在 `a + b - 1` 个互异域元素处求值，再用同一组节点作拉格朗日插值，便给出具有相应项数的实际秩分解。

**英文原文**

The polynomial multiplication tensor

The coefficient tensor records ordinary, untruncated polynomial multiplication.
Evaluation at `a + b - 1` distinct field elements and uniform Lagrange
interpolation give an actual rank decomposition of that size.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

-- 读法：当 `i.val + j.val = k.val` 成立时取 `1`，否则取 `0`。
/-- 分别有 `a` 和 `b` 个系数的两个多项式的乘法，保留所有输出系数。

英文原文：Multiplication of polynomials with `a` and `b` coefficients, with every
output coefficient retained.
-/
def polynomialTensor (a b : ℕ) :
    Tensor Coeff (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

-- 读法：`polynomialTensor a b i j k` 等于 `if i.val + j.val = k.val then 1 else 0`。两端由定义化简为同一项。
@[simp] theorem polynomialTensor_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

-- 读法：`polynomialTensor a b i j k` 等于 `((Polynomial.X : Polynomial Coeff) ^ (i.val + j.val)).coeff k.val`。
/-- 张量系数等于两个输入单项式之积的相应系数。

英文原文：The tensor coefficient is the coefficient of the product of the two input
monomials.
-/
theorem polynomialTensor_eq_coeff (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k =
      ((Polynomial.X : Polynomial Coeff) ^ (i.val + j.val)).coeff k.val := by
  simp [polynomialTensor, Polynomial.coeff_X_pow, eq_comm]

-- 读法：`polynomialTensor a b i j k` 等于 `polynomialTensor b a j i (Fin.cast (by omega) k)`。
/-- 交换输入因子只需给维数相同的输出空间重新编排索引。

英文原文：Commuting the input factors only reindexes the equal-sized output space.
-/
theorem polynomialTensor_swap (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k =
      polynomialTensor b a j i (Fin.cast (by omega) k) := by
  simp [polynomialTensor, Nat.add_comm]

-- 读法：`polynomialTensor 1 b i j k` 等于 `if j.val = k.val then 1 else 0`。
/-- 当第一输入为标量时，乘法张量在第二输入和输出的系数坐标之间给出恒等配对。

英文原文：With a scalar as the first input, multiplication is the identity pairing
between the second input and output coefficient coordinates.
-/
theorem polynomialTensor_one_left (b : ℕ)
    (i : Fin 1) (j : Fin b) (k : Fin (1 + b - 1)) :
    polynomialTensor 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [polynomialTensor]

-- 读法：张量 `(polynomialTensor a b)` 的秩至多为 `(a + b - 1)`。用函数外延性比较等号两侧在 `i j k` 处的取值。
/-- 普通多项式乘法可显式分解为 `a + b - 1` 个秩一张量，含有空输入的退化情形也在内。

英文原文：Ordinary polynomial multiplication has an actual decomposition into
`a + b - 1` rank-one tensors. The degenerate empty-input cases are included.
-/
theorem polynomialTensor_rankAtMost (a b : ℕ) :
    Tensor.RankAtMost (polynomialTensor a b) (a + b - 1) := by
  classical
  obtain ⟨nodes, hnodes, _⟩ := exists_nonzero_nodes (F := Coeff) (a + b - 1)
  refine ⟨(fun t i => nodes t ^ i.val),
    (fun t j => nodes t ^ j.val),
    (fun t k => (Lagrange.basis Finset.univ nodes t).coeff k.val), ?_⟩
  funext i j k
  have hsum : i.val + j.val < a + b - 1 := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hdegree : ((Polynomial.X : Polynomial Coeff) ^ (i.val + j.val)).degree <
      Fintype.card (Fin (a + b - 1)) := by
    rw [Polynomial.degree_X_pow, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr hsum
  have hcoeff := Tensor.coeff_eq_sum_eval nodes hnodes
    ((Polynomial.X : Polynomial Coeff) ^ (i.val + j.val)) k.val hdegree
  rw [polynomialTensor_eq_coeff]
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Tensor.rankOne, pow_add]
    using hcoeff

end OAI.LinearAlgebra.MatrixExponent.Upper
