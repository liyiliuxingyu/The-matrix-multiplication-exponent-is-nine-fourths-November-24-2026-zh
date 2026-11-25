-- 本文件所属证明环节：分别固定三条连线中的一条，在其对面站点的张量展平中选出一个方形子矩阵。由连线指标必须匹配，该子矩阵为恒等阵。这给出了三个展平方向的满行秩证据，对域的特征没有限制。
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.Data.Matrix.Diagonal

/-!
# 矩阵乘法张量中的单位子式

固定一个位置对面的连线，可在该位置的展平矩阵中选出一个方形子矩阵，每个局部索引对应一行。连线匹配规则保证此子矩阵为单位矩阵，与标量域的特征无关。

**英文原文**

Identity minors of the matrix multiplication tensor

Fixing the wire opposite a site selects a square submatrix of its flattening
with one row for every local index. The matching-wire rule makes this
submatrix the identity, independently of the scalar characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation.Tensor

variable {K A B C : Type*} [CommSemiring K] [DecidableEq A] [DecidableEq B] [DecidableEq C]

-- 读法：`Matrix.of (fun x x' : A × B => matrixCoefficients (K := K) A B C x (x'.2, k) (k, x'.1))` 等于 `1`。按 `x.1 = x'.1 <;> by_cases hb : x.2 = x'.2 <;> simp_all [eq_comm]` 成立与否分情况。
/-- 固定第三条连线，读出第一个位置的两个指标。

英文原文：Fix the third wire and read off both indices of the first site.
-/
theorem matrixMinor₁ (k : C) :
    Matrix.of (fun x x' : A × B =>
      matrixCoefficients (K := K) A B C x (x'.2, k) (k, x'.1)) = 1 := by
  ext x x'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases ha : x.1 = x'.1 <;> by_cases hb : x.2 = x'.2 <;> simp_all [eq_comm]

-- 读法：`Matrix.of (fun y y' : B × C => matrixCoefficients (K := K) A B C (i, y'.1) y (y'.2, i))` 等于 `1`。按 `y.1 = y'.1 <;> by_cases hc : y.2 = y'.2 <;> simp_all [eq_comm]` 成立与否分情况。
/-- 固定第一条连线，读出第二个位置的两个指标。

英文原文：Fix the first wire and read off both indices of the second site.
-/
theorem matrixMinor₂ (i : A) :
    Matrix.of (fun y y' : B × C =>
      matrixCoefficients (K := K) A B C (i, y'.1) y (y'.2, i)) = 1 := by
  ext y y'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hb : y.1 = y'.1 <;> by_cases hc : y.2 = y'.2 <;> simp_all [eq_comm]

-- 读法：`Matrix.of (fun z z' : C × A => matrixCoefficients (K := K) A B C (z'.2, j) (j, z'.1) z)` 等于 `1`。按 `z.1 = z'.1 <;> by_cases ha : z.2 = z'.2 <;> simp_all [eq_comm]` 成立与否分情况。
/-- 固定第二条连线，读出第三个位置的两个指标。

英文原文：Fix the second wire and read off both indices of the third site.
-/
theorem matrixMinor₃ (j : B) :
    Matrix.of (fun z z' : C × A =>
      matrixCoefficients (K := K) A B C (z'.2, j) (j, z'.1) z) = 1 := by
  ext z z'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hc : z.1 = z'.1 <;> by_cases ha : z.2 = z'.2 <;> simp_all [eq_comm]

end SpectralBooks
end LinearAlgebra
end OAI
