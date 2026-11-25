-- 本文件所属证明环节：用有限三线性系数张量定义通常秩，并用各正整数次张量幂的秩根的下确界定义渐近秩。矩阵乘法的三条连线依次标为 12、23、31；三个指标均匹配时相应张量坐标才非零。
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# 域上的矩形矩阵乘法

这里采用矩阵乘法库中的有限系数张量与克罗内克幂。各维数是共享连线的大小，按论文中的 `12, 23, 31` 排列。因此第一个位置的坐标由 `Fin n31 × Fin n12` 索引。

**英文原文**

Rectangular matrix multiplication over a field

We use the finite coefficient tensors and Kronecker powers from the matrix
multiplication library. The dimensions are the shared wire sizes, in the
paper's order `12, 23, 31`. The first site's coordinates are consequently
indexed by `Fin n31 × Fin n12`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

section

section Rank

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

-- 读法：存在 `r`，张量 `T` 的秩至多为 `r`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 在前两个位置的坐标基下展开，得到有限个简单张量的分解。

英文原文：Expanding in the coordinate bases of the first two sites gives a finite
decomposition into simple tensors.
-/
theorem exists_rankAtMost (T : Tensor F X Y Z) : ∃ r, Tensor.RankAtMost T r := by
  classical
  let a : X × Y → X → F := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → F := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → F := fun p => T p.1 p.2
  refine ⟨Fintype.card (X × Y), ?_⟩
  have h : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [h]
  exact Tensor.rankAtMost_sum_rankOne a b c

-- 读法：`tensorRank` 的结果类型为 `ℕ`。
/-- 基域上分解所需简单张量数的最小值。

英文原文：The least number of simple tensors in a decomposition over the ground field.
-/
def tensorRank (T : Tensor F X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

-- 读法：张量 `T` 的秩至多为 `(tensorRank T)`。这里调用 `Nat.find_spec`。
theorem rankAtMost_tensorRank (T : Tensor F X Y Z) : Tensor.RankAtMost T (tensorRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

-- 读法：`tensorRank T` 不超过 `r`。这里调用 `Nat.find_min'`。
theorem tensorRank_le_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : tensorRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

-- 读法：`asymptoticRank` 的取值由 `⨅ n : ℕ, (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)` 给出。
/-- 对所有正次数张量幂的秩开相应次方根，再取下确界。

英文原文：The infimum of the positive tensor-power rank roots.
-/
def asymptoticRank (T : Tensor F X Y Z) : ℝ :=
  ⨅ n : ℕ, (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

-- 读法：`0` 不超过 `asymptoticRank T`。使用 `le_ciInf` 给出的结论。
theorem asymptoticRank_nonneg (T : Tensor F X Y Z) : 0 ≤ asymptoticRank T :=
  le_ciInf (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

-- 读法：`asymptoticRank T` 不超过 `tensorRank T`。这里调用 `le_trans`。
theorem asymptoticRank_le_tensorRank (T : Tensor F X Y Z) :
    asymptoticRank T ≤ tensorRank T := by
  have hu := ciInf_le ⟨(0 : ℝ), by rintro _ ⟨n, rfl⟩; positivity⟩ (0 : ℕ)
    (f := fun n : ℕ => (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹))
  have h₁ := tensorRank_le_of_rankAtMost ((rankAtMost_tensorRank T).power 1)
  simp only [pow_one] at h₁
  apply le_trans _ (Nat.cast_le (α := ℝ) |>.mpr h₁)
  simpa [asymptoticRank] using hu

end Rank

-- 读法：在后续公式中，`matrixTensor` 是 `Tensor.matrixCoefficients (K := F) (Fin n31) (Fin n12) (Fin n23)` 的缩写。
/-- 循环图样 `e_{ki} ⊗ e_{ij} ⊗ e_{jk}` 的系数为一。

英文原文：The coefficient of the cyclic pattern `e_{ki} ⊗ e_{ij} ⊗ e_{jk}` is one.
-/
abbrev matrixTensor (F : Type*) [Field F] (n12 n23 n31 : ℕ) :=
  Tensor.matrixCoefficients (K := F) (Fin n31) (Fin n12) (Fin n23)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
