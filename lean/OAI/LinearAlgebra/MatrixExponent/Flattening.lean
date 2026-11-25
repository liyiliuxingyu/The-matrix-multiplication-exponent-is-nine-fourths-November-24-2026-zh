-- 本文件所属证明环节：对方阵乘法张量沿输出方向展平，从输出空间的维数得到每个秩分解至少需要边长平方项。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：`n ^ 2` 不超过 `r`。按 `n = 0` 成立与否分情况。
/-- 方阵乘法张量沿输出指标展平所得的矩阵，其秩等于输出面积。

英文原文：The square output flattening has rank equal to the area.
-/
theorem rank_lower {F : Type*} [Field F] {n r : ℕ} (h : RankLE F n r) :
    n ^ 2 ≤ r := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [pow_two]
    exact Rectangle.RankLE.area h (Nat.pos_of_ne_zero hn)

end OAI.LinearAlgebra.MatrixExponent
