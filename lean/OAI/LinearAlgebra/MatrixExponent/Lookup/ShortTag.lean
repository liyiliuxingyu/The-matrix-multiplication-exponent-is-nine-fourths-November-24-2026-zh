-- 本文件所属证明环节：把批量查表的查询与字典记录排序和分组，用扫描、短标签及重数约束验证选取的表项，再将查表网络接回宽网络。
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

-- 读法：`ShortTag` 表示以下条件：存在 `C : ℝ`，对每个 `w : ℕ`，要证明的命题是 `1 ≤ w → ∃ v : ℕ, Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) v ∧ (v : ℝ) ≤ C * (2 : ℝ) ^ w * (w : ℝ) ^ p`。
/-- 普通宽度的带标签置换估计。

英文原文：The ordinary-width tagged permutation estimate.
-/
def ShortTag (F : Type) [Field F] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∃ v : ℕ,
    Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) v ∧
    (v : ℝ) ≤ C * (2 : ℝ) ^ w * (w : ℝ) ^ p

end OAI.LinearAlgebra.MatrixExponent.Lookup
