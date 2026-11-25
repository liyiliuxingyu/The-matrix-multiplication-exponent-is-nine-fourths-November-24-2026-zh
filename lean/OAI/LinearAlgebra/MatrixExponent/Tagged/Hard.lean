-- 本文件所属证明环节：把带标签置换、稳定排序和列表判重联系起来；通过给出的归约，把置换验证的困难性转化为批量判重下界。
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags

/-!
# 核验一个置换所需的对数幂下界

**英文原文**

Power-of-logarithm lower bound for verifying one permutation
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged
open Filter

-- 读法：`Hard` 表示以下条件：存在 `σ : ℝ`，由 `0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m, Net F (inputs w (word w)) .unit (tag F w (word w)) m` 推出 `(2 : ℝ) ^ w * w * (w : ℝ) ^ σ ≤ m`。
/-- 只需考虑尺度为二的幂的方形有效载荷。对精确实现的三价网络计顶点数。把正指数调小即可吸收下界中的任意常数。

英文原文：Only square payloads at powers of two are required. Count vertices
of exact trivalent networks. Any constant in the lower bound can be
absorbed by decreasing the positive exponent.
-/
def Hard (F : Type) [Field F] : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m,
    Net F (inputs w (word w)) .unit (tag F w (word w)) m →
    (2 : ℝ) ^ w * w * (w : ℝ) ^ σ ≤ m

end OAI.LinearAlgebra.MatrixExponent.Tagged
