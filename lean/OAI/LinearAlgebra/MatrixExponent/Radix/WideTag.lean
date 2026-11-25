-- 本文件所属证明环节：按位段执行稳定排序，将短记录与宽记录的带标签置换问题分解成可安装的较小调用，并估计每阶段的槽位与成本。
import OAI.LinearAlgebra.MatrixExponent.Lookup.ShortTag

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：`Tag` 表示以下条件：存在从 `(Tagged.inputs w (word v))` 到 `.unit` 的网络，核为 `(Tagged.tag F w (word v))`，顶点数为 `m`，系数取自 `F`。
def Tag (F : Type) [Field F] (w v m : ℕ) : Prop :=
  Net F (Tagged.inputs w (word v)) .unit (Tagged.tag F w (word v)) m

-- 读法：`WideTag` 表示以下条件：对每个 `ζ : ℝ`，要证明的命题是 `0 < ζ → ∃ A : ℕ, 2 ≤ A ∧ ∃ C : ℝ, ∀ w v : ℕ, 1 ≤ w → w ^ A ≤ v → ∃ m : ℕ, Tag F w v m ∧ (m : ℝ) ≤ C * (2 : ℝ) ^ w * v * (w : ℝ) ^ ζ`。
/-- 条件稳定排序定理中的宽记录估计。

英文原文：The wide-record estimate in the conditional stable sorting theorem.
-/
def WideTag (F : Type) [Field F] : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ A : ℕ, 2 ≤ A ∧ ∃ C : ℝ, ∀ w v : ℕ, 1 ≤ w → w ^ A ≤ v →
    ∃ m : ℕ, Tag F w v m ∧ (m : ℝ) ≤ C * (2 : ℝ) ^ w * v * (w : ℝ) ^ ζ

end OAI.LinearAlgebra.MatrixExponent.Radix
