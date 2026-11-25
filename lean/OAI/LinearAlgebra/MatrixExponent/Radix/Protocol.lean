-- 本文件所属证明环节：按位段执行稳定排序，将短记录与宽记录的带标签置换问题分解成可安装的较小调用，并估计每阶段的槽位与成本。
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag

/-!
# 安装较小规模的带标签置换调用的成本

**英文原文**

Cost of installing the smaller tagged-permutation calls
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：`Protocol` 的结果类型为 `Prop`。
/-- 路由协议的一层，仅处理长度为 `h^A` 的载荷。归纳成本是 `L` 份较短验证器的成本。即使高度之比缩小，总载荷项的常数仍有界。

英文原文：One layer of the routing protocol, restricted to payloads of length
`h^A`. The inductive cost is that of `L` copies of a shorter verifier.
The constant on the total payload stays bounded as the height ratio shrinks.
-/
def Protocol (F : Type) [Field F] : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∃ Y : ℝ, 0 < Y ∧ ∃ J : ℕ,
    ∀ A : ℕ, J ≤ A → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in Filter.atTop,
      ∃ l v M L : ℕ, 1 ≤ l ∧ (l : ℝ) ≤ τ * h ∧ Y * (h : ℝ) ^ A ≤ v ∧
        (L : ℝ) * (2 : ℝ) ^ l * v ≤ C * (2 : ℝ) ^ h * (h : ℝ) ^ A ∧
        (M : ℝ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ ∧
        ∀ s, Tag F l v s → ∃ m ≤ M + L * s, Tag F h (h ^ A) m

end OAI.LinearAlgebra.MatrixExponent.Radix
