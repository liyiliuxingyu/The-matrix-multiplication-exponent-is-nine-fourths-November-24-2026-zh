-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-!
# 加权乘积及其支撑集大小

**英文原文**

Weighted products and the size of their support
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
variable {F : Type*} [Field F] {i j k : ℕ}

-- 读法：`WeightedRankLE` 的结果类型为 `Prop`。
def WeightedRankLE (w : Fin i → Fin j → Fin k → F) (r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

open Classical in
-- 读法：`supportSize` 的取值由 `∑ c, ∑ a, ∑ b, if w a c b = 0 then 0 else 1` 给出。
noncomputable def supportSize (w : Fin i → Fin j → Fin k → F) : ℕ :=
  ∑ c, ∑ a, ∑ b, if w a c b = 0 then 0 else 1

-- 读法：`DensityBound` 的结果类型为 `Prop`。
/-- 密度乘以普通渐近秩，给出任意精确分解的成本上界，也适用于支撑稀疏的分解。

英文原文：Density times the ordinary asymptotic rank bounds the cost of
any exact decomposition, including a sparsely supported one.
-/
def DensityBound (F : Type*) [Field F] : Prop :=
  ∀ i j k r : ℕ, 0 < i → 0 < j → 0 < k → ∀ w : Fin i → Fin j → Fin k → F,
    WeightedRankLE w r →
    supportSize w * Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k)) ≤
      (i : ℝ) * j * k * r

end OAI.LinearAlgebra.MatrixExponent.Rectangle
