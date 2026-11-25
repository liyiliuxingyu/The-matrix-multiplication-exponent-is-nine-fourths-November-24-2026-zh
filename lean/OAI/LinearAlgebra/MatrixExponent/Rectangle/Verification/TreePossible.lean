-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Gaps


/-!
# 用算术树和相等性检验树进行验证

每个种子各有自己的有限树和见证坐标数。在得知种子后才选取见证。大小上界计入单条路径上算术运算与检验总数的最大值。

**英文原文**

Verification by arithmetic and equality-test trees

Each seed has its own finite tree and number of witness coordinates.
The witness is chosen after the seed is known. The size bound counts
the maximum number of arithmetic operations and tests on a path.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter
variable (F : Type*) [Field F]

-- 读法：`TreeSupportPossible` 的结果类型为 `Prop`。
def TreeSupportPossible (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (t : ι → ℕ) (A : ∀ i, Tree F n (t i)),
      (Fintype.card ι : ℝ) ≤ (n : ℝ) ^ (ρ + ε) ∧ (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
      (∀ i, ((A i).depth : ℝ) ≤ (n : ℝ) ^ (v + ε)) ∧ Accurate w (fun i => (A i).accept) Correct

-- 读法：`TreeEntropyPossible` 的结果类型为 `Prop`。
def TreeEntropyPossible (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℝ) (t : ι → ℕ) (A : ∀ i, Tree F n (t i)),
      (∃ E, HasSum (fun i => -w i * Real.log (w i)) E ∧ E ≤ (η + ε) * Real.log n) ∧
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ (∀ i, ((A i).depth : ℝ) ≤ (n : ℝ) ^ (v + ε)) ∧
      Accurate w (fun i => (A i).accept) Correct

-- 读法：`treeSupportExponent` 的取值由 `sInf {v : ℝ | TreeSupportPossible F ρ v}` 给出。
def treeSupportExponent (ρ : ℝ) := sInf {v : ℝ | TreeSupportPossible F ρ v}
-- 读法：`treeEntropyExponent` 的取值由 `sInf {v : ℝ | TreeEntropyPossible F η v}` 给出。
def treeEntropyExponent (η : ℝ) := sInf {v : ℝ | TreeEntropyPossible F η v}

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
