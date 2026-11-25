-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Data.Fintype.BigOperators

/-!
# 各次张量幂的精确秩及其渐近增长率

幂的每条边对每个副本各有一个独立数位。在支撑密度为正时证明收敛到所述极限。

**英文原文**

Exact ranks of powers and their asymptotic rate

Each side of a power has one independent digit per copy. Convergence
to the stated limit is proved for positive support density.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F : Type*} [Field F] {i j k : ℕ}

-- 读法：输入 `a b c` 时返回 `∏ l : Fin n, w (finFunctionFinEquiv.symm a l) (finFunctionFinEquiv.symm b l) (finFunctionFinEquiv.symm c l)`。
def WPower (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    Fin (i ^ n) → Fin (j ^ n) → Fin (k ^ n) → F := fun a b c =>
  ∏ l : Fin n, w (finFunctionFinEquiv.symm a l)
    (finFunctionFinEquiv.symm b l) (finFunctionFinEquiv.symm c l)

-- 读法：`rankW` 的取值由 `sInf {r : ℕ | WeightedRankLE w r}` 给出。
def rankW (w : Fin i → Fin j → Fin k → F) : ℕ := sInf {r : ℕ | WeightedRankLE w r}

-- 读法：`asymptoticRank` 的取值由 `limUnder atTop fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹` 给出。
def asymptoticRank (w : Fin i → Fin j → Fin k → F) : ℝ :=
  limUnder atTop fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹

-- 读法：输入 `_ _ _` 时返回 `1`。
def ordinary (F : Type*) [Field F] (i j k : ℕ) : Fin i → Fin j → Fin k → F :=
  fun _ _ _ => 1

-- 读法：`density` 的取值由 `supportSize w / ((i : ℝ) * j * k)` 给出。
def density (w : Fin i → Fin j → Fin k → F) : ℝ := supportSize w / ((i : ℝ) * j * k)

-- 读法：`normalized` 的取值由 `let A := (side n x : ℝ) * side n y ((r n : ℝ) - A) * Real.log A / A` 给出。
/-- 用输出面积除以其自然对数所得的量对盈余作归一化。

英文原文：Normalize the surplus by the output area divided by its natural logarithm.
-/
noncomputable def normalized (x y : ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  let A := (side n x : ℝ) * side n y
  ((r n : ℝ) - A) * Real.log A / A

end OAI.LinearAlgebra.MatrixExponent.Rectangle
