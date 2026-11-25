-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel

/-!
# 在调和阈值处缩放内维数

**英文原文**

Scaling the inner dimension at the harmonic threshold
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold

-- 读法：`width` 的取值由 `⌈a * (n : ℝ) ^ (x * y)⌉₊` 给出。
def width (n : ℕ) (x y a : ℝ) := ⌈a * (n : ℝ) ^ (x * y)⌉₊

-- 读法：`gain` 的取值由 `Real.exp (-u) * (max (b + C * u) 0) ^ 2 / 4` 给出。
def gain (b C u : ℝ) := Real.exp (-u) * (max (b + C * u) 0) ^ 2 / 4

-- 读法：当 `b ≤ 2 * C` 成立时取 `C ^ 2 * Real.exp (b / C - 2)`，否则取 `b ^ 2 / 4`。
def optimum (b C : ℝ) := if b ≤ 2 * C then C ^ 2 * Real.exp (b / C - 2) else b ^ 2 / 4

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold
