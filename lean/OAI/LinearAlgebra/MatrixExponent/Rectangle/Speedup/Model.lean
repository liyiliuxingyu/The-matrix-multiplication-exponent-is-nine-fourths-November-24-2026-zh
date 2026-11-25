-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-!
# 有限边界秩不等式的参数

**英文原文**

Parameters of the finite border-rank inequality
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

-- 读法：`largest` 的取值由 `max (i * j) (max (i * k) (j * k))` 给出。
def largest (i j k : ℕ) := max (i * j) (max (i * k) (j * k))

-- 读法：`value` 的取值由 `Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))` 给出。
def value (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))

-- 读法：`slope` 的取值由 `Real.log (value F i j k) / Real.log ((i : ℝ) * j * k)` 给出。
def slope (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.log (value F i j k) / Real.log ((i : ℝ) * j * k)

-- 读法：`Speedup.cStar` 的取值由 `sSup {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v}` 给出。
def Speedup.cStar : ℝ := sSup {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v}

end OAI.LinearAlgebra.MatrixExponent.Rectangle
