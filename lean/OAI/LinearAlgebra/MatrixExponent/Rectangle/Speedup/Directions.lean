-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# 指数的单侧坐标导数

**英文原文**

The one-sided coordinate derivatives of an exponent
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Set

-- 读法：`vary` 的取值由 `![L (a + t) b c, L a (b + t) c, L a b (c + t)] e` 给出。
def vary (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) (t : ℝ) : ℝ :=
  ![L (a + t) b c, L a (b + t) c, L a b (c + t)] e

-- 读法：`partialRight` 的取值由 `derivWithin (vary L a b c e) (Ici 0) 0` 给出。
def partialRight (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) : ℝ :=
  derivWithin (vary L a b c e) (Ici 0) 0

end OAI.LinearAlgebra.MatrixExponent.Rectangle
