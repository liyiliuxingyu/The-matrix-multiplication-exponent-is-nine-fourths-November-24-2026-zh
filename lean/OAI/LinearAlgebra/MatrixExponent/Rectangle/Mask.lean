-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights

/-!
# 加权乘积在输出单元上的限制

**英文原文**

Output-cell restrictions of a weighted product
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}

-- 读法：当 `(x, y) ∈ u` 成立时取 `w x y z`，否则取 `0`。
def mask (w : Fin i → Fin j → Fin k → F) (u : Finset (Pos i j))
    (x : Fin i) (y : Fin j) (z : Fin k) : F := if (x, y) ∈ u then w x y z else 0

-- 读法：`short` 的取值由 `min (min (Real.log i) (Real.log j)) (Real.log q / 2)` 给出。
/-- 面积为 `q`、能放进原尺寸规格且最接近正方形的矩形，其短边长度的对数。

英文原文：Logarithm of the short side of the most nearly square rectangle
of area `q` fitting in the original format.
-/
noncomputable def short (i j q : ℕ) : ℝ :=
  min (min (Real.log i) (Real.log j)) (Real.log q / 2)

-- 读法：`CellBound` 的结果类型为 `Prop`。
def CellBound (F : Type*) [Field F] : Prop :=
  ∀ i j k r : ℕ, 0 < i → 0 < j → 0 < k →
    ∀ (w : Fin i → Fin j → Fin k → F) (u : Finset (Pos i j)),
    u.Nonempty → (∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) → WeightedRankLE w r →
      Real.exp (exponent F (short i j u.card)
        (Real.log u.card - short i j u.card) (Real.log k)) ≤ r

-- 读法：`0 ≤ short i j q` 与 `short i j q ≤ Real.log q` 同时成立。
theorem short_bounds {i j q : ℕ} (hi : 0 < i) (hj : 0 < j) (hq : 0 < q) :
    0 ≤ short i j q ∧ short i j q ≤ Real.log q := by
  have hlog {n : ℕ} (hn : 0 < n) : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  exact ⟨le_min (le_min (hlog hi) (hlog hj)) (by linarith [hlog hq]),
    (min_le_right _ _).trans (by linarith [hlog hq])⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
