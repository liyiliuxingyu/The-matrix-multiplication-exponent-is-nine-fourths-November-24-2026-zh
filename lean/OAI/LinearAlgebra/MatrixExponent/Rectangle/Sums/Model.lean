-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.WeightedModel

/-!
# 各自独立加权的乘积之和

站址始终按输出、左输入、右输入的次序排列。谱张量半环以直和为加法、张量积为乘法。

**英文原文**

A sum of independently weighted products

The site order throughout is output, left input, right input.
The spectral tensor semiring uses direct sum and tensor product.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sums
open Spectral Filter

-- 读法：结构的字段包括 `i`、`j`、`k`、`hi`、`hj`。
structure Shape where
  i : ℕ
  j : ℕ
  k : ℕ
  hi : 0 < i
  hj : 0 < j
  hk : 0 < k

-- 读法：在后续公式中，`Weights` 是 `Fin v.i → Fin v.j → Fin v.k → F` 的缩写。
abbrev Weights (F : Type) (v : Shape) := Fin v.i → Fin v.j → Fin v.k → F
-- 读法：在后续公式中，`Three` 是 `Tensor F (Fin 3)` 的缩写。
abbrev Three (F : Type) [Field F] := Tensor F (Fin 3)

variable {F : Type} [Field F] {n : ℕ}

-- 读法：`rank` 的取值由 `sInf {r : ℕ | A ≤ (r : Three F)}` 给出。
def rank (A : Three F) : ℕ := sInf {r : ℕ | A ≤ (r : Three F)}

-- 读法：`asymptotic` 的取值由 `limUnder atTop fun t : ℕ => (rank (A ^ t) : ℝ) ^ (t : ℝ)⁻¹` 给出。
def asymptotic (A : Three F) : ℝ :=
  limUnder atTop fun t : ℕ => (rank (A ^ t) : ℝ) ^ (t : ℝ)⁻¹

-- 读法：`blocks` 的取值由 `∑ t, weightedTensor (w t)` 给出。
def blocks (v : Fin n → Shape) (w : ∀ t, Weights F (v t)) : Three F :=
  ∑ t, weightedTensor (w t)

-- 读法：输入 `_ _ _ _` 时返回 `1`。
def unweighted (F : Type) [Field F] (v : Fin n → Shape) : ∀ t, Weights F (v t) :=
  fun _ _ _ _ => 1

-- 读法：`entropy` 的取值由 `-(∑ i, p i * Real.log (p i))` 给出。
def entropy (p : Fin n → ℝ) := -(∑ i, p i * Real.log (p i))

-- 读法：`mean` 的取值由 `∑ i, p i * Real.log (q (v i))` 给出。
def mean (v : Fin n → Shape) (p : Fin n → ℝ) (q : Shape → ℕ) :=
  ∑ i, p i * Real.log (q (v i))

-- 读法：`objective` 的取值由 `entropy p + L (mean v p Shape.i) (mean v p Shape.j) (mean v p Shape.k)` 给出。
def objective (L : ℝ → ℝ → ℝ → ℝ) (v : Fin n → Shape) (p : Fin n → ℝ) :=
  entropy p + L (mean v p Shape.i) (mean v p Shape.j) (mean v p Shape.k)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sums
