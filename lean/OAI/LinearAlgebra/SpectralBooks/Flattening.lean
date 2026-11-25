-- 本文件所属证明环节：矩阵乘法张量的三种展平都含有相应大小的恒等子矩阵，因而任一张量秩分解至少有三种局部基数中最大的那么多项。同样论证应用于张量幂并取根，得到有限矩形规格的渐近秩下界。
import OAI.LinearAlgebra.SpectralBooks.Tensor
import OAI.LinearAlgebra.SpectralBooks.MatrixMinors

/-!
# 固定矩形尺寸下由展平得到的下界

每种展平都含有一个单位子矩阵。将这一论证应用于各次幂，此时连线指标为元组，再开相应次数的根，就能保留下界。

**英文原文**

Flattening lower bounds in finite rectangular formats

Each flattening contains an identity minor. Applying the argument to powers,
whose wire indices are tuples, preserves the lower bound on taking roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open MatrixMultiplication.Foundation

section Finite

variable {F A B C : Type*} [Field F] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

omit [Fintype B] in
-- 读法：`Fintype.card C * Fintype.card A` 不超过 `r`。这里调用 `h.card_le_of_identity`。
private theorem card_last_le_rank {r : ℕ} (b : B)
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A B C) r) :
    Fintype.card C * Fintype.card A ≤ r := by
  rw [← Fintype.card_prod]
  apply h.card_le_of_identity (fun i : C × A => (i.2, b)) (fun i => (b, i.1)) id
  intro i j
  have hh := congrFun (congrFun (matrixMinor₃ (K := F) (A := A) (C := C) b) j) i
  simpa [Matrix.one_apply, eq_comm] using hh

-- 读法：要证明的命题是 `max (Fintype.card A * Fintype.card B) (max (Fintype.card B * Fintype.card C) (Fintype.card C * Fintype.card A)) ≤ r`。这里调用 `max_le`。
/-- 秩分解给出三个局部基的基数上界。

英文原文：A rank decomposition bounds the cardinalities of all three local bases.
-/
theorem matrixCoefficients_flattenings {r : ℕ} (a : A) (b : B) (c : C)
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A B C) r) :
    max (Fintype.card A * Fintype.card B)
      (max (Fintype.card B * Fintype.card C) (Fintype.card C * Fintype.card A)) ≤ r := by
  exact max_le (card_last_le_rank c (Tensor.matrixCoefficients_cyclic_rank h))
    (max_le (card_last_le_rank a
      (Tensor.matrixCoefficients_cyclic_rank (Tensor.matrixCoefficients_cyclic_rank h)))
      (card_last_le_rank b h))

end Finite

variable (F : Type*) [Field F] {n12 n23 n31 : ℕ}

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 用连线指标的元组重新标记张量幂的三个位置，就得到单个更大规格的矩阵乘法张量。

英文原文：Reindexing the three sites of a tensor power by tuples of wire indices
turns it into a single larger matrix multiplication tensor.
-/
theorem matrix_power_rankAtMost (s : ℕ) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F)
      (Fin s → Fin n31) (Fin s → Fin n12) (Fin s → Fin n23))
      (tensorRank (Tensor.power (matrixTensor F n12 n23 n31) s)) := by
  have h := (rankAtMost_tensorRank (Tensor.power (matrixTensor F n12 n23 n31) s)).pullback
    (fun x : (Fin s → Fin n31) × (Fin s → Fin n12) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin s → Fin n12) × (Fin s → Fin n23) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin s → Fin n23) × (Fin s → Fin n31) => fun i => (z.1 i, z.2 i))
  convert h using 1
  funext x y z
  exact (Tensor.matrixCoefficients_power s x y z).symm

-- 读法：`max (n31 * n12) (max (n12 * n23) (n23 * n31))` 不超过 `tensorRank (matrixTensor F n12 n23 n31)`。这里调用 `matrixCoefficients_flattenings`。
/-- 最大局部维数给出普通秩的下界。

英文原文：The largest local dimension bounds ordinary rank from below.
-/
theorem matrix_flattening_le_tensorRank (h12 : 0 < n12) (h23 : 0 < n23) (h31 : 0 < n31) :
    max (n31 * n12) (max (n12 * n23) (n23 * n31)) ≤
      tensorRank (matrixTensor F n12 n23 n31) := by
  simpa using matrixCoefficients_flattenings
    (F := F) (⟨0, h31⟩ : Fin n31) (⟨0, h12⟩ : Fin n12) (⟨0, h23⟩ : Fin n23)
    (rankAtMost_tensorRank (matrixTensor F n12 n23 n31))

-- 读法：`(max (n31 * n12) (max (n12 * n23) (n23 * n31)) : ℕ)` 不超过 `asymptoticRank (matrixTensor F n12 n23 n31)`。这里调用 `le_ciInf`。
/-- 在任意域上，最大局部维数都是渐近秩的下界。

英文原文：The largest local dimension bounds asymptotic rank from below over every field.
-/
theorem matrix_flattening_le_asymptoticRank (h12 : 0 < n12) (h23 : 0 < n23) (h31 : 0 < n31) :
    (max (n31 * n12) (max (n12 * n23) (n23 * n31)) : ℕ) ≤
      asymptoticRank (matrixTensor F n12 n23 n31) := by
  apply le_ciInf
  intro s
  have h := matrixCoefficients_flattenings
    (fun _ => (⟨0, h31⟩ : Fin n31)) (fun _ => (⟨0, h12⟩ : Fin n12))
    (fun _ => (⟨0, h23⟩ : Fin n23)) (matrix_power_rankAtMost F (s + 1))
  simp only [Fintype.card_pi_const, Fintype.card_fin, ← mul_pow] at h
  apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (show 0 < (s : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast]
  have hm (a b : ℕ) : max a b ^ (s+1) = max (a ^ (s+1)) (b ^ (s+1)) :=
    (pow_left_mono (n := s+1)).map_max
  have hh : max (n31 * n12) (max (n12 * n23) (n23 * n31)) ^ (s+1) ≤
      tensorRank (Tensor.power (matrixTensor F n12 n23 n31) (s+1)) := by
    simpa only [hm] using h
  exact_mod_cast hh

end

end

end SpectralBooks
end LinearAlgebra
end OAI
