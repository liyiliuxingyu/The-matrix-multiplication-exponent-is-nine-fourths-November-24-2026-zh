-- 本文件所属证明环节：把每条连线上的指标串拆成两段，证明张量幂的秩构成次乘性数列。对其对数使用 Fekete 引理，并单独处理出现零项的情况，得到正整数次秩根的极限等于其下确界。
import OAI.LinearAlgebra.SpectralBooks.Tensor
import Mathlib.Analysis.Subadditive

/-!
# 定义渐近张量秩的极限

拆分克罗内克幂可得到一个以自然数为值的次乘性秩序列。对其对数应用 Fekete 引理，即可将论文中的极限表示为各正整数幂次的秩开相应次方根后的下确界。

**英文原文**

The limit defining asymptotic tensor rank

Splitting Kronecker powers gives a submultiplicative sequence of natural
ranks. Applying Fekete's lemma to their logarithms identifies the manuscript's
limit with the infimum of the positive-index rank roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

-- 读法：`(fun n : ℕ => (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹))` 沿滤子 `atTop` 收敛到 `(⨅ n : ℕ, (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹))`。按 `∃ k, r k = 0` 成立与否分情况。
/-- 对取自然数值的次乘法序列，所有正指标项的相应次方根的下确界就是这些根的极限。存在零项时结论仍成立。

英文原文：The positive-index root infimum is the limit for a natural-valued
submultiplicative sequence, including sequences with a zero term.
-/
theorem tendsto_root_of_submultiplicative (r : ℕ → ℕ)
    (hmul : ∀ m n, r (m + n) ≤ r m * r n) :
    Tendsto (fun n : ℕ => (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)) atTop
      (𝓝 (⨅ n : ℕ, (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹))) := by
  let root (n : ℕ) := (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)
  change Tendsto root atTop (𝓝 (⨅ n, root n))
  have hnonneg n : 0 ≤ root n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbdd : BddBelow (Set.range root) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  by_cases hz : ∃ k, r k = 0
  -- 推导：从 `hz` 中取出 `k, hk`。
  · obtain ⟨k, hk⟩ := hz
    have heq (n : ℕ) (hn : k ≤ n) : root n = 0 := by
      have h := hmul k (n + 1 - k)
      rw [show k + (n + 1 - k) = n + 1 by omega, hk, zero_mul, Nat.le_zero] at h
      simp [root, h, Real.zero_rpow (by positivity : ((n + 1 : ℝ)⁻¹) ≠ 0)]
    have hinf : (⨅ n, root n) = 0 :=
      le_antisymm ((ciInf_le hbdd k).trans_eq (heq k le_rfl)) (le_ciInf hnonneg)
    rw [hinf]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨k, fun n hn => (heq n hn).symm⟩)
  · push Not at hz
    have hpos (n : ℕ) : (0 : ℝ) < r n := by exact_mod_cast Nat.pos_of_ne_zero (hz n)
    let u (n : ℕ) := Real.log (r n)
    have hsub : Subadditive u := by
      intro m n
      dsimp [u]
      rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
      apply Real.log_le_log (hpos _)
      exact_mod_cast hmul m n
    -- 推导：记下中间结论 `hu`：`BddBelow (Set.range fun n : ℕ => u n / n)`。
    have hu : BddBelow (Set.range fun n : ℕ => u n / n) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero (hz n))) (Nat.cast_nonneg _)
    have hroot n : root n = Real.exp (u (n + 1) / (n + 1)) := by
      dsimp only [root]
      rw [Real.rpow_def_of_pos (hpos _)]
      rfl
    have hlim : Tendsto root atTop (𝓝 (Real.exp hsub.lim)) := by
      have h := (Real.continuous_exp.continuousAt.tendsto.comp
        ((hsub.tendsto_lim hu).comp (tendsto_add_atTop_nat 1)))
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ← hroot] using h
    -- 推导：记下中间结论 `hinf`：`(⨅ n, root n) = Real.exp hsub.lim`。
    have hinf : (⨅ n, root n) = Real.exp hsub.lim := by
      refine le_antisymm (ge_of_tendsto' hlim (ciInf_le hbdd)) (le_ciInf fun n => ?_)
      rw [hroot, Real.exp_le_exp]
      simpa only [Nat.cast_succ] using
        hsub.lim_le_div hu (Nat.succ_ne_zero n)
    rwa [hinf]

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

-- 读法：`splitPowerWord` 的取值由 `(x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)` 给出。
private def splitPowerWord {A : Type*} (m n : ℕ) (x : Fin (m + n) → A) :
    (Fin m → A) × (Fin n → A) :=
  (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)

-- 读法：`tensorRank (Tensor.power T (m + n))` 不超过 `tensorRank (Tensor.power T m) * tensorRank (Tensor.power T n)`。这里调用 `tensorRank_le_of_rankAtMost`。
/-- 将各位置上的词拆成前缀和后缀，即可证明克罗内克幂的秩具有次乘性。

英文原文：Splitting each site's words into a prefix and suffix shows that the
rank of Kronecker powers is submultiplicative.
-/
theorem tensorRank_power_add_le (T : Tensor F X Y Z) (m n : ℕ) :
    tensorRank (Tensor.power T (m + n)) ≤
      tensorRank (Tensor.power T m) * tensorRank (Tensor.power T n) := by
  have h := ((rankAtMost_tensorRank (Tensor.power T m)).product
    (rankAtMost_tensorRank (Tensor.power T n))).pullback
    (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
  apply tensorRank_le_of_rankAtMost
  have heq : Tensor.power T (m + n) = Tensor.pullback
      (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
      (Tensor.product (Tensor.power T m) (Tensor.power T n)) := by
    funext x y z
    exact Fin.prod_univ_add (fun i => T (x i) (y i) (z i))
  rw [heq]
  exact h

-- 读法：`(fun n : ℕ => (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹))` 沿滤子 `atTop` 收敛到 `(asymptoticRank T)`。这里调用 `tendsto_add_atTop_iff_nat`。
/-- 张量幂的秩的相应次方根收敛到渐近秩。

英文原文：The tensor-power rank roots converge to asymptotic rank.
-/
theorem tendsto_tensorRank_power_root (T : Tensor F X Y Z) :
    Tendsto (fun n : ℕ => (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 (asymptoticRank T)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, asymptoticRank] using
    tendsto_root_of_submultiplicative (fun n => tensorRank (Tensor.power T n))
      (tensorRank_power_add_le T)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
