-- 本文件所属证明环节：在底数 N＝2ᵏ 的各个尺度上应用有限尺度的高度不等式。由于连线维数向上取整，站点的对数负载只增不减；除以 k 后，多项式成本前面的常数产生的误差趋零，从而取得指数级的不等式及其下确界版本。
import OAI.LinearAlgebra.SpectralBooks.Rank
import OAI.LinearAlgebra.SpectralBooks.Scaling

/-!
# 从有限尺度的高度界推导算术指数

在基准大小 `2 ^ k` 处应用有限规模上界。对每个维数向上取整只会增大其对数负载。多项式成本界中的常数取对数后只贡献固定加项；由于不等式对每个二进尺度均成立，该加项在极限中消失。

**英文原文**

From finite height bounds to arithmetic exponents

Evaluate the finite bound at base sizes `2 ^ k`. Rounding each dimension
up only increases its logarithmic load. The logarithm of a constant in
a polynomial cost bound contributes a fixed additive term, which disappears
when the inequality holds at every dyadic scale.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

noncomputable section

-- 读法：`scaledLoads` 的取值由 `loads (Real.logb 2 (wireDimension N w12)) (Real.logb 2 (wireDimension N w23)) (Real.logb 2 (wireDimension N w31))` 给出。
/-- 基础规模为 `N` 时，由取整后的三个连线维数给出各位置的对数负载。

英文原文：Logarithmic site loads at the three rounded wire dimensions of base size `N`.
-/
def scaledLoads (N : ℕ) (w12 w23 w31 : ℝ) : Fin 3 → ℝ :=
  loads (Real.logb 2 (wireDimension N w12)) (Real.logb 2 (wireDimension N w23))
    (Real.logb 2 (wireDimension N w31))

-- 读法：`(k : ℝ) * loads w12 w23 w31 i` 不超过 `scaledLoads (2 ^ k) w12 w23 w31 i`。这里调用 `add_le_add`。
/-- 在二进尺度上，各负载均不小于对应实权重与尺度指数之积。

英文原文：The dyadic loads dominate the real weights multiplied by the scale exponent.
-/
theorem dyadic_load_le (k : ℕ) (w12 w23 w31 : ℝ) (i : Fin 3) :
    (k : ℝ) * loads w12 w23 w31 i ≤ scaledLoads (2 ^ k) w12 w23 w31 i := by
  fin_cases i <;> dsimp [scaledLoads, loads] <;> rw [mul_add] <;>
    exact add_le_add (dyadic_wireDimension_log_ge _ _) (dyadic_wireDimension_log_ge _ _)

-- 读法：`u` 不超过 `τ`。这里调用 `le_of_forall_pos_le_add`。
/-- 若在二进尺度上具有一致的多项式上界，则增长指数至少为该斜率，此结论与乘法常数无关。

英文原文：A uniform polynomial bound at dyadic scales forces the growth exponent
to dominate the slope, independently of the multiplicative constant.
-/
theorem le_of_dyadic_log_bound {u τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (k : ℝ) * u ≤ Real.logb 2 (C * ((2 ^ k : ℕ) : ℝ) ^ (τ + ε))) : u ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, hC, hk⟩ := h ε hε
  by_contra! hlt
  obtain ⟨k, hlarge⟩ := exists_lt_nsmul (sub_pos.mpr hlt) (Real.logb 2 C)
  rw [nsmul_eq_mul] at hlarge
  have hbound := hk k
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_mul hC.ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at hbound
  nlinarith only [hlarge, hbound]

-- 读法：要证明的命题是 `HeightTest (loads w12 w23 w31) τ`。这里调用 `div_le_iff₀`。
/-- 若有限规格高度检验的参数具有多项式上界，则指数负载满足相应检验，且可消去全部正松弛量。

英文原文：A polynomial upper bound on the finite height-test parameter implies
the corresponding test on exponent loads, with all positive slack removed.
-/
theorem heightTest_of_polynomial_bound {w12 w23 w31 τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      HeightTest (scaledLoads N w12 w23 w31) (Real.logb 2 (C * (N : ℝ) ^ (τ + ε)))) :
    HeightTest (loads w12 w23 w31) τ := by
  intro a ha
  let M := ∑ i, a i * loads w12 w23 w31 i
  let D := ∑ i, Real.sqrt (1 + a i ^ 2) - 1
  have hD : 0 < D := heightDenom_pos a
  change M ≤ τ * D
  apply (div_le_iff₀ hD).mp
  apply le_of_dyadic_log_bound
  intro ε hε
  -- 推导：从 `h ε hε` 中取出 `C, hC, hN`。
  obtain ⟨C, hC, hN⟩ := h ε hε
  refine ⟨C, hC, fun k => ?_⟩
  rw [← mul_div_assoc, div_le_iff₀ hD]
  have hstep : (k : ℝ) * M ≤ ∑ i, a i * scaledLoads (2 ^ k) w12 w23 w31 i := by
    dsimp only [M]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (dyadic_load_le k _ _ _ i) (ha i).le
  exact hstep.trans (hN (2 ^ k) (Nat.one_le_pow _ _ (by decide)) a ha)

-- 读法：要证明的命题是 `HeightTest m (sInf S)`。这里调用 `div_le_iff₀`。
/-- 对任意非空的可容许指数集取下确界后，高度检验仍成立。

英文原文：Height tests pass to the infimum of any nonempty set of admissible exponents.
-/
theorem heightTest_sInf {m : Fin 3 → ℝ} {S : Set ℝ} (hS : S.Nonempty)
    (h : ∀ τ ∈ S, HeightTest m τ) : HeightTest m (sInf S) := by
  intro a ha
  have hD := heightDenom_pos a
  apply (div_le_iff₀ hD).mp
  exact le_csInf hS fun τ hτ => (div_le_iff₀ hD).mpr (h τ hτ a ha)

end

end SpectralBooks
end LinearAlgebra
end OAI
