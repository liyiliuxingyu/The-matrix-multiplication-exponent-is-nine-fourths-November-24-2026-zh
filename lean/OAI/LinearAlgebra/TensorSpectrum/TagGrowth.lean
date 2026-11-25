-- 本文件所属证明环节：证明若每个幂次的指数型比较只多出固定多项式因子，则较大的指数底数不能被该因子抵消。对张量幂取极限时可据此移除多项式开销。
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 从张量幂不等式中消去多项式开销

固定的多项式因子无法弥补指数底数的严格下降。开销的指数可以是任意固定的非负实数。这是对有限字作标签分解后所用的标量极限步骤。

**英文原文**

Removing polynomial overhead from tensor-power inequalities

A fixed polynomial factor cannot compensate for a strictly smaller exponential
base. The exponent of the overhead may be any fixed nonnegative real number.
This is the scalar limit step used after the finite-word tag decomposition.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Filter Asymptotics

-- 读法：`B` 不超过 `A`。
/-- 若不等式对所有正次数张量幂都成立，就可消去固定的实多项式开销。指数项的底数为零时也适用。

英文原文：Remove a fixed real polynomial overhead from an inequality valid for every
positive tensor power. This statement includes zero exponential bases.
-/
theorem le_of_pow_le_polynomial_mul_pow
    (A B C q : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hC : 0 < C) (_hq : 0 ≤ q)
    (h : ∀ N : ℕ, 1 ≤ N →
      B ^ N ≤ C * ((N : ℝ) + 1) ^ q * A ^ N) : B ≤ A := by
  by_contra hnot
  have hAB : A < B := lt_of_not_ge hnot
  have hBpos : 0 < B := hA.trans_lt hAB
  obtain ⟨k, hqk⟩ := exists_nat_ge q
  have hnorm : ‖A‖ < B := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hA] using hAB
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖(C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N)‖ ≤
        (1 / 2 : ℝ) * ‖B ^ N‖ :=
    ((isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hnorm).const_mul_left
      (C * (2 : ℝ) ^ k)).def (by norm_num)
  -- 推导：从 `((eventually_ge_atTop (1 : ℕ)).and hsmall).exists` 中取出 `N, hN, hsmallN`。
  obtain ⟨N, hN, hsmallN⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpoly : ((N : ℝ) + 1) ^ q ≤ (2 : ℝ) ^ k * (N : ℝ) ^ k := by
    calc
      ((N : ℝ) + 1) ^ q ≤ ((N : ℝ) + 1) ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hqk
      _ = ((N : ℝ) + 1) ^ k := Real.rpow_natCast _ _
      _ ≤ (2 * (N : ℝ)) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = (2 : ℝ) ^ k * (N : ℝ) ^ k := mul_pow _ _ _
  -- 推导：记下中间结论 `hlarge`：`B ^ N ≤ (C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N)`。
  have hlarge : B ^ N ≤ (C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N) := by
    calc
      B ^ N ≤ C * ((N : ℝ) + 1) ^ q * A ^ N := h N hN
      _ ≤ C * ((2 : ℝ) ^ k * (N : ℝ) ^ k) * A ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC.le)
          (pow_nonneg hA N)
      _ = (C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N) := by ring
  have hnonneg : 0 ≤ (C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N) := by
    positivity
  have hsmall' : (C * (2 : ℝ) ^ k) * ((N : ℝ) ^ k * A ^ N) ≤
      (1 / 2 : ℝ) * B ^ N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (pow_nonneg hBpos.le N)] using hsmallN
  -- 推导：记下中间结论 `hBN`：`0 < B ^ N`。
  have hBN : 0 < B ^ N := pow_pos hBpos N
  linarith

end OAI.LinearAlgebra.TensorSpectrum
