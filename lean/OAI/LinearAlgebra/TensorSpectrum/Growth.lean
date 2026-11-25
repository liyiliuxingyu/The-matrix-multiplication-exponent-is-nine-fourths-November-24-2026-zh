-- 本文件所属证明环节：引入从下标零开始的辅助增长因子，对其递推式取三次幂。将这一标量估计代入两个对角不等式，得到每个正整数 a 的下界 a⁴ ≤ D(a)³。
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 由对角不等式推导精确的标量增长率

辅助数列从零开始编号：`growthFactor n` 对应论文中的 `G_(n+1)`。对递推式取三次幂即得精确估计 `n + 1 ≤ G_(n+1)^3`，本环节因而无须对数渐近估计。本模块仅证明两个对角不等式的标量推论；张量特征标能否给出这两个不等式，既不是此处的假设，也不是此处的结论。

**英文原文**

Exact scalar growth from the diagonal inequalities

The auxiliary sequence is indexed from zero: `growthFactor n` is the paper's
`G_(n+1)`.  Cubing its recurrence gives the exact estimate `n + 1 ≤ G_(n+1)^3`.
Thus no logarithmic asymptotic estimate is needed for this component.

This module proves only the scalar consequence of the two diagonal inequalities.
It does not assume or assert that a tensor character supplies those inequalities.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

-- 读法：逐一匹配以下输入模式：`0`、`n + 1`。
noncomputable def growthFactor : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 + 1 / (3 * ((n : ℝ) + 1))) * growthFactor n

-- 读法：`0` 严格小于 `growthFactor n`。对 `n` 作归纳。
theorem growthFactor_pos (n : ℕ) : 0 < growthFactor n := by
  induction n with
  | zero => norm_num [growthFactor]
  | succ n ih =>
      rw [growthFactor]
      positivity

-- 读法：`(n : ℝ) + 1` 不超过 `growthFactor n ^ 3`。对 `n` 作归纳。
theorem growthFactor_cube (n : ℕ) : (n : ℝ) + 1 ≤ growthFactor n ^ 3 := by
  induction n with
  | zero => norm_num [growthFactor]
  | succ n ih =>
      let a : ℝ := (n : ℝ) + 1
      let u : ℝ := 1 / (3 * a)
      have ha : 0 < a := by dsimp [a]; positivity
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have hau : 3 * a * u = 1 := by
        dsimp [u]
        field_simp
      -- 推导：记下中间结论 `hstep`：`a + 1 ≤ (1 + u) ^ 3 * a`。
      have hstep : a + 1 ≤ (1 + u) ^ 3 * a := by
        have h₂ : 0 ≤ a * u ^ 2 := mul_nonneg ha.le (sq_nonneg u)
        have h₃ : 0 ≤ a * u ^ 3 := mul_nonneg ha.le (pow_nonneg hu 3)
        nlinarith
      have ih' : a ≤ growthFactor n ^ 3 := ih
      have hfactor : 0 ≤ (1 + u) ^ 3 := by positivity
      have hmul := mul_le_mul_of_nonneg_left ih' hfactor
      change ((n + 1 : ℕ) : ℝ) + 1 ≤
        ((1 + 1 / (3 * ((n : ℝ) + 1))) * growthFactor n) ^ 3
      rw [mul_pow]
      push_cast
      exact hstep.trans hmul

-- 读法：`growthFactor n ≤ g (n + 1)` 与 `((3 * ((n : ℝ) + 1) - 1) / 2) * growthFactor n ≤ D (n + 1)` 同时成立。对 `n` 作归纳。
theorem diagonal_lower_bounds
    (D g : ℕ → ℝ)
    (hD : D 1 = 1) (hg : g 1 = 1)
    (hupper : ∀ a : ℕ, 1 ≤ a →
      D a ≤ ((3 * (a : ℝ) - 1) / 2) * g a)
    (hstep : ∀ a : ℕ, 1 ≤ a →
      D a + g a + g (a + 1) ≤ D (a + 1))
    (n : ℕ) :
    growthFactor n ≤ g (n + 1) ∧
      ((3 * ((n : ℝ) + 1) - 1) / 2) * growthFactor n ≤ D (n + 1) := by
  induction n with
  | zero => norm_num [growthFactor, hD, hg]
  | succ n ih =>
      let a : ℝ := (n : ℝ) + 1
      let u : ℝ := 1 / (3 * a)
      let G : ℝ := growthFactor n
      -- 推导：记下中间结论 `ha`：`0 < a`。
      have ha : 0 < a := by dsimp [a]; positivity
      have hden : 3 * a ≠ 0 := ne_of_gt (by positivity)
      have hupper' := hupper (n + 1 + 1) (by omega)
      have hstep' := hstep (n + 1) (by omega)
      have hgprev : G ≤ g (n + 1) := ih.1
      have hDprev : ((3 * a - 1) / 2) * G ≤ D (n + 1) := ih.2
      have hupper'' : D (n + 1 + 1) ≤
          ((3 * (a + 1) - 1) / 2) * g (n + 1 + 1) := by
        simpa [a, Nat.cast_add, Nat.cast_one] using hupper'
      have hidentity : 3 * a * ((1 + u) * G) = (3 * a + 1) * G := by
        dsimp [u]
        field_simp
      -- 推导：记下中间结论 `hgnext`：`(1 + u) * G ≤ g (n + 1 + 1)`。
      have hgnext : (1 + u) * G ≤ g (n + 1 + 1) := by
        apply (mul_le_mul_iff_right₀ (show 0 < 3 * a by positivity)).mp
        rw [hidentity]
        nlinarith [hupper'', hstep', hgprev, hDprev]
      have hDidentity :
          ((3 * (a + 1) - 1) / 2) * ((1 + u) * G) =
            ((3 * a - 1) / 2) * G + G + (1 + u) * G := by
        dsimp [u]
        field_simp; ring
      have hDnext : ((3 * (a + 1) - 1) / 2) * ((1 + u) * G) ≤
          D (n + 1 + 1) := by
        rw [hDidentity]
        exact (add_le_add (add_le_add hDprev hgprev) hgnext).trans hstep'
      constructor
      · simpa [growthFactor, a, u, G] using hgnext
      · simpa [growthFactor, a, u, G, Nat.cast_add, Nat.cast_one] using hDnext

-- 读法：对每个 `a : ℕ`，由 `1 ≤ a` 推出 `(a : ℝ) ^ 4 ≤ (D a) ^ 3`。
theorem diagonalCubicGrowth
    (D g : ℕ → ℝ)
    (hD : D 1 = 1) (hg : g 1 = 1)
    (_hgnonneg : ∀ a : ℕ, 1 ≤ a → 0 ≤ g a)
    (hupper : ∀ a : ℕ, 1 ≤ a →
      D a ≤ ((3 * (a : ℝ) - 1) / 2) * g a)
    (hstep : ∀ a : ℕ, 1 ≤ a →
      D a + g a + g (a + 1) ≤ D (a + 1)) :
    ∀ a : ℕ, 1 ≤ a → (a : ℝ) ^ 4 ≤ (D a) ^ 3 := by
  intro a ha
  -- 推导：从 `Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)` 中取出 `n, rfl`。
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hlow := (diagonal_lower_bounds D g hD hg hupper hstep n).2
  have hG : 0 ≤ growthFactor n := (growthFactor_pos n).le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef : (n : ℝ) + 1 ≤ (3 * ((n : ℝ) + 1) - 1) / 2 := by
    linarith
  have hprod : ((n : ℝ) + 1) * growthFactor n ≤ D (n + 1) :=
    (mul_le_mul_of_nonneg_right hcoef hG).trans hlow
  have hprodnonneg : 0 ≤ ((n : ℝ) + 1) * growthFactor n := by positivity
  have hcube := pow_le_pow_left₀ hprodnonneg hprod 3
  have hGc := growthFactor_cube n
  have hmult := mul_le_mul_of_nonneg_left hGc
    (show 0 ≤ ((n : ℝ) + 1) ^ 3 by positivity)
  push_cast
  calc
    ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * growthFactor n ^ 3 := hmult
    _ = (((n : ℝ) + 1) * growthFactor n) ^ 3 := (mul_pow _ _ _).symm
    _ ≤ (D (n + 1)) ^ 3 := hcube

end OAI.LinearAlgebra.TensorSpectrum
