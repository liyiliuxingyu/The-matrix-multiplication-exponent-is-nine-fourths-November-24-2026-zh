-- 本文件所属证明环节：把秩阈值和严格的复杂度改进专化到素数域，使任意域上的指数问题可由素数域估计控制。
import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# 化归到素域

每次只需排除一个有限系数方程组。检验阈值时只需整数运算。

**英文原文**

Reduction to prime fields

It suffices to rule out one finite system of coefficient equations at
a time. The threshold can be tested with integer arithmetic alone.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：存在 `(p : ℕ) (_ : Fact p.Prime)`，`omega (ZMod p)` 严格小于 `s`。
theorem prime_specialization {F : Type*} [Field F] {s : ℝ} (h : omega F < s) :
    ∃ (p : ℕ) (_ : Fact p.Prime), omega (ZMod p) < s := by
  obtain ⟨k, _, _, hk⟩ := finite_specialization h
  let p := ringChar k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let : Algebra (ZMod p) k := ZMod.algebra k p
  exact ⟨p, inferInstance, (omega_extension (ZMod p) k) ▸ hk⟩

-- 读法：`omega F` 不超过 `s`。
/-- 将对小域成立的上界提升到任意类型宇宙。

英文原文：Lifting the upper bound from small fields to all universes.
-/
theorem upper_of_small {s : ℝ} (h : ∀ (k : Type) [Field k], omega k ≤ s)
    (F : Type*) [Field F] : omega F ≤ s := by
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    let : Algebra (ZMod p) F := ZMod.algebra F p
    rw [omega_extension (ZMod p) F]
    exact h _
  · let : CharZero F := CharP.charP_to_charZero F
    rw [omega_extension ℚ F]
    exact h _

-- 读法：`(r : ℝ) < (n : ℝ) ^ (9 / 4 : ℝ)` 与 `r ^ 4 < n ^ 9` 等价。
theorem rank_threshold (n r : ℕ) :
    (r : ℝ) < (n : ℝ) ^ (9 / 4 : ℝ) ↔ r ^ 4 < n ^ 9 := by
  have he : ((n : ℝ) ^ (9 / 4 : ℝ)) ^ (4 : ℕ) = (n : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  rw [← pow_lt_pow_iff_left₀ (Nat.cast_nonneg (α := ℝ) r)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (9 / 4)) (by decide : (4 : ℕ) ≠ 0), he]
  norm_cast

end OAI.LinearAlgebra.MatrixExponent
