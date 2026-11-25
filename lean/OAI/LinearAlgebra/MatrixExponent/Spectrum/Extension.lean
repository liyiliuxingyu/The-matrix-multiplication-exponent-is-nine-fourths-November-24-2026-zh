-- 本文件所属证明环节：研究满足乘法性、可加性及给定不等式的谱点，借助紧致性与延拓把逐谱点的严格比较转化为一致的张量比较。
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison


/-!
# 谱点的同时延拓

严格比较可将目标谱上的不等式转移回来。对像外的一点，可用其中一条不等式将其分离：先将其有限多个坐标取整，再在距离平方式中通分，并把负项移至另一侧。

**英文原文**

Simultaneous extension of spectral points

Strict comparison transfers inequalities from the spectrum of the target.
A point outside its image can be separated by one such inequality: round
its finitely many coordinates, then clear denominators in the squared
distance and move negative terms to the other side.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

open scoped NNReal

-- 读法：`x` 不超过 `y`。按 `y = 0` 成立与否分情况。
theorem le_of_powers_le {x y : ℝ≥0} {C : ℕ}
    (h : ∀ r : ℕ, x ^ r ≤ (C : ℝ≥0) * y ^ r) : x ≤ y := by
  by_cases hy : y = 0
  · simpa [hy] using h 1
  by_contra! hxy
  have hy' : 0 < y := pos_iff_ne_zero.mpr hy
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (C : ℝ≥0) ((one_lt_div hy').mpr hxy)
  rw [div_pow, lt_div_iff₀ (pow_pos hy' _)] at hr
  exact hr.not_ge (h r)

variable {S T : Type*} [CommSemiring S] [CommSemiring T] [PartialOrder T]

-- 读法：存在 `x y : S`，`f y` 小于 `f x ∧ ∀ g : S →+* ℝ≥0, ε ≤ ∑ a ∈ U, ((g a : ℝ) - f a) ^ 2 → g x < g y`。
/-- 单独一对有序半环元素即可检出有限个观测给出的严格正的平方距离间隔。

英文原文：A single ordered pair of semiring elements distinguishes a finite
strictly positive squared-distance gap.
-/
private theorem separate_by_elements (f : S →+* ℝ≥0) (U : Finset S) {ε : ℝ} (he : 0 < ε) :
    ∃ x y : S, f y < f x ∧ ∀ g : S →+* ℝ≥0,
      ε ≤ ∑ a ∈ U, ((g a : ℝ) - f a) ^ 2 → g x < g y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((4 * (U.card : ℝ) + 2) / ε))
  have hn1 := (le_max_left _ _).trans_lt hn
  have hn2 := (div_lt_iff₀ he).mp ((le_max_right _ _).trans_lt hn)
  have hn3 : 4 * (U.card : ℝ) + 2 < (n : ℝ) ^ 2 * ε :=
    hn2.trans_le (mul_le_mul_of_nonneg_right (by nlinarith) he.le)
  let p (a : S) := ⌊(n : ℝ) * (f a : ℝ)⌋₊
  let E (g : S →+* ℝ≥0) := ∑ a ∈ U, ((n : ℝ) * (g a : ℝ) - p a) ^ 2
  -- 推导：记下中间结论 `small`：`E f ≤ U.card`。
  have small : E f ≤ U.card := by
    calc
      E f ≤ ∑ _ ∈ U, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        have hl : (p a : ℝ) ≤ (n : ℝ) * f a := Nat.floor_le (by positivity)
        have hr : (n : ℝ) * f a < (p a : ℝ) + 1 := Nat.lt_floor_add_one _
        nlinarith
      _ = U.card := by simp
  let x := (U.card : S) + 1 + ∑ a ∈ U, 2 * (p a : S) * (n : S) * a
  let y := ∑ a ∈ U, (((n : S) * a) ^ 2 + (p a : S) ^ 2)
  have price (g : S →+* ℝ≥0) : (g y : ℝ) - g x = E g - (U.card + 1) := by
    simp only [x, y, E, map_add, map_sum, map_one, map_mul, map_natCast, map_pow, map_ofNat,
      NNReal.coe_add, NNReal.coe_sum, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_pow, NNReal.coe_ofNat]
    rw [sub_add_eq_sub_sub_swap, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  refine ⟨x, y, NNReal.coe_lt_coe.mp (by linarith [price f]), ?_⟩
  intro g hg
  -- 推导：记下中间结论 `large`：`(n : ℝ) ^ 2 * ε ≤ 2 * E g + 2 * E f`。
  have large : (n : ℝ) ^ 2 * ε ≤ 2 * E g + 2 * E f := by
    refine (mul_le_mul_of_nonneg_left hg (sq_nonneg _)).trans ?_
    simp only [E, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    nlinarith only [sq_nonneg ((n : ℝ) * ((g a : ℝ) + f a) - 2 * (p a : ℝ))]
  exact NNReal.coe_lt_coe.mp (by linarith [price g])

-- 读法：存在 `g : T →+* ℝ≥0`，`Monotone g` 与 `∀ a, g (i a) = f a` 同时成立。
/-- 只需给定特征标保持在目标半环中作出的比较。延拓在所有元素上同时与原特征标一致。

英文原文：It suffices that the given character respects comparisons made in the
target semiring. The extension agrees at every element simultaneously.
-/
theorem extension
    (hadd : ∀ a b c : T, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a) (hunit : ∀ a : T, a ≠ 0 → 1 ≤ a)
    (hbound : ∀ a : T, ∃ n : ℕ, a ≤ (n : T))
    (i : S →+* T) (f : S →+* ℝ≥0) (h : ∀ a b, i a ≤ i b → f a ≤ f b) :
    ∃ g : T →+* ℝ≥0, Monotone g ∧ ∀ a, g (i a) = f a := by
  by_contra hn
  obtain ⟨U, ε, he, hgap⟩ := separated hbound i f hn
  obtain ⟨x, y, hf, hg⟩ := separate_by_elements f U he
  have hy : i (y + 1) ≠ 0 := by
    intro e
    have := h (y + 1) 0 (by simp [e])
    simp at this
  have hl (g : T →+* ℝ≥0) (hm : Monotone g) : g (i (x + 1)) < g (i (y + 1)) := by
    have := hg (g.comp i) (hgap g hm)
    simpa only [map_add, map_one, add_lt_add_iff_right, RingHom.comp_apply] using this
  -- 推导：从 `strictComparison hadd hmul hzero hunit hbound hy hl` 中取出 `C, hC`。
  obtain ⟨C, hC⟩ := strictComparison hadd hmul hzero hunit hbound hy hl
  have hxy : f (x + 1) ≤ f (y + 1) := by
    apply le_of_powers_le (C := C)
    intro r
    simpa only [map_pow, map_mul, map_natCast] using
      h ((x + 1) ^ r) ((C : S) * (y + 1) ^ r) (by simpa only [map_pow, map_mul, map_natCast] using hC r)
  exact hf.not_ge (by simpa using hxy)

end OAI.LinearAlgebra.MatrixExponent.Spectrum
