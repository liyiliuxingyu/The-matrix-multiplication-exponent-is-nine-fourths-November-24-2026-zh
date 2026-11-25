-- 本文件所属证明环节：由半环上的序条件证明非零元素的状态值为正，因而归一化乘法有定义且把加性状态集映回自身；从所有映射的共同不动点读出乘法特征标。
import OAI.LinearAlgebra.TensorSpectrum.Additive.States
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective

/-!
# 归一化乘法保持态

这里的序假设正是具体的张量限制所具有的性质。特别地，分母为正由非零张量的下界推出，无须对候选特征标另加假设。

**英文原文**

State preservation by normalized multiplication

The order hypotheses here are the concrete tensor restriction properties. In
particular the lower bound on nonzero tensors proves the denominator is positive;
it is not a separate premise about a proposed character.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

-- 读法：`1` 不超过 `f z`。这里调用 `hf.2.2.2.1`。
theorem state_one_le {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 (hunit z hz)

-- 读法：`0` 严格小于 `f z`。使用 `lt_of_lt_of_le` 给出的结论。
theorem state_pos {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : 0 < f z :=
  lt_of_lt_of_le zero_lt_one (state_one_le hf hunit hz)

-- 读法：`projective z f` 属于 `stateSet T k`。这里调用 `div_le_div_of_nonneg_right`。
/-- 每个射影映射都保持定义状态的全部五个条件，包括针对每个张量的检测不等式。

英文原文：Every projective map preserves all five defining state conditions, including
the detecting inequalities for every tensor.
-/
theorem projective_mem_stateSet {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    {z : S} (hz : z ≠ 0) : projective z f ∈ stateSet T k := by
  have hpos : 0 < f z := state_pos hf hunit hz
  refine ⟨projective_zero z f hf.1, projective_one z f hpos.ne', ?_, ?_, ?_⟩
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 (hmul z hxy)) hpos.le
  · intro s
    change (k : ℝ) * (f (z * s) / f z) ≤ f (z * (T * s)) / f z
    rw [show z * (T * s) = T * (z * s) by ac_rfl, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf.2.2.2.2 (z * s)) hpos.le

-- 读法：要证明的命题是 `MapsTo (projective z) (stateSet T k) (stateSet T k)`。
theorem projective_mapsTo_stateSet (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    {z : S} (hz : z ≠ 0) :
    MapsTo (projective z) (stateSet T k) (stateSet T k) :=
  fun _ hf => projective_mem_stateSet hf hunit hmul hz

-- 读法：要证明的命题是 `ContinuousOn (projective z) (stateSet T k)`。使用 `continuousOn_projective` 给出的结论。
theorem projective_continuousOn_stateSet (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : ContinuousOn (projective z) (stateSet T k) :=
  continuousOn_projective z (stateSet T k) fun _ hf => (state_pos hf hunit hz).ne'

-- 读法：存在 `χ : S →+* ℝ`，`Monotone χ` 与 `(k : ℝ) ≤ χ T ∧ ∀ x, χ x = f x` 同时成立。按 `x = 0` 成立与否分情况。
/-- 实际状态映射的一个公共不动点给出单调半环特征；在单位元处应用检测不等式即可得到所需的值。

英文原文：A simultaneous fixed point of the actual state maps is a monotone semiring
character, and the detection inequality at the unit yields its required value.
-/
theorem character_of_common_fixedPoint (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (f : S → ℝ) (hf : f ∈ stateSet T k)
    (hfixed : ∀ z : S, z ≠ 0 → projective z f = f) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (k : ℝ) ≤ χ T ∧ ∀ x, χ x = f x := by
  have hmul : ∀ x y : S, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x = 0
    · simp [hx, hf.1]
    · exact (projective_fixed_iff x f (state_pos hf hunit hx).ne').mp (hfixed x hx) y
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := hf.1
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hmul }
  refine ⟨χ, hf.2.2.2.1, ?_, fun _ => rfl⟩
  change (k : ℝ) ≤ f T
  simpa only [mul_one, hf.2.1] using hf.2.2.2.2 1

end OAI.LinearAlgebra.TensorSpectrum
