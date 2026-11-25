-- 本文件所属证明环节：为有限多个有理系数选择共同的正整数分母。清除分母后仍保持非负性，并将有理的线性等式和有限求和公式转为整数证书。
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# 消去有限生成有理锥中的分母

对任一有限有理系数向量，可以用同一个正整数消去所有分母。若原向量非负，所得整数向量也非负。最后两个引理说明有限线性恒等式在该构造下仍然成立。

**英文原文**

Clearing denominators in finite rational cones

A single positive natural number clears every denominator of a finite rational
coefficient vector. The resulting integer vector preserves nonnegativity. The
last two lemmas transport finite linear identities through this construction.
-/

namespace OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

open scoped BigOperators

-- 读法：存在 `m : ℕ`，由 `0 < m ∧ ∃ z : ι` 推出 `ℤ, (∀ i, (z i : ℚ) = (m : ℚ) * c i) ∧ (∀ i, 0 ≤ c i → 0 ≤ z i)`。
/-- 为有限有理向量取公共正分母，各坐标的符号均得到保留。乘积构造也涵盖空指标类型。

英文原文：A common positive denominator for a finite rational vector, with signs
preserved coordinatewise. The product construction includes the empty type.
-/
theorem exists_pos_nat_mul_eq_int {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : ι → ℤ,
      (∀ i, (z i : ℚ) = (m : ℚ) * c i) ∧
      (∀ i, 0 ≤ c i → 0 ≤ z i) := by
  classical
  let m : ℕ := ∏ i, (c i).den
  let z : ι → ℤ := fun i =>
    (∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) * (c i).num
  have hm : 0 < m := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (c i).den_pos.ne')
  refine ⟨m, hm, z, ?_, ?_⟩
  · intro i
    -- 推导：记下中间结论 `hprod`：`m = (∏ j ∈ Finset.univ.erase i, (c j).den) * (c i).den`。
    have hprod : m = (∏ j ∈ Finset.univ.erase i, (c j).den) * (c i).den :=
      (Finset.prod_erase_mul Finset.univ (fun j => (c j).den)
        (Finset.mem_univ i)).symm
    dsimp only [z]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hprod, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  · intro i hi
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Rat.num_nonneg.mpr hi)

-- 读法：存在 `m : ℕ`，由 `0 < m ∧ ∃ z : ι` 推出 `ℤ, (∀ i, 0 ≤ z i) ∧ (∀ i, (z i : ℚ) = (m : ℚ) * c i)`。
/-- 将非负有理系数向量乘以某个正整数，可得到非负整数系数向量。

英文原文：A nonnegative rational coefficient vector has a positive integral scaling
which is a nonnegative integer coefficient vector.
-/
theorem exists_nonneg_int_scaling {ι : Type*} [Fintype ι]
    (c : ι → ℚ) (hc : ∀ i, 0 ≤ c i) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : ι → ℤ,
      (∀ i, 0 ≤ z i) ∧ (∀ i, (z i : ℚ) = (m : ℚ) * c i) := by
  obtain ⟨m, hm, z, hz, hnonneg⟩ := exists_pos_nat_mul_eq_int c
  exact ⟨m, hm, z, fun i => hnonneg i (hc i), hz⟩

-- 读法：`((∑ i, z i * v i : ℤ) : ℚ)` 等于 `(m : ℚ) * ∑ i, c i * (v i : ℚ)`。这里调用 `Finset.sum_congr`。
/-- 有理系数按比例缩放时，每个有限整数线性形式的值按同一比例缩放。

英文原文：Scaling rational coefficients scales each finite integer linear form.
-/
theorem cast_sum_mul_of_cleared {ι : Type*} [Fintype ι]
    {c : ι → ℚ} {z : ι → ℤ} {m : ℕ}
    (hz : ∀ i, (z i : ℚ) = (m : ℚ) * c i) (v : ι → ℤ) :
    ((∑ i, z i * v i : ℤ) : ℚ) = (m : ℚ) * ∑ i, c i * (v i : ℚ) := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, hz i, mul_assoc]

-- 读法：结论为 `∑ i, z i * v i = (m : ℤ) * b`。这里调用 `Rat.intCast_injective`。
/-- 清除系数的分母后，有理线性恒等式就成为整数线性恒等式。

英文原文：A rational linear identity becomes an integer linear identity once its
coefficients have been cleared.
-/
theorem sum_mul_eq_nat_mul_of_cleared {ι : Type*} [Fintype ι]
    {c : ι → ℚ} {z : ι → ℤ} {m : ℕ}
    (hz : ∀ i, (z i : ℚ) = (m : ℚ) * c i) (v : ι → ℤ) (b : ℤ)
    (h : ∑ i, c i * (v i : ℚ) = (b : ℚ)) :
    ∑ i, z i * v i = (m : ℤ) * b := by
  apply Rat.intCast_injective
  rw [cast_sum_mul_of_cleared hz v, h, Int.cast_mul, Int.cast_natCast]

end OAI.LinearAlgebra.TensorSpectrum.AdditiveCone
