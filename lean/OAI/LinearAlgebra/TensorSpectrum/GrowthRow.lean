-- 本文件所属证明环节：对正的离散凹数列比较割线斜率和相邻差分，用三倍指标处的不等式控制行上的函数值；再取差分的下确界，得到对角论证需要的行斜率。
import OAI.LinearAlgebra.TensorSpectrum.Growth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# 有限行集上的界

对一个正的凹行序列，应用一次三倍化不等式，即可用平移后的索引乘以当前增量来控制行值。再由有限割线不等式，可对每个增量得到同一类型的界。最后取下确界即可得到对角论证所需的斜率，无须取渐近极限。

**英文原文**

Finite row bounds

For a concave positive row, one application of tripling bounds the row value
by a shifted index times the current increment.  Finite secant inequalities
then give the same bound for every increment.  Taking the infimum supplies
the slope required by the diagonal argument, without an asymptotic limit.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

-- 读法：`rowDifference` 的取值由 `x (n + 1) - x n` 给出。
def rowDifference (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - x n

-- 读法：`x (n + k) ≤ x n + (k : ℝ) * rowDifference x n` 与 `x n + (k : ℝ) * rowDifference x (n + k) ≤ x (n + k)` 同时成立。对 `k` 作归纳。
theorem row_secant_bounds
    (x : ℕ → ℝ) (hdec : Antitone (rowDifference x)) (n k : ℕ) :
    x (n + k) ≤ x n + (k : ℝ) * rowDifference x n ∧
      x n + (k : ℝ) * rowDifference x (n + k) ≤ x (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hdn := hdec (show n ≤ n + k by omega)
      have hdk := hdec (show n + k ≤ n + (k + 1) by omega)
      have hscaled := mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      -- 推导：记下中间结论 `hdelta`：`x (n + (k + 1)) = x (n + k) + rowDifference x (n + k)`。
      have hdelta : x (n + (k + 1)) = x (n + k) + rowDifference x (n + k) := by
        dsimp [rowDifference]
        simp only [Nat.add_assoc]
        ring
      constructor
      · push_cast
        linarith [ih.1]
      · push_cast
        linarith [ih.2]

-- 读法：`x n` 不超过 `((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x n`。
theorem row_local_bound
    (x : ℕ → ℝ) (a : ℕ)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1))
    (n : ℕ) :
    x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x n := by
  have hsec := (row_secant_bounds x hdec n (2 * n + a + 1)).1
  have hindex : n + (2 * n + a + 1) = 3 * n + a + 1 := by omega
  rw [hindex] at hsec
  push_cast at hsec
  have ht := htrip n
  nlinarith

-- 读法：`x n` 不超过 `((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x m`。
theorem row_bound_by_every_increment
    (x : ℕ → ℝ) (a : ℕ)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1))
    (n m : ℕ) :
    x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowDifference x m := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hlo := (row_secant_bounds x hdec n k).2
    have hup := row_local_bound x a hdec htrip (n + k)
    push_cast at hup
    linarith
  · have hd := hdec hmn
    have hc : 0 ≤ (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    exact (row_local_bound x a hdec htrip n).trans
      (mul_le_mul_of_nonneg_left hd hc)

-- 读法：`rowSlope` 的取值由 `sInf (Set.range (rowDifference x))` 给出。
noncomputable def rowSlope (x : ℕ → ℝ) : ℝ := sInf (Set.range (rowDifference x))

-- 读法：`0 ≤ rowSlope x` 与 `(∀ n : ℕ, rowSlope x ≤ rowDifference x n) ∧ (∀ n : ℕ, x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowSlope x)` 同时成立。
theorem row_slope_properties
    (x : ℕ → ℝ) (a : ℕ)
    (hpos : ∀ n : ℕ, 0 < x n)
    (hdec : Antitone (rowDifference x))
    (htrip : ∀ n : ℕ, 3 * x n ≤ x (3 * n + a + 1)) :
    0 ≤ rowSlope x ∧
      (∀ n : ℕ, rowSlope x ≤ rowDifference x n) ∧
      (∀ n : ℕ, x n ≤ ((n : ℝ) + ((a : ℝ) + 1) / 2) * rowSlope x) := by
  have hdnonneg : ∀ n : ℕ, 0 ≤ rowDifference x n := by
    intro n
    have hlocal := row_local_bound x a hdec htrip n
    -- 推导：记下中间结论 `hc`：`0 ≤ (n : ℝ) + ((a : ℝ) + 1) / 2`。
    have hc : 0 ≤ (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    by_contra! hneg
    have hm := mul_nonpos_of_nonneg_of_nonpos hc hneg.le
    linarith [hpos n]
  have hne : (Set.range (rowDifference x)).Nonempty := ⟨rowDifference x 0, 0, rfl⟩
  have hbounded : BddBelow (Set.range (rowDifference x)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact hdnonneg n
  refine ⟨?_, ?_, ?_⟩
  · apply le_csInf hne
    rintro y ⟨n, rfl⟩
    exact hdnonneg n
  · intro n
    exact csInf_le hbounded ⟨n, rfl⟩
  · intro n
    -- 推导：记下中间结论 `hc`：`0 < (n : ℝ) + ((a : ℝ) + 1) / 2`。
    have hc : 0 < (n : ℝ) + ((a : ℝ) + 1) / 2 := by positivity
    have hratio : x n / ((n : ℝ) + ((a : ℝ) + 1) / 2) ≤ rowSlope x := by
      apply le_csInf hne
      rintro y ⟨m, rfl⟩
      apply (div_le_iff₀ hc).mpr
      simpa [mul_comm] using row_bound_by_every_increment x a hdec htrip n m
    have hout := (div_le_iff₀ hc).mp hratio
    simpa [mul_comm] using hout

end OAI.LinearAlgebra.TensorSpectrum
