-- 本文件所属证明环节：用每个站点两条关联连线的对数维数之和表示负载。证明按三个高度参数测试的线性不等式等价于三个展平下界加一条根式不等式，包含零负载及展平达到等号的情形。对方形规格，该检验给出指数下界 3/√2。
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 矩形矩阵乘法的高度检验与根式检验

一个位置的负载是所有关联连线的维数取对数后的总和。本文件证明矩形秩定理中的两个数值判据等价，涵盖零负载和展平界取等的情形。

**英文原文**

The height and radical tests for rectangular matrix multiplication

The load at a site is the sum of its incident logarithmic wire dimensions.
This file proves the equivalence of the two numerical tests in the rectangular
rank theorem, including the cases of zero loads and saturated flattenings.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped BigOperators Topology
noncomputable section

-- 读法：`loads` 的取值由 `![w31 + w12, w12 + w23, w23 + w31]` 给出。
/-- 连线按循环次序排列时三个位置的负载。

英文原文：The three site loads for the cyclically ordered wires.
-/
def loads (w12 w23 w31 : ℝ) : Fin 3 → ℝ := ![w31 + w12, w12 + w23, w23 + w31]

-- 读法：`HeightTest` 表示以下条件：对每个 `a : Fin 3 → ℝ`，使 `(∀ i, 0 < a i) → ∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1)` 成立。
/-- 在各自独立选定的正高度上检验不等式 (height-bound)。

英文原文：Inequality (height-bound), tested at independently chosen positive heights.
-/
def HeightTest (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) →
    ∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1)

-- 读法：`RadicalTest` 的取值由 `(∀ i, m i ≤ L) ∧ L ≤ ∑ i, Real.sqrt (L ^ 2 - m i ^ 2)` 给出。
/-- 矩形秩定理中的展平不等式和根式不等式。

英文原文：The flattening and radical inequalities of the rectangular rank theorem.
-/
def RadicalTest (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  (∀ i, m i ≤ L) ∧ L ≤ ∑ i, Real.sqrt (L ^ 2 - m i ^ 2)

-- 读法：`0` 小于 `∑ i, Real.sqrt (1 + a i ^ 2) - 1`。这里调用 `Real.le_sqrt`。
/-- 对任意一组三个高度，对角价格的上界均为正。

英文原文：The diagonal-price upper bound is positive for every triple of heights.
-/
theorem heightDenom_pos (a : Fin 3 → ℝ) : 0 < ∑ i, Real.sqrt (1 + a i ^ 2) - 1 := by
  have h i : 1 ≤ Real.sqrt (1 + a i ^ 2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg (a i)])
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

-- 读法：要证明的命题是 `HeightTest m U`。
theorem HeightTest.mono {m : Fin 3 → ℝ} {L U : ℝ} (h : HeightTest m L) (hLU : L ≤ U) :
    HeightTest m U := by
  intro a ha
  exact (h a ha).trans (mul_le_mul_of_nonneg_right hLU (heightDenom_pos a).le)

-- 读法：`f x` 不超过 `g x`。这里调用 `le_of_tendsto_of_tendsto`。
private theorem le_at_right_endpoint {f g : ℝ → ℝ} {x : ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y, x < y → f y ≤ g y) : f x ≤ g x := by
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] x) hf.continuousAt.continuousWithinAt
    hg.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with y hy using h y hy

-- 读法：结论为 `∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1)`。
/-- 让正高度趋于零，即可处理高度为零的位置。

英文原文：Zero-height sites are obtained by approaching from positive heights.
-/
theorem HeightTest.nonnegHeights {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1) := by
  let f (t : ℝ) := ∑ i, (a i + t) * m i
  let g (t : ℝ) := L * (∑ i, Real.sqrt (1 + (a i + t) ^ 2) - 1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have bound : f 0 ≤ g 0 := le_at_right_endpoint hf hg
    (fun t ht => h (fun i => a i + t) (fun i => add_pos_of_nonneg_of_pos (ha i) ht))
  simpa [f, g] using bound

-- 读法：`0` 不超过 `L`。
theorem HeightTest.nonneg {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L) : 0 ≤ L := by
  have hzero := h.nonnegHeights (fun _ => 0) (fun _ => le_rfl)
  norm_num [Fin.sum_univ_three] at hzero
  linarith

-- 读法：`m i` 不超过 `L`。
/-- 让一个高度趋于无穷，得到对应的展平不等式。

英文原文：Sending one height to infinity gives the corresponding flattening inequality.
-/
theorem HeightTest.load_le {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L) (i : Fin 3) :
    m i ≤ L := by
  by_contra! hsmall
  let x := (2 * L + 1) / (m i - L)
  have hx : 0 < x := div_pos (by linarith [h.nonneg]) (sub_pos.mpr hsmall)
  have hax := h.nonnegHeights (fun j => if j = i then x else 0)
    (fun j => by split <;> positivity)
  have hbound : x * m i ≤ L * (Real.sqrt (1 + x ^ 2) + 1) := by
    fin_cases i <;> simp [Fin.sum_univ_three] at hax ⊢ <;> linarith
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have hden : x * (m i - L) = 2 * L + 1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hsmall.ne')
  nlinarith [mul_le_mul_of_nonneg_left hs h.nonneg]

-- 读法：结论为 `let r := Real.sqrt (p ^ 2 - b ^ 2) p * Real.sqrt (1 + (b / r) ^ 2) - (b / r) * b = r`。这里调用 `Real.sqrt_eq_iff_eq_sq`。
private theorem minimizing_height {p b : ℝ} (hb : 0 ≤ b) (hbp : b < p) :
    let r := Real.sqrt (p ^ 2 - b ^ 2)
    p * Real.sqrt (1 + (b / r) ^ 2) - (b / r) * b = r := by
  dsimp only
  let r := Real.sqrt (p ^ 2 - b ^ 2)
  have hdiff : 0 < p ^ 2 - b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hbp) (show 0 < p + b by linarith)]
  have hr : 0 < r := Real.sqrt_pos.2 hdiff
  have hrsq : r ^ 2 = p ^ 2 - b ^ 2 := Real.sq_sqrt hdiff.le
  have hs : Real.sqrt (1 + (b / r) ^ 2) = p / r := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (hb.trans hbp.le) hr.le)).mpr
    field_simp
    nlinarith
  change p * Real.sqrt (1 + (b / r) ^ 2) - (b / r) * b = r
  rw [hs]
  field_simp
  nlinarith

-- 读法：要证明的命题是 `RadicalTest m L`。这里调用 `le_at_right_endpoint`。
/-- 先增大秩参数，对每个加项取最小值，再让参数下降到原值。这样也能处理负载恰等于该参数的位置。

英文原文：Minimize each summand after increasing the rank parameter, then let it decrease to
its original value. This also handles sites with load equal to that parameter.
-/
theorem HeightTest.radicalTest {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L)
    (hm : ∀ i, 0 ≤ m i) : RadicalTest m L := by
  refine ⟨h.load_le, ?_⟩
  apply le_at_right_endpoint (f := id) (g := fun p => ∑ i, Real.sqrt (p ^ 2 - m i ^ 2))
    continuous_id (by fun_prop)
  intro p hp
  let a i := m i / Real.sqrt (p ^ 2 - m i ^ 2)
  have htest := (h.mono hp.le).nonnegHeights a (fun i => div_nonneg (hm i) (Real.sqrt_nonneg _))
  have hmin : ∀ i, p * Real.sqrt (1 + a i ^ 2) - a i * m i = Real.sqrt (p ^ 2 - m i ^ 2) :=
    fun i => minimizing_height (hm i) (lt_of_le_of_lt (h.load_le i) hp)
  change p ≤ _
  simp only [← hmin, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

-- 读法：要证明的命题是 `HeightTest m L`。
/-- 反向的变分不等式由二维柯西不等式推出。

英文原文：The converse variational inequality follows from the two-dimensional Cauchy inequality.
-/
theorem RadicalTest.heightTest {m : Fin 3 → ℝ} {L : ℝ} (h : RadicalTest m L)
    (hm : ∀ i, 0 ≤ m i) : HeightTest m L := by
  intro a ha
  have hL := (hm 0).trans (h.1 0)
  have hterm (i) : a i * m i + Real.sqrt (L ^ 2 - m i ^ 2) ≤
      L * Real.sqrt (1 + a i ^ 2) := by
    let r := Real.sqrt (L ^ 2 - m i ^ 2)
    have hr : r ^ 2 = L ^ 2 - m i ^ 2 := Real.sq_sqrt (by
      nlinarith [mul_nonneg (sub_nonneg.mpr (h.1 i)) (add_nonneg hL (hm i))])
    have hs : Real.sqrt (1 + a i ^ 2) ^ 2 = 1 + a i ^ 2 := Real.sq_sqrt (by positivity)
    change a i * m i + r ≤ _
    apply le_of_sq_le_sq _ (mul_nonneg hL (Real.sqrt_nonneg _))
    calc
      (a i * m i + r) ^ 2 ≤ (a i * m i + r) ^ 2 + (a i * r - m i) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      _ = (a i ^ 2 + 1) * (m i ^ 2 + r ^ 2) := by ring
      _ = _ := by rw [hr, mul_pow, hs]; ring
  -- 推导：记下中间结论 `hsum`：`= Finset.sum_le_sum (s`。
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith [h.2]

-- 读法：`HeightTest m L` 与 `RadicalTest m L` 等价。
theorem heightTest_iff_radicalTest {m : Fin 3 → ℝ} {L : ℝ} (hm : ∀ i, 0 ≤ m i) :
    HeightTest m L ↔ RadicalTest m L := ⟨(·.radicalTest hm), (·.heightTest hm)⟩

-- 读法：要证明的命题是 `RadicalTest m U`。
/-- 将渐近秩的对数换成较大秩度量的对数，两个不等式仍成立。

英文原文：Replacing log asymptotic rank by the logarithm of a larger rank measure
preserves both inequalities.
-/
theorem RadicalTest.mono {m : Fin 3 → ℝ} {L U : ℝ} (h : RadicalTest m L)
    (hm : ∀ i, 0 ≤ m i) (hLU : L ≤ U) : RadicalTest m U :=
  ((h.heightTest hm).mono hLU).radicalTest hm

-- 读法：`3 / Real.sqrt 2` 不超过 `L`。这里调用 `div_le_iff₀`。
/-- 当三个负载均为二时，根式不等式给出严格大于二的指数常数。

英文原文：For three equal loads of size two the radical inequality gives the
superquadratic exponent constant.
-/
theorem square_lower_bound {L : ℝ} (h : RadicalTest (fun _ => 2) L) :
    3 / Real.sqrt 2 ≤ L := by
  have hL : 2 ≤ L := h.1 0
  have hrad := h.2
  simp only [Fin.sum_univ_three] at hrad
  have hsq := Real.sq_sqrt (show 0 ≤ L ^ 2 - 2 ^ 2 by nlinarith [sq_nonneg (L - 2)])
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))).mpr
  apply le_of_sq_le_sq _ (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  rw [mul_pow, h2]
  nlinarith [sq_le_sq' (by linarith [Real.sqrt_nonneg (L ^ 2 - 2 ^ 2)] :
    -(3 * Real.sqrt (L ^ 2 - 2 ^ 2)) ≤ L) (by linarith : L ≤ 3 * Real.sqrt (L ^ 2 - 2 ^ 2))]

-- 读法：`0` 不超过 `loads w12 w23 w31 i`。使用 `fin_cases` 给出的结论。
theorem loads_nonneg {w12 w23 w31 : ℝ} (h12 : 0 ≤ w12) (h23 : 0 ≤ w23)
    (h31 : 0 ≤ w31) (i : Fin 3) : 0 ≤ loads w12 w23 w31 i := by
  fin_cases i <;> dsimp [loads] <;> positivity

-- 读法：要证明的命题是 `RadicalTest (loads w12 w23 w31) L`。这里调用 `Real.le_sqrt_of_sq_le`。
/-- 三条连线的权重之和总能通过根式检验。

英文原文：The sum of the three wire weights always passes the radical test.
-/
theorem radicalTest_of_totalWireLoad_le {w12 w23 w31 L : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) (htotal : w12 + w23 + w31 ≤ L) :
    RadicalTest (loads w12 w23 w31) L := by
  let m := loads w12 w23 w31
  have hbound (i : Fin 3) : m i ≤ L := by fin_cases i <;> dsimp [m, loads] <;> linarith
  have hterm (i : Fin 3) : L - m i ≤ Real.sqrt (L ^ 2 - m i ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have hprod : 0 ≤ m i * (L - m i) :=
      mul_nonneg (loads_nonneg h12 h23 h31 i) (sub_nonneg.mpr (hbound i))
    nlinarith
  refine ⟨hbound, ?_⟩
  -- 推导：记下中间结论 `hsum`：`= Finset.sum_le_sum (s`。
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Fin.sum_univ_three] at hsum ⊢
  dsimp [m, loads] at hsum ⊢
  linarith

-- 读法：`3 / Real.sqrt 2 * b` 不超过 `L`。这里调用 `Real.sqrt_eq_iff_eq_sq`。
/-- 方阵规格下，对数秩的界与阶数的二进对数成正比，其中也包括一阶矩阵。

英文原文：At square order the log-rank bound is proportional to the base-two
logarithm of the order, including order one.
-/
theorem square_log_lower_bound {b L : ℝ} (h : HeightTest (loads b b b) L) :
    3 / Real.sqrt 2 * b ≤ L := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt (1 + (2 * Real.sqrt 2) ^ 2) = 3 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)).mpr
    nlinarith
  have hh := h (fun _ => 2 * Real.sqrt 2) (fun _ => by positivity)
  simp only [Fin.sum_univ_three, loads, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, hden] at hh
  change 2 * Real.sqrt 2 * (b + b) + 2 * Real.sqrt 2 * (b + b) +
    2 * Real.sqrt 2 * (b + b) ≤ L * (3 + 3 + 3 - 1) at hh
  -- 推导：记下中间结论 `heq`：`3 / Real.sqrt 2 = 3 * Real.sqrt 2 / 2`。
  have heq : 3 / Real.sqrt 2 = 3 * Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  rw [heq]
  linarith

-- 读法：`n ^ (3 / Real.sqrt 2)` 不超过 `r`。这里调用 `Real.logb_le_logb`。
/-- 若方阵张量在秩度量 r 下满足有限高度界，则该秩度量至少是其阶数的指定次幂。

英文原文：A square tensor with the finite height bound at rank measure r has
rank measure at least the stated power of its order.
-/
theorem square_rpow_lower_bound {n r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (h : let b := Real.logb 2 n; HeightTest (loads b b b) (Real.logb 2 r)) :
    n ^ (3 / Real.sqrt 2) ≤ r := by
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (Real.rpow_pos_of_pos hn _) hr).mp
  rw [Real.logb_rpow_eq_mul_logb_of_pos hn]
  exact square_log_lower_bound h

end

end SpectralBooks
end LinearAlgebra
end OAI
