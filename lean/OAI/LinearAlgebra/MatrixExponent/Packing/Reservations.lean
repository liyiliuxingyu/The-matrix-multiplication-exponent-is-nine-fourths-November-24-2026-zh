-- 本文件所属证明环节：对二进分组的站点和线束装包、匹配及重新布线，逐项控制异常基区、临界负载、重置度数以及核心连线宽度的递推。
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array

section
/-!
# 汇总二分传播的各项代价

传播权重每八层翻倍。在基块下方深度 `j` 处的分裂按 `min (2^-k) (2^-j)` 计费，其中最小基块长度为 `F = 2^k`。总和至多为 `24 * 2^⌈k/8⌉ / 2^k`。

**英文原文**

Summing the charges for propagated splits

The propagation weight doubles every eight levels. Splits at depth `j`
below a base are paid for at rate `min (2^-k) (2^-j)`, where the minimum
base length is `F = 2^k`. The sum is at most `24 * 2^⌈k/8⌉ / 2^k`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset

-- 读法：`resetWeight` 的取值由 `(2 : ℝ) ^ ((j + 7) / 8)` 给出。
def resetWeight (j : ℕ) := (2 : ℝ) ^ ((j + 7) / 8)

-- 读法：`0` 不超过 `resetWeight j`。
private theorem weight_nonneg (j : ℕ) : 0 ≤ resetWeight j := by
  unfold resetWeight
  positivity

-- 读法：`resetWeight` 是单调不减的。这里调用 `pow_le_pow_right₀`。
private theorem weight_mono : Monotone resetWeight := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num) (by omega)

-- 读法：`resetWeight (j + 8)` 等于 `2 * resetWeight j`。
private theorem weight_add (j : ℕ) : resetWeight (j + 8) = 2 * resetWeight j := by
  unfold resetWeight
  rw [show (j + 8 + 7) / 8 = (j + 7) / 8 + 1 by omega, pow_succ']

-- 读法：结论为 `∑ j ∈ range k, resetWeight j ≤ 16 * resetWeight k`。这里调用 `le_add_of_nonneg_left`。
private theorem prefix_bound (k : ℕ) :
    ∑ j ∈ range k, resetWeight j ≤ 16 * resetWeight k := by
  have h : 2 * ∑ j ∈ range k, resetWeight j ≤ ∑ j ∈ range (k + 8), resetWeight j := by
    rw [Nat.add_comm k 8, sum_range_add]
    simp only [Nat.add_comm 8, weight_add, ← mul_sum]
    exact le_add_of_nonneg_left (sum_nonneg fun j _ => weight_nonneg j)
  have ht : ∑ j ∈ range 8, resetWeight (k + j) ≤ 16 * resetWeight k := by
    calc
      _ ≤ ∑ _j ∈ range 8, resetWeight (k + 8) := sum_le_sum fun j hj =>
        weight_mono (Nat.add_le_add_left (mem_range.mp hj).le k)
      _ = _ := by simp [weight_add]; ring
  rw [sum_range_add] at h
  linarith

-- 读法：结论为 `∑ j ∈ range n, resetWeight (k + j) / (2 : ℝ) ^ (k + j) ≤ (4 * resetWeight k + 2 * resetWeight (k + 1)) / (2 : ℝ) ^ k`。对 `n` 作归纳，并把 `k` 保持为任意参数。
private theorem tail_bound (k n : ℕ) :
    ∑ j ∈ range n, resetWeight (k + j) / (2 : ℝ) ^ (k + j) ≤
      (4 * resetWeight k + 2 * resetWeight (k + 1)) / (2 : ℝ) ^ k := by
  induction n generalizing k with
  | zero =>
    have := weight_nonneg k
    have := weight_nonneg (k + 1)
    simp only [range_zero, sum_empty]
    positivity
  | succ n ih =>
    rw [sum_range_succ']
    have he : (∑ j ∈ range n, resetWeight (k + (j + 1)) / (2 : ℝ) ^ (k + (j + 1))) =
        ∑ j ∈ range n, resetWeight (k + 1 + j) / (2 : ℝ) ^ (k + 1 + j) :=
      sum_congr rfl (fun j _ => by rw [show k + (j + 1) = k + 1 + j by omega])
    rw [he, Nat.add_zero]
    apply (add_le_add_left (ih (k + 1)) (resetWeight k / (2 : ℝ) ^ k)).trans
    have hu := weight_mono (show k + 1 + 1 ≤ k + 8 by omega)
    rw [weight_add] at hu
    rw [pow_succ]
    field_simp
    linarith [weight_nonneg k]

-- 读法：结论为 `∑ j ∈ range n, resetWeight j / (2 : ℝ) ^ (max k j) ≤ 24 * resetWeight k / (2 : ℝ) ^ k`。
theorem resetWeight_bound (k n : ℕ) :
    ∑ j ∈ range n, resetWeight j / (2 : ℝ) ^ (max k j) ≤
      24 * resetWeight k / (2 : ℝ) ^ k := by
  calc
    _ ≤ ∑ j ∈ range (k + n), resetWeight j / (2 : ℝ) ^ (max k j) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun j _ _ => div_nonneg (weight_nonneg j) (by positivity))
    _ = (∑ j ∈ range k, resetWeight j) / (2 : ℝ) ^ k +
          ∑ j ∈ range n, resetWeight (k + j) / (2 : ℝ) ^ (k + j) := by
      rw [sum_range_add, sum_div]
      congr 1
      · apply sum_congr rfl
        intro j hj
        rw [max_eq_left (mem_range.mp hj).le]
      · simp only [max_eq_right (Nat.le_add_right k _)]
    _ ≤ 16 * resetWeight k / (2 : ℝ) ^ k +
        (4 * resetWeight k + 2 * resetWeight (k + 1)) / (2 : ℝ) ^ k :=
      add_le_add (div_le_div_of_nonneg_right (prefix_bound k) (by positivity)) (tail_bound k n)
    _ ≤ _ := by
      have hu := weight_mono (show k + 1 ≤ k + 8 by omega)
      rw [weight_add] at hu
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

-- 读法：存在 `k ≥ j`，`144 * resetWeight k / (2 : ℝ) ^ k + 4 * g ^ 2 / (2 : ℝ) ^ k` 不超过 `ε`。
/-- 所需的最小基块长度只取决于安全余量与容许误差，系线邻点的数量可以任意大。

英文原文：The required minimum base length depends only on the safety margin
and error tolerance, even with arbitrarily many tether neighbors.
-/
theorem small_resetWeight (g ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ k ≥ j, 144 * resetWeight k / (2 : ℝ) ^ k + 4 * g ^ 2 / (2 : ℝ) ^ k ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((144 + 4 * g ^ 2) / ε)
  let r := max n j
  have hN : (n : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (le_max_left n j).trans (Nat.lt_two_pow_self (n := r)).le
  have h : 144 + 4 * g ^ 2 ≤ (2 : ℝ) ^ r * ε := (div_le_iff₀ hε).mp (hn.le.trans hN)
  refine ⟨8 * r, by dsimp [r]; omega, ?_⟩
  rw [resetWeight, show (8 * r + 7) / 8 = r by omega, ← add_div, div_le_iff₀ (by positivity)]
  have hr : 1 ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (144 + 4 * g ^ 2) * (2 : ℝ) ^ r := by
      rw [add_mul]
      exact add_le_add_right (le_mul_of_one_le_right (by positivity) hr) _
    _ ≤ ((2 : ℝ) ^ r * ε) * (2 : ℝ) ^ r := mul_le_mul_of_nonneg_right h (by positivity)
    _ = ε * (2 : ℝ) ^ (r + r) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hε.le

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 度数重置中的超额负载

以容量 `FB` 归一化。若各负载至多为 `1/F`，且基块均值至多为一，则有两个互补的上界。轻微超载由方差项控制，偏离较远的超载由非对角项控制。

**英文原文**

Excess loads in the degree reset

Normalize by the capacity `FB`. Loads at most `1/F` with base mean
at most one obey two complementary bounds. The variance pays for near
overloads and the off-diagonal term for distant ones.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset

variable {h : ℕ} (l : Cell h → ℝ) (π : Equiv.Perm (Cell h)) (i : ℕ)

-- 读法：`excess` 的取值由 `∑ z : Cell i, if 2 < load l π i z then load l π i z else 0` 给出。
def excess := ∑ z : Cell i, if 2 < load l π i z then load l π i z else 0

-- 读法：`2 * (∑ z, if 2 < load l π i z then (1 : ℝ) else 0)` 不超过 `excess l π i`。这里调用 `sum_le_sum`。
theorem overload_count :
    2 * (∑ z, if 2 < load l π i z then (1 : ℝ) else 0) ≤ excess l π i := by
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs <;> linarith

-- 读法：`excess l π i` 不超过 `2 * variance l π i`。这里调用 `sum_le_sum`。
theorem excess_variance (hm : mean l i ≤ 1) :
    excess l π i ≤ 2 * variance l π i := by
  unfold variance
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · have := sq_nonneg (load l π i z - mean l i - 1)
    nlinarith
  · positivity

-- 读法：`excess l π i` 不超过 `2 * ∑ z, cross l π i z`。这里调用 `sum_le_sum`。
theorem excess_cross (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1) :
    excess l π i ≤ 2 * ∑ z, cross l π i z := by
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · unfold cross
    nlinarith [diagonal_le l π i z hl]
  · exact mul_nonneg (by norm_num) (cross_nonneg l π i (fun x => (hl x).1) z)

variable {M : Type} [Fintype M] {p : M → Equiv.Perm (Cell h)} {k b : ℕ}

-- 读法：`(∑ m, variance l (p m) i)` 不超过 `(Fintype.card M : ℝ) * (∑ x, l x) / (2 : ℝ) ^ k`。这里调用 `variance_bound`。
private theorem small_variance (hp : Mixes p) (hi : i ≤ h)
    (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / (2 : ℝ) ^ k) :
    (∑ m, variance l (p m) i) ≤ (Fintype.card M : ℝ) * (∑ x, l x) / (2 : ℝ) ^ k := by
  apply (variance_bound l i hp (fun x => (hl x).1) hi).trans
  rw [mul_div_assoc, sum_div]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro x _
  simpa [pow_two, div_eq_mul_inv] using mul_le_mul_of_nonneg_left (hl x).2 (hl x).1

-- 读法：`estimate` 的取值由 `if b + j ≤ h then if j ≤ k then 2 * variance l π (b + j) else 2 * ∑ z, cross l π (b + j) z else 0` 给出。
/-- 该估计量中只有二次矩依赖于置换。

英文原文：Only quadratic moments in this estimator depend on the permutation.
-/
def estimate (k b j : ℕ) : ℝ :=
  if b + j ≤ h then
    if j ≤ k then 2 * variance l π (b + j) else 2 * ∑ z, cross l π (b + j) z
  else 0

-- 读法：`excess l π (b + j)` 不超过 `estimate l π k b j`。这里调用 `excess_variance`。
theorem excess_le_estimate (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / (2 : ℝ) ^ k)
    (hb : ∑ x, l x ≤ (2 : ℝ) ^ b) (j : ℕ) : excess l π (b + j) ≤ estimate l π k b j := by
  unfold estimate
  split_ifs with hd hj
  · apply excess_variance
    apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ (b + j))).mpr
    exact hb.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _))
  · apply excess_cross
    exact fun x =>
      ⟨(hl x).1, (hl x).2.trans ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))⟩
  · simp [excess, load, hd]

-- 读法：`(∑ m, estimate l (p m) k b j)` 不超过 `2 * (Fintype.card M : ℝ) * (∑ x, l x) / (2 : ℝ) ^ (max k j)`。按 `b + j ≤ h` 成立与否分情况。
theorem estimate_bound (hp : Mixes p)
    (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / (2 : ℝ) ^ k) (hb : ∑ x, l x ≤ (2 : ℝ) ^ b) (j : ℕ) :
    (∑ m, estimate l (p m) k b j) ≤
      2 * (Fintype.card M : ℝ) * (∑ x, l x) / (2 : ℝ) ^ (max k j) := by
  have hl₀ x := (hl x).1
  have hs : 0 ≤ ∑ x, l x := sum_nonneg fun x _ => hl₀ x
  by_cases hd : b + j ≤ h
  swap
  · simp only [estimate, ite_eq_right hd, sum_const_zero]
    positivity
  by_cases hj : j ≤ k
  · simp only [estimate, ite_eq_left hd, ite_eq_left hj]
    rw [← mul_sum, max_eq_left hj, mul_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (small_variance l _ hp hd hl) (by norm_num)
  · simp only [estimate, ite_eq_left hd, ite_eq_right hj]
    calc
      _ ≤ 2 * ((Fintype.card M : ℝ) * ((∑ x, l x) ^ 2 / (2 : ℝ) ^ (b + j))) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (cross_bound l _ hp hl₀ hd) (by norm_num)
      _ ≤ _ := by
        rw [max_eq_right (le_of_not_ge hj), pow_add]
        field_simp
        nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card M)) hs)
          (sub_nonneg.mpr hb)]

-- 读法：`(∑ m, ∑ j ∈ range n, resetWeight j * estimate l (p m) k b j)` 不超过 `(Fintype.card M : ℝ) * (48 * resetWeight k / (2 : ℝ) ^ k) * ∑ x, l x`。这里调用 `sum_le_sum`。
/-- 给出单个位置的上界，再对各位置与各接触求和。

英文原文：A bound for a single position, to be summed over positions and contacts.
-/
theorem weighted_estimate (hp : Mixes p)
    (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / (2 : ℝ) ^ k) (hb : ∑ x, l x ≤ (2 : ℝ) ^ b) (n : ℕ) :
    (∑ m, ∑ j ∈ range n, resetWeight j * estimate l (p m) k b j) ≤
      (Fintype.card M : ℝ) * (48 * resetWeight k / (2 : ℝ) ^ k) * ∑ x, l x := by
  have hs : 0 ≤ ∑ x, l x := sum_nonneg fun x _ => (hl x).1
  calc
    _ ≤ ∑ j ∈ range n, 2 * (Fintype.card M : ℝ) * (∑ x, l x) *
        (resetWeight j / (2 : ℝ) ^ (max k j)) := by
      rw [sum_comm]
      apply sum_le_sum
      intro j _
      rw [← mul_sum]
      have he := mul_le_mul_of_nonneg_left (estimate_bound l hp hl hb j)
        (show 0 ≤ resetWeight j by unfold resetWeight; positivity)
      exact he.trans_eq (by ring)
    _ ≤ _ := by
      rw [← mul_sum]
      have he := mul_le_mul_of_nonneg_left (resetWeight_bound k n)
        (show 0 ≤ 2 * (Fintype.card M : ℝ) * (∑ x, l x) by positivity)
      exact he.trans_eq (by ring)

-- 读法：`spills` 的取值由 `∑ z : Cell i, if mean l i + 1 / g < load l π i z then (1 : ℝ) else 0` 给出。
/-- 每个接触的预留量等于其平均值加上固定的安全余量。

英文原文：A contact reserves its mean plus a fixed safety margin.
-/
def spills (g : ℝ) := ∑ z : Cell i, if mean l i + 1 / g < load l π i z then (1 : ℝ) else 0

-- 读法：`spills l π i g` 不超过 `g ^ 2 * variance l π i`。这里调用 `sum_le_sum`。
theorem spills_variance {g : ℝ} (hg : 0 < g) : spills l π i g ≤ g ^ 2 * variance l π i := by
  unfold variance
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · have hv : 1 ≤ g * (load l π i z - mean l i) := by
      rw [mul_comm]
      exact (div_le_iff₀ hg).mp (by linarith)
    rw [← mul_pow]
    exact one_le_pow₀ hv
  · positivity

-- 读法：`(∑ m, g ^ 2 * variance l (p m) i)` 不超过 `(Fintype.card M : ℝ) * (g ^ 2 / (2 : ℝ) ^ k) * ∑ x, l x`。这里调用 `mul_le_mul_of_nonneg_left`。
theorem spill_estimate (hp : Mixes p) (hi : i ≤ h)
    (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / (2 : ℝ) ^ k) (g : ℝ) :
    (∑ m, g ^ 2 * variance l (p m) i) ≤
      (Fintype.card M : ℝ) * (g ^ 2 / (2 : ℝ) ^ k) * ∑ x, l x := by
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (small_variance l i hp hi hl) (sq_nonneg g)).trans_eq
    (by ring)

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# 每对基块之间的预留量

两个相交的二进单元必然互相嵌套。因此，每个接触由两个深度中较深的那一层的单元索引，其端点可通过取前缀得到。其容量等于对所有此类单元求得的均值，加上一个与混合器无关的安全余量。

**英文原文**

Reservations between pairs of bases

Two dyadic cells that intersect are nested. Thus each contact is indexed
by a cell at the finer of the two depths, with endpoints obtained by
taking prefixes. Its capacity is the mean over all such cells plus a
safety margin independent of the mixer.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {V A : Type} (base : V → ℕ) (ends : A → Bool → V)

-- 读法：`contactDepth` 的取值由 `max (base (ends c false)) (base (ends c true))` 给出。
def contactDepth (c : A) := max (base (ends c false)) (base (ends c true))

-- 读法：`base (ends c t)` 不超过 `contactDepth base ends c`。
theorem le_contactDepth (c : A) (t : Bool) : base (ends c t) ≤ contactDepth base ends c := by
  cases t <;> simp [contactDepth]

-- 读法：`contactEnd` 的取值由 `⟨ends w.1 t, ancestor (le_contactDepth base ends w.1 t) w.2⟩` 给出。
def contactEnd (w : Σ c, Cell (contactDepth base ends c)) (t : Bool) : Σ v, Cell (base v) :=
  ⟨ends w.1 t, ancestor (le_contactDepth base ends w.1 t) w.2⟩

-- 读法：`(∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then x else 0)` 等于 `if ends c t = v then (2 : ℝ) ^ (contactDepth base ends c - base v) * x else 0`。按 `ends c t = v` 成立与否分情况。
private theorem endpoint_sum (c : A) (t : Bool) (v : V) (z : Cell (base v)) (x : ℝ) :
    (∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then x else 0) =
    if ends c t = v then (2 : ℝ) ^ (contactDepth base ends c - base v) * x else 0 := by
  by_cases he : ends c t = v
  · subst v
    simp only [contactEnd, Sigma.mk.inj_iff, heq_eq_eq, true_and, ite_true]
    rw [← sum_filter, sum_const, nsmul_eq_mul, ← Fintype.card_subtype, card_prefix (le_contactDepth base ends c t) z]
    norm_cast
  · have hn (w : Cell (contactDepth base ends c)) :
        contactEnd base ends ⟨c, w⟩ t ≠ ⟨v, z⟩ := fun eq => he (congrArg Sigma.fst eq)
    simp only [hn, he, ite_false, sum_const_zero]

-- 读法：`(∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then (1 : ℝ) else 0)` 不超过 `D * (2 : ℝ) ^ s`。这里调用 `sum_le_sum`。
theorem reservation_count [Fintype A] (v : V) (z : Cell (base v)) (s : ℕ) (D : ℝ)
    (gap : ∀ c t, ends c t = v → contactDepth base ends c ≤ base v + s)
    (degree : (∑ c, ∑ t : Bool, if ends c t = v then (1 : ℝ) else 0) ≤ D) :
    (∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then (1 : ℝ) else 0) ≤
      D * (2 : ℝ) ^ s := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_right degree (by positivity))
  simp only [sum_mul, endpoint_sum, mul_one]
  apply sum_le_sum
  intro c _
  apply sum_le_sum
  intro t _
  split_ifs with he
  · rw [one_mul]
    have := gap c t he
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · simp

-- 读法：这里调用 `sum_le_sum`。
/-- 一个基块上预留容量的总成本至多为两个归一化单位。

英文原文：The reserved capacities at a base cost at most two normalized units.
-/
theorem reservation_bound [Fintype A] (y : A → ℝ) (v : V) (z : Cell (base v))
    (s : ℕ) (D : ℝ) (hD : 0 < D)
    (gap : ∀ c t, ends c t = v → contactDepth base ends c ≤ base v + s)
    (degree : (∑ c, ∑ t : Bool, if ends c t = v then (1 : ℝ) else 0) ≤ D)
    (mass : (∑ c, ∑ t : Bool, if ends c t = v then y c else 0) ≤ (2 : ℝ) ^ (base v)) :
    (∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then
        y c / (2 : ℝ) ^ (contactDepth base ends c) + 1 / (D * (2 : ℝ) ^ s) else 0) ≤ 2 := by
  calc
    _ ≤ ∑ c, ∑ t : Bool, ((if ends c t = v then y c else 0) / (2 : ℝ) ^ (base v) +
          (if ends c t = v then (1 : ℝ) else 0) / D) := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro t _
      rw [endpoint_sum]
      by_cases hv : ends c t = v
      swap
      · simp [hv]
      -- 推导：记下中间结论 `lo`：`base v ≤ contactDepth base ends c`。
      have lo : base v ≤ contactDepth base ends c := hv ▸ le_contactDepth base ends c t
      have hi := gap c t hv
      have hr : (2 : ℝ) ^ (contactDepth base ends c - base v) ≤ (2 : ℝ) ^ s :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simp only [hv, ite_true, mul_add]
      have he : (2 : ℝ) ^ (contactDepth base ends c) =
          (2 : ℝ) ^ (contactDepth base ends c - base v) * (2 : ℝ) ^ (base v) := by
        rw [← pow_add, Nat.sub_add_cancel lo]
      rw [he]
      apply add_le_add
      · field_simp
        exact le_rfl
      · field_simp
        exact hr
    _ ≤ _ := by
      simp only [sum_add_distrib, ← sum_div]
      have := (div_le_one (by positivity : 0 < (2 : ℝ) ^ (base v))).mpr mass
      have := (div_le_one hD).mpr degree
      linarith

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# 以域元素为乘子混合块索引

将二进制块索引与 `2 ^ h` 阶域对应。当乘子取遍该域所有可逆元时，任意两个不同索引之差恰好遍历每个非零向量一次。这些向量中，长度为 `i` 的前缀全零者至多有 `2 ^ (h-i) - 1` 个。

**英文原文**

Mixing block indices by a field multiplier

Identify binary block indices with a field of order `2 ^ h`. As the
multiplier ranges over units, the difference of any two distinct indices
visits each nonzero vector once. At most `2 ^ (h-i) - 1` of these vectors
have zero prefix of length `i`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

-- 读法：按 `h = 0` 成立与否分情况。
/-- 同一族线性置换可同时用于所有深度。

英文原文：A single family of linear permutations works simultaneously at all depths.
-/
theorem mixer (h : ℕ) :
    ∃ (M : Type) (_ : Fintype M) (_ : Nonempty M) (π : M → Equiv.Perm (Cell h)),
      Fintype.card M ≤ 2 ^ h ∧ (∀ m, ∃ f : Cell h ≃ₗ[ZMod 2] Cell h, f.toEquiv = π m) ∧
      Mixes π := by
  classical
  by_cases hh : h = 0
  · subst h
    refine ⟨Unit, inferInstance, inferInstance, fun _ => Equiv.refl _, by simp,
      fun _ => ⟨LinearEquiv.refl _ _, rfl⟩, ?_⟩
    exact fun _ _ x y hxy => (hxy (Subsingleton.elim x y)).elim
  let E := GaloisField 2 h
  let : Fintype E := Fintype.ofFinite _
  let e : Cell h ≃ₗ[ZMod 2] E :=
    LinearEquiv.ofFinrankEq _ _ (by simp [E, GaloisField.finrank 2 hh])
  let f (m : Eˣ) : Cell h ≃ₗ[ZMod 2] Cell h :=
    e.trans (((LinearEquiv.smulOfUnit m : E ≃ₗ[E] E).restrictScalars (ZMod 2)).trans e.symm)
  -- 推导：记下中间结论 `hc`：`Fintype.card Eˣ + 1 = 2 ^ h`。
  have hc : Fintype.card Eˣ + 1 = 2 ^ h := by
    rw [Fintype.card_units, Nat.sub_add_cancel Fintype.card_pos, ← Fintype.card_congr e.toEquiv,
      card_cell]
  refine ⟨Eˣ, inferInstance, inferInstance, fun m => (f m).toEquiv, by omega,
    fun m => ⟨f m, rfl⟩, fun i hi x y hxy => ?_⟩
  let B := {m : Eˣ // ancestor hi (f m x) = ancestor hi (f m y)}
  let K := {x : Cell h // ancestor hi x = 0}
  let g (m : B) : K := ⟨f m.1 (x - y), by
    rw [map_sub]
    change ancestor hi (f m.1 x) - ancestor hi (f m.1 y) = 0
    exact sub_eq_zero.mpr m.2⟩
  have inj : Function.Injective g := by
    intro m n eq
    -- 推导：记下中间结论 `he`：`e.symm (m.1.val * e (x - y)) = e.symm (n.1.val * e (x - y))`。
    have he : e.symm (m.1.val * e (x - y)) = e.symm (n.1.val * e (x - y)) :=
      congrArg Subtype.val eq
    have hne : e (x - y) ≠ 0 := e.map_eq_zero_iff.not.mpr (sub_ne_zero.mpr hxy)
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hne (e.symm.injective he)))
  have miss : (⟨0, rfl⟩ : K) ∉ Set.range g := by
    rintro ⟨m, hm⟩
    have he : f m.1 (x - y) = 0 := congrArg Subtype.val hm
    exact hxy (sub_eq_zero.mp ((f m.1).map_eq_zero_iff.mp he))
  have hsmall := (Fintype.card_lt_of_injective_of_notMem g inj miss).trans_eq (card_prefix hi 0)
  have bound : Fintype.card B * 2 ^ i ≤ Fintype.card Eˣ := by
    have := Nat.mul_lt_mul_of_pos_right hsmall (by positivity : 0 < 2 ^ i)
    rw [← pow_add, Nat.sub_add_cancel hi] at this
    omega
  rw [Finset.sum_boole, ← Fintype.card_subtype, le_div_iff₀ (by positivity)]
  exact_mod_cast bound

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# 核心重置的共同预留量与各项专用层

**英文原文**

Common reservations and term-specific layers for the core reset
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

variable {P U X W : Type}
  (leaf : P → X) (point : U → Bool → P) (good : U → Prop)
  (edge : U → W) (outLeaf : W → Bool → X) (cap : W → ℝ) (Y w : ℕ)

-- 读法：在后续公式中，`Port` 是 `Σ q : {q : W × Bool // outLeaf q.1 q.2 = x}, Fin ⌈cap q.val.1 * Y / 8⌉₊` 的缩写。
/-- 一条预留链路的两端各有一个槽位，且两端槽位的索引相同。

英文原文：A reserved link has one slot at each end with the same index.
-/
abbrev Port (x : X) :=
  Σ q : {q : W × Bool // outLeaf q.1 q.2 = x}, Fin ⌈cap q.val.1 * Y / 8⌉₊

-- 读法：在后续公式中，`GoodEnd` 是 `{q : {i // good i} × Bool // leaf (point q.1.val q.2) = x}` 的缩写。
abbrev GoodEnd (x : X) :=
  {q : {i // good i} × Bool // leaf (point q.1.val q.2) = x}

-- 读法：`portOf` 的取值由 `⟨⟨(edge q.val.1.val, q.val.2), (agree _ q.val.1.property _).symm.trans q.property⟩, slot q.val.1⟩` 给出。
def portOf (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (slot : ∀ a : {i // good i}, Fin ⌈cap (edge a.val) * Y / 8⌉₊)
    {x : X} (q : GoodEnd leaf point good x) : Port outLeaf cap Y x :=
  ⟨⟨(edge q.val.1.val, q.val.2), (agree _ q.val.1.property _).symm.trans q.property⟩, slot q.val.1⟩

variable [Fintype P]

-- 读法：结构的字段包括 `agree`、`slot`、`terminal`、`layers`、`config`。
/-- 将各输入的整个出现项接到终端。对每个良好单位，在其两端分别选取互不冲突的端口，所在层连接到预留链路。

英文原文：Attach whole input occurrences to terminals. At both ends of each good
unit, select a distinct port on a layer connecting to the reserved link.
-/
structure Delivery (out : ∀ x, Port outLeaf cap Y x ↪ Fin Y) (l : P → ℝ) (u : ℝ) where
  agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t
  slot : ∀ a : {i // good i}, Fin ⌈cap (edge a.val) * Y / 8⌉₊
  terminal : P → Fin Y
  layers : X → ℕ
  config : ∀ x, Fin (layers x) → Equiv.Perm (Fin Y)
  lane : ∀ x, GoodEnd leaf point good x → Fin (layers x) × Fin w
  load : ∀ x i, push (fun p => (leaf p, terminal p)) l (x, i) * Y ≤ 3
  cost : ∀ x, (layers x : ℝ) * Y * w * u ≤ 10
  empty : ∀ x, IsEmpty (GoodEnd leaf point good x) → layers x = 0
  routes : ∀ x q, config x (lane x q).1 (terminal (point q.val.1.val q.val.2)) =
    out x (portOf leaf point good edge outLeaf cap Y agree slot q)
  input : ∀ x, Function.Injective (fun q : GoodEnd leaf point good x =>
    (terminal (point q.val.1.val q.val.2), lane x q))
  output : ∀ x, Function.Injective (fun q : GoodEnd leaf point good x =>
    (out x (portOf leaf point good edge outLeaf cap Y agree slot q), lane x q))

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 通过固定输出标签为带标签的验证器编程

**英文原文**

Programming a tagged verifier by fixing the output tags
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Tagged
open scoped Classical

variable {a b : Wire} {k w : ℕ} {I : Type}

-- 读法：`write` 的取值由 `(bits b).symm fun j => bits a (x (L.positions.symm j).1) (L.positions.symm j).2` 给出。
private def write (L : Layout a b I) (x : I → Val a) : Val b :=
  (bits b).symm fun j => bits a (x (L.positions.symm j).1) (L.positions.symm j).2

-- 读法：`bits b (write L x) (L.positions (i, j))` 等于 `bits a (x i) j`。
private theorem bits_write (L : Layout a b I) (x : I → Val a) (i : I) (j : slots a) :
    bits b (write L x) (L.positions (i, j)) = bits a (x i) j := by simp [write]

-- 读法：`L.read (write L x)` 等于 `x`。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem read_write (L : Layout a b I) (x : I → Val a) :
    L.read (write L x) = x := by
  funext i
  simp [Layout.read, bits_write]

-- 读法：存在 `addr : Fin (2 ^ k) → Val (word k)`，`Function.Injective addr` 与 `∀ x i, R.read (label k x) i = (addr i, P.read x i)` 同时成立。
private theorem label_read (P : Layout a (tree k a) (Fin (2 ^ k)))
    (hp : ∀ x, List.ofFn (P.read x) = flatten k x)
    (R : Layout (row k a) (tree k (row k a)) (Fin (2 ^ k)))
    (hr : ∀ x, List.ofFn (R.read x) = flatten k x) :
    ∃ addr : Fin (2 ^ k) → Val (word k), Function.Injective addr ∧
      ∀ x i, R.read (label k x) i = (addr i, P.read x i) := by
  obtain ⟨L, hL⟩ := Layout.exists_tree (word k) k
  refine ⟨L.read (indices k), List.nodup_ofFn.mp ?_, fun x i => Prod.ext ?_ ?_⟩
  · rw [hL]; exact indices_nodup k
  · have ht := label_tags k x
    rw [← hr, ← hL, List.map_ofFn] at ht
    exact congrFun (List.ofFn_injective ht) i
  · have ht := congrArg (flatten k) (label_payloads k x)
    rw [payloads, flatten_mapRows, ← hr, ← hp, List.map_ofFn] at ht
    exact congrFun (List.ofFn_injective ht) i

-- 读法：`(List.ofFn (fun i => (t (σ.symm i), y (σ.symm i)))).Perm (List.ofFn (fun i => (t i, x i)))` 与 `x = y` 等价。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem perm_tagged {n : ℕ} {X Y : Type} (t : Fin n → X) (ht : Function.Injective t)
    (x y : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn (fun i => (t (σ.symm i), y (σ.symm i)))).Perm
      (List.ofFn (fun i => (t i, x i))) ↔ x = y := by
  constructor
  · intro hp
    funext i
    have hi : (t i, y i) ∈ List.ofFn (fun j => (t (σ.symm j), y (σ.symm j))) :=
      List.mem_ofFn.mpr ⟨σ i, by simp⟩
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp (hp.subset hi)
    -- 推导：从 `Prod.mk.inj hj` 中取出 `e, he`。
    obtain ⟨e, he⟩ := Prod.mk.inj hj
    simpa only [ht e] using he
  · rintro rfl
    exact Equiv.Perm.ofFn_comp_perm σ.symm (fun i => (t i, x i))

-- 读法：证明中先建立 `hg`，即 `Function.Injective g`。
/-- 为转子指定固定且互不相同的输入位置与输出位置。由置换进行编程的只有位置标签。

英文原文：Designate fixed, distinct input and output positions for the rotor.
Only the positional tags are programmed by the permutation.
-/
theorem tag_program (F : Type) [Field F] (k w : ℕ) :
    ∃ port : Bool × (Fin (2 ^ k) × Fin w) ↪ slots (inputs k (word w)),
      ∀ σ : Equiv.Perm (Fin (2 ^ k)),
      ∃ cfg : (Fin (2 ^ k) × Fin w → Bool) → (Fin (2 ^ k) × Fin w → Bool) → Val (inputs k (word w)),
        (∀ (x y x' y' : Fin (2 ^ k) × Fin w → Bool) i,
          (∀ j : Fin (2 ^ k) × Fin w, port (false, j) = i → x j = x' j) →
          (∀ j : Fin (2 ^ k) × Fin w, port (true, σ j.1, j.2) = i → y j = y' j) →
          bits (inputs k (word w)) (cfg x y) i = bits (inputs k (word w)) (cfg x' y') i) ∧
        ∀ x y, tag F k (word w) (cfg x y) () = if x = y then 1 else 0 := by
  obtain ⟨P, hp⟩ := Layout.exists_tree (word w) k
  -- 推导：从 `Layout.exists_tree (row k (word w)) k` 中取出 `R, hr`。
  obtain ⟨R, hr⟩ := Layout.exists_tree (row k (word w)) k
  obtain ⟨addr, ha, hl⟩ := label_read P hp R hr
  let e : Fin w ≃ slots (word w) := Fintype.equivOfCardEq (by simp [wd_word])
  let g : Bool × (Fin (2 ^ k) × Fin w) → slots (inputs k (word w))
    | (false, i, j) => .inl (P.positions (i, e j))
    | (true, i, j) => .inr (R.positions (i, .inr (e j)))
  have hg : Function.Injective g := by
    rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ he
    cases b <;> cases b' <;> simp [g] at he ⊢ <;> exact he
  refine ⟨⟨g, hg⟩, fun σ => ?_⟩
  let payload (x : Fin (2 ^ k) × Fin w → Bool) (i : Fin (2 ^ k)) :=
    (bits (word w)).symm fun j => x (i, e.symm j)
  have hinj : Function.Injective payload := by
    intro x y eq
    funext ⟨i, j⟩
    simpa [payload] using congrFun (congrArg (bits (word w)) (congrFun eq i)) (e j)
  let cfg (x y : Fin (2 ^ k) × Fin w → Bool) : Val (inputs k (word w)) :=
    (write P (payload x), write R (fun i => (addr (σ.symm i), payload y (σ.symm i))))
  refine ⟨cfg, ?_, ?_⟩
  · rintro x y x' y' (i | i) hx hy
    -- 推导：从 `P.positions.surjective i` 中取出 `⟨r, j⟩, rfl`。
    · obtain ⟨⟨r, j⟩, rfl⟩ := P.positions.surjective i
      change bits (tree k (word w)) (write P _) _ = bits (tree k (word w)) (write P _) _
      simp only [bits_write, payload, Equiv.apply_symm_apply]
      exact hx (r, e.symm j) (by simp [g])
    · obtain ⟨⟨r, j⟩, rfl⟩ := R.positions.surjective i
      change bits (tree k (row k (word w))) (write R _) _ = bits (tree k (row k (word w))) (write R _) _
      rw [bits_write, bits_write]
      cases j with
      | inl j => rfl
      | inr j =>
        change bits (word w) (payload y _) _ = bits (word w) (payload y' _) _
        simp only [payload, Equiv.apply_symm_apply]
        exact hy (σ.symm r, e.symm j) (by simp [g])
  · intro x y
    -- 推导：记下中间结论 `he`：`R.read (label k (write P (payload x))) = fun i => (addr i, payload x i)`。
    have he : R.read (label k (write P (payload x))) = fun i => (addr i, payload x i) := by
      funext i
      rw [hl, read_write]
    simp only [cfg, tag, permuted, ← hr, he, read_write, perm_tagged addr ha, hinj.eq_iff]

end OAI.LinearAlgebra.MatrixExponent.Packing
end
