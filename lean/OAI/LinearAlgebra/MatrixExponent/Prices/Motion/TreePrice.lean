-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Field.Subfield.Basic
import OAI.LinearAlgebra.MatrixExponent.Prices.Space

/-!
以稀疏矩阵作逼近，并给出误差的显式因子分解。

**英文原文**

Sparse matrix approximation with an explicit factorization of the error.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Finset
open scoped Classical

variable {F X Y Z : Type} [Field F]

-- 读法：`Low` 表示以下条件：存在 `(I : Type) (_ : Fintype I)`，`Fintype.card I ≤ b` 与 `∃ P : Matrix X I F, ∃ Q : Matrix I Y F, M = P * Q` 同时成立。
def Low (M : Matrix X Y F) (b : ℝ) : Prop :=
  ∃ (I : Type) (_ : Fintype I), Fintype.card I ≤ b ∧
    ∃ P : Matrix X I F, ∃ Q : Matrix I Y F, M = P * Q

-- 读法：要证明的命题是 `Low (0 : Matrix X Y F) 0`。
theorem Low.zero : Low (0 : Matrix X Y F) 0 :=
  ⟨Empty, inferInstance, by simp, 0, 0, by simp⟩

-- 读法：要证明的命题是 `Low M c`。
theorem Low.mono {M : Matrix X Y F} {b c : ℝ} (h : Low M b) (he : b ≤ c) : Low M c := by
  obtain ⟨I, _, hb, H⟩ := h
  exact ⟨I, inferInstance, hb.trans he, H⟩

-- 读法：要证明的命题是 `Low (M + N) (b + c)`。
theorem Low.add {M N : Matrix X Y F} {b c : ℝ} (h : Low M b) (h' : Low N c) :
    Low (M + N) (b + c) := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h
  obtain ⟨J, _, hj, R, S, rfl⟩ := h'
  refine ⟨I ⊕ J, inferInstance, by simpa using add_le_add hi hj,
    fun x => Sum.elim (P x) (R x), Sum.elim Q S, ?_⟩
  ext x y
  change (∑ i, P x i * Q i y) + (∑ j, R x j * S j y) =
    ∑ k, Sum.elim (P x) (R x) k * (Sum.elim Q S k) y
  rw [Fintype.sum_sum_type]
  rfl

-- 读法：要证明的命题是 `Low (N * M) b`。
theorem Low.left [Fintype X] {M : Matrix X Y F} {b : ℝ} (h : Low M b) (N : Matrix Z X F) :
    Low (N * M) b := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h
  exact ⟨I, inferInstance, hi, N * P, Q, (Matrix.mul_assoc _ _ _).symm⟩

-- 读法：要证明的命题是 `Low (M * N) b`。
theorem Low.right [Fintype Y] {M : Matrix X Y F} {b : ℝ} (h : Low M b) (N : Matrix Y Z F) :
    Low (M * N) b := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h
  exact ⟨I, inferInstance, hi, P, Q * N, Matrix.mul_assoc _ _ _⟩

-- 读法：要证明的命题是 `Low M (Fintype.card Y)`。
theorem Low.full [Fintype Y] (M : Matrix X Y F) : Low M (Fintype.card Y) :=
  ⟨Y, inferInstance, le_rfl, M, 1, by simp⟩

-- 读法：要证明的命题是 `Low (M - N) (r + s)`。这里调用 `h.add`。
theorem Low.sub {M N : Matrix X Y F} {r s : ℝ} (h : Low M r) (h' : Low N s) :
    Low (M - N) (r + s) := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h'
  rw [sub_eq_add_neg]
  exact h.add ⟨I, inferInstance, hi, -P, Q, by simp⟩

-- 读法：要证明的命题是 `Low (M * N - P * Q) (r + s)`。这里调用 `hp.right`。
theorem approx_mul [Fintype X] {M N P Q : Matrix X X F} {r s : ℝ}
    (hp : Low (M - P) r) (hq : Low (N - Q) s) : Low (M * N - P * Q) (r + s) := by
  rw [show M * N - P * Q = (M - P) * N + P * (N - Q) by rw [sub_mul, mul_sub]; abel]
  exact (hp.right _).add (hq.left _)

-- 读法：在后续公式中，`Bits` 是 `Fin m → Bool` 的缩写。
/-- 给出活动寄存器以外各寄存器的逐坐标位移上界。

英文原文：Upper bound the coordinatewise displacement on all but the active
register.
-/
abbrev Bits (m : ℕ) := Fin m → Bool
-- 读法：在后续公式中，`Registers` 是 `Fin (n + 1) → Bits m` 的缩写。
abbrev Registers (n m : ℕ) := Fin (n + 1) → Bits m

variable {n m : ℕ}

-- 读法：`Near` 表示以下条件：存在 `N`，由 `Low (M - N) b ∧ ∀ x y, N x y ≠ 0` 推出 `∀ j ≠ 0, (hammingDist (x j) (y j) : ℝ) ≤ t`。
def Near (M : Matrix (Registers n m) (Registers n m) F) (t b : ℝ) : Prop :=
  ∃ N, Low (M - N) b ∧ ∀ x y, N x y ≠ 0 → ∀ j ≠ 0, (hammingDist (x j) (y j) : ℝ) ≤ t

variable {M N : Matrix (Registers n m) (Registers n m) F} {a b c d : ℝ}

-- 读法：要证明的命题是 `Near M 0 0`。
theorem Near.exact (hM : ∀ x y, M x y ≠ 0 → ∀ j ≠ 0, x j = y j) : Near M 0 0 :=
  ⟨M, by rw [sub_self]; exact Low.zero, fun x y h j hj => by simp [hM x y h j hj]⟩

-- 读法：要证明的命题是 `Near (M * N) (a + c) (b + d)`。这里调用 `approx_mul`。
theorem Near.mul (h : Near M a b) (h' : Near N c d) : Near (M * N) (a + c) (b + d) := by
  obtain ⟨P, hp, hp'⟩ := h
  obtain ⟨Q, hq, hq'⟩ := h'
  refine ⟨P * Q, ?_, fun x y hxy j hj => ?_⟩
  · exact approx_mul hp hq
  · obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero (show (∑ z, P x z * Q z y) ≠ 0 from hxy)
    calc
      _ ≤ (hammingDist (x j) (z j) : ℝ) + hammingDist (z j) (y j) := by
        exact_mod_cast hammingDist_triangle (x j) (z j) (y j)
      _ ≤ _ := add_le_add (hp' _ _ (left_ne_zero_of_mul hz) j hj)
        (hq' _ _ (right_ne_zero_of_mul hz) j hj)

-- 读法：要证明的命题是 `Near M c d`。
theorem Near.mono (h : Near M a b) (h₁ : a ≤ c) (h₂ : b ≤ d) : Near M c d := by
  obtain ⟨P, hp, hp'⟩ := h
  exact ⟨P, hp.mono h₂, fun x y h j hj => (hp' x y h j hj).trans h₁⟩

-- 读法：要证明的命题是 `Low (Matrix.diagonal (fun x : X => if x ∈ u then (1 : F) else 0)) u.card`。按 `x = y <;> simp [h]` 成立与否分情况。
theorem diag_low [DecidableEq X] (u : Finset X) :
    Low (Matrix.diagonal (fun x : X => if x ∈ u then (1 : F) else 0)) u.card := by
  refine ⟨↥u, inferInstance, by simp, fun x j => if x = j.val then 1 else 0,
    fun j y => if y = j.val then 1 else 0, ?_⟩
  ext x y
  change _ = ∑ j : u, (if x = j.val then (1 : F) else 0) * (if y = j.val then 1 else 0)
  rw [sum_coe_sort u (fun j => (if x = j then (1 : F) else 0) * (if y = j then 1 else 0))]
  by_cases h : x = y <;> simp [h]

-- 读法：要证明的命题是 `Near M a (2 * u.card)`。按 `x = y <;> by_cases hx : y ∈ u <;> simp [P, Q, he, hx]` 成立与否分情况。
/-- 删除属于例外集的行与列。

英文原文：Delete rows and columns in an exceptional set.
-/
theorem Near.crop (u : Finset (Registers n m))
    (h : ∀ x ∉ u, ∀ y ∉ u, M x y ≠ 0 → ∀ j ≠ 0, (hammingDist (x j) (y j) : ℝ) ≤ a) :
    Near M a (2 * u.card) := by
  let P := Matrix.diagonal (fun x => if x ∈ u then (1 : F) else 0)
  let Q := Matrix.diagonal (fun x => if x ∈ u then (0 : F) else 1)
  have hq : P = 1 - Q := by
    ext x y
    by_cases he : x = y <;> by_cases hx : y ∈ u <;> simp [P, Q, he, hx]
  refine ⟨Q * M * Q, ?_, fun x y hxy => ?_⟩
  · have hp : Low P u.card := diag_low u
    rw [show M - Q * M * Q = P * M + Q * M * P by rw [hq, sub_mul, mul_sub, one_mul, mul_one]; abel, two_mul]
    exact (hp.right M).add (hp.left _)
  · simp [Q, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_ite, ite_mul] at hxy
    exact h x hxy.2.1 y hxy.1 hxy.2.2

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

section
/-!
# 二元汉明球

每个不匹配处乘以一个属于 `(0,1)` 的权重因子。总质量可按坐标分解为乘积。选取两个不同的因子，就能估计小球的大小，以及词长一半的某个固定邻域外的上下两个尾部。

**英文原文**

Binary Hamming balls

Weight each mismatch by a factor in `(0,1)`. The total mass factors by
coordinate. Two choices of the factor bound small balls and both tails
outside a fixed neighborhood of half the word length.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Finset Real

-- 读法：结论为 `∑ y, r ^ hammingDist x y = (1 + r) ^ m`。
private theorem mass {m : ℕ} (x : Fin m → Bool) (r : ℝ) :
    ∑ y, r ^ hammingDist x y = (1 + r) ^ m := by
  let f (i : Fin m) (b : Bool) := if x i ≠ b then r else 1
  have hy (y : Fin m → Bool) : r ^ hammingDist x y = ∏ i, f i (y i) := by
    simp only [f, prod_ite, prod_const, one_pow, mul_one, hammingDist]
  have hi (i : Fin m) : ∑ b, f i b = 1 + r := by
    unfold f
    cases x i <;> simp [add_comm]
  simp_rw [hy]
  rw [← Fintype.prod_sum f]
  simp only [hi, prod_const, card_univ, Fintype.card_fin]

-- 读法：`(#{y | (hammingDist x y : ℝ) ≤ a * m} : ℝ)` 不超过 `(2 : ℝ) ^ (d * m)`。这里调用 `mul_le_mul_iff_left₀`。
private theorem weighted_ball {m : ℕ} (x : Fin m → Bool) {r a d : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1) (hd : log (1 + r) - a * log r ≤ d * log 2) :
    (#{y | (hammingDist x y : ℝ) ≤ a * m} : ℝ) ≤ (2 : ℝ) ^ (d * m) := by
  let S := (univ : Finset (Fin m → Bool)).filter fun y => (hammingDist x y : ℝ) ≤ a * m
  apply (mul_le_mul_iff_left₀ (exp_pos (log r * (a * m)))).mp
  calc
    _ = ∑ _ ∈ S, exp (log r * (a * m)) := by simp [S]
    _ ≤ ∑ y ∈ S, r ^ hammingDist x y := by
      apply sum_le_sum
      intro y hy
      rw [← rpow_natCast, rpow_def_of_pos hr]
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (mem_filter.mp hy).2 (log_nonpos hr.le hr'))
    _ ≤ ∑ y, r ^ hammingDist x y :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
    _ = (1 + r) ^ m := mass x r
    _ ≤ _ := by
      rw [← rpow_natCast, rpow_def_of_pos (by positivity), rpow_def_of_pos (by norm_num), ← exp_add]
      apply exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg m)]

-- 读法：存在 `t : ℝ`，由 `0 < t ∧ ∀ m : ℕ, ∀ x : Fin m` 推出 `Bool, (#{y | (hammingDist x y : ℝ) ≤ t * m} : ℝ) ≤ (2 : ℝ) ^ (δ * m)`。
theorem ball_bound {δ : ℝ} (hd : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ ∀ m : ℕ, ∀ x : Fin m → Bool,
      (#{y | (hammingDist x y : ℝ) ≤ t * m} : ℝ) ≤ (2 : ℝ) ^ (δ * m) := by
  let b := δ * log 2 / 2
  have hb : 0 < b := by unfold b; positivity
  let r := min b (1 / 2)
  have hr : 0 < r := lt_min hb (by norm_num)
  have hr' : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hk : log r < 0 := log_neg hr hr'
  refine ⟨-b / log r, div_pos_of_neg_of_neg (neg_neg_of_pos hb) hk, fun _ x => weighted_ball x hr hr'.le ?_⟩
  rw [div_mul_cancel₀ _ hk.ne]
  have he := log_le_sub_one_of_pos (show 0 < 1 + r by positivity)
  have hl : r ≤ b := min_le_left _ _
  unfold b at hl ⊢
  linarith

-- 读法：存在 `δ : ℝ`，由 `0 < δ ∧ ∀ m : ℕ, ∀ x : Fin m` 推出 `Bool, (#{y | (hammingDist x y : ℝ) ≤ a * m} : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * m)`。
private theorem below_half {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, ∀ x : Fin m → Bool,
      (#{y | (hammingDist x y : ℝ) ≤ a * m} : ℝ) ≤ (2 : ℝ) ^ ((1 - δ) * m) := by
  let r := a + 1 / 2
  have hr : 0 < r := by unfold r; linarith
  have hr' : r < 1 := by unfold r; linarith
  have h₁ := log_le_sub_one_of_pos (show 0 < (1 + r) / 2 by positivity)
  rw [log_div (by positivity) (by norm_num)] at h₁
  have h₂ := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (inv_pos.mpr hr)) hr.le
  rw [log_inv, mul_sub, mul_inv_cancel₀ hr.ne', mul_one] at h₂
  have h₃ := mul_lt_mul_of_neg_right (show a < r / 2 by unfold r; linarith) (log_neg hr hr')
  have hl : log (1 + r) - a * log r < log 2 := by linarith
  have hp : 0 < log 2 := by positivity
  refine ⟨1 - (log (1 + r) - a * log r) / log 2,
    sub_pos.mpr ((div_lt_one hp).mpr hl), fun _ x => weighted_ball x hr hr'.le ?_⟩
  rw [sub_sub_cancel, div_mul_cancel₀ _ hp.ne']

-- 读法：`hammingDist (fun _ => false) x + hammingDist (fun _ => true) x` 等于 `m`。
private theorem opposite {m : ℕ} (x : Fin m → Bool) :
    hammingDist (fun _ => false) x + hammingDist (fun _ => true) x = m := by
  have he : (univ.filter (fun i => true ≠ x i)) = univ.filter (fun i => ¬false ≠ x i) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    cases x i <;> simp
  rw [hammingDist, hammingDist, he, card_filter_add_card_filter_not]
  simp

-- 读法：存在 `δ : ℝ`，要证明的命题是 `0 < δ ∧ ∀ m : ℕ, (#{x : Fin m → Bool | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} : ℝ) ≤ 2 * (2 : ℝ) ^ ((1 - δ) * m)`。
theorem tail_bound {t : ℝ} (ht : 0 < t) : ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ,
    (#{x : Fin m → Bool | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} : ℝ) ≤
      2 * (2 : ℝ) ^ ((1 - δ) * m) := by
  let a := max 0 (1 / 2 - t)
  obtain ⟨δ, hd, hb⟩ := below_half (le_max_left _ _) (show a < 1 / 2 from max_lt (by norm_num) (by linarith))
  refine ⟨δ, hd, fun m => ?_⟩
  let S (b : Bool) := (univ : Finset (Fin m → Bool)).filter
    fun x => (hammingDist (fun _ => b) x : ℝ) ≤ a * m
  have h : ({x : Fin m → Bool | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} : Finset _) ⊆
      S false ∪ S true := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, lt_abs] at hx
    simp only [S, mem_union, mem_filter, mem_univ, true_and]
    -- 推导：记下中间结论 `he`：`(hammingDist (fun _ => false) x : ℝ) + hammingDist (fun _ => true) x = m`。
    have he : (hammingDist (fun _ => false) x : ℝ) + hammingDist (fun _ => true) x = m :=
      by exact_mod_cast opposite x
    have ha := mul_le_mul_of_nonneg_right (show 1 / 2 - t ≤ a from le_max_right _ _) (Nat.cast_nonneg m)
    rcases hx with hx | hx
    · right; linarith
    · left; linarith
  have hh := (card_le_card h).trans (card_union_le _ _)
  calc
    _ ≤ ((S false).card : ℝ) + (S true).card := by exact_mod_cast hh
    _ ≤ _ := by rw [two_mul]; exact add_le_add (hb m _) (hb m _)

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 一个参数的各有理次幂生成的域

取哈恩域的一个子域，使有理表达式具有由最低指数给出的赋值。这里只允许有限表达式。

**英文原文**

The field generated by rational powers of a parameter

Taking a subfield of the Hahn field equips rational expressions with
their lowest-exponent valuation. Only finite expressions are admitted.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

-- 读法：`seriesField` 的取值由 `Subfield.closure {x | ∃ r : ℚ, ∃ a : E, HahnSeries.single r a = x}` 给出。
def seriesField (E : Type*) [Field E] : Subfield (HahnSeries ℚ E) :=
  Subfield.closure {x | ∃ r : ℚ, ∃ a : E, HahnSeries.single r a = x}

-- 读法：在后续公式中，`K0` 是 `↥(seriesField E)` 的缩写。
abbrev K0 (E : Type*) [Field E] := ↥(seriesField E)

namespace K0

variable {E L : Type*} [Field E] [Field L]

-- 读法：`HahnSeries.single r a` 属于 `seriesField E`。使用 `Subfield.subset_closure` 给出的结论。
private theorem single_mem (r : ℚ) (a : E) : HahnSeries.single r a ∈ seriesField E :=
  Subfield.subset_closure ⟨r, a, rfl⟩

-- 读法：`C` 的取值由 `HahnSeries.C.codRestrict (seriesField E) (single_mem 0)` 给出。
def C : E →+* K0 E := HahnSeries.C.codRestrict (seriesField E) (single_mem 0)

-- 读法：`Algebra E (K0 E)` 的取值由 `C.toAlgebra` 给出。
instance : Algebra E (K0 E) := C.toAlgebra

-- 读法：`t` 的取值由 `⟨HahnSeries.single r 1, single_mem _ _⟩` 给出。
def t (r : ℚ) : K0 E := ⟨HahnSeries.single r 1, single_mem _ _⟩

-- 读法：`(t r : K0 E)` 不等于 `0`。
-- 读法：`(t 0 : K0 E)` 等于 `1`。两端由定义化简为同一项。
@[simp] theorem t_zero : (t 0 : K0 E) = 1 := rfl

@[simp] theorem t_ne_zero (r : ℚ) : (t r : K0 E) ≠ 0 :=
  fun he => HahnSeries.single_ne_zero one_ne_zero (congrArg Subtype.val he)

-- 读法：`(t (r + s) : K0 E)` 等于 `t r * t s`。按 `Subtype.ext` 的外延性准则比较各分量。
theorem t_add (r s : ℚ) : (t (r + s) : K0 E) = t r * t s := by
  apply Subtype.ext
  change HahnSeries.single (r + s) 1 = HahnSeries.single r (1 : E) * HahnSeries.single s 1
  rw [HahnSeries.single_mul_single, mul_one]

-- 读法：`(t (-r) : K0 E)` 等于 `(t r)⁻¹`。这里调用 `eq_inv_of_mul_eq_one_left`。
@[simp] theorem t_neg (r : ℚ) : (t (-r) : K0 E) = (t r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← t_add, neg_add_cancel, t_zero]

-- 读法：`(t r : K0 E) ^ n` 等于 `t (n * r)`。对 `n` 作归纳。
theorem t_pow (r : ℚ) (n : ℕ) : (t r : K0 E) ^ n = t (n * r) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, t_add, pow_succ, ih]

-- 读法：`(t r : K0 E) ^ n` 等于 `t (n * r)`。对 `n` 分类讨论。
theorem t_zpow (r : ℚ) (n : ℤ) : (t r : K0 E) ^ n = t (n * r) := by
  cases n with
  | ofNat n => simpa using t_pow (E := E) r n
  | negSucc n =>
    rw [Int.negSucc_eq, zpow_neg, Int.cast_neg, neg_mul, t_neg]
    rw [show (n : ℤ) + 1 = ↑(n + 1) by rfl, zpow_natCast]
    simpa using congrArg Inv.inv (t_pow (E := E) r (n + 1))

-- 读法：`val` 的取值由 `(HahnSeries.addVal ℚ E).comap (seriesField E).subtype` 给出。
def val (E : Type*) [Field E] : AddValuation (K0 E) (WithTop ℚ) :=
  (HahnSeries.addVal ℚ E).comap (seriesField E).subtype

-- 读法：`val E x` 等于 `(Subtype.val x).orderTop`。使用 `HahnSeries.addVal_apply` 给出的结论。
theorem val_def (x : K0 E) : val E x = (Subtype.val x).orderTop := HahnSeries.addVal_apply

-- 读法：`val E (t r)` 等于 `↑r`。通过传递性衔接 `val_def` 与 `HahnSeries.orderTop_single`。
@[simp] theorem val_t (r : ℚ) : val E (t r) = ↑r :=
  (val_def _).trans (HahnSeries.orderTop_single one_ne_zero)

-- 读法：`val E (C a)` 等于 `0`。通过传递性衔接 `val_def` 与 `HahnSeries.orderTop_single`。
@[simp] theorem val_C {a : E} (ha : a ≠ 0) : val E (C a) = 0 :=
  (val_def _).trans (HahnSeries.orderTop_single ha)

-- 读法：要证明的命题是 `P x`。对 `hx` 作归纳，采用 `Subfield.closure_induction` 的归纳原则。
theorem induction_on {P : K0 E → Prop} (x : K0 E)
    (hc : ∀ a, P (C a)) (ht : ∀ r, P (t r))
    (ha : ∀ x y, P x → P y → P (x + y)) (hn : ∀ x, P x → P (-x))
    (hi : ∀ x, P x → P x⁻¹) (hm : ∀ x y, P x → P y → P (x * y)) : P x := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨r, a, rfl⟩ := hx
    have he : (⟨HahnSeries.single r a, single_mem r a⟩ : K0 E) = t r * C a := by
      apply Subtype.ext
      change _ = HahnSeries.single r (1 : E) * HahnSeries.single 0 a
      rw [HahnSeries.single_mul_single, one_mul, add_zero]
    rw [he]
    exact hm _ _ (ht r) (hc a)
  | one => exact ht 0
  | add x y hx hy h k => exact ha ⟨x, hx⟩ ⟨y, hy⟩ h k
  | neg x hx h => exact hn ⟨x, hx⟩ h
  | inv x hx h => exact hi ⟨x, hx⟩ h
  | mul x y hx hy h k => exact hm ⟨x, hx⟩ ⟨y, hy⟩ h k

-- 读法：`f` 等于 `g`。按 `RingHom.ext` 的外延性准则比较各分量。
@[ext] theorem hom_ext {f g : K0 E →+* L} (hC : ∀ a, f (C a) = g (C a))
    (ht : ∀ r, f (t r) = g (t r)) : f = g := by
  apply RingHom.ext
  intro x
  induction x using induction_on with
  | hc a => exact hC a
  | ht r => exact ht r
  | ha _ _ h k => rw [map_add, map_add, h, k]
  | hn _ h => rw [map_neg, map_neg, h]
  | hi _ h => rw [map_inv₀, map_inv₀, h]
  | hm _ _ h k => rw [map_mul, map_mul, h, k]

end K0
end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 有理圆盘树及其叶节点度量

**英文原文**

The rational disk tree and its leaf metric
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
variable {E : Type*} [Field E]

-- 读法：在后续公式中，`Depth` 是 `{l : ℚ // l ≤ 1}` 的缩写。
abbrev Depth := {l : ℚ // l ≤ 1}

-- 读法：在后续公式中，`diskPoint` 是 `K0 E × Depth` 的缩写。
abbrev diskPoint (E : Type*) [Field E] := K0 E × Depth

-- 读法：`leaf` 的取值由 `(z, ⟨1, le_rfl⟩)` 给出。
def leaf (z : K0 E) : diskPoint E := (z, ⟨1, le_rfl⟩)

-- 读法：`diskGap` 的取值由 `a + b - 2 * min (min a b) ((val E (x - y)).untopD 1)` 给出。
def diskGap (x y : K0 E) (a b : ℚ) : ℚ :=
  a + b - 2 * min (min a b) ((val E (x - y)).untopD 1)

-- 读法：`diskDist` 的取值由 `diskGap x.1 y.1 x.2.val y.2.val` 给出。
def diskDist (x y : diskPoint E) : ℚ := diskGap x.1 y.1 x.2.val y.2.val

-- 读法：`diskDist x y` 等于 `diskDist y x`。
theorem diskDist_comm (x y : diskPoint E) : diskDist x y = diskDist y x := by
  unfold diskDist diskGap
  rw [add_comm, min_comm x.2.val, AddValuation.map_sub_swap]

-- 读法：`diskDist x x` 等于 `0`。
@[simp] theorem diskDist_self (x : diskPoint E) : diskDist x x = 0 := by
  simp [diskDist, diskGap, min_eq_left x.2.property, two_mul]

-- 读法：`diskDist (leaf x) (leaf y)` 等于 `2 * max (1 - r) 0`。
theorem leaf_dist {x y : K0 E} {r : ℚ} (h : val E (x - y) = ↑r) :
    diskDist (leaf x) (leaf y) = 2 * max (1 - r) 0 := by
  simp only [diskDist, diskGap, leaf, min_self, h, WithTop.untopD_coe]
  rcases le_total 1 r with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# 系数变换与赋值伸缩

**英文原文**

Changes of coefficients and dilation of valuations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
variable {E L : Type*} [Field E] [Field L]

-- 读法：`restrictSeries` 的结果类型为 `K0 E →+* K0 L`。
private def restrictSeries (f : HahnSeries ℚ E →+* HahnSeries ℚ L)
    (h : ∀ r a, f (HahnSeries.single r a) ∈ seriesField L) : K0 E →+* K0 L :=
  (f.comp (seriesField E).subtype).codRestrict (seriesField L) fun x => by
    have H : seriesField E ≤ (seriesField L).comap f :=
      Subfield.closure_le.mpr (by rintro _ ⟨r, a, rfl⟩; exact h r a)
    exact H x.property

-- 读法：用字段 `toFun`、`map_add'`、`map_mul'`、`map_zero'` 构造 `HahnSeries ℚ E →+* HahnSeries ℚ L`。
private def mapSeries (φ : E →+* L) : HahnSeries ℚ E →+* HahnSeries ℚ L where
  toFun x := x.map φ
  map_add' x y := by ext; simp
  map_mul' _ _ := HahnSeries.map_mul φ.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_one' := by ext i; simp [HahnSeries.coeff_one, apply_ite]

-- 读法：`mapSeries φ (HahnSeries.single r a)` 等于 `HahnSeries.single r (φ a)`。按 `i = r <;> simp [h]` 成立与否分情况。
private theorem mapSeries_single (φ : E →+* L) (r : ℚ) (a : E) :
    mapSeries φ (HahnSeries.single r a) = HahnSeries.single r (φ a) := by
  ext i
  change φ ((HahnSeries.single r a).coeff i) = _
  by_cases h : i = r <;> simp [h]

-- 读法：`map` 的结果类型为 `K0 E →+* K0 L`。
def map (φ : E →+* L) : K0 E →+* K0 L :=
  restrictSeries (mapSeries φ) fun r a => by
    rw [mapSeries_single]
    exact Subfield.subset_closure ⟨r, φ a, rfl⟩

-- 读法：`map φ (C a)` 等于 `C (φ a)`。使用 `Subtype.ext` 给出的结论。
@[simp] theorem map_C (φ : E →+* L) (a : E) : map φ (C a) = C (φ a) :=
  Subtype.ext (mapSeries_single φ 0 a)

-- 读法：`map φ (t r)` 等于 `t r`。通过传递性衔接 `Subtype.ext` 与 `congrArg`。
@[simp] theorem map_t (φ : E →+* L) (r : ℚ) : map φ (t r) = t r :=
  Subtype.ext ((mapSeries_single φ r 1).trans (congrArg _ φ.map_one))

-- 读法：`val L (map φ x)` 等于 `val E x`。这里调用 `map_ne_zero`。
@[simp] theorem val_map (φ : E →+* L) (x : K0 E) : val L (map φ x) = val E x := by
  have e : (Subtype.val (map φ x)).support = (Subtype.val x).support := by
    ext i
    change φ ((Subtype.val x).coeff i) ≠ 0 ↔ (Subtype.val x).coeff i ≠ 0
    exact map_ne_zero φ
  rw [val_def, val_def]
  by_cases h : x = 0
  · simp [h]
  have hu : Subtype.val x ≠ 0 := fun he => h (Subtype.ext he)
  have hv : Subtype.val (map φ x) ≠ 0 := fun he => (map_ne_zero (map φ)).mpr h (Subtype.ext he)
  simp only [HahnSeries.orderTop_of_ne_zero hu, HahnSeries.orderTop_of_ne_zero hv, e]

-- 读法：`expand` 的结果类型为 `HahnSeries ℚ E →+* HahnSeries ℚ E`。
private def expand (d : ℚ) (hd : 0 < d) : HahnSeries ℚ E →+* HahnSeries ℚ E :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft d) (fun _ _ => mul_left_cancel₀ hd.ne')
    (fun _ _ => mul_le_mul_iff_right₀ hd)

-- 读法：`expand d hd (HahnSeries.single r a)` 等于 `HahnSeries.single (d * r) a`。使用 `HahnSeries.embDomain_single` 给出的结论。
private theorem expand_single (d : ℚ) (hd : 0 < d) (r : ℚ) (a : E) :
    expand d hd (HahnSeries.single r a) = HahnSeries.single (d * r) a :=
  HahnSeries.embDomain_single

-- 读法：`dilate` 的结果类型为 `K0 E →+* K0 E`。
def dilate (d : ℚ) (hd : 0 < d) : K0 E →+* K0 E :=
  restrictSeries (expand d hd) fun r a => by
    rw [expand_single]
    exact Subfield.subset_closure ⟨d * r, a, rfl⟩

-- 读法：`dilate d hd (C a)` 等于 `C a`。按 `Subtype.ext` 的外延性准则比较各分量。
@[simp] theorem dilate_C (d : ℚ) (hd : 0 < d) (a : E) : dilate d hd (C a) = C a := by
  apply Subtype.ext
  change expand d hd (HahnSeries.single 0 a) = HahnSeries.single 0 a
  rw [expand_single, mul_zero]

-- 读法：`dilate d hd (t r : K0 E)` 等于 `t (d * r)`。使用 `Subtype.ext` 给出的结论。
@[simp] theorem dilate_t (d : ℚ) (hd : 0 < d) (r : ℚ) :
    dilate d hd (t r : K0 E) = t (d * r) :=
  Subtype.ext (expand_single d hd r 1)

-- 读法：`val E (dilate d hd x)` 等于 `WithTop.map (fun r => d * r) (val E x)`。这里调用 `HahnSeries.orderTop_embDomain`。
theorem val_dilate (d : ℚ) (hd : 0 < d) (x : K0 E) :
    val E (dilate d hd x) = WithTop.map (fun r => d * r) (val E x) := by
  rw [val_def, val_def]
  exact HahnSeries.orderTop_embDomain

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
二进制寄存器的互换可以用三次剪切再加一次符号变换实现。

**英文原文**

Binary register swap as three shears followed by a sign change.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Finset
open scoped Classical

variable {F X I : Type} [Field F] [Fintype I] [DecidableEq I] [Fintype X]

-- 读法：输入 `x y` 时返回 `∏ i, M i (x i) (y i)`。
def matPower (M : I → Matrix X X F) : Matrix (I → X) (I → X) F :=
  fun x y => ∏ i, M i (x i) (y i)

-- 读法：`matPower (fun i => M i * N i)` 等于 `matPower M * matPower N`。
theorem matPower_mul (M N : I → Matrix X X F) :
    matPower (fun i => M i * N i) = matPower M * matPower N := by
  ext x y
  simp only [matPower, Matrix.mul_apply, Fintype.prod_sum, prod_mul_distrib]

variable {n m : ℕ}

-- 读法：在后续公式中，`Col` 是 `Fin (n + 1) → Bool` 的缩写。
abbrev Col (n : ℕ) := Fin (n + 1) → Bool
-- 读法：在后续公式中，`Op` 是 `Matrix (Registers n m) (Registers n m) F` 的缩写。
abbrev Op (F : Type) (n m : ℕ) := Matrix (Registers n m) (Registers n m) F

-- 读法：`swap` 的取值由 `x ∘ Equiv.swap 0 i` 给出。
def swap (i : Fin (n + 1)) (x : Fin (n + 1) → X) := x ∘ Equiv.swap 0 i

omit [Fintype X] in
-- 读法：`swap i (swap i x)` 等于 `x`。用函数外延性比较等号两侧在 `fun _ => congrArg x (Equiv.swap_apply_self _ _ _)` 处的取值。
@[simp] theorem swap_swap (i : Fin (n + 1)) (x : Fin (n + 1) → X) : swap i (swap i x) = x :=
  funext fun _ => congrArg x (Equiv.swap_apply_self _ _ _)

-- 读法：当 `y = swap i x` 成立时取 `1`，否则取 `0`。
def exchange (F X : Type) [Field F] [DecidableEq X] (i : Fin (n + 1)) :
    Matrix (Fin (n + 1) → X) (Fin (n + 1) → X) F := fun x y => if y = swap i x then 1 else 0

-- 读法：输入 `i` 时返回 `x i b`。
def column (x : Registers n m) (b : Fin m) : Col n := fun i => x i b

-- 读法：输入 `x y` 时返回 `∏ b, A (column x b) (column y b)`。
def parallel (m : ℕ) (A : Matrix (Col n) (Col n) F) : Op F n m :=
  fun x y => ∏ b, A (column x b) (column y b)

-- 读法：`parallel m (A * B)` 等于 `parallel m A * parallel m B`。这里调用 `e.sum_comp`。
theorem parallel_mul (A B : Matrix (Col n) (Col n) F) :
    parallel m (A * B) = parallel m A * parallel m B := by
  ext x y
  simp only [parallel, Matrix.mul_apply, Fintype.prod_sum, prod_mul_distrib]
  let e := Equiv.piComm (fun (_ : Fin (n + 1)) (_ : Fin m) => Bool)
  exact (e.sum_comp _).symm

-- 读法：`parallel m (exchange F Bool i)` 等于 `exchange F (Bits m) i`。按 `y = swap i x` 成立与否分情况。
theorem parallel_exchange (i : Fin (n + 1)) :
    parallel m (exchange F Bool i) = exchange F (Bits m) i := by
  ext x y
  change (∏ b, if column y b = swap i (column x b) then (1 : F) else 0) =
    if y = swap i x then 1 else 0
  by_cases h : y = swap i x
  · rw [ite_eq_left h]
    exact prod_eq_one (fun _ _ => ite_eq_left (by rw [h]; rfl))
  · rw [ite_eq_right h]
    obtain ⟨a, b, he⟩ : ∃ a b, y a b ≠ swap i x a b := by simpa [funext_iff] using h
    exact prod_eq_zero (mem_univ b) (ite_eq_right fun e => he (congrFun e a))

-- 读法：`starts` 表示以下条件：`x 0 = b` 与 `x i ≠ b` 同时成立。
def starts (i : Fin (n + 1)) (b : Bool) (x : Col n) : Prop := x 0 = b ∧ x i ≠ b

-- 读法：输入 `x y` 时返回 `(if y = x then 1 else 0) + if starts i b x then (if y = swap i x then v else 0) else 0`。
def shear (i : Fin (n + 1)) (b : Bool) (v : F) : Matrix (Col n) (Col n) F :=
  fun x y => (if y = x then 1 else 0) +
    if starts i b x then (if y = swap i x then v else 0) else 0

-- 读法：`(shear i b v * A) x y` 等于 `A x y + if starts i b x then v * A (swap i x) y else 0`。使用 `by_cases` 给出的结论。
private theorem shear_mul (i : Fin (n + 1)) (b : Bool) (v : F)
    (A : Matrix (Col n) (Col n) F) (x y : Col n) :
    (shear i b v * A) x y = A x y + if starts i b x then v * A (swap i x) y else 0 := by
  by_cases h : starts i b x <;> simp [Matrix.mul_apply, shear, h, add_mul, sum_add_distrib, ite_mul]

-- 读法：`signs` 的取值由 `Matrix.diagonal fun x => if starts i false x then -1 else 1` 给出。
def signs (F : Type) [Field F] (i : Fin (n + 1)) : Matrix (Col n) (Col n) F :=
  Matrix.diagonal fun x => if starts i false x then -1 else 1

-- 读法：`exchange F Bool i` 等于 `shear i false 1 * (shear i true (-1) * (shear i false 1 * signs F i))`。用函数外延性比较等号两侧在 `a` 处的取值。
theorem exchange_shears (i : Fin (n + 1)) :
    exchange F Bool i = shear i false 1 * (shear i true (-1) * (shear i false 1 * signs F i)) := by
  ext x y
  simp only [shear_mul, swap_swap, one_mul, neg_one_mul, exchange]
  have h₁ : swap i x 0 = x i := by simp [swap]
  have h₂ : swap i x i = x 0 := by simp [swap]
  have hsame (h : x 0 = x i) : swap i x = x := by
    funext a
    simp only [swap, Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have hd (a : Col n) : signs F i a y =
      if y = a then (if starts i false a then -1 else 1) else 0 := by
    simp only [signs, Matrix.diagonal_apply, eq_comm (a := a)]
  simp only [hd, starts, h₁, h₂]
  rcases Bool.dichotomy (x 0) with h₀|h₀ <;> rcases Bool.dichotomy (x i) with hi|hi <;> simp [h₀, hi] at hsame ⊢ <;>
    first | rw [hsame] | split_ifs <;> ring

-- 读法：要证明的命题是 `Near (parallel m (signs F i)) 0 0`。这里调用 `Near.exact`。
theorem near_signs (i : Fin (n + 1)) : Near (parallel m (signs F i)) 0 0 := by
  apply Near.exact
  intro x y h j _
  funext b
  have hb := prod_ne_zero_iff.mp h b (mem_univ b)
  by_contra he
  exact hb (Matrix.diagonal_apply_ne _ (fun he' => he (congrFun he' j)))

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 将剪切阶段限制在典型词上

在一次剪切中，每个被改变的比特都使活动寄存器沿同一方向移动。若两个端点的重量均为典型值，则只有少量比特可以改变。例外行和例外列各自所占的比例呈指数级衰减。

**英文原文**

Restricting shear stages to typical words

In a shear every changed bit moves the active register in the same
direction. If both endpoints have typical weight, few bits can change.
The exceptional rows and columns have exponentially small relative size.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Finset
open scoped Classical

variable {F : Type} [Field F] {n m : ℕ}

-- 读法：`weight` 的取值由 `hammingDist (fun _ => false) (x 0)` 给出。
private def weight (x : Registers n m) : ℝ := hammingDist (fun _ => false) (x 0)

-- 读法：`(hammingDist x y : ℝ)` 等于 `∑ b, if x b = y b then 0 else 1`。
private theorem count_dist (x y : Bits m) :
    (hammingDist x y : ℝ) = ∑ b, if x b = y b then 0 else 1 := by
  simp [hammingDist, sum_ite]

-- 读法：`(hammingDist (x j) (y j) : ℝ)` 不超过 `|weight y - weight x|`。按 `w = u` 成立与否分情况。
private theorem shear_dist (i : Fin (n + 1)) (b : Bool) (v : F) (x y : Registers n m)
    (h : parallel m (shear i b v) x y ≠ 0) (j : Fin (n + 1)) :
    (hammingDist (x j) (y j) : ℝ) ≤ |weight y - weight x| := by
  let s : ℝ := if b then -1 else 1
  have step (u w : Col n) (h : shear i b v u w ≠ 0) :
      (if u j = w j then (0 : ℝ) else 1) ≤
        s * ((if false = w 0 then 0 else 1) - (if false = u 0 then 0 else 1)) := by
    by_cases he : w = u
    · simp [he]
    have hh : starts i b u ∧ w = swap i u := by
      by_contra hh
      by_cases h' : starts i b u <;> simp_all [shear]
    -- 推导：记下中间结论 `h₀`：`u 0 = b`。
    have h₀ : u 0 = b := hh.1.1
    have h₁ : w 0 ≠ b := by simpa [hh.2, swap] using hh.1.2
    cases b <;> simp [s, h₀, h₁] <;> split_ifs <;> norm_num
  have hs : (hammingDist (x j) (y j) : ℝ) ≤ s * (weight y - weight x) := by
    simp only [weight, count_dist, ← sum_sub_distrib, mul_sum]
    exact sum_le_sum fun k hk => step _ _ (prod_ne_zero_iff.mp h k hk)
  cases b
  · exact hs.trans (by simpa [s] using le_abs_self (weight y - weight x))
  · exact hs.trans (by simpa [s] using neg_le_abs (weight y - weight x))

-- 读法：`bad` 的取值由 `{x | t * m < |weight x - (m : ℝ) / 2|}` 给出。
private def bad (n m : ℕ) (t : ℝ) : Finset (Registers n m) :=
  {x | t * m < |weight x - (m : ℝ) / 2|}

-- 读法：要证明的命题是 `Near (parallel m (shear i b v)) (2 * (t * m)) (2 * (bad n m t).card)`。这里调用 `Near.crop`。
private theorem near_shear (i : Fin (n + 1)) (t : ℝ) (b : Bool) (v : F) :
    Near (parallel m (shear i b v)) (2 * (t * m)) (2 * (bad n m t).card) := by
  apply Near.crop
  intro x hx y hy h j _
  simp only [bad, mem_filter, mem_univ, true_and, not_lt] at hx hy
  refine (shear_dist i b v x y h j).trans ?_
  rw [abs_le] at hx hy ⊢
  constructor <;> linarith

-- 读法：`(bad n m t).card` 不超过 `#{x : Bits m | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} * 2 ^ (m * n)`。这里调用 `mem_product.mpr`。
private theorem bad_count (n m : ℕ) (t : ℝ) :
    (bad n m t).card ≤
      #{x : Bits m | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} * 2 ^ (m * n) := by
  let S : Finset (Bits m) :=
    {x | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|}
  let e := (Fin.consEquiv (fun _ : Fin (n + 1) => Bits m)).symm
  have h : (bad n m t).image e ⊆ S ×ˢ univ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩, mem_univ _⟩
  simpa [card_image_of_injective _ e.injective, Bits, S, pow_mul] using card_le_card h

-- 读法：存在 `c : ℝ`，要证明的命题是 `0 < c ∧ c ≤ 1 ∧ ∀ (m : ℕ) (i : Fin (n + 1)), Near (exchange F (Bits m) i) (6 * (t * m)) (12 * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * m))`。
theorem near_exchange (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (m : ℕ) (i : Fin (n + 1)),
      Near (exchange F (Bits m) i) (6 * (t * m)) (12 * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * m)) := by
  obtain ⟨δ, hδ, h⟩ := tail_bound ht
  let c := min 1 δ
  refine ⟨c, lt_min zero_lt_one hδ, min_le_left _ _, fun m i => ?_⟩
  have he : ((bad n m t).card : ℝ) ≤ 2 * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * m) := calc
    _ ≤ (#{x : Bits m | t * m < |(hammingDist (fun _ => false) x : ℝ) - (m : ℝ) / 2|} : ℝ) *
      (2 : ℝ) ^ (m * n) := by exact_mod_cast bad_count n m t
    _ ≤ 2 * (2 : ℝ) ^ ((1 - δ) * m) * (2 : ℝ) ^ (m * n) := mul_le_mul_of_nonneg_right (h m) (by positivity)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), Nat.cast_mul]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_right (show c ≤ δ from min_le_right _ _) (Nat.cast_nonneg m)]
  rw [← parallel_exchange, exchange_shears, parallel_mul, parallel_mul, parallel_mul]
  have hf := near_shear (m := m) i t false (1 : F)
  have hg := near_shear (m := m) i t true (-1 : F)
  exact (hf.mul (hg.mul (hf.mul (near_signs i)))).mono (by linarith) (by linarith)

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 单个活动寄存器

用互换变换对单寄存器矩阵作共轭，使所有稠密运算都作用于零号寄存器。无论基矩阵多大，都只需固定次数的近似互换。

**英文原文**

One active register

Conjugate the single-register matrix by a swap, so that all dense
operations act on register zero. Only a fixed number of approximate
swaps is needed, independently of the size of the base matrix.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Finset
open scoped Classical

variable {F : Type} [Field F] {n m : ℕ}

-- 读法：`applyAt` 的取值由 `matPower (fun j => if j = i then B else 1)` 给出。
private def applyAt (B : Matrix (Bits m) (Bits m) F) (i : Fin (n + 1)) : Op F n m :=
  matPower (fun j => if j = i then B else 1)

-- 读法：`applyAt B i` 等于 `exchange F (Bits m) i * applyAt B 0 * exchange F (Bits m) i`。
private theorem conjugate (B : Matrix (Bits m) (Bits m) F) (i : Fin (n + 1)) :
    applyAt B i = exchange F (Bits m) i * applyAt B 0 * exchange F (Bits m) i := by
  ext x y
  have h (z : Registers n m) : y = swap i z ↔ z = swap i y := by
    constructor <;> rintro rfl <;> simp
  simp only [Matrix.mul_apply, exchange, h, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  simp only [sum_ite_eq', mem_univ, ite_true]
  unfold applyAt matPower
  rw [← Equiv.prod_comp (Equiv.swap 0 i)]
  refine prod_congr rfl fun j _ => ?_
  have hj : Equiv.swap 0 i j = i ↔ j = 0 := by
    rw [← (Equiv.swap 0 i).injective.eq_iff (a := j), Equiv.swap_apply_left]
  simp [swap, hj]

-- 读法：要证明的命题是 `Near (applyAt B (0 : Fin (n + 1))) 0 0`。这里调用 `Near.exact`。
private theorem local_exact (B : Matrix (Bits m) (Bits m) F) :
    Near (applyAt B (0 : Fin (n + 1))) 0 0 := by
  apply Near.exact
  intro x y h j hj
  unfold applyAt matPower at h
  have hn := prod_ne_zero_iff.mp h j (mem_univ _)
  simpa [hj, Matrix.one_apply] using hn

-- 读法：要证明的命题是 `Near (matPower (fun _ : Fin (n + 1) => B)) (2 * (n + 1) * a) (2 * (n + 1) * b)`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
private theorem parallel_near (B : Matrix (Bits m) (Bits m) F) {a b : ℝ}
    (h : ∀ i : Fin (n + 1), Near (exchange F (Bits m) i) a b) :
    Near (matPower (fun _ : Fin (n + 1) => B)) (2 * (n + 1) * a) (2 * (n + 1) * b) := by
  let T (s : Finset (Fin (n + 1))) := matPower (fun i => if i ∈ s then B else 1)
  have go (s : Finset (Fin (n + 1))) : Near (T s) (2 * s.card * a) (2 * s.card * b) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [card_empty, Nat.cast_zero, mul_zero, zero_mul]
      apply Near.exact
      intro x y h j _
      have hn := prod_ne_zero_iff.mp h j (mem_univ _)
      simpa [Matrix.one_apply] using hn
    | @insert i s hi ih =>
      -- 推导：记下中间结论 `eq`：`T (insert i s) = applyAt B i * T s`。
      have eq : T (insert i s) = applyAt B i * T s := by
        unfold T applyAt
        rw [← matPower_mul]
        congr 1
        funext j
        by_cases he : j = i <;> simp [he, hi]
      rw [eq, conjugate, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      exact ((((h i).mul (local_exact B)).mul (h i)).mul ih).mono (by linarith) (by linarith)
  simpa [T] using go univ

-- 读法：`S.card` 不超过 `2 ^ (2 * m)`。按 `i = 0` 成立与否分情况。
private theorem row_size (n m : ℕ) (x : Registers n m) (t : ℝ)
    (S : Finset (Registers n m))
    (h : ∀ y ∈ S, ∀ i ≠ 0, (hammingDist (x i) (y i) : ℝ) ≤ t * m)
    (hb : ∀ u : Bits m, (#{v | (hammingDist u v : ℝ) ≤ t * m} : ℝ) ≤
      (2 : ℝ) ^ ((1 / ((n : ℝ) + 1)) * m)) : S.card ≤ 2 ^ (2 * m) := by
  let B (i : Fin (n + 1)) : Finset (Bits m) :=
    if i = 0 then univ else univ.filter fun v => (hammingDist (x i) v : ℝ) ≤ t * m
  have hsub : S ⊆ Fintype.piFinset B := by
    intro y hy
    refine Fintype.mem_piFinset.mpr fun i => ?_
    by_cases hi : i = 0
    · simp [B, hi]
    · simpa [B, hi] using h y hy i hi
  have hcard := card_le_card hsub
  rw [Fintype.card_piFinset, Fin.prod_univ_succ] at hcard
  -- 推导：记下中间结论 `hz`：`(B 0).card = 2 ^ m`。
  have hz : (B 0).card = 2 ^ m := by simp [B, Bits]
  have htail : (∏ i : Fin n, ((B i.succ).card : ℝ)) ≤ (2 : ℝ) ^ m := calc
    _ ≤ ∏ _i : Fin n, (2 : ℝ) ^ ((1 / ((n : ℝ) + 1)) * m) := by
      refine prod_le_prod₀ (by intros; positivity) fun i _ => ?_
      simpa [B] using hb (x i.succ)
    _ ≤ _ := by
      simp only [prod_const, card_univ, Fintype.card_fin]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [show 1 / ((n : ℝ) + 1) * m * n = (m * n) / ((n : ℝ) + 1) by ring, div_le_iff₀ (by positivity)]
      nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  -- 推导：记下中间结论 `ht`：`∏ i : Fin n, (B i.succ).card ≤ 2 ^ m`。
  have ht : ∏ i : Fin n, (B i.succ).card ≤ 2 ^ m := by exact_mod_cast htail
  rw [hz] at hcard
  rw [two_mul, pow_add]
  exact hcard.trans (Nat.mul_le_mul_left _ ht)

-- 读法：结论为 `∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 ≤ C ∧ ∀ m (B : Matrix (Bits m) (Bits m) F), ∃ D : Op F n m, Low (matPower (fun _ : Fin (n + 1) => B) - D) (C * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * m)) ∧ ∀ x, #{y | D x y ≠ 0} ≤ 2 ^ (2 * m)`。
theorem sparse_power (n : ℕ) : ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 ≤ C ∧
    ∀ m (B : Matrix (Bits m) (Bits m) F), ∃ D : Op F n m,
      Low (matPower (fun _ : Fin (n + 1) => B) - D) (C * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * m)) ∧
      ∀ x, #{y | D x y ≠ 0} ≤ 2 ^ (2 * m) := by
  obtain ⟨t, ht, hb⟩ := ball_bound (by positivity : 0 < 1 / ((n : ℝ) + 1))
  let u := t / (12 * ((n : ℝ) + 1))
  obtain ⟨c, hc, hc', he⟩ := near_exchange (F := F) n (show 0 < u by positivity)
  refine ⟨c, 24 * ((n : ℝ) + 1), hc, hc', by positivity, fun m B => ?_⟩
  obtain ⟨D, hd, hD⟩ := parallel_near B (he m)
  refine ⟨D, hd.mono (by linarith), fun x => row_size n m x t _ ?_ (hb m)⟩
  intro y hy i hi
  refine (hD x y (mem_filter.mp hy).2 i hi).trans_eq ?_
  unfold u
  field_simp
  ring

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 圆盘树上的标签速率

一个星形将任意的中心值与某些端点的值作比较。无需指定某个特定的超越参数。

**英文原文**

Label rates on a tree of disks

A star compares an arbitrary center value with some values at the
ends. No particular choice of a transcendental parameter is needed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

open Spectral

variable {E : Type*} [Field E]

-- 读法：在后续公式中，`Four` 是 `Fin 4 → α` 的缩写。
abbrev Four (α : Type*) := Fin 4 → α

-- 读法：输入 `i` 时返回 `a i + b i * u`。
def diskAffine (a b : Four (K0 E)) (u : K0 E) : Four (K0 E) := fun i => a i + b i * u

-- 读法：逐一匹配以下输入模式：`none`、`some j`。
def armEnd {n : ℕ} (c : Fin n → K0 E) (r : Option (Fin n) → ℚ) (u : K0 E) :
    Option (Fin n) → K0 E
  | none => t (-r none) * u
  | some j => c j + t (r (some j)) * u

-- 读法：结构的字段包括 `rate`、`realized`、`chord`、`star`。
structure MotionTree (F : Type) [Field F] (E : Type*) [Field E] where
  rate : Four (K0 E) → Four ℚ → ℝ
  realized (x : Four (K0 E)) (l : Four ℚ) (hl : ∀ i, l i ≤ 1) :
    ∃ D : ℝ, ∃ P ∈ Tensor.ordinary F (Fin 4) D, P 2 = rate x l ∧
      ∀ i j, P (Tensor.wire F i j 2) = (diskGap (x i) (x j) (l i) (l j) : ℝ)
  chord (x y z : Four (K0 E)) (l m k : Four ℚ)
    (hl : ∀ i, l i ≤ 1) (hm : ∀ i, m i ≤ 1) (hk : ∀ i, k i ≤ 1)
    (θ : ℚ) (h₀ : 0 ≤ θ) (h₁ : θ ≤ 1)
    (left : ∀ i, diskGap (x i) (z i) (l i) (k i) = θ * diskGap (x i) (y i) (l i) (m i))
    (right : ∀ i, diskGap (z i) (y i) (k i) (m i) = (1 - θ) * diskGap (x i) (y i) (l i) (m i)) :
    rate z k ≤ (1 - (θ : ℝ)) * rate x l + θ * rate y m
  star {n : ℕ} (a b : Four (K0 E)) (c : Fin n → K0 E)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (r : Option (Fin n) → ℚ) (hr : ∀ j, 0 < r j)
    (l : Four ℚ) (k : Option (Fin n) → Four ℚ)
    (hl : ∀ i, l i ≤ 1) (hk : ∀ j i, k j i ≤ 1)
    (harmonic : ∀ i, ∑ j, (k j i - l i) / r j = 0) (v : K0 E) (hv : 0 ≤ val E v) :
    ∃ u : Option (Fin n) → K0 E, (∀ j, 0 ≤ val E (u j)) ∧
      0 ≤ ∑ j, (rate (diskAffine a b (armEnd c r (u j) j)) (k j) -
        rate (diskAffine a b v) l) / (r j : ℝ)

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
利用由三条连线构成的路径估计对角成本。

**英文原文**

Bounds on the diagonal cost from paths of three wires.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

open Spectral Finset

variable {F : Type} [Field F] {E : Type*} [Field E]

-- 读法：`P 2` 不超过 `P (Tensor.wire F a b 2) + P (Tensor.wire F b c 2) + P (Tensor.wire F c d 2)`。
private theorem path_cost {D : ℝ} {P : Tensor F (Fin 4) → ℝ}
    (h : P ∈ Tensor.ordinary F (Fin 4) D) (a b c d : Fin 4)
    (ha : ({a, b, c, d} : Finset (Fin 4)) = univ) :
    P 2 ≤ P (Tensor.wire F a b 2) + P (Tensor.wire F b c 2) + P (Tensor.wire F c d 2) := by
  let W (a b : Fin 4) := Tensor.wire F a b 2
  have h₁ := Tensor.shared_join F (U := {a, b}) (V := {b, c, d}) (c := b) (by simp) (by simp) 2
  have h₂ := Tensor.shared_join F (U := {b, c}) (V := {c, d}) (c := c) (by simp) (by simp) 2
  rw [show ({a, b} : Finset (Fin 4)) ∪ {b, c, d} = univ by rw [← ha]; ext; simp; tauto, Tensor.shared_all] at h₁
  rw [show ({b, c} : Finset (Fin 4)) ∪ {c, d} = {b, c, d} by simp] at h₂
  have h₃ : (2 : Tensor F (Fin 4)) ≤ W a b * (W b c * W c d) :=
    h₁.trans (Tensor.mul_le_mul_left _ _ _ h₂)
  -- 推导：从 `h` 中取出 `s, hs, f, hf, rfl`。
  obtain ⟨s, hs, f, hf, rfl⟩ := h
  have hpos (i j : Fin 4) : 0 < f (W i j) := by
    rw [show f (W i j) = _ from Tensor.price_wire f hf _ _ (by decide : 0 < 2)]
    positivity
  have he := Real.log_le_log (show 0 < f 2 by rw [map_ofNat]; norm_num) (hf h₃)
  rw [f.map_mul, f.map_mul, Real.log_mul (hpos _ _).ne' (mul_ne_zero (hpos _ _).ne' (hpos _ _).ne'),
    Real.log_mul (hpos _ _).ne' (hpos _ _).ne'] at he
  have he' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) hs.1
  simpa only [Tensor.values, W, add_div, mul_add, add_assoc] using he'

namespace MotionTree
variable (H : MotionTree F E)

-- 读法：`H.rate x l` 不超过 `(diskGap (x a) (x b) (l a) (l b) + diskGap (x b) (x c) (l b) (l c) + diskGap (x c) (x d) (l c) (l d) : ℚ)`。这里调用 `path_cost`。
theorem path (x : Four (K0 E)) (l : Four ℚ) (hl : ∀ i, l i ≤ 1)
    (a b c d : Fin 4) (ha : ({a, b, c, d} : Finset (Fin 4)) = univ) :
    H.rate x l ≤ (diskGap (x a) (x b) (l a) (l b) + diskGap (x b) (x c) (l b) (l c) +
      diskGap (x c) (x d) (l c) (l d) : ℚ) := by
  obtain ⟨D, P, hP, he, hw⟩ := H.realized x l hl
  simpa only [he, hw, Rat.cast_add] using path_cost hP a b c d ha

-- 读法：`0` 不超过 `H.rate x l`。这里调用 `Tensor.values_nonneg`。
theorem nonneg (x : Four (K0 E)) (l : Four ℚ) (hl : ∀ i, l i ≤ 1) : 0 ≤ H.rate x l := by
  obtain ⟨D, P, ⟨d, hd, f, hf, rfl⟩, he, _⟩ := H.realized x l hl
  rw [← he]
  exact Tensor.values_nonneg hd.1 hf _

end MotionTree

-- 读法：`diskGap x y a b` 不超过 `a + b - 2 * r`。
theorem gap_bound {x y : K0 E} {a b r : ℚ} (ha : r ≤ a) (hb : r ≤ b)
    (hr : r ≤ 1) (h : (r : WithTop ℚ) ≤ val E (x - y)) : diskGap x y a b ≤ a + b - 2 * r := by
  have hm : r ≤ (val E (x - y)).untopD 1 := by
    generalize val E (x - y) = t at *
    cases t <;> simp_all
  unfold diskGap
  linarith only [le_min (le_min ha hb) hm]

-- 读法：`diskGap x y a b` 等于 `b - a`。
theorem gap_of_le {x y : K0 E} {a b : ℚ} (ha : a ≤ b)
    (h : (a : WithTop ℚ) ≤ val E (x - y)) (ha' : a ≤ 1) : diskGap x y a b = b - a := by
  have hu := gap_bound le_rfl ha ha' h
  unfold diskGap at *
  linarith [min_le_left (min a b) ((val E (x - y)).untopD 1), min_le_left a b]

-- 读法：`diskGap x y a b` 等于 `diskGap y x b a`。
theorem gap_symm (x y : K0 E) (a b : ℚ) : diskGap x y a b = diskGap y x b a := by
  rw [diskGap, diskGap, add_comm, min_comm a b, AddValuation.map_sub_swap]

-- 读法：`diskGap x x a b` 等于 `b - a`。使用 `gap_of_le` 给出的结论。
theorem gap_same (x : K0 E) {a b : ℚ} (hab : a ≤ b) (ha : a ≤ 1) :
    diskGap x x a b = b - a := gap_of_le hab (by simp) ha

-- 读法：`diskGap x y a b` 等于 `a + b - 2 * r`。
theorem gap_branch {x y : K0 E} {a b r : ℚ} (ha : r ≤ a) (hb : r ≤ b)
    (h : val E (x - y) = ↑r) : diskGap x y a b = a + b - 2 * r := by
  rw [diskGap, h, WithTop.untopD_coe, min_eq_right (le_min ha hb)]

-- 读法：`H.rate x l` 不超过 `H.rate y l`。这里调用 `H.chord`。
theorem MotionTree.same (H : MotionTree F E) (x y : Four (K0 E)) (l : Four ℚ)
    (hl : ∀ i, l i ≤ 1) (hh : ∀ i, (l i : WithTop ℚ) ≤ val E (x i - y i)) :
    H.rate x l ≤ H.rate y l := by
  have h i : diskGap (x i) (y i) (l i) (l i) = 0 := by rw [gap_of_le le_rfl (hh i) (hl i), sub_self]
  have h' i : diskGap (x i) (x i) (l i) (l i) = 0 := by rw [gap_same _ le_rfl (hl i), sub_self]
  simpa using H.chord x y x l l l hl hl hl 1 zero_le_one le_rfl (by simp [h, h']) (by simp [h])

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end
