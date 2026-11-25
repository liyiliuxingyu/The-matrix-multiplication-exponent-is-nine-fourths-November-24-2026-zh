-- 本文件所属证明环节：证明双调归并的次序性质，保证归并后的树状数组按所需方向排列。
import OAI.LinearAlgebra.MatrixExponent.BitonicSort

/-!
# 双调合并

把位置分为 `x ≤ b` 与 `b < x` 两类。双调性要求对每个阈值 `b`，都不存在跨这两类交替出现的四个有序位置。比较相对位置，将两半分离并保持各自内部的双调性。

**英文原文**

Bitonic merge

Bitonicity is expressed by forbidding four ordered positions alternating
between the two classes `x ≤ b` and `b < x`, for every threshold `b`.
Opposite-position comparisons separate the two halves and preserve
bitonicity within each half.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {a : Wire}

-- 读法：逐一匹配以下输入模式：`0, x, _`、`w + 1, x, i`。
private def read : (w : ℕ) → Val (tree w a) → ℕ → Val a
  | 0, x, _ => x
  | w + 1, x, i =>
    if i < 2 ^ w then read w x.1 i else read w x.2 (i - 2 ^ w)

-- 读法：`read (w + 1) x i` 等于 `read w x.1 i`。
private theorem read_left (w : ℕ) (x : Val (tree (w + 1) a)) {i : ℕ} (h : i < 2 ^ w) :
    read (w + 1) x i = read w x.1 i := by
  simp [read, h]

-- 读法：`read (w + 1) x (2 ^ w + i)` 等于 `read w x.2 i`。
private theorem read_right (w : ℕ) (x : Val (tree (w + 1) a)) (i : ℕ) :
    read (w + 1) x (2 ^ w + i) = read w x.2 i := by
  simp [read]

-- 读法：`y ∈ flatten w x` 与 `∃ i < 2 ^ w, read w x i = y` 等价。对 `w` 作归纳。
private theorem mem_flatten (w : ℕ) (x : Val (tree w a)) (y : Val a) :
    y ∈ flatten w x ↔ ∃ i < 2 ^ w, read w x i = y := by
  induction w with
  | zero => simp [read, flatten, eq_comm]
  | succ w ih =>
    rw [flatten, List.mem_append, ih, ih, pow_succ]
    constructor
    · rintro (⟨i, hi, hy⟩ | ⟨i, hi, hy⟩)
      · exact ⟨i, by omega, (read_left w x hi).trans hy⟩
      · exact ⟨2 ^ w + i, by omega, (read_right w x i).trans hy⟩
    · rintro ⟨i, hi, hy⟩
      rw [read] at hy
      split at hy
      · exact .inl ⟨i, by omega, hy⟩
      · exact .inr ⟨i - 2 ^ w, by omega, hy⟩

-- 读法：要证明的命题是 `R (read w x i) (read w x j)`。对 `w` 作归纳，并把 `i j` 保持为任意参数。
private theorem read_pairwise (w : ℕ) (x : Val (tree w a)) {R : Val a → Val a → Prop}
    (h : (flatten w x).Pairwise R) {i j : ℕ} (hij : i < j) (hj : j < 2 ^ w) :
    R (read w x i) (read w x j) := by
  induction w generalizing i j with
  | zero => simp at hj; omega
  | succ w ih =>
    rw [flatten, List.pairwise_append] at h
    rw [pow_succ] at hj
    rw [read, read]
    split <;> split
    · exact ih _ h.1 hij (by omega)
    · exact h.2.2 _ ((mem_flatten ..).2 ⟨i, by omega, rfl⟩)
        _ ((mem_flatten ..).2 ⟨j - 2 ^ w, by omega, rfl⟩)
    · omega
    · exact ih _ h.2.1 (by omega) (by omega)

variable [LinearOrder (Val a)]

-- 读法：`read w (splitTree w x).1 i = min (read w x.1 i) (read w x.2 i)` 与 `read w (splitTree w x).2 i = max (read w x.1 i) (read w x.2 i)` 同时成立。对 `w` 作归纳，并把 `i` 保持为任意参数。
private theorem read_split (w : ℕ) (x : Val (tree (w + 1) a)) (i : ℕ) :
    read w (splitTree w x).1 i = min (read w x.1 i) (read w x.2 i) ∧
    read w (splitTree w x).2 i = max (read w x.1 i) (read w x.2 i) := by
  induction w generalizing i with
  | zero => exact ⟨rfl, rfl⟩
  | succ w ih =>
    by_cases h : i < 2 ^ w
    · simpa [read, h, splitTree] using ih (x.1.1, x.2.1) i
    · simpa [read, h, splitTree] using ih (x.1.2, x.2.2) (i - 2 ^ w)

-- 读法：`NoAlt` 表示以下条件：`(u → s → v ∨ t)` 与 `(v → t → u ∨ s)` 同时成立。
private def NoAlt (u v s t : Prop) : Prop :=
  (u → s → v ∨ t) ∧ (v → t → u ∨ s)

-- 读法：`Bitonic` 表示以下条件：对每个 `i j k l : ℕ`，由 `i < j` 推出 `j < k → k < l → l < 2 ^ w → ∀ b : Val a, NoAlt (read w x i ≤ b) (read w x j ≤ b) (read w x k ≤ b) (read w x l ≤ b)`。
private def Bitonic (w : ℕ) (x : Val (tree w a)) : Prop :=
  ∀ i j k l : ℕ, i < j → j < k → k < l → l < 2 ^ w → ∀ b : Val a,
    NoAlt (read w x i ≤ b) (read w x j ≤ b) (read w x k ≤ b) (read w x l ≤ b)

-- 读法：`NoAlt (p ∨ t) (q ∨ u) (r ∨ v) (s ∨ z)` 与 `NoAlt (p ∧ t) (q ∧ u) (r ∧ v) (s ∧ z)` 同时成立。
/-- 在四个位置及与之相对的四个位置检验切分。对于最小值（或）与最大值（与），原有的六个约束便已足够。

英文原文：Test the cut at four positions and their four opposites. Six inherited
constraints suffice for the minima (or) and the maxima (and).
-/
private theorem split_cuts {p q r s t u v z : Prop}
    (h₁ : NoAlt p q r s) (h₂ : NoAlt p q r z)
    (h₃ : NoAlt s t u v) (h₄ : NoAlt t u v z)
    (h₅ : NoAlt p q v z) (h₆ : NoAlt r s t u) :
    NoAlt (p ∨ t) (q ∨ u) (r ∨ v) (s ∨ z) ∧
    NoAlt (p ∧ t) (q ∧ u) (r ∧ v) (s ∧ z) := by
  unfold NoAlt at *
  grind

-- 读法：`Bitonic w (splitTree w x).1` 与 `Bitonic w (splitTree w x).2` 同时成立。
private theorem bitonic_split (w : ℕ) (x : Val (tree (w + 1) a)) (hx : Bitonic (w + 1) x) :
    Bitonic w (splitTree w x).1 ∧ Bitonic w (splitTree w x).2 := by
  have both (i j k l : ℕ) (h₁ : i < j) (h₂ : j < k) (h₃ : k < l) (h₄ : l < 2 ^ w)
      (b : Val a) :
      let cut := fun y => NoAlt (read w y i ≤ b) (read w y j ≤ b)
        (read w y k ≤ b) (read w y l ≤ b)
      cut (splitTree w x).1 ∧ cut (splitTree w x).2 := by
    have hi : i < 2 ^ w := by omega
    have hj : j < 2 ^ w := by omega
    have hk : k < 2 ^ w := by omega
    -- 推导：记下中间结论 `hw`：`2 ^ (w + 1) = 2 ^ w * 2`。
    have hw : 2 ^ (w + 1) = 2 ^ w * 2 := pow_succ ..
    have H := split_cuts
      (hx i j k l h₁ h₂ h₃ (by omega) b)
      (hx i j k (2 ^ w + l) h₁ h₂ (by omega) (by omega) b)
      (hx l (2 ^ w + i) (2 ^ w + j) (2 ^ w + k) (by omega) (by omega) (by omega) (by omega) b)
      (hx (2 ^ w + i) (2 ^ w + j) (2 ^ w + k) (2 ^ w + l) (by omega) (by omega) (by omega) (by omega) b)
      (hx i j (2 ^ w + k) (2 ^ w + l) h₁ (by omega) (by omega) (by omega) b)
      (hx k l (2 ^ w + i) (2 ^ w + j) h₃ (by omega) (by omega) (by omega) b)
    simpa only [read_split, min_le_iff, max_le_iff, read_left w x hi, read_left w x hj,
      read_left w x hk, read_left w x h₄, read_right] using H
  exact ⟨fun i j k l h₁ h₂ h₃ h₄ b => (both i j k l h₁ h₂ h₃ h₄ b).1,
    fun i j k l h₁ h₂ h₃ h₄ b => (both i j k l h₁ h₂ h₃ h₄ b).2⟩

-- 读法：`u` 不超过 `v`。
private theorem split_le (w : ℕ) (x : Val (tree (w + 1) a)) (hx : Bitonic (w + 1) x)
    (u : Val a) (hu : u ∈ flatten w (splitTree w x).1)
    (v : Val a) (hv : v ∈ flatten w (splitTree w x).2) : u ≤ v := by
  obtain ⟨i, hi, rfl⟩ := (mem_flatten ..).1 hu
  obtain ⟨j, hj, rfl⟩ := (mem_flatten ..).1 hv
  rw [(read_split ..).1, (read_split ..).2, min_le_iff]
  have hw : 2 ^ (w + 1) = 2 ^ w * 2 := pow_succ ..
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h := hx i j (2 ^ w + i) (2 ^ w + j) hij (by omega) (by omega) (by omega)
      (max (read w x.1 j) (read w x.2 j))
    rw [read_left w x hi, read_left w x hj, read_right, read_right] at h
    exact h.2 (le_max_left ..) (le_max_right ..)
  · exact Or.inl (le_max_left ..)
  · have h := hx j i (2 ^ w + j) (2 ^ w + i) hji (by omega) (by omega) (by omega)
      (max (read w x.1 j) (read w x.2 j))
    rw [read_left w x hi, read_left w x hj, read_right, read_right] at h
    exact h.1 (le_max_left ..) (le_max_right ..)

-- 读法：要证明的命题是 `Bitonic (w + 1) x`。按 `q < 2 ^ w` 成立与否分情况。
private theorem bitonic_of_pairwise (w : ℕ) (x : Val (tree (w + 1) a))
    (hl : (flatten w x.1).Pairwise (· ≤ ·)) (hr : (flatten w x.2).Pairwise (· ≥ ·)) :
    Bitonic (w + 1) x := by
  intro i j k l h₁ h₂ h₃ h₄ b
  rw [pow_succ] at h₄
  have prevOrNext (p q r : ℕ) (hp : p < q) (hq : q < r) (hr' : r < 2 ^ w * 2)
      (hb : read (w + 1) x q ≤ b) : read (w + 1) x p ≤ b ∨ read (w + 1) x r ≤ b := by
    by_cases hq' : q < 2 ^ w
    · left
      rw [read_left w x hq'] at hb
      rw [read_left w x (by omega : p < 2 ^ w)]
      exact (read_pairwise w x.1 hl hp hq').trans hb
    · right
      rw [read, ite_eq_right hq'] at hb
      rw [read, ite_eq_right (by omega : ¬ r < 2 ^ w)]
      exact (read_pairwise w x.2 hr (by omega : q - 2 ^ w < r - 2 ^ w) (by omega)).trans hb
  exact ⟨fun _ hk => prevOrNext j k l h₂ h₃ h₄ hk,
    fun hj _ => prevOrNext i j k h₁ h₂ (by omega) hj⟩

-- 读法：要证明的命题是 `(flatten w (mergeTree w x)).Pairwise (· ≤ ·)`。对 `w` 作归纳。
private theorem mergeTree_sorted (w : ℕ) (x : Val (tree w a)) (hx : Bitonic w x) :
    (flatten w (mergeTree w x)).Pairwise (· ≤ ·) := by
  induction w with
  | zero => simp [flatten]
  | succ w ih =>
    rw [mergeTree, flatten, List.pairwise_append]
    obtain ⟨hl, hr⟩ := bitonic_split w x hx
    refine ⟨ih _ hl, ih _ hr, fun u hu v hv => ?_⟩
    exact split_le w x hx u ((mergeTree_perm ..).mem_iff.mp hu)
      v ((mergeTree_perm ..).mem_iff.mp hv)

-- 读法：要证明的命题是 `(flatten w (sortTree w x)).Pairwise (· ≤ ·)`。对 `w` 作归纳。
theorem sortTree_sorted (w : ℕ) (x : Val (tree w a)) :
    (flatten w (sortTree w x)).Pairwise (· ≤ ·) := by
  induction w with
  | zero => simp [flatten]
  | succ w ih =>
    rw [sortTree]
    apply mergeTree_sorted
    apply bitonic_of_pairwise
    · exact ih _
    · rw [flatten_reverseTree, List.pairwise_reverse]
      exact ih _

end OAI.LinearAlgebra.MatrixExponent
