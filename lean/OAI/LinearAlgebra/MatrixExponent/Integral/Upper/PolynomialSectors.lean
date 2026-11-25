-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialTensor
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialDegeneration
import Lean.Elab.Tactic.Omega

open OAI.LinearAlgebra.MatrixExponent.Integral

/-!
# 三扇区的多项式退化

这些是第 5.2 节的系数恒等式。在整个退化过程中，第一输入的权重始终为零。只有在单独识别中间分支时才反转其第一索引，并交换另外两个索引。

**英文原文**

The three-sector polynomial degeneration

These are the coefficient identities of Section 5.2.  The first input has
weight zero throughout the degeneration.  Only when identifying the individual
middle branch do we reverse its first index; its other two indices are swapped.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

-- 读法：`triplingWidth` 的取值由 `3 * h + a - 1` 给出。
/-- 三倍化构造中第二输入的长度。

英文原文：The second input length in the tripling construction.
-/
def triplingWidth (a h : ℕ) : ℕ := 3 * h + a - 1

-- 读法：当 `h ≤ y ∧ y < 2 * h + a - 1` 成立时取 `1`，否则取 `0`。
/-- 第二输入的中间区间的权重为一。

英文原文：The middle interval of the second input has weight one.
-/
def triplingYWeight (a h y : ℕ) : ℤ :=
  if h ≤ y ∧ y < 2 * h + a - 1 then 1 else 0

-- 读法：当 `h + a - 1 ≤ z ∧ z < 2 * h + a - 1` 成立时取 `-1`，否则取 `0`。
/-- 输出对偶空间的中间区间的权重为负一。

英文原文：The middle output-dual interval has weight minus one.
-/
def triplingZWeight (a h z : ℕ) : ℤ :=
  if h + a - 1 ≤ z ∧ z < 2 * h + a - 1 then -1 else 0

-- 读法：`triplingMatched` 表示以下条件：`(y < h ∧ z < h + a - 1)`、`(h ≤ y ∧ y < 2 * h + a - 1 ∧ h + a - 1 ≤ z ∧ z < 2 * h + a - 1) ∨ (2 * h + a - 1 ≤ y ∧ 2 * h + a - 1 ≤ z)` 至少有一项成立。
/-- 三对相匹配的区间，均不含右端点。

英文原文：The three matched pairs of intervals, expressed with exclusive upper bounds.
-/
def triplingMatched (a h y z : ℕ) : Prop :=
  (y < h ∧ z < h + a - 1) ∨
  (h ≤ y ∧ y < 2 * h + a - 1 ∧ h + a - 1 ≤ z ∧ z < 2 * h + a - 1) ∨
  (2 * h + a - 1 ≤ y ∧ 2 * h + a - 1 ≤ z)

-- 读法：为 `Decidable (triplingMatched a h y z)` 构造类型类实例。
instance triplingMatched_decidable (a h y z : ℕ) : Decidable (triplingMatched a h y z) := by
  unfold triplingMatched
  infer_instance

-- 读法：`z` 严格小于 `h + a - 1`。
theorem tripling_support_left {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hy : y < h) (hs : x + y = z) :
    z < h + a - 1 := by omega

-- 读法：`2 * h + a - 1` 不超过 `z`。
theorem tripling_support_right {a h x y z : ℕ}
    (hy : 2 * h + a - 1 ≤ y) (hs : x + y = z) :
    2 * h + a - 1 ≤ z := by omega

-- 读法：`h ≤ y` 与 `y < 2 * h + a - 1` 同时成立。
/-- 支集中的中间输出只能来自第二输入的中间区间。

英文原文：A supported middle output can only come from the middle second input.
-/
theorem tripling_support_middle {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z)
    (hz : h + a - 1 ≤ z ∧ z < 2 * h + a - 1) :
    h ≤ y ∧ y < 2 * h + a - 1 := by omega

-- 读法：`0` 不超过 `triplingYWeight a h y + triplingZWeight a h z`。
/-- 所有非零卷积系数的总权重皆非负。

英文原文：No nonzero convolution coefficient has a negative total weight.
-/
theorem tripling_weight_nonneg {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z) :
    0 ≤ triplingYWeight a h y + triplingZWeight a h z := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> omega

-- 读法：`triplingYWeight a h y + triplingZWeight a h z = 0` 与 `triplingMatched a h y z` 等价。
/-- 恰有三个匹配的分区保留在权重零的部分。

英文原文：Precisely the three matched sectors survive in weight zero.
-/
theorem tripling_weight_zero_iff {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z) :
    triplingYWeight a h y + triplingZWeight a h z = 0 ↔
      triplingMatched a h y z := by
  unfold triplingYWeight triplingZWeight triplingMatched
  split_ifs <;> omega

-- 读法：`triplingYWeight a h y + triplingZWeight a h z = 1` 与 `h ≤ y ∧ y < 2 * h + a - 1 ∧ (z < h + a - 1 ∨ 2 * h + a - 1 ≤ z)` 等价。
/-- 每个消失的项的权重都恰为一，且从第二输入的中间分区连到输出的两个外侧分区之一。

英文原文：Every term that disappears has weight exactly one, and goes from the
middle second-input sector to one of the two outer output sectors.
-/
theorem tripling_weight_one_iff {a h x y z : ℕ}
    (ha : 1 ≤ a) (_hx : x < a) (_hs : x + y = z) :
    triplingYWeight a h y + triplingZWeight a h z = 1 ↔
      h ≤ y ∧ y < 2 * h + a - 1 ∧
        (z < h + a - 1 ∨ 2 * h + a - 1 ≤ z) := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> omega

-- 读法：`triplingGraded` 的结果类型为 `Tensor O (Fin a) (Fin (triplingWidth a h)) (Fin (a + triplingWidth a h - 1))`。
/-- 同时取各分区的零权重部分得到的张量，共享的第一条腿保持原样。

英文原文：The simultaneous weight-zero tensor, with one unchanged shared first leg.
-/
def triplingGraded (a h : ℕ) :
    Tensor O (Fin a) (Fin (triplingWidth a h)) (Fin (a + triplingWidth a h - 1)) :=
  weightedLimit (polynomialTensor a (triplingWidth a h)) (fun _ => 0)
    (fun y => triplingYWeight a h y.val) (fun z => triplingZWeight a h z.val)

-- 读法：`triplingGraded a h x y z` 等于 `polynomialTensor a (triplingWidth a h) x y z`。
theorem triplingGraded_of_weights (a h : ℕ)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1))
    (hw : triplingYWeight a h y.val + triplingZWeight a h z.val = 0) :
    triplingGraded a h x y z = polynomialTensor a (triplingWidth a h) x y z := by
  simp [triplingGraded, weightedLimit, hw]

-- 读法：`triplingGraded a h x y z` 等于 `if x.val + y.val = z.val ∧ triplingMatched a h y.val z.val then 1 else 0`。按 `x.val + y.val = z.val` 成立与否分情况。
/-- 完整的系数公式列入所有取值为零的跨分区项。

英文原文：The full coefficient formula includes all vanishing cross-sector terms.
-/
theorem triplingGraded_coefficient (a h : ℕ) (ha : 1 ≤ a)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1)) :
    triplingGraded a h x y z =
      if x.val + y.val = z.val ∧ triplingMatched a h y.val z.val then 1 else 0 := by
  classical
  by_cases hs : x.val + y.val = z.val
  · have hw := tripling_weight_zero_iff (h := h) ha x.isLt hs
    simp [triplingGraded, weightedLimit, polynomialTensor, hs, hw]
  · simp [triplingGraded, weightedLimit, polynomialTensor, hs]

-- 读法：`triplingLeftY` 的结果类型为 `Fin (triplingWidth a h)`。
/-- 将坐标平移到第二输入的左分区。

英文原文：Translate a coordinate into the left second-input sector.
-/
def triplingLeftY (a h : ℕ) (ha : 1 ≤ a) (j : Fin h) : Fin (triplingWidth a h) :=
  ⟨j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingLeftZ` 的结果类型为 `Fin (a + triplingWidth a h - 1)`。
/-- 将坐标平移到输出的左分区。

英文原文：Translate a coordinate into the left output sector.
-/
def triplingLeftZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (a + triplingWidth a h - 1) :=
  ⟨k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingMiddleY` 的结果类型为 `Fin (triplingWidth a h)`。
/-- 将坐标平移到第二输入的中分区。

英文原文：Translate a coordinate into the middle second-input sector.
-/
def triplingMiddleY (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (triplingWidth a h) :=
  ⟨h + k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingMiddleZ` 的结果类型为 `Fin (a + triplingWidth a h - 1)`。
/-- 将坐标平移到输出的中分区。

英文原文：Translate a coordinate into the middle output sector.
-/
def triplingMiddleZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) : Fin (a + triplingWidth a h - 1) :=
  ⟨h + a - 1 + j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingRightY` 的结果类型为 `Fin (triplingWidth a h)`。
/-- 将坐标平移到第二输入的右分区。

英文原文：Translate a coordinate into the right second-input sector.
-/
def triplingRightY (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) : Fin (triplingWidth a h) :=
  ⟨2 * h + a - 1 + j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingRightZ` 的结果类型为 `Fin (a + triplingWidth a h - 1)`。
/-- 将坐标平移到输出的右分区。

英文原文：Translate a coordinate into the right output sector.
-/
def triplingRightZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (a + triplingWidth a h - 1) :=
  ⟨2 * h + a - 1 + k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

-- 读法：`triplingReverse` 的结果类型为 `Fin a`。
/-- 仅用于识别中间分支的次序反转。

英文原文：Reversal used only in the middle branch identification.
-/
def triplingReverse {a : ℕ} (u : Fin a) : Fin a :=
  ⟨a - 1 - u.val, by have hu := u.isLt; omega⟩

-- 读法：`triplingReverse (triplingReverse u)` 等于 `u`。按 `Fin.ext` 的外延性准则比较各分量。
theorem triplingReverse_involutive {a : ℕ} (u : Fin a) :
    triplingReverse (triplingReverse u) = u := by
  apply Fin.ext
  have hu := u.isLt
  dsimp [triplingReverse]
  omega

-- 读法：要证明的命题是 `triplingYWeight a h (triplingLeftY a h ha j).val + triplingZWeight a h (triplingLeftZ a h ha hh k).val = 0`。
theorem tripling_left_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) (k : Fin (a + h - 1)) :
    triplingYWeight a h (triplingLeftY a h ha j).val +
      triplingZWeight a h (triplingLeftZ a h ha hh k).val = 0 := by
  have hj := j.isLt
  have hk := k.isLt
  dsimp [triplingYWeight, triplingZWeight, triplingLeftY, triplingLeftZ]
  split_ifs <;> omega

-- 读法：要证明的命题是 `triplingYWeight a h (triplingMiddleY a h ha hh k).val + triplingZWeight a h (triplingMiddleZ a h ha hh j).val = 0`。
theorem tripling_middle_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) (j : Fin h) :
    triplingYWeight a h (triplingMiddleY a h ha hh k).val +
      triplingZWeight a h (triplingMiddleZ a h ha hh j).val = 0 := by
  have hj := j.isLt
  have hk := k.isLt
  dsimp [triplingYWeight, triplingZWeight, triplingMiddleY, triplingMiddleZ]
  split_ifs <;> omega

-- 读法：要证明的命题是 `triplingYWeight a h (triplingRightY a h ha hh j).val + triplingZWeight a h (triplingRightZ a h ha hh k).val = 0`。
theorem tripling_right_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) (k : Fin (a + h - 1)) :
    triplingYWeight a h (triplingRightY a h ha hh j).val +
      triplingZWeight a h (triplingRightZ a h ha hh k).val = 0 := by
  dsimp [triplingYWeight, triplingZWeight, triplingRightY, triplingRightZ]
  split_ifs <;> omega

-- 读法：`triplingGraded a h x (triplingLeftY a h ha j) (triplingLeftZ a h ha hh k)` 等于 `polynomialTensor a h x j k`。
/-- 左分支恰为两个长度分别为 `a,h` 的多项式的乘法。

英文原文：The left branch is exactly polynomial multiplication of lengths `a,h`.
-/
theorem tripling_left_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (j : Fin h) (k : Fin (a + h - 1)) :
    triplingGraded a h x (triplingLeftY a h ha j) (triplingLeftZ a h ha hh k) =
      polynomialTensor a h x j k := by
  rw [triplingGraded_of_weights a h x _ _ (tripling_left_weights a h ha hh j k)]
  rfl

-- 读法：`triplingGraded a h x (triplingRightY a h ha hh j) (triplingRightZ a h ha hh k)` 等于 `polynomialTensor a h x j k`。
/-- 在后两条腿上进行平移后，右分支给出同一个张量。

英文原文：The right branch is the same tensor after translations on the last two legs.
-/
theorem tripling_right_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (j : Fin h) (k : Fin (a + h - 1)) :
    triplingGraded a h x (triplingRightY a h ha hh j) (triplingRightZ a h ha hh k) =
      polynomialTensor a h x j k := by
  rw [triplingGraded_of_weights a h x _ _ (tripling_right_weights a h ha hh j k)]
  have hs : x.val + (2 * h + a - 1 + j.val) = 2 * h + a - 1 + k.val ↔
      x.val + j.val = k.val := by omega
  simp only [polynomialTensor, triplingRightY, triplingRightZ, hs]

-- 读法：要证明的命题是 `triplingGraded a h (triplingReverse u) (triplingMiddleY a h ha hh k) (triplingMiddleZ a h ha hh j) = polynomialTensor a h u j k`。
/-- 中间分支交换张量的第二、第三条腿，并逆转第一组基的次序。这个恒等式仅在中间分支上作此逆转，两个外侧分支和整个同时退化的第一组基都保持原来的次序。

英文原文：In the middle branch the second and third tensor legs are exchanged, and
the first basis is reversed.  This identity does not reverse the first basis
of either outer branch or of the whole simultaneous degeneration.
-/
theorem tripling_middle_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (u : Fin a) (k : Fin (a + h - 1)) (j : Fin h) :
    triplingGraded a h (triplingReverse u)
      (triplingMiddleY a h ha hh k) (triplingMiddleZ a h ha hh j) =
      polynomialTensor a h u j k := by
  rw [triplingGraded_of_weights a h (triplingReverse u) _ _
    (tripling_middle_weights a h ha hh k j)]
  have hu := u.isLt
  have hs : a - 1 - u.val + (h + k.val) = h + a - 1 + j.val ↔
      u.val + j.val = k.val := by omega
  simp only [polynomialTensor, triplingReverse, triplingMiddleY, triplingMiddleZ, hs]

-- 读法：`triplingLeftY a h ha j₁ ≠ triplingMiddleY a h ha hh k` 与 `triplingMiddleY a h ha hh k ≠ triplingRightY a h ha hh j₂ ∧ triplingLeftY a h ha j₁ ≠ triplingRightY a h ha hh j₂` 同时成立。
/-- 三个分区在第二输入中的像两两不交。

英文原文：The three second-input images are pairwise disjoint.
-/
theorem tripling_second_sectors_disjoint (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j₁ j₂ : Fin h) (k : Fin (a + h - 1)) :
    triplingLeftY a h ha j₁ ≠ triplingMiddleY a h ha hh k ∧
    triplingMiddleY a h ha hh k ≠ triplingRightY a h ha hh j₂ ∧
    triplingLeftY a h ha j₁ ≠ triplingRightY a h ha hh j₂ := by
  have hj₁ := j₁.isLt
  have hk := k.isLt
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftY, triplingMiddleY] at hv
    omega
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingMiddleY, triplingRightY] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftY, triplingRightY] at hv
    omega

-- 读法：结论为 `triplingLeftZ a h ha hh k₁ ≠ triplingMiddleZ a h ha hh j ∧ triplingMiddleZ a h ha hh j ≠ triplingRightZ a h ha hh k₂ ∧ triplingLeftZ a h ha hh k₁ ≠ triplingRightZ a h ha hh k₂`。
/-- 三个分区在输出中的像也两两不交。

英文原文：The three output images are pairwise disjoint as well.
-/
theorem tripling_output_sectors_disjoint (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k₁ k₂ : Fin (a + h - 1)) (j : Fin h) :
    triplingLeftZ a h ha hh k₁ ≠ triplingMiddleZ a h ha hh j ∧
    triplingMiddleZ a h ha hh j ≠ triplingRightZ a h ha hh k₂ ∧
    triplingLeftZ a h ha hh k₁ ≠ triplingRightZ a h ha hh k₂ := by
  have hk₁ := k₁.isLt
  have hj := j.isLt
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftZ, triplingMiddleZ] at hv
    omega
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingMiddleZ, triplingRightZ] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftZ, triplingRightZ] at hv
    omega

-- 读法：在后续公式中，`TriplingY` 是 `Fin h ⊕ (Fin (a + h - 1) ⊕ Fin h)` 的缩写。
/-- 保留各自标签时，第二输入的三个完整分区。

英文原文：The three complete second-input sectors, before forgetting their labels.
-/
abbrev TriplingY (a h : ℕ) := Fin h ⊕ (Fin (a + h - 1) ⊕ Fin h)

-- 读法：在后续公式中，`TriplingZ` 是 `Fin (a + h - 1) ⊕ (Fin h ⊕ Fin (a + h - 1))` 的缩写。
/-- 相应的完整输出分区。

英文原文：The corresponding complete output sectors.
-/
abbrev TriplingZ (a h : ℕ) := Fin (a + h - 1) ⊕ (Fin h ⊕ Fin (a + h - 1))

-- 读法：逐一匹配以下输入模式：`.inl j`、`.inr (.inl k)`、`.inr (.inr j)`。
def triplingYMap (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingY a h → Fin (triplingWidth a h)
  | .inl j => triplingLeftY a h ha j
  | .inr (.inl k) => triplingMiddleY a h ha hh k
  | .inr (.inr j) => triplingRightY a h ha hh j

-- 读法：逐一匹配以下输入模式：`.inl k`、`.inr (.inl j)`、`.inr (.inr k)`。
def triplingZMap (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingZ a h → Fin (a + triplingWidth a h - 1)
  | .inl k => triplingLeftZ a h ha hh k
  | .inr (.inl j) => triplingMiddleZ a h ha hh j
  | .inr (.inr k) => triplingRightZ a h ha hh k

-- 读法：`(triplingYMap a h ha hh)` 是单射。
theorem triplingYMap_injective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Injective (triplingYMap a h ha hh) := by
  intro u v he
  rcases u with j | (k | j) <;> rcases v with j' | (k' | j')
  all_goals
    have hv := congrArg Fin.val he
    simp only [triplingYMap, triplingLeftY, triplingMiddleY, triplingRightY] at hv
    first
    | (exfalso; omega)
    | (simp only [Sum.inl.injEq, Sum.inr.injEq]; apply Fin.ext; omega)

-- 读法：`(triplingZMap a h ha hh)` 是单射。
theorem triplingZMap_injective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Injective (triplingZMap a h ha hh) := by
  intro u v he
  rcases u with k | (j | k) <;> rcases v with k' | (j' | k')
  all_goals
    have hv := congrArg Fin.val he
    simp only [triplingZMap, triplingLeftZ, triplingMiddleZ, triplingRightZ] at hv
    first
    | (exfalso; omega)
    | (simp only [Sum.inl.injEq, Sum.inr.injEq]; apply Fin.ext; omega)

-- 读法：`(triplingYMap a h ha hh)` 是满射。按 `y.val < h` 成立与否分情况。
/-- 每个第二输入坐标恰好属于一个分区。

英文原文：All second-input coordinates occur in exactly one sector.
-/
theorem triplingYMap_surjective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Surjective (triplingYMap a h ha hh) := by
  intro y
  have hy := y.isLt
  dsimp [triplingWidth] at hy
  by_cases hl : y.val < h
  · refine ⟨.inl ⟨y.val, hl⟩, ?_⟩
    apply Fin.ext
    rfl
  · by_cases hm : y.val < 2 * h + a - 1
    · refine ⟨.inr (.inl ⟨y.val - h, by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingYMap, triplingMiddleY]
      omega
    · refine ⟨.inr (.inr ⟨y.val - (2 * h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingYMap, triplingRightY]
      omega

-- 读法：`(triplingZMap a h ha hh)` 是满射。按 `z.val < h + a - 1` 成立与否分情况。
/-- 每个输出坐标恰好属于一个对应的分区。

英文原文：All output coordinates occur in exactly one corresponding sector.
-/
theorem triplingZMap_surjective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Surjective (triplingZMap a h ha hh) := by
  intro z
  have hz := z.isLt
  dsimp [triplingWidth] at hz
  by_cases hl : z.val < h + a - 1
  · refine ⟨.inl ⟨z.val, by omega⟩, ?_⟩
    apply Fin.ext
    rfl
  · by_cases hm : z.val < 2 * h + a - 1
    · refine ⟨.inr (.inl ⟨z.val - (h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingZMap, triplingMiddleZ]
      omega
    · refine ⟨.inr (.inr ⟨z.val - (2 * h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingZMap, triplingRightZ]
      omega

-- 读法：`triplingYEquiv` 的取值由 `Equiv.ofBijective (triplingYMap a h ha hh) ⟨triplingYMap_injective a h ha hh, triplingYMap_surjective a h ha hh⟩` 给出。
/-- 同时覆盖各分区的单个第二输入基等价。

英文原文：A single simultaneous second-input basis equivalence.
-/
def triplingYEquiv (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingY a h ≃ Fin (triplingWidth a h) :=
  Equiv.ofBijective (triplingYMap a h ha hh)
    ⟨triplingYMap_injective a h ha hh, triplingYMap_surjective a h ha hh⟩

-- 读法：`triplingZEquiv` 的取值由 `Equiv.ofBijective (triplingZMap a h ha hh) ⟨triplingZMap_injective a h ha hh, triplingZMap_surjective a h ha hh⟩` 给出。
/-- 同时覆盖各分区的单个输出基等价。

英文原文：A single simultaneous output basis equivalence.
-/
def triplingZEquiv (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingZ a h ≃ Fin (a + triplingWidth a h - 1) :=
  Equiv.ofBijective (triplingZMap a h ha hh)
    ⟨triplingZMap_injective a h ha hh, triplingZMap_surjective a h ha hh⟩

-- 读法：逐一匹配以下输入模式：`x, .inl j, .inl k`、`x, .inr (.inl k), .inr (.inl j)`、`x, .inr (.inr j), .inr (.inr k)`、`_, _, _`。
/-- 显式组装共用第一输入的张量。在与两个外侧加项相同的第一输入坐标中，中间加项的第一输入系数次序相反。每个跨分区系数都为零。

英文原文：The actual common-first-input assembly.  Its middle summand, in the same
first-input coordinates as the outer summands, has reversed first coefficients.
Every cross-sector coefficient is zero.
-/
def triplingSectorTensor (a h : ℕ) : Tensor O (Fin a) (TriplingY a h) (TriplingZ a h)
  | x, .inl j, .inl k => polynomialTensor a h x j k
  | x, .inr (.inl k), .inr (.inl j) => polynomialTensor a h (triplingReverse x) j k
  | x, .inr (.inr j), .inr (.inr k) => polynomialTensor a h x j k
  | _, _, _ => 0

-- 读法：要证明的命题是 `(fun x y z => triplingGraded a h x (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)) = triplingSectorTensor a h`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 用后两条腿各自唯一的完整分区等价重编索引，就得到组装后的完整张量。第一输入完全保持原样。

英文原文：Reindexing the last two legs by their single complete sector equivalences
gives the full assembled tensor.  The first input is literally unchanged.
-/
theorem triplingGraded_sector_assembly (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (fun x y z => triplingGraded a h x
      (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)) =
        triplingSectorTensor a h := by
  funext x y z
  change triplingGraded a h x (triplingYMap a h ha hh y)
    (triplingZMap a h ha hh z) = triplingSectorTensor a h x y z
  rcases y with j | (k | j) <;> rcases z with k' | (j' | k')
  · exact tripling_left_coefficient a h ha hh x j k'
  · rw [triplingGraded_coefficient a h ha]
    have hj := j.isLt
    have hx := x.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inl j)).val =
        (triplingZMap a h ha hh (.inr (.inl j'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inl j)).val
        (triplingZMap a h ha hh (.inr (.inl j'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingLeftY,
        triplingMiddleZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hj := j.isLt
    have hx := x.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inl j)).val =
        (triplingZMap a h ha hh (.inr (.inr k'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inl j)).val
        (triplingZMap a h ha hh (.inr (.inr k'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingLeftY,
        triplingRightZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hk := k.isLt
    have hk' := k'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inl k))).val =
        (triplingZMap a h ha hh (.inl k')).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inl k))).val
        (triplingZMap a h ha hh (.inl k')).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingMiddleY,
        triplingLeftZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · simpa only [triplingReverse_involutive, triplingYMap, triplingZMap,
      triplingSectorTensor] using
      tripling_middle_coefficient a h ha hh (triplingReverse x) k j'
  · rw [triplingGraded_coefficient a h ha]
    have hk := k.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inl k))).val =
        (triplingZMap a h ha hh (.inr (.inr k'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inl k))).val
        (triplingZMap a h ha hh (.inr (.inr k'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingMiddleY,
        triplingRightZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hk' := k'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inr j))).val =
        (triplingZMap a h ha hh (.inl k')).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inr j))).val
        (triplingZMap a h ha hh (.inl k')).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingRightY,
        triplingLeftZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hj' := j'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inr j))).val =
        (triplingZMap a h ha hh (.inr (.inl j'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inr j))).val
        (triplingZMap a h ha hh (.inr (.inl j'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingRightY,
        triplingMiddleZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · exact tripling_right_coefficient a h ha hh x j k'

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
