-- 本文件所属证明环节：把固定长度的词按各字母出现次数划为纤维，在纤维内权重保持不变。用有限分配律求总权重，并由至多 (N+1)^s 个计数向量选出质量至少为平均值的非空纤维。
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# 标签不等式中有限字的精确纤维

将含 `s` 个字母的字母表上所有长度为 `N` 的字按各字母出现的次数分组。容纳计数向量的空间恰有 `(N + 1)^s` 个元素。由有限分配律算出总权重，故至少一个纤维的权重不低于平均值。这里不需要有关张量、渐近行为或阶乘的假设。

**英文原文**

Exact finite word fibers for the tag inequality

Length-`N` words over `s` letters are grouped by their occurrence counts.
The ambient count-vector space has exactly `(N + 1)^s` elements. Finite
distributivity gives the total weight, so one fiber has at least the average
weight. There are no tensor, asymptotic, or factorial assumptions here.
-/

noncomputable section

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum.TagWords

-- 读法：在后续公式中，`Word` 是 `Fin N → Fin s` 的缩写。
abbrev Word (s N : ℕ) := Fin N → Fin s

-- 读法：在后续公式中，`CountVector` 是 `Fin s → Fin (N + 1)` 的缩写。
abbrev CountVector (s N : ℕ) := Fin s → Fin (N + 1)

-- 读法：`occurrences` 的取值由 `(Finset.univ.filter (fun j => w j = i)).card` 给出。
/-- 指定字母所占位置的数目。

英文原文：Number of positions occupied by the specified letter.
-/
def occurrences {s N : ℕ} (w : Word s N) (i : Fin s) : ℕ :=
  (Finset.univ.filter (fun j => w j = i)).card

-- 读法：`occurrences w i` 不超过 `N`。
theorem occurrences_le {s N : ℕ} (w : Word s N) (i : Fin s) :
    occurrences w i ≤ N := by
  simpa [occurrences] using
    (Finset.card_le_card (Finset.filter_subset (fun j => w j = i) Finset.univ))

-- 读法：输入 `i` 时返回 `⟨occurrences w i, Nat.lt_succ_of_le (occurrences_le w i)⟩`。
/-- 每个字母的出现次数都介于零与词长之间。

英文原文：Every occurrence count lies between zero and the word length.
-/
def countVector {s N : ℕ} (w : Word s N) : CountVector s N :=
  fun i => ⟨occurrences w i, Nat.lt_succ_of_le (occurrences_le w i)⟩

-- 读法：`(countVector w i).val` 等于 `occurrences w i`。两端由定义化简为同一项。
@[simp] theorem countVector_val {s N : ℕ} (w : Word s N) (i : Fin s) :
    (countVector w i).val = occurrences w i := rfl

-- 读法：`Fintype.card (CountVector s N)` 等于 `(N + 1) ^ s`。
@[simp] theorem card_countVector (s N : ℕ) :
    Fintype.card (CountVector s N) = (N + 1) ^ s := by
  simp [CountVector]

-- 读法：结论为 `∑ i, occurrences w i = N`。
theorem sum_occurrences {s N : ℕ} (w : Word s N) :
    ∑ i, occurrences w i = N := by
  simpa [occurrences] using
    (Finset.sum_fiberwise' Finset.univ w (fun _ : Fin s => (1 : ℕ)))

-- 读法：`fiber` 的取值由 `Finset.univ.filter (fun w => countVector w = c)` 给出。
/-- 具有给定计数向量的词所组成的有限集合。

英文原文：The finite set of words having exactly this count vector.
-/
def fiber {s N : ℕ} (c : CountVector s N) : Finset (Word s N) :=
  Finset.univ.filter (fun w => countVector w = c)

-- 读法：`w ∈ fiber c` 与 `countVector w = c` 等价。
@[simp] theorem mem_fiber {s N : ℕ} (w : Word s N) (c : CountVector s N) :
    w ∈ fiber c ↔ countVector w = c := by
  simp [fiber]

-- 读法：要证明的命题是 `Disjoint (fiber c) (fiber d)`。这里调用 `Finset.disjoint_left.mpr`。
theorem disjoint_fiber {s N : ℕ} {c d : CountVector s N} (h : c ≠ d) :
    Disjoint (fiber c) (fiber d) := by
  apply Finset.disjoint_left.mpr
  intro w hc hd
  exact h (((mem_fiber w c).mp hc).symm.trans ((mem_fiber w d).mp hd))

section Weights

variable {R : Type*} [CommMonoid R] {s N : ℕ}

-- 读法：`wordWeight` 的取值由 `∏ j, a (w j)` 给出。
def wordWeight (a : Fin s → R) (w : Word s N) : R :=
  ∏ j, a (w j)

-- 读法：`countWeight` 的取值由 `∏ i, a i ^ (c i).val` 给出。
def countWeight (a : Fin s → R) (c : CountVector s N) : R :=
  ∏ i, a i ^ (c i).val

-- 读法：`wordWeight a w` 等于 `countWeight a (countVector w)`。
/-- 按位置上的字母分组，即可确定同一计数纤维内所有词的共同权重。这是一个精确的有限乘积恒等式。

英文原文：Grouping positions by their letters identifies the common weight of a
count fiber. This is an exact finite product identity.
-/
theorem wordWeight_eq_countWeight (a : Fin s → R) (w : Word s N) :
    wordWeight a w = countWeight a (countVector w) := by
  classical
  simpa [wordWeight, countWeight, countVector, occurrences] using
    (Finset.prod_fiberwise' Finset.univ w a).symm

-- 读法：`wordWeight a w` 等于 `countWeight a c`。
theorem wordWeight_eq_of_mem_fiber (a : Fin s → R)
    {c : CountVector s N} {w : Word s N} (hw : w ∈ fiber c) :
    wordWeight a w = countWeight a c := by
  rw [wordWeight_eq_countWeight, (mem_fiber w c).mp hw]

end Weights

section Mass

variable {R : Type*} [CommSemiring R] {s N : ℕ}

-- 读法：`fiberMass` 的取值由 `(fiber c).card * countWeight a c` 给出。
/-- 纤维的总质量等于其实际基数乘以其中各词的共同权重。

英文原文：Fiber mass is its actual cardinality times its common word weight.
-/
def fiberMass (a : Fin s → R) (c : CountVector s N) : R :=
  (fiber c).card * countWeight a c

-- 读法：结论为 `∑ w ∈ fiber c, wordWeight a w = fiberMass a c`。这里调用 `Finset.sum_congr`。
theorem sum_fiber_wordWeight (a : Fin s → R) (c : CountVector s N) :
    ∑ w ∈ fiber c, wordWeight a w = fiberMass a c := by
  calc
    ∑ w ∈ fiber c, wordWeight a w = ∑ _w ∈ fiber c, countWeight a c := by
      apply Finset.sum_congr rfl
      intro w hw
      exact wordWeight_eq_of_mem_fiber a hw
    _ = fiberMass a c := by simp [fiberMass]

-- 读法：结论为 `∑ w : Word s N, wordWeight a w = (∑ i, a i) ^ N`。这里调用 `Fintype.sum_pow`。
/-- 对所有长度为 `N` 的词应用有限分配律。

英文原文：Finite distributivity over all length-`N` words.
-/
theorem sum_wordWeight (a : Fin s → R) :
    ∑ w : Word s N, wordWeight a w = (∑ i, a i) ^ N := by
  exact (Fintype.sum_pow a N).symm

-- 读法：结论为 `∑ c : CountVector s N, fiberMass a c = (∑ i, a i) ^ N`。这里调用 `Finset.sum_congr`。
/-- 各纤维将全部词分组求和。空纤维贡献为零，不影响总质量。

英文原文：The fibers partition all words, including empty fibers without changing
the total mass.
-/
theorem sum_fiberMass (a : Fin s → R) :
    ∑ c : CountVector s N, fiberMass a c = (∑ i, a i) ^ N := by
  calc
    ∑ c : CountVector s N, fiberMass a c =
        ∑ c : CountVector s N, ∑ w ∈ fiber c, wordWeight a w := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (sum_fiber_wordWeight a c).symm
    _ = ∑ w : Word s N, wordWeight a w := by
      exact Finset.sum_fiberwise Finset.univ countVector (wordWeight a)
    _ = (∑ i, a i) ^ N := sum_wordWeight a

end Mass

-- 读法：存在 `c : CountVector s N`，`(∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s` 不超过 `fiberMass a c`。这里调用 `mul_div_cancel₀`。
/-- 在取任何极限之前得到的精确多项式开销界。

英文原文：Exact polynomial-overhead bound, before any limit is taken.
-/
theorem exists_fiberMass_ge_average {s N : ℕ} (a : Fin s → ℝ) :
    ∃ c : CountVector s N,
      (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s ≤ fiberMass a c := by
  classical
  have hd : ((N : ℝ) + 1) ^ s ≠ 0 := by positivity
  have hsum :
      (∑ _c : CountVector s N, (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s) =
        (∑ i, a i) ^ N := by
    simp only [Finset.sum_const, Finset.card_univ, card_countVector, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact mul_div_cancel₀ _ hd
  -- 推导：从 `Finset.exists_le_of_sum_le` 中取出 `c, hc, hbound`。
  obtain ⟨c, hc, hbound⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) Finset.univ_nonempty
    (f := fun _c : CountVector s N => (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s)
    (g := fiberMass a) (by rw [hsum, sum_fiberMass])
  exact ⟨c, hbound⟩

-- 读法：存在 `c : CountVector s N`，`(fiber c).Nonempty` 与 `(∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s ≤ fiberMass a c` 同时成立。
/-- 若总量为正，就可选出一个确实非空的词纤维。

英文原文：A positive total gives a genuinely nonempty selected word fiber.
-/
theorem exists_nonempty_fiberMass_ge_average {s N : ℕ} (a : Fin s → ℝ)
    (ha : 0 < ∑ i, a i) :
    ∃ c : CountVector s N, (fiber c).Nonempty ∧
      (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s ≤ fiberMass a c := by
  obtain ⟨c, hc⟩ := exists_fiberMass_ge_average (N := N) a
  have hmass : 0 < fiberMass a c :=
    lt_of_lt_of_le (div_pos (pow_pos ha N) (by positivity)) hc
  have hcard : (fiber c).card ≠ 0 := by
    intro hzero
    simp [fiberMass, hzero] at hmass
  exact ⟨c, Finset.card_pos.mp (Nat.pos_of_ne_zero hcard), hc⟩

end OAI.LinearAlgebra.TensorSpectrum.TagWords
