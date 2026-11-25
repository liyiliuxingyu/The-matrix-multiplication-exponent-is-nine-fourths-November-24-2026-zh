-- 本文件所属证明环节：为置换网络中配对的边作匹配和均衡着色，并把图论分配步骤编码成可计算的有限地址和置换。
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Ring.Parity
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Batcher
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Control.Named

section
/-!
# 在成对的边上交替着色

两端的对合有相同的不动点。在其余边上，每个交替环分成两步置换下的两个不交轨道。比较两轨道中的最小索引，就能在两种可能的着色中选定一种。

**英文原文**

Alternating colours on paired edges

The two endpoint involutions share their fixed points. On the remaining
edges each alternating cycle splits into two disjoint orbits of the
two-step permutation. Comparing the least indices of the two orbits
chooses one of the two possible colourings.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：逐一匹配以下输入模式：`0`、`k + 1`。
def jump {α : Type} (P : α → α) : ℕ → α → α
  | 0 => P
  | k + 1 => fun x => jump P k (jump P k x)

-- 读法：逐一匹配以下输入模式：`0`、`k + 1`。
def low {α : Type} [LinearOrder α] (P : α → α) : ℕ → α → α
  | 0 => id
  | k + 1 => fun x => min (low P k x) (low P k (jump P k x))

-- 读法：`colour` 的取值由 `decide (low (R ∘ L) h x < low (R ∘ L) h (L x))` 给出。
def colour (h : ℕ) (L R : Fin (2 ^ h) → Fin (2 ^ h)) (x : Fin (2 ^ h)) : Bool :=
  decide (low (R ∘ L) h x < low (R ∘ L) h (L x))

open Function

variable {α : Type}

-- 读法：`jump P k x` 等于 `P^[2 ^ k] x`。对 `k` 作归纳，并把 `x` 保持为任意参数。
private theorem jump_iterate (P : α → α) (k : ℕ) (x : α) :
    jump P k x = P^[2 ^ k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [jump, ih, pow_succ, mul_two, iterate_add_apply]

-- 读法：存在 `i : ℕ`，`low P k x` 等于 `P^[i] x`。对 `k` 作归纳，并把 `x` 保持为任意参数。
private theorem low_hit [LinearOrder α] (P : α → α) (k : ℕ) (x : α) :
    ∃ i : ℕ, low P k x = P^[i] x := by
  induction k generalizing x with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    simp only [low]
    rcases min_choice (low P k x) (low P k (jump P k x)) with h | h
    · rw [h]; exact ih x
    · obtain ⟨i, hi⟩ := ih (jump P k x)
      exact ⟨i + 2 ^ k, by rw [h, hi, jump_iterate, iterate_add_apply]⟩

-- 读法：`low P k x` 不超过 `P^[i] x`。对 `k` 作归纳，并把 `x i` 保持为任意参数。
private theorem low_le [LinearOrder α] (P : α → α) (k : ℕ) (x : α)
    (i : ℕ) (hi : i < 2 ^ k) : low P k x ≤ P^[i] x := by
  induction k generalizing x i with
  | zero =>
    have : i = 0 := by simpa using hi
    subst i
    rfl
  | succ k ih =>
    simp only [low]
    by_cases h : i < 2 ^ k
    · exact (min_le_left ..).trans (ih _ _ h)
    rw [pow_succ] at hi
    calc
      _ ≤ low P k (jump P k x) := min_le_right ..
      _ ≤ P^[i - 2 ^ k] (jump P k x) := ih _ _ (by omega)
      _ = P^[i] x := by rw [jump_iterate, ← iterate_add_apply, Nat.sub_add_cancel (by omega)]

-- 读法：`low P h (P x)` 等于 `low P h x`。这里调用 `low_le`。
private theorem low_step {h : ℕ} {P : Fin (2 ^ h) → Fin (2 ^ h)}
    (hp : Injective P) (x : Fin (2 ^ h)) : low P h (P x) = low P h x := by
  have hpos (y) : 0 < minimalPeriod P y :=
    minimalPeriod_pos_of_mem_periodicPts (by rw [injective_iff_periodicPts_eq_univ.mp hp]; trivial)
  have hmin (y) (i : ℕ) : low P h y ≤ P^[i] y := by
    rw [← iterate_mod_minimalPeriod_eq]
    apply low_le
    exact (Nat.mod_lt _ (hpos y)).trans_le (minimalPeriod_le_card.trans_eq (Fintype.card_fin _))
  apply le_antisymm
  · obtain ⟨i, hi⟩ := low_hit P h x
    have he : P^[minimalPeriod P x - 1] (P x) = x := by
      rw [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel (hpos x)]
      exact isPeriodicPt_minimalPeriod _ _
    rw [hi]
    simpa only [iterate_add_apply, he] using hmin (P x) (i + (minimalPeriod P x - 1))
  · obtain ⟨i, hi⟩ := low_hit P h (P x)
    rw [hi, ← iterate_succ_apply]
    exact hmin x _

-- 读法：`(R ∘ L)^[k] x` 不等于 `L x`。对 `k` 作归纳，采用 `Nat.twoStepInduction` 的归纳原则，并把 `x` 保持为任意参数。
private theorem no_mirror {L R : α → α} (hl : Involutive L) (hr : Involutive R)
    (hf : ∀ x, L x = x ↔ R x = x) (k : ℕ) (x : α) (hx : L x ≠ x) :
    (R ∘ L)^[k] x ≠ L x := by
  have hL (y) (hy : L y ≠ y) : L (L y) ≠ L y := hl.injective.ne hy
  have hR (y) (hy : L y ≠ y) : L (R y) ≠ R y :=
    (hf _).not.mpr (hr.injective.ne ((hf _).not.mp hy))
  induction k using Nat.twoStepInduction generalizing x with
  | zero => exact hx.symm
  | one => exact (hf _).not.mp (hL x hx)
  | more k ih _ =>
    intro h
    rw [iterate_succ_apply', iterate_succ_apply] at h
    have he : (R ∘ L) (L ((R ∘ L) x)) = L x := by simp only [comp_apply, hl _, hr _]
    exact ih ((R ∘ L) x) (hR _ (hL x hx))
      ((hr.injective.comp hl.injective) (h.trans he.symm))

variable {h : ℕ} {L R : Fin (2 ^ h) → Fin (2 ^ h)}

-- 读法：`low (R ∘ L) h x` 不等于 `low (R ∘ L) h (L x)`。
private theorem low_ne (hl : Involutive L) (hr : Involutive R) (hf : ∀ x, L x = x ↔ R x = x)
    {x : Fin (2 ^ h)} (hx : L x ≠ x) : low (R ∘ L) h x ≠ low (R ∘ L) h (L x) := by
  intro e
  obtain ⟨i, hi⟩ := low_hit (R ∘ L) h x
  obtain ⟨j, hj⟩ := low_hit (R ∘ L) h (L x)
  rw [hi, hj] at e
  have hp := hr.injective.comp hl.injective
  rcases le_total j i with hh | hh
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
    rw [iterate_add_apply] at e
    exact no_mirror hl hr hf k x hx ((hp.iterate j) e)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
    rw [iterate_add_apply] at e
    exact no_mirror hl hr hf k (L x) (hl.injective.ne hx) (((hp.iterate i) e.symm).trans (hl x).symm)

-- 读法：`colour h L R (L x)` 等于 `!(colour h L R x)`。
theorem colour_left (hl : Involutive L) (hr : Involutive R) (hf : ∀ x, L x = x ↔ R x = x)
    {x : Fin (2 ^ h)} (hx : L x ≠ x) : colour h L R (L x) = !(colour h L R x) := by
  unfold colour
  rw [hl x]
  rcases lt_or_gt_of_ne (low_ne hl hr hf hx) with h | h <;> simp [h, h.not_gt]

-- 读法：`colour h L R (R x)` 等于 `!(colour h L R x)`。
theorem colour_right (hl : Involutive L) (hr : Involutive R) (hf : ∀ x, L x = x ↔ R x = x)
    {x : Fin (2 ^ h)} (hx : L x ≠ x) : colour h L R (R x) = !(colour h L R x) := by
  rw [← colour_left hl hr hf hx]
  have hp := hr.injective.comp hl.injective
  have h₁ := low_step hp (L x)
  have h₂ := low_step hp (L (R x))
  simp only [comp_apply, hl _, hr _] at h₁ h₂
  simp only [colour, h₁, ← h₂, hl _]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 配对相邻的活动边

排序后，与顶点的任意初段相连的活动边构成前缀。该前缀长度为偶数，因此相邻配对不会横跨两个顶点，也不会跨越活动区的末端。

**英文原文**

Pairing adjacent active edges

After sorting, the active edges incident to any initial segment of
vertices form a prefix. Its length is even, so adjacent pairs never
straddle a change of vertex or the end of the active region.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h k : ℕ}

-- 读法：`permutation` 的取值由 `Tuple.sort (fun i => toLex (!a i, toLex (f i, i)))` 给出。
def permutation (f : Fin (2 ^ h) → Fin (2 ^ k)) (a : Fin (2 ^ h) → Bool) :=
  Tuple.sort (fun i => toLex (!a i, toLex (f i, i)))

-- 读法：逐一匹配以下输入模式：`0, i`、`h + 1, i`。
def toggle : (h : ℕ) → Fin (2 ^ h) → Fin (2 ^ h)
  | 0, i => i
  | h + 1, i => ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
      have := i.isLt
      simp only [pow_succ] at *
      split <;> omega⟩

-- 读法：当 `a i` 成立时取 `permutation f a (toggle h ((permutation f a).symm i))`，否则取 `i`。
def partner (f : Fin (2 ^ h) → Fin (2 ^ k)) (a : Fin (2 ^ h) → Bool) (i : Fin (2 ^ h)) : Fin (2 ^ h) :=
  if a i then permutation f a (toggle h ((permutation f a).symm i)) else i

-- 读法：`EvenFibers` 表示以下条件：对每个 `j`，要证明的命题是 `Even (Finset.univ.filter fun i => a i = true ∧ f i = j).card`。
def EvenFibers (f : Fin (2 ^ h) → Fin (2 ^ k)) (a : Fin (2 ^ h) → Bool) : Prop :=
  ∀ j, Even (Finset.univ.filter fun i => a i = true ∧ f i = j).card

-- 读法：要证明的命题是 `Function.Involutive (toggle h)`。对 `h` 分类讨论。
theorem toggle_involutive (h : ℕ) : Function.Involutive (toggle h) := by
  intro i
  cases h with
  | zero => rfl
  | succ h =>
    apply Fin.ext
    simp only [toggle]
    split_ifs <;> omega

variable {f : Fin (2 ^ h) → Fin (2 ^ k)} {a : Fin (2 ^ h) → Bool}

-- 读法：`a (permutation f a i) = true` 与 `f (permutation f a i) ≤ f (permutation f a j)` 同时成立。
private theorem ordered {i j : Fin (2 ^ h)} (hij : i ≤ j) (ha : a (permutation f a j) = true) :
    a (permutation f a i) = true ∧ f (permutation f a i) ≤ f (permutation f a j) := by
  have hs := Tuple.monotone_sort (fun i => toLex (!a i, toLex (f i, i))) hij
  let σ := permutation f a
  change toLex (!a (σ i), toLex (f (σ i), σ i)) ≤ toLex (!a (σ j), toLex (f (σ j), σ j)) at hs
  rw [Prod.Lex.toLex_le_toLex, ha] at hs
  rcases hs with he | ⟨he, hr⟩
  · cases e : a (σ i) <;> simp [e] at he
    exact absurd he (by decide)
  · refine ⟨by simpa using he, ?_⟩
    rcases Prod.Lex.toLex_le_toLex.mp hr with hl | hl
    · exact hl.le
    · exact hl.1.le

-- 读法：要证明的命题是 `Even (Finset.univ.filter fun i => a i = true ∧ f i ≤ j).card`。
private theorem EvenFibers.prefix_even (he : EvenFibers f a) (j : Fin (2 ^ k)) :
    Even (Finset.univ.filter fun i => a i = true ∧ f i ≤ j).card := by
  let S := Finset.univ.filter (fun i => a i)
  have hh := Finset.sum_card_fiberwise_eq_card_filter S (Finset.Iic j) f
  simp only [S, Finset.filter_filter, Finset.mem_Iic] at hh
  rw [← hh]
  choose b hb using he
  exact ⟨∑ t ∈ Finset.Iic j, b t, by simp only [hb, Finset.sum_add_distrib]⟩

-- 读法：`a (permutation f a j) = true` 与 `f (permutation f a j) = f (permutation f a i)` 同时成立。这里调用 `Finset.card_equiv`。
private theorem EvenFibers.adjacent (he : EvenFibers f a) {i j : Fin (2 ^ h)}
    (hi : i.val % 2 = 0) (hj : j.val = i.val + 1) (ha : a (permutation f a i) = true) :
    a (permutation f a j) = true ∧ f (permutation f a j) = f (permutation f a i) := by
  let σ := permutation f a
  by_contra bad
  have hn : (Finset.Iic i).card = (Finset.univ.filter fun l => a l = true ∧ f l ≤ f (σ i)).card := by
    apply Finset.card_equiv σ
    intro s
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hsi => ordered hsi ha, fun ⟨hs, hf⟩ => ?_⟩
    by_contra! hlt
    obtain ⟨ha', hf'⟩ := ordered (show j ≤ s by omega) hs
    exact bad ⟨ha', le_antisymm (hf'.trans hf) (ordered (show i ≤ j by omega) ha').2⟩
  obtain ⟨t, ht⟩ := he.prefix_even (f (σ i))
  rw [← hn, Fin.card_Iic] at ht
  omega

-- 读法：`a (permutation f a (toggle h i)) = true` 与 `f (permutation f a (toggle h i)) = f (permutation f a i) ∧ toggle h i ≠ i` 同时成立。对 `h` 分类讨论。
private theorem EvenFibers.neighbor (he : EvenFibers f a) (i : Fin (2 ^ h))
    (ha : a (permutation f a i) = true) :
    a (permutation f a (toggle h i)) = true ∧
    f (permutation f a (toggle h i)) = f (permutation f a i) ∧ toggle h i ≠ i := by
  cases h with
  | zero =>
    let z := permutation f a i
    let S := Finset.univ.filter (fun j => a j = true ∧ f j = f z)
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, rfl⟩⟩
    have hle : S.card ≤ 1 := by simpa using Finset.card_le_univ S
    obtain ⟨b, hb⟩ : Even S.card := he (f z)
    omega
  | succ h =>
    let j := toggle (h + 1) i
    by_cases ht : i.val % 2 = 0
    -- 推导：记下中间结论 `hj`：`j.val = i.val + 1`。
    · have hj : j.val = i.val + 1 := by simp [j, toggle, ht]
      obtain ⟨ha', heq⟩ := he.adjacent ht hj ha
      exact ⟨ha', heq, show j ≠ i by omega⟩
    · have hj : j.val = i.val - 1 := by simp [j, toggle, ht]
      have ha' := (ordered (show j ≤ i by omega) ha).1
      obtain ⟨_, heq⟩ := he.adjacent (i := j) (j := i) (by omega) (by omega) ha'
      exact ⟨ha', heq.symm, show j ≠ i by omega⟩

-- 读法：`a (partner f a i) = true` 与 `f (partner f a i) = f i ∧ partner f a i ≠ i` 同时成立。这里调用 `he.neighbor`。
private theorem EvenFibers.active (he : EvenFibers f a) {i : Fin (2 ^ h)} (hi : a i = true) :
    a (partner f a i) = true ∧ f (partner f a i) = f i ∧ partner f a i ≠ i := by
  obtain ⟨j, rfl⟩ := (permutation f a).surjective i
  simpa [partner, hi] using he.neighbor j hi

-- 读法：`partner f a i = i` 与 `a i = false` 等价。
theorem EvenFibers.fixed (he : EvenFibers f a) (i : Fin (2 ^ h)) :
    partner f a i = i ↔ a i = false := by
  cases hi : a i
  · simp [partner, hi]
  · simp [(he.active hi).2.2]

-- 读法：`f (partner f a i)` 等于 `f i`。这里调用 `he.active`。
theorem EvenFibers.preserve (he : EvenFibers f a) (i : Fin (2 ^ h)) : f (partner f a i) = f i := by
  cases hi : a i
  · rw [(he.fixed i).mpr hi]
  · exact (he.active hi).2.1

-- 读法：要证明的命题是 `Function.Involutive (partner f a)`。
theorem EvenFibers.involutive (he : EvenFibers f a) : Function.Involutive (partner f a) := by
  intro i
  cases hi : a i
  · rw [(he.fixed i).mpr hi, (he.fixed i).mpr hi]
  · have ha := (he.active hi).1
    rw [partner, ite_eq_left ha, partner, ite_eq_left hi, Equiv.symm_apply_apply,
      toggle_involutive, Equiv.apply_symm_apply]

-- 读法：`split` 的取值由 `colour h (partner f a) (partner g a)` 给出。
def split {h k : ℕ} (f g : Fin (2 ^ h) → Fin (2 ^ k)) (a : Fin (2 ^ h) → Bool) :=
  colour h (partner f a) (partner g a)

-- 读法：`2 * (Finset.univ.filter fun i => a i = true ∧ f i = j ∧ c i = b).card` 等于 `(Finset.univ.filter fun i => a i = true ∧ f i = j).card`。这里调用 `Finset.card_equiv`。
private theorem EvenFibers.half (he : EvenFibers f a) {c : Fin (2 ^ h) → Bool}
    (hc : ∀ i, a i = true → c (partner f a i) = !(c i)) (j : Fin (2 ^ k)) (b : Bool) :
    2 * (Finset.univ.filter fun i => a i = true ∧ f i = j ∧ c i = b).card =
      (Finset.univ.filter fun i => a i = true ∧ f i = j).card := by
  let S := Finset.univ.filter (fun i => a i = true ∧ f i = j)
  have eq : (S.filter fun i => c i = b).card = (S.filter fun i => c i ≠ b).card := by
    apply Finset.card_equiv he.involutive.toPerm
    intro i
    change i ∈ _ ↔ partner f a i ∈ _
    simp only [Finset.mem_filter, S, Finset.mem_univ, true_and, he.preserve]
    cases hi : a i
    · rw [(he.fixed i).mpr hi, hi]
      simp
    · rw [(he.active hi).1, hc i hi]
      cases b <;> cases c i <;> simp
  have sum := Finset.card_filter_add_card_filter_not (s := S) (fun i => c i = b)
  rw [← eq, ← two_mul] at sum
  simpa only [S, Finset.filter_filter, and_assoc] using sum

-- 读法：`split_balanced` 的证明用到 `hf.fixed`、`hg.fixed`、`hf.half`。
theorem split_balanced {g : Fin (2 ^ h) → Fin (2 ^ k)} (hf : EvenFibers f a) (hg : EvenFibers g a)
    (j : Fin (2 ^ k)) (b : Bool) :
    2 * (Finset.univ.filter fun i => a i = true ∧ f i = j ∧ split f g a i = b).card =
      (Finset.univ.filter fun i => a i = true ∧ f i = j).card ∧
    2 * (Finset.univ.filter fun i => a i = true ∧ g i = j ∧ split f g a i = b).card =
      (Finset.univ.filter fun i => a i = true ∧ g i = j).card := by
  have eq (i) : partner f a i = i ↔ partner g a i = i := (hf.fixed i).trans (hg.fixed i).symm
  exact ⟨hf.half (fun i hi => colour_left hf.involutive hg.involutive eq (hf.active hi).2.2) j b,
    hg.half (fun i hi => colour_right hf.involutive hg.involutive eq (hf.active hi).2.2) j b⟩

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 复合与并行操作的多项式开销

**英文原文**

Polynomial overhead for compositions and parallel operations
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {F : Type} [Field F] {h k c d : ℕ} {A D E : Format} {f : A.obj → D.obj}

-- 读法：`100 * (2 ^ h * (100 + k) ^ c)` 不超过 `2 ^ h * (100 + k) ^ (c + 1)`。这里调用 `Nat.mul_le_mul_left`。
private theorem grow (h k c : ℕ) :
    100 * (2 ^ h * (100 + k) ^ c) ≤ 2 ^ h * (100 + k) ^ (c + 1) := by
  rw [mul_comm 100, pow_succ, ← mul_assoc]
  exact Nat.mul_le_mul_left _ (by omega)

namespace Cheap

-- 读法：映射 `f` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ (d)` 为上界。
theorem mono (hf : Cheap F h k A D f c) (le : c ≤ d) : Cheap F h k A D f d := by
  obtain ⟨m, hf, hm⟩ := hf
  exact ⟨m, hf, hm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) le))⟩

-- 读法：映射 `f` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (l)) ^ (c)` 为上界。
theorem widen {l : ℕ} (hf : Cheap F h k A D f c) (le : k ≤ l) : Cheap F h l A D f c := by
  obtain ⟨m, hf, hm⟩ := hf
  exact ⟨m, hf, hm.trans (by gcongr)⟩

-- 读法：映射 `(g ∘ f)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((max c d + 1))` 为上界。
theorem comp {g : D.obj → E.obj} (hf : Cheap F h k A D f c) (hg : Cheap F h k D E g d) :
    Cheap F h k A E (g ∘ f) (max c d + 1) := by
  obtain ⟨m, hf, hm⟩ := hf.mono (le_max_left c d)
  obtain ⟨n, hg, hn⟩ := hg.mono (le_max_right c d)
  exact ⟨_, hf.comp hg, le_trans (by omega) (grow h k (max c d))⟩

-- 读法：映射 `(fun x => (f x, g x))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((max c d + 1))` 为上界。
theorem pair {g : A.obj → E.obj} (hf : Cheap F h k A D f c) (hg : Cheap F h k A E g d) :
    Cheap F h k A (.pair D E) (fun x => (f x, g x)) (max c d + 1) := by
  obtain ⟨m, hf, hm⟩ := hf.mono (le_max_left c d)
  obtain ⟨n, hg, hn⟩ := hg.mono (le_max_right c d)
  refine ⟨_, hf.pair hg, le_trans ?_ (grow h k (max c d))⟩
  rw [Format.width_pair]
  omega

-- 读法：映射 `_root_.id` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem id (F : Type) [Field F] (ha : A.width ≤ 2 ^ h * (100 + k) ^ c) :
    Cheap F h k A A _root_.id (c + 1) :=
  ⟨_, Circuit.id F A, le_trans (by omega) (grow h k c)⟩

-- 读法：映射 `(fun _ => x)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem const (F : Type) [Field F] (ha : A.width ≤ 2 ^ h * (100 + k) ^ c)
    (hd : D.width ≤ 2 ^ h * (100 + k) ^ c) (x : D.obj) :
    Cheap F h k A D (fun _ => x) (c + 1) := by
  have t : Install.Depends (fun _ : A.pins → Bool => D.code x) 0 :=
    fun _ => ⟨∅, by simp, fun _ _ _ => rfl⟩
  refine ⟨_, t.bnet F, le_trans ?_ (grow h k c)⟩
  change A.width + D.width + (A.width + 16 * D.width) ≤ _
  omega

-- 读法：映射 `f` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem project (F : Type) [Field F] (ha : A.width ≤ 2 ^ h * (100 + k) ^ c)
    (hd : D.width ≤ 2 ^ h * (100 + k) ^ c) (e : D.pins → A.pins)
    (he : ∀ x i, D.code (f x) i = A.code x (e i)) : Cheap F h k A D f (c + 1) :=
  ⟨_, Circuit.project e he, le_trans (by omega) (grow h k c)⟩

-- 读法：映射 `(fun x => (f x).1)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem fst {f : A.obj → D.obj × E.obj} (hf : Cheap F h k A (.pair D E) f c) :
    Cheap F h k A D (fun x => (f x).1) (c + 1) := by
  obtain ⟨m, hf, hm⟩ := hf
  have hp := Circuit.project (F := F) (A := .pair D E) (D := D) (f := Prod.fst) Sum.inl
    (fun _ _ => rfl)
  refine ⟨_, hf.comp hp, le_trans ?_ (grow h k c)⟩
  simp only [Format.width_pair] at hm ⊢
  omega

-- 读法：映射 `(fun x => (f x).2)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem snd {f : A.obj → D.obj × E.obj} (hf : Cheap F h k A (.pair D E) f c) :
    Cheap F h k A E (fun x => (f x).2) (c + 1) := by
  obtain ⟨m, hf, hm⟩ := hf
  have hp := Circuit.project (F := F) (A := .pair D E) (D := E) (f := Prod.snd) Sum.inr
    (fun _ _ => rfl)
  refine ⟨_, hf.comp hp, le_trans ?_ (grow h k c)⟩
  simp only [Format.width_pair] at hm ⊢
  omega

-- 读法：映射 `(fun x i => f i (x i))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ (c)` 为上界。这里调用 `hh.mono`。
theorem map (f : B h → A.obj → D.obj) (hf : ∀ i, Cheap F 0 k A D (f i) c) :
    Cheap F h k (.vec h A) (.vec h D) (fun x i => f i (x i)) c := by
  let m := (100 + k) ^ c - (A.width + D.width)
  have hc (i) : Circuit F A D (f i) m := by
    obtain ⟨_, hh, hm⟩ := hf i
    exact hh.mono (by simp [m] at *; omega)
  refine ⟨_, Circuit.map f hc, ?_⟩
  obtain ⟨_, _, hm⟩ := hf 0
  simp only [Format.width_vec, ← mul_add]
  exact Nat.mul_le_mul_left _ (by simp [m] at *; omega)

-- 读法：映射 `(fun x i => ((f x).1 i, (f x).2 i))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。
theorem zip {B : Format} {f : A.obj → (Coloring.B h → D.obj) × (Coloring.B h → B.obj)}
    (hf : Cheap F h k A (.pair (.vec h D) (.vec h B)) f c) :
    Cheap F h k A (.vec h (.pair D B)) (fun x i => ((f x).1 i, (f x).2 i)) (c + 1) := by
  let g (y : (Coloring.B h → D.obj) × (Coloring.B h → B.obj)) (i : Coloring.B h) := (y.1 i, y.2 i)
  have hz := Circuit.project (F := F) (A := .pair (.vec h D) (.vec h B))
    (D := .vec h (.pair D B)) (f := g) (Equiv.prodSumDistrib _ _ _)
    (by rintro x ⟨i, j | j⟩ <;> rfl)
  obtain ⟨_, hf, hm⟩ := hf
  refine ⟨_, hf.comp hz, le_trans ?_ (grow h k c)⟩
  simp only [Format.width_vec, Format.width_pair, mul_add] at hm ⊢
  omega

-- 读法：映射 `(f^[r])` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 1))` 为上界。对 `r` 作归纳。
theorem iterate {f : A.obj → A.obj} (hf : Cheap F h k A A f c) {r : ℕ} (hr : r ≤ k) :
    Cheap F h k A A (f^[r]) (c + 1) := by
  obtain ⟨m, hf, hm⟩ := hf
  have it (r : ℕ) : Circuit F A A (f^[r]) (A.width + r * m) := by
    induction r with
    | zero => simpa using Circuit.id F A
    | succ r ih =>
      rw [Function.iterate_succ', Nat.succ_mul, ← Nat.add_assoc]
      exact ih.comp hf
  refine ⟨_, it r, ?_⟩
  rw [pow_succ, ← mul_assoc]
  have := Nat.mul_le_mul hr (show m ≤ 2 ^ h * (100 + k) ^ c by omega)
  rw [mul_add, mul_comm _ 100, mul_comm _ k]
  omega

end Cheap
end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# 按指定次序对编码记录作双调排序

**英文原文**

Bitonic sorting in a prescribed order on encoded records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：在 `F` 上，函数 `(fun x => (min x.1 x.2, max x.1 x.2))` 从 `(.pair (word t) (word t))` 到 `(.pair (word t) (word t))` 的图张量可由至多 `(m + 100 * (1 + t))` 个顶点实现。用函数外延性比较等号两侧在 `⟨x, y⟩` 处的取值。
private theorem exchange {F : Type} [Field F] (t : ℕ) [L : LinearOrder (Val (word t))]
    {m : ℕ} (p : DNet F (.pair (word t) (word t)) .bit (fun x => decide (L.lt x.1 x.2)) m) :
    DNet F (.pair (word t) (word t)) (.pair (word t) (word t))
      (fun x => (min x.1 x.2, max x.1 x.2)) (m + 100 * (1 + t)) := by
  let a := word t
  have lo := selectWord F t
  have hi := lo.pre ((Rewire.swap a a).par (.id .bit))
  have k := ((DNet.id F (.pair a a)).pair p).comp (lo.pair hi)
  convert k.mono (n := m + 100 * (1 + t)) (by simp [wd, a]; omega) using 1
  funext ⟨x, y⟩
  by_cases hh : x < y
  · simp [hh, min_eq_left hh.le, max_eq_right hh.le]
  · simp [hh, min_eq_right (le_of_not_gt hh), max_eq_left (le_of_not_gt hh)]

variable {F : Type} [Field F] {A : Format} [LinearOrder A.obj] {m : ℕ}

-- 读法：在 `F` 上按格式 `(.vec h A)`、`(.vec h A)` 编码输入输出，映射 `(fun x => x ∘ Tuple.sort x)` 的电路规模至多为 `(2 ^ h * (h + 1) ^ 2 * (m + 100 * (1 + A.width) + A.width))`。
theorem Circuit.sort (cmp : Circuit F (.pair A A) .bit (fun x => decide (x.1 < x.2)) m)
    (h : ℕ) :
    Circuit F (.vec h A) (.vec h A) (fun x => x ∘ Tuple.sort x)
      (2 ^ h * (h + 1) ^ 2 * (m + 100 * (1 + A.width) + A.width)) := by
  let t := A.width
  let a := word t
  let e : A.pins ≃ slots (word A.width) := Fintype.equivOfCardEq (by simp [Format.width])
  let decode (x : Val a) := A.code.symm (bits a x ∘ e)
  have inj : Function.Injective decode := by
    intro x y eq
    have hh := A.code.symm.injective eq
    apply (bits a).injective
    funext j
    simpa using congrFun hh (e.symm j)
  let ord : LinearOrder (Val a) := LinearOrder.lift' decode inj
  let _ := ord
  -- 推导：记下中间结论 `hd`：`DNet F (.pair a a) .bit (fun x => decide (ord.lt x.1 x.2)) m`。
  have hd : DNet F (.pair a a) .bit (fun x => decide (ord.lt x.1 x.2)) m :=
    cmp (.pair a a) .bit (e.sumCongr e) (.refl _)
  have hn := sortTree_net (exchange t hd) h
  rw [wd_word] at hn
  obtain ⟨L, hL⟩ := Layout.exists_tree a h
  let i := ((Equiv.refl (B h)).prodCongr e).trans L.positions
  apply Circuit.of_dnet (a := tree h a) (b := tree h a) i i hn
  intro x
  let read (y : Val (tree h a)) := decode ∘ L.read y
  have er (y : Val (tree h a)) :
      (Format.vec h A).code.symm (bits (tree h a) y ∘ i) = read y := by
    funext j
    change A.code.symm _ = A.code.symm _
    simp [Layout.read, i, Function.comp_def]
    rfl
  -- 推导：记下中间结论 `ho`：`read (sortTree h x) = read x ∘ Tuple.sort (read x)`。
  have ho : read (sortTree h x) = read x ∘ Tuple.sort (read x) := by
    apply List.ofFn_injective
    have ep (y : Val (tree h a)) : List.ofFn (read y) = (flatten h y).map decode := by
      rw [← hL y, List.map_ofFn]
    rw [ep]
    refine List.Perm.eq_of_pairwise' ?_ (Tuple.monotone_sort _).sortedLE_ofFn.pairwise ?_
    · exact List.pairwise_map.mpr (sortTree_sorted h x)
    · exact ((sortTree_perm h x).map decode).trans
        ((ep x).symm ▸ (Equiv.Perm.ofFn_comp_perm ..).symm)
  apply (Format.vec h A).code.symm.injective
  rw [Equiv.symm_apply_apply, er, er]
  exact ho

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 比较小端序地址

**英文原文**

Comparing little-endian addresses
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：在后续公式中，`two` 是 `Wire.pair .bit .bit` 的缩写。
private abbrev two := Wire.pair .bit .bit
-- 读法：在后续公式中，`twoWords` 是 `Wire.pair (word n) (word n)` 的缩写。
private abbrev twoWords (n : ℕ) := Wire.pair (word n) (word n)

-- 读法：`cmp` 的取值由 `(decide (Lookup.value n x.1 < Lookup.value n x.2), decide (Lookup.value n x.1 = Lookup.value n x.2))` 给出。
private def cmp (n : ℕ) (x : Val (twoWords n)) : Val two :=
  (decide (Lookup.value n x.1 < Lookup.value n x.2),
   decide (Lookup.value n x.1 = Lookup.value n x.2))

variable (F : Type) [Field F]

-- 读法：在 `F` 上，函数 `(cmp n)` 从 `(twoWords n)` 到 `two` 的图张量可由至多 `(514 * n + 1)` 个顶点实现。对 `n` 作归纳。
private theorem cmp_net (n : ℕ) : DNet F (twoWords n) two (cmp n) (514 * n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih =>
    let combine (x : Val (.pair two two)) : Val two :=
      (x.2.1 || (x.2.2 && !x.1.1 && x.1.2), x.2.2 && (x.1.1 == x.1.2))
    have gate : DNet F (.pair two two) two combine 512 := by
      obtain ⟨m, hm, hc⟩ := Net.dense (.pair two two) two
        (fun x y => if combine x = y then (1 : F) else 0)
      exact ⟨m, hc, hm⟩
    have f := (((DNet.id F two).par ih).pre (.middle .bit (word n) .bit (word n))).comp gate
    convert f.mono (n := 514 * (n + 1) + 1) (by simp [wd]; omega) using 1
    funext ⟨⟨i, x⟩, ⟨j, y⟩⟩
    cases i <;> cases j <;> apply Prod.ext <;> apply Bool.eq_iff_iff.mpr <;>
      simp [cmp, combine, Lookup.value] <;> omega

-- 读法：在 `F` 上，函数 `(fun x => decide (Lookup.value n x.1 < Lookup.value n x.2))` 从 `(twoWords n)` 到 `.bit` 的图张量可由至多 `(520 * (1 + n))` 个顶点实现。
theorem lt_net (n : ℕ) : DNet F (twoWords n) .bit
    (fun x => decide (Lookup.value n x.1 < Lookup.value n x.2)) (520 * (1 + n)) :=
  ((cmp_net F n).comp (DNet.fst F .bit .bit)).mono (by simp [wd]; omega)

-- 读法：`(Format.addr n).code (Control.index n x)` 等于 `bits (word n) x`。
theorem code_addr (n : ℕ) (x : Val (word n)) :
    (Format.addr n).code (Control.index n x) = bits (word n) x := by
  change bits (word n) ((Control.index n).symm (Control.index n x)) = _
  rw [Equiv.symm_apply_apply]

-- 读法：`(Format.addr n).code.symm (bits (word n) x)` 等于 `Control.index n x`。
theorem decode_addr (n : ℕ) (x : Val (word n)) :
    (Format.addr n).code.symm (bits (word n) x) = Control.index n x := by
  rw [← code_addr, Equiv.symm_apply_apply]

-- 读法：`(Format.pair (.addr n) (.addr n)).code.symm (bits (twoWords n) x)` 等于 `(Control.index n x.1, Control.index n x.2)`。使用 `Prod.ext` 给出的结论。
theorem decode_pair (n : ℕ) (x : Val (twoWords n)) :
    (Format.pair (.addr n) (.addr n)).code.symm (bits (twoWords n) x) =
      (Control.index n x.1, Control.index n x.2) :=
  Prod.ext (decode_addr n x.1) (decode_addr n x.2)

-- 读法：在 `F` 上按格式 `(.pair (.addr n) (.addr n))`、`.bit` 编码输入输出，映射 `(fun x => decide (x.1 < x.2))` 的电路规模至多为 `(1000 * (1 + n))`。这里调用 `Circuit.of_dnet`。
theorem numeric_lt (n : ℕ) :
    Circuit F (.pair (.addr n) (.addr n)) .bit (fun x => decide (x.1 < x.2)) (1000 * (1 + n)) := by
  apply Circuit.of_dnet (.refl _) (.refl _) ((lt_net F n).mono (n := 1000 * (1 + n)) (by omega))
  intro x
  exact congrArg (fun y : B n × B n => bits .bit (decide (y.1 < y.2))) (decode_pair n x).symm

-- 读法：在 `F` 上按格式 `(.pair (.addr n) (.addr n))`、`(.addr n)` 编码输入输出，映射 `(fun x => min x.1 x.2)` 的电路规模至多为 `(1000 * (1 + n))`。这里调用 `Circuit.of_dnet`。
theorem numeric_min (n : ℕ) :
    Circuit F (.pair (.addr n) (.addr n)) (.addr n) (fun x => min x.1 x.2) (1000 * (1 + n)) := by
  have h := ((DNet.id F (twoWords n)).pair (lt_net F n)).comp (selectWord F n)
  apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 1000 * (1 + n)) (by simp [wd]; omega))
  intro x
  simp only [Equiv.coe_refl, Function.comp_id, decide_eq_true_eq]
  rw [decode_pair n x]
  by_cases hx : Lookup.value n x.1 < Lookup.value n x.2
  · rw [ite_eq_left hx, min_eq_left (show Control.index n x.1 ≤ Control.index n x.2 from hx.le), code_addr]
  · rw [ite_eq_right hx, min_eq_right (show Control.index n x.2 ≤ Control.index n x.1 from le_of_not_gt hx),
      code_addr]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 计算使数组有序的置换

**英文原文**

Computing the ordered permutation of an array
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：在后续公式中，`Format.lex` 是 `⟨Lex (A.obj × D.obj), A.pins ⊕ D.pins, (Format.pair A D).code⟩` 的缩写。
abbrev Format.lex (A D : Format) : Format :=
  ⟨Lex (A.obj × D.obj), A.pins ⊕ D.pins, (Format.pair A D).code⟩

-- 读法：`(A.lex D).width` 等于 `A.width + D.width`。使用 `Format.width_pair` 给出的结论。
@[simp] theorem Format.width_lex (A D : Format) :
    (A.lex D).width = A.width + D.width := Format.width_pair A D

variable {F : Type} [Field F]

-- 读法：在 `F` 上按格式 `A`、`.bit` 编码输入输出，映射 `f` 的电路规模至多为 `200`。这里调用 `hh.bnet`。
theorem small {A : Format} (hw : A.width ≤ 3) (f : A.obj → Bool) :
    Circuit F A .bit f 200 := by
  have hh : Install.Depends (Format.bit.code ∘ f ∘ A.code.symm) 3 := by
    intro i
    refine ⟨Finset.univ, hw, ?_⟩
    intro x y he
    rw [funext (fun j => he j (Finset.mem_univ _))]
  exact (hh.bnet F).mono (by change A.width + 134 * 1 ≤ 200; omega)

-- 读法：在 `F` 上按格式 `(.pair (.lex A D) (.lex A D))`、`.bit` 编码输入输出，映射 `(fun x => decide (x.1 < x.2))` 的电路规模至多为 `(50 * (A.width + D.width) + 2 * m + n + 200)`。
theorem lex_lt {A D : Format} [LinearOrder A.obj] [LinearOrder D.obj] {m n : ℕ}
    (ha : Circuit F (.pair A A) .bit (fun x => decide (x.1 < x.2)) m)
    (hd : Circuit F (.pair D D) .bit (fun x => decide (x.1 < x.2)) n) :
    Circuit F (.pair (.lex A D) (.lex A D)) .bit (fun x => decide (x.1 < x.2))
      (50 * (A.width + D.width) + 2 * m + n + 200) := by
  let X := Format.pair (.lex A D) (.lex A D)
  have l := Circuit.project (F := F) (A := X) (D := .pair A A)
    (f := fun x => (x.1.1, x.2.1)) (Sum.map Sum.inl Sum.inl)
    (by rintro x (i|j) <;> rfl)
  have r := Circuit.project (F := F) (A := X) (D := .pair A A)
    (f := fun x => (x.2.1, x.1.1)) (Sum.swap ∘ Sum.map Sum.inl Sum.inl)
    (by rintro x (i|j) <;> rfl)
  -- 推导：记下中间结论 `u`：`= Circuit.project (F`。
  have u := Circuit.project (F := F) (A := X) (D := .pair D D)
    (f := fun x => (x.1.2, x.2.2)) (Sum.map Sum.inr Sum.inr)
    (by rintro x (i|j) <;> rfl)
  have g := small (F := F) (A := .pair .bit (.pair .bit .bit)) (by simp)
    (fun x => x.1 || (!x.2.1 && x.2.2))
  have net := ((l.comp ha).pair ((r.comp ha).pair (u.comp hd))).comp g
  convert net.mono (n := 50 * (A.width + D.width) + 2 * m + n + 200)
    (by simp only [X, Format.width_pair, Format.width_lex]; omega) using 1
  funext ⟨x, y⟩
  change decide (toLex (x.1, x.2) < toLex (y.1, y.2)) = _
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, Prod.Lex.toLex_lt_toLex]
  grind

-- 读法：在后续公式中，`Fields` 是 `Format.pair (.vec h (.addr k)) (.vec h .bit)` 的缩写。
private abbrev Fields (h k : ℕ) := Format.pair (.vec h (.addr k)) (.vec h .bit)
-- 读法：在后续公式中，`Row` 是 `Format.lex .bit (.lex (.addr k) (.addr h))` 的缩写。
private abbrev Row (h k : ℕ) := Format.lex .bit (.lex (.addr k) (.addr h))

-- 读法：`rows` 的取值由 `toLex (!x.2 i, toLex (x.1 i, i))` 给出。
private def rows (h k : ℕ) (x : (Fields h k).obj) (i : B h) : (Row h k).obj :=
  toLex (!x.2 i, toLex (x.1 i, i))

-- 读法：在 `F` 上按格式 `(Fields h k)`、`(.vec h (Row h k))` 编码输入输出，映射 `(rows h k)` 的电路规模至多为 `((Fields h k).width + 34 * (Format.vec h (Row h k)).width)`。
private theorem prepared (F : Type) [Field F] (h k : ℕ) :
    Circuit F (Fields h k) (.vec h (Row h k)) (rows h k)
      ((Fields h k).width + 34 * (Format.vec h (Row h k)).width) := by
  classical
  have t : Install.Depends ((Format.vec h (Row h k)).code ∘ rows h k ∘ (Fields h k).code.symm) 1 := by
    rintro ⟨i, j | j | j⟩
    · refine ⟨{Sum.inr (i, ())}, by simp, fun x y e => ?_⟩
      exact congrArg Bool.not (e _ (by simp))
    · refine ⟨{Sum.inl (i, j)}, by simp, fun x y e => ?_⟩
      change (Format.addr k).code ((Format.addr k).code.symm _) _ =
        (Format.addr k).code ((Format.addr k).code.symm _) _
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact e _ (by simp)
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  exact t.bnet F

-- 读法：映射 `(fun x => ⇑(permutation x.1 x.2))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + ((h + k))) ^ (40)` 为上界。
theorem cheap_permutation (F : Type) [Field F] (h k : ℕ) :
    Cheap F h (h + k) (.pair (.vec h (.addr k)) (.vec h .bit)) (Perm h)
      (fun x => ⇑(permutation x.1 x.2)) 40 := by
  have flag := small (F := F) (A := .pair .bit .bit) (by simp) (fun x => decide (x.1 < x.2))
  have cmp := lex_lt flag (lex_lt (numeric_lt F k) (numeric_lt F h))
  have hs := cmp.sort h
  have out := Circuit.project (F := F) (A := .vec h (Row h k)) (D := Perm h)
    (f := fun x i => (x i).2.2) (fun z => (z.1, .inr (.inr z.2))) (fun _ _ => rfl)
  have net := ((prepared F h k).comp hs).comp out
  refine (show Cheap F h (h + k) (Fields h k) (Perm h) _ 5 from ⟨_, net, ?_⟩).mono (by decide)
  simp only [Format.width_pair, Format.width_lex, Format.width_addr,
    Format.width_vec]
  rw [Format.width_bit]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 同时对编码数据作间接读取

**英文原文**

Simultaneous indirect reads of encoded data
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install.BNet

variable {F I J : Type} [Field F] [Fintype I] [Fintype J]
variable {f : (I → Bool) → (J → Bool)} {m : ℕ}

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : Fin n × I → Bool) (p : Fin n × J) => f (fun j => x (p.1, j)) p.2)` 均在 `F` 上有顶点数至多为 `(n * m)` 的网络实现。对 `n` 作归纳。
private theorem copiesFin (h : BNet F f m) (n : ℕ) :
    BNet F (fun (x : Fin n × I → Bool) (p : Fin n × J) =>
      f (fun j => x (p.1, j)) p.2) (n * m) := by
  induction n with
  | zero =>
    have hp := (BNet.id F (Fin 0 × I)).rename (.refl _) (Equiv.equivOfIsEmpty _ (Fin 0 × J))
    convert hp using 1
    · funext x p
      exact p.1.elim0
    · simp
  | succ n ih =>
    let e (M : Type) := (Equiv.sumProdDistrib (Fin n) (Fin 1) M).symm.trans
      (finSumFinEquiv.prodCongr (.refl M))
    have k := (h.rename (Equiv.uniqueProd I (Fin 1)).symm (Equiv.uniqueProd J (Fin 1)).symm)
    rw [Nat.succ_mul]
    convert (ih.parallel k).rename (e I) (e J) using 1
    funext x p
    -- 推导：从 `(e J).surjective p` 中取出 `⟨i, j⟩ | ⟨i, j⟩, rfl`。
    obtain ⟨⟨i, j⟩ | ⟨i, j⟩, rfl⟩ := (e J).surjective p
    · simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rfl
    · rw [Fin.eq_zero i]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rfl

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : P × I → Bool) (p : P × J) => f (fun j => x (p.1, j)) p.2)` 均在 `F` 上有顶点数至多为 `(Fintype.card P * m)` 的网络实现。用函数外延性比较等号两侧在 `x p` 处的取值。
theorem copies (h : BNet F f m) (P : Type) [Fintype P] :
    BNet F (fun (x : P × I → Bool) (p : P × J) => f (fun j => x (p.1, j)) p.2)
      (Fintype.card P * m) := by
  let e := (Fintype.equivFin P).symm
  convert (h.copiesFin _).rename (e.prodCongr (.refl I)) (e.prodCongr (.refl J)) using 1
  funext x p
  simp

end OAI.LinearAlgebra.MatrixExponent.Install.BNet

namespace OAI.LinearAlgebra.MatrixExponent.Coloring
open Install

-- 读法：用函数外延性比较等号两侧在 `x ⟨i, j⟩` 处的取值。
private theorem read_all (F : Type) [Field F] (h : ℕ) (A : Format) :
    Circuit F (.pair (.vec h A) (Perm h)) (.vec h A) (fun y i => y.1 (y.2 i))
      ((2 ^ h * A.width + 2 ^ h * h) + 2 * (A.width * (2 ^ h + 2 ^ h * h)) +
        A.width * (10000 * 2 ^ h * (h + 1) ^ 3)) := by
  let e : A.pins × (B h ⊕ (B h × slots (word h))) →
      (Format.pair (.vec h A) (Perm h)).pins :=
    fun ⟨j, p⟩ => Sum.elim (fun i => .inl (i, j)) Sum.inr p
  have r := ((Control.read_net F h).copies A.pins).pull e
  have f := r.rename (.refl _) (Equiv.prodComm A.pins (B h))
  unfold Circuit
  convert f using 1
  · funext x ⟨i, j⟩
    change A.code (A.code.symm (fun j => x (.inl (Control.decode h (fun k => x (.inr (i, k))), j)))) j = _
    rw [Equiv.apply_symm_apply]
    rfl
  · simp [Format.width, Fintype.card_sum, Fintype.card_prod]

-- 读法：映射 `(fun y i => y.1 (y.2 i))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ (8)` 为上界。
theorem Cheap.lookup (F : Type) [Field F] (h k : ℕ) (A : Format)
    (hh : h ≤ k) (ha : A.width ≤ k) :
    Cheap F h k (.pair (.vec h A) (Perm h)) (.vec h A) (fun y i => y.1 (y.2 i)) 8 := by
  refine ⟨_, read_all F h A, ?_⟩
  simp only [Format.width_pair, Format.width_vec, Format.width_addr]
  calc
    _ = 2 ^ h * (5 * A.width + 2 * h + 2 * A.width * h + A.width * (10000 * (h + 1) ^ 3)) := by ring
    _ ≤ 2 ^ h * (5 * k + 2 * k + 2 * k * k + k * (10000 * (k + 1) ^ 3)) := by gcongr
    _ ≤ 2 ^ h * (100 + k) ^ 8 := by gcongr; ring_nf; omega

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# 带间接寻址的多个有限局部表的同时求值

地址宽度增长时，邻点数与记录格式保持固定。局部真值表可以依赖中心点。

**英文原文**

Simultaneous finite local tables with indirect addressing

The number of neighbors and the record format stay fixed as the
address width grows. The local truth table may depend on the center.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring
open Install

variable {F : Type} [Field F] {A D : Format} {h k c t : ℕ}

-- 读法：在 `F` 上按格式 `A`、`(.vec t D)` 编码输入输出，映射 `(fun x i => f i x)` 的电路规模至多为 `(2 ^ t * (3 * A.width + m))`。使用 `BNet.share` 给出的结论。
theorem Circuit.share (f : B t → A.obj → D.obj) {m : ℕ} (hf : ∀ i, Circuit F A D (f i) m) :
    Circuit F A (.vec t D) (fun x i => f i x) (2 ^ t * (3 * A.width + m)) :=
  BNet.share t _ hf

-- 读法：映射 `(fun x i => f i x)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ ((c + 2))` 为上界。这里调用 `hm.mono`。
theorem Cheap.share (f : B t → A.obj → D.obj) (hf : ∀ i, Cheap F h k A D (f i) c)
    (ht : 2 ^ t ≤ k) : Cheap F h k A (.vec t D) (fun x i => f i x) (c + 2) := by
  let x := 2 ^ h * (100 + k) ^ c
  have hx (i) : Circuit F A D (f i) x := by
    obtain ⟨m, hm, he⟩ := hf i
    exact hm.mono (by unfold x; omega)
  obtain ⟨m, _, hm⟩ := hf 0
  have ha : A.width ≤ x := by unfold x; omega
  have hd : D.width ≤ x := by unfold x; omega
  refine ⟨_, Circuit.share f hx, ?_⟩
  rw [Format.width_vec, pow_add, ← mul_assoc]
  change A.width + 2 ^ t * D.width + 2 ^ t * (3 * A.width + x) ≤ x * (100 + k) ^ 2
  calc
    _ ≤ x + k * x + k * (3 * x + x) := by gcongr
    _ = x * (1 + 5 * k) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

-- 读法：映射 `f` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (k)) ^ (1)` 为上界。
theorem Cheap.fixed (F : Type) [Field F] (f : A.obj → D.obj)
    (hk : 2 * A.width + D.width + localCost A.width * D.width ≤ k) :
    Cheap F 0 k A D f 1 := by
  have hd : Depends (D.code ∘ f ∘ A.code.symm) A.width :=
    fun _ => ⟨Finset.univ, le_rfl, fun _ _ h => by rw [funext fun i => h i (Finset.mem_univ _)]⟩
  refine ⟨_, hd.bnet F, ?_⟩
  change A.width + D.width + (A.width + localCost A.width * D.width) ≤ _
  simp only [pow_zero, one_mul, pow_one]
  omega

-- 读法：映射 `(fun x => (x.1, x.2 j))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ (3)` 为上界。这里调用 `Nat.mul_le_mul_left`。
private theorem pick (F : Type) [Field F] (A : Format) (h k t : ℕ)
    (hh : h ≤ k) (ha : A.width ≤ k) (ht : 2 ^ t ≤ k) (j : B t) :
    Cheap F h k (.pair (.vec h A) (.vec t (Perm h))) (.pair (.vec h A) (Perm h))
      (fun x => (x.1, x.2 j)) 3 := by
  let X := Format.pair (.vec h A) (.vec t (Perm h))
  let Y := Format.pair (.vec h A) (Perm h)
  have bound : A.width + 2 ^ t * h ≤ (100 + k) ^ 2 := by
    nlinarith only [ha, Nat.mul_le_mul ht hh]
  have bx : X.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simp only [X, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [mul_left_comm (2 ^ t), ← mul_add]
    exact Nat.mul_le_mul_left _ bound
  -- 推导：记下中间结论 `by'`：`Y.width ≤ 2 ^ h * (100 + k) ^ 2`。
  have by' : Y.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simp only [Y, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add]
    exact Nat.mul_le_mul_left _ (by nlinarith only [ha, hh])
  apply Cheap.project F bx by' (Sum.map _root_.id (fun i => (j, i)))
  rintro x (a | b) <;> rfl

-- 读法：映射 `(fun x i j => x.1 (x.2 j i))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (h) * (100 + (k)) ^ (12)` 为上界。
/-- 由任意地址向量汇集有界数量的邻居。

英文原文：Gather a bounded number of neighbors from arbitrary address vectors.
-/
theorem Cheap.neighbors (F : Type) [Field F] (A : Format) (h k t : ℕ)
    (hh : h ≤ k) (ha : A.width ≤ k) (ht : 2 ^ t ≤ k) :
    Cheap F h k (.pair (.vec h A) (.vec t (Perm h))) (.vec h (.vec t A))
      (fun x i j => x.1 (x.2 j i)) 12 := by
  let X := Format.pair (.vec h A) (.vec t (Perm h))
  have each (j : B t) : Cheap F h k X (.vec h A) (fun x i => x.1 (x.2 j i)) 9 :=
    (pick F A h k t hh ha ht j).comp (Cheap.lookup F h k A hh ha)
  have all := Cheap.share _ each ht
  let Z := Format.vec t (.vec h A)
  let W := Format.vec h (.vec t A)
  -- 推导：记下中间结论 `bw`：`W.width ≤ 2 ^ h * (100 + k) ^ 2`。
  have bw : W.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simp only [W, Format.width_vec]
    exact Nat.mul_le_mul_left _ (by nlinarith only [Nat.mul_le_mul ht ha])
  have bz : Z.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simpa only [Z, W, Format.width_vec, mul_left_comm] using bw
  have flip : Cheap F h k Z W (fun x i j => x j i) 3 :=
    Cheap.project F bz bw (fun p => (p.2.1, p.1, p.2.2)) fun _ _ => rfl
  have ans := all.comp flip
  simp only [Function.comp_def] at ans
  exact ans

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 判定地址是否重合

转置地址列表，在同一个中心处逐对比较地址。传入任意局部表的只有固定大小的相等性比特矩阵。

**英文原文**

Evaluating address coincidences

Transpose the address lists and compare every pair at the same center.
Only the fixed-size matrix of equality bits enters the arbitrary table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：在 `F` 上按格式 `(.pair (.addr h) (.addr h))`、`.bit` 编码输入输出，映射 `(fun x => decide (x.1 = x.2))` 的电路规模至多为 `(2 * h + 1)`。这里调用 `Circuit.of_dnet`。
theorem numeric_eq (F : Type) [Field F] (h : ℕ) :
    Circuit F (.pair (.addr h) (.addr h)) .bit (fun x => decide (x.1 = x.2)) (2 * h + 1) := by
  apply Circuit.of_dnet (.refl _) (.refl _) (Lookup.eq_net F h)
  intro x
  simp only [Equiv.coe_refl, Function.comp_id, decode_pair h x, (Control.index h).injective.eq_iff]

-- 读法：在后续公式中，`row` 是 `Format.vec t (.addr h)` 的缩写。
private abbrev row (t h : ℕ) := Format.vec t (.addr h)
-- 读法：在后续公式中，`pattern` 是 `Format.vec t (.vec t .bit)` 的缩写。
private abbrev pattern (t : ℕ) := Format.vec t (.vec t .bit)

-- 读法：映射 `(fun x j l => decide (x j = x l))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (k)) ^ (8)` 为上界。
private theorem row_pattern (F : Type) [Field F] (t h k : ℕ) (hh : h ≤ k) (ht : 2 ^ t ≤ k) :
    Cheap F 0 k (row t h) (pattern t) (fun x j l => decide (x j = x l)) 8 := by
  let A := Format.pair (.addr h) (.addr h)
  have bx : (row t h).width ≤ 2 ^ 0 * (100 + k) ^ 2 := by
    simp only [Format.width_vec, Format.width_addr, pow_zero, one_mul]
    nlinarith only [Nat.mul_le_mul ht hh]
  have ba : A.width ≤ 2 ^ 0 * (100 + k) ^ 2 := by
    simp only [A, Format.width_pair, Format.width_addr, pow_zero, one_mul]
    nlinarith only [hh]
  have pick (j l : B t) : Cheap F 0 k (row t h) A (fun x => (x j, x l)) 3 := by
    apply Cheap.project F bx ba (Sum.elim (fun i => (j, i)) (fun i => (l, i)))
    rintro x (i | i) <;> rfl
  -- 推导：记下中间结论 `cmp`：`Cheap F 0 k A .bit (fun x => decide (x.1 = x.2)) 2`。
  have cmp : Cheap F 0 k A .bit (fun x => decide (x.1 = x.2)) 2 := by
    refine ⟨_, numeric_eq F h, ?_⟩
    simp only [A, Format.width_pair, Format.width_addr, pow_zero, one_mul]
    change h + h + 1 + (2 * h + 1) ≤ (100 + k) ^ 2
    nlinarith only [hh]
  have each (j l : B t) : Cheap F 0 k (row t h) .bit (fun x => decide (x j = x l)) 4 :=
    (pick j l).comp cmp
  exact Cheap.share _ (fun j => Cheap.share _ (each j) ht) ht

-- 读法：结论为 `∃ k₀, ∀ h k : ℕ, h ≤ k → k₀ ≤ k → ∀ f : (B t → B t → Bool) → B q, Cheap F h k (.vec t (Perm h)) (.vec h (.addr q)) (fun w i => f (fun j l => decide (w j i = w l i))) 30`。
theorem Cheap.equalityTable (F : Type) [Field F] (t q : ℕ) :
    ∃ k₀, ∀ h k : ℕ, h ≤ k → k₀ ≤ k → ∀ f : (B t → B t → Bool) → B q,
      Cheap F h k (.vec t (Perm h)) (.vec h (.addr q))
        (fun w i => f (fun j l => decide (w j i = w l i))) 30 := by
  let P := pattern t
  let D := Format.addr q
  let c := 2 * P.width + D.width + Install.localCost P.width * D.width
  refine ⟨max c (2 ^ t), fun h k hh hk f => ?_⟩
  obtain ⟨hc, ht⟩ := max_le_iff.mp hk
  let X := Format.vec t (Perm h)
  let Y := Format.vec h (row t h)
  -- 推导：记下中间结论 `hy`：`Y.width ≤ 2 ^ h * (100 + k) ^ 2`。
  have hy : Y.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simp only [Y, Format.width_vec, Format.width_addr]
    exact Nat.mul_le_mul_left _ (by nlinarith only [Nat.mul_le_mul ht hh])
  have hx : X.width ≤ 2 ^ h * (100 + k) ^ 2 := by
    simpa only [X, Y, Format.width_vec, mul_left_comm] using hy
  have tr : Cheap F h k X Y (fun w i j => w j i) 3 :=
    Cheap.project F hx hy (fun p => (p.2.1, p.1, p.2.2)) fun _ _ => rfl
  have table : Cheap F 0 k P D f 1 := Cheap.fixed F _ hc
  have one := (row_pattern F t h k hh ht).comp table
  have net := tr.comp (Cheap.map _ (fun _ => one))
  exact net.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
