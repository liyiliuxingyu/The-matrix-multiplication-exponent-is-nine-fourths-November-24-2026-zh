-- 本文件所属证明环节：在有限域上把具有短标签的调用编成批量下降过程；结合带标签置换的难度和对角抵抗性，导出多份独立列表同时判重的规模下界。
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels

section
/-!
# 底数可变时的统一多项式界

**英文原文**

Uniform polynomial bounds with a variable base
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase

-- 读法：结构的字段包括 `two`、`bound`。
structure Poly {I : Type*} (s f : I → ℕ) : Prop where
  two : ∀ i, 2 ≤ s i
  bound : ∃ k : ℕ, ∀ i, f i ≤ s i ^ k

namespace Poly
variable {I : Type*} {s t f g : I → ℕ}

-- 读法：要证明的命题是 `Poly s (fun _ => n)`。
theorem const (h : ∀ i, 2 ≤ s i) (n : ℕ) : Poly s (fun _ => n) :=
  ⟨h, n, fun i => Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (h i) n)⟩

-- 读法：要证明的命题是 `Poly s f`。
theorem of_le (h : ∀ i, 2 ≤ s i) (hf : ∀ i, f i ≤ s i) : Poly s f :=
  ⟨h, 1, by simpa using hf⟩

-- 读法：要证明的命题是 `Poly s g`。
theorem mono (h : Poly s f) (hg : ∀ i, g i ≤ f i) : Poly s g :=
  let ⟨k, hk⟩ := h.bound
  ⟨h.two, k, fun i => (hg i).trans (hk i)⟩

-- 读法：要证明的命题是 `Poly t f`。
theorem grow (h : Poly s f) (ht : ∀ i, s i ≤ t i) : Poly t f :=
  let ⟨k, hk⟩ := h.bound
  ⟨fun i => (h.two i).trans (ht i), k, fun i => (hk i).trans (Nat.pow_le_pow_left (ht i) k)⟩

-- 读法：`n ^ i + n ^ j` 不超过 `n ^ (max i j + 1)`。这里调用 `Nat.add_le_add`。
theorem pow_sum {n : ℕ} (h : 2 ≤ n) (i j : ℕ) : n ^ i + n ^ j ≤ n ^ (max i j + 1) := by
  have hi := Nat.pow_le_pow_right (show 0 < n by omega) (le_max_left i j)
  have hj := Nat.pow_le_pow_right (show 0 < n by omega) (le_max_right i j)
  rw [pow_succ]
  exact (Nat.add_le_add hi hj).trans (by rw [← Nat.mul_two]; exact Nat.mul_le_mul_left _ h)

-- 读法：要证明的命题是 `Poly s (fun i => f i + g i)`。
theorem add (h : Poly s f) (h' : Poly s g) : Poly s (fun i => f i + g i) :=
  let ⟨j, hj⟩ := h.bound
  let ⟨k, hk⟩ := h'.bound
  ⟨h.two, max j k + 1, fun i => (Nat.add_le_add (hj i) (hk i)).trans (pow_sum (h.two i) ..)⟩

-- 读法：要证明的命题是 `Poly s (fun i => f i * g i)`。
theorem mul (h : Poly s f) (h' : Poly s g) : Poly s (fun i => f i * g i) :=
  let ⟨j, hj⟩ := h.bound
  let ⟨k, hk⟩ := h'.bound
  ⟨h.two, j + k, fun i => (Nat.mul_le_mul (hj i) (hk i)).trans_eq (pow_add ..).symm⟩

-- 读法：要证明的命题是 `Poly s (fun i => f i ^ n)`。
theorem pow (h : Poly s f) (n : ℕ) : Poly s (fun i => f i ^ n) :=
  let ⟨j, hj⟩ := h.bound
  ⟨h.two, j * n, fun i => (Nat.pow_le_pow_left (hj i) n).trans_eq (pow_mul ..).symm⟩

-- 读法：要证明的命题是 `Poly s f`。使用 `h.mono` 给出的结论。
theorem of_exp (h : Poly s (fun i => 2 ^ f i)) : Poly s f :=
  h.mono (fun _ => Nat.lt_two_pow_self.le)

-- 读法：要证明的命题是 `Poly s (fun i => 2 ^ (f i + g i))`。这里调用 `h.mul`。
theorem exp_add (h : Poly s (fun i => 2 ^ f i)) (h' : Poly s (fun i => 2 ^ g i)) :
    Poly s (fun i => 2 ^ (f i + g i)) := by
  simpa only [pow_add] using h.mul h'

-- 读法：要证明的命题是 `Poly s (fun i => Nat.clog 2 (f i))`。使用 `h.mono` 给出的结论。
theorem clog (h : Poly s f) : Poly s (fun i => Nat.clog 2 (f i)) :=
  h.mono (fun _ => (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le)

-- 读法：要证明的命题是 `Poly s (fun i => 2 ^ Nat.clog 2 (f i))`。
theorem exp_clog (h : Poly s f) : Poly s (fun i => 2 ^ Nat.clog 2 (f i)) := by
  refine ((h.add (const h.two 1)).mul (const h.two 2)).mono fun i => ?_
  cases he : Nat.clog 2 (f i) with
  | zero => rw [pow_zero]; omega
  | succ k =>
    have ht : ¬ f i ≤ 2 ^ k := fun hn => by
      have := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hn
      omega
    rw [pow_succ]
    exact Nat.mul_le_mul_right 2 (by omega)

end Poly
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase
end

/-!
# 对已标记候选项计数的电路

**英文原文**

Circuits for counting marked candidates
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

open Finset Install Classical
variable {F I J : Type} [Field F] [Fintype I] [Fintype J] {a b M : ℕ}

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : J → Bool) (_ : Unit) => decide (p (univ.filter (fun j => x j = true)).card))` 均在 `F` 上有顶点数至多为 `(M ^ 25)` 的网络实现。这里调用 `Nat.mul_le_mul_left`。
private theorem countTest (p : ℕ → Prop) (hM : 2 ≤ M) (hJ : Fintype.card J ≤ M ^ 2) :
    BNet F (fun (x : J → Bool) (_ : Unit) => decide (p (univ.filter (fun j => x j = true)).card))
      (M ^ 25) := by
  let w := Nat.log 2 (M ^ 2) + 1
  have hp : M ^ 2 < 2 ^ w := Nat.lt_pow_succ_log_self (by decide) _
  have ht : 2 ^ w ≤ 2 * M ^ 2 := by
    unfold w
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by positivity))
  have hw := (Nat.lt_two_pow_self (n := w)).trans_le ht
  clear_value w
  let f (x : slots (word w) → Bool) (_ : Unit) := decide (p (Control.decode w x).val)
  have hdep : Depends f w := by
    intro i
    exact ⟨univ, by simp, fun x y h => congrArg (fun t => f t i) (funext fun j => h j (mem_univ _))⟩
  have h := BNet.comp (Processor.Register.weighted F w (fun _ : J => 1)) (hdep.bnet F)
  -- 推导：记下中间结论 `hs`：`20000 * (1 + Fintype.card J) * (1 + w) + (w + localCost w) ≤ M ^ 25`。
  have hs : 20000 * (1 + Fintype.card J) * (1 + w) + (w + localCost w) ≤ M ^ 25 := by
    have hl : localCost w ≤ 40 * M ^ 2 := by unfold localCost; rw [pow_succ]; omega
    have hz : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ 20000 * (2 * M ^ 2) * (2 * M ^ 2) + 42 * M ^ 2 := by gcongr <;> omega
      _ ≤ 80042 * M ^ 4 := by nlinarith only [hz]
      _ ≤ _ := by
        rw [show M ^ 25 = M ^ 21 * M ^ 4 from pow_add M 21 4]
        exact Nat.mul_le_mul_right _ ((by decide : 80042 ≤ 2 ^ 21).trans (Nat.pow_le_pow_left hM _))
  simp only [card_slots, wd_word, Fintype.card_unit, mul_one] at h
  convert h.mono hs using 1
  funext x t
  -- 推导：记下中间结论 `hc`：`(univ.filter (fun j => x j = true)).card < 2 ^ w`。
  have hc : (univ.filter (fun j => x j = true)).card < 2 ^ w :=
    ((card_filter_le _ _).trans hJ).trans_lt hp
  simp only [f, Function.comp_apply, Processor.digits, Equiv.apply_symm_apply,
    Fin.val_ofNat, sum_boole, Nat.cast_id, Nat.mod_eq_of_lt hc]

-- 读法：`bound` 的取值由 `M ^ (25 + 6 * k)` 给出。
def bound (M k : ℕ) := M ^ (25 + 6 * k)

-- 读法：`Gate` 的取值由 `BNet F (fun x (_ : Unit) => decide (p x)) (bound M k)` 给出。
def Gate (F : Type) [Field F] (M k : ℕ) (p : (I → Bool) → Prop) :=
  BNet F (fun x (_ : Unit) => decide (p x)) (bound M k)

namespace Gate

variable {p q : (I → Bool) → Prop} (hM : 2 ≤ M) (hI : Fintype.card I ≤ M ^ 2)

omit [Fintype I] in
-- 读法：要证明的命题是 `Gate F M a q`。
theorem congr (h : Gate F M a p) (he : ∀ x, p x ↔ q x) : Gate F M a q := by
  simpa only [Gate, he] using h

include hM in
omit [Fintype I] in
-- 读法：要证明的命题是 `Gate F M b p`。使用 `BNet.mono` 给出的结论。
theorem mono (h : Gate F M a p) (hab : a ≤ b) : Gate F M b p :=
  BNet.mono h (Nat.pow_le_pow_right (by omega) (by omega))

include hM in
-- 读法：`t + u * (2 * t + bound M k) + bound M 0` 不超过 `bound M (k + 1)`。这里调用 `Nat.mul_le_mul_right`。
private theorem slack (k : ℕ) {t u : ℕ} (ht : t ≤ M ^ 2) (hu : u ≤ M ^ 2) :
    t + u * (2 * t + bound M k) + bound M 0 ≤ bound M (k + 1) := by
  let v := bound M k
  have ht' : t ≤ v := ht.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hb : bound M 0 ≤ v := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ v + M ^ 2 * (2 * v + v) + v := by gcongr
    _ = (2 + 3 * M ^ 2) * v := by ring
    _ ≤ M ^ 6 * v := by
      apply Nat.mul_le_mul_right
      have h4 : 16 ≤ M ^ 4 := Nat.pow_le_pow_left hM 4
      have h2 : 4 ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
      nlinarith only [h4, h2]
    _ = _ := by unfold v bound; rw [← pow_add]; congr 1; omega

include hM hI in
-- 读法：要证明的命题是 `Gate F M 0 (fun x => p (x i) (x j))`。这里调用 `hp.bnet`。
theorem atom (p : Bool → Bool → Prop) (i j : I) :
    Gate F M 0 (fun x => p (x i) (x j)) := by
  have hp : Depends (fun (x : I → Bool) (_ : Unit) => decide (p (x i) (x j))) 2 :=
    fun _ => ⟨{i, j}, card_le_two, fun x y h => by dsimp only; rw [h i (by simp), h j (by simp)]⟩
  apply (hp.bnet F).mono
  rw [Fintype.card_unit, mul_one]
  have he : M ^ 2 + localCost 2 ≤ M ^ 23 * M ^ 2 := by
    have h₁ : 100 ≤ M ^ 23 := (by decide : 100 ≤ 2 ^ 23).trans (Nat.pow_le_pow_left hM _)
    have h₂ : 4 ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
    change M ^ 2 + 68 ≤ _
    nlinarith only [h₁, h₂]
  exact (Nat.add_le_add_right hI _).trans (he.trans_eq (pow_add M 23 2).symm)

include hM hI in
-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun x j => decide (P j x))` 均在 `F` 上有顶点数至多为 `(bound M (a + 1))` 的网络实现。这里调用 `ht.mono`。
theorem collect (hJ : Fintype.card J ≤ M ^ 2) (P : J → (I → Bool) → Prop)
    (h : ∀ j, Gate F M a (P j)) :
    BNet F (fun x j => decide (P j x)) (bound M (a + 1)) := by
  have ht := (BNet.collect _ h).rename (.refl I) (Equiv.prodUnique _ Unit)
  exact ht.mono ((Nat.le_add_right ..).trans (slack hM a hI hJ))

include hM hI in
-- 读法：要证明的命题是 `Gate F M (a + 1) (fun x => f (univ.filter (fun j => P j x)).card)`。
theorem count (hJ : Fintype.card J ≤ M ^ 2) (P : J → (I → Bool) → Prop)
    (h : ∀ j, Gate F M a (P j)) (f : ℕ → Prop) :
    Gate F M (a + 1) (fun x => f (univ.filter (fun j => P j x)).card) := by
  have ht := (BNet.collect _ h).rename (.refl I) (Equiv.prodUnique _ Unit)
  have k := (ht.comp (countTest f hM hJ)).mono (slack hM a hI hJ)
  change BNet F (fun x (_ : Unit) => decide (f (univ.filter (fun j => decide (P j x) = true)).card)) _ at k
  simpa only [Gate, decide_eq_true_eq] using k

include hM hI in
-- 读法：要证明的命题是 `Gate F M (a + 1) (fun x => ∀ j, P j x)`。
theorem every (hJ : Fintype.card J ≤ M ^ 2) (P : J → (I → Bool) → Prop)
    (h : ∀ j, Gate F M a (P j)) : Gate F M (a + 1) (fun x => ∀ j, P j x) := by
  apply (count hM hI hJ P h (· = Fintype.card J)).congr
  intro x
  rw [← card_univ, card_filter_eq_iff]
  simp

include hM hI in
-- 读法：要证明的命题是 `Gate F M (a + 1) (fun x => ∃ j, P j x)`。
theorem any (hJ : Fintype.card J ≤ M ^ 2) (P : J → (I → Bool) → Prop)
    (h : ∀ j, Gate F M a (P j)) : Gate F M (a + 1) (fun x => ∃ j, P j x) := by
  apply (count hM hI hJ P h (0 < ·)).congr
  intro x
  simp [card_pos, filter_nonempty_iff]

include hM hI in
-- 读法：要证明的命题是 `Gate F M (a + 1) (fun x => ¬∃ j, P j x)`。
theorem absent (hJ : Fintype.card J ≤ M ^ 2) (P : J → (I → Bool) → Prop)
    (h : ∀ j, Gate F M a (P j)) : Gate F M (a + 1) (fun x => ¬∃ j, P j x) := by
  apply (count hM hI hJ P h (· = 0)).congr
  intro x
  simp [card_eq_zero, filter_eq_empty_iff]

include hM hI in
-- 读法：要证明的命题是 `Gate F M (a + 1) (fun x => p x ∧ q x)`。
theorem both (h : Gate F M a p) (k : Gate F M a q) :
    Gate F M (a + 1) (fun x => p x ∧ q x) := by
  let P (b : Bool) := if b then q else p
  have t : ∀ b, Gate F M a (P b) := by rintro (_|_); exact h; exact k
  exact (every hM hI (by simpa using hM.trans (Nat.le_pow (by decide : 0 < 2))) P t).congr
    (fun _ => by simp [P])

end Gate
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
end

/-!
# 压紧已标记的名称

每个名称的第一次被标记的出现位置是其代表。其信道编号等于在它之前的代表数量。

**英文原文**

Compacting marked names

The first marked occurrence of each name is its representative.
Its channel number is the count of earlier representatives.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

open Finset Classical
-- 读法：在后续公式中，`Input` 是 `K × Option (Fin e)` 的缩写。
abbrev Input (K : Type) (e : ℕ) := K × Option (Fin e)
-- 读法：在后续公式中，`Output` 是 `(Fin d × Fin e) ⊕ (K × Fin d)` 的缩写。
abbrev Output (K : Type) (d e : ℕ) := (Fin d × Fin e) ⊕ (K × Fin d)

variable {K : Type} [Fintype K] {d e : ℕ}

-- 读法：`name` 的取值由 `x (k, some j)` 给出。
def name (x : Input K e → Bool) (k : K) (j : Fin e) := x (k, some j)

-- 读法：`names` 的取值由 `(univ.filter (fun k => x (k, none) = true)).image (name x)` 给出。
def names (x : Input K e → Bool) :=
  (univ.filter (fun k => x (k, none) = true)).image (name x)

-- 读法：`pos` 的取值由 `(Fintype.equivFin K k).val` 给出。
private def pos (k : K) := (Fintype.equivFin K k).val

-- 读法：`lead` 表示以下条件：`x (k, none) = true` 与 `¬∃ j, (pos j < pos k ∧ x (j, none) = true) ∧ name x j = name x k` 同时成立。
private def lead (x : Input K e → Bool) (k : K) : Prop :=
  x (k, none) = true ∧ ¬∃ j, (pos j < pos k ∧ x (j, none) = true) ∧ name x j = name x k

-- 读法：`before` 的取值由 `univ.filter (fun j => pos j < pos k ∧ lead x j)` 给出。
private def before (x : Input K e → Bool) (k : K) :=
  univ.filter (fun j => pos j < pos k ∧ lead x j)

-- 读法：`atRank` 表示以下条件：`lead x k` 与 `(before x k).card = i.val` 同时成立。
private def atRank (x : Input K e → Bool) (k : K) (i : Fin d) : Prop :=
  lead x k ∧ (before x k).card = i.val

-- 读法：逐一匹配以下输入模式：`.inl (i, j)`、`.inr (k, i)`。
def run (d : ℕ) (x : Input K e → Bool) : Output K d e → Bool
  | .inl (i, j) => decide (∃ k, atRank x k i ∧ name x k j = true)
  | .inr (k, i) => decide (∃ t, atRank x t i ∧ name x t = name x k)

variable (x : Input K e → Bool)

-- 读法：`(pos (K := K))` 是单射。使用 `Fin.val_injective.comp` 给出的结论。
private theorem pos_injective : Function.Injective (pos (K := K)) :=
  Fin.val_injective.comp (Fintype.equivFin K).injective

-- 读法：存在 `j`，`lead x j` 与 `name x j = name x k` 同时成立。这里调用 `ht.not_ge`。
private theorem lead_exists (k : K) (hk : x (k, none) = true) :
    ∃ j, lead x j ∧ name x j = name x k := by
  let s := univ.filter (fun j => x (j, none) = true ∧ name x j = name x k)
  obtain ⟨j, hj, hle⟩ := exists_min_image s pos ⟨k, by simp [s, hk]⟩
  obtain ⟨hu, he⟩ := (mem_filter.mp hj).2
  refine ⟨j, ⟨hu, ?_⟩, he⟩
  rintro ⟨t, ⟨ht, hv⟩, h⟩
  exact ht.not_ge (hle t (mem_filter.mpr ⟨mem_univ _, hv, h.trans he⟩))

-- 读法：`k` 等于 `j`。这里调用 `pos_injective`。
private theorem lead_unique {k j : K} (hk : lead x k) (hj : lead x j)
    (he : name x k = name x j) : k = j := by
  apply pos_injective
  exact le_antisymm (le_of_not_gt (fun h => hk.2 ⟨j, ⟨h, hj.1⟩, he.symm⟩))
    (le_of_not_gt (fun h => hj.2 ⟨k, ⟨h, hk.1⟩, he⟩))

-- 读法：`(before x k).card` 严格小于 `s.card`。这里调用 `mem_filter.mp`。
private theorem rank_lt {k : K} (s : Finset K)
    (hm : k ∈ s) (hu : before x k ⊆ s) : (before x k).card < s.card :=
  card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hu, by
    intro he
    rw [← he] at hm
    exact (mem_filter.mp hm).2.1.false⟩)

-- 读法：`(before x k).card` 严格小于 `(names x).card`。这里调用 `h.trans_le`。
private theorem rank_bound {k : K} (hk : lead x k) : (before x k).card < (names x).card := by
  let s := univ.filter (lead x)
  have h := rank_lt x (k := k) s (by simp [s, hk]) (fun _ hj => mem_filter.mpr
    ⟨mem_univ _, (mem_filter.mp hj).2.2⟩)
  apply h.trans_le
  apply card_le_card_of_injOn (name x)
  · exact fun j hj => mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2.1⟩, rfl⟩
  · exact fun _ hj _ ht => lead_unique x (mem_filter.mp hj).2 (mem_filter.mp ht).2

-- 读法：`k` 等于 `j`。这里调用 `mem_filter.mpr`。
private theorem rank_unique {k j : K} {i : Fin d} (hk : atRank x k i) (hj : atRank x j i) :
    k = j := by
  have lt {u v : K} (hu : lead x u) (hv : pos u < pos v) :
      (before x u).card < (before x v).card := by
    refine rank_lt x (k := u) _ (mem_filter.mpr ⟨mem_univ _, hv, hu⟩) ?_
    intro t ht
    obtain ⟨h, h'⟩ := (mem_filter.mp ht).2
    exact mem_filter.mpr ⟨mem_univ _, h.trans hv, h'⟩
  rcases lt_trichotomy (pos k) (pos j) with h | h | h
  · exact ((lt hk.1 h).ne (hk.2.trans hj.2.symm)).elim
  · exact pos_injective h
  · exact ((lt hj.1 h).ne (hj.2.trans hk.2.symm)).elim

-- 读法：存在 `f : (Fin e → Bool) → Fin d`，对每个 `k`，由 `x (k, none) = true` 推出 `(∀ j, run d x (.inl (f (name x k), j)) = name x k j) ∧ (∀ i, run d x (.inr (k, i)) = decide (i = f (name x k)))`。按 `∃ k, lead x k ∧ name x k = v` 成立与否分情况。
/-- 在不同名称数满足上界时，各活跃出现位置的长名称与独热字段采用相同的信道分配。

英文原文：Under the distinct-name bound the long names and the one-hot fields
use the same channel assignment at every active occurrence.
-/
theorem correct (hd : 0 < d) (x : Input K e → Bool) (hx : (names x).card ≤ d) :
    ∃ f : (Fin e → Bool) → Fin d, ∀ k, x (k, none) = true →
      (∀ j, run d x (.inl (f (name x k), j)) = name x k j) ∧
      (∀ i, run d x (.inr (k, i)) = decide (i = f (name x k))) := by
  have pick (v : Fin e → Bool) : ∃ i : Fin d, ∀ k, lead x k → name x k = v → atRank x k i := by
    by_cases h : ∃ k, lead x k ∧ name x k = v
    · obtain ⟨k, hk, he⟩ := h
      refine ⟨⟨_, (rank_bound x hk).trans_le hx⟩, fun j hj hj' => ?_⟩
      rw [lead_unique x hj hk (hj'.trans he.symm)]
      exact ⟨hk, rfl⟩
    · exact ⟨⟨0, hd⟩, fun k hk he => (h ⟨k, hk, he⟩).elim⟩
  choose f hf using pick
  refine ⟨f, fun k hk => ?_⟩
  -- 推导：从 `lead_exists x k hk` 中取出 `t, ht, he`。
  obtain ⟨t, ht, he⟩ := lead_exists x k hk
  have h := hf _ t ht he
  constructor
  · intro j
    apply Bool.eq_iff_iff.mpr
    simp only [run, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hj⟩
      rwa [rank_unique x hq h, he] at hj
    · exact fun hj => ⟨t, h, he.symm ▸ hj⟩
  · intro i
    simp only [run, decide_eq_decide]
    exact ⟨fun ⟨q, hq, hq'⟩ => Fin.ext (hq.2.symm.trans (hf _ q hq.1 hq').2), fun e => ⟨t, e ▸ h, he⟩⟩

-- 读法：要证明的命题是 `Install.BNet F (run (K := K) (e := e) d) ((Fintype.card K + d + e + 2) ^ 100)`。这里调用 `Nat.mul_le_mul`。
/-- 即使输入的名称数量超过信道数，该网络也有定义。

英文原文：The network is defined even on inputs with more names than channels.
-/
theorem net (F K : Type) [Field F] [Fintype K] (d e : ℕ) :
    Install.BNet F (run (K := K) (e := e) d) ((Fintype.card K + d + e + 2) ^ 100) := by
  let M := Fintype.card K + d + e + 2
  let I := Input K e
  have hm : 2 ≤ M := by omega
  have hi : Fintype.card I ≤ M ^ 2 := by
    simp only [I, Input, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hk : Fintype.card K ≤ M ^ 2 :=
    (by omega : Fintype.card K ≤ M).trans (Nat.le_pow (by decide))
  -- 推导：记下中间结论 `he`：`Fintype.card (Fin e) ≤ M ^ 2`。
  have he : Fintype.card (Fin e) ≤ M ^ 2 := by
    rw [Fintype.card_fin]
    exact (by omega : e ≤ M).trans (Nat.le_pow (by decide))
  have hatom := Gate.atom (F := F) hm hi
  have used (k : K) : Gate F M 0 (fun x : I → Bool => x (k, none) = true) :=
    hatom (fun t _ => t = true) (k, none) (k, none)
  have same (j k : K) : Gate F M 1 (fun x : I → Bool => name x j = name x k) := by
    apply (Gate.every hm hi he _ (fun t => hatom Eq (j, some t) (k, some t))).congr
    exact fun x => funext_iff.symm
  have leads (k : K) : Gate F M 4 (fun x : I → Bool => lead x k) := by
    have prev (j : K) := hatom (fun t _ => pos j < pos k ∧ t = true) (j, none) (j, none)
    have both (j : K) := Gate.both hm hi ((prev j).mono hm (by decide : 0 ≤ 1)) (same j k)
    exact Gate.both hm hi ((used k).mono hm (by decide : 0 ≤ 3)) (Gate.absent hm hi hk _ both)
  have rank (k : K) (i : Fin d) : Gate F M 7 (fun x : I → Bool => atRank x k i) := by
    have prev (j : K) := hatom (fun _ _ => pos j < pos k) (j, none) (j, none)
    have both (j : K) := Gate.both hm hi ((prev j).mono hm (by decide : 0 ≤ 4)) (leads j)
    have hcnt := Gate.count hm hi hk _ both (· = i.val)
    apply Gate.both hm hi ((leads k).mono hm (by decide : 4 ≤ 6))
    apply hcnt.congr
    intro x
    simp only [before]
    congr! 4
  have output (j : Output K d e) : Gate F M 9 (fun x : I → Bool => run d x j = true) := by
    rcases j with ⟨i, t⟩ | ⟨k, i⟩
    · have bit (k : K) := hatom (fun a _ => a = true) (k, some t) (k, some t)
      have both (k : K) := Gate.both hm hi (rank k i) ((bit k).mono hm (by decide : 0 ≤ 7))
      exact (Gate.any hm hi hk _ both).congr (fun _ => by simp only [run, decide_eq_true_eq]; rfl)
    · have both (t : K) := Gate.both hm hi (rank t i) ((same t k).mono hm (by decide : 1 ≤ 7))
      exact (Gate.any hm hi hk _ both).congr (fun _ => by simp only [run, decide_eq_true_eq])
  -- 推导：记下中间结论 `ho`：`Fintype.card (Output K d e) ≤ M ^ 2`。
  have ho : Fintype.card (Output K d e) ≤ M ^ 2 := by
    simp only [Output, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [Nat.mul_comm d, ← Nat.add_mul, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have H := Gate.collect hm hi ho _ output
  have heq : (fun x j => @decide (run d x j = true) (propDecidable _)) =
      run (K := K) (e := e) d := by funext x j; simp
  rw [heq] at H
  exact H.mono (Nat.pow_le_pow_right (by omega) (by decide))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
end
