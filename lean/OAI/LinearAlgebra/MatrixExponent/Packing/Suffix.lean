-- 本文件所属证明环节：对二进分组的站点和线束装包、匹配及重新布线，逐项控制异常基区、临界负载、重置度数以及核心连线宽度的递推。
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Packing.Reservations
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi

section
/-!
# 将完整物件匹配到容量给定的箱中

**英文原文**

Matching whole items to bins of given capacity
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {I D : Type}

-- 读法：按 `∀ i, p i = none → size i = 0` 成立与否分情况。
theorem into_bins [Fintype I] [Fintype D] (size : I → ℕ) (cap : D → ℕ) (B : ℕ) (hsize : ∀ i, size i ≤ B) :
    ∃ p : I → Option D, (∀ i, (p i).isSome → 0 < size i) ∧
      (∀ d, (∑ i, if p i = some d then size i else 0) ≤ cap d) ∧
      min (∑ i, size i) (∑ d, cap d) ≤ (∑ i, if (p i).isSome then size i else 0) +
        B * (univ.filter fun d => 0 < cap d).card := by
  let used (p : I → Option D) d := ∑ i, if p i = some d then size i else 0
  let total (p : I → Option D) := ∑ i, if (p i).isSome then size i else 0
  let valid := univ.filter fun p : I → Option D =>
    (∀ i, (p i).isSome → 0 < size i) ∧ ∀ d, used p d ≤ cap d
  obtain ⟨p, hp, hm⟩ := valid.exists_max_image total ⟨fun _ => none, by simp [valid, used]⟩
  -- 推导：从 `(mem_filter.mp hp).2` 中取出 `hpos, hcap`。
  obtain ⟨hpos, hcap⟩ := (mem_filter.mp hp).2
  refine ⟨p, hpos, hcap, ?_⟩
  by_cases hall : ∀ i, p i = none → size i = 0
  · apply le_trans (min_le_left _ _)
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply sum_le_sum
    intro i _
    cases he : p i with
    | none => simp [hall i he]
    | some d => simp
  push Not at hall
  -- 推导：从 `hall` 中取出 `i, hi, hs`。
  obtain ⟨i, hi, hs⟩ := hall
  have small (d : D) : cap d ≤ used p d + B := by
    by_contra! big
    let q := Function.update p i (some d)
    have add (f : I → Option D → ℕ) (hz : f i none = 0) :
        (∑ j, f j (q j)) = (∑ j, f j (p j)) + f i (some d) := by
      rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ (fun j => f j (p j)) (mem_univ i)]
      simp only [q, Function.update_self, hi, hz, add_zero]
      congr 1
      exact sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
    -- 推导：记下中间结论 `hq`：`q ∈ valid`。
    have hq : q ∈ valid := by
      refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
      · intro j hj
        by_cases he : j = i
        · simpa [he] using Nat.pos_of_ne_zero hs
        · exact hpos j (by simpa [q, he] using hj)
      · intro b
        have he : used q b = used p b + if d = b then size i else 0 := by
          simpa only [Option.some.injEq] using
            add (fun j r => if r = some b then size j else 0) (by simp)
        rw [he]
        split_ifs with eq
        · subst b
          exact (Nat.add_le_add_left (hsize i) _).trans big.le
        · simpa using hcap b
    -- 推导：记下中间结论 `ht`：`total q = total p + size i`。
    have ht : total q = total p + size i :=
      add (fun j r => if r.isSome then size j else 0) rfl
    have := hm q hq
    omega
  have he : (∑ d, used p d) = total p := by
    unfold used total
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    cases p j <;> simp
  calc
    _ ≤ ∑ d, cap d := min_le_right _ _
    _ ≤ ∑ d, (used p d + if 0 < cap d then B else 0) := by
      apply sum_le_sum
      intro d _
      split_ifs <;> first | exact small d | omega
    _ = _ := by rw [sum_add_distrib, he, ← sum_filter, sum_const, Nat.nsmul_eq_mul, mul_comm]

-- 读法：存在 `mate : {e // (plan e).isSome} ↪ E`，对每个 `e`，存在 `d`，`plan e.val = some d` 与 `mate e ∈ stock (src e.val) d` 同时成立。
/-- 将每个选定单位匹配到指定箱中的一个不同单位。

英文原文：Match each selected unit to a distinct unit of the specified bin.
-/
theorem match_units {E : Type} [Fintype E] (src : E → I) (plan : E → Option D)
    (stock : I → D → Finset E)
    (unique : ∀ i j d c e, e ∈ stock i d → e ∈ stock j c → i = j ∧ d = c)
    (enough : ∀ i d, (univ.filter fun e => src e = i ∧ plan e = some d).card ≤
      (stock i d).card) :
    ∃ mate : {e // (plan e).isSome} ↪ E, ∀ e, ∃ d,
      plan e.val = some d ∧ mate e ∈ stock (src e.val) d := by
  let items i d := univ.filter fun e => src e = i ∧ plan e = some d
  have ex (i d) : ∃ f : E → E, (∀ e ∈ items i d, f e ∈ stock i d) ∧
      Set.InjOn f (items i d) := by
    obtain ⟨g⟩ : Nonempty (items i d ↪ stock i d) := Function.Embedding.nonempty_of_card_le
      (by simpa only [Fintype.card_coe] using enough i d)
    let f e := if he : e ∈ items i d then (g ⟨e, he⟩).val else e
    refine ⟨f, ?_, ?_⟩
    · intro e he; simp [f, he]
    · intro a ha b hb he
      simp only [mem_coe] at ha hb
      simp only [f, dite_eq_left ha, dite_eq_left hb] at he
      exact congrArg Subtype.val (g.injective (Subtype.ext he))
  choose f hm hi using ex
  let D' := {e // (plan e).isSome}
  let bin (e : D') := (plan e.val).get e.property
  have hb (e : D') : plan e.val = some (bin e) := (Option.some_get _).symm
  have he (e : D') : e.val ∈ items (src e.val) (bin e) :=
    mem_filter.mpr ⟨mem_univ _, rfl, hb e⟩
  let g (e : D') := f (src e.val) (bin e) e.val
  have hg (e : D') : g e ∈ stock (src e.val) (bin e) := hm _ _ _ (he e)
  have inj : Function.Injective g := by
    intro x y h
    -- 推导：从 `unique _ _ _ _ _ (hg x) (h.symm ▸ hg y)` 中取出 `h₁, h₂`。
    obtain ⟨h₁, h₂⟩ := unique _ _ _ _ _ (hg x) (h.symm ▸ hg y)
    have hx := he x
    dsimp only [g] at h
    rw [h₁, h₂] at h hx
    exact Subtype.ext (hi _ _ hx (he y) h)
  exact ⟨⟨g, inj⟩, fun e => ⟨bin e, hb e, hg e⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# 二进制单元的仿射着色

对于两个不同的单元，选取一个恰好在其中一个单元上为零的仿射形式，用它平移颜色，就会抵消这两个单元在二阶矩中的交叉项。

**英文原文**

Affine colorings of binary cells

For two distinct cells, translating the color by an affine form that
vanishes at just one of them cancels their cross term in the second moment.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

open scoped Classical

-- 读法：在后续公式中，`Color` 是 `Cell h × ZMod 2` 的缩写。
abbrev Color (h : ℕ) := Cell h × ZMod 2

-- 读法：`thick` 表示以下条件：`(∑ i, c.1 i * x i) + c.2` 等于 `0`。
def thick {h} (c : Color h) (x : Cell h) : Prop :=
  (∑ i, c.1 i * x i) + c.2 = 0

-- 读法：`thick (c + d) x` 与 `(thick c x ↔ thick d x)` 等价。
private theorem thick_add {h} (c d : Color h) (x : Cell h) :
    thick (c + d) x ↔ (thick c x ↔ thick d x) := by
  have parity : ∀ u v : ZMod 2, u + v = 0 ↔ (u = 0 ↔ v = 0) := by decide
  unfold thick
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [add_add_add_comm, parity]

-- 读法：当 `thick c x` 成立时取 `w x`，否则取 `-w x`。
private noncomputable def signed {h} (w : Cell h → ℝ) (c : Color h) (x : Cell h) : ℝ :=
  if thick c x then w x else -w x

-- 读法：结论为 `∑ c : Color h, signed w c x * signed w c y = 0`。按 `thick c y <;> simp [hy]` 成立与否分情况。
private theorem cross_term {h} (w : Cell h → ℝ) {x y : Cell h} (hxy : y ≠ x) :
    ∑ c : Color h, signed w c x * signed w c y = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  let d : Color h := (fun j => if j = i then 1 else 0, -x i)
  have hd (z : Cell h) : thick d z ↔ z i = x i := by
    simp only [thick, d, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq', ← sub_eq_add_neg, sub_eq_zero]
  have flip (c : Color h) :
      signed w (c + d) x * signed w (c + d) y = -(signed w c x * signed w c y) := by
    simp only [signed, thick_add, hd, hi, iff_true, iff_false]
    by_cases hy : thick c y <;> simp [hy]
  have he := Equiv.sum_comp (Equiv.addRight d) (fun c => signed w c x * signed w c y)
  change (∑ c, signed w (c + d) x * signed w (c + d) y) = _ at he
  simp_rw [flip, Finset.sum_neg_distrib] at he
  exact eq_zero_of_neg_eq he

-- 读法：`(∑ c : Color h, (∑ x, signed w c x) ^ 2)` 等于 `∑ _c : Color h, ∑ x, (w x) ^ 2`。这里调用 `Finset.sum_congr`。
private theorem second_moment {h} (w : Cell h → ℝ) :
    (∑ c : Color h, (∑ x, signed w c x) ^ 2) = ∑ _c : Color h, ∑ x, (w x) ^ 2 := by
  simp_rw [pow_two, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm, Fintype.sum_eq_single x (fun y hy => cross_term w hy)]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hx : thick c x <;> simp [signed, hx]

-- 读法：存在 `c : Color h`，`(∑ p, |∑ x, if thick c x then w p x else -w p x|) ^ 2` 不超过 `B * Fintype.card P * (∑ p, ∑ x, w p x)`。
theorem coloring {P : Type} [Fintype P] {h : ℕ} (w : P → Cell h → ℝ) (B : ℝ)
    (hw : ∀ p x, 0 ≤ w p x ∧ w p x ≤ B) :
    ∃ c : Color h, (∑ p, |∑ x, if thick c x then w p x else -w p x|) ^ 2 ≤
      B * Fintype.card P * (∑ p, ∑ x, w p x) := by
  have he : (∑ c : Color h, ∑ p, (∑ x, signed (w p) c x) ^ 2) =
      ∑ _c : Color h, ∑ p, ∑ x, (w p x) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [second_moment]
    rw [Finset.sum_comm]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty he.le
  -- 推导：记下中间结论 `hb`：`(∑ p, ∑ x, (w p x) ^ 2) ≤ B * ∑ p, ∑ x, w p x`。
  have hb : (∑ p, ∑ x, (w p x) ^ 2) ≤ B * ∑ p, ∑ x, w p x := by
    simp_rw [Finset.mul_sum, pow_two]
    exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hw p x).2 (hw p x).1
  refine ⟨c, ?_⟩
  calc
    _ ≤ (Fintype.card P : ℝ) * ∑ p, |∑ x, signed (w p) c x|^2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (Fintype.card P : ℝ) * (B * ∑ p, ∑ x, w p x) := by
      simp_rw [sq_abs]
      exact mul_le_mul_of_nonneg_left (hc.trans hb) (Nat.cast_nonneg _)
    _ = _ := by ac_rfl

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 在单个二进组中匹配核心连线单位

将一个细出现项视为不可拆分的物件。匹配完成后，可把目的地相同的细出现项汇入同一个包。因此每箱至多有一个细包，另外还有一个未匹配包，总负载不超过所在群的负载。

**英文原文**

Matching core wire units within one dyadic group

Treat a thin occurrence as one indivisible item. After the matching,
thin occurrences with the same destination can be gathered into one
pack. This gives at most one thin pack per bin plus an unmatched pack,
with total load bounded by the load of the colony.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {E P : Type} {h : ℕ}

-- 读法：结构的字段包括 `color`、`plan`、`thin`、`used`、`mate`。
/-- 某个出现项的所有出发单位，要么都未匹配，要么分别与从同一源群到同一目的地的互异粗单位配对。

英文原文：All outgoing units of an occurrence are either unmatched or paired
with distinct thick units from one source colony to one destination.
-/
structure Matching (src dst : E → P) (ix : E → Cell h) where
  color : Color h
  plan : P → Cell h → Option P
  thin : ∀ p x, (plan p x).isSome → ¬thick color x
  used : ∀ p x, (plan p x).isSome → ∃ e, src e = p ∧ ix e = x
  mate : {e // (plan (src e) (ix e)).isSome} ↪ E
  spec : ∀ e, thick color (ix (mate e)) ∧ src (mate e) = src e.val ∧
    plan (src e.val) (ix e.val) = some (dst (mate e))

-- 读法：`Matching.count` 的取值由 `(univ.filter fun e => (m.plan (src e) (ix e)).isSome).card` 给出。
def Matching.count [Fintype E] {src dst : E → P} {ix : E → Cell h} (m : Matching src dst ix) :=
  (univ.filter fun e => (m.plan (src e) (ix e)).isSome).card

-- 读法：`(∑ i, if p i then (s.filter fun e => f e = i).card else 0)` 等于 `(s.filter fun e => p (f e)).card`。
private theorem count_if {I : Type} [Fintype I] [DecidableEq I] (s : Finset E) (f : E → I) (p : I → Prop) [DecidablePred p] :
    (∑ i, if p i then (s.filter fun e => f e = i).card else 0) =
      (s.filter fun e => p (f e)).card := by
  rw [← sum_filter, sum_card_fiberwise_eq_card_filter s _ f]
  simp

-- 读法：结论为 `∑ i, (s.filter fun e => f e = i).card = s.card`。这里调用 `count_if`。
private theorem count_all {I : Type} [Fintype I] [DecidableEq I] (s : Finset E) (f : E → I) :
    ∑ i, (s.filter fun e => f e = i).card = s.card := by
  simpa using count_if s f (fun _ => True)

variable [Fintype E] [Fintype P] (src dst : E → P) (ix : E → Cell h)

-- 读法：`out` 的取值由 `univ.filter fun e => src e = p` 给出。
private def out (p : P) := univ.filter fun e => src e = p
-- 读法：`units` 的取值由 `((out src p).filter fun e => ix e = x).card` 给出。
private def units (p : P) (x : Cell h) := ((out src p).filter fun e => ix e = x).card

-- 读法：结论为 `∃ m : Matching src dst ix, (∑ p, min (∑ x, if thick c x then 0 else units src ix p x) (∑ x, if thick c x then units src ix p x else 0)) ≤ m.count + b * K * Fintype.card P`。
private theorem match_color (b K : ℕ) (c : Color h)
    (hs : ∀ p x, units src ix p x ≤ b)
    (hd : ∀ p, ((out src p).image dst).card ≤ K) :
    ∃ m : Matching src dst ix, (∑ p,
      min (∑ x, if thick c x then 0 else units src ix p x)
          (∑ x, if thick c x then units src ix p x else 0)) ≤
      m.count + b * K * Fintype.card P := by
  let size p x := if thick c x then 0 else units src ix p x
  let thickOut p := (out src p).filter fun e => thick c (ix e)
  let stock p d := (thickOut p).filter fun e => dst e = d
  let cap p d := (stock p d).card
  have hsize p x : size p x ≤ b := by unfold size; split_ifs <;> simp [hs]
  choose plan hpos hcap htotal using fun p => into_bins (size p) (cap p) b (hsize p)
  have thin p x (hx : (plan p x).isSome) : ¬thick c x := by
    intro h
    simpa [size, h] using hpos p x hx
  have used p x (hx : (plan p x).isSome) : ∃ e, src e = p ∧ ix e = x := by
    have hn := hpos p x hx
    simp only [size, ite_eq_right (thin p x hx), units, card_pos] at hn
    -- 推导：从 `hn` 中取出 `e, he`。
    obtain ⟨e, he⟩ := hn
    exact ⟨e, by simpa [out] using he⟩
  let sel e := plan (src e) (ix e)
  have count p (r : Option P → Prop) [DecidablePred r] (hr : ¬ r none) :
      (∑ x, if r (plan p x) then size p x else 0) =
        (univ.filter fun e => src e = p ∧ r (sel e)).card := by
    trans ∑ x, if r (plan p x) then units src ix p x else 0
    · apply sum_congr rfl
      intro x _
      cases ht : plan p x with
      | none => simp [hr]
      | some d => rw [show size p x = units src ix p x by simp [size, thin p x (by simp [ht])]]
    · rw [show units src ix p = fun x => ((out src p).filter fun e => ix e = x).card from rfl,
        count_if (out src p) ix (fun x => r (plan p x))]
      congr 1
      ext e
      simp only [out, sel, mem_filter, mem_univ, true_and]
      by_cases hp : src e = p <;> simp [hp]
  have mem p d e : e ∈ stock p d ↔ src e = p ∧ thick c (ix e) ∧ dst e = d := by
    simp [stock, thickOut, out, and_assoc]
  -- 推导：从 `match_units src sel stock` 中取出 `mate, hm`。
  obtain ⟨mate, hm⟩ := match_units src sel stock
    (fun i j d t e h h' => by
      rw [mem] at h h'
      exact ⟨h.1.symm.trans h'.1, h.2.2.symm.trans h'.2.2⟩)
    (fun p d => by rw [← count p (· = some d) (by simp)]; exact hcap p d)
  let m : Matching src dst ix := ⟨c, plan, thin, used, mate, fun e => by
    obtain ⟨d, he, hf⟩ := hm e
    rw [mem] at hf
    exact ⟨hf.2.1, hf.1, hf.2.2.symm ▸ he⟩⟩
  refine ⟨m, ?_⟩
  let selected := univ.filter fun e => (sel e).isSome
  have each (p : P) :
      min (∑ x, size p x) (∑ x, if thick c x then units src ix p x else 0) ≤
        (selected.filter fun e => src e = p).card + b * K := by
    -- 推导：记下中间结论 `thickSum`：`(∑ x, if thick c x then units src ix p x else 0) = ∑ d, cap p d`。
    have thickSum : (∑ x, if thick c x then units src ix p x else 0) = ∑ d, cap p d :=
      (count_if (out src p) ix (thick c)).trans (count_all (thickOut p) dst).symm
    have bins : (univ.filter fun d => 0 < cap p d).card ≤ K := by
      apply le_trans _ (hd p)
      apply card_le_card
      intro d hx
      obtain ⟨e, he⟩ := card_pos.mp (mem_filter.mp hx).2
      exact mem_image.mpr ⟨e, (mem_filter.mp (mem_filter.mp he).1).1, (mem_filter.mp he).2⟩
    rw [thickSum]
    apply (htotal p).trans
    rw [count p (fun r => r.isSome) (by simp)]
    simpa only [selected, filter_filter, and_comm] using
      Nat.add_le_add_left (Nat.mul_le_mul_left b bins) (selected.filter fun e => src e = p).card
  -- 推导：记下中间结论 `all`：`= sum_le_sum (s`。
  have all := sum_le_sum (s := univ) (fun p _ => each p)
  rw [sum_add_distrib, count_all selected src, sum_const, card_univ, Nat.nsmul_eq_mul,
    mul_comm (Fintype.card P)] at all
  exact all

omit [Fintype P] in
-- 读法：这里调用 `count_if`。
private theorem color_counts (p : P) (c : Color h) :
    min (∑ x, if thick c x then 0 else units src ix p x)
      (∑ x, if thick c x then units src ix p x else 0) =
    min (univ.filter fun e => src e = p ∧ ¬thick c (ix e)).card
      (univ.filter fun e => src e = p ∧ thick c (ix e)).card := by
  apply congrArg₂ min
  · simpa only [ite_not, units, out, filter_filter] using
      count_if (out src p) ix (fun x => ¬thick c x)
  · simpa only [units, out, filter_filter] using count_if (out src p) ix (thick c)

-- 读法：存在 `m : Matching src dst ix`，`good m` 与 `u * Fintype.card E * (3 / 8) ≤ u * m.count + B * (K + 1) * Fintype.card P` 同时成立。这里调用 `Nat.floor_le`。
/-- 匹配构造给出的任何性质在宽度估计中都得到保留。

英文原文：The width estimate preserves any property supplied by the matching construction.
-/
theorem subround_of_matching (u B : ℝ) (K : ℕ) (hu : 0 < u) (hB : 0 ≤ B)
    (hs : ∀ p x, u * (univ.filter fun e => src e = p ∧ ix e = x).card ≤ B)
    (good : Matching src dst ix → Prop)
    (make : ∀ (c : Color h) (b : ℕ),
      (∀ p x, (univ.filter fun e => src e = p ∧ ix e = x).card ≤ b) →
      ∃ m : Matching src dst ix, good m ∧
        (∑ p, min (univ.filter fun e => src e = p ∧ ¬thick c (ix e)).card
          (univ.filter fun e => src e = p ∧ thick c (ix e)).card) ≤
          m.count + b * K * Fintype.card P) :
    ∃ m : Matching src dst ix, good m ∧
      u * Fintype.card E * (3 / 8) ≤ u * m.count + B * (K + 1) * Fintype.card P := by
  let b := ⌊B / u⌋₊
  let w p x := u * (units src ix p x : ℝ)
  have hw p x : 0 ≤ w p x ∧ w p x ≤ B :=
    ⟨mul_nonneg hu.le (Nat.cast_nonneg _), by simpa [w, units, out, filter_filter] using hs p x⟩
  -- 推导：记下中间结论 `hb`：`u * b ≤ B`。
  have hb : u * b ≤ B := by
    rw [mul_comm, ← le_div_iff₀ hu]
    exact Nat.floor_le (div_nonneg hB hu.le)
  have hb' p x : units src ix p x ≤ b :=
    Nat.le_floor ((le_div_iff₀ hu).mpr (by simpa only [mul_comm, w] using (hw p x).2))
  have htotal : (∑ p, ∑ x, w p x) = u * Fintype.card E := by
    have h p : ∑ x, units src ix p x = (out src p).card := count_all _ _
    simp only [w, ← mul_sum, ← Nat.cast_sum, h, out]
    exact congrArg (fun n : ℕ => u * (n : ℝ)) (count_all univ src)
  obtain ⟨c, hc⟩ := coloring w B hw
  -- 推导：从 `make c b (by simpa only [units, out, filter_filter] using hb')` 中取出 `m, hg, hm`。
  obtain ⟨m, hg, hm⟩ := make c b (by simpa only [units, out, filter_filter] using hb')
  simp_rw [← color_counts] at hm
  let err p := ∑ x, if thick c x then w p x else -w p x
  let left p := ∑ x, if thick c x then 0 else units src ix p x
  let right p := ∑ x, if thick c x then units src ix p x else 0
  have he p : ∑ x, w p x ≤ 2 * u * (min (left p) (right p) : ℕ) + |err p| := by
    have hh p : (∑ x, w p x) + err p = 2 * u * right p := by
      simp only [err, right, Nat.cast_sum, ← sum_add_distrib, mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases h : thick c x <;> simp [w, h]
      ring
    have hl p : (∑ x, w p x) - err p = 2 * u * left p := by
      simp only [err, left, Nat.cast_sum, ← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases h : thick c x <;> simp [w, h]
      ring
    rcases le_total (left p) (right p) with h | h
    · rw [min_eq_left h, ← hl]
      linarith only [le_abs_self (err p)]
    · rw [min_eq_right h, ← hh]
      linarith only [neg_le_abs (err p)]
  -- 推导：记下中间结论 `he'`：`= sum_le_sum (s`。
  have he' := sum_le_sum (s := univ) fun p _ => he p
  rw [htotal, sum_add_distrib, ← mul_sum, ← Nat.cast_sum] at he'
  have hm' : ((∑ p, min (left p) (right p) : ℕ) : ℝ) ≤
      m.count + (b : ℝ) * K * Fintype.card P := by exact_mod_cast hm
  have h' : (∑ p, |err p|) ≤ u * Fintype.card E / 4 + B * Fintype.card P := by
    rw [htotal] at hc
    change (∑ p, |err p|) ^ 2 ≤ _ at hc
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [hc, sq_nonneg (u * Fintype.card E / 4 - B * Fintype.card P)]
  refine ⟨m, hg, ?_⟩
  linarith only [he', h', mul_le_mul_of_nonneg_left hm' hu.le,
    mul_le_mul_of_nonneg_right hb (show 0 ≤ (K : ℝ) * Fintype.card P by positivity),
    show 0 ≤ B * Fintype.card P by positivity]

-- 读法：存在 `m : Matching src dst ix`，`u * Fintype.card E * (3 / 8)` 不超过 `u * m.count + B * (K + 1) * Fintype.card P`。
/-- 利用杨氏不等式吸收不平衡项后得到的宽度界。这里 `E` 为各连线束的索引集，各束具有相同的正宽度 `u`。

英文原文：Width bound with the imbalance absorbed by Young's inequality.
Here `E` indexes bundles of common positive width `u`.
-/
theorem subround (u B : ℝ) (K : ℕ) (hu : 0 < u) (hB : 0 ≤ B)
    (hs : ∀ p x, u * (univ.filter fun e => src e = p ∧ ix e = x).card ≤ B)
    (hd : ∀ p, ((univ.filter fun e => src e = p).image dst).card ≤ K) :
    ∃ m : Matching src dst ix,
      u * Fintype.card E * (3 / 8) ≤ u * m.count + B * (K + 1) * Fintype.card P := by
  obtain ⟨m, _, hm⟩ := subround_of_matching src dst ix u B K hu hB hs (fun _ => True) (by
    intro c b hb
    obtain ⟨m, hm⟩ := match_color src dst ix b K c (by simpa only [units, out, filter_filter] using hb) hd
    simp_rw [color_counts] at hm
    exact ⟨m, trivial, hm⟩)
  exact ⟨m, hm⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 各二进组的共同宿主

**英文原文**

Common host for dyadic groups
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

-- 读法：在后续公式中，`Site` 是 `V × (Σ d : Fin (h + 1), Cell d.val)` 的缩写。
abbrev Site (V : Type) (h : ℕ) := V × (Σ d : Fin (h + 1), Cell d.val)

variable {V : Type} {h : ℕ}

namespace Site

-- 读法：`depth` 的取值由 `p.2.1.val` 给出。
def depth (p : Site V h) := p.2.1.val

-- 读法：`p.depth` 不超过 `h`。使用 `Nat.lt_succ_iff.mp` 给出的结论。
theorem depth_le (p : Site V h) : p.depth ≤ h := Nat.lt_succ_iff.mp p.2.1.isLt

-- 读法：`contains` 表示以下条件：`ancestor p.depth_le x` 等于 `p.2.2`。
def contains (p : Site V h) (x : Cell h) : Prop := ancestor p.depth_le x = p.2.2

end Site

variable [Fintype V]

-- 读法：`near` 的结果类型为 `Finset (Site V h)`。
/-- 宿主上的接触只取决于原有邻接关系与深度上限，与所选的组、匹配以及收缩布局无关。

英文原文：Host contacts depend only on the original adjacency and depth limit,
independently of the chosen group, matching and contraction layout.
-/
def near (N : V → Finset V) (D : ℕ) (p : Site V h) : Finset (Site V h) :=
  insert p (univ.filter fun q =>
    q.1 ∈ N p.1 ∧ (∃ x, p.contains x ∧ q.contains x) ∧
    p.depth ≤ q.depth + 64 * Nat.clog 2 (2 * D) ∧
    q.depth ≤ p.depth + 64 * Nat.clog 2 (2 * D))

-- 读法：结论为 `q ∈ near N D p ↔ q = p ∨ q.1 ∈ N p.1 ∧ (∃ x, p.contains x ∧ q.contains x) ∧ p.depth ≤ q.depth + 64 * Nat.clog 2 (2 * D) ∧ q.depth ≤ p.depth + 64 * Nat.clog 2 (2 * D)`。
theorem mem_near (N : V → Finset V) (D : ℕ) (p q : Site V h) :
    q ∈ near N D p ↔ q = p ∨
    q.1 ∈ N p.1 ∧ (∃ x, p.contains x ∧ q.contains x) ∧
    p.depth ≤ q.depth + 64 * Nat.clog 2 (2 * D) ∧
    q.depth ≤ p.depth + 64 * Nat.clog 2 (2 * D) := by simp [near]

-- 读法：`p` 属于 `near N D p`。使用 `mem_near` 给出的结论。
@[simp] theorem near_self (N : V → Finset V) (D : ℕ) (p : Site V h) :
    p ∈ near N D p := (mem_near _ _ _ _).mpr (.inl rfl)

-- 读法：`p` 属于 `near N D q`。
theorem near_symm {N : V → Finset V} (sym : ∀ v u, u ∈ N v → v ∈ N u)
    (D : ℕ) (p q : Site V h) (hq : q ∈ near N D p) : p ∈ near N D q := by
  rw [mem_near] at hq ⊢
  rcases hq with rfl | ⟨hn, ⟨x, hp, hq⟩, h₁, h₂⟩
  · exact .inl rfl
  · exact .inr ⟨sym _ _ hn, ⟨x, hq, hp⟩, h₂, h₁⟩

-- 读法：`near C Δ p` 包含于 `near N D p`。
theorem near_mono {C N : V → Finset V} (sub : ∀ v, C v ⊆ N v)
    {Δ D : ℕ} (hle : Δ ≤ D) (p : Site V h) : near C Δ p ⊆ near N D p := by
  intro q hq
  rw [mem_near] at hq ⊢
  rcases hq with rfl | ⟨hn, hp, h₁, h₂⟩
  · exact .inl rfl
  · have hm := Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 hle)
    exact .inr ⟨sub _ hn, hp, by omega, by omega⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 共同二进宿主的大小与度数

若一个区间与固定站点的区间重叠，且两者深度之差不超过 `s`，则其深度与至多 `s` 个附加前缀比特即可确定这个区间。

**英文原文**

Size and degree of the common dyadic host

An overlapping interval at depth within `s` of a fixed site is determined
by its depth and at most `s` additional prefix bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

-- 读法：`Fintype.card (Site V h)` 不超过 `2 * 2 ^ h * Fintype.card V`。对 `n` 作归纳。
theorem Site.card (V : Type) [Fintype V] (h : ℕ) :
    Fintype.card (Site V h) ≤ 2 * 2 ^ h * Fintype.card V := by
  have H (n : ℕ) : (∑ i : Fin n, 2 ^ i.val) < 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc, pow_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
  rw [Fintype.card_prod, Fintype.card_sigma, mul_comm (Fintype.card V)]
  simp_rw [card_cell]
  apply Nat.mul_le_mul_right
  simpa only [pow_succ'] using (H (h + 1)).le

variable {V : Type} [Fintype V] {h : ℕ}

-- 读法：结论为 `let s := 64 * Nat.clog 2 (2 * D) (near N D p).card ≤ ((N p.1).card + 1) * ((2 * s + 1) * 2 ^ s)`。
private theorem near_card_raw (N : V → Finset V) (D : ℕ) (p : Site V h) :
    let s := 64 * Nat.clog 2 (2 * D)
    (near N D p).card ≤ ((N p.1).card + 1) * ((2 * s + 1) * 2 ^ s) := by
  intro s
  have facts (q : Site V h) (hq : q ∈ near N D p) :
      q.1 ∈ insert p.1 (N p.1) ∧ p.depth ≤ q.depth + s ∧ q.depth ≤ p.depth + s ∧
      ∀ (i : Fin q.depth) (hi : i.val < p.depth), q.2.2 i = p.2.2 ⟨i.val, hi⟩ := by
    rcases (mem_near N D p q).mp hq with rfl | ⟨hn, ⟨x, hp, hq⟩, h₁, h₂⟩
    · exact ⟨mem_insert_self _ _, by omega, by omega, fun _ _ => rfl⟩
    · exact ⟨mem_insert_of_mem hn, h₁, h₂, fun i hi =>
        (congrFun hq i).symm.trans (congrFun hp ⟨i.val, hi⟩)⟩
  let extra (q : Site V h) : Cell s := fun i =>
    if hi : p.depth + i.val < q.depth then q.2.2 ⟨p.depth + i.val, hi⟩ else 0
  let code (q : near N D p) : ↥(insert p.1 (N p.1)) × Fin (2 * s + 1) × Cell s :=
    (⟨q.val.1, (facts _ q.property).1⟩, ⟨q.val.depth + s - p.depth, by
      have := (facts _ q.property).2.2.1
      omega⟩, extra q.val)
  have inj : Function.Injective code := by
    rintro ⟨⟨v, d, a⟩, ha⟩ ⟨⟨w, e, b⟩, hb⟩ he
    -- 推导：记下中间结论 `hv`：`v = w`。
    have hv : v = w := congrArg (fun z => z.1.val) he
    subst w
    obtain ⟨_, ha₁, ha₂, ha₃⟩ := facts _ ha
    obtain ⟨_, hb₁, _, hb₃⟩ := facts _ hb
    change p.depth ≤ d.val + s at ha₁
    change p.depth ≤ e.val + s at hb₁
    change d.val ≤ p.depth + s at ha₂
    have hval : d.val + s - p.depth = e.val + s - p.depth :=
      congrArg (fun z => z.2.1.val) he
    have heq : d = e := Fin.ext (by omega)
    subst e
    -- 推导：记下中间结论 `hx`：`extra (v, ⟨d, a⟩) = extra (v, ⟨d, b⟩)`。
    have hx : extra (v, ⟨d, a⟩) = extra (v, ⟨d, b⟩) := congrArg (fun z => z.2.2) he
    have hab : a = b := by
      funext i
      by_cases hi : i.val < p.depth
      · exact (ha₃ i hi).trans (hb₃ i hi).symm
      · have hj : p.depth + (i.val - p.depth) = i.val := by omega
        have hz := congrFun hx ⟨i.val - p.depth, by omega⟩
        unfold Site.depth at hj
        simpa [extra, Site.depth, hj, i.isLt] using hz
    subst b
    rfl
  have H := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, card_cell] at H
  exact H.trans (Nat.mul_le_mul_right _ (card_insert_le _ _))

-- 读法：`(near N D p).card` 不超过 `(4 * D) ^ 300`。
theorem near_card (N : V → Finset V) (D : ℕ) (hD : 0 < D)
    (deg : ∀ v, (N v).card ≤ D) (p : Site V h) :
    (near N D p).card ≤ (4 * D) ^ 300 := by
  let n := Nat.clog 2 (2 * D)
  let s := 64 * n
  have hn : 1 ≤ n := Nat.clog_pos (by decide) (by omega)
  have hpred : 2 ^ (n - 1) < 2 * D := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have hpow : 2 ^ n ≤ 4 * D := by
    rw [← Nat.sub_add_cancel hn, pow_succ]
    omega
  -- 推导：记下中间结论 `hextra`：`2 ^ s ≤ (4 * D) ^ 64`。
  have hextra : 2 ^ s ≤ (4 * D) ^ 64 := by
    rw [show s = n * 64 by exact Nat.mul_comm _ _, pow_mul]
    exact Nat.pow_le_pow_left hpow _
  have hdepth : 2 * s + 1 ≤ (4 * D) ^ 128 := calc
    _ ≤ 2 ^ (2 * s) := Nat.lt_pow_self (by decide)
    _ = (2 ^ s) ^ 2 := by rw [Nat.mul_comm 2 s, pow_mul]
    _ ≤ ((4 * D) ^ 64) ^ 2 := Nat.pow_le_pow_left hextra _
    _ = _ := by rw [← pow_mul]
  have hbase : (N p.1).card + 1 ≤ 4 * D := by have := deg p.1; omega
  calc
    _ ≤ ((N p.1).card + 1) * ((2 * s + 1) * 2 ^ s) := near_card_raw N D p
    _ ≤ 4 * D * ((4 * D) ^ 128 * (4 * D) ^ 64) := Nat.mul_le_mul hbase (Nat.mul_le_mul hdepth hextra)
    _ = (4 * D) ^ 193 := by rw [← pow_add, ← pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# 组内的相对地址

丢弃共同前缀与取接触端点这两个操作可交换。用相对地址及任一绝对端点即可恢复完整地址。

**英文原文**

Relative addresses inside a group

Forgetting a common prefix commutes with taking the endpoint of a contact.
The relative address and either absolute endpoint recover the whole address.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

variable {h : ℕ} {V A : Type}

-- 读法：`suffix` 的结果类型为 `Cell (h - a)`。
def suffix (a : ℕ) (x : Cell h) : Cell (h - a) :=
  fun i => x ⟨a + i, by have := i.isLt; omega⟩

-- 读法：`Site.drop` 的结果类型为 `Site V (h - a)`。
def Site.drop (a : ℕ) (p : Site V h) : Site V (h - a) :=
  (p.1, ⟨⟨p.depth - a, by have := p.depth_le; omega⟩, suffix a p.2.2⟩)

-- 读法：`relBase` 的取值由 `base v - a` 给出。
def relBase (a : ℕ) (base : V → ℕ) (v : V) := base v - a

-- 读法：`relBase a base v` 不超过 `h - a`。使用 `Nat.sub_le_sub_right` 给出的结论。
theorem relHi (a : ℕ) {base : V → ℕ} (hb : ∀ v, base v ≤ h) (v : V) :
    relBase a base v ≤ h - a := Nat.sub_le_sub_right (hb v) a

-- 读法：`contactDepth (relBase a base) ends c` 等于 `contactDepth base ends c - a`。
theorem relDepth (a : ℕ) (base : V → ℕ) (ends : A → Bool → V) (c : A) :
    contactDepth (relBase a base) ends c = contactDepth base ends c - a := by
  unfold contactDepth relBase
  omega

variable {base : V → ℕ} {ends : A → Bool → V}

-- 读法：`dropContact` 的取值由 `⟨z.1, fun i => suffix a z.2 (Fin.cast (relDepth a base ends z.1) i)⟩` 给出。
def dropContact (a : ℕ) (z : Σ c, Cell (contactDepth base ends c)) :
    Σ c, Cell (contactDepth (relBase a base) ends c) :=
  ⟨z.1, fun i => suffix a z.2 (Fin.cast (relDepth a base ends z.1) i)⟩

-- 读法：`x` 等于 `y`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem dropContact_inj (a : ℕ) (lo : ∀ v, a ≤ base v) (t : Bool)
    {x y : Σ c, Cell (contactDepth base ends c)}
    (hr : dropContact a x = dropContact a y)
    (he : contactEnd base ends x t = contactEnd base ends y t) : x = y := by
  rcases x with ⟨b, x⟩
  rcases y with ⟨c, y⟩
  have eq : b = c := congrArg Sigma.fst hr
  subst c
  have hs := eq_of_heq (Sigma.mk.inj hr).2
  have hp := eq_of_heq (Sigma.mk.inj he).2
  congr 1
  funext i
  by_cases hi : i.val < a
  · exact congrFun hp ⟨i, hi.trans_le (lo _)⟩
  · have hd : i.val - a < contactDepth (relBase a base) ends b := by rw [relDepth]; omega
    have ht := congrFun hs ⟨i.val - a, hd⟩
    simpa [suffix, Nat.add_sub_of_le (Nat.le_of_not_gt hi)] using ht

-- 读法：要证明的命题是 `(p.drop a).contains (suffix a x)`。
theorem Site.drop_contains {p : Site V h} {x : Cell h} (a : ℕ) (hx : p.contains x) :
    (p.drop a).contains (suffix a x) :=
  congrArg (suffix a) hx

-- 读法：`q.drop a` 属于 `near N D (p.drop a)`。
theorem drop_near [Fintype V] {N : V → Finset V} {D : ℕ} {p q : Site V h}
    (a : ℕ) (hp : q ∈ near N D p) : q.drop a ∈ near N D (p.drop a) := by
  rw [mem_near] at hp ⊢
  rcases hp with rfl | ⟨hn, ⟨x, hx, hy⟩, hp, hq⟩
  · exact .inl rfl
  · have hd (s : Site V h) : (s.drop a).depth = s.depth - a := rfl
    exact .inr ⟨hn, ⟨_, Site.drop_contains a hx, Site.drop_contains a hy⟩,
      by rw [hd, hd]; omega, by rw [hd, hd]; omega⟩

-- 读法：`p` 等于 `q`。
theorem Site.drop_injective {p q : Site V h} (a : ℕ) (hp : a ≤ p.depth) (hq : a ≤ q.depth)
    (e : ancestor hp p.2.2 = ancestor hq q.2.2) (hh : p.drop a = q.drop a) : p = q := by
  have hv : p.1 = q.1 := congrArg (fun z : Site V (h - a) => z.1) hh
  have hd : p.depth - a = q.depth - a := congrArg (fun z : Site V (h - a) => z.depth) hh
  have hd' : p.depth = q.depth := by omega
  obtain ⟨v, ⟨i, x⟩⟩ := p
  obtain ⟨w, ⟨j, y⟩⟩ := q
  have h₁ : v = w := hv
  have h₂ : i = j := Fin.ext hd'
  subst w j
  have hs : suffix a x = suffix a y := eq_of_heq (Sigma.mk.inj (congrArg Prod.snd hh)).2
  suffices x = y by subst y; rfl
  funext k
  by_cases hk : k.val < a
  · exact congrFun e ⟨k, hk⟩
  · have ht := congrFun hs ⟨k.val - a, by have := k.isLt; omega⟩
    simpa [suffix, Nat.add_sub_of_le (Nat.le_of_not_gt hk)] using ht

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 块的二进分组所用的数据与界

**英文原文**

Data and bounds for a dyadic grouping of blocks
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} [Fintype V] {h : ℕ}

-- 读法：`coreBins` 的取值由 `Δ * 2 ^ (64 * Nat.clog 2 (2 * Δ))` 给出。
/-- 每个群所能到达的核心目的地数量的上界。

英文原文：The bound on the number of core destinations per colony.
-/
def coreBins (Δ : ℕ) := Δ * 2 ^ (64 * Nat.clog 2 (2 * Δ))

-- 读法：结构的字段包括 `π`、`parts`、`label`、`total`、`mem`。
structure Grouping (N C : V → Finset V) (Δ D k : ℕ) (B : ℝ) (l : V → Cell h → ℝ) where
  π : Cell h ≃ₗ[ZMod 2] Cell h
  parts : V → Finset (Σ i, Cell i)
  label : V → Cell h → Σ i, Cell i
  total : (∑ v, ((parts v).card : ℝ)) ≤
    Fintype.card V + 16 * (∑ v, ∑ x, l v x) / ((2 : ℝ) ^ k * B)
  mem : ∀ v x, label v x ∈ parts v
  part : ∀ v c, c ∈ parts v →
    c.1 ≤ h - k ∧ (∃ hi : c.1 ≤ h, ∀ x, label v x = c ↔ ancestor hi (π x) = c.2) ∧
    2 ^ k ≤ (univ.filter fun x => label v x = c).card ∧
    (∑ x, if label v x = c then l v x else 0) ≤ (2 : ℝ) ^ k * B
  edge : ∀ v u, u ∈ N v → ∀ x, (label u x).1 ≤ (label v x).1 +
    64 * Nat.clog 2 (2 * if u ∈ C v then Δ else D)
  bins : ∀ v c, c ∈ parts v →
    (∑ u ∈ C v, ((univ.filter fun x => label v x = c).image (label u)).card) ≤ coreBins Δ

namespace Grouping
variable {N C : V → Finset V} {Δ D k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l)

-- 读法：在后续公式中，`Colony` 是 `Σ v, ↥(g.parts v)` 的缩写。
abbrev Colony := Σ v, ↥(g.parts v)

-- 读法：`loc` 的取值由 `⟨v, g.label v x, g.mem v x⟩` 给出。
def loc (v : V) (x : Cell h) : g.Colony := ⟨v, g.label v x, g.mem v x⟩

-- 读法：`ends` 的取值由 `g.loc (src e) (ix e)` 给出。
def ends {E : Type} (src : E → V) (ix : E → Cell h) (e : E) : g.Colony :=
  g.loc (src e) (ix e)

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 原有出现位置上的两种子轮收缩

行收缩将每个出现项送到自己的群。列收缩则恰好将已匹配的细源出现项移到粗目的地。一个出现项的全部出发单位有共同的目的地。

**英文原文**

The two subround contractions on old occurrences

Row contraction sends each occurrence to its own colony. Column contraction
moves precisely the matched thin source occurrences to the thick destination.
A whole occurrence has the same destination for all its outgoing units.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {E P V : Type} [Fintype V] {h : ℕ}

-- 读法：在后续公式中，`Matching.items` 是 `{e // (m.plan (src e) (ix e)).isSome}` 的缩写。
abbrev Matching.items {src dst : E → P} {ix : E → Cell h} (m : Matching src dst ix) :=
  {e // (m.plan (src e) (ix e)).isSome}

namespace Grouping

variable {N C : V → Finset V} {Δ D k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l)

-- 读法：`site` 的结果类型为 `Site V h`。
def site (p : g.Colony) : Site V h :=
  (p.1, ⟨⟨p.2.val.1, by have := (g.part p.1 p.2.val p.2.property).1; omega⟩, p.2.val.2⟩)

-- 读法：`g.site` 是单射。
theorem site_injective : Function.Injective g.site := by
  rintro ⟨v, p⟩ ⟨w, q⟩ he
  have : v = w := congrArg Prod.fst he
  subst w
  have : p.val = q.val := congrArg
    (fun z : Site V h => (⟨z.2.1.val, z.2.2⟩ : Σ i, Cell i)) he
  rw [Subtype.ext this]

-- 读法：`here` 的取值由 `g.site (g.loc v x)` 给出。
def here (v : V) (x : Cell h) := g.site (g.loc v x)

-- 读法：要证明的命题是 `(g.here v x).contains (g.π x)`。
theorem here_contains (v : V) (x : Cell h) : (g.here v x).contains (g.π x) := by
  obtain ⟨_, he⟩ := (g.part _ _ (g.mem v x)).2.1
  exact (he x).mp rfl

-- 读法：`g.here w x` 属于 `near C Δ (g.here v x)`。这里调用 `g.edge`。
theorem here_core (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    {v w : V} (hw : w ∈ C v) (x : Cell h) : g.here w x ∈ near C Δ (g.here v x) := by
  have hv := cs _ _ hw
  refine (mem_near _ _ _ _).mpr (.inr ⟨hw, ⟨_, g.here_contains v x, g.here_contains w x⟩,
    ?_, ?_⟩)
  · simpa only [ite_eq_left hv, here, site, loc, Site.depth] using g.edge w v (sub w hv) x
  · simpa only [ite_eq_left hw, here, site, loc, Site.depth] using g.edge v w (sub v hw) x

-- 读法：`g.here w x` 属于 `near N D (g.here v x)`。这里调用 `Nat.clog_mono_right`。
theorem here_full (ns : ∀ v w, w ∈ N v → v ∈ N w) (le : Δ ≤ D)
    {v w : V} (hw : w ∈ N v) (x : Cell h) : g.here w x ∈ near N D (g.here v x) := by
  have edge (v w : V) (hw : w ∈ N v) :
      (g.here w x).depth ≤ (g.here v x).depth + 64 * Nat.clog 2 (2 * D) := by
    refine (g.edge v w hw x).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
    apply Nat.clog_mono_right
    split_ifs <;> omega
  exact (mem_near _ _ _ _).mpr (.inr ⟨hw, ⟨_, g.here_contains v x, g.here_contains w x⟩,
    edge _ _ (ns _ _ hw), edge _ _ hw⟩)

variable {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

-- 读法：当 `col` 成立时取 `g.site ((m.plan (g.loc v x) x).getD (g.loc v x))`，否则取 `g.here v x`。
def route (col : Bool) (v : V) (x : Cell h) : Site V h :=
  if col then g.site ((m.plan (g.loc v x) x).getD (g.loc v x)) else g.here v x

-- 读法：`g.route m col v x` 等于 `g.here v x`。
theorem route_thick (col : Bool) (v : V) (x : Cell h) (hx : thick m.color x) :
    g.route m col v x = g.here v x := by
  cases hp : m.plan (g.loc v x) x with
  | none => simp [route, hp, here]
  | some _ => exact (m.thin (g.loc v x) x (by simp [hp]) hx).elim

-- 读法：`g.route m col (src e.val) (ix e.val)` 等于 `if col then g.here (dst (m.mate e)) (ix (m.mate e)) else g.here (src (m.mate e)) (ix (m.mate e))`。对 `col` 分类讨论。
theorem route_thin (col : Bool) (e : m.items) :
    g.route m col (src e.val) (ix e.val) =
      if col then g.here (dst (m.mate e)) (ix (m.mate e))
        else g.here (src (m.mate e)) (ix (m.mate e)) := by
  obtain ⟨_, hs, ht⟩ := m.spec e
  cases col
  · exact congrArg g.site hs.symm
  · change g.site ((m.plan (g.ends src ix e.val) (ix e.val)).getD _) = _
    rw [ht]
    rfl

-- 读法：对 `col` 分类讨论。
/-- 只有核心单位的源点可以移动，而且移动至多跨越一条核心边。

英文原文：Only a source of core units can move, and it moves by at most one core hop.
-/
theorem route_cases (col : Bool) (v : V) (x : Cell h) :
    g.route m col v x = g.here v x ∨
      ∃ e : m.items, src e.val = v ∧ ix e.val = x ∧
        g.here (src (m.mate e)) (ix (m.mate e)) = g.here v x ∧
        g.route m col v x = g.here (dst (m.mate e)) (ix (m.mate e)) := by
  cases col
  · exact .inl rfl
  cases hp : m.plan (g.loc v x) x with
  | none => exact .inl (by simp [route, hp, here])
  | some p =>
    have hh : (m.plan (g.loc v x) x).isSome := by simp [hp]
    obtain ⟨e, he, hi⟩ := m.used _ _ hh
    have hs : src e = v := congrArg Sigma.fst he
    let i : m.items := ⟨e, by rw [he, hi]; exact hh⟩
    exact .inr ⟨i, hs, hi, congrArg g.site ((m.spec i).2.1.trans he),
      by simpa [i, hs, hi] using g.route_thin m true i⟩

-- 读法：`g.route m col v x` 属于 `near C Δ (g.here v x)`。
theorem route_near (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (col : Bool) (v : V) (x : Cell h) :
    g.route m col v x ∈ near C Δ (g.here v x) := by
  rcases g.route_cases m col v x with he | ⟨e, _, _, hs, ht⟩
  · rw [he]; exact near_self _ _ _
  · rw [ht, ← hs]; exact g.here_core cs sub (hedge _) _

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 行收缩或列收缩后站点的负载

**英文原文**

Load of a site after row or column contraction
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Grouping
open Finset
open scoped Classical

variable {E V : Type} [Fintype V] {h : ℕ}
  {N C : V → Finset V} {Δ D k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l)

-- 读法：`(∑ t : V × Cell h, if g.here t.1 t.2 = z then l t.1 t.2 else 0)` 不超过 `(2 : ℝ) ^ k * B`。按 `∃ p, g.site p = z` 成立与否分情况。
theorem here_load (hB : 0 ≤ B) (z : Site V h) :
    (∑ t : V × Cell h, if g.here t.1 t.2 = z then l t.1 t.2 else 0) ≤ (2 : ℝ) ^ k * B := by
  by_cases hz : ∃ p, g.site p = z
  · obtain ⟨⟨v, c, hc⟩, rfl⟩ := hz
    rw [Fintype.sum_prod_type, Fintype.sum_eq_single v]
    · have eq (x : Cell h) : g.here v x = g.site ⟨v, c, hc⟩ ↔ g.label v x = c := by
        simp [here, g.site_injective.eq_iff, loc]
      simp_rw [eq]
      exact (g.part v c hc).2.2.2
    · intro w hw
      apply sum_eq_zero
      intro x _
      exact ite_eq_right (fun he => hw (congrArg Prod.fst he))
  · have hn (t : V × Cell h) : g.here t.1 t.2 ≠ z := fun he => hz ⟨g.loc _ _, he⟩
    simp_rw [ite_eq_right (hn _), sum_const_zero]
    exact mul_nonneg (by positivity) hB

variable {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

-- 读法：`(∑ t : V × Cell h, if g.route m col t.1 t.2 = z then l t.1 t.2 else 0)` 不超过 `(near C Δ z).card * ((2 : ℝ) ^ k * B)`。这里调用 `sum_le_sum`。
/-- 附近每个群贡献的负载至多为一个完整群的负载。

英文原文：Each nearby colony contributes at most one full colony load.
-/
theorem route_load (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (hl : ∀ v x, 0 ≤ l v x) (hB : 0 ≤ B)
    (col : Bool) (z : Site V h) :
    (∑ t : V × Cell h, if g.route m col t.1 t.2 = z then l t.1 t.2 else 0) ≤
      (near C Δ z).card * ((2 : ℝ) ^ k * B) := by
  calc
    _ ≤ ∑ t : V × Cell h, ∑ a ∈ near C Δ z, if g.here t.1 t.2 = a then l t.1 t.2 else 0 := by
      apply sum_le_sum
      intro t _
      rw [sum_ite_eq]
      by_cases he : g.route m col t.1 t.2 = z
      · have hn := near_symm cs Δ _ _ (g.route_near m cs sub hedge col t.1 t.2)
        rw [he] at hn
        rw [ite_eq_left he, ite_eq_left hn]
      · rw [ite_eq_right he]
        split_ifs
        · exact hl _ _
        · exact le_rfl
    _ ≤ ∑ _a ∈ near C Δ z, (2 : ℝ) ^ k * B := by
      rw [sum_comm]
      exact sum_le_sum fun a _ => g.here_load hB a
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end OAI.LinearAlgebra.MatrixExponent.Packing.Grouping
end
