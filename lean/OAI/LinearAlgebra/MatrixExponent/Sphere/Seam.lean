-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Real.Sqrt

section
/-!
# 配对和的缩放、限制与系数变换

**英文原文**

Scaling, restriction and change of coefficients for pairing sums
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α R S : Type*} [CommRing R] [CommRing S]

-- 读法：`contract (fun x => c * f x * g x) (fun t => (t.map f).prod * P t) xs` 等于 `c * (xs.map f).prod * contract g P xs`。对 `xs` 作归纳，并把 `P` 保持为任意参数。
private theorem contract_scale_rows (c : R) (f g : α → R) (P : List α → R) (xs : List α) :
    contract (fun x => c * f x * g x) (fun t => (t.map f).prod * P t) xs =
      c * (xs.map f).prod * contract g P xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih =>
    simp only [contract_cons, List.map_cons, List.prod_cons]
    simp only [mul_assoc (f x)]
    rw [contract_scale, ih (fun t => P (x :: t))]
    ring

-- 读法：`wick (fun x y => f x * f y * k x y) xs` 等于 `(xs.map f).prod * wick k xs`。对 `xs` 分类讨论。
/-- 每个生成元在每个 Wick 单项式中恰好出现一次。

英文原文：Every generator occurs exactly once in each Wick monomial.
-/
theorem wick_scale_rows (k : α → α → R) (f : α → R) (xs : List α) :
    wick (fun x y => f x * f y * k x y) xs = (xs.map f).prod * wick k xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.length_cons] at hn
      rw [wick_cons, wick_cons, List.map_cons, List.prod_cons, ← contract_scale_rows]
      apply contract_congr
      intro ys hy
      exact ih ys.length (by omega) ys rfl

-- 读法：`contract f P xs` 等于 `contract g P xs`。对 `xs` 作归纳，并把 `P` 保持为任意参数。
private theorem contract_eq_on (f g : α → R) (P : List α → R) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : contract f P xs = contract g P xs := by
  induction xs generalizing P with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forall_mem_cons] at h
    rw [contract_cons, contract_cons, h.1, ih _ h.2]

-- 读法：`wick k xs` 等于 `wick l xs`。对 `xs` 分类讨论。
theorem wick_eq_on (k l : α → α → R) (xs : List α)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, k x y = l x y) : wick k xs = wick l xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      have head (z : α) (hz : z ∈ xs) : k x z = l x z := h x (by simp) z (by simp [hz])
      rw [wick_cons, wick_cons, contract_eq_on _ _ _ _ head]
      apply contract_sublist_congr
      intro ys hy he
      apply ih ys.length (by omega) ys _ rfl
      intro y h₁ z h₂
      exact h y (List.mem_cons_of_mem _ (hy.subset h₁)) z (List.mem_cons_of_mem _ (hy.subset h₂))

-- 读法：`f (contract g P xs)` 等于 `contract (fun x => f (g x)) (fun t => f (P t)) xs`。对 `xs` 作归纳，并把 `P` 保持为任意参数。
private theorem contract_hom (f : R →+* S) (g : α → R) (P : List α → R) (xs : List α) :
    f (contract g P xs) = contract (fun x => f (g x)) (fun t => f (P t)) xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih => rw [contract_cons, contract_cons, map_sub, map_mul, ih]

-- 读法：`f (wick k xs)` 等于 `wick (fun x y => f (k x y)) xs`。对 `xs` 分类讨论。
theorem wick_hom (f : R →+* S) (k : α → α → R) (xs : List α) :
    f (wick k xs) = wick (fun x y => f (k x y)) xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.length_cons] at hn
      rw [wick_cons, wick_cons, contract_hom]
      apply contract_congr
      intro ys hy
      exact ih ys.length (by omega) ys rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# 能量有界的态数

将能量加倍后，互不相同的模式构成一个矩形内的有限子集。估计其幂集的生成函数即可，无须引入无穷乘积。

**英文原文**

Number of states at bounded energy

Energy is doubled. Distinct modes give a finite subset of a rectangle.
Bounding the generating function of its powerset avoids infinite products.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset Real

-- 读法：在后续公式中，`LevelLE` 是 `{w : Wedge r // energy w.val ≤ e}` 的缩写。
abbrev LevelLE (r e : ℕ) := {w : Wedge r // energy w.val ≤ e}

variable {r e : ℕ}

-- 读法：`modes` 的取值由 `univ ×ˢ range e` 给出。
private def modes (r e : ℕ) : Finset (Mode r) := univ ×ˢ range e

-- 读法：`used` 的取值由 `w.val.val.toFinset` 给出。
private def used (w : LevelLE r e) := w.val.val.toFinset

-- 读法：`used w` 属于 `(modes r e).powerset`。
private theorem used_mem (w : LevelLE r e) : used w ∈ (modes r e).powerset := by
  rw [mem_powerset]
  intro i hi
  have h : 2 * i.2 + 1 ≤ energy w.val.val :=
    List.le_sum_of_mem (List.mem_map_of_mem (List.mem_toFinset.mp hi))
  have := w.property
  simp only [modes, mem_product, mem_univ, true_and, mem_range]
  omega

-- 读法：`(fun w : Wedge r => w.val.toFinset)` 是单射。按 `Subtype.ext` 的外延性准则比较各分量。
theorem Wedge.toFinset_injective : Function.Injective (fun w : Wedge r => w.val.toFinset) := by
  intro x y h
  apply Subtype.ext
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (asymm h₁ h₂).elim) x.property y.property
  apply (List.perm_ext_iff_of_nodup x.nodup y.nodup).mpr
  intro i
  exact List.mem_toFinset.symm.trans ((congrArg (i ∈ ·) h).to_iff.trans List.mem_toFinset)

-- 读法：`(used (r := r) (e := e))` 是单射。
private theorem used_inj : Function.Injective (used (r := r) (e := e)) :=
  fun _ _ h => Subtype.ext (Wedge.toFinset_injective h)

-- 读法：为 `Fintype (LevelLE r e)` 构造类型类实例。
noncomputable instance (r e : ℕ) : Fintype (LevelLE r e) :=
  Fintype.ofInjective (fun w => (⟨used w, used_mem w⟩ : ↥(modes r e).powerset))
    (fun _ _ h => used_inj (congrArg Subtype.val h))

-- 读法：`weightFromDimension` 的取值由 `exp (-t * (2 * j + 1))` 给出。
private noncomputable def weightFromDimension (t : ℝ) (j : ℕ) := exp (-t * (2 * j + 1))

-- 读法：结论为 `∏ i ∈ used w, weightFromDimension t i.2 = exp (-t * energy w.val.val)`。
private theorem weight_prod (t : ℝ) (w : LevelLE r e) :
    ∏ i ∈ used w, weightFromDimension t i.2 = exp (-t * energy w.val.val) := by
  unfold weightFromDimension
  rw [← exp_sum, ← mul_sum]
  have he := List.sum_toFinset (fun i : Mode r => 2 * i.2 + 1) w.val.nodup
  change ∑ i ∈ used w, (2 * i.2 + 1) = energy w.val.val at he
  rw [← he]
  push_cast
  rfl

-- 读法：`Fintype.card (LevelLE r e) * exp (-t * e)` 不超过 `∏ i ∈ modes r e, (1 + weightFromDimension t i.2)`。这里调用 `sum_le_sum`。
private theorem partition_bound (r e : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Fintype.card (LevelLE r e) * exp (-t * e) ≤
      ∏ i ∈ modes r e, (1 + weightFromDimension t i.2) := by
  classical
  let g (a : Finset (Mode r)) := ∏ i ∈ a, weightFromDimension t i.2
  calc
    _ = ∑ _w : LevelLE r e, exp (-t * e) := by simp
    _ ≤ ∑ w : LevelLE r e, g (used w) := by
      apply sum_le_sum
      intro w _
      rw [show g (used w) = _ from weight_prod t w]
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr w.property) (neg_nonpos.mpr ht))
    _ = ∑ a ∈ (univ : Finset (LevelLE r e)).image used, g a :=
      (sum_image used_inj.injOn).symm
    _ ≤ ∑ a ∈ (modes r e).powerset, g a := by
      apply sum_le_sum_of_subset_of_nonneg
      · rintro _ ha
        obtain ⟨w, _, rfl⟩ := mem_image.mp ha
        exact used_mem w
      · intro a _ _
        exact prod_nonneg (fun _ _ => exp_nonneg _)
    _ = _ := (prod_one_add _).symm

-- 读法：结论为 `∑ j ∈ range e, weightFromDimension t j ≤ 1 / t`。这里调用 `le_div_iff₀`。
/-- 单个物种的指数权重可用望远镜求和估计。

英文原文：The exponential weights for one species are bounded by a telescoping sum.
-/
private theorem sum_weight (e : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ j ∈ range e, weightFromDimension t j ≤ 1 / t := by
  apply (le_div_iff₀ ht).mpr
  rw [sum_mul]
  let f (j : ℕ) := exp (-t * j)
  calc
    _ ≤ ∑ j ∈ range e, (f j - f (j + 1)) := by
      apply sum_le_sum
      intro j _
      have h₁ : weightFromDimension t j ≤ f (j + 1) := by
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr ht.le)
        push_cast
        linarith
      -- 推导：记下中间结论 `h₂`：`f (j + 1) * exp t = f j`。
      have h₂ : f (j + 1) * exp t = f j := by
        unfold f
        rw [← exp_add]
        congr 1
        push_cast
        ring
      calc
        _ ≤ f (j + 1) * t := mul_le_mul_of_nonneg_right h₁ ht.le
        _ ≤ f (j + 1) * (exp t - 1) :=
          mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mpr (add_one_le_exp t)) (exp_nonneg _)
        _ = _ := by rw [mul_sub, h₂, mul_one]
    _ = f 0 - f e := sum_range_sub' _ _
    _ ≤ 1 := by simp [f, exp_nonneg]

-- 读法：`Fintype.card (LevelLE r e)` 不超过 `exp (r / t + t * e)`。这里调用 `prod_le_prod₀`。
private theorem card_bound (r e : ℕ) {t : ℝ} (ht : 0 < t) :
    Fintype.card (LevelLE r e) ≤ exp (r / t + t * e) := by
  rw [exp_add, ← div_le_iff₀ (exp_pos _), div_eq_mul_inv, ← exp_neg, ← neg_mul]
  calc
    _ ≤ ∏ i ∈ modes r e, (1 + weightFromDimension t i.2) := partition_bound r e ht.le
    _ ≤ exp (∑ i ∈ modes r e, weightFromDimension t i.2) := by
      rw [exp_sum]
      apply prod_le_prod₀
      · intro i _; unfold weightFromDimension; positivity
      · intro i _; rw [add_comm]; exact add_one_le_exp _
    _ ≤ _ := by
      apply exp_le_exp.mpr
      rw [modes, sum_product]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left (sum_weight e ht) (Nat.cast_nonneg (α := ℝ) r)

-- 读法：`Fintype.card (LevelLE r e)` 不超过 `exp (2 * sqrt ((r : ℝ) * e))`。这里调用 `partition_bound`。
/-- 对倍能量不超过 `e` 的各能级取直和，其维数有统一上界。

英文原文：A uniform dimension bound for the direct sum through doubled energy `e`.
-/
theorem card_levelLE (r e : ℕ) :
    Fintype.card (LevelLE r e) ≤ exp (2 * sqrt ((r : ℝ) * e)) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa [modes] using partition_bound 0 e (le_refl 0)
  rcases eq_or_ne e 0 with rfl | he
  · simpa [modes] using partition_bound r 0 (le_refl 0)
  let z := sqrt ((r : ℝ) * e)
  have hz : 0 < z := by unfold z; positivity
  have he' : (0 : ℝ) < e := by positivity
  have hsq : z ^ 2 = (r : ℝ) * e := sq_sqrt (by positivity)
  have h : (r : ℝ) / (z / e) = z := by
    rw [div_div_eq_mul_div, ← hsq, pow_two, mul_div_cancel_right₀ _ hz.ne']
  simpa only [h, div_mul_cancel₀ _ he'.ne', ← two_mul] using
    card_bound r e (div_pos hz he')

-- 读法：在后续公式中，`Level` 是 `{w : Wedge r // energy w.val = e}` 的缩写。
abbrev Level (r e : ℕ) := {w : Wedge r // energy w.val = e}

-- 读法：`Level.include` 的取值由 `⟨fun w => ⟨w.val, w.property.le⟩, fun _ _ h => Subtype.ext (congrArg (fun x : LevelLE r e => x.val) h)⟩` 给出。
def Level.include (r e : ℕ) : Level r e ↪ LevelLE r e :=
  ⟨fun w => ⟨w.val, w.property.le⟩,
    fun _ _ h => Subtype.ext (congrArg (fun x : LevelLE r e => x.val) h)⟩

-- 读法：`Fintype (Level r e)` 的取值由 `Fintype.ofInjective (Level.include r e) (Level.include r e).injective` 给出。
noncomputable instance (r e : ℕ) : Fintype (Level r e) :=
  Fintype.ofInjective (Level.include r e) (Level.include r e).injective

-- 读法：`Fintype.card (Level r e)` 不超过 `exp (2 * sqrt ((r : ℝ) * e))`。
theorem card_level (r e : ℕ) :
    Fintype.card (Level r e) ≤ exp (2 * sqrt ((r : ℝ) * e)) :=
  (Nat.cast_le.mpr (Fintype.card_le_of_injective _ (Level.include r e).injective)).trans
    (card_levelLE r e)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# 交错排列同一能级的多个副本

为每个副本的模式分配一个单独的剩余类。反转剩余类的分配顺序，两种分配的总能量之和便等于目标的两倍。保留能量较低的一种，再记录一个方向比特，即得到单射编码。

**英文原文**

Interleaving copies of one level

Put the modes of each copy in their own residue class. Reversing the
class assignment makes the two total energies add to twice the target.
Keeping the lower one and one orientation bit is an injective encoding.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere
open Finset

-- 读法：`ordered` 的结果类型为 `Wedge 1`。
private def ordered (s : Finset ℕ) : Wedge 1 :=
  ⟨(s.sort (· ≤ ·)).map (fun k => (0, k)), by
    rw [List.pairwise_map]
    simpa only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] using
      s.sortedLT_sort.pairwise⟩

-- 读法：`ordered` 是单射。
private theorem ordered_injective : Function.Injective ordered := by
  intro x y h
  simpa [ordered, Function.comp_def] using
    congrArg (fun w : Wedge 1 => (w.val.map Prod.snd).toFinset) h

-- 读法：`energy (ordered s).val` 等于 `∑ i ∈ s, (2 * i + 1)`。
private theorem energy_ordered (s : Finset ℕ) : energy (ordered s).val = ∑ i ∈ s, (2 * i + 1) := by
  simp only [energy, ordered, List.map_map, Function.comp_def]
  rw [← List.sum_toFinset _ (s.sort_nodup _), sort_toFinset]

variable {m e : ℕ}

-- 读法：在后续公式中，`Index` 是 `Sigma (fun _ : Fin m => Mode 1)` 的缩写。
private abbrev Index (m : ℕ) := Sigma (fun _ : Fin m => Mode 1)

-- 读法：`code` 的取值由 `m * i.2.2 + (π i.1).val` 给出。
private def code (π : Equiv.Perm (Fin m)) (i : Index m) := m * i.2.2 + (π i.1).val

-- 读法：`(code π)` 是单射。
private theorem code_injective (π : Equiv.Perm (Fin m)) : Function.Injective (code π) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  change m * k.2 + (π i).val = m * l.2 + (π j).val at h
  have hi := (π i).isLt
  have hj := (π j).isLt
  have hij : i = j := π.injective (Fin.ext (by
    simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using
      congrArg (· % m) h))
  have hkl : k = l := Prod.ext (Subsingleton.elim _ _) (by
    simpa only [Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj,
      add_zero] using congrArg (· / m) h)
  rw [hij, hkl]

-- 读法：`positions` 的取值由 `univ.sigma fun i => (x i).val.val.toFinset` 给出。
private def positions (x : Fin m → Level 1 e) : Finset (Index m) :=
  univ.sigma fun i => (x i).val.val.toFinset

-- 读法：`pack` 的取值由 `ordered ((positions x).image (code π))` 给出。
private def pack (π : Equiv.Perm (Fin m)) (x : Fin m → Level 1 e) : Wedge 1 :=
  ordered ((positions x).image (code π))

-- 读法：`(pack (e := e) π)` 是单射。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem pack_injective (π : Equiv.Perm (Fin m)) : Function.Injective (pack (e := e) π) := by
  intro x y h
  have hp := image_injective (code_injective π) (ordered_injective h)
  funext i
  apply Subtype.ext
  apply Wedge.toFinset_injective
  ext k
  simpa only [positions, mem_sigma, mem_univ, true_and] using
    (congrArg (fun s : Finset (Index m) => ⟨i, k⟩ ∈ s) hp).to_iff

-- 读法：`energy (pack (.refl _) x).val + energy (pack Fin.revPerm x).val` 等于 `2 * (m ^ 2 * e)`。
private theorem energy_pack (x : Fin m → Level 1 e) :
    energy (pack (.refl _) x).val + energy (pack Fin.revPerm x).val = 2 * (m ^ 2 * e) := by
  simp only [pack, energy_ordered, sum_image (code_injective _).injOn, ← sum_add_distrib]
  have he (j : Index m) : 2 * code (.refl _) j + 1 + (2 * code Fin.revPerm j + 1) =
      2 * m * (2 * j.2.2 + 1) := by
    have h : j.1.val + (Fin.revPerm j.1).val + 1 = m := by
      change j.1.val + (m - (j.1.val + 1)) + 1 = m
      have := j.1.isLt
      omega
    unfold code
    simp only [Equiv.refl_apply]
    nlinarith only [h]
  simp_rw [he]
  rw [← mul_sum, positions, sum_sigma]
  have h (i : Fin m) : ∑ k ∈ (x i).val.val.toFinset, (2 * k.2 + 1) = e := by
    rw [List.sum_toFinset _ (x i).val.nodup]
    exact (x i).property
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

-- 读法：`store` 的结果类型为 `Bool × LevelLE 1 (m ^ 2 * e)`。
private def store (x : Fin m → Level 1 e) : Bool × LevelLE 1 (m ^ 2 * e) :=
  if h : energy (pack (.refl _) x).val ≤ m ^ 2 * e then (false, ⟨pack (.refl _) x, h⟩)
  else (true, ⟨pack Fin.revPerm x, by have := energy_pack x; omega⟩)

-- 读法：`(store (m := m) (e := e))` 是单射。这里调用 `pack_injective`。
private theorem store_injective : Function.Injective (store (m := m) (e := e)) := by
  intro x y h
  unfold store at h
  split_ifs at h
  · exact pack_injective _ (congrArg (fun s => s.2.val) h)
  · cases congrArg Prod.fst h
  · cases congrArg Prod.fst h
  · exact pack_injective _ (congrArg (fun s => s.2.val) h)

-- 读法：存在 `g ≤ b`，`Fintype.card (LevelLE 1 b)` 不超过 `(b + 1) * Fintype.card (Level 1 g)`。
theorem largest_level (b : ℕ) :
    ∃ g ≤ b, Fintype.card (LevelLE 1 b) ≤ (b + 1) * Fintype.card (Level 1 g) := by
  let f : LevelLE 1 b → (Σ i : Fin (b + 1), Level 1 i) :=
    fun x => ⟨⟨energy x.val.val, Nat.lt_succ_of_le x.property⟩, ⟨x.val, rfl⟩⟩
  have hf : Function.Injective f :=
    fun _ _ h => Subtype.ext (congrArg (fun x : (Σ i : Fin (b + 1), Level 1 i) => x.2.val) h)
  obtain ⟨j, _, hj⟩ := univ.exists_max_image (fun i : Fin (b + 1) => Fintype.card (Level 1 i))
    univ_nonempty
  refine ⟨j.val, by have := j.isLt; omega, (Fintype.card_le_of_injective f hf).trans ?_⟩
  rw [Fintype.card_sigma]
  simpa using sum_le_card_nsmul univ _ _ hj

-- 读法：存在 `g ≤ m ^ 2 * e`，`Fintype.card (Level 1 e) ^ m` 不超过 `2 * (m ^ 2 * e + 1) * Fintype.card (Level 1 g)`。这里调用 `hs.trans`。
/-- 放大过程的损失至多为目标能量的多项式。

英文原文：Amplification with a loss polynomial in the target energy.
-/
theorem interleave_level (m e : ℕ) :
    ∃ g ≤ m ^ 2 * e, Fintype.card (Level 1 e) ^ m ≤ 2 * (m ^ 2 * e + 1) * Fintype.card (Level 1 g) := by
  obtain ⟨g, hg, hb⟩ := largest_level (m ^ 2 * e)
  refine ⟨g, hg, ?_⟩
  have hs := Fintype.card_le_of_injective _ (store_injective (m := m) (e := e))
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hs
  rw [mul_assoc]
  exact hs.trans (Nat.mul_le_mul_left 2 hb)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# 站点比特的定能量编码

每个比特使用四个连续模式中的中间一对或最外一对。两种选择的能量相等，由此在单一整数能级上得到二次能量上界，无须借助整数分拆的渐近公式。

**英文原文**

Fixed-energy codes for station bits

For each bit use either the inner or outer pair of four consecutive modes.
The two choices have equal energy. This gives a quadratic energy bound at
a single integer level without partition asymptotics.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

-- 读法：`toLex a < toLex b` 与 `a.2 < b.2` 等价。
private theorem lex_one (a b : Mode 1) : toLex a < toLex b ↔ a.2 < b.2 := by
  rw [Prod.Lex.toLex_lt_toLex, Subsingleton.elim a.1 b.1]
  simp

-- 读法：`xs.length ^ 2 + 2 * n * xs.length` 不超过 `energy xs`。对 `xs` 作归纳，并把 `n` 保持为任意参数。
private theorem length_bound (xs : List (Mode 1)) (n : ℕ)
    (h : xs.Pairwise fun a b => toLex a < toLex b) (hn : ∀ a ∈ xs, n ≤ a.2) :
    xs.length ^ 2 + 2 * n * xs.length ≤ energy xs := by
  induction xs generalizing n with
  | nil => simp [energy]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    have h₀ := hn a (by simp)
    have h₁ := ih (n + 1) hl (fun b hb => Nat.succ_le_of_lt
      (lt_of_le_of_lt h₀ ((lex_one a b).mp (ha b hb))))
    change (l.length + 1) ^ 2 + 2 * n * (l.length + 1) ≤ 2 * a.2 + 1 + energy l
    nlinarith only [h₀, h₁]

-- 读法：`w.val.length ^ 2` 不超过 `energy w.val`。这里调用 `length_bound`。
theorem Wedge.length_sq_le (w : Wedge 1) : w.val.length ^ 2 ≤ energy w.val := by
  simpa using length_bound w.val 0 w.property (by simp)

-- 读法：逐一匹配以下输入模式：`_, []`、`j, b :: l`。
private def encode : ℕ → List Bool → List (Mode 1)
  | _, [] => []
  | j, b :: l =>
    (0, 4 * j + b.toNat) :: (0, 4 * j + 2 + (!b).toNat) :: encode (j + 1) l

-- 读法：`(∀ a ∈ encode j l, 4 * j ≤ a.2)` 与 `(encode j l).Pairwise (fun a b => toLex a < toLex b)` 同时成立。对 `l` 作归纳，并把 `j` 保持为任意参数。
private theorem encode_order (j : ℕ) (l : List Bool) :
    (∀ a ∈ encode j l, 4 * j ≤ a.2) ∧ (encode j l).Pairwise (fun a b => toLex a < toLex b) := by
  induction l generalizing j with
  | nil => simp [encode]
  | cons b l ih =>
    obtain ⟨hl, hp⟩ := ih (j + 1)
    have h₁ : b.toNat ≤ 1 := by cases b <;> decide
    have h₂ : (!b).toNat ≤ 1 := by cases b <;> decide
    simp only [encode, List.forall_mem_cons, List.pairwise_cons]
    refine ⟨⟨by omega, by omega, fun a ha => ?_⟩,
      ⟨by rw [lex_one]; omega, fun a ha => ?_⟩, fun a ha => ?_, hp⟩
    all_goals have := hl a ha
    · omega
    · rw [lex_one]; omega
    · rw [lex_one]; omega

-- 读法：`energy (encode j l)` 等于 `8 * l.length ^ 2 + 16 * j * l.length`。对 `l` 作归纳，并把 `j` 保持为任意参数。
private theorem encode_energy (j : ℕ) (l : List Bool) :
    energy (encode j l) = 8 * l.length ^ 2 + 16 * j * l.length := by
  induction l generalizing j with
  | nil => simp [encode, energy]
  | cons b l ih =>
    change 2 * (4 * j + b.toNat) + 1 + (2 * (4 * j + 2 + (!b).toNat) + 1 + energy (encode (j + 1) l)) = _
    rw [ih, List.length_cons]
    cases b <;> simp <;> ring

-- 读法：`(encode j)` 是单射。对 `l'` 分类讨论。
private theorem encode_injective (j : ℕ) : Function.Injective (encode j) := by
  intro l l' he
  induction l generalizing j l' with
  | nil => cases l' <;> simp_all [encode]
  | cons b l ih =>
    cases l' with
    | nil => simp [encode] at he
    | cons c l' =>
      simp only [encode, List.cons.injEq, Prod.mk.injEq, true_and] at he
      have : b = c := by cases b <;> cases c <;> simp_all
      rw [this, ih _ he.2.2]

-- 读法：用字段 `toFun`、`inj'` 构造 `(Fin n → Bool) ↪ {w : Wedge 1 // energy w.val = 8 * n ^ 2}`。
/-- 将 `n` 个比特显式单射到物理能量 `4n²`（倍能量 `8n²`）的单物种能级。

英文原文：An explicit injection of `n` bits into a single-species level of
physical energy `4n²` (doubled energy `8n²`).
-/
def bitCode (n : ℕ) : (Fin n → Bool) ↪ {w : Wedge 1 // energy w.val = 8 * n ^ 2} where
  toFun x := ⟨⟨encode 0 (List.ofFn x), (encode_order _ _).2⟩, by simp [encode_energy]⟩
  inj' _ _ h := List.ofFn_inj.mp (encode_injective 0 (congrArg (fun x => x.val.val) h))

-- 读法：`(encode k xs).length` 等于 `2 * xs.length`。对 `xs` 作归纳，并把 `k` 保持为任意参数。
private theorem encode_length (k : ℕ) (xs : List Bool) : (encode k xs).length = 2 * xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp only [encode, List.length_cons, ih]; omega

-- 读法：`(bitCode n x).val.val.length` 等于 `2 * n`。
theorem bitCode_length {n : ℕ} (x : Fin n → Bool) : (bitCode n x).val.val.length = 2 * n := by
  change (encode 0 (List.ofFn x)).length = _
  rw [encode_length, List.length_ofFn]

-- 读法：`j.2` 严格小于 `4 * (k + xs.length)`。对 `xs` 作归纳，并把 `k` 保持为任意参数。
private theorem encode_support (k : ℕ) (xs : List Bool) (j : Mode 1) (h : j ∈ encode k xs) :
    j.2 < 4 * (k + xs.length) := by
  induction xs generalizing k with
  | nil => simp [encode] at h
  | cons x xs ih =>
    simp only [encode, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · cases x <;> simp; omega
    · cases x <;> simp <;> omega
    · have := ih _ h
      simp only [List.length_cons]
      omega

-- 读法：`j.2` 严格小于 `4 * n`。这里调用 `encode_support`。
theorem bitCode_support {n : ℕ} (x : Fin n → Bool) (j : Mode 1) (h : j ∈ (bitCode n x).val.val) :
    j.2 < 4 * n := by
  simpa using encode_support 0 (List.ofFn x) j h

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# 双位点融合中带权的输入和输出位置

当两倍能量分别为 `e,g` 时，各位置的总权重为 `√e + √g`。对于权重为 `t` 的槽位，可用两倍能量至多为 `(√e + √g) * t + 1` 的检验将其单独分离。

**英文原文**

Weighted input and output positions for two-site fusion

At doubled energies `e,g` the positions have total weight
`√e + √g`. A slot of weight `t` can be isolated with a test
of doubled energy at most `(√e + √g) * t + 1`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Width

-- 读法：在后续公式中，`Slot` 是 `Bool × Mode 1` 的缩写。
abbrev Slot := Bool × Mode 1

-- 读法：`slots` 的取值由 `a.val.map (false, ·) ++ b.val.reverse.map (true, ·)` 给出。
/-- 输入按楔积次序排列，输出按对偶次序排列。

英文原文：Input in wedge order, output in dual order.
-/
def slots (a b : Wedge 1) : List Slot :=
  a.val.map (false, ·) ++ b.val.reverse.map (true, ·)

-- 读法：`a` 等于 `b`。按 `Subtype.ext` 的外延性准则比较各分量。
private theorem eq_wedge {a b : Wedge 1} (h : ∀ i, i ∈ a.val ↔ i ∈ b.val) : a = b := by
  apply Subtype.ext
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (asymm h₁ h₂).elim) a.property b.property
  exact (List.perm_ext_iff_of_nodup a.nodup b.nodup).mpr h

-- 读法：`a = a'` 与 `b = b'` 同时成立。这里调用 `eq_wedge`。
theorem slots_inj {a b a' b' : Wedge 1} (h : (slots a b).Perm (slots a' b')) :
    a = a' ∧ b = b' := by
  constructor
  · apply eq_wedge
    intro i
    simpa [slots] using h.mem_iff (a := (false, i))
  · apply eq_wedge
    intro i
    simpa [slots] using h.mem_iff (a := (true, i))

-- 读法：要证明的命题是 `(slots a b).Nodup`。这里调用 `List.nodup_append.mpr`。
theorem slots_nodup (a b : Wedge 1) : (slots a b).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨a.nodup.map (fun _ _ h => congrArg Prod.snd h),
    (List.nodup_reverse.mpr b.nodup).map (fun _ _ h => congrArg Prod.snd h), ?_⟩
  simp

variable (w : Bool → ℝ)

-- 读法：`weight` 的取值由 `(2 * (x.2.2 : ℝ) + 1) / w x.1` 给出。
def weight (x : Slot) : ℝ := (2 * (x.2.2 : ℝ) + 1) / w x.1

-- 读法：`other` 的取值由 `⌊(weight w x * w (!x.1) + 1) / 2⌋₊` 给出。
def other (x : Slot) := ⌊(weight w x * w (!x.1) + 1) / 2⌋₊

-- 读法：当 `x.1` 成立时取 `x.2.2`，否则取 `other w x`。
def start (x : Slot) := if x.1 then x.2.2 else other w x

-- 读法：当 `x.1` 成立时取 `other w x`，否则取 `x.2.2`。
def order (x : Slot) := if x.1 then other w x else x.2.2

-- 读法：`cost` 的取值由 `2 * (start w x + order w x) + 1` 给出。
def cost (x : Slot) := 2 * (start w x + order w x) + 1

-- 读法：`0` 严格小于 `weight w x`。使用 `div_pos` 给出的结论。
theorem weight_pos {x : Slot} (h : 0 < w x.1) : 0 < weight w x :=
  div_pos (by positivity) h

-- 读法：`weight w x * w x.1` 等于 `2 * (x.2.2 : ℝ) + 1`。使用 `div_mul_cancel₀` 给出的结论。
private theorem weight_mul {x : Slot} (h : 0 < w x.1) :
    weight w x * w x.1 = 2 * (x.2.2 : ℝ) + 1 := div_mul_cancel₀ _ h.ne'

-- 读法：`y.2.2` 不超过 `x.2.2`。
theorem same {x y : Slot} (hx : 0 < w x.1) (hs : y.1 = x.1) (h : weight w y ≤ weight w x) :
    y.2.2 ≤ x.2.2 := by
  simp only [weight, hs, div_le_div_iff_of_pos_right hx] at h
  exact_mod_cast (show (y.2.2 : ℝ) ≤ x.2.2 by linarith)

-- 读法：`y.2.2` 严格小于 `other w x`。
theorem different {x y : Slot} (hy : 0 < w y.1) (hs : y.1 = !x.1)
    (h : weight w y ≤ weight w x) : y.2.2 < other w x := by
  have hl := mul_le_mul_of_nonneg_right h hy.le
  rw [weight_mul w hy, hs] at hl
  have hu := Nat.lt_floor_add_one ((weight w x * w (!x.1) + 1) / 2)
  unfold other
  exact_mod_cast (show (y.2.2 : ℝ) < ⌊(weight w x * w (!x.1) + 1) / 2⌋₊ by linarith)

-- 读法：`(cost w x : ℝ)` 不超过 `(w false + w true) * weight w x + 1`。
private theorem cost_le (hw : ∀ i, 0 ≤ w i) {x : Slot} (hx : 0 < w x.1) :
    (cost w x : ℝ) ≤ (w false + w true) * weight w x + 1 := by
  have hother : (other w x : ℝ) ≤ (weight w x * w (!x.1) + 1) / 2 :=
    Nat.floor_le (by have := hw (!x.1); have := weight_pos w hx; positivity)
  have h := weight_mul w hx
  obtain ⟨_ | _, x⟩ := x <;> simp [cost, start, order] at * <;> linarith

-- 读法：`((xs.map (cost w)).sum : ℝ)` 不超过 `(w false + w true) * (xs.map (weight w)).sum + xs.length`。对 `xs` 作归纳。
private theorem cost_sum (hw : ∀ i, 0 ≤ w i) (xs : List Slot) (hx : ∀ x ∈ xs, 0 < w x.1) :
    ((xs.map (cost w)).sum : ℝ) ≤ (w false + w true) * (xs.map (weight w)).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.forall_mem_cons] at hx
    have h := add_le_add (cost_le w hw hx.1) (ih hx.2)
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, List.length_cons, Nat.cast_one, mul_add]
    linarith

-- 读法：`((xs.map (i, ·)).map (weight w)).sum` 等于 `energy xs / w i`。对 `xs` 作归纳。
private theorem side_sum (i : Bool) (xs : List (Mode 1)) :
    ((xs.map (i, ·)).map (weight w)).sum = energy xs / w i := by
  induction xs with
  | nil => simp [energy]
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih]
    simp [weight, energy, add_div]

variable (a b : Wedge 1) (ha : w false = Real.sqrt (energy a.val))
    (hb : w true = Real.sqrt (energy b.val))

include ha hb

-- 读法：`0` 严格小于 `w x.1`。这里调用 `Real.sqrt_pos.mpr`。
theorem slots_valid (x : Slot) (hx : x ∈ slots a b) : 0 < w x.1 := by
  have pos (s : List (Mode 1)) (i : Mode 1) (hi : i ∈ s) : 0 < Real.sqrt (energy s) := by
    have hm : 2 * i.2 + 1 ≤ energy s := List.le_sum_of_mem (List.mem_map_of_mem hi)
    exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  simp only [slots, List.mem_append, List.mem_map, List.mem_reverse] at hx
  rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [ha]; exact pos _ _ hi
  · rw [hb]; exact pos _ _ hi

-- 读法：`((slots a b).map (weight w)).sum` 等于 `w false + w true`。按 `x = 0` 成立与否分情况。
theorem slots_weight : ((slots a b).map (weight w)).sum = w false + w true := by
  have he (x : ℕ) : (x : ℝ) / Real.sqrt x = Real.sqrt x := by
    by_cases h : x = 0
    · simp [h]
    · rw [div_eq_iff (by positivity)]
      exact (Real.mul_self_sqrt (by positivity)).symm
  simp only [slots, List.map_append, List.sum_append, side_sum, ha, hb,
    show energy b.val.reverse = energy b.val by simp [energy], he]

-- 读法：`(((slots a b).map (cost w)).sum : ℝ)` 不超过 `(w false + w true) ^ 2 + (w false + w true)`。这里调用 `Real.le_sqrt`。
theorem slots_cost : (((slots a b).map (cost w)).sum : ℝ) ≤
    (w false + w true) ^ 2 + (w false + w true) := by
  have hp (i : Bool) : 0 ≤ w i := by cases i <;> simp [ha, hb]
  have h := cost_sum w hp _ (slots_valid w a b ha hb)
  rw [slots_weight w a b ha hb, ← pow_two] at h
  refine h.trans (add_le_add_right ?_ _)
  have len (z : Wedge 1) : (z.val.length : ℝ) ≤ Real.sqrt (energy z.val) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast z.length_sq_le
  simpa [slots, ha, hb] using add_le_add (len a) (len b)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Width
end

section
/-!
# 单物种能级共同的精确增长率

归一化对数维数的上确界有限且为正。选定一个接近该上确界的能级，将其交错排列，就能适配所有充分大的目标宽度，损失仅为对数量级。

**英文原文**

Sharp common growth rate for one-species levels

The supremum of the normalized log dimensions is finite and positive.
Interleaving a fixed level approaching this supremum works at every
sufficiently large target width, with only logarithmic loss.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere
open Real Filter

-- 读法：`rate` 的取值由 `log (Fintype.card (Level 1 e)) / sqrt e` 给出。
private noncomputable def rate (e : ℕ) : ℝ := log (Fintype.card (Level 1 e)) / sqrt e

-- 读法：`entropy` 的取值由 `sSup (Set.range rate)` 给出。
noncomputable def entropy : ℝ := sSup (Set.range rate)

-- 读法：`log (Fintype.card (Level 1 e))` 不超过 `2 * sqrt e`。按 `Fintype.card (Level 1 e) = 0` 成立与否分情况。
private theorem coarse (e : ℕ) : log (Fintype.card (Level 1 e)) ≤ 2 * sqrt e := by
  by_cases h : Fintype.card (Level 1 e) = 0
  · simp [h]
  · apply (log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    simpa using card_level 1 e

-- 读法：要证明的命题是 `BddAbove (Set.range rate)`。按 `e = 0` 成立与否分情况。
private theorem rate_bdd : BddAbove (Set.range rate) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨e, rfl⟩
  by_cases h : e = 0
  · simp [rate, h]
  · exact (div_le_iff₀ (by positivity)).mpr (coarse e)

-- 读法：`0` 严格小于 `entropy`。这里调用 `hr.trans_le`。
theorem entropy_pos : 0 < entropy := by
  have h : 1 < Fintype.card (Level 1 8) := by
    have hb := Fintype.card_le_of_injective (bitCode 1) (bitCode 1).injective
    change 2 ≤ Fintype.card (Level 1 8)
    simpa [Fintype.card_fun] using hb
  have hr : 0 < rate 8 := div_pos (log_pos (by exact_mod_cast h)) (by positivity)
  exact hr.trans_le (le_csSup rate_bdd (Set.mem_range_self 8))

-- 读法：`log (Fintype.card (Level 1 e))` 不超过 `entropy * sqrt e`。按 `e = 0` 成立与否分情况。
theorem entropy_bound (e : ℕ) : log (Fintype.card (Level 1 e)) ≤ entropy * sqrt e := by
  by_cases h : e = 0
  · simpa [h] using coarse e
  · exact (div_le_iff₀ (by positivity)).mp (le_csSup rate_bdd (Set.mem_range_self e))

-- 读法：`(Fintype.card (LevelLE 1 e) : ℝ)` 不超过 `(e + 1) * exp (entropy * sqrt e)`。这里调用 `le_exp_of_log_le`。
theorem card_levelLE_exp (e : ℕ) :
    (Fintype.card (LevelLE 1 e) : ℝ) ≤ (e + 1) * exp (entropy * sqrt e) := by
  obtain ⟨g, hg, hb⟩ := largest_level e
  calc
    _ ≤ ((e : ℝ) + 1) * Fintype.card (Level 1 g) := by exact_mod_cast hb
    _ ≤ ((e : ℝ) + 1) * exp (entropy * sqrt g) := by
      gcongr
      exact le_exp_of_log_le (entropy_bound g)
    _ ≤ _ := by have := entropy_pos; gcongr

-- 读法：对每个 `ᶠ t : ℝ in atTop`，`C + log (2 * (t ^ 2 + 1))` 不超过 `ε * t`。
private theorem negligible (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, C + log (2 * (t ^ 2 + 1)) ≤ ε * t := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * (C + log 4) / ε),
    isLittleO_log_id_atTop.bound (by positivity : 0 < ε / 4)] with t ht hc hl
  rw [div_le_iff₀ hε] at hc
  have h : log (2 * (t ^ 2 + 1)) ≤ log 4 + 2 * log t := by
    calc
      _ ≤ log (4 * t ^ 2) := log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [log_mul (by norm_num) (by positivity), log_pow]; norm_num
  simp only [id_eq, norm_eq_abs, abs_of_nonneg (log_nonneg ht), abs_of_nonneg (by linarith : 0 ≤ t)]
    at hl
  linarith

-- 读法：对每个 `ᶠ t : ℝ in atTop`，存在 `e : ℕ`，`(e : ℝ) ≤ t ^ 2` 与 `a * t ≤ log (Fintype.card (Level 1 e))` 同时成立。
private theorem entropy_reaches {a : ℝ} (ha : 0 < a) (ha' : a < entropy) :
    ∀ᶠ t : ℝ in atTop, ∃ e : ℕ, (e : ℝ) ≤ t ^ 2 ∧ a * t ≤ log (Fintype.card (Level 1 e)) := by
  obtain ⟨_, ⟨e, rfl⟩, he⟩ := exists_lt_of_lt_csSup (Set.range_nonempty rate) ha'
  have hpos : 0 < rate e := ha.trans he
  have he0 : e ≠ 0 := by rintro rfl; simp [rate] at hpos
  have hs : 0 < sqrt (e : ℝ) := by positivity
  have hrate : rate e * sqrt e = log (Fintype.card (Level 1 e)) := div_mul_cancel₀ _ hs.ne'
  have hn : 0 < Fintype.card (Level 1 e) := by
    by_contra! h
    have : Fintype.card (Level 1 e) = 0 := by omega
    simp [rate, this] at hpos
  filter_upwards [eventually_ge_atTop 0,
    negligible (log (Fintype.card (Level 1 e))) (rate e - a) (sub_pos.mpr he)] with t ht hl
  let m := ⌊t / sqrt e⌋₊
  -- 推导：记下中间结论 `hu`：`(m : ℝ) * sqrt e ≤ t`。
  have hu : (m : ℝ) * sqrt e ≤ t := (le_div_iff₀ hs).mp (Nat.floor_le (by positivity))
  have hv : t ≤ ((m : ℝ) + 1) * sqrt e := (div_le_iff₀ hs).mp (Nat.lt_floor_add_one _).le
  have hb : (m : ℝ) ^ 2 * e ≤ t ^ 2 := by
    rw [← sq_sqrt (Nat.cast_nonneg e), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hu _
  obtain ⟨g, hg, hdim⟩ := interleave_level m e
  refine ⟨g, le_trans (by exact_mod_cast hg) hb, ?_⟩
  have hng : 0 < Fintype.card (Level 1 g) := by
    have := (pow_pos hn m).trans_le hdim
    exact Nat.pos_of_mul_pos_left this
  -- 推导：记下中间结论 `hd`：`(Fintype.card (Level 1 e) : ℝ) ^ m ≤ 2 * (t ^ 2 + 1) * Fintype.card (Level 1 g)`。
  have hd : (Fintype.card (Level 1 e) : ℝ) ^ m ≤ 2 * (t ^ 2 + 1) * Fintype.card (Level 1 g) := by
    calc
      _ ≤ 2 * ((m : ℝ) ^ 2 * e + 1) * Fintype.card (Level 1 g) := by exact_mod_cast hdim
      _ ≤ _ := by gcongr
  have hlog := log_le_log (by positivity) hd
  rw [log_pow, log_mul (by positivity) (by positivity)] at hlog
  have hlow : rate e * t ≤ ((m : ℝ) + 1) * log (Fintype.card (Level 1 e)) := by
    rw [← hrate, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hv hpos.le
  linarith

-- 读法：对每个 `ᶠ t : ℝ in atTop`，存在 `e : ℕ`，`(e : ℝ) ≤ t ^ 2` 与 `(entropy - δ) * t ≤ log (Fintype.card (Level 1 e))` 同时成立。
/-- 在任意充分大的二次截断界之下，总有一个能级在该截断界的尺度上接近公共的对数维数上界。

英文原文：One level below any sufficiently large quadratic cutoff nearly attains
the common log-dimension bound at the scale of the cutoff.
-/
theorem entropy_attained {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, ∃ e : ℕ, (e : ℝ) ≤ t ^ 2 ∧
      (entropy - δ) * t ≤ log (Fintype.card (Level 1 e)) := by
  let a := max (entropy - δ) (entropy / 2)
  have ha : 0 < a := (half_pos entropy_pos).trans_le (le_max_right _ _)
  have hb : a < entropy := max_lt (sub_lt_self _ hδ) (half_lt_self entropy_pos)
  filter_upwards [eventually_ge_atTop 0, entropy_reaches ha hb] with t ht h
  obtain ⟨e, he, hd⟩ := h
  exact ⟨e, he, (mul_le_mul_of_nonneg_right (le_max_left _ _) ht).trans hd⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# 双位点融合映射的整系数检验

参数为 `a,d` 的检验表示洛朗多项式 `X^(-a-1) (1-X⁻¹)^d`。它在零点和一点的首项位置索引分别为 `a` 和 `d`。

**英文原文**

Integral tests for the two-site fusion map

The test with parameters `a,d` represents the Laurent polynomial
`X^(-a-1) (1-X⁻¹)^d`. Its leading positions at zero and one have
indices `a` and `d` respectively.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Width

variable (R : Type*) [CommRing R]

-- 读法：`test` 的取值由 `∑ f ∈ Finset.range (d + 1), (-1 : R) ^ f * d.choose f * pairing R (.origin, 0, a + f) y` 给出。
def test (a d : ℕ) (y : Mark 1) : R :=
  ∑ f ∈ Finset.range (d + 1), (-1 : R) ^ f * d.choose f * pairing R (.origin, 0, a + f) y

-- 读法：`test R a d (.origin, y)` 等于 `0`。
theorem test_origin (a d : ℕ) (y : Mode 1) : test R a d (.origin, y) = 0 := by
  have he (m : ℕ) : pairing R (.origin, 0, m) (.origin, y) = 0 := by
    change (if 0 = y.1 then (0 : R) else 0) = _
    simp
  simp [test, he]

-- 读法：`test R a d (.infinity, y)` 等于 `if a = y.2 then 1 else 0`。
private theorem test_infinity (a d : ℕ) (y : Mode 1) (hy : y.2 ≤ a) :
    test R a d (.infinity, y) = if a = y.2 then 1 else 0 := by
  have he (m : ℕ) : pairing R (.origin, 0, m) (.infinity, y) =
      if m = y.2 then 1 else 0 := by
    change (if 0 = y.1 then (if m = y.2 then (1 : R) else 0) else 0) = _
    rw [ite_eq_left (Subsingleton.elim _ _)]
  unfold test
  rw [Finset.sum_eq_single 0]
  · simp [he]
  · intro b _ hb
    rw [he, ite_eq_right (by omega), mul_zero]
  · simp

-- 读法：`test R a d (.middle, y)` 等于 `if d = y.2 then 1 else 0`。这里调用 `Finset.sum_congr`。
private theorem test_middle (a d : ℕ) (y : Mode 1) (hy : y.2 ≤ d) :
    test R a d (.middle, y) = if d = y.2 then 1 else 0 := by
  have he (m : ℕ) : pairing R (.origin, 0, m) (.middle, y) =
      (-1 : R) ^ y.2 * (m + y.2).choose y.2 := by
    change (if 0 = y.1 then (-1 : R) ^ y.2 * (m + y.2).choose y.2 else 0) = _
    rw [ite_eq_left (Subsingleton.elim _ _)]
  have e : test R a d (.middle, y) = (-1 : R) ^ y.2 * ((-1) ^ d * (a + y.2).choose (d + a)) := by
    unfold test
    rw [← binom_difference, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    -- 推导：记下中间结论 `h`：`(a + f + y.2).choose y.2 = (a + y.2 + f).choose (f + a)`。
    have h : (a + f + y.2).choose y.2 = (a + y.2 + f).choose (f + a) := by
      rw [← Nat.choose_symm (by omega : y.2 ≤ a + f + y.2)]
      congr 1 <;> omega
    rw [he, h]
    ring
  rw [e]
  by_cases h : d = y.2
  · rw [h, Nat.add_comm y.2 a, Nat.choose_self, Nat.cast_one, mul_one, ← mul_pow]
    simp
  · rw [ite_eq_right h, Nat.choose_eq_zero_of_lt (by omega : a + y.2 < d + a)]
    simp

-- 读法：`mark` 的取值由 `(if x.1 then .infinity else .middle, x.2)` 给出。
def mark (x : Slot) : Mark 1 := (if x.1 then .infinity else .middle, x.2)

-- 读法：`x = y` 与 `x.2 = y.2` 等价。
private theorem mode_eq (x y : Mode 1) : x = y ↔ x.2 = y.2 :=
  ⟨fun h => congrArg _ h, fun h => Prod.ext (Subsingleton.elim _ _) h⟩

-- 读法：`test R (start w x) (order w x) (mark y)` 等于 `if x = y then 1 else 0`。
/-- 在权重相等或更小时，只有指定槽位保留下来。

英文原文：At equal or smaller weight only the designated slot survives.
-/
theorem test_pivot (w : Bool → ℝ) (x y : Slot) (hx : 0 < w x.1) (hy : 0 < w y.1)
    (h : weight w y ≤ weight w x) :
    test R (start w x) (order w x) (mark y) = if x = y then 1 else 0 := by
  obtain ⟨_ | _, i⟩ := x <;> obtain ⟨_ | _, j⟩ := y
  · have := same w (y := (false, j)) hx rfl h
    simp [start, order, mark, test_middle _ _ _ _ this, mode_eq]
  · have hl := different w hy rfl h
    simp [start, order, mark, test_infinity _ _ _ _ hl.le, ne_of_gt hl]
  · have hl := different w hy rfl h
    simp [start, order, mark, test_middle _ _ _ _ hl.le, ne_of_gt hl]
  · have := same w (y := (true, j)) hx rfl h
    simp [start, order, mark, test_infinity _ _ _ _ this, mode_eq]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Width
end

/-!
# 接缝处的转置

在通常的楔积基中计算融合时，将输出模式倒序置于末尾。取逆使每个配对变号，再反转整个 Wick 列表，便逐对抵消这些符号。由此得到同一个整系数降低算子，在任何特征下其标量因子均为一。

**英文原文**

Transposition at a seam

Evaluate fusion in the ordinary wedge basis by placing the output modes
last, in reverse order. Inversion negates each pairing. Reversing the
entire Wick list then cancels the signs pair by pair. This gives a single
integral lowering operator, with scalar one in every characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable (R : Type*) [CommRing R] {r : ℕ}

-- 读法：`marks` 的取值由 `x.map (c, ·)` 给出。
def marks (c : Chart) (x : List (Mode r)) : List (Mark r) := x.map (c, ·)

-- 读法：`fusion` 的取值由 `wick (pairing R) (marks .origin a ++ marks .middle x ++ marks .infinity b.reverse)` 给出。
/-- 偏移量为零和一时双位点融合的矩阵元。与输出块的两项收缩给出两个平移系数；其逆序给出通常的对偶楔积配对。

英文原文：Matrix entry of the two-site fusion at offsets zero and one.
Contractions to the output block are the two translation coefficients.
Its reversed order gives the ordinary dual wedge pairing.
-/
def fusion (a x b : List (Mode r)) : R :=
  wick (pairing R) (marks .origin a ++ marks .middle x ++ marks .infinity b.reverse)

-- 读法：`fusion R a x b` 等于 `wick (pairing R) (marks .origin b ++ marks .dual x.reverse ++ marks .infinity a.reverse)`。
theorem fusion_reflect (a x b : List (Mode r)) :
    fusion R a x b =
      wick (pairing R) (marks .origin b ++ marks .dual x.reverse ++ marks .infinity a.reverse) := by
  let l := marks .origin a ++ marks .middle x ++ marks .infinity b.reverse
  have he : (l.map reflect).reverse =
      marks .origin b ++ marks .dual x.reverse ++ marks .infinity a.reverse := by
    simp [l, marks, List.map_map, Function.comp_def, reflect, Chart.reflect]
  rw [← he, wick_reverse (pairing_skew R), wick_map]
  simp only [pairing_reflect, neg_neg]
  rfl

-- 读法：`transform` 的证明用到 `Finset.range`、`Finset.mem_range`。
private theorem transform (x p : List (Mode r)) :
    ∃ g : Wedge r →₀ R,
      (∀ y ∈ g.support, energy y.val ≤ energy p + energy x ∧
        y.val.length = p.length + x.length) ∧
      ∀ a b : List (Mark r),
        wick (pairing R) (a ++ marks .middle p ++ marks .dual x ++ b) =
          Finsupp.linearCombination R
            (fun y : Wedge r => wick (pairing R) (a ++ marks .middle y.val ++ b)) g := by
  refine substitute_modes (pairing_skew R) (pairing_self R)
    (fun i => (.dual, i)) (fun i => (.middle, i)) (fun i => 2 * i.2 + 1) ?_ x p
  intro z
  refine ⟨Finset.range (z.2 + 1), lower R z.2, fun f => (z.1, f), ?_, pairing_lower R z⟩
  simp only [Finset.mem_range]
  omega

-- 读法：`entry` 的取值由 `Finsupp.linearCombination R (fun x => fusion R a.val x.val b.val)` 给出。
/-- 中间态取叠加时的矩阵系数。

英文原文：Matrix coefficient with a superposition of middle states.
-/
def entry (a b : Wedge r) : (Wedge r →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun x => fusion R a.val x.val b.val)

-- 读法：这里调用 `Finsupp.lhom_ext`。
/-- 同一个算子将所有融合矩阵转置。基输入的每个输出都保持外代数次数，且其能量不增加。

英文原文：The same operator transposes every fusion matrix. Each output of a
basis input preserves exterior degree and weakly lowers energy.
-/
theorem seam (r : ℕ) :
    ∃ S : (Wedge r →₀ R) →ₗ[R] (Wedge r →₀ R),
      (∀ x y : Wedge r, y ∈ (S (Finsupp.single x 1)).support →
        energy y.val ≤ energy x.val ∧ y.val.length = x.val.length) ∧
      ∀ a b : Wedge r, entry R a b = (entry R b a).comp S := by
  choose g hg he using fun x : Wedge r => transform R x.val.reverse []
  refine ⟨Finsupp.linearCombination R g, ?_, ?_⟩
  · intro x y hy
    simp only [Finsupp.linearCombination_single, one_smul] at hy
    simpa [energy] using hg x y hy
  · intro a b
    apply Finsupp.lhom_ext
    intro x t
    simp only [entry, LinearMap.comp_apply, Finsupp.linearCombination_single, map_smul]
    rw [fusion_reflect]
    simpa only [marks, List.map_nil, List.append_nil, fusion] using
      congrArg (t • ·) (he x (marks .origin b.val) (marks .infinity a.val.reverse))

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

-- 读法：`vac` 的结果类型为 `Level r 0`。
/-- 空楔积是唯一的零能态。

英文原文：The empty wedge is the only state at zero energy.
-/
def vac (r : ℕ) : Level r 0 := ⟨⟨[], by simp⟩, rfl⟩

-- 读法：`x` 等于 `vac r`。按 `Subtype.ext` 的外延性准则比较各分量。
theorem eq_vac {r : ℕ} (x : Level r 0) : x = vac r := by
  apply Subtype.ext
  apply Subtype.ext
  have h := x.2
  cases e : x.val.val with
  | nil => rfl
  | cons i s => simp [e, energy] at h

-- 读法：用字段 `default`、`uniq` 构造 `Unique (Level r 0)`。
instance (r : ℕ) : Unique (Level r 0) where
  default := vac r
  uniq := eq_vac

end OAI.LinearAlgebra.MatrixExponent.Sphere
end
