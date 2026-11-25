-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

universe u w

section
/-!
# 系数取自赋值环时的消元

**英文原文**

Elimination with coefficients in a valuation ring
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (A : Subalgebra K E) (hA : ∀ x : E, x ∈ A ∨ x⁻¹ ∈ A)
  {I : Type} [Fintype I] [DecidableEq I]

include hA in
-- 读法：存在 `m`，`v m ≠ 0` 与 `∀ i, v i / v m ∈ A` 同时成立。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
/-- 在赋值环上选一个非零主元，使其整除所有矩阵元。

英文原文：Pick a nonzero pivot dividing every entry over the valuation ring.
-/
private theorem pivot (v : I → E) {k : I} (hk : v k ≠ 0) :
    ∃ m, v m ≠ 0 ∧ ∀ i, v i / v m ∈ A := by
  have aux (s : Finset I) : ∃ m, v m ≠ 0 ∧ ∀ i ∈ s, v i / v m ∈ A := by
    induction s using Finset.induction_on with
    | empty => exact ⟨k, hk, by simp⟩
    | insert j _ _ ih =>
      obtain ⟨m, hm, hr⟩ := ih
      simp only [mem_insert, forall_eq_or_imp]
      by_cases h : v j / v m ∈ A
      · exact ⟨m, hm, h, hr⟩
      have hj : v j ≠ 0 := fun e => h (by simp [e])
      have h' : v m / v j ∈ A := by simpa using (hA _).resolve_left h
      refine ⟨j, hj, by simp [hj], fun i hi => ?_⟩
      rw [← div_mul_div_cancel₀ hm]
      exact A.mul_mem (hr i hi) h'
  simpa using aux univ

include hA in
-- 读法：存在 `(S : Finset I) (P : Matrix I I A)`，`Fintype.card I - d` 不超过 `S.card ∧ (∀ i ∈ S, ∀ j ∈ S, P i j = if i = j then 1 else 0) ∧ ∀ i l, ∑ j, (P i j : E) * w l j = 0`。对 `d` 作归纳。
/-- 保留下来的列始终等于相应的标准基列。因此减去第 `m` 行的某个倍数时，除第 `m` 列外，这些列均保持不变。

英文原文：The surviving columns are kept equal to the standard basis columns.
Subtracting a multiple of row `m` therefore preserves all of them except `m`.
-/
theorem eliminate {d : ℕ} (w : Fin d → I → E) :
    ∃ (S : Finset I) (P : Matrix I I A), Fintype.card I - d ≤ S.card ∧
      (∀ i ∈ S, ∀ j ∈ S, P i j = if i = j then 1 else 0) ∧
      ∀ i l, ∑ j, (P i j : E) * w l j = 0 := by
  suffices ∃ (S : Finset I) (P : Matrix I I A), Fintype.card I - d ≤ S.card ∧
      (∀ i j, j ∈ S → P i j = if i = j then 1 else 0) ∧
      ∀ i l, ∑ j, (P i j : E) * w l j = 0 by
    obtain ⟨S, P, hS, hP, h⟩ := this
    exact ⟨S, P, hS, fun i _ => hP i, h⟩
  induction d with
  | zero => exact ⟨univ, 1, by simp, fun _ _ _ => rfl, fun _ l => Fin.elim0 l⟩
  | succ d ih =>
    -- 推导：从 `ih (fun l => w l.succ)` 中取出 `S, P, hS, hP, h`。
    obtain ⟨S, P, hS, hP, h⟩ := ih (fun l => w l.succ)
    let v i := ∑ j, (P i j : E) * w 0 j
    by_cases hz : ∀ i, v i = 0
    · exact ⟨S, P, by omega, hP, fun i => Fin.cases (hz i) (h i)⟩
    obtain ⟨k, hk⟩ := not_forall.mp hz
    obtain ⟨m, hm, hr⟩ := pivot A hA v hk
    let r (i : I) : A := ⟨v i / v m, hr i⟩
    let Q : Matrix I I A := fun i j => P i j - r i * P m j
    refine ⟨S.erase m, Q, ?_, ?_, ?_⟩
    · exact (Nat.sub_le_sub_right hS 1).trans pred_card_le_card_erase
    · intro i j hj
      -- 推导：从 `mem_erase.mp hj` 中取出 `hne, hj`。
      obtain ⟨hne, hj⟩ := mem_erase.mp hj
      simp only [Q, hP m j hj, ite_eq_right hne.symm, mul_zero, sub_zero, hP i j hj]
    · intro i l
      change ∑ j, ((P i j : E) - (v i / v m) * (P m j : E)) * w l j = 0
      simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]
      induction l using Fin.cases with
      | zero => exact sub_eq_zero.mpr (div_mul_cancel₀ (v i) hm).symm
      | succ l => rw [h i l, h m l, mul_zero, sub_zero]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 有限多个变元的公共零点的存在性与下降

**英文原文**

Existence and descent of common zeros in finitely many variables
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open MvPolynomial

-- 读法：存在 `x : I → K`，对每个 `p ∈ s`，`aeval x p` 等于 `0`。
theorem point_of_proper {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {I : Type*} [Finite I] (s : Set (MvPolynomial I k)) (h : Ideal.span s ≠ ⊤) :
    ∃ x : I → K, ∀ p ∈ s, aeval x p = 0 := by
  obtain ⟨J, hJ, hs⟩ := Ideal.exists_le_maximal (Ideal.span s) h
  obtain ⟨x, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hJ
  exact ⟨x, fun p hp => (mem_vanishingIdeal_singleton_iff x p).mp (hs (Ideal.subset_span hp))⟩

-- 读法：存在 `v : I → F`，对每个 `p ∈ s`，`eval v p` 等于 `0`。
theorem descend_point {F K : Type*} [Field F] [Field K] [IsAlgClosed F] [Algebra F K]
    {I : Type*} [Finite I] (s : Set (MvPolynomial I F)) (z : I → K)
    (h : ∀ p ∈ s, aeval z p = 0) :
    ∃ v : I → F, ∀ p ∈ s, eval v p = 0 := by
  have hz : z ∈ zeroLocus K (Ideal.span s) := by rw [zeroLocus_span]; exact h
  have hs : Ideal.span s ≠ ⊤ := by
    intro he
    rw [he, zeroLocus_top] at hz
    exact hz
  obtain ⟨v, hv⟩ := point_of_proper (K:=F) s hs
  exact ⟨v, hv⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 多项式投影的有限并中的一般参数

若一个方程组在一般参数上无解，局部化可产生一个非零多项式，在所有使该方程组有解的基域参数处取零值。有限多个这类障碍多项式的乘积不可能在整个参数空间上恒为零。

**英文原文**

Generic parameters in a finite union of polynomial projections

If a system has no solution over the generic parameters, localization
produces a nonzero polynomial vanishing on every ground-field parameter
where that system has a solution. The product of finitely many such
obstructions cannot vanish on the whole parameter space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical
variable {F K P J : Type*} [Field F] [Field K] [Algebra F K]

-- 读法：`curry` 的取值由 `eval₂Hom (C.comp C) (Sum.elim (C ∘ X) X)` 给出。
private def curry : MvPolynomial (P ⊕ J) F →+* MvPolynomial J (MvPolynomial P F) :=
  eval₂Hom (C.comp C) (Sum.elim (C ∘ X) X)

-- 读法：`eval₂ (aeval x).toRingHom y (curry p)` 等于 `aeval (Sum.elim x y) p`。这里调用 `ringHom_ext`。
private theorem curry_eval (x : P → K) (y : J → K) (p : MvPolynomial (P ⊕ J) F) :
    eval₂ (aeval x).toRingHom y (curry p) = aeval (Sum.elim x y) p := by
  have h : (eval₂Hom (aeval (R:=F) x).toRingHom y).comp curry = (aeval (Sum.elim x y)).toRingHom := by
    apply ringHom_ext
    · intro a; simp [curry]
    · rintro (i|i) <;> simp [curry]
  exact DFunLike.congr_fun h p

attribute [local instance] algebraMvPolynomial

-- 读法：存在 `y : J → K`，对每个 `p ∈ s`，`eval₂ f y p` 等于 `0`。这里调用 `IsLocalization.map_algebraMap_ne_top_iff_disjoint`。
private theorem solve_localized {R : Type*} [CommRing R] [IsDomain R] [IsAlgClosed K]
    [Finite J] (f : R →+* K) (hf : Function.Injective f) (s : Set (MvPolynomial J R))
    (h : ∀ a : R, C a ∈ Ideal.span s → a = 0) : ∃ y : J → K, ∀ p ∈ s, eval₂ f y p = 0 := by
  let L := FractionRing R
  let g : L →+* K := IsFractionRing.lift hf
  let _ : Algebra L K := g.toAlgebra
  have hg : (algebraMap L K).comp (algebraMap R L) = f :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf a
  have hs : Ideal.span (map (algebraMap R L) '' s) ≠ ⊤ := by
    rw [← Ideal.map_span, ← MvPolynomial.algebraMap_def]
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      ((nonZeroDivisors R).map (C (σ:=J))) (MvPolynomial J L) (Ideal.span s)).mpr
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hm
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (h a hm)
  obtain ⟨y, hy⟩ := point_of_proper (K:=K) _ hs
  refine ⟨y, fun p hp => ?_⟩
  simpa only [aeval_def, eval₂_map, hg] using hy _ ⟨p, hp, rfl⟩

-- 读法：存在 `q : MvPolynomial P F`，由 `q ≠ 0 ∧ ∀ (v : P → F) (y : J → F), (∀ p ∈ s, eval (Sum.elim v y) p = 0)` 推出 `eval v q = 0`。这里调用 `Ideal.span_le.mpr`。
private theorem obstruction [Finite J] [IsAlgClosed K] {x : P → K} (hx : AlgebraicIndependent F x)
    (s : Set (MvPolynomial (P ⊕ J) F)) (h : ¬ ∃ y : J → K, ∀ p ∈ s, aeval (Sum.elim x y) p = 0) :
    ∃ q : MvPolynomial P F, q ≠ 0 ∧ ∀ (v : P → F) (y : J → F),
      (∀ p ∈ s, eval (Sum.elim v y) p = 0) → eval v q = 0 := by
  have ex : ∃ q : MvPolynomial P F, C q ∈ Ideal.span (curry '' s) ∧ q ≠ 0 := by
    by_contra! hn
    obtain ⟨y, hy⟩ := solve_localized (aeval (R:=F) x).toRingHom hx (curry '' s) hn
    exact h ⟨y, fun p hp => (curry_eval x y p).symm.trans (hy _ ⟨p, hp, rfl⟩)⟩
  obtain ⟨q, hq, hn⟩ := ex
  refine ⟨q, hn, fun v y he => ?_⟩
  have hold : Ideal.span (curry '' s) ≤ RingHom.ker (eval₂Hom (aeval v).toRingHom y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact (curry_eval v y p).trans (he p hp)
  have hc : eval₂ (aeval v).toRingHom y (C q) = 0 := hold hq
  rw [eval₂_C] at hc
  exact hc

-- 读法：存在 `i`，存在 `w : J i → K`，对每个 `p ∈ S i`，`aeval (Sum.elim x w) p` 等于 `0`。这里调用 `MvPolynomial.funext`。
theorem generic_point [IsAlgClosed F] [IsAlgClosed K] {X A : Type*} [Fintype A]
    {x : X → K} (hx : AlgebraicIndependent F x) (J : A → Type*) [∀ i, Finite (J i)]
    (S : (i : A) → Set (MvPolynomial (X ⊕ J i) F))
    (h : ∀ v : X → F, ∃ i, ∃ w : J i → F, ∀ p ∈ S i, eval (Sum.elim v w) p = 0) :
    ∃ i, ∃ w : J i → K, ∀ p ∈ S i, aeval (Sum.elim x w) p = 0 := by
  by_contra hn
  have fails (i : A) : ¬ ∃ w : J i → K, ∀ p ∈ S i, aeval (Sum.elim x w) p = 0 :=
    fun a => hn ⟨i, a⟩
  choose q hq hzero using fun i => obstruction hx (S i) (fails i)
  have ne : ∏ i, q i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hq i
  apply ne
  apply MvPolynomial.funext
  intro v
  obtain ⟨i, w, hw⟩ := h v
  rw [map_zero, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i v w hw)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 代数形变的局部环

在正规化曲线的选定点处，剩余域就是常数域。形变参数是一个局部一致化参数的幂乘以单位元。本质有限生成性将给出导子的极点阶数的一致上界。

**英文原文**

The local ring of an algebraic deformation

At the selected point of a normalized curve the residue field is
the field of constants. The deformation parameter is a power of a
uniformizer times a unit. Essential finite generation will give
a uniform bound on the poles of a derivation.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

-- 读法：结构的字段包括 `ring`、`res`、`val`、`π`、`nonzero`。
structure Branch (K E : Type*) [Field K] [Field E] [Algebra K E] (t : E) where
  ring : Subalgebra K E
  res : ring →ₐ[K] K
  val : ∀ x : E, x ∈ ring ∨ x⁻¹ ∈ ring
  π : ring
  nonzero : (π : E) ≠ 0
  zero : res π = 0
  residue : ∀ x : ring, ∃ b : ring, (x : E) = algebraMap K E (res x) + (π : E) * b
  factor : ∃ e : ℕ, ∃ u : ringˣ, t = (π : E) ^ (e + 1) * (u.val : E)
  clear : ∀ x : E, ∃ m : ℕ, (π : E) ^ m * x ∈ ring
  generated : ∃ B : Subalgebra K E, B.FG ∧ B ≤ ring ∧
    ∀ x : ring, ∃ a b : B, (b : E)⁻¹ ∈ ring ∧ (x : E) = (a : E) / (b : E)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 固定点下方素理想链的长度

显式保留下方的素理想，以便在乘积环中拼接素理想链，再将它们映到商环。最后的上界自身未必属于这条链。

**英文原文**

Lengths of prime chains below a fixed point

Keep the lower prime explicit so that chains can be concatenated
in a product ring and mapped to a quotient. The final upper bound
need not itself be a member of the chain.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable {R S : Type*} [CommRing R] [CommRing S]

-- 读法：归纳构造子包括 `nil`、`cons`。
inductive Chain : Ideal R → Ideal R → ℕ → Prop
  | nil {p m} : p.IsPrime → p ≤ m → Chain p m 0
  | cons {p q m n} : p.IsPrime → p < q → Chain q m n → Chain p m (n + 1)

namespace Chain
variable {p q m : Ideal R} {n : ℕ}

-- 读法：要证明的命题是 `p.IsPrime`。
theorem prime (h : Chain p m n) : p.IsPrime := by cases h <;> assumption

-- 读法：`p` 不超过 `m`。对 `h` 作归纳。
theorem le (h : Chain p m n) : p ≤ m := by
  induction h with
  | nil _ e => exact e
  | cons _ h _ ih => exact h.le.trans ih

-- 读法：`p` 严格小于 `m`。对 `h` 分类讨论。
theorem lt (h : Chain p m (n + 1)) : p < m := by
  cases h with | cons _ h t => exact h.trans_le t.le

-- 读法：要证明的命题是 `Chain p m n`。对 `h` 作归纳。
theorem weaken (h : Chain p q n) (hm : q ≤ m) : Chain p m n := by
  induction h with
  | nil hp he => exact .nil hp (he.trans hm)
  | cons hp he _ ih => exact .cons hp he (ih hm)

-- 读法：要证明的命题是 `Chain p m n`。对 `h` 分类讨论。
theorem start (h : Chain q m n) (hp : p.IsPrime) (hsub : p ≤ q) : Chain p m n := by
  cases h with
  | nil _ he => exact .nil hp (hsub.trans he)
  | cons _ he h => exact .cons hp (hsub.trans_lt he) h

-- 读法：要证明的命题是 `Chain p m (k + n)`。对 `h` 作归纳。
theorem append {k : ℕ} (h : Chain p q n) (g : Chain q m k) : Chain p m (k + n) := by
  induction h with
  | nil hp he => exact g.start hp he
  | cons hp he _ ih => exact .cons hp he (ih g)

-- 读法：`p.height + n` 不超过 `m.height`。对 `h` 作归纳。
theorem bound (h : Chain p m n) : p.height + n ≤ m.height := by
  induction h with
  | nil _ e => simpa using Ideal.height_mono e
  | cons hp e h ih =>
    have := hp
    have := h.prime
    rw [Nat.cast_add, Nat.cast_one, add_comm _ 1, ← add_assoc]
    exact (add_le_add_left (Ideal.height_add_one_le_of_lt_of_isPrime e) _).trans ih

-- 读法：`(n : ℕ∞)` 不超过 `m.height`。使用 `le_add_self.trans` 给出的结论。
theorem length_le (h : Chain p m n) : (n : ℕ∞) ≤ m.height := le_add_self.trans h.bound

-- 读法：要证明的命题是 `Chain (f p) (f m) n`。对 `h` 作归纳。
theorem transport (f : Ideal R → Ideal S) (hf : Monotone f)
    (hp : ∀ i, i.IsPrime → (f i).IsPrime)
    (he : ∀ i j, i.IsPrime → j.IsPrime → f i = f j → i = j)
    (h : Chain p m n) : Chain (f p) (f m) n := by
  induction h with
  | nil e hm => exact .nil (hp _ e) (hf hm)
  | cons e hi g ih =>
    exact .cons (hp _ e) (lt_of_le_of_ne (hf hi.le) (fun hu => hi.ne (he _ _ e g.prime hu))) ih

variable {I : Ideal R}

-- 读法：要证明的命题是 `Chain (p.map (Ideal.Quotient.mk I)) (m.map (Ideal.Quotient.mk I)) n`。这里调用 `Ideal.map_isPrime_of_surjective`。
private theorem quotient (h : Chain p m n) (hi : I ≤ p) :
    Chain (p.map (Ideal.Quotient.mk I)) (m.map (Ideal.Quotient.mk I)) n := by
  let f := Ideal.Quotient.mk I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hp (j : Ideal R) (h : j.IsPrime) (e : I ≤ j) : (j.map f).IsPrime := by
    have := h
    exact Ideal.map_isPrime_of_surjective hf (I.mk_ker.trans_le e)
  have he (j : Ideal R) (e : I ≤ j) : (j.map f).comap f = j := by
    rw [Ideal.comap_map_of_surjective' _ hf, I.mk_ker, sup_eq_left.mpr e]
  induction h with
  | nil h e => exact .nil (hp _ h hi) (Ideal.map_mono e)
  | cons h e _ ih =>
    refine .cons (hp _ h hi) (lt_of_le_of_ne (Ideal.map_mono e.le) ?_) (ih (hi.trans e.le))
    intro eq
    exact e.ne ((he _ hi).symm.trans ((congrArg (Ideal.comap f) eq).trans (he _ (hi.trans e.le))))

-- 读法：`n` 不超过 `Fintype.card σ`。
theorem equations [IsNoetherianRing R] {σ : Type} [Fintype σ] (y : σ → R)
    (hm : m ∈ (I ⊔ Ideal.span (Set.range y)).minimalPrimes) (h : Chain p m n) (hi : I ≤ p) :
    n ≤ Fintype.card σ := by
  classical
  let f := Ideal.Quotient.mk I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  let s := Finset.univ.image (f ∘ y)
  have he : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range y)).map f := by
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp, Ideal.map_span]
  have hk : m.map f ∈ (Ideal.span (s : Set (R ⧸ I))).minimalPrimes := by
    rw [he, Ideal.minimalPrimes_map_of_surjective hf, I.mk_ker, sup_comm]
    exact ⟨m, hm, rfl⟩
  have hb := (h.quotient hi).length_le.trans (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hk)
  exact (ENat.natCast_le_natCast.mp hb).trans Finset.card_image_le

end Chain
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 正规化曲线上的求导与特殊化可交换

固定形变参数的导子在局部环上具有一致的极点上界。对分歧关系求导，使局部一致化参数的极点上界改善一阶。再从每个元素中减去其剩余类的代表值，便可改进整个环上的界。

**英文原文**

Derivatives on a normalized curve commute with specialization

A derivation fixing the deformation parameter has a uniform pole
bound on the local ring. Differentiating the ramification relation
improves the bound on the uniformizer by one. Subtracting each
element's residue then improves the bound on the whole ring.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Branch

variable {F K E : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
  [Algebra K E] {t : E} (b : Branch K E t) (D : Derivation F E E)
  (d : Derivation F K K) (he : ∀ x, D (algebraMap K E x) = algebraMap K E (d x))

-- 读法：`bounded` 的取值由 `∀ x ∈ b.ring, (b.π : E) ^ m * D x ∈ b.ring` 给出。
def bounded (m : ℕ) := ∀ x ∈ b.ring, (b.π : E) ^ m * D x ∈ b.ring

include he in
-- 读法：存在 `m`，要证明的命题是 `b.bounded D m`。对 `hx` 作归纳，采用 `Algebra.adjoin_induction` 的归纳原则。
theorem pole_bound : ∃ m, b.bounded D m := by
  classical
  obtain ⟨B, ⟨s, rfl⟩, hB, hfrac⟩ := b.generated
  choose l hl using fun x : E => b.clear (D x)
  let m := s.sup l
  let c := (b.π : E) ^ m
  have hc : c ∈ b.ring := b.ring.pow_mem b.π.property _
  have ha {x : E} (hx : x ∈ Algebra.adjoin K (↑s : Set E)) : c * D x ∈ b.ring := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      -- 推导：从 `Nat.exists_eq_add_of_le (Finset.le_sup (f := l) hx)` 中取出 `k, hk`。
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := l) hx)
      change (b.π : E) ^ m * D x ∈ b.ring
      rw [show m = l x + k from hk, add_comm, pow_add, mul_assoc]
      exact b.ring.mul_mem (b.ring.pow_mem b.π.property _) (hl x)
    | algebraMap x => rw [he]; exact b.ring.mul_mem hc (b.ring.algebraMap_mem _)
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact b.ring.add_mem hx hy
    | mul x y hx hy ex ey =>
      rw [D.leibniz, smul_eq_mul, smul_eq_mul, mul_add, mul_left_comm c x, mul_left_comm c y]
      exact b.ring.add_mem (b.ring.mul_mem (hB hx) ey) (b.ring.mul_mem (hB hy) ex)
  refine ⟨m, fun x hx => ?_⟩
  -- 推导：从 `hfrac ⟨x, hx⟩` 中取出 `p, q, hi, hr`。
  obtain ⟨p, q, hi, hr⟩ := hfrac ⟨x, hx⟩
  change x = (p : E) / (q : E) at hr
  change c * D x ∈ b.ring
  rw [hr, D.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_left_comm c, mul_sub,
    mul_left_comm c (q : E), mul_left_comm c (p : E)]
  exact b.ring.mul_mem (b.ring.pow_mem hi _) (b.ring.sub_mem
    (b.ring.mul_mem (hB q.property) (ha p.property)) (b.ring.mul_mem (hB p.property) (ha q.property)))

variable [CharZero K] (ht : D t = 0)

omit [Algebra F K] in
include ht in
-- 读法：存在 `c x : b.ring`，`D (b.π : E)` 等于 `(b.π : E) * c * D (x : E)`。这里调用 `mul_eq_zero.mp`。
private theorem uniformizer : ∃ c x : b.ring, D (b.π : E) = (b.π : E) * c * D (x : E) := by
  obtain ⟨e, u, hu⟩ := b.factor
  let v : E := u.val
  let q : E := b.π
  have hh : D (q ^ (e + 1) * v) = 0 := by rw [← hu]; exact ht
  rw [D.leibniz, D.leibniz_pow] at hh
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ] at hh
  have hv : q * D v + (↑(e + 1) : E) * v * D q = 0 := by
    apply (mul_eq_zero.mp (show q ^ e * (q * D v + (↑(e + 1) : E) * v * D q) = 0 from ?_)).resolve_left
      (pow_ne_zero _ b.nonzero)
    calc
      _ = q ^ e * q * D v + v * ((↑(e + 1) : E) * (q ^ e * D q)) := by ring
      _ = _ := hh
  let k := ((↑(e + 1) : K))⁻¹
  let c : b.ring := -(algebraMap K b.ring k) * (u⁻¹).val
  -- 推导：记下中间结论 `eqn`：`(c : E) * ((↑(e + 1) : E) * v) = -1`。
  have eqn : (c : E) * ((↑(e + 1) : E) * v) = -1 := by
    have hk : k * (↑(e + 1) : K) = 1 := inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero e)
    have hu' : ((u⁻¹).val : E) * v = 1 := congrArg Subtype.val (Units.inv_mul u)
    calc
      _ = -(algebraMap K E k * (↑(e + 1) : E)) * (((u⁻¹).val : E) * v) := by
        change (-(algebraMap K E k) * _) * _ = _
        ring
      _ = -1 := by rw [← map_natCast (algebraMap K E), ← map_mul, hk, map_one, hu', mul_one]
  refine ⟨c, u.val, ?_⟩
  change D q = q * (c : E) * D v
  calc
    _ = -((c : E) * ((↑(e + 1) : E) * v)) * D q := by rw [eqn, neg_neg, one_mul]
    _ = (c : E) * (-((↑(e + 1) : E) * v * D q)) := by ring
    _ = _ := by rw [neg_eq_of_add_eq_zero_left hv]; ring

include he ht in
-- 读法：`D (a : E)` 属于 `b.ring`。
theorem regular (a : b.ring) : D (a : E) ∈ b.ring := by
  obtain ⟨c, x, hu⟩ := b.uniformizer D ht
  have step (m : ℕ) (h : b.bounded D (m + 1)) : b.bounded D m := by
    intro y hy
    obtain ⟨z, hz⟩ := b.residue ⟨y, hy⟩
    let s := b.res ⟨y, hy⟩
    change y = algebraMap K E s + (b.π : E) * z at hz
    rw [hz, map_add, he, D.leibniz, smul_eq_mul, smul_eq_mul, hu]
    rw [show (b.π : E) ^ m * (algebraMap K E (d s) + ((b.π : E) * D (z : E) + (z : E) * ((b.π : E) * c * D (x : E)))) =
      (b.π : E) ^ m * algebraMap K E (d s) + ((b.π : E) ^ (m + 1) * D (z : E) + (z : E) * c * ((b.π : E) ^ (m + 1) * D (x : E))) by ring]
    exact b.ring.add_mem (b.ring.mul_mem (b.ring.pow_mem b.π.property _) (b.ring.algebraMap_mem _))
      (b.ring.add_mem (h _ z.property) (b.ring.mul_mem (b.ring.mul_mem z.property c.property) (h _ x.property)))
  obtain ⟨m, hm⟩ := b.pole_bound D d he
  induction m with
  | zero => simpa using hm _ a.property
  | succ m ih => exact ih (step m hm)

-- 读法：`lift` 的取值由 `⟨D (a : E), b.regular D d he ht a⟩` 给出。
def lift (a : b.ring) : b.ring := ⟨D (a : E), b.regular D d he ht a⟩

-- 读法：`b.res (b.lift D d he ht a)` 等于 `d (b.res a)`。按 `Subtype.ext` 的外延性准则比较各分量。
theorem specialize (a : b.ring) : b.res (b.lift D d he ht a) = d (b.res a) := by
  obtain ⟨c, x, hu⟩ := b.uniformizer D ht
  obtain ⟨z, hz⟩ := b.residue a
  let g := b.lift D d he ht
  have h : g a = algebraMap K b.ring (d (b.res a)) + b.π * (g z + z * c * g x) := by
    apply Subtype.ext
    change D (a : E) = algebraMap K E _ + (b.π : E) * (D (z : E) + (z : E) * c * D (x : E))
    conv_lhs => rw [hz, map_add, he, D.leibniz, smul_eq_mul, smul_eq_mul, hu]
    ring
  change b.res (g a) = _
  rw [h, map_add, b.res.commutes, map_mul, b.zero, zero_mul, add_zero]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Branch
end

section
/-!
# 将导子解释为到对偶数的映射

第一个坐标记录域嵌入，第二个坐标记录导子。

**英文原文**

Derivations as maps to dual numbers

The first coordinate records the field embedding and the second records the derivation.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable {F K E : Type u} [Field F] [Field K] [Field E]

-- 读法：用字段 `toFun`、`map_one'`、`map_zero'`、`map_add'` 构造 `K →+* TrivSqZeroExt E E`。
def prolong [Algebra F K] [Algebra K E] (D : Derivation F K K) :
    K →+* TrivSqZeroExt E E where
  toFun x := (algebraMap K E x, algebraMap K E (D x))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by
    simp only [map_add]
    rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap K E) x y
    · change algebraMap K E (D (x * y)) =
        algebraMap K E x * algebraMap K E (D y) + algebraMap K E (D x) * algebraMap K E y
      simp [Derivation.leibniz, smul_eq_mul, mul_comm]

-- 读法：用字段 `toFun`、`map_add'`、`map_smul'`、`map_one_eq_zero'` 构造 `Derivation F E E`。
def extract [Algebra F E] (f : E →+* TrivSqZeroExt E E) (fst : ∀ x, (f x).fst = x)
    (zero : ∀ a : F, (f (algebraMap F E a)).snd = 0) : Derivation F E E where
  toFun x := (f x).snd
  map_add' x y := by simp
  map_smul' c x := by simp [Algebra.smul_def, TrivSqZeroExt.snd_mul, fst, zero]
  map_one_eq_zero' := by change (f 1).snd = 0; simp
  leibniz' x y := by
    change (f (x * y)).snd = x • (f y).snd + y • (f x).snd
    simp [TrivSqZeroExt.snd_mul, fst, smul_eq_mul, mul_comm]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 拼接独立块中的素理想链

**英文原文**

Concatenating chains of primes in independent blocks
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Chain
open Finset
open scoped Classical

variable {J : Type} [Fintype J] {R : J → Type*} [∀ j, CommRing (R j)] {S : Type*} [CommRing S]

-- 读法：要证明的命题是 `Chain (D P) (D Q) (Fintype.card J * n)`。
theorem product (D : (∀ j, Ideal (R j)) → Ideal S) (hm : Monotone D)
    (hp : ∀ I, (∀ j, (I j).IsPrime) → (D I).IsPrime)
    (he : ∀ I I', (∀ j, (I j).IsPrime) → (∀ j, (I' j).IsPrime) → D I = D I' → I = I')
    {P Q : ∀ j, Ideal (R j)} (hq : ∀ j, (Q j).IsPrime) {n : ℕ} (h : ∀ j, Chain (P j) (Q j) n) :
    Chain (D P) (D Q) (Fintype.card J * n) := by
  let g (s : Finset J) j := if j ∈ s then Q j else P j
  have hg (s : Finset J) (j : J) : (g s j).IsPrime := by
    unfold g
    split
    · exact hq j
    · exact (h j).prime
  have step (s : Finset J) (j : J) (hj : j ∉ s) : Chain (D (g s)) (D (g (insert j s))) n := by
    let f (P : Ideal (R j)) := Function.update (g s) j P
    have hf (a : Ideal (R j)) (ha : a.IsPrime) (k : J) : (f a k).IsPrime := by
      by_cases e : k = j
      · subst k; simpa [f] using ha
      · simpa [f, e] using hg s k
    have hmono : Monotone f := by
      intro a b hab k
      by_cases e : k = j
      · subst k; simpa [f] using hab
      · simp [f, e]
    -- 推导：记下中间结论 `hleft`：`f (P j) = g s`。
    have hleft : f (P j) = g s := by
      funext k
      by_cases e : k = j
      · subst k; simp [f, g, hj]
      · simp [f, e]
    have hright : f (Q j) = g (insert j s) := by
      funext k
      by_cases e : k = j
      · subst k; simp [f, g]
      · simp [f, g, e]
    rw [← hleft, ← hright]
    apply (h j).transport (D ∘ f) (hm.comp hmono) (fun a ha => hp _ (hf a ha))
    intro a b ha hb heq
    simpa only [f, Function.update_self] using congrFun (he _ _ (hf a ha) (hf b hb) heq) j
  have aux (s : Finset J) : Chain (D (g ∅)) (D (g s)) (s.card * n) := by
    induction s using Finset.induction with
    | empty => rw [card_empty, zero_mul]; exact .nil (hp _ (hg _)) le_rfl
    | @insert j s hj ih =>
      rw [card_insert_of_notMem hj, Nat.succ_mul, add_comm]
      exact ih.append (step s j hj)
  simpa [g] using aux univ

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Chain
end

/-!
# 将独立元素上的取值提升到对偶数

零特征域在任一子域上形式光滑。它在代数独立元生成的多项式子代数上也形式光滑，因为转到分式域是局部化。因此可以同时规定生成元和系数域上的一阶增量。

**英文原文**

Lifting values on independent elements to dual numbers

A field of characteristic zero is formally smooth over any subfield.
It is also formally smooth over the polynomial subalgebra generated
by independent elements, since passing to its fraction field is a
localization. Consequently we can specify first-order increments
on the generators and on the coefficient field simultaneously.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
-- 读法：要证明的命题是 `Algebra.FormallySmooth K E`。这里调用 `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`。
private theorem smooth (K E : Type u) [Field K] [Field E] [Algebra K E] [CharZero E] :
    Algebra.FormallySmooth K E := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K E
  have := hx.isAlgebraic_field
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hx.1

-- 读法：存在 `f : E →+* TrivSqZeroExt E E`，`(∀ a, (f a).fst = a)` 与 `∀ a : A, f (algebraMap A E a) = q a` 同时成立。
private theorem section_of_smooth {A E : Type u} [CommRing A] [Field E] [Algebra A E]
    [Algebra.FormallySmooth A E] (q : A →+* TrivSqZeroExt E E)
    (hq : ∀ a, (q a).fst = algebraMap A E a) :
    ∃ f : E →+* TrivSqZeroExt E E, (∀ a, (f a).fst = a) ∧
      ∀ a : A, f (algebraMap A E a) = q a := by
  let : Algebra A (TrivSqZeroExt E E) := q.toAlgebra
  let π : TrivSqZeroExt E E →ₐ[A] E :=
    { (TrivSqZeroExt.fstHom E E E).toRingHom with commutes' := hq }
  have ep : Function.Surjective π := fun x => ⟨(x, 0), rfl⟩
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, TrivSqZeroExt.kerIdeal_sq E E⟩
  let f := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A E) π ep hn
  exact ⟨f.toRingHom, Algebra.FormallySmooth.liftOfSurjective_apply _ π ep hn, f.commutes⟩

open scoped IntermediateField.algebraAdjoinAdjoin in
-- 读法：存在 `f : E →+* TrivSqZeroExt E E`，`(∀ a, (f a).fst = a)` 与 `(∀ a : K, f (algebraMap K E a) = d a) ∧ ∀ i, (f (x i)).snd = v i` 同时成立。
theorem lift_independent {K E : Type u} [Field K] [Field E] [Algebra K E] [CharZero E]
    {ι : Type w} {x : ι → E} (hx : AlgebraicIndependent K x) (v : ι → E)
    (d : K →+* TrivSqZeroExt E E) (hd : ∀ a, (d a).fst = algebraMap K E a) :
    ∃ f : E →+* TrivSqZeroExt E E, (∀ a, (f a).fst = a) ∧
      (∀ a : K, f (algebraMap K E a) = d a) ∧ ∀ i, (f (x i)).snd = v i := by
  let A := Algebra.adjoin K (Set.range x)
  let L := IntermediateField.adjoin K (Set.range x)
  have : Algebra.FormallySmooth A L := .of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallySmooth L E := smooth L E
  have : Algebra.FormallySmooth A E := .comp A L E
  -- 推导：记下中间结论 `y`：`ι → TrivSqZeroExt E E`。
  let y : ι → TrivSqZeroExt E E := fun i => (x i, v i)
  let φ := MvPolynomial.eval₂Hom d y
  have hC (r : K) : φ (MvPolynomial.C r) = d r := MvPolynomial.eval₂Hom_C d y r
  have hX (i : ι) : φ (MvPolynomial.X i) = y i := MvPolynomial.eval₂Hom_X' d y i
  let π := (TrivSqZeroExt.fstHom E E E).toRingHom
  have hh : π.comp φ = (MvPolynomial.aeval x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hC, π] using hd a
    · intro i
      simp [hX, π, y]
      rfl
  let q : A →+* TrivSqZeroExt E E := φ.comp hx.aevalEquiv.symm.toRingHom
  have eval (p : MvPolynomial ι K) : q (hx.aevalEquiv p) = φ p := by
    change φ (hx.aevalEquiv.symm (hx.aevalEquiv p)) = _
    rw [AlgEquiv.symm_apply_apply]
  have hq (a : A) : (q a).fst = algebraMap A E a := by
    -- 推导：从 `hx.aevalEquiv.surjective a` 中取出 `p, rfl`。
    obtain ⟨p, rfl⟩ := hx.aevalEquiv.surjective a
    rw [eval, hx.algebraMap_aevalEquiv]
    exact DFunLike.congr_fun hh p
  obtain ⟨f, hf, hf'⟩ := section_of_smooth q hq
  have hp (p : MvPolynomial ι K) : f (MvPolynomial.aeval x p) = φ p := by
    rw [← hx.algebraMap_aevalEquiv, hf', eval]
  refine ⟨f, hf, ?_, ?_⟩
  · intro a
    simpa [hC] using hp (MvPolynomial.C a)
  · intro i
    simpa [hX, y] using congrArg TrivSqZeroExt.snd (hp (MvPolynomial.X i))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 域扩张中的独立坐标与导子

**英文原文**

Independent coordinates and derivations of field extensions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
variable {F K E : Type u} [Field F] [Field K] [Field E] [Algebra K E] [CharZero E]

-- 读法：存在 `D' : Derivation F E E`，`(∀ a, D' (algebraMap K E a) = algebraMap K E (D a))` 与 `∀ i, D' (x i) = v i` 同时成立。
/-- 在系数域上任给一个导子，并在其上规定增量。

英文原文：Prescribe increments over an arbitrary derivation on the coefficient field.
-/
theorem extend_derivation [Algebra F K] [Algebra F E] [IsScalarTower F K E]
    {ι : Type w} {x : ι → E} (h : AlgebraicIndependent K x) (D : Derivation F K K) (v : ι → E) :
    ∃ D' : Derivation F E E, (∀ a, D' (algebraMap K E a) = algebraMap K E (D a)) ∧
      ∀ i, D' (x i) = v i := by
  obtain ⟨f, hf, hc, hi⟩ := lift_independent h v (prolong D) (fun _ => rfl)
  have extend (x : K) : (f (algebraMap K E x)).snd = algebraMap K E (D x) := by rw [hc]; rfl
  have hz (a : F) : (f (algebraMap F E a)).snd = 0 := by
    rw [IsScalarTower.algebraMap_apply F K E, extend, D.map_algebraMap, map_zero]
  exact ⟨extract f hf hz, extend, hi⟩

-- 读法：存在 `D : Derivation K E E`，对每个 `i`，`D (x i)` 等于 `v i`。
/-- 一个代数独立族的无穷小增量可以任意指定。

英文原文：The infinitesimal increments of an independent family may be prescribed arbitrarily.
-/
theorem derivation_of_independent {ι : Type w} {x : ι → E}
    (hx : AlgebraicIndependent K x) (v : ι → E) :
    ∃ D : Derivation K E E, ∀ i, D (x i) = v i := by
  obtain ⟨D, _, h⟩ := extend_derivation hx (0 : Derivation K K K) v
  exact ⟨D, h⟩

-- 读法：存在 `D' : Derivation F E E`，`(∀ x, D' (algebraMap K E x) = algebraMap K E (D x))` 与 `D' t = 0` 同时成立。
/-- 把系数域的导子延拓，并令某个超越元的导数为零。

英文原文：Extend a derivation of the coefficient field, holding a transcendental element fixed.
-/
theorem exists_derivation_extension [Algebra F K] [Algebra F E] [IsScalarTower F K E]
    {t : E} (ht : Transcendental K t) (D : Derivation F K K) :
    ∃ D' : Derivation F E E,
      (∀ x, D' (algebraMap K E x) = algebraMap K E (D x)) ∧ D' t = 0 := by
  have h : AlgebraicIndependent K (fun _ : Unit => t) := algebraicIndependent_unique_type_iff.mpr ht
  obtain ⟨D', he, hzero⟩ := extend_derivation h D (fun _ => 0)
  exact ⟨D', he, hzero ()⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 含有新独立坐标的代数闭扩域

**英文原文**

An algebraically closed extension with new independent coordinates
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
-- 读法：在后续公式中，`Free` 是 `AlgebraicClosure (FractionRing (MvPolynomial σ K))` 的缩写。
abbrev Free (K : Type u) [Field K] (σ : Type) := AlgebraicClosure (FractionRing (MvPolynomial σ K))

namespace Free

variable (K : Type u) [Field K] (σ : Type)

-- 读法：在后续公式中，`P` 是 `MvPolynomial σ K` 的缩写。
private abbrev P := MvPolynomial σ K
-- 读法：在后续公式中，`R` 是 `FractionRing (P K σ)` 的缩写。
private abbrev R := FractionRing (P K σ)

-- 读法：`point` 的取值由 `algebraMap (R K σ) (Free K σ) (algebraMap (P K σ) (R K σ) (MvPolynomial.X i))` 给出。
def point (i : σ) : Free K σ :=
  algebraMap (R K σ) (Free K σ) (algebraMap (P K σ) (R K σ) (MvPolynomial.X i))

-- 读法：要证明的命题是 `AlgebraicIndependent K (fun i => algebraMap A B (x i))`。使用 `h.map'` 给出的结论。
private theorem injective_map {A B : Type u} [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] {x : σ → A}
    (h : AlgebraicIndependent K x) (hf : Function.Injective (algebraMap A B)) :
    AlgebraicIndependent K (fun i => algebraMap A B (x i)) :=
  h.map' (f := IsScalarTower.toAlgHom K A B) hf

-- 读法：要证明的命题是 `AlgebraicIndependent K (point K σ)`。这里调用 `injective_map`。
theorem independent : AlgebraicIndependent K (point K σ) := by
  have hr := injective_map K σ (MvPolynomial.algebraicIndependent_X σ K)
    (IsFractionRing.injective (P K σ) (R K σ))
  exact injective_map K σ hr (algebraMap (R K σ) (Free K σ)).injective

variable {K} {F : Type u} [Field F] [Algebra F K] [CharZero K]

-- 读法：存在 `D' : Derivation F (Free K σ) (Free K σ)`，`(∀ a, D' (algebraMap K (Free K σ) a) = algebraMap K (Free K σ) (D a))` 与 `∀ i, D' (point K σ i) = 0` 同时成立。使用 `extend_derivation` 给出的结论。
theorem derivation (D : Derivation F K K) :
    ∃ D' : Derivation F (Free K σ) (Free K σ),
      (∀ a, D' (algebraMap K (Free K σ) a) = algebraMap K (Free K σ) (D a)) ∧
      ∀ i, D' (point K σ i) = 0 :=
  extend_derivation (independent K σ) D (fun _ => 0)

end Free
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 各坐标像代数独立时该点处的雅可比矩阵

任意指定像的导数后，将它们延拓为整个域上的导子。多项式的链式法则将所指定的导数向量写为雅可比矩阵乘以各坐标的导数向量。

**英文原文**

The Jacobian at a point with algebraically independent images

Given arbitrary derivatives of the images, extend to a derivation of the field.
The polynomial chain rule writes the prescribed derivatives as the Jacobian
times the derivatives of the coordinates.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {ι : Type}

-- 读法：`D (aeval a p)` 等于 `∑ j, aeval a (pderiv j p) * D (a j)`。对 `p` 作归纳，采用 `MvPolynomial.induction_on` 的归纳原则。
theorem derivation_aeval [Fintype ι] (D : Derivation F K K) (a : ι → K)
    (p : MvPolynomial ι F) :
    D (aeval a p) = ∑ j, aeval a (pderiv j p) * D (a j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, map_add, hp,
      add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Pi.single_apply, apply_ite]

-- 读法：输入 `i j` 时返回 `aeval a (pderiv j (G i))`。
noncomputable def jacobian (G : ι → MvPolynomial ι F) (a : ι → K) : Matrix ι ι K :=
  fun i j => aeval a (pderiv j (G i))

-- 读法：要证明的命题是 `IsUnit (jacobian G a)`。这里调用 `Matrix.mulVec_surjective_iff_isUnit.mp`。
theorem isUnit_jacobian [CharZero K] [Fintype ι] [DecidableEq ι]
    (G : ι → MvPolynomial ι F) (a : ι → K)
    (ha : AlgebraicIndependent F (fun i => aeval a (G i))) :
    IsUnit (jacobian G a) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro v
  obtain ⟨D, hD⟩ := derivation_of_independent ha v
  refine ⟨fun j => D (a j), funext fun i => ?_⟩
  exact (derivation_aeval D a (G i)).symm.trans (hD i)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 在参数上作正规化

参数代数在函数域中的整闭包是 Dedekind 环。它包含在原仿射代数的整闭包中，因此位于原代数上方的点可限制为此模型上的点。

**英文原文**

Normalization over the parameter

The integral closure of the parameter algebra in the function field is Dedekind.
It is contained in the integral closure of the original affine algebra, so
points above the original algebra restrict to points on this model.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped IntermediateField.algebraAdjoinAdjoin

-- 读法：存在 `B : Subalgebra K E`，`B.FG` 与 `B ≤ (integralClosure R E).restrictScalars K ∧ (t : E) ∈ B ∧ IsFractionRing B E ∧ IsDedekindDomain B` 同时成立。这里调用 `IsPrincipalIdealRing.of_surjective`。
theorem curve {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K]
    (R : Subalgebra K E) [IsFractionRing R E] (fg : R.FG) (t : R)
    (alg : Algebra.IsAlgebraic (IntermediateField.adjoin K {(t : E)}) E) :
    ∃ B : Subalgebra K E, B.FG ∧ B ≤ (integralClosure R E).restrictScalars K ∧
      (t : E) ∈ B ∧ IsFractionRing B E ∧ IsDedekindDomain B := by
  classical
  let A := Algebra.adjoin K {(t : E)}
  let F := IntermediateField.adjoin K {(t : E)}
  have : IsPrincipalIdealRing A := by
    unfold A
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    -- 推导：记下中间结论 `f`：`= Polynomial.aeval (R`。
    let f := Polynomial.aeval (R := K) (t : E)
    exact IsPrincipalIdealRing.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Algebra.FiniteType K R := R.fg_iff_finiteType.mp fg
  have : Algebra.EssFiniteType R E := .of_isLocalization E (nonZeroDivisors R)
  have : Algebra.EssFiniteType K E := .comp K R E
  have : Algebra.EssFiniteType F E := .of_comp K F E
  have : Algebra.IsAlgebraic F E := alg
  have : Module.Finite F E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let C := integralClosure A E
  have : Module.Finite A C := IsIntegralClosure.finite A F E C
  have ft : Algebra.FiniteType K C :=
    (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton (t : E))).trans
      (inferInstance : Algebra.FiniteType A C)
  refine ⟨C.restrictScalars K, (Subalgebra.fg_iff_finiteType _).mpr ft, ?_, ?_,
    IsIntegralClosure.isFractionRing_of_finite_extension A F E C,
    integralClosure.isDedekindDomain A F E⟩
  -- 推导：记下中间结论 `h`：`A ≤ R`。
  · have h : A ≤ R := Algebra.adjoin_le (Set.singleton_subset_iff.mpr t.property)
    let _ := (Subalgebra.inclusion h).toAlgebra
    have : IsScalarTower A R E := Subalgebra.inclusion.isScalarTower_right h E
    exact fun x hx => (show IsIntegral A x from hx).tower_top
  · exact isIntegral_algebraMap (R := A) (A := E)
      (x := ⟨(t : E), Algebra.self_mem_adjoin_singleton K (t : E)⟩)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 离散赋值环的分支参数

**英文原文**

The branch parameters of a discrete valuation ring
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open IsDiscreteValuationRing

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
    (O : Subalgebra K E) [IsFractionRing O E] [IsDiscreteValuationRing O]

-- 读法：`x ∈ O`、`x⁻¹ ∈ O` 至少有一项成立。这里调用 `Or.inl`。
theorem mem_or_inv (x : E) : x ∈ O ∨ x⁻¹ ∈ O := by
  rcases ValuationRing.isInteger_or_isInteger O x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl (hy ▸ y.property)
  · exact Or.inr (hy ▸ y.property)

-- 读法：存在 `m : ℕ`，`(π : E) ^ m * x` 属于 `O`。
private theorem clear_denominator (π : O) (hirr : Irreducible π) (x : E) :
    ∃ m : ℕ, (π : E) ^ m * x ∈ O := by
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective O x
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hb' hirr
  have hf : π ^ m = (u⁻¹ : Oˣ).val * b := by rw [hu]; simp
  have ht : (π : E) ^ m = ((u⁻¹ : Oˣ).val : E) * (b : E) := congrArg Subtype.val hf
  refine ⟨m, ?_⟩
  change (a : E) / (b : E) = x at he
  rw [ht, ← he, mul_assoc, mul_div_cancel₀ _ (show (b : E) ≠ 0 by simpa)]
  exact O.mul_mem (u⁻¹ : Oˣ).val.property a.property

-- 读法：`discreteBranch` 的结果类型为 `Branch K E (t : E)`。
def discreteBranch (φ : O →ₐ[K] K) (t : O) (hne : t ≠ 0) (hz : φ t = 0)
    (gen : ∃ B : Subalgebra K E, B.FG ∧ B ≤ O ∧
      ∀ x : O, ∃ a b : B, (b : E)⁻¹ ∈ O ∧ (x : E) = (a : E) / (b : E)) : Branch K E (t : E) := by
  let π := (exists_irreducible O).choose
  have hirr : Irreducible π := (exists_irreducible O).choose_spec
  have hker : RingHom.ker φ = Ideal.span {π} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ
      (fun x => ⟨algebraMap K O x, by simp⟩))).trans ((irreducible_iff_uniformizer π).mp hirr)
  refine ⟨O, φ, mem_or_inv O, π, by simpa using hirr.ne_zero, ?_, ?_, ?_, clear_denominator O π hirr, gen⟩
  · change π ∈ RingHom.ker φ
    rw [hker, Ideal.mem_span_singleton]
  · intro x
    have hx : x - algebraMap K O (φ x) ∈ RingHom.ker φ := by simp
    rw [hker, Ideal.mem_span_singleton] at hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨b, congrArg Subtype.val (sub_eq_iff_eq_add'.mp hb)⟩
  · obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hne hirr
    cases m with
    | zero =>
      have ht : IsUnit t := by rw [hu, pow_zero, mul_one]; exact u.isUnit
      exact ((ht.map φ).ne_zero hz).elim
    | succ m =>
      rw [mul_comm] at hu
      exact ⟨m, u, congrArg Subtype.val hu⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
