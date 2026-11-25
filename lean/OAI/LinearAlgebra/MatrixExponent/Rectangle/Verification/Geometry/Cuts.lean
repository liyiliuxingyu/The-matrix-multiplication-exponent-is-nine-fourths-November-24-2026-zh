-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Jacobian
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nullstellensatz

universe u

/-!
# 对正规化的仿射参数直线作局部化

较大子环上的一个点选定正规化上的素理想。若较大环中某元素的逆属于局部化，将分母清除并在该点求值，可知对应分子在那里也是可逆元。

**英文原文**

Localizing a normalized affine parameter line

A point of a larger subring selects the prime on the normalization.
If the inverse of an element of the larger ring belongs to the
localization, clearing its denominator and evaluating at the point
shows that its numerator is also invertible there.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (B D : Subalgebra K E) [IsFractionRing B E] [IsDedekindDomain B]

-- 读法：存在 `b : Branch K E (t : E)`，存在 `l : D ≤ b.ring`，对每个 `x : D`，`b.res ⟨x.val, l x.property⟩` 等于 `δ x`。
theorem local_branch (fg : B.FG) (h : B ≤ D) (δ : D →ₐ[K] K)
    (t : B) (hne : t ≠ 0) (hz : δ (Subalgebra.inclusion h t) = 0) :
    ∃ b : Branch K E (t : E), ∃ l : D ≤ b.ring, ∀ x : D, b.res ⟨x.val, l x.property⟩ = δ x := by
  let f := Subalgebra.inclusion h
  let ψ := δ.comp f
  let P := RingHom.ker ψ
  have : P.IsPrime := RingHom.ker_isPrime _
  have hP : P ≠ ⊥ := by
    intro hh
    have ht : t ∈ P := hz
    rw [hh] at ht
    exact hne ht
  let A := Localization.subalgebra.ofField E P.primeCompl P.primeCompl_le_nonZeroDivisors
  let O := A.restrictScalars K
  have : IsFractionRing O E := inferInstanceAs (IsFractionRing A E)
  have : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP A
  -- 推导：记下中间结论 `lift`：`B ≤ O`。
  have lift : B ≤ O := fun x hx => A.algebraMap_mem (⟨x, hx⟩ : B)
  let g := Subalgebra.inclusion lift
  have units : ∀ x : P.primeCompl, IsUnit (ψ x.val) := fun x => isUnit_iff_ne_zero.mpr x.property
  let φ : O →ₐ[K] K := (IsLocalization.liftAlgHom units : A →ₐ[K] K)
  have restrict (x : B) : φ (g x) = ψ x := IsLocalization.lift_eq (S := A) units x
  have ne (b : B) (hb : ψ b ≠ 0) : (b : E) ≠ 0 := by
    intro he
    exact hb (by rw [show b = 0 from Subtype.ext he, map_zero])
  have inv (b : B) (hb : ψ b ≠ 0) : (b : E)⁻¹ ∈ O :=
    ⟨1, b, hb, by simp⟩
  have fraction (x : E) (hx : x ∈ O) : ∃ a b : B, ψ b ≠ 0 ∧ x = (a : E) / (b : E) := by
    -- 推导：从 `hx` 中取出 `a, b, hb, he`。
    obtain ⟨a, b, hb, he⟩ := hx
    exact ⟨a, b, hb, he.trans (div_eq_mul_inv ..).symm⟩
  have gen : ∃ S : Subalgebra K E, S.FG ∧ S ≤ O ∧
      ∀ x : O, ∃ a b : S, (b : E)⁻¹ ∈ O ∧ (x : E) = (a : E) / (b : E) := by
    refine ⟨B, fg, lift, fun x => ?_⟩
    obtain ⟨a, b, hb, he⟩ := fraction x.val x.property
    exact ⟨a, b, inv b hb, he⟩
  have le : D ≤ O := by
    intro x hx
    by_cases he : x = 0
    · rw [he]; exact O.zero_mem
    rcases mem_or_inv O x with hin | hin
    · exact hin
    -- 推导：从 `fraction _ hin` 中取出 `a, b, hb, hfrac`。
    obtain ⟨a, b, hb, hfrac⟩ := fraction _ hin
    have heq : x * (a : E) = b := by
      rw [← (eq_div_iff (ne b hb)).mp hfrac, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
    have eq : (⟨x, hx⟩ : D) * f a = f b := Subtype.ext heq
    have hg : ψ a ≠ 0 := by
      intro hn
      apply hb
      change δ (f b) = 0
      rw [← eq, map_mul, show δ (f a) = 0 from hn, mul_zero]
    rw [(eq_div_iff (ne a hg)).mpr heq, div_eq_mul_inv]
    exact O.mul_mem (lift b.property) (inv a hg)
  have he (x : D) : φ ⟨x.val, le x.property⟩ = δ x := by
    -- 推导：从 `fraction _ (le x.property)` 中取出 `a, b, hb, hx`。
    obtain ⟨a, b, hb, hx⟩ := fraction _ (le x.property)
    have eq := (eq_div_iff (ne b hb)).mp hx
    have hx₁ : (⟨x.val, le x.property⟩ : O) * g b = g a := Subtype.ext eq
    have hx₂ : x * f b = f a := Subtype.ext eq
    apply mul_right_cancel₀ hb
    calc
      _ = ψ a := by rw [← restrict, ← map_mul, hx₁, restrict]
      _ = _ := by change δ (f a) = δ x * δ (f b); rw [← map_mul, hx₂]
  have ht : g t ≠ 0 := fun he => hne (Subtype.ext (congrArg (fun x : O => x.val) he))
  exact ⟨discreteBranch O φ (g t) ht ((restrict t).trans hz) gen, le, he⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 将有理点延拓到整闭包

**英文原文**

Extending rational points to the integral closure
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

-- 读法：存在 `φ : S →ₐ[K] K`，对每个 `x`，`φ (algebraMap R S x)` 等于 `δ x`。这里调用 `Ideal.Quotient.eq.mpr`。
private theorem extend_integral {K R S : Type*} [Field K] [IsAlgClosed K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [FaithfulSMul R S] [Algebra.IsIntegral R S]
    (δ : R →ₐ[K] K) : ∃ φ : S →ₐ[K] K, ∀ x, φ (algebraMap R S x) = δ x := by
  have : (RingHom.ker δ).IsMaximal := RingHom.ker_isMaximal_of_surjective δ
    (fun a => ⟨algebraMap K R a, δ.commutes a⟩)
  obtain ⟨I, hI, ho⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) (RingHom.ker δ)
  let q := Ideal.Quotient.mkₐ K I
  have h (x : R) : algebraMap K (S ⧸ I) (δ x) = q (algebraMap R S x) := by
    rw [← q.commutes, IsScalarTower.algebraMap_apply K R S]
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    change _ ∈ Ideal.under R I
    rw [← (Ideal.liesOver_iff _ _).mp ho]
    simp
  have : Algebra.IsIntegral K (S ⧸ I) := ⟨by
    intro y
    -- 推导：从 `Ideal.Quotient.mk_surjective y` 中取出 `x, rfl`。
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact IsIntegral.map_of_comp_eq δ.toRingHom q.toRingHom (RingHom.ext h)
      (Algebra.IsIntegral.isIntegral x)⟩
  let f : (S ⧸ I) →ₐ[K] K := IsAlgClosed.lift
  exact ⟨f.comp q, fun x => by rw [AlgHom.comp_apply, ← h, f.commutes]; rfl⟩

-- 读法：存在 `φ : ((integralClosure R E).restrictScalars K) →ₐ[K] K`，对每个 `(x : R) (hx : (x : E) ∈ integralClosure R E)`，`φ ⟨x.val, hx⟩` 等于 `δ x`。
/-- 子代数上的每个有理点都可延拓到其整闭包上。

英文原文：Every rational point of the subalgebra extends over its integral closure.
-/
theorem extend_point {K E : Type*} [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (R : Subalgebra K E) (δ : R →ₐ[K] K) :
    ∃ φ : ((integralClosure R E).restrictScalars K) →ₐ[K] K,
      ∀ (x : R) (hx : (x : E) ∈ integralClosure R E), φ ⟨x.val, hx⟩ = δ x := by
  obtain ⟨φ, hφ⟩ := extend_integral (S := integralClosure R E) δ
  exact ⟨φ, fun x _ => hφ x⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 形变曲线在指定点处的一个分支

**英文原文**

A branch of the deformation curve at the prescribed point
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

-- 读法：存在 `b : Branch K E (t : E)`，存在 `h : R ≤ b.ring`，对每个 `a : R`，`b.res ⟨a.val, h a.property⟩` 等于 `δ a`。
/-- 先相对于参数作正规化，再选取仿射代数的整闭包上某点下方的素理想。即使原来的点是奇点，此法仍适用。

英文原文：Normalize over the parameter, then choose the prime below a point
on the integral closure of the affine algebra. This works even when
the original point is singular.
-/
theorem exists_branch {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero K] [IsAlgClosed K]
    (R : Subalgebra K E) [IsFractionRing R E] (fg : R.FG) (δ : R →ₐ[K] K)
    (t : R) (ht : t ≠ 0) (hδ : δ t = 0)
    (alg : Algebra.IsAlgebraic (IntermediateField.adjoin K {(t : E)}) E) :
    ∃ b : Branch K E (t : E), ∃ h : R ≤ b.ring, ∀ a : R, b.res ⟨a.val, h a.property⟩ = δ a := by
  let D := (integralClosure R E).restrictScalars K
  have hR : R ≤ D := fun x hx => isIntegral_algebraMap (R := R) (A := E) (x := ⟨x, hx⟩)
  obtain ⟨B, hB, inc, mem, frac, ded⟩ := curve R fg t alg
  obtain ⟨φ, hφ⟩ := extend_point R δ
  let x : B := ⟨t.val, mem⟩
  have hx : x ≠ 0 := fun hn => ht (Subtype.ext (congrArg (fun x : B => x.val) hn))
  have hz : φ (Subalgebra.inclusion inc x) = 0 := (hφ t _).trans hδ
  obtain ⟨b, hb, h⟩ := local_branch B D hB inc φ x hx hz
  exact ⟨b, hR.trans hb, fun a => (h ⟨a.val, hR a.property⟩).trans (hφ a _)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 仿射空间中有理点的孤立性

**英文原文**

Isolation at a rational point of affine space
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

variable {K : Type*} {σ : Type} [Field K]

-- 读法：在后续公式中，`maxPoint` 是 `RingHom.ker (eval x)` 的缩写。
abbrev maxPoint (x : σ → K) : Ideal (MvPolynomial σ K) := RingHom.ker (eval x)

-- 读法：`Isolated` 表示以下条件：`maxPoint x` 属于 `I.minimalPrimes`。
def Isolated (x : σ → K) (I : Ideal (MvPolynomial σ K)) : Prop := maxPoint x ∈ I.minimalPrimes

-- 读法：`comb` 的取值由 `∑ i, C (a i : K) * y i` 给出。
def comb [CharZero K] {B : Type} [Fintype B] (y : B → MvPolynomial σ K) (a : B → ℚ) :=
  ∑ i, C (a i : K) * y i

-- 读法：`offset` 的取值由 `X (.inl i) - C (β i)` 给出。
def offset {Z W : Type} (β : Z → K) (i : Z) : MvPolynomial (Z ⊕ W) K := X (.inl i) - C (β i)

-- 读法：`diagonalIdeal` 的取值由 `⨆ j, (I j).map (rename (Sum.map id (Sigma.mk j)))` 给出。
def diagonalIdeal {J Z : Type} {W : J → Type} (I : ∀ j, Ideal (MvPolynomial (Z ⊕ W j) K)) :
    Ideal (MvPolynomial (Z ⊕ (Σ j, W j)) K) :=
  ⨆ j, (I j).map (rename (Sum.map id (Sigma.mk j)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 避开有限多个极小素理想的有理切片

**英文原文**

Rational cuts avoiding finitely many minimal primes
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {B σ : Type} [Fintype B]
    (y : B → MvPolynomial σ K)

-- 读法：`comb y a` 属于 `Ideal.span (Set.range y)`。这里调用 `Submodule.sum_mem`。
theorem comb_mem (a : B → ℚ) : comb y a ∈ Ideal.span (Set.range y) := by
  exact Submodule.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

-- 读法：用字段 `carrier`、`zero_mem'`、`add_mem'`、`smul_mem'` 构造 `Submodule ℚ (B → ℚ)`。
private def bad (P : Ideal (MvPolynomial σ K)) : Submodule ℚ (B → ℚ) where
  carrier := {a | comb y a ∈ P}
  zero_mem' := by simp [comb]
  add_mem' := by
    intro a b ha hb
    change comb y (a + b) ∈ P
    simpa only [comb, Pi.add_apply, Rat.cast_add, map_add, add_mul, Finset.sum_add_distrib] using P.add_mem ha hb
  smul_mem' := by
    intro c a ha
    change comb y (c • a) ∈ P
    simpa only [comb, Pi.smul_apply, smul_eq_mul, Rat.cast_mul, map_mul, mul_assoc, Finset.mul_sum]
      using P.mul_mem_left (C (c : K)) ha

-- 读法：`comb y (fun j => if j = i then 1 else 0)` 等于 `y i`。
private theorem coeff_one (i : B) : comb y (fun j => if j = i then 1 else 0) = y i := by
  unfold comb
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

-- 读法：存在 `a`，对每个 `P ∈ I.minimalPrimes`，由 `P < m` 推出 `comb y a ∉ P`。这里调用 `Ideal.span_le.mpr`。
theorem avoid [Finite σ] {I m : Ideal (MvPolynomial σ K)}
    (h : m ∈ (I ⊔ Ideal.span (Set.range y)).minimalPrimes) :
    ∃ a, ∀ P ∈ I.minimalPrimes, P < m → comb y a ∉ P := by
  let t := {P | P ∈ I.minimalPrimes ∧ P < m}
  have : Finite ↥t := (I.finite_minimalPrimes_of_isNoetherianRing.subset (fun _ h => h.1)).to_subtype
  have hb (P : t) : bad y P.val ≠ ⊤ := by
    intro e
    have hs : Ideal.span (Set.range y) ≤ P.val := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [← coeff_one y i]
      change (fun j => if j = i then 1 else 0) ∈ bad y P.val
      rw [e]; exact Submodule.mem_top
    exact P.2.2.not_ge (h.2 ⟨P.2.1.1.1, sup_le P.2.1.1.2 hs⟩ P.2.2.le)
  have : Infinite ℚ := Infinite.of_injective (fun n : ℕ => (n : ℚ)) Nat.cast_injective
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (fun P : t => bad y P.val) hb
  exact ⟨a, fun P hp hm => ha ⟨P, hp, hm⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 用给定方程的有理组合分离一个点

一次截取即可去除经过选定点的所有正维分量。剩下位于该点下方的每条素理想链，其长度至少减一。对零理想反复应用可得方阵型方程组。

**英文原文**

Isolating a point by rational combinations of given equations

One cut removes all positive-dimensional components through the
chosen point. The length of every chain remaining below it drops
by at least one. Applied to the zero ideal this gives a square
system of equations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {σ B : Type} [Fintype σ] [Fintype B]
    (x : σ → K) (y : B → MvPolynomial σ K)
local notation "m" => maxPoint x
local notation "Y" => Ideal.span (Set.range y)

-- 读法：`Ideal.span (Set.range (f ∘ Fin.cons a b))` 等于 `Ideal.span {f a} ⊔ Ideal.span (Set.range (f ∘ b))`。
private theorem span_cons {A R : Type*} [CommRing R] {d : ℕ} (f : A → R) (a : A) (b : Fin d → A) :
    Ideal.span (Set.range (f ∘ Fin.cons a b)) = Ideal.span {f a} ⊔ Ideal.span (Set.range (f ∘ b)) := by
  rw [Set.range_comp, Set.range_comp, Fin.range_cons, Set.image_insert_eq, Ideal.span_insert]

-- 读法：存在 `A : Fin d → B → ℚ`，要证明的命题是 `Isolated x (I ⊔ Ideal.span (Set.range (fun t => comb y (A t))))`。对 `d` 作归纳，并把 `I` 保持为任意参数。
theorem cut {I : Ideal (MvPolynomial σ K)} (h : Isolated x (I ⊔ Y)) {d : ℕ}
    (hd : ∀ p, I ≤ p → ¬Chain p m (d + 1)) :
    ∃ A : Fin d → B → ℚ, Isolated x (I ⊔ Ideal.span (Set.range (fun t => comb y (A t)))) := by
  induction d generalizing I with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    rw [Set.range_eq_empty, Ideal.span_empty, sup_bot_eq]
    refine ⟨⟨h.1.1, le_sup_left.trans h.1.2⟩, ?_⟩
    intro p hp hm
    by_contra hn
    exact hd p hp.2 (.cons hp.1 (lt_of_le_not_ge hm hn) (.nil h.1.1 le_rfl))
  | succ d ih =>
    -- 推导：从 `avoid y h` 中取出 `a, ha`。
    obtain ⟨a, ha⟩ := avoid y h
    let J := I ⊔ Ideal.span {comb y a}
    have he : J ⊔ Y = I ⊔ Y := by
      rw [show J = _ from rfl, sup_assoc, sup_eq_right.mpr (Ideal.span_singleton_le_iff_mem _ |>.mpr (comb_mem y a))]
    have short (p : Ideal (MvPolynomial σ K)) (hp : J ≤ p) (hc : Chain p m (d + 1)) : False := by
      have := hc.prime
      obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hp : I ≤ p)
      have hlt : q < p := lt_of_le_of_ne hle fun eq =>
        ha q hq (hle.trans_lt hc.lt) (by
          rw [eq]
          exact (le_sup_right.trans hp : Ideal.span {comb y a} ≤ p) (Ideal.subset_span rfl))
      exact hd q hq.1.2 (.cons hq.1.1 hlt hc)
    -- 推导：从 `ih (he.symm ▸ h) short` 中取出 `A, hA`。
    obtain ⟨A, hA⟩ := ih (he.symm ▸ h) short
    refine ⟨Fin.cons a A, ?_⟩
    change Isolated x (I ⊔ Ideal.span (Set.range (comb y ∘ Fin.cons a A)))
    rw [span_cons, ← sup_assoc]
    exact hA

omit [CharZero K] in
-- 读法：`(m).height` 不超过 `Fintype.card σ`。
theorem point_height_le : (m).height ≤ Fintype.card σ := by
  have : (m).IsPrime := RingHom.ker_isPrime _
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_fintype_card] at h
  exact_mod_cast h

-- 读法：存在 `A : σ → B → ℚ`，要证明的命题是 `Isolated x (Ideal.span (Set.range (fun j => comb y (A j))))`。这里调用 `Nat.not_succ_le_self`。
theorem square_system (h : Isolated x Y) :
    ∃ A : σ → B → ℚ, Isolated x (Ideal.span (Set.range (fun j => comb y (A j)))) := by
  have short (p : Ideal (MvPolynomial σ K)) (_ : ⊥ ≤ p) (hc : Chain p m (Fintype.card σ + 1)) : False := by
    have ht := hc.length_le.trans (point_height_le x)
    exact Nat.not_succ_le_self _ (ENat.natCast_le_natCast.mp ht)
  obtain ⟨A, hA⟩ := cut x y (I := ⊥) (by rwa [bot_sup_eq]) short
  let e := Fintype.equivFin σ
  refine ⟨A ∘ e, ?_⟩
  rw [bot_sup_eq] at hA
  change Isolated x (Ideal.span (Set.range ((fun j => comb y (A j)) ∘ e)))
  rwa [Set.range_comp, e.surjective.range_eq, Set.image_univ]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 把孤立性传递到扩张后的系数及各个坐标

**英文原文**

Transferring isolation to extended coefficients and to separate coordinates
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

variable {K : Type*} {σ : Type} [Field K]

-- 读法：`maxPoint x` 不超过 `P`。这里调用 `MvPolynomial.ringHom_ext`。
/-- 固定了所有坐标的理想包含求值映射的核。

英文原文：Every ideal fixing all coordinates contains the evaluation kernel.
-/
theorem point_le (x : σ → K) (P : Ideal (MvPolynomial σ K))
    (h : ∀ i, X i - C (x i) ∈ P) : maxPoint x ≤ P := by
  let q := Ideal.Quotient.mk P
  have e : q = (q.comp C).comp (eval x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.comp_apply, eval_X]
      exact Ideal.Quotient.eq.mpr (h i)
  intro p hp
  change eval x p = 0 at hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q p = 0
  rw [e, RingHom.comp_apply, hp, map_zero]

-- 读法：要证明的命题是 `Isolated (f ∘ x) (I.map (MvPolynomial.map f))`。
/-- 扩张基域后，孤立有理点仍是孤立点。

英文原文：An isolated rational point remains isolated under a field extension.
-/
theorem Isolated.map {L : Type*} [Field L] {x : σ → K} {I : Ideal (MvPolynomial σ K)}
    (h : Isolated x I) (f : K →+* L) : Isolated (f ∘ x) (I.map (MvPolynomial.map f)) := by
  refine ⟨⟨RingHom.ker_isPrime _, Ideal.map_le_iff_le_comap.mpr ?_⟩, ?_⟩
  · intro p hp
    change eval (f ∘ x) (MvPolynomial.map f p) = 0
    have hx : eval x p = 0 := h.1.2 hp
    rw [← map_eval, hx, map_zero]
  · intro P hP hle
    have : P.IsPrime := hP.1
    have hp : maxPoint x ≤ P.comap (MvPolynomial.map f) := by
      apply h.2 ⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp hP.2⟩
      intro p hm
      -- 推导：记下中间结论 `hz`：`eval (f ∘ x) (MvPolynomial.map f p) = 0`。
      have hz : eval (f ∘ x) (MvPolynomial.map f p) = 0 := hle hm
      change eval x p = 0
      apply f.injective
      rw [map_eval, hz, map_zero]
    apply point_le
    intro i
    have hm : X i - C (x i) ∈ maxPoint x := by simp [maxPoint]
    have hz : MvPolynomial.map f (X i - C (x i)) ∈ P := hp hm
    simpa using hz

variable {J Z : Type} {W : J → Type}

-- 读法：`difference` 的取值由 `X ⟨p.1.1, Sum.inl p.2⟩ - X ⟨j₀, Sum.inl p.2⟩` 给出。
/-- 重复坐标的值等于它在参照块中的值。

英文原文：Equality of a repeated coordinate with its value in the reference block.
-/
def difference (j₀ : J) (p : {j // j ≠ j₀} × Z) : MvPolynomial (Σ j, Z ⊕ W j) K :=
  X ⟨p.1.1, Sum.inl p.2⟩ - X ⟨j₀, Sum.inl p.2⟩

-- 读法：这里调用 `Ideal.map_le_iff_le_comap.mpr`。
/-- 把一个共用的坐标块拆成多个副本，并要求每个副本与其中一个指定副本相等。

英文原文：Replace a shared block of coordinates by separate copies, imposing equality to one copy.
-/
theorem Isolated.separate {β : Z → K} {w : ∀ j, W j → K}
    {I : ∀ j, Ideal (MvPolynomial (Z ⊕ W j) K)}
    (h : Isolated (Sum.elim β (fun x => w x.1 x.2)) (diagonalIdeal I)) (j₀ : J) :
    Isolated (fun x : (Σ j, Z ⊕ W j) => Sum.elim β (w x.1) x.2)
      ((⨆ j, (I j).map (rename (@Sigma.mk J (fun k => Z ⊕ W k) j))) ⊔
        Ideal.span (Set.range (difference j₀))) := by
  let x : Z ⊕ (Σ j, W j) → K := Sum.elim β (fun a => w a.1 a.2)
  let y : (Σ j, Z ⊕ W j) → K := fun a => Sum.elim β (w a.1) a.2
  let s : Z ⊕ (Σ j, W j) → (Σ j, Z ⊕ W j) :=
    Sum.elim (fun z => ⟨j₀, .inl z⟩) (fun a => ⟨a.1, .inr a.2⟩)
  -- 推导：记下中间结论 `he`：`y ∘ s = x`。
  have he : y ∘ s = x := by funext a; cases a <;> rfl
  refine ⟨⟨RingHom.ker_isPrime _, sup_le (iSup_le fun j => ?_) (Ideal.span_le.mpr ?_)⟩, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    have hblock : (I j).map (rename (Sum.map id (Sigma.mk j))) ≤ diagonalIdeal I :=
      le_iSup (fun k => (I k).map (rename (Sum.map id (Sigma.mk k)))) j
    have hz : eval x (rename (Sum.map id (Sigma.mk j)) p) = 0 :=
      h.1.2 (hblock (Ideal.mem_map_of_mem _ hp))
    have hem : y ∘ Sigma.mk j = x ∘ Sum.map id (Sigma.mk j) := by
      funext a; cases a <;> rfl
    change eval y (rename (Sigma.mk j) p) = 0
    rwa [eval_rename, hem, ← eval_rename]
  · rintro _ ⟨a, rfl⟩
    change eval y (difference j₀ a) = 0
    simp [difference, y]
  · intro P hP hle
    have : P.IsPrime := hP.1
    have hd (j : J) (z : Z) :
        X ⟨j, Sum.inl z⟩ - X ⟨j₀, Sum.inl z⟩ ∈ P := by
      by_cases hj : j = j₀
      · subst j; simp
      · exact (le_sup_right.trans hP.2) (Ideal.subset_span ⟨(⟨j, hj⟩, z), rfl⟩)
    -- 推导：记下中间结论 `hs`：`diagonalIdeal I ≤ P.comap (rename s)`。
    have hs : diagonalIdeal I ≤ P.comap (rename s) := by
      refine iSup_le fun j => Ideal.map_le_iff_le_comap.mpr ?_
      intro p hp
      let q := Ideal.Quotient.mk P
      have heq : (q.comp (rename s).toRingHom).comp
          (rename (Sum.map id (Sigma.mk j))).toRingHom =
          q.comp (rename (Sigma.mk j)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r; simp
        · rintro (z | v)
          · simpa [s] using (Ideal.Quotient.eq.mpr (hd j z)).symm
          · simp [s]
      -- 推导：记下中间结论 `hj`：`(I j).map (rename (@Sigma.mk J (fun k => Z ⊕ W k) j)) ≤ P`。
      have hj : (I j).map (rename (@Sigma.mk J (fun k => Z ⊕ W k) j)) ≤ P :=
        (iSup_le_iff.mp (le_sup_left.trans hP.2)) j
      change rename s (rename (Sum.map id (Sigma.mk j)) p) ∈ P
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (RingHom.congr_fun heq p).trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr (hj (Ideal.mem_map_of_mem _ hp)))
    have hm : maxPoint x ≤ P.comap (rename s) := by
      apply h.2 ⟨Ideal.comap_isPrime _ _, hs⟩
      intro p hp
      have hz : eval y (rename s p) = 0 := hle hp
      rwa [eval_rename, he] at hz
    have hh (i : Z ⊕ (Σ j, W j)) : X (s i) - C (x i) ∈ P := by
      -- 推导：记下中间结论 `hz`：`rename s (X i - C (x i)) ∈ P`。
      have hz : rename s (X i - C (x i)) ∈ P := hm (by simp [maxPoint])
      simpa using hz
    apply point_le
    rintro ⟨j, z | v⟩
    · simpa [s, x] using P.add_mem (hd j z) (hh (.inl z))
    · exact hh (.inr ⟨j, v⟩)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 依次对坐标求值以确定有理点的高度

**英文原文**

Height of a rational point by successively evaluating its coordinates
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial Finset
open scoped Classical

variable {K : Type*} [Field K] {σ : Type} (x : σ → K)

-- 读法：`fixAt` 的取值由 `aeval (fun j => if j ∈ s then C (x j) else X j)` 给出。
private def fixAt (s : Finset σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun j => if j ∈ s then C (x j) else X j)

-- 读法：`RingHom.ker (fixAt x s)` 严格小于 `RingHom.ker (fixAt x (insert i s))`。这里调用 `algHom_ext`。
private theorem fix_insert (s : Finset σ) (i : σ) (hi : i ∉ s) :
    RingHom.ker (fixAt x s) < RingHom.ker (fixAt x (insert i s)) := by
  let a := fixAt x s
  let b := fixAt x (insert i s)
  have he : b.comp a = b := by
    apply algHom_ext
    intro j
    by_cases h : j ∈ s <;> simp [a, b, fixAt, h]
  refine lt_of_le_of_ne ?_ ?_
  · intro z hz
    change a z = 0 at hz
    change b z = 0
    rw [← he, AlgHom.comp_apply, hz, map_zero]
  · intro h
    -- 推导：记下中间结论 `hz`：`X i - C (x i) ∈ RingHom.ker b`。
    have hz : X i - C (x i) ∈ RingHom.ker b := by simp [b, fixAt]
    rw [show RingHom.ker b = RingHom.ker a from h.symm] at hz
    have ha : X i - C (x i) = (0 : MvPolynomial σ K) := by simpa [a, fixAt, hi] using hz
    have := congrArg (eval (fun _ => x i + 1)) ha
    simp at this

-- 读法：`(Fintype.card σ : ℕ∞)` 不超过 `(maxPoint x).height`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
theorem height_maxPoint [Fintype σ] : (Fintype.card σ : ℕ∞) ≤ (maxPoint x).height := by
  have bound (s : Finset σ) : (s.card : ℕ∞) ≤ (RingHom.ker (fixAt x s)).height := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have lt := fix_insert x s i hi
      let _ := RingHom.ker_isPrime (fixAt x s)
      let _ := RingHom.ker_isPrime (fixAt x (insert i s))
      rw [card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      exact (add_le_add_left ih _).trans (Ideal.height_add_one_le_of_lt_of_isPrime lt)
  -- 推导：记下中间结论 `eq`：`(aeval x).comp (fixAt x univ) = aeval x`。
  have eq : (aeval x).comp (fixAt x univ) = aeval x := by
    apply algHom_ext
    intro i
    simp [fixAt]
  refine (bound univ).trans (Ideal.height_mono ?_)
  intro z hz
  change fixAt x univ z = 0 at hz
  change aeval x z = 0
  rw [← eq, AlgHom.comp_apply, hz, map_zero]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 在孤立点处扰动一个方形方程组

增加一个变量，并从各方程中减去它的某个倍数。经过给定点的极小素理想都不能包含新变量；否则由该点在原纤维中是孤立点可知，该素理想等于极大理想，而后者的高度超过了方程数。

**英文原文**

Perturbing a square system at an isolated point

Add one variable and subtract a multiple of it from each equation.
No minimal prime through the given point can contain the new variable.
Otherwise isolation in the original fiber forces that prime to equal
the maximal ideal, whose height exceeds the number of equations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical
variable {K : Type*} [Field K] {σ : Type} (G : σ → MvPolynomial σ K) (c : σ → K)

-- 读法：`perturb` 的取值由 `rename some (G i) - X none * C (c i)` 给出。
def perturb (i : σ) : MvPolynomial (Option σ) K :=
  rename some (G i) - X none * C (c i)

-- 读法：`fixedZero` 的取值由 `i.elim 0 x` 给出。
def fixedZero (x : σ → K) (i : Option σ) := i.elim 0 x

-- 读法：存在 `P : Ideal (MvPolynomial (Option σ) K)`，`P.IsPrime` 与 `P ≤ maxPoint (fixedZero x) ∧ (∀ i, perturb G c i ∈ P) ∧ X none ∉ P` 同时成立。
theorem perturb_prime [Fintype σ] {x : σ → K} (hx : Isolated x (Ideal.span (Set.range G))) :
    ∃ P : Ideal (MvPolynomial (Option σ) K), P.IsPrime ∧ P ≤ maxPoint (fixedZero x) ∧
      (∀ i, perturb G c i ∈ P) ∧ X none ∉ P := by
  let z := fixedZero x
  let M := maxPoint z
  let I := Ideal.span (Set.range (perturb G c))
  have h : I ≤ M := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hg : eval x (G i) = 0 := hx.1.2 (Ideal.subset_span ⟨i, rfl⟩)
    change eval z (perturb G c i) = 0
    simp [perturb, eval_rename, z, fixedZero, Function.comp_def, hg]
  have : M.IsPrime := RingHom.ker_isPrime _
  -- 推导：从 `Ideal.exists_minimalPrimes_le h` 中取出 `P, hP, hm`。
  obtain ⟨P, hP, hm⟩ := Ideal.exists_minimalPrimes_le h
  have : P.IsPrime := hP.1.1
  have hs i : perturb G c i ∈ P := hP.1.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨P, hP.1.1, hm, hs, fun ht => ?_⟩
  let Q := P.comap (rename some)
  have he : Ideal.span (Set.range G) ≤ Q := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change rename some (G i) ∈ P
    simpa [perturb] using P.add_mem (hs i) (P.mul_mem_right (C (c i)) ht)
  -- 推导：记下中间结论 `hle`：`Q ≤ maxPoint x`。
  have hle : Q ≤ maxPoint x := by
    intro q hq
    have hh : eval z (rename some q) = 0 := hm hq
    rw [eval_rename] at hh
    exact hh
  have inv := hx.2 ⟨Ideal.comap_isPrime _ _, he⟩ hle
  have eq : M ≤ P := by
    apply point_le
    rintro (_|i)
    · simpa [z, fixedZero] using ht
    -- 推导：记下中间结论 `hp`：`rename some (X i - C (x i)) ∈ P`。
    · have hp : rename some (X i - C (x i)) ∈ P := inv (by simp [maxPoint])
      simpa [z, fixedZero] using hp
  have lower := (height_maxPoint z).trans (Ideal.height_mono eq)
  have upper := Ideal.height_le_ncard_of_mem_minimalPrimes_span (Set.finite_range _) hP
  have small : (Set.range (perturb G c)).ncard ≤ Fintype.card σ := by
    simpa using Set.ncard_image_le (f := perturb G c) (s := Set.univ)
  have le : Fintype.card (Option σ) ≤ Fintype.card σ := by
    exact_mod_cast (lower.trans upper).trans (show (_ : ℕ∞) ≤ Fintype.card σ by exact_mod_cast small)
  rw [Fintype.card_option] at le
  omega

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 扰动后方程组的一个分支的函数域

**英文原文**

The function field of a component of the perturbed system
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical
variable {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type}

-- 读法：要证明的命题是 `Transcendental K (t : E)`。按 `Subtype.ext` 的外延性准则比较各分量。
theorem transcendental_of_residue (R : Subalgebra K E) (f : R →ₐ[K] K)
    (t : R) (hn : t ≠ 0) (hz : f t = 0) : Transcendental K (t : E) := by
  intro h
  let p := minpoly K (t : E)
  have ht : Polynomial.aeval t p = 0 := by
    apply Subtype.ext
    change R.val (Polynomial.aeval t p) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact minpoly.aeval _ _
  have hp := congrArg f ht
  rw [← Polynomial.aeval_algHom_apply, hz, map_zero] at hp
  have he : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using hp
  exact minpoly.coeff_zero_ne_zero h.isIntegral (fun h => hn (Subtype.ext h)) he

-- 读法：结构的字段包括 `E`、`ring`、`fg`、`res`、`t`。
structure Deformation (G : σ → MvPolynomial σ K) (c x : σ → K) where
  E : Type u
  [field : Field E]
  [alg : Algebra K E]
  ring : Subalgebra K E
  [fraction : IsFractionRing ring E]
  fg : ring.FG
  res : ring →ₐ[K] K
  t : ring
  nonzero : t ≠ 0
  zero : res t = 0
  y : σ → ring
  point : ∀ i, res (y i) = x i
  ray : ∀ i, aeval (fun j => (y j : E)) (G i) = (t : E) * algebraMap K E (c i)
  generates : IntermediateField.adjoin K (insert (t : E) (Set.range (fun i => (y i : E)))) = ⊤

attribute [instance] Deformation.field Deformation.alg Deformation.fraction

-- 读法：`IntermediateField.adjoin K (Set.range (f ∘ X))` 等于 `⊤`。这里调用 `top_unique`。
private theorem generates {ι : Type} (f : MvPolynomial ι K →ₐ[K] E) [IsFractionRing f.range E] :
    IntermediateField.adjoin K (Set.range (f ∘ X)) = ⊤ := by
  have h : f.range ≤ (IntermediateField.adjoin K (Set.range (f ∘ X))).toSubalgebra := by
    have := IntermediateField.algebra_adjoin_le_adjoin K (Set.range (f ∘ X))
    rwa [Algebra.adjoin_range_eq_range_aeval, ← aeval_unique f] at this
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective f.range z
  exact IntermediateField.div_mem _ (h a.property) (h b.property)

-- 读法：要证明的命题是 `f.range.FG`。
private theorem generated {ι : Type} [Finite ι] (f : MvPolynomial ι K →ₐ[K] E) : f.range.FG := by
  let s := Set.range (f ∘ X)
  have hs : s.Finite := Set.finite_range _
  refine ⟨hs.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, show s = Set.range (f ∘ X) from rfl,
    Algebra.adjoin_range_eq_range_aeval, ← aeval_unique f]

-- 读法：`(Deformation G c x)` 有元素。
theorem exists_deformation [Fintype σ] (G : σ → MvPolynomial σ K) (c x : σ → K)
    (h : Isolated x (Ideal.span (Set.range G))) : Nonempty (Deformation G c x) := by
  classical
  obtain ⟨P, hP, hm, hs, ht⟩ := perturb_prime G c h
  have : P.IsPrime := hP
  let A := MvPolynomial (Option σ) K ⧸ P
  let E := FractionRing A
  let f := (IsScalarTower.toAlgHom K A E).comp (Ideal.Quotient.mkₐ K P)
  have ker (z : MvPolynomial (Option σ) K) : f z = 0 ↔ z ∈ P := by
    change algebraMap A E (Ideal.Quotient.mk P z) = 0 ↔ _
    rw [← map_zero (algebraMap A E), (IsFractionRing.injective A E).eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  have hf : IsFractionRing f.range E := by
    apply IsFractionRing.of_field
    intro z
    -- 推导：从 `IsFractionRing.div_surjective A z` 中取出 `a, b, _, rfl`。
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K P a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective K P b
    exact ⟨f.rangeRestrict a, f.rangeRestrict b, rfl⟩
  let _ := hf
  let z := fixedZero x
  have he : RingHom.ker f.rangeRestrict.toRingHom ≤ RingHom.ker (aeval z).toRingHom := by
    intro g hg
    exact hm ((ker g).mp (congrArg Subtype.val hg))
  let δ := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective (aeval z) he
  let y (i : Option σ) := f.rangeRestrict (X i)
  have hd i : δ (y i) = z i := by simp [δ, y]
  refine ⟨{ E := E
            ring := f.range
            fg := generated f
            res := δ
            t := y none
            nonzero := fun he => ht ((ker _).mp (congrArg Subtype.val he))
            zero := hd none
            y := y ∘ some
            point := fun i => hd (some i)
            ray := ?_
            generates := ?_ }⟩
  · intro i
    have hi := (ker _).mpr (hs i)
    rw [aeval_unique f, perturb, map_sub, map_mul, aeval_X, aeval_C, aeval_rename, sub_eq_zero] at hi
    exact hi
  -- 推导：记下中间结论 `eq`：`Set.range (f ∘ X) = insert (y none : E) (Set.range (fun i => (y (some i) : E)))`。
  · have eq : Set.range (f ∘ X) = insert (y none : E) (Set.range (fun i => (y (some i) : E))) := by
      ext t
      constructor
      · rintro ⟨_|i, rfl⟩
        · exact .inl rfl
        · exact .inr ⟨i, rfl⟩
      · rintro (rfl|⟨i, rfl⟩)
        · exact ⟨none, rfl⟩
        · exact ⟨some i, rfl⟩
    exact eq ▸ generates f

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 由有限见证纤维和唯一公共输出得到孤立性

每个坐标只有有限个可能值。由这些值分裂得到的零化多项式，属于包含该方程组的每个素理想。在指定点至多只有一个一次因子可以为零。

**英文原文**

Isolation from finite witness fibers and a unique common output

Each coordinate has finitely many possible values. Its split
annihilating polynomial belongs to every prime over the equations.
At the specified point only one linear factor can vanish.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical
variable {K : Type*} [Field K]

-- 读法：要证明的命题是 `Isolated x I`。
private theorem isolate_coordinates [IsAlgClosed K] {σ : Type} [Finite σ]
    {I : Ideal (MvPolynomial σ K)} {x : σ → K} (hx : I ≤ maxPoint x)
    (h : ∀ i, ∃ s : Finset K, ∀ y : σ → K, I ≤ maxPoint y → y i ∈ s) :
    Isolated x I := by
  refine ⟨⟨RingHom.ker_isPrime _, hx⟩, fun P hP hle => point_le x P fun i => ?_⟩
  have : P.IsPrime := hP.1
  obtain ⟨s, hs⟩ := h i
  have hp : ∏ a ∈ s, (X i - C a) ∈ P := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K:=K) P]
    intro y hy
    have ht : I ≤ maxPoint y := fun p hm => hy p (hP.2 hm)
    rw [map_prod]
    exact Finset.prod_eq_zero (hs y ht) (by simp)
  obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
  have he : x i = a := by simpa [maxPoint, sub_eq_zero] using hle ha
  rwa [he]

variable {J Z : Type} {W : J → Type}
    (I : ∀ j, Ideal (MvPolynomial (Z ⊕ W j) K))

-- 读法：`diagonalIdeal I ≤ maxPoint y` 与 `∀ j, I j ≤ maxPoint (Sum.elim (y ∘ Sum.inl) (fun a => y (.inr ⟨j, a⟩)))` 等价。用函数外延性比较等号两侧在 `i; cases i <;> rfl` 处的取值。
private theorem diagonal_eval (y : Z ⊕ (Σ j, W j) → K) :
    diagonalIdeal I ≤ maxPoint y ↔ ∀ j, I j ≤
      maxPoint (Sum.elim (y ∘ Sum.inl) (fun a => y (.inr ⟨j, a⟩))) := by
  have he (j : J) : (maxPoint y).comap (rename (Sum.map id (Sigma.mk j))) =
      maxPoint (Sum.elim (y ∘ Sum.inl) (fun a => y (.inr ⟨j, a⟩))) := by
    have e : y ∘ Sum.map id (Sigma.mk j) = Sum.elim (y ∘ Sum.inl) (fun a => y (.inr ⟨j, a⟩)) := by
      funext i; cases i <;> rfl
    ext p
    change eval y (rename _ p) = 0 ↔ eval _ p = 0
    rw [eval_rename, e]
  simp only [diagonalIdeal, iSup_le_iff, Ideal.map_le_iff_le_comap, he]

-- 读法：`Isolated (Sum.elim β (fun x => w x.1 x.2)) (diagonalIdeal I)` 与 `∀ j, Isolated (Sum.elim β (w j)) (I j ⊔ Ideal.span (Set.range (offset β)))` 同时成立。
theorem isolate_family [IsAlgClosed K] [Fintype J] [Fintype Z] [∀ j, Fintype (W j)]
    (β : Z → K) (w : ∀ j, W j → K) (hw : ∀ j, I j ≤ maxPoint (Sum.elim β (w j)))
    (hf : ∀ j, Set.Finite {y : W j → K | I j ≤ maxPoint (Sum.elim β y)})
    (hu : ∀ z, (∀ j, ∃ y : W j → K, I j ≤ maxPoint (Sum.elim z y)) → z = β) :
    Isolated (Sum.elim β (fun x => w x.1 x.2)) (diagonalIdeal I) ∧
      ∀ j, Isolated (Sum.elim β (w j)) (I j ⊔ Ideal.span (Set.range (offset β))) := by
  have witness (j : J) (a : W j) :
      ∃ s : Finset K, ∀ y, I j ≤ maxPoint (Sum.elim β y) → y a ∈ s :=
    ⟨(hf j).toFinset.image (fun y => y a), fun y hy =>
      Finset.mem_image.mpr ⟨y, (hf j).mem_toFinset.mpr hy, rfl⟩⟩
  constructor
  · have out (y : Z ⊕ (Σ j, W j) → K) (hy : diagonalIdeal I ≤ maxPoint y) :
        y ∘ Sum.inl = β :=
      hu _ (fun j => ⟨_, (diagonal_eval I y).mp hy j⟩)
    -- 推导：记下中间结论 `x`：`Z ⊕ (Σ j, W j) → K`。
    let x : Z ⊕ (Σ j, W j) → K := Sum.elim β (fun x => w x.1 x.2)
    have he : diagonalIdeal I ≤ maxPoint x := (diagonal_eval I x).mpr hw
    refine isolate_coordinates he ?_
    rintro (i | ⟨j, a⟩)
    · exact ⟨{β i}, fun y hy => Finset.mem_singleton.mpr (congrFun (out y hy) i)⟩
    · obtain ⟨s, hs⟩ := witness j a
      refine ⟨s, fun y hy => hs (fun b => y (.inr ⟨j, b⟩)) ?_⟩
      rw [← out y hy]
      exact (diagonal_eval I y).mp hy j
  · intro j
    let A := I j ⊔ Ideal.span (Set.range (offset β))
    -- 推导：记下中间结论 `hit`：`A ≤ maxPoint (Sum.elim β (w j))`。
    have hit : A ≤ maxPoint (Sum.elim β (w j)) := by
      refine sup_le (hw j) (Ideal.span_le.mpr ?_)
      rintro _ ⟨i, rfl⟩
      simp [maxPoint, offset]
    have out (y : Z ⊕ W j → K) (hy : A ≤ maxPoint y) (i : Z) : y (.inl i) = β i := by
      have he := (le_sup_right.trans hy) (Ideal.subset_span ⟨i, rfl⟩)
      simpa [maxPoint, offset, sub_eq_zero] using he
    apply isolate_coordinates hit
    rintro (i|a)
    · exact ⟨{β i}, fun y hy => Finset.mem_singleton.mpr (out y hy i)⟩
    -- 推导：从 `witness j a` 中取出 `s, hs`。
    · obtain ⟨s, hs⟩ := witness j a
      refine ⟨s, fun y hy => hs (y ∘ Sum.inr) ?_⟩
      have he : Sum.elim β (y ∘ Sum.inr) = y := by
        funext b
        cases b with
        | inl i => exact (out y hy i).symm
        | inr v => rfl
      rw [he]
      exact le_sup_left.trans hy

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
