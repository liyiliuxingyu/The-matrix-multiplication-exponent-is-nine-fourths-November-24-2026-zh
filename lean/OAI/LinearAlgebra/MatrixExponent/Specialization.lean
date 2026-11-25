-- 本文件所属证明环节：把秩分解的有限组系数写在有限生成子环内，通过商域、有限扩张或降域传递同一个分解见证。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# 秩分解的特殊化

取一个包含「在分解系数处求值」这一映射之核的极大理想，便可同时保留这些系数满足的全部方程。在整数上构造时所得剩余域有限；在基域上构造时所得剩余域是基域的有限扩张。

**英文原文**

Specializing a rank decomposition

A maximal ideal containing the kernel of polynomial evaluation at the
decomposition coefficients preserves all their equations. Over the integers
the residue field is finite. Over a base field it is a finite extension.
-/

universe u v

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：要证明的命题是 `IsJacobsonRing ℤ`。这里调用 `isJacobsonRing_iff_prime_eq.mpr`。
private theorem int_jacobson : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hp : P = ⊥
  · subst P
    apply bot_unique
    intro x hx
    change x = 0
    -- 使 3x + 1 成为整数环单位的整数 x 只有零。
    have hu := Int.isUnit_iff.mp (Ideal.mem_jacobson_bot.mp hx 3)
    omega
  · have : P.IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hp
    exact Ideal.jacobson_eq_self_of_isMaximal

-- 读法：`k` 是有限的。
/-- 若一个域作为环是有限生成的，则它是有限域。

英文原文：A field finitely generated as a ring is finite.
-/
private theorem finite_field_of_finiteType (k : Type*) [Field k] [Algebra ℤ k]
    [Algebra.FiniteType ℤ k] : Finite k := by
  cases Subsingleton.elim (inferInstance : Algebra ℤ k) (Ring.toIntAlgebra k)
  have := int_jacobson
  have := finite_of_finite_type_of_isJacobsonRing ℤ k
  let p : Ideal ℤ := (⊥ : Ideal k).under ℤ
  have hp : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (⊥ : Ideal k)
  have : Finite (ℤ ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient
    (Ring.ne_bot_of_isMaximal_of_not_isField hp Int.not_isField)
  have : Module.Finite (ℤ ⧸ p) (k ⧸ (⊥ : Ideal k)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Finite (k ⧸ (⊥ : Ideal k)) := Module.finite_of_finite (ℤ ⧸ p)
  exact Finite.of_equiv _ (RingEquiv.quotientBot k).toEquiv

namespace Rectangle

-- 读法：要证明的命题是 `∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L), WeightedRankLE (fun a b c => algebraMap R L (w a b c)) r`。
/-- 若秩的见证定义在某个域上，且一个基环映入该域，则可在该基环上的某个有限型域上实现同样的见证。

英文原文：Rank witnesses over a field can be realized over a field of finite type
over any base ring mapping into the given field.
-/
theorem finiteTypeWeighted {R : Type u} {K : Type v} [CommRing R] [Field K]
    (φ : R →+* K) {i j k r : ℕ} (w : Fin i → Fin j → Fin k → R)
    (h : WeightedRankLE (fun a b c => φ (w a b c)) r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L),
      WeightedRankLE (fun a b c => algebraMap R L (w a b c)) r := by
  classical
  obtain ⟨a, b, c, habc⟩ := h
  let S := MvPolynomial (Fin r × (Pos i k ⊕ Pos k j ⊕ Pos i j)) R
  let X (l : Fin r) (x : Pos i k) : S := MvPolynomial.X (l, .inl x)
  let Y (l : Fin r) (y : Pos k j) : S := MvPolynomial.X (l, .inr (.inl y))
  let Z (l : Fin r) (z : Pos i j) : S := MvPolynomial.X (l, .inr (.inr z))
  let f : S →+* K := MvPolynomial.eval₂Hom φ
    (fun u ↦ Sum.elim (a u.1) (Sum.elim (b u.1) (c u.1)) u.2)
  -- 推导：从 `Ideal.exists_le_maximal (RingHom.ker f) (RingHom.ker_ne_top f)` 中取出 `m, hm, hker`。
  obtain ⟨m, hm, hker⟩ := Ideal.exists_le_maximal (RingHom.ker f) (RingHom.ker_ne_top f)
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  let g := Ideal.Quotient.mk m
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance,
    fun l x ↦ g (X l x), fun l y ↦ g (Y l y), fun l z ↦ g (Z l z), ?_⟩
  intro x y z
  let t : S := ∑ l : Fin r, X l x * Y l y * Z l z
  let d : S := if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then MvPolynomial.C (w x.1 y.2 x.2) else 0
  have hf : f t = f d := by
    simpa [t, d, apply_ite f, f, X, Y, Z, S] using habc x y z
  -- 推导：记下中间结论 `hg`：`g t = g d`。
  have hg : g t = g d := Ideal.Quotient.eq.mpr (hker (by
    change f (t - d) = 0
    rw [map_sub, hf, sub_self]))
  have hc (a : R) : g (MvPolynomial.C a) = algebraMap R (S ⧸ m) a := rfl
  simpa only [t, d, map_sum, map_mul, apply_ite g, hc, map_zero] using hg

-- 读法：要证明的命题是 `∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L), RankLE L i j k r`。
theorem finiteTypeRank {R : Type u} {K : Type v} [CommRing R] [Field K]
    (φ : R →+* K) {i j k r : ℕ} (h : RankLE K i j k r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L),
      RankLE L i j k r := by
  obtain ⟨L, _, _, _, hL⟩ := finiteTypeWeighted φ (fun _ _ _ => 1) (by
    simpa only [map_one, WeightedRankLE, RankLE] using h)
  exact ⟨L, inferInstance, inferInstance, inferInstance, by
    simpa only [map_one, WeightedRankLE, RankLE] using hL⟩

-- 读法：存在 `(K : Type) (_ : Field K) (_ : Finite K)`，在 `K` 上，三个尺寸为 `i`、`j`、`k` 的矩阵乘法张量的秩至多为 `r`。
/-- 特化保持三条边长和加数的数目。

英文原文：Specialization preserves all three side lengths and the number of summands.
-/
theorem specializeRank {F : Type*} [Field F] {i j k r : ℕ} (h : RankLE F i j k r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), RankLE K i j k r := by
  obtain ⟨K, _, _, _, hK⟩ := finiteTypeRank (Int.castRingHom F) h
  exact ⟨K, inferInstance, finite_field_of_finiteType K, hK⟩

-- 读法：存在 `(L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Module.Finite F L)`，在 `L` 上，三个尺寸为 `i`、`j`、`k` 的矩阵乘法张量的秩至多为 `r`。
/-- 若一个秩上界在某个任意扩域上成立，则它在某个有限扩域上也成立。

英文原文：A rank bound over an arbitrary extension holds over some finite extension.
-/
theorem finiteExtensionRank {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
    {i j k r : ℕ} (h : RankLE K i j k r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Module.Finite F L), RankLE L i j k r := by
  obtain ⟨L, _, _, _, hL⟩ := finiteTypeRank (algebraMap F K) h
  exact ⟨L, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing F L, hL⟩

end Rectangle

-- 读法：要证明的命题是 `∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L), RankLE L n r`。使用 `Rectangle.finiteTypeRank` 给出的结论。
theorem finiteTypeRank {R : Type u} {K : Type v} [CommRing R] [Field K]
    (φ : R →+* K) {n r : ℕ} (h : RankLE K n r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra.FiniteType R L),
      RankLE L n r :=
  Rectangle.finiteTypeRank φ h

-- 读法：存在 `(k : Type) (_ : Field k) (_ : Finite k)`，在 `k` 上，边长为 `n` 的矩阵乘法张量的秩至多为 `r`。使用 `Rectangle.specializeRank` 给出的结论。
theorem specializeRank {F : Type*} [Field F] {n r : ℕ} (h : RankLE F n r) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), RankLE k n r :=
  Rectangle.specializeRank h

-- 读法：存在 `(L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Module.Finite F L)`，在 `L` 上，边长为 `n` 的矩阵乘法张量的秩至多为 `r`。使用 `Rectangle.finiteExtensionRank` 给出的结论。
theorem finiteExtensionRank {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
    {n r : ℕ} (h : RankLE K n r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Module.Finite F L), RankLE L n r :=
  Rectangle.finiteExtensionRank h

end OAI.LinearAlgebra.MatrixExponent
