-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Cuts
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Jacobian
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Root
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi.Radial

universe u

/-!
# 代数闭域上多项式素理想的乘积

在模去块方程的商环中工作。由有限线性消元和零点定理，可将一个块的有理点替换为该商环中的任意解。因此，即使尚未知理想之和为根理想，也可用在乘积上消失来判定是否属于该理想之和。

**英文原文**

Products of prime polynomial ideals over an algebraically closed field

Work in the quotient by the block equations. Finite linear elimination
and the Nullstellensatz permit replacing a rational point of a block
by any solution in this quotient. Thus vanishing on the product detects
membership in the sum of the ideals, before knowing it is radical.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

variable {K J : Type*} [Field K] {W : J → Type*}

-- 读法：`productIdeal` 的取值由 `⨆ j, (P j).map (rename (Sigma.mk j))` 给出。
def productIdeal (P : ∀ j, Ideal (MvPolynomial (W j) K)) : Ideal (MvPolynomial (Sigma W) K) :=
  ⨆ j, (P j).map (rename (Sigma.mk j))

namespace BlockProduct
variable {Z R : Type*} [CommRing R] [Algebra K R]

-- 读法：存在 `x ∈ zeroLocus K P`，`aeval x p` 不等于 `0`。
private theorem point [IsAlgClosed K] [Finite Z] (P : Ideal (MvPolynomial Z K)) [P.IsPrime]
    (p : MvPolynomial Z K) (hp : p ∉ P) : ∃ x ∈ zeroLocus K P, aeval x p ≠ 0 := by
  by_contra! h
  apply hp
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) P]
  exact h

-- 读法：`specialize` 的取值由 `(Algebra.ofId K R).comp (aeval x)` 给出。
private def specialize (x : Z → K) : MvPolynomial Z K →ₐ[K] R :=
  (Algebra.ofId K R).comp (aeval x)

-- 读法：结论为 `∑ i, φ (u i) * w i = 0`。对 `n` 作归纳。
/-- 改变一个独立变量块的求值。每次取使某一系数非零的点代入，逐个消去系数。

英文原文：Change the evaluation of an isolated block of variables. Eliminate
one coefficient at a time by evaluating it at a point where it survives.
-/
private theorem eliminate [IsAlgClosed K] [Finite Z] (P : Ideal (MvPolynomial Z K)) [P.IsPrime]
    (φ : MvPolynomial Z K →ₐ[K] R) (hφ : ∀ u ∈ P, φ u = 0)
    (n : ℕ) (u : Fin n → MvPolynomial Z K) (w : Fin n → R)
    (h : ∀ x ∈ zeroLocus K P, ∑ i, specialize x (u i) * w i = 0) :
    ∑ i, φ (u i) * w i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hm : u 0 ∈ P
    · rw [Fin.sum_univ_succ, hφ _ hm, zero_mul, zero_add]
      apply ih
      intro x hx
      have he : specialize (R := R) x (u 0) = 0 := by
        change algebraMap K R (aeval x (u 0)) = 0
        rw [hx _ hm, map_zero]
      simpa only [Fin.sum_univ_succ, he, zero_mul, zero_add] using h x hx
    -- 推导：从 `point P _ hm` 中取出 `x, hx, hn`。
    obtain ⟨x, hx, hn⟩ := point P _ hm
    let c (i : Fin n) := -(aeval x (u 0))⁻¹ * aeval x (u i.succ)
    have e : w 0 = ∑ i : Fin n, algebraMap K R (c i) * w i.succ := by
      have H := h x hx
      rw [Fin.sum_univ_succ] at H
      simp only [c, map_mul, map_neg, mul_assoc, ← Finset.mul_sum]
      change w 0 = -algebraMap K R (aeval x (u 0))⁻¹ * ∑ i : Fin n, specialize x (u i.succ) * w i.succ
      rw [eq_neg_of_add_eq_zero_right H, neg_mul_neg, ← mul_assoc]
      change w 0 = (algebraMap K R (aeval x (u 0))⁻¹ * algebraMap K R (aeval x (u 0))) * w 0
      rw [← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]
    let u' (i : Fin n) := u 0 * C (c i) + u i.succ
    have H (ψ : MvPolynomial Z K →ₐ[K] R) :
        (∑ i, ψ (u i) * w i) = ∑ i, ψ (u' i) * w i.succ := by
      rw [Fin.sum_univ_succ, e, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show u' i = _ from rfl, map_add ψ, map_mul ψ, ← algebraMap_eq, ψ.commutes, add_mul, mul_assoc]
    rw [H]
    exact ih _ _ fun z hz => (H _).symm.trans (h z hz)

-- 读法：`total` 的取值由 `aeval (fun i => x i.1 i.2)` 给出。
private def total (x : ∀ j, W j → R) : MvPolynomial (Sigma W) K →ₐ[K] R :=
  aeval (fun i => x i.1 i.2)

variable [DecidableEq J]

-- 读法：`plug` 的取值由 `total (K := K) (Function.update x j (fun v => φ (X v)))` 给出。
private def plug (x : ∀ j, W j → R) (j : J) (φ : MvPolynomial (W j) K →ₐ[K] R) :=
  total (K := K) (Function.update x j (fun v => φ (X v)))

-- 读法：存在 `(n : ℕ) (u : Fin n → MvPolynomial (W j) K) (w : Fin n → R)`，对每个 `φ : MvPolynomial (W j) K →ₐ[K] R`，`plug x j φ p` 等于 `∑ i, φ (u i) * w i`。对 `p` 作归纳，采用 `MvPolynomial.induction_on` 的归纳原则。
private theorem expand (x : ∀ j, W j → R) (j : J) (p : MvPolynomial (Sigma W) K) :
    ∃ (n : ℕ) (u : Fin n → MvPolynomial (W j) K) (w : Fin n → R),
      ∀ φ : MvPolynomial (W j) K →ₐ[K] R, plug x j φ p = ∑ i, φ (u i) * w i := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact ⟨1, fun _ => 1, fun _ => algebraMap K R a, fun _ => by simp [plug, total]⟩
  | add a b ha hb =>
    obtain ⟨n, u, w, hu⟩ := ha
    obtain ⟨m, v, t, hv⟩ := hb
    refine ⟨n + m, Fin.append u v, Fin.append w t, fun φ => ?_⟩
    rw [map_add, hu, hv, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  | mul_X a i ha =>
    -- 推导：从 `ha` 中取出 `n, u, w, hu`。
    obtain ⟨n, u, w, hu⟩ := ha
    obtain ⟨i, v⟩ := i
    by_cases h : i = j
    · subst i
      refine ⟨n, fun i => u i * X v, w, fun φ => ?_⟩
      rw [map_mul, hu, Finset.sum_mul]
      simp only [plug, total, aeval_X, Function.update_self, map_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_right_comm _ _ _
    · refine ⟨n, u, fun t => w t * x i v, fun φ => ?_⟩
      rw [map_mul, hu, Finset.sum_mul]
      simp only [plug, total, aeval_X, Function.update_of_ne h, mul_assoc]

variable (P : ∀ j, Ideal (MvPolynomial (W j) K))

-- 读法：在后续公式中，`Points` 是 `∀ j, ↥(zeroLocus K (P j))` 的缩写。
private abbrev Points := ∀ j, ↥(zeroLocus K (P j))

-- 读法：`ev` 的取值由 `total (fun j => (x j).val)` 给出。
private def ev (x : Points P) : MvPolynomial (Sigma W) K →ₐ[K] K :=
  total (fun j => (x j).val)

omit [DecidableEq J] in
-- 读法：`ev P x (rename (Sigma.mk j) f)` 等于 `aeval (x j).val f`。使用 `aeval_rename` 给出的结论。
private theorem ev_rename (x : Points P) (j : J) (f : MvPolynomial (W j) K) :
    ev P x (rename (Sigma.mk j) f) = aeval (x j).val f := aeval_rename _ _ _

omit [DecidableEq J] in
-- 读法：`ev P x p` 等于 `0`。这里调用 `ev_rename`。
private theorem ev_zero (x : Points P) {p : MvPolynomial (Sigma W) K} (hp : p ∈ productIdeal P) :
    ev P x p = 0 := by
  have h : productIdeal P ≤ RingHom.ker (ev P x) := by
    refine iSup_le fun j => Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
    exact (ev_rename P x j f).trans ((x j).property f hf)
  exact h hp

variable [IsAlgClosed K] [∀ j, Finite (W j)] (hP : ∀ j, (P j).IsPrime)
include hP

omit [DecidableEq J] in
-- 读法：`(Points P)` 有元素。
private theorem inhabited : Nonempty (Points P) := by
  have h (j : J) : (zeroLocus K (P j)).Nonempty := by
    let _ := hP j
    obtain ⟨x, hx, _⟩ := point (P j) 1 (hP j).one_notMem
    exact ⟨x, hx⟩
  exact ⟨fun j => ⟨(h j).choose, (h j).choose_spec⟩⟩

variable [Fintype J]

-- 读法：`p` 属于 `productIdeal P`。
private theorem vanishes (p : MvPolynomial (Sigma W) K) (hp : ∀ x, ev P x p = 0) :
    p ∈ productIdeal P := by
  let R := MvPolynomial (Sigma W) K ⧸ productIdeal P
  let f := Ideal.Quotient.mkₐ K (productIdeal P)
  let φ (j : J) := f.comp (rename (Sigma.mk j))
  have hφ (j : J) (p : MvPolynomial (W j) K) (h : p ∈ P j) : φ j p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((le_iSup (fun j => (P j).map (rename (Sigma.mk j))) j) (Ideal.mem_map_of_mem _ h))
  let X' (s : Finset J) (x : Points P) (j : J) (t : W j) : R :=
    if j ∈ s then φ j (X t) else algebraMap K R ((x j).val t)
  have H (s : Finset J) (x : Points P) : total (X' s x) p = 0 := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      -- 推导：记下中间结论 `e`：`total (X' ∅ x) = (Algebra.ofId K R).comp (ev P x)`。
      have e : total (X' ∅ x) = (Algebra.ofId K R).comp (ev P x) := by
        apply algHom_ext
        rintro ⟨j, t⟩
        simp [total, ev, X']
      rw [e, AlgHom.comp_apply, hp, map_zero]
    | @insert j s hj ih =>
      let _ := hP j
      obtain ⟨n, u, w, he⟩ := expand (X' s x) j p
      have e : total (X' (insert j s) x) = plug (X' s x) j (φ j) := by
        unfold plug
        apply congrArg
        funext k t
        by_cases h : k = j
        · subst k; simp [X']
        · simp [X', h]
      rw [e, he]
      refine eliminate (P j) (φ j) (hφ j) n u w fun y hy => ?_
      rw [← he]
      let z := Function.update x j (⟨y, hy⟩ : zeroLocus K (P j))
      -- 推导：记下中间结论 `h`：`plug (X' s x) j (specialize y) = total (X' s z)`。
      have h : plug (X' s x) j (specialize y) = total (X' s z) := by
        unfold plug
        apply congrArg
        funext k t
        by_cases h : k = j
        · subst k; simp [X', z, hj, specialize]
        · simp [X', z, h]
      rw [h, ih]
  obtain ⟨x⟩ := inhabited P hP
  have e : total (X' Finset.univ x) = f := by
    apply algHom_ext
    rintro ⟨j, t⟩
    simp [X', total, φ]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f p = 0
  rw [← e, H]

omit [IsAlgClosed K] [∀ j, Finite (W j)] [Fintype J] hP in
-- 读法：存在 `q : MvPolynomial (W j) K`，对每个 `y : zeroLocus K (P j)`，`ev P (Function.update x j y) p` 等于 `aeval y.val q`。用函数外延性比较等号两侧在 `k t` 处的取值。
private theorem section_eval (x : Points P) (j : J) (p : MvPolynomial (Sigma W) K) :
    ∃ q : MvPolynomial (W j) K, ∀ y : zeroLocus K (P j),
      ev P (Function.update x j y) p = aeval y.val q := by
  obtain ⟨n, u, w, he⟩ := expand (fun i => (x i).val) j p
  refine ⟨∑ i, u i * C (w i), fun y => ?_⟩
  have e : ev P (Function.update x j y) = plug (fun i => (x i).val) j (aeval y.val) := by
    unfold ev plug
    apply congrArg
    funext k t
    by_cases h : k = j
    · subst k; simp
    · simp [h]
  rw [e, he]
  simp

-- 读法：存在 `z`，`ev P z (p * q)` 不等于 `0`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
/-- 逐块同时移动两个非零性的见证。

英文原文：Move a pair of nonvanishing witnesses together, one block at a time.
-/
private theorem common (p q : MvPolynomial (Sigma W) K) (x y : Points P)
    (hx : ev P x p ≠ 0) (hy : ev P y q ≠ 0) : ∃ z, ev P z (p * q) ≠ 0 := by
  have H (s : Finset J) : ∃ x y : Points P,
      ev P x p ≠ 0 ∧ ev P y q ≠ 0 ∧ ∀ i ∈ s, x i = y i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨x, y, hx, hy, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨x, y, hx, hy, e⟩ := ih
      obtain ⟨u, hu⟩ := section_eval P x j p
      obtain ⟨w, hw⟩ := section_eval P y j q
      have h₁ : u ∉ P j := by
        intro h
        apply hx
        simpa using (hu (x j)).trans ((x j).property _ h)
      have h₂ : w ∉ P j := by
        intro h
        apply hy
        simpa using (hw (y j)).trans ((y j).property _ h)
      let _ := hP j
      -- 推导：从 `point (P j) (u * w) (fun h => ((hP j).mem_or_mem h).elim h₁ h₂)` 中取出 `z, hz, he`。
      obtain ⟨z, hz, he⟩ := point (P j) (u * w) (fun h => ((hP j).mem_or_mem h).elim h₁ h₂)
      let a : zeroLocus K (P j) := ⟨z, hz⟩
      rw [map_mul] at he
      refine ⟨Function.update x j a, Function.update y j a, ?_, ?_, ?_⟩
      · rw [hu]; exact left_ne_zero_of_mul he
      · rw [hw]; exact right_ne_zero_of_mul he
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · have h : i ≠ j := fun he => hj (he ▸ hi)
          simpa [h] using e i hi
  -- 推导：从 `H Finset.univ` 中取出 `x, y, hx, hy, e`。
  obtain ⟨x, y, hx, hy, e⟩ := H Finset.univ
  have h : x = y := funext fun i => e i (Finset.mem_univ _)
  subst y
  exact ⟨x, by rw [map_mul]; exact mul_ne_zero hx hy⟩

end BlockProduct
open BlockProduct
variable [IsAlgClosed K] [∀ j, Finite (W j)] (P : ∀ j, Ideal (MvPolynomial (W j) K))
  (hP : ∀ j, (P j).IsPrime)

include hP

-- 读法：要证明的命题是 `(productIdeal P).IsPrime`。
/-- 位于互不相交的多项式变量块上的素理想之和仍是素理想。

英文原文：The sum of prime ideals on disjoint polynomial blocks is prime.
-/
theorem productIdeal_prime [Finite J] : (productIdeal P).IsPrime := by
  classical
  let _ := Fintype.ofFinite J
  obtain ⟨x⟩ := inhabited P hP
  constructor
  · intro h
    have hh := ev_zero P x (show 1 ∈ productIdeal P by rw [h]; trivial)
    simp at hh
  · intro p q h
    by_contra! hn
    obtain ⟨x, hx⟩ := not_forall.mp (mt (vanishes P hP p) hn.1)
    obtain ⟨y, hy⟩ := not_forall.mp (mt (vanishes P hP q) hn.2)
    obtain ⟨z, hz⟩ := common P hP p q x y hx hy
    exact hz (ev_zero P z h)

-- 读法：`(productIdeal P).comap (rename (Sigma.mk j))` 等于 `P j`。
/-- 乘积的方程不会在单个块内引入新的关系。

英文原文：The product equations impose no new relations within a single block.
-/
theorem productIdeal_comap (j : J) : (productIdeal P).comap (rename (Sigma.mk j)) = P j := by
  classical
  let _ := hP j
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mp (le_iSup (fun j => (P j).map (rename (Sigma.mk j))) j))
  intro p hp
  by_contra h
  obtain ⟨z, hz, hn⟩ := point (P j) p h
  obtain ⟨x⟩ := inhabited P hP
  let y := Function.update x j (⟨z, hz⟩ : zeroLocus K (P j))
  have he := ev_zero P y (show rename (Sigma.mk j) p ∈ productIdeal P from hp)
  rw [ev_rename] at he
  apply hn
  simpa [y] using he

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 具有共享坐标的方程组的局部维数

拆开公共坐标，并要求每份副本等于第一份。若每个因子都有一条经过该点的长素理想链，它们的乘积就会有一条长度超过这些对角方程数目的链。因此有一个因子只有短链，可在上面作有理截取。

**英文原文**

Local dimension of systems with shared coordinates

Separate the common coordinates and impose equality to the first
copy. If every factor had a long prime chain through the point,
their product would have a chain longer than the number of these
diagonal equations. The remaining short factor admits rational cuts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] {J Z : Type} {W : J → Type}

-- 读法：`(productIdeal (K := K) (W := W))` 是单调不减的。这里调用 `iSup_mono`。
private theorem mono_product : Monotone (productIdeal (K := K) (W := W)) := by
  intro p q h
  exact iSup_mono fun i => Ideal.map_mono (h i)

-- 读法：`productIdeal (fun j => maxPoint (w j))` 不超过 `maxPoint (fun t : Sigma W => w t.1 t.2)`。
private theorem point_product (w : ∀ j, W j → K) :
    productIdeal (fun j => maxPoint (w j)) ≤ maxPoint (fun t : Sigma W => w t.1 t.2) := by
  refine iSup_le fun j => Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
  change eval (fun t : Sigma W => w t.1 t.2) (rename (Sigma.mk j) p) = 0
  rw [eval_rename]
  exact hp

-- 读法：`Fintype.card J * n` 不超过 `Fintype.card B`。用函数外延性比较等号两侧在 `j` 处的取值。
private theorem lengths [IsAlgClosed K] [Fintype J] [∀ j, Fintype (W j)]
    (I : ∀ j, Ideal (MvPolynomial (W j) K)) (w : ∀ j, W j → K) {B : Type} [Fintype B]
    (y : B → MvPolynomial (Sigma W) K)
    (h : Isolated (fun t : Sigma W => w t.1 t.2) (productIdeal I ⊔ Ideal.span (Set.range y)))
    {n : ℕ} (hc : ∀ j, ∃ p, I j ≤ p ∧ Chain p (maxPoint (w j)) n) :
    Fintype.card J * n ≤ Fintype.card B := by
  choose p hp hchain using hc
  have he (u v : ∀ j, Ideal (MvPolynomial (W j) K))
      (hu : ∀ j, (u j).IsPrime) (hv : ∀ j, (v j).IsPrime) (he : productIdeal u = productIdeal v) : u = v := by
    funext j
    rw [← productIdeal_comap u hu j, ← productIdeal_comap v hv j, he]
  have chain := Chain.product productIdeal mono_product (fun u hu => productIdeal_prime u hu) he
    (fun j => RingHom.ker_isPrime (eval (w j))) hchain
  exact (chain.weaken (point_product w)).equations y h (mono_product hp)

-- 读法：存在 `d ≤ N`，`N ≤ L * (N - d)` 与 `(L - 1) * N < L * (d + 1)` 同时成立。
private theorem threshold (L N : ℕ) (h : 0 < L) :
    ∃ d ≤ N, N ≤ L * (N - d) ∧ (L - 1) * N < L * (d + 1) := by
  let A := (L - 1) * N
  let d := A / L
  have hd : L * d ≤ A := Nat.mul_div_le A L
  have ht : A < (d + 1) * L := (Nat.div_lt_iff_lt_mul h).mp (Nat.lt_succ_self d)
  have ha : A + N = L * N := by
    unfold A
    rw [← Nat.succ_mul, show (L - 1).succ = L by omega]
  refine ⟨d, Nat.le_of_mul_le_mul_left (hd.trans (by omega)) h, ?_, ?_⟩
  · rw [Nat.mul_sub_left_distrib]; omega
  · rwa [mul_comm L]

-- 读法：这里调用 `hmax.not_ge`。
theorem local_cut [CharZero K] [IsAlgClosed K] [Fintype J] [Fintype Z]
    [∀ j, Fintype (W j)] [Nonempty J]
    (I : ∀ j, Ideal (MvPolynomial (Z ⊕ W j) K)) (β : Z → K) (w : ∀ j, W j → K)
    (joint : Isolated (Sum.elim β (fun x => w x.1 x.2)) (diagonalIdeal I))
    (fiber : ∀ j, Isolated (Sum.elim β (w j)) (I j ⊔ Ideal.span (Set.range (offset β)))) :
    ∃ (j : J) (d : ℕ), d ≤ Fintype.card Z ∧ Fintype.card Z ≤ Fintype.card J * (Fintype.card Z - d) ∧
      ∃ A : Fin d → Z → ℚ, Isolated (Sum.elim β (w j))
        (I j ⊔ Ideal.span (Set.range (fun t => comb (offset β) (A t)))) := by
  obtain ⟨d, hd, hsize, hmax⟩ := threshold (Fintype.card J) (Fintype.card Z) Fintype.card_pos
  have ex : ∃ j, ∀ p, I j ≤ p → ¬Chain p (maxPoint (Sum.elim β (w j))) (d + 1) := by
    by_contra! hh
    let k := Classical.arbitrary J
    have hc := lengths I (fun j => Sum.elim β (w j)) (difference k) (joint.separate k) hh
    have he : Fintype.card {j // j ≠ k} = Fintype.card J - 1 := by simp
    rw [Fintype.card_prod, he] at hc
    exact hmax.not_ge hc
  obtain ⟨j, hj⟩ := ex
  exact ⟨j, d, hd, hsize, cut _ _ (fiber j) hj⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 避开一个无限子域的坐标投影

由 Chevalley 定理，像在一元多项式环的素谱中是可构造集。零点定理确定它的有理点。每个基本可构造部分的有理点集都是有限集或余有限集。

**英文原文**

A coordinate projection missing an infinite subfield

Chevalley's theorem makes the image constructible in the prime spectrum
of the polynomial ring in one variable. The Nullstellensatz identifies
its rational points. Each basic constructible piece has finite or
cofinite rational points.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open PrimeSpectrum Topology
variable {K W : Type*} [Field K]

-- 读法：`polyPoint` 的取值由 `⟨RingHom.ker (Polynomial.evalRingHom x), RingHom.ker_isPrime _⟩` 给出。
private def polyPoint (x : K) : PrimeSpectrum (Polynomial K) :=
  ⟨RingHom.ker (Polynomial.evalRingHom x), RingHom.ker_isPrime _⟩

-- 读法：`coord` 的取值由 `(Polynomial.aeval (MvPolynomial.X i)).toRingHom` 给出。
private def coord (i : W) : Polynomial K →+* MvPolynomial W K :=
  (Polynomial.aeval (MvPolynomial.X i)).toRingHom

-- 读法：要证明的命题是 `(coord (K := K) i).FinitePresentation`。这里调用 `RingHom.FinitePresentation.of_finiteType.mp`。
private theorem presented [Finite W] (i : W) : (coord (K := K) i).FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap K (Polynomial K))
  have he : (coord i).comp (algebraMap K (Polynomial K)) = algebraMap K (MvPolynomial W K) := by
    ext1 t
    exact AlgHom.commutes (Polynomial.aeval (MvPolynomial.X i : MvPolynomial W K)) t
  rw [he, RingHom.finiteType_algebraMap]
  infer_instance

-- 读法：`MvPolynomial.eval x (coord i f)` 等于 `f.eval (x i)`。这里调用 `h.symm`。
private theorem eval_coord (i : W) (x : W → K) (f : Polynomial K) :
    MvPolynomial.eval x (coord i f) = f.eval (x i) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval x) (MvPolynomial.X i) f
  simpa [coord, MvPolynomial.aeval_eq_eval] using h.symm

-- 读法：`polyPoint t ∈ comap (coord i) '' zeroLocus P` 与 `∃ x : W → K, (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ x i = t` 等价。
private theorem projected [Finite W] [IsAlgClosed K] (P : Set (MvPolynomial W K)) (i : W) (t : K) :
    polyPoint t ∈ comap (coord i) '' zeroLocus P ↔
      ∃ x : W → K, (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ x i = t := by
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hm
    have h (p) (hp : p ∈ q.asIdeal) : MvPolynomial.eval x p = 0 := by
      have h := hle hp
      rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] at h
      exact h
    refine ⟨x, fun p hp => h p (hq hp), ?_⟩
    let f := Polynomial.X - Polynomial.C t
    -- 推导：记下中间结论 `hf`：`f ∈ (comap (coord i) q).asIdeal`。
    have hf : f ∈ (comap (coord i) q).asIdeal := by
      rw [he]
      change f.eval t = 0
      simp [f]
    have hh := h (coord i f) hf
    simpa [eval_coord, f, sub_eq_zero] using hh
  · rintro ⟨x, hx, rfl⟩
    let q : PrimeSpectrum (MvPolynomial W K) :=
      ⟨RingHom.ker (MvPolynomial.eval x), RingHom.ker_isPrime _⟩
    refine ⟨q, fun p hp => hx p hp, PrimeSpectrum.ext ?_⟩
    ext f
    change MvPolynomial.eval x (coord i f) = 0 ↔ f.eval (x i) = 0
    rw [eval_coord]

-- 读法：要证明的命题是 `IsConstructible (comap (coord i) '' zeroLocus P)`。这里调用 `isConstructible_comap_image`。
private theorem constructible_projection [Finite W] (P : Set (MvPolynomial W K)) (i : W) :
    IsConstructible (comap (coord i) '' zeroLocus P) := by
  apply isConstructible_comap_image (presented i)
  have hc := (isClosed_zeroLocus P).isOpen_compl
  have h : IsRetrocompact (zeroLocus P)ᶜ := fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _
  simpa using (h.isConstructible hc).compl

-- 读法：要证明的命题是 `(polyPoint ⁻¹' s.toSet).Finite`。按 `∃ j, s.g j ≠ 0` 成立与否分情况。
private theorem basic_thin (s : BasicConstructibleSetData (Polynomial K)) (T : Set K)
    (ht : T.Infinite) (h : ∀ x ∈ T, polyPoint x ∉ s.toSet) :
    (polyPoint ⁻¹' s.toSet).Finite := by
  classical
  by_cases hx : ∃ j, s.g j ≠ 0
  · obtain ⟨j, hj⟩ := hx
    apply (Polynomial.finite_setOfPred_isRoot hj).subset
    intro y hy
    exact hy.1 ⟨j, rfl⟩
  push Not at hx
  -- 推导：记下中间结论 `hf`：`s.f = 0`。
  have hf : s.f = 0 := by
    by_contra he
    apply ht
    refine (Polynomial.finite_setOfPred_isRoot he).subset (fun x hxt => ?_)
    by_contra hn
    apply h x hxt
    constructor
    · rintro _ ⟨j, rfl⟩
      rw [hx]
      exact (polyPoint x).asIdeal.zero_mem
    · exact fun hh => hn (hh (Set.mem_singleton _))
  apply Set.finite_empty.subset
  intro x h
  apply h.2
  rintro _ rfl
  rw [hf]
  exact (polyPoint x).asIdeal.zero_mem

-- 读法：要证明的命题是 `{t | ∃ x : W → K, (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ x i = t}.Finite`。这里调用 `D.finite_toSet.biUnion`。
/-- 若有理点的投影避开一个无穷集，则被投影的坐标只取有限多个值。

英文原文：If the projected rational points avoid an infinite set, their
coordinate assumes only finitely many values.
-/
theorem finite_projection [Finite W] [IsAlgClosed K] (P : Set (MvPolynomial W K)) (i : W)
    (T : Set K) (ht : T.Infinite) (ha : ∀ x, (∀ p ∈ P, MvPolynomial.eval x p = 0) → x i ∉ T) :
    {t | ∃ x : W → K, (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ x i = t}.Finite := by
  obtain ⟨D, hD⟩ := exists_constructibleSetData_iff.mpr (constructible_projection P i)
  have hs : (polyPoint ⁻¹' D.toSet).Finite := by
    simp only [ConstructibleSetData.toSet, Set.preimage_iUnion]
    apply D.finite_toSet.biUnion
    intro s hs
    apply basic_thin s T ht
    intro t ht' he
    have hz : polyPoint t ∈ D.toSet := Set.mem_iUnion₂.mpr ⟨s, hs, he⟩
    rw [hD, projected] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ha x hx ht'
  rw [hD] at hs
  exact hs.subset (fun t hx => (projected P i t).mpr hx)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 沿一般射线得到的域

将缩放参数特化为一即可证明独立性。在参数生成的域上，每个导子都把给定的多项式值映为零，再由雅可比矩阵可知该导子也把所有坐标生成元映为零。零特征下，这排除了任何额外的超越元。

**英文原文**

The field along a generic ray

Specializing the scaling parameter to one proves independence.
Over the field generated by the parameter, every derivation kills
the given polynomial values. The Jacobian then forces it to kill
all the generating coordinates. In characteristic zero this excludes
any further transcendental element.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
variable {K L E : Type u} [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  {σ : Type} {c : σ → L} (hc : AlgebraicIndependent K c)
  {t : E} (ht : Transcendental L t) {a : σ → E} {G : σ → MvPolynomial σ K}
  (h : ∀ i, aeval a (G i) = t * algebraMap L E (c i))

include hc ht h in
-- 读法：要证明的命题是 `AlgebraicIndependent K (fun i => aeval a (G i))`。这里调用 `mul_comm`。
theorem independent_ray : AlgebraicIndependent K (fun i => aeval a (G i)) := by
  let P := aeval (R := K) (fun i => Polynomial.X * Polynomial.C (c i))
  have param : ((Polynomial.aeval t).restrictScalars K).comp P =
      aeval (fun i => aeval a (G i)) := by
    ext i
    simp [P, h]
    exact mul_comm _ _
  have one : ((Polynomial.aeval (1 : L)).restrictScalars K).comp P = aeval c := by
    ext i
    simp [P]
  rw [algebraicIndependent_iff_injective_aeval, ← param]
  intro x y he
  have he' : P x = P y := (transcendental_iff_injective.mp ht) he
  apply algebraicIndependent_iff_injective_aeval.mp hc
  rw [← one]
  exact congrArg (Polynomial.aeval (1 : L)) he'

include hc ht h in
-- 读法：要证明的命题是 `Algebra.IsAlgebraic (IntermediateField.adjoin L {t}) E`。
theorem algebraic_ray [Fintype σ] [CharZero E]
    (ha : IntermediateField.adjoin L (insert t (Set.range a)) = ⊤) :
    Algebra.IsAlgebraic (IntermediateField.adjoin L {t}) E := by
  classical
  let M := IntermediateField.adjoin L {t}
  have unit := isUnit_jacobian G a (independent_ray hc ht h)
  constructor
  intro z
  by_contra hz
  have ind : AlgebraicIndependent M (fun _ : Unit => z) := algebraicIndependent_unique_type_iff.mpr hz
  -- 推导：从 `derivation_of_independent ind (fun _ => 1)` 中取出 `d, hd`。
  obtain ⟨d, hd⟩ := derivation_of_independent ind (fun _ => 1)
  let D := d.restrictScalars L
  have hdt : D t = 0 := d.map_algebraMap (⟨t, IntermediateField.subset_adjoin L _ (by simp)⟩ : M)
  have eval (i : σ) : D (aeval a (G i)) = 0 := by
    rw [h, D.leibniz, hdt, D.map_algebraMap, smul_zero, smul_zero, add_zero]
  have killed : (fun i => D (a i)) = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr unit
    rw [Matrix.mulVec_zero]
    funext i
    exact (derivation_aeval (D.restrictScalars K) a (G i)).symm.trans (eval i)
  have zero (z : E) (hm : z ∈ IntermediateField.adjoin L (insert t (Set.range a))) : D z = 0 := by
    induction hm using IntermediateField.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | ⟨j, rfl⟩
      · exact hdt
      · exact congrFun killed j
    | algebraMap z => exact D.map_algebraMap z
    | add z w _ _ hz hw => rw [map_add, hz, hw, add_zero]
    | inv z _ hz => rw [D.leibniz_inv, hz, smul_zero]
    | mul z w _ _ hz hw => rw [D.leibniz, hz, hw, smul_zero, smul_zero, add_zero]
  exact one_ne_zero ((hd ()).symm.trans (zero z (by rw [ha]; trivial)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 用基域上的坐标方程截得有限非空切片

**英文原文**

A finite, nonempty slice by base-field coordinate equations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped Classical
variable {F K W : Type*} [Field F] [Field K] [Algebra F K]

-- 读法：`slice` 的取值由 `{x | (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ ∀ j t, b j = some t → x j = algebraMap F K t}` 给出。
def slice (P : Set (MvPolynomial W K)) (b : W → Option F) : Set (W → K) :=
  {x | (∀ p ∈ P, MvPolynomial.eval x p = 0) ∧ ∀ j t, b j = some t → x j = algebraMap F K t}

-- 读法：`equations` 的取值由 `P ∪ {p | ∃ j t, b j = some t ∧ p = MvPolynomial.X j - MvPolynomial.C (algebraMap F K t)}` 给出。
private def equations (P : Set (MvPolynomial W K)) (b : W → Option F) :=
  P ∪ {p | ∃ j t, b j = some t ∧ p = MvPolynomial.X j - MvPolynomial.C (algebraMap F K t)}

-- 读法：`(∀ p ∈ equations P b, MvPolynomial.eval x p = 0)` 与 `x ∈ slice P b` 等价。
private theorem equations_iff (P : Set (MvPolynomial W K)) (b : W → Option F) (x : W → K) :
    (∀ p ∈ equations P b, MvPolynomial.eval x p = 0) ↔ x ∈ slice P b := by
  constructor
  · intro h
    refine ⟨fun p hp => h _ (.inl hp), fun j t ht => ?_⟩
    simpa [sub_eq_zero] using h _ (.inr ⟨j, t, ht, rfl⟩)
  · rintro ⟨h, h'⟩ p (hp|⟨j, t, ht, rfl⟩)
    · exact h _ hp
    · simp [h' j t ht]

-- 读法：存在 `b' : W → Option F`，`(slice P b').Nonempty` 与 `slice P b' ⊆ slice P b ∧ ((fun x => x i) '' slice P b').Finite` 同时成立。按 `∃ x ∈ slice P b, ∃ t, x i = algebraMap F K t` 成立与否分情况。
private theorem single_slice [Finite W] [Infinite F] [IsAlgClosed K]
    (P : Set (MvPolynomial W K)) (b : W → Option F) (hb : (slice P b).Nonempty) (i : W) :
    ∃ b' : W → Option F, (slice P b').Nonempty ∧ slice P b' ⊆ slice P b ∧
      ((fun x => x i) '' slice P b').Finite := by
  by_cases hh : ∃ x ∈ slice P b, ∃ t, x i = algebraMap F K t
  · obtain ⟨x, hx, t, ht⟩ := hh
    let b' := Function.update b i (some t)
    have he (y : W → K) (hy : y ∈ slice P b') : y i = x i :=
      (hy.2 i t (by simp [b'])).trans ht.symm
    refine ⟨b', ⟨x, hx.1, ?_⟩, ?_, ?_⟩
    · intro j s hs
      by_cases hj : j = i
      · subst j
        have : t = s := by simpa [b'] using hs
        rwa [← this]
      · exact hx.2 j s (by simpa [b', hj] using hs)
    · intro y hy
      refine ⟨hy.1, fun j s hs => ?_⟩
      by_cases hj : j = i
      · subst j; exact (he y hy).trans (hx.2 i s hs)
      · exact hy.2 j s (by simpa [b', hj] using hs)
    · apply (Set.finite_singleton (x i)).subset
      rintro _ ⟨y, hy, rfl⟩
      exact he y hy
  · refine ⟨b, hb, Set.Subset.rfl, ?_⟩
    have hp := finite_projection (equations P b) i (Set.range (algebraMap F K))
      (Set.infinite_range_of_injective (algebraMap F K).injective) (by
        rintro x hx ⟨t, ht⟩
        exact hh ⟨x, (equations_iff P b x).mp hx, t, ht.symm⟩)
    refine hp.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (equations_iff P b x).mpr hx, rfl⟩

-- 读法：存在 `b : W → Option F`，`(slice P b).Nonempty` 与 `(slice P b).Finite` 同时成立。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
/-- 只要可能就固定一个坐标。否则其投影避开整个无穷子域，因而已是有限集。后续截取只会缩小先前已控制的投影。

英文原文：Fix a coordinate when possible. Otherwise its projection omits the
entire infinite subfield, hence is already finite. Later cuts can only
shrink the projections already controlled.
-/
theorem finite_slice (F : Type*) [Field F] [Infinite F] {K W : Type*}
    [Field K] [Algebra F K] [IsAlgClosed K] [Finite W] (P : Set (MvPolynomial W K))
    (h : ∃ x, ∀ p ∈ P, MvPolynomial.eval x p = 0) :
    ∃ b : W → Option F, (slice P b).Nonempty ∧ (slice P b).Finite := by
  let _ := Fintype.ofFinite W
  have step (s : Finset W) : ∃ b : W → Option F, (slice P b).Nonempty ∧
      ∀ i ∈ s, ((fun x => x i) '' slice P b).Finite := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := h
      exact ⟨fun _ => none, ⟨x, hx, by simp⟩, by simp⟩
    | @insert i s _ ih =>
      -- 推导：从 `ih` 中取出 `b, hb, hs`。
      obtain ⟨b, hb, hs⟩ := ih
      obtain ⟨b', hb', hle, hi⟩ := single_slice P b hb i
      refine ⟨b', hb', fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hi
      · exact (hs j hj).subset (Set.image_mono hle)
  obtain ⟨b, hb, hs⟩ := step Finset.univ
  exact ⟨b, hb, (Set.Finite.pi' (fun j => hs j (Finset.mem_univ _))).subset
    (fun x hx _ => ⟨x, hx, rfl⟩)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

section
/-!
# 坐标轴附近的变分能量

**英文原文**

The variational energy near an axis
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Minimum Profile

variable {D : Vec → ℝ} {P : PairPrices} {v : Vec} {R : Vec → ℝ} {i j k : Fin 3}

-- 读法：这里调用 `le_of_mul_le_mul_left`。
private theorem Root.upper (h : Root D v R P) (hv : Positive v) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (x : Vec) (hx : Positive x) :
    R x ≤ intercept P (opposite v) (criticalWidth v) i +
      Profile.residual D v i * Real.log (x i / criticalWidth v i) +
      (v j)⁻¹ * Real.log (x j + x i) + (v k)⁻¹ * Real.log (x k + x i) := by
  have hu := critical_pos hv
  have hd := opposite_pos hv
  have h₁ := (h.family.envelope hu hd hij (hx i) (hx j)).2
  have h₂ := (h.family.envelope hu hd hik (hx i) (hx k)).2
  apply le_of_mul_le_mul_left _ (hd i)
  refine (h.chord _ _ _ hij hik hjk x hx).trans ?_
  refine (add_le_add (mul_le_mul_of_nonneg_left h₁ (inv_pos.mpr (hv j)).le)
    (mul_le_mul_of_nonneg_left h₂ (inv_pos.mpr (hv k)).le)).trans_eq ?_
  unfold model Profile.residual
  rw [opposite_eq v hij hik hjk]
  ring

-- 读法：`cost (near i r / v) x` 等于 `(v i)⁻¹ * x i + r * (v j)⁻¹ * x j + r * (v k)⁻¹ * x k`。
private theorem near_cost (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : ℝ) (x : Vec) :
    cost (near i r / v) x = (v i)⁻¹ * x i + r * (v j)⁻¹ * x j + r * (v k)⁻¹ * x k := by
  change mass _ = _
  rw [mass_eq _ hij hik hjk]
  simp only [Pi.div_apply, near, ite_true, ite_eq_right hij.symm, ite_eq_right hik.symm, div_eq_mul_inv, one_mul]

-- 读法：`b * Real.log (x / u) - a * x` 不超过 `b * Real.log (b / (a * u)) - b`。
private theorem scaled_max {u a b x : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    b * Real.log (x / u) - a * x ≤ b * Real.log (b / (a * u)) - b := by
  rw [Real.log_div hx.ne' hu.ne', ← div_div, Real.log_div (div_pos hb ha).ne' hu.ne']
  linarith only [log_max hb ha hx]

-- 读法：`Real.log x - r * x` 不超过 `-Real.log r - 1`。这里调用 `log_max`。
private theorem unit_max {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    Real.log x - r * x ≤ -Real.log r - 1 := by
  simpa only [one_mul, one_div, Real.log_inv] using log_max zero_lt_one hr hx

-- 读法：这里调用 `le_sub_iff_add_le.mp`。
theorem Root.axis_upper (h : Root D v R P) (hv : Positive v) (i : Fin 3)
    (hb : 0 < Profile.residual D v i) {r : ℝ} (hr : 0 < r) (ha : 0 < (v i)⁻¹ - r * opposite v i) :
    variational R (D v⁻¹) (near i r / v) + opposite v i * Real.log r ≤
      intercept P (opposite v) (criticalWidth v) i + Profile.residual D v i *
        Real.log (Profile.residual D v i / (((v i)⁻¹ - r * opposite v i) * criticalWidth v i)) := by
  let j := i + 1
  let k := i + 2
  have hij : i ≠ j := by unfold j; omega
  have hik : i ≠ k := by unfold k; omega
  have hjk : j ≠ k := by unfold j k; omega
  apply le_sub_iff_add_le.mp
  apply variational_le
  intro x hx
  have h₁ := scaled_max (critical_pos hv i) ha hb (hx i)
  have h₂ := mul_le_mul_of_nonneg_left (unit_max hr (add_pos (hx j) (hx i))) (inv_pos.mpr (hv j)).le
  have h₃ := mul_le_mul_of_nonneg_left (unit_max hr (add_pos (hx k) (hx i))) (inv_pos.mpr (hv k)).le
  have hu := h.upper hv hij hik hjk x hx
  rw [near_cost hij hik hjk]
  simp only [Profile.residual, opposite_eq v hij hik hjk] at hu h₁ ⊢
  linarith only [hu, h₁, h₂, h₃]

-- 读法：`axisValue D v P i - r * (v (i + 2))⁻¹ * (Profile.residual D v i * v i)` 不超过 `variational R (D v⁻¹) (near i r / v) + opposite v i * Real.log r`。
theorem Root.axis_lower (h : Root D v R P) (hv : Positive v) (i : Fin 3)
    (hb : 0 < Profile.residual D v i) {r : ℝ} (hr : 0 < r) :
    axisValue D v P i - r * (v (i + 2))⁻¹ * (Profile.residual D v i * v i) ≤
      variational R (D v⁻¹) (near i r / v) + opposite v i * Real.log r := by
  let j := i + 1
  let k := i + 2
  have hij : i ≠ j := by unfold j; omega
  have hik : i ≠ k := by unfold k; omega
  have hjk : j ≠ k := by unfold j k; omega
  let X := Profile.residual D v i * v i
  -- 推导：记下中间结论 `hX`：`0 < X`。
  have hX : 0 < X := mul_pos hb (hv i)
  let x : Vec := fun l => if l = i then X else if l = j then r⁻¹ else X + r⁻¹
  have hx : Positive x := by intro l; unfold x; split_ifs <;> positivity
  have hxi : x i = X := by simp [x]
  have hxj : x j = r⁻¹ := by simp [x, hij.symm]
  have hxk : x k = X + r⁻¹ := by simp [x, hik.symm, hjk.symm]
  have hu := (h.family.envelope (critical_pos hv) (opposite_pos hv) hij (hx i) (hx j)).1
  have hp := h.pairing _ _ _ hij hik hjk x hx (by rw [hxi, hxj, hxk])
  have hs : Positive (near i r / v) := by
    intro l
    apply div_pos _ (hv l)
    unfold near
    split <;> positivity
  have he := h.growth.lower hs hx
  -- 推导：记下中间结论 `hcost`：`cost (near i r / v) x = D v⁻¹ + r * (v k)⁻¹ * X`。
  have hcost : cost (near i r / v) x = D v⁻¹ + r * (v k)⁻¹ * X := by
    rw [near_cost hij hik hjk, hxi, hxj, hxk]
    have hi : (v i)⁻¹ * X = Profile.residual D v i := by
      unfold X; rw [mul_left_comm, inv_mul_cancel₀ (hv i).ne', mul_one]
    have ht (a : ℝ) : r * a * r⁻¹ = a := by rw [mul_right_comm, mul_inv_cancel₀ hr.ne', one_mul]
    rw [hi, mul_add, ht, ht, Profile.residual, opposite_eq v hij hik hjk]
    ring
  rw [hcost] at he
  have hlo := hu.trans hp
  rw [model, hxi, hxj, Real.log_inv] at hlo
  -- 推导：记下中间结论 `heq`：`X / criticalWidth v i = Profile.residual D v i / ((v i)⁻¹ * criticalWidth v i)`。
  have heq : X / criticalWidth v i = Profile.residual D v i / ((v i)⁻¹ * criticalWidth v i) := by
    simp [X, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  rw [heq] at hlo
  change axisValue D v P i - r * (v k)⁻¹ * X ≤ _
  unfold axisValue Profile.residual at *
  linarith only [hlo, he]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

section
/-!
# 由径向能量收缩得到谱传播

测试宽度和弦估计给出每条坐标轴上相互吻合的单侧极限。截距比较一致控制它们的差，一直到达倒数坐标的一个面。

**英文原文**

From radial energy contraction to spectral propagation

The test widths and the chord estimate give matching one-sided
limits at each axis. The intercept comparison controls their
differences uniformly up to a reciprocal face.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
open Profile Minimum Set Filter
open scoped Topology

variable {F : Type} [Field F] {D : Vec → ℝ} {R : Vec → Vec → ℝ}
  {P : PairPrices} {v : Vec}

-- 读法：`potential (adjusted D R) v (near i r)` 等于 `variational (R v⁻¹) (D v⁻¹) (near i r / v) + opposite v i * Real.log r - (mass v)⁻¹ * Real.log (1 + 2 * r)`。
private theorem near_potential (i : Fin 3) (r : ℝ) :
    potential (adjusted D R) v (near i r) =
      variational (R v⁻¹) (D v⁻¹) (near i r / v) + opposite v i * Real.log r -
        (mass v)⁻¹ * Real.log (1 + 2 * r) := by
  unfold potential adjusted opposite mass
  fin_cases i <;> simp [near, Fin.sum_univ_three] <;> ring_nf

-- 读法：`(fun r => potential (adjusted D R) v (near i r))` 沿滤子 `(𝓝[>] 0)` 收敛到 `(axisValue D v P i)`。
theorem Root.axis_limit (h : Root D v (R v⁻¹) P) (hd : StarTripod F D)
    (hv : Positive v) (i : Fin 3) :
    Tendsto (fun r => potential (adjusted D R) v (near i r)) (𝓝[>] 0)
      (𝓝 (axisValue D v P i)) := by
  let a := (v i)⁻¹
  let d := opposite v i
  let B := Profile.residual D v i
  let u := criticalWidth v i
  let C := intercept P (opposite v) (criticalWidth v) i
  have ha : 0 < a := inv_pos.mpr (hv i)
  -- 推导：记下中间结论 `hB`：`0 < B`。
  have hB : 0 < B := (residual_bounds hd hv i).1
  have hu : 0 < u := critical_pos hv i
  let lo (r : ℝ) := axisValue D v P i - r * (v (i + 2))⁻¹ * (B * v i)
  let hi (r : ℝ) := C + B * Real.log (B / ((a - r * d) * u))
  let g (r : ℝ) := variational (R v⁻¹) (D v⁻¹) (near i r / v) + d * Real.log r
  have hlo : ContinuousAt lo 0 := by unfold lo; fun_prop
  have hhi : ContinuousAt hi 0 := by
    unfold hi
    fun_prop (disch := simp [ha.ne', hu.ne', hB.ne'])
  have hl₀ : lo 0 = axisValue D v P i := by simp [lo]
  -- 推导：记下中间结论 `hh₀`：`hi 0 = axisValue D v P i`。
  have hh₀ : hi 0 = axisValue D v P i := by simp [hi, axisValue, C, B, a, u]
  have hn : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < a - r * d := by
    have he : ContinuousAt (fun r : ℝ => a - r * d) 0 := by fun_prop
    exact he.continuousWithinAt.eventually_const_lt (by simpa using ha)
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (axisValue D v P i)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hl₀ ▸ hlo.continuousWithinAt.tendsto) (hh₀ ▸ hhi.continuousWithinAt.tendsto) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact h.axis_lower hv i hB hr
    · filter_upwards [self_mem_nhdsWithin, hn] with r hr ha'
      exact h.axis_upper hv i hB hr ha'
  -- 推导：记下中间结论 `hx`：`ContinuousAt (fun r : ℝ => (mass v)⁻¹ * Real.log (1 + 2 * r)) 0`。
  have hx : ContinuousAt (fun r : ℝ => (mass v)⁻¹ * Real.log (1 + 2 * r)) 0 := by
    fun_prop (disch := norm_num)
  simp_rw [near_potential]
  simpa only [mul_zero, add_zero, Real.log_one, sub_zero, g] using hg.sub hx.continuousWithinAt

-- 读法：`Contracts` 的结果类型为 `Prop`。
/-- 所有成本增加相同的量。移动终端时，初始成本与各臂的长度成正比。

英文原文：All costs increase by the same amount. Initial costs are
proportional to the arm lengths when the terminals move.
-/
def Contracts (D : Vec → ℝ) (R : Vec → Vec → ℝ) : Prop :=
  ∀ v w s, Positive v → Positive w → Positive s → v ≤ w → ∀ t : ℝ, 0 < t →
    adjusted D R w s - adjusted D R w (s + t • w) ≤
      adjusted D R v s - adjusted D R v (s + t • v)

-- 读法：要证明的命题是 `Face.Uniform (defect D)`。这里调用 `hP.growth.continuous.comp`。
theorem uniform_of_contraction (hd : StarTripod F D)
    (h : ∀ v, Positive v → ∃ P, Root D v (R v⁻¹) P) (hc : Contracts D R) :
    Face.Uniform (defect D) := by
  have hp {v s : Vec} (hv : Positive v) (hs : Positive s) : Positive (s / v) :=
    fun i => div_pos (hs i) (hv i)
  have hr : Radial D (adjusted D R) := by
    refine ⟨?_, ?_, hc⟩
    · intro v hv
      obtain ⟨P, hP⟩ := h v hv
      exact hP.growth.continuous.comp (by fun_prop (disch := exact (hv _).ne'))
        (fun _ hs => hp hv hs)
    · intro v s hv hs t ht
      -- 推导：从 `h v hv` 中取出 `P, hP`。
      obtain ⟨P, hP⟩ := h v hv
      unfold adjusted
      rw [show (t • s) / v = t • (s / v) by ext i; simp [mul_div_assoc]]
      exact hP.growth.log_scale (hp hv hs) ht
  apply hr.uniform hd
  apply axisLimits hd
  intro v hv
  obtain ⟨P, hP⟩ := h v hv
  exact ⟨P, hP.family, hP.axis_limit hd hv⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Energy
end

section
/-!
沿三条射线作径向收缩，可对三脚架缺陷给出一致控制。

**英文原文**

Radial contraction on the three rays controls the tripod defect uniformly.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Twig
open Energy Minimum Profile

variable {K : Type} [Field K] {A : MatrixExponent.Prices.Atlas K Twig}

-- 读法：`adjusted (label A) (rootPrices A) v s` 等于 `Multi.Q A origin (mark v⁻¹) (s / v)`。
private theorem adjusted_eq {v : Vec} (hv : Positive v) (s : Vec) :
    adjusted (label A) (rootPrices A) v s = Multi.Q A origin (mark v⁻¹) (s / v) := by
  unfold Multi.Q
  rw [← rootPlacement,
    root_label A (a := v⁻¹) (fun i => inv_pos.mpr (hv i))]
  rfl

variable [Infinite K]

-- 读法：要证明的命题是 `Contracts (label A) (rootPrices A)`。这里调用 `hA.star.pos`。
private theorem Homogeneous.contracts (hA : Homogeneous A) : Contracts (label A) (rootPrices A) := by
  intro v w s hv hw hs hvw t ht
  have hp (z : Vec) (hz : Positive z) : Positive z⁻¹ := fun i => inv_pos.mpr (hz i)
  have hl (z : Vec) (hz : Positive z) : 0 < A.price (Multi.sites origin (mark z⁻¹)) 2 := by
    rw [← rootPlacement, root_label A (hp z hz)]
    exact hA.star.pos _ (hp z hz)
  have hm (z : Vec) (hz : Positive z) (i) : Dist.dist origin (mark z⁻¹ i) = (z i)⁻¹ := by
    simp [mark, radius, (hz i).le]
  have hd (z : Vec) (hz : Positive z) :
      (s + t • z) / z = (fun i => (s / z) i + t) := by
    funext i
    simp [add_div, (hz i).ne']
  rw [adjusted_eq hw, adjusted_eq hw, adjusted_eq hv, adjusted_eq hv, hd w hw, hd v hv]
  refine Multi.Q_contract A origin (mark v⁻¹) (mark w⁻¹) (s / v) (s / w) (v / w)
    (fun i => (div_pos (hv i) (hw i)).le) (fun i => (div_le_one (hw i)).mpr (hvw i))
    ?_ ?_ ?_ (fun i => div_pos (hs i) (hv i)) (fun i => div_pos (hs i) (hw i))
    (hl v hv) (hl w hw) ht.le
  · intro i
    rw [hm v hv, hm w hw, Pi.div_apply]
    field_simp [(hv i).ne', (hw i).ne']
  · intro i
    rw [hm v hv, mark_dist (hp w hw) (hp v hv), ite_eq_left rfl]
    simp only [Pi.inv_apply, Pi.div_apply]
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ (hv i) (hvw i)))]
    field_simp [(hv i).ne', (hw i).ne']; ring
  · intro i
    apply le_of_eq
    simp only [Pi.div_apply]
    field_simp [(hv i).ne', (hw i).ne']

-- 读法：要证明的命题是 `Face.Uniform (defect (label A))`。这里调用 `uniform_of_contraction`。
theorem Homogeneous.uniform (hA : Homogeneous A) : Face.Uniform (defect (label A)) := by
  apply uniform_of_contraction hA.star _ hA.contracts
  intro v hv
  refine ⟨_, root A hA hv ?_⟩
  apply family A (mark v⁻¹) _ _ (critical_pos hv) (opposite_pos hv)
  intro i j k hij hik hjk
  have ha : Positive v⁻¹ := fun l => inv_pos.mpr (hv l)
  rw [mark_dist ha ha, ite_eq_right hjk, opposite_eq v hij hik hjk]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Twig
end
