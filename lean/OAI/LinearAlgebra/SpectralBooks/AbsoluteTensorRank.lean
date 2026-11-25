-- 本文件所属证明环节：有限个张量分解系数满足有限个多项式方程。把这些系数特化到代数闭包，再应用代数扩域的下降结果，证明任意扩域都保持渐近秩。矩阵乘法张量的系数来自素域，因而其渐近秩在相同特征的域上相等。
import OAI.LinearAlgebra.SpectralBooks.AlgebraicExtensionRank
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimeField
import Mathlib.Algebra.Algebra.ZMod

/-!
# 同一特征所有域上的渐近秩

若表示分解的多项式方程在某扩域上有解，则它们在代数闭包上也有解。将这一特化与有限扩域下降相结合，无须假设扩域是代数扩张即可得到标量扩张不变性，从而得到矩阵乘法张量在同一特征内的不变性。

**英文原文**

Asymptotic rank over all fields of a characteristic

The polynomial equations expressing a decomposition over any field extension
have a solution over the algebraic closure. Combining this specialization
with finite-extension descent gives scalar invariance without an algebraicity
hypothesis, hence characteristic invariance for matrix multiplication tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (K : Type*) [Field K] [Algebra F K] [IsAlgClosed K]

-- 读法：存在 `b : V → K`，对每个 `p : MvPolynomial V F`，由 `MvPolynomial.aeval a p = 0` 推出 `MvPolynomial.aeval b p = 0`。
/-- 把一个有限元组特化到代数闭域，同时保留其基域上的全部多项式等式。

英文原文：Specialize a finite tuple to an algebraically closed field while preserving
all polynomial equalities over its ground field.
-/
theorem exists_specialization {V : Type*} [Finite V] (a : V → E) :
    ∃ b : V → K, ∀ p : MvPolynomial V F, MvPolynomial.aeval a p = 0 →
      MvPolynomial.aeval b p = 0 := by
  let I := MvPolynomial.vanishingIdeal F {a}
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (Ideal.IsPrime.ne_top (inferInstance : I.IsPrime))
  obtain ⟨b, hb⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨b, fun p hp ↦ (MvPolynomial.mem_vanishingIdeal_singleton_iff b p).mp ?_⟩
  rw [← hb]
  exact hIJ ((MvPolynomial.mem_vanishingIdeal_singleton_iff a p).mpr hp)

-- 读法：张量 `(fun x y z ↦ algebraMap F K (T x y z))` 的秩至多为 `r`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 若定义在 `F` 上的有限张量在 `E` 上有精确的秩分解，则在扩张 `F` 的代数闭域 `K` 上也有同样规模的分解。

英文原文：A finite tensor defined over `F` admitting an exact rank decomposition over
`E` admits one of the same size over an algebraically closed `K` extending `F`.
-/
theorem rankAtMost_of_extension_to_algClosed {X Y Z : Type*}
    [Finite X] [Finite Y] [Finite Z] {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost (fun x y z ↦ algebraMap F E (T x y z)) r) :
    Tensor.RankAtMost (fun x y z ↦ algebraMap F K (T x y z)) r := by
  classical
  obtain ⟨A, B, C, habc⟩ := h
  let v : Fin r × (X ⊕ Y ⊕ Z) → E := fun p ↦ p.2.elim (A p.1) (Sum.elim (B p.1) (C p.1))
  obtain ⟨w, hw⟩ := exists_specialization (F := F) K v
  refine ⟨fun i x ↦ w (i, .inl x), fun i y ↦ w (i, .inr (.inl y)),
    fun i z ↦ w (i, .inr (.inr z)), ?_⟩
  funext x y z
  let p : MvPolynomial (Fin r × (X ⊕ Y ⊕ Z)) F := MvPolynomial.C (T x y z) - ∑ i,
    MvPolynomial.X (i, .inl x) * MvPolynomial.X (i, .inr (.inl y)) * MvPolynomial.X (i, .inr (.inr z))
  -- 推导：记下中间结论 `hp`：`MvPolynomial.aeval v p = 0`。
  have hp : MvPolynomial.aeval v p = 0 := by
    simpa [p, v, Tensor.rankOne, sub_eq_zero] using congrFun (congrFun (congrFun habc x) y) z
  simpa [p, Tensor.rankOne, sub_eq_zero] using hw p hp

-- 读法：`asymptoticRank (fun x y z ↦ algebraMap F E (T x y z))` 等于 `asymptoticRank T`。这里调用 `le_antisymm`。
/-- 对任意超越次数的标量扩张，每个有限三阶张量的渐近秩保持不变。

英文原文：A scalar extension of any transcendence degree preserves the asymptotic
rank of every finite three-tensor.
-/
theorem asymptoticRank_map_eq {X Y Z : Type*} [Fintype X] [Fintype Y] [Finite Z]
    (T : Tensor F X Y Z) :
    asymptoticRank (fun x y z ↦ algebraMap F E (T x y z)) = asymptoticRank T := by
  apply le_antisymm (asymptoticRank_map_le T)
  rw [← asymptoticRank_map_eq_of_isAlgebraic (K := AlgebraicClosure F) T]
  apply le_ciInf
  intro n
  let U := fun x y z ↦ algebraMap F E (T x y z)
  let V := fun x y z ↦ algebraMap F (AlgebraicClosure F) (T x y z)
  have h : Tensor.RankAtMost (fun x y z ↦ algebraMap F E (Tensor.power T (n + 1) x y z))
      (tensorRank (Tensor.power U (n + 1))) := by
    rw [← power_scalarExtension (K := E)]
    exact rankAtMost_tensorRank _
  have hV := rankAtMost_of_extension_to_algClosed (AlgebraicClosure F) h
  -- 推导：记下中间结论 `hle`：`tensorRank (Tensor.power V (n + 1)) ≤ tensorRank (Tensor.power U (n + 1))`。
  have hle : tensorRank (Tensor.power V (n + 1)) ≤ tensorRank (Tensor.power U (n + 1)) := by
    apply tensorRank_le_of_rankAtMost
    rw [← power_scalarExtension (K := AlgebraicClosure F)] at hV
    exact hV
  apply (ciInf_le (f := fun k : ℕ ↦ (tensorRank (Tensor.power V (k+1)) : ℝ) ^ ((k+1:ℝ)⁻¹))
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ n).trans
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) (by positivity)

-- 读法：`asymptoticRank (matrixTensor E a b c)` 等于 `asymptoticRank (matrixTensor F a b c)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 在 `F` 的所有扩域上，矩阵乘法张量的渐近秩相同。

英文原文：All fields extending `F` give the same asymptotic rank to the matrix tensor.
-/
theorem asymptoticRank_matrixTensor_baseChange (F E : Type*) [Field F] [Field E] [Algebra F E]
    (a b c : ℕ) : asymptoticRank (matrixTensor E a b c) = asymptoticRank (matrixTensor F a b c) := by
  convert asymptoticRank_map_eq (E := E) (matrixTensor F a b c) using 2
  funext x y z
  simp only [matrixTensor, Tensor.matrixCoefficients]
  split <;> simp

-- 读法：`asymptoticRank (matrixTensor F a b c)` 等于 `asymptoticRank (matrixTensor E a b c)`。按 `ringChar F = 0` 成立与否分情况。
/-- 矩形矩阵乘法张量的渐近秩只依赖于域的特征，也包括零特征。

英文原文：The rectangular matrix tensor's asymptotic rank depends only on the
characteristic, including characteristic zero.
-/
theorem asymptoticRank_matrixTensor_eq_of_ringChar_eq (F E : Type*) [Field F] [Field E]
    (hchar : ringChar F = ringChar E) (a b c : ℕ) :
    asymptoticRank (matrixTensor F a b c) = asymptoticRank (matrixTensor E a b c) := by
  by_cases hzero : ringChar F = 0
  · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hzero
    let : CharZero E := (CharP.ringChar_zero_iff_CharZero E).mp (hchar.symm.trans hzero)
    exact (asymptoticRank_matrixTensor_baseChange ℚ F a b c).trans
      (asymptoticRank_matrixTensor_baseChange ℚ E a b c).symm
  · let : Fact (ringChar F).Prime := ⟨(CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hzero⟩
    let : CharP E (ringChar F) := ringChar.eq_iff.mp hchar.symm
    let : Algebra (ZMod (ringChar F)) E := ZMod.algebra _ _
    let : Algebra (ZMod (ringChar F)) F := ZMod.algebra _ _
    exact (asymptoticRank_matrixTensor_baseChange (ZMod (ringChar F)) F a b c).trans
      (asymptoticRank_matrixTensor_baseChange (ZMod (ringChar F)) E a b c).symm

-- 读法：`asymptoticRank (matrixTensor F x y z)` 等于 `asymptoticRank (matrixTensor G x y z)`。
/-- 用 `CharP F p` 表述按特征作出的比较，允许 `p = 0`。

英文原文：The characteristic-wise comparison in the notation `CharP F p`, with `p = 0`
allowed.
-/
theorem matrix_asymptoticRank_eq_of_charP (F G : Type*) [Field F] [Field G]
    (p : ℕ) [CharP F p] [CharP G p] (x y z : ℕ) :
    asymptoticRank (matrixTensor F x y z) = asymptoticRank (matrixTensor G x y z) :=
  asymptoticRank_matrixTensor_eq_of_ringChar_eq F G
    ((ringChar.eq_iff.mpr (inferInstance : CharP F p)).trans
      (ringChar.eq_iff.mpr (inferInstance : CharP G p)).symm) x y z

end

end SpectralBooks
end LinearAlgebra
end OAI
