-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Rank

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 秩界与具体张量的序

商半环中的自然数正是对角张量。借助这些引理，可将通常的有限分解与状态所用的序联系起来。

**英文原文**

Rank bounds and the concrete tensor order

Natural numbers in the quotient semiring are precisely the diagonal tensors.
These lemmas connect ordinary finite decompositions to the order used by states.
-/

open OAI.MatrixMultiplication.Foundation
open OAI.LinearAlgebra.MatrixExponent.Upper.CoefficientTensor

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

-- 读法：`ofTensor (0 : Tensor Coeff X Y Z)` 等于 `0`。这里调用 `ofTensor_eq`。
theorem ofTensor_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    ofTensor (0 : Tensor Coeff X Y Z) = 0 := by
  change ofTensor (0 : Tensor Coeff X Y Z) = ofTensor emptyTensor
  apply ofTensor_eq
  · refine ⟨fun x => x.elim, fun y => y.elim, fun z => z.elim, ?_⟩
    funext x
    exact x.elim
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x y z
    simp [Tensor.restrict]

-- 读法：`(n : TensorClass)` 等于 `ofTensor (natTensor n)`。对 `n` 作归纳。
theorem natCast_eq_ofTensor_natTensor (n : ℕ) :
    (n : TensorClass) = ofTensor (natTensor n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, ofTensor_natTensor_zero]
    exact ofTensor_zero.symm
  | succ n ih =>
    rw [Nat.cast_succ, ih, ofTensor_natTensor_add n 1, ← ofTensor_add,
      ofTensor_natTensor_one]
    rfl

-- 读法：`rank (A + B)` 不超过 `rank A + rank B`。对 `A` 作归纳，采用 `Quotient.inductionOn` 的归纳原则。
theorem rank_add_le (A B : TensorClass) : rank (A + B) ≤ rank A + rank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change rank (ofRep a + ofRep b) ≤ rank (ofRep a) + rank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_add]
      simp only [rank_ofTensor]
      exact CoefficientTensor.rank_blockSum_le _ _

-- 读法：`rank (A * B)` 不超过 `rank A * rank B`。对 `A` 作归纳，采用 `Quotient.inductionOn` 的归纳原则。
theorem rank_mul_le (A B : TensorClass) : rank (A * B) ≤ rank A * rank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change rank (ofRep a * ofRep b) ≤ rank (ofRep a) * rank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_mul]
      simp only [rank_ofTensor]
      exact CoefficientTensor.rank_product_le _ _

-- 读法：`A` 不超过 `(rank A : TensorClass)`。对 `A` 作归纳，采用 `Quotient.inductionOn` 的归纳原则。
theorem le_rank_natCast (A : TensorClass) : A ≤ (rank A : TensorClass) := by
  induction A using Quotient.inductionOn with | h a =>
    change ofRep a ≤ (rank (ofRep a) : TensorClass)
    rw [← ofTensor_coeff a, rank_ofTensor, natCast_eq_ofTensor_natTensor]
    exact ofTensor_le ((rankAtMost_iff_natTensor_restricts _ _).mp
      (CoefficientTensor.rank_spec a.coeff))

-- 读法：`1` 不超过 `A`。对 `A` 作归纳，采用 `Quotient.inductionOn` 的归纳原则。
theorem one_le_of_ne_zero {A : TensorClass} (hA : A ≠ 0) : 1 ≤ A := by
  induction A using Quotient.inductionOn with | h a =>
    change ofRep a ≠ 0 at hA
    change 1 ≤ ofRep a
    have ha : a.coeff ≠ 0 := by
      intro h
      apply hA
      rw [← ofTensor_coeff a, h, ofTensor_zero]
    rw [← ofTensor_coeff a]
    have h := ofTensor_le (nonzero_restricts_natTensor_one ha)
    rw [ofTensor_natTensor_one] at h
    exact h

-- 读法：`rank A = 0` 与 `A = 0` 等价。这里调用 `le_antisymm`。
theorem rank_eq_zero_iff (A : TensorClass) : rank A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hle := le_rank_natCast A
    rw [h, Nat.cast_zero] at hle
    exact le_antisymm hle (zero_le A)
  · rintro rfl
    change rank (ofTensor emptyTensor) = 0
    rw [rank_ofTensor, CoefficientTensor.rank_eq_zero_iff]
    funext x
    exact x.elim

-- 读法：`z * x` 不超过 `(rank x : TensorClass) * z`。这里调用 `mul_mono`。
theorem mul_le_rank_mul (z x : TensorClass) : z * x ≤ (rank x : TensorClass) * z := by
  rw [mul_comm (rank x : TensorClass) z]
  exact mul_mono (le_refl z) (le_rank_natCast x)

-- 读法：`f n` 等于 `n`。使用 `_root_.map_natCast` 给出的结论。
@[simp] theorem Character.map_natCast (f : Character) (n : ℕ) : f n = n :=
  _root_.map_natCast f.toHom n

-- 读法：`f A` 不超过 `rank A`。
theorem Character.le_rank (f : Character) (A : TensorClass) : f A ≤ rank A := by
  have h := f.monotone' (le_rank_natCast A)
  simpa only [Character.map_natCast] using h

-- 读法：`1` 不超过 `f A`。
theorem Character.one_le (f : Character) {A : TensorClass} (hA : A ≠ 0) : 1 ≤ f A := by
  have h := f.monotone' (one_le_of_ne_zero hA)
  simpa only [Character.map_one] using h

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
