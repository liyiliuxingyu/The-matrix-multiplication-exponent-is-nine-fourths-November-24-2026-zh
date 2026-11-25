-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.RankOrder
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Flattening

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
具体张量半环上由实际展平矩阵给出的可加不变量。

**英文原文**

The actual additive flattening invariant on the concrete tensor semiring.
-/

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

-- 读法：`flatteningRank (n : TensorClass)` 等于 `n`。
@[simp] theorem flatteningRank_natCast (n : ℕ) : flatteningRank (n : TensorClass) = n := by
  rw [natCast_eq_ofTensor_natTensor, flatteningRank_ofTensor,
    CoefficientTensor.flatteningRank_natTensor]

-- 读法：`flatteningRank (0 : TensorClass)` 等于 `0`。使用 `flatteningRank_natCast` 给出的结论。
@[simp] theorem flatteningRank_zero : flatteningRank (0 : TensorClass) = 0 :=
  flatteningRank_natCast 0

-- 读法：`flatteningRank (1 : TensorClass)` 等于 `1`。这里调用 `flatteningRank_natCast`。
@[simp] theorem flatteningRank_one : flatteningRank (1 : TensorClass) = 1 := by
  simpa only [Nat.cast_one] using flatteningRank_natCast 1

-- 读法：`flatteningRank (A + B)` 等于 `flatteningRank A + flatteningRank B`。对 `A` 作归纳，采用 `Quotient.inductionOn` 的归纳原则。
theorem flatteningRank_add (A B : TensorClass) :
    flatteningRank (A + B) = flatteningRank A + flatteningRank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change flatteningRank (ofRep a + ofRep b) =
        flatteningRank (ofRep a) + flatteningRank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_add]
      simp only [flatteningRank_ofTensor, CoefficientTensor.flatteningRank_blockSum]

-- 读法：`rank (n : TensorClass)` 等于 `n`。这里调用 `Nat.le_antisymm`。
@[simp] theorem rank_natCast (n : ℕ) : rank (n : TensorClass) = n := by
  apply Nat.le_antisymm
  · rw [natCast_eq_ofTensor_natTensor, rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr
      (CoefficientTensor.rankAtMost_natTensor n)
  · simpa only [flatteningRank_natCast] using
      flatteningRank_le_rank (n : TensorClass)

-- 读法：`(m : TensorClass) ≤ (n : TensorClass)` 与 `m ≤ n` 等价。这里调用 `rank_mono`。
theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : TensorClass) ≤ (n : TensorClass) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    rw [natCast_eq_ofTensor_natTensor, natCast_eq_ofTensor_natTensor]
    exact ofTensor_le (CoefficientTensor.natTensor_restricts_of_le h)

-- 读法：为 `Nontrivial TensorClass` 构造类型类实例。
instance : Nontrivial TensorClass := ⟨⟨0, 1, by
  intro h
  have hr := congrArg flatteningRank h
  simp only [flatteningRank_zero, flatteningRank_one] at hr
  exact Nat.zero_ne_one hr⟩⟩

-- 读法：`¬ D + (m : TensorClass)` 不超过 `D`。这里调用 `Nat.not_lt_of_ge`。
/-- 有限催化子无法吸收正标量。这里使用展平秩的可加性，普通张量秩无须具有可加性。

英文原文：A positive scalar cannot be absorbed by a finite catalyst. This is where
additive flattening rank is used, rather than additivity of ordinary rank.
-/
theorem not_add_positive_natCast_le (D : TensorClass) {m : ℕ} (hm : 0 < m) :
    ¬ D + (m : TensorClass) ≤ D := by
  intro h
  have hf := flatteningRank_mono h
  rw [flatteningRank_add, flatteningRank_natCast] at hf
  exact (Nat.not_lt_of_ge hf) (Nat.lt_add_of_pos_right hm)

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
