-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.Degeneration
import OAI.LinearAlgebra.MatrixExponent.Upper.Character.DirectSum
import OAI.LinearAlgebra.MatrixExponent.Upper.Separation

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# 具体张量特征标的带代价分离不等式

用完整直和的可加性对输出求值。恰好计入 `5*M` 个源副本的成本，并保留辅助内积。在各值相等的情形下，输出块数抵消源成本中的因子 `M`，但辅助内积因子仍然保留。

**英文原文**

The charged separation inequality for actual characters

The output is evaluated using full direct-sum additivity.  Exactly `5*M`
source copies are paid for, and the auxiliary dot product is retained.  In
the equal-value case the number of output blocks cancels the factor `M` in
that source cost, but never the auxiliary dot-product factor.
-/

noncomputable section

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

-- 读法：`(∑ h, f (ofTensor (A h))) * f (ofTensor (Separation.dotPairingX (Fin M)))` 不超过 `(5 * M : ℝ≥0) * f (ofTensor (Separation.shared A))`。
theorem Character.charged_separation (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor Coeff X Y Z) :
    (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      (5 * M : ℝ≥0) * f (ofTensor (Separation.shared A)) := by
  obtain ⟨P, hconstant, hdegree, heval⟩ := Separation.finite_charged_separation hM A
  have h := f.polynomial_constant_le
    (Tensor.directSum (fun _ : Fin (5 * M) => Separation.shared A))
    (Separation.separated A) P ((M - 1) ^ 2) hconstant hdegree heval
  rw [Character.map_directSum_const] at h
  have houtput : f (ofTensor (Separation.separated A)) =
      (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) := by
    unfold Separation.separated
    rw [Character.map_directSum_fin]
    simp only [← ofTensor_mul, Character.map_mul, Finset.sum_mul]
  rw [houtput] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

-- 读法：`c * f (ofTensor (Separation.dotPairingX (Fin M)))` 不超过 `5 * f (ofTensor (Separation.shared A))`。这里调用 `mul_le_mul_iff_right₀`。
/-- 分离成本中增长的部分由块数支付，剩下固定的因子五，要到后续取幂极限时才消去。

英文原文：The block count pays the growing part of the separation cost.  The
remaining factor five is fixed, and is removed only in a later power limit.
-/
theorem Character.charged_separation_equal (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor Coeff X Y Z)
    (c : ℝ≥0) (hvalue : ∀ h, f (ofTensor (A h)) = c) :
    c * f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      5 * f (ofTensor (Separation.shared A)) := by
  have h := f.charged_separation hM A
  simp only [hvalue, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hM' : (0 : ℝ≥0) < M := by exact_mod_cast hM
  apply (mul_le_mul_iff_right₀ hM').mp
  calc
    (M : ℝ≥0) * (c * f (ofTensor (Separation.dotPairingX (Fin M)))) =
        ((M : ℝ≥0) * c) * f (ofTensor (Separation.dotPairingX (Fin M))) :=
      (mul_assoc _ _ _).symm
    _ ≤ (5 * M : ℝ≥0) * f (ofTensor (Separation.shared A)) := h
    _ = (M : ℝ≥0) * (5 * f (ofTensor (Separation.shared A))) := by ring

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
