-- 本文件所属证明环节：以三个因子分别施加线性映射定义三阶张量的限制轨道，证明进一步限制仍属于相同轨道。
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

namespace OAI.LinearAlgebra.MatrixExponent.LocalTensor

open OAI.MatrixMultiplication.Foundation

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`orbit` 的取值由 `{U | ∃ (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K), U = Tensor.restrict A B C T}` 给出。
/-- 分别在三个因子上施加一个线性映射所得的张量。

英文原文：Tensors obtained by a linear map on each of the three factors.
-/
def orbit (T : Tensor K X Y Z) : Set (Tensor K X' Y' Z') :=
  {U | ∃ (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K),
    U = Tensor.restrict A B C T}

-- 读法：`Tensor.restrict D E F U` 属于 `orbit T`。
theorem restrict_mem {X'' Y'' Z'' : Type*} [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'} (h : U ∈ orbit T)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K) :
    Tensor.restrict D E F U ∈ orbit T := by
  obtain ⟨A, B, C, rfl⟩ := h
  exact ⟨_, _, _, Tensor.restrict_restrict A B C D E F T⟩

end OAI.LinearAlgebra.MatrixExponent.LocalTensor
