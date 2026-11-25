-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.TagFinite
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagOptimized
import OAI.LinearAlgebra.TensorSpectrum.TagEntropy

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# 具体张量特征标的优化标记法

利用具体的张量限制以及计入成本的分离构造，证明有限计数纤维所需的前提；之后才消去多项式数量的纤维带来的开销。整个论证无须多项式展开中的多项系数的渐近估计，辅助张量的成本也均已计入。

**英文原文**

Optimized tagging for actual tensor characters

The finite count-fiber premise is discharged by the actual tensor restriction
and charged separation construction.  Only then is the polynomial number of
fibers removed.  No multinomial asymptotics or uncharged auxiliary tensor is
used.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass

-- 读法：`(∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX` 不超过 `(f (ofTensor (Separation.shared A)) : ℝ)`。这里调用 `Integral.tag_optimized_of_fiber_bounds`。
theorem Character.shared_tag_optimized_of_pos (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (hs : 0 < s) (A : Fin s → Tensor O X Y Z)
    (hA : ∀ i, 0 < (f (ofTensor (A i)) : ℝ)) (hp : 0 < f.pX) :
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Separation.shared A)) : ℝ) := by
  apply Integral.tag_optimized_of_fiber_bounds hs f.pX hp
    (fun i => (f (ofTensor (A i)) : ℝ)) hA
    (f (ofTensor (Separation.shared A)) : ℝ)
    (f (ofTensor (Separation.shared A))).coe_nonneg
  intro N hN c hc
  exact f.tag_count_fiber A c hc

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TensorClass
