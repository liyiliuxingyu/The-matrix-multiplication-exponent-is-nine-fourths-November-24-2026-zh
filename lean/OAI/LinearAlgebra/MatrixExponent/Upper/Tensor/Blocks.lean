-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Base

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 异型直和与限制

两个加项在每条腿上分别保留自己的坐标。交叉项的系数为零，分块对角的局部矩阵给出了具体的限制见证。

**英文原文**

Heterogeneous direct sums and restrictions

The two summands retain separate coordinates on every leg. Cross coefficients
are zero, and block diagonal local matrices give actual restriction witnesses.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.CoefficientTensor

section Algebra

variable {K X Y Z U V W X' Y' Z' U' V' W' : Type*} [CommSemiring K]

-- 读法：逐一匹配以下输入模式：`.inl x, .inl y, .inl z`、`.inr u, .inr v, .inr w`、`_, _, _`。
/-- 两个张量的直和，它们在三条腿上各自的坐标空间均可以不同。

英文原文：Direct sum of tensors whose three coordinate spaces may all differ.
-/
def blockSum (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

-- 读法：逐一匹配以下输入模式：`.inl x', .inl x`、`.inr u', .inr u`、`_, _`。
/-- 分块对角的局部系数矩阵，不同直和项之间的映射均为零。

英文原文：Block diagonal local coefficient matrix, with no cross-summand maps.
-/
def blockMatrix (A : X' → X → K) (D : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => A x' x
  | .inr u', .inr u => D u' u
  | _, _ => 0

-- 读法：`blockSum T S (.inl x) (.inl y) (.inl z)` 等于 `T x y z`。两端由定义化简为同一项。
@[simp] theorem blockSum_inl (T : Tensor K X Y Z) (S : Tensor K U V W)
    (x : X) (y : Y) (z : Z) :
    blockSum T S (.inl x) (.inl y) (.inl z) = T x y z := rfl

-- 读法：`blockSum T S (.inr u) (.inr v) (.inr w)` 等于 `S u v w`。两端由定义化简为同一项。
@[simp] theorem blockSum_inr (T : Tensor K X Y Z) (S : Tensor K U V W)
    (u : U) (v : V) (w : W) :
    blockSum T S (.inr u) (.inr v) (.inr w) = S u v w := rfl

-- 读法：`Tensor.restrict (blockMatrix A D) (blockMatrix B E) (blockMatrix C F) (blockSum T S)` 等于 `blockSum (Tensor.restrict A B C T) (Tensor.restrict D E F S)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 两个直和项上的独立限制合成对整个直和的单个限制，也覆盖每个为零的交叉系数。

英文原文：Independent restrictions on the two summands combine into one restriction
on their full direct sum, including every vanishing cross coefficient.
-/
theorem restrict_blockSum
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (blockMatrix A D) (blockMatrix B E) (blockMatrix C F)
      (blockSum T S) = blockSum (Tensor.restrict A B C T) (Tensor.restrict D E F S) := by
  funext x y z
  rcases x with x | u <;> rcases y with y | v <;> rcases z with z | w <;>
    simp [Tensor.restrict, blockSum, blockMatrix, Fintype.sum_sum_type]

-- 读法：`Tensor.pullback (Sum.map a d) (Sum.map b e) (Sum.map c f) (blockSum T S)` 等于 `blockSum (Tensor.pullback a b c T) (Tensor.pullback d e f S)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 分别为每个直和项的坐标重新标号。

英文原文：Relabel the coordinates of each summand independently.
-/
theorem pullback_blockSum (T : Tensor K X Y Z) (S : Tensor K U V W)
    (a : X' → X) (b : Y' → Y) (c : Z' → Z)
    (d : U' → U) (e : V' → V) (f : W' → W) :
    Tensor.pullback (Sum.map a d) (Sum.map b e) (Sum.map c f) (blockSum T S) =
      blockSum (Tensor.pullback a b c T) (Tensor.pullback d e f S) := by
  funext x y z
  rcases x with x | u <;> rcases y with y | v <;> rcases z with z | w <;> rfl

end Algebra

section Restriction

variable {X Y Z U V W X' Y' Z' U' V' W' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

-- 读法：要证明的命题是 `Restricts (blockSum T S) (blockSum T' S')`。
/-- 限制与不同类型张量的直和相容。

英文原文：Restriction is compatible with heterogeneous tensor direct sums.
-/
theorem Restricts.blockSum
    {T : Tensor Coeff X Y Z} {T' : Tensor Coeff X' Y' Z'}
    {S : Tensor Coeff U V W} {S' : Tensor Coeff U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (blockSum T S) (blockSum T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨blockMatrix A D, blockMatrix B E, blockMatrix C F,
    (restrict_blockSum A B C D E F T S).symm⟩

-- 读法：要证明的命题是 `Restricts (Tensor.product T S) (Tensor.product T' S')`。
/-- 将三条腿上相应的局部系数矩阵分别取积，可知限制与张量积相容。

英文原文：Restriction is compatible with tensor products through the actual products
of the three local coefficient matrices.
-/
theorem Restricts.product
    {T : Tensor Coeff X Y Z} {T' : Tensor Coeff X' Y' Z'}
    {S : Tensor Coeff U V W} {S' : Tensor Coeff U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨fun x u => A x.1 u.1 * D x.2 u.2,
    fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2,
    (Tensor.restrict_product A B C D E F T S).symm⟩

end Restriction

end OAI.LinearAlgebra.MatrixExponent.Upper.CoefficientTensor
