-- 本文件所属证明环节：把张量幂的每条连线指标元组重新编号，证明 k 次张量幂与三条连线维数分别取 k 次幂的矩阵乘法张量有相同的秩。该等式把重复使用的小规格乘法同单个大规格乘法联系起来。
import OAI.LinearAlgebra.SpectralBooks.Flattening

/-!
# 矩形矩阵乘法张量的张量幂

**英文原文**

Tensor powers of rectangular matrix multiplication
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

-- 读法：张量 `(Tensor.matrixCoefficients (K := F) A' B' C')` 的秩至多为 `r`。用函数外延性比较等号两侧在 `x y z` 处的取值。
private theorem matrixCoefficients_rankAtMost_reindex {F A B C A' B' C' : Type*}
    [Field F] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (f : A' ≃ A) (g : B' ≃ B) (j : C' ≃ C) {r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A B C) r) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A' B' C') r := by
  have h' := h.pullback (Prod.map f g) (Prod.map g j) (Prod.map j f)
  convert h' using 1
  funext x y z
  simp [Tensor.pullback, Tensor.matrixCoefficients]

-- 读法：`tensorRank (Tensor.power (matrixTensor F a b c) k)` 等于 `tensorRank (matrixTensor F (a ^ k) (b ^ k) (c ^ k))`。这里调用 `le_antisymm`。
/-- 矩阵乘法张量的 `k` 次张量幂与把每条连线维数提升到 `k` 次幂所得矩阵乘法张量具有相同的秩。

英文原文：The `k`-fold tensor power of a matrix multiplication tensor has the same rank
as the matrix multiplication tensor with each wire dimension raised to `k`.
-/
theorem tensorRank_matrixTensor_power (F : Type*) [Field F] (a b c k : ℕ) :
    tensorRank (Tensor.power (matrixTensor F a b c) k) =
      tensorRank (matrixTensor F (a ^ k) (b ^ k) (c ^ k)) := by
  let e (n : ℕ) : (Fin k → Fin n) ≃ Fin (n ^ k) := Fintype.equivFinOfCardEq (by simp)
  apply le_antisymm <;> apply tensorRank_le_of_rankAtMost
  · have h := matrixCoefficients_rankAtMost_reindex (e c) (e a) (e b)
      (rankAtMost_tensorRank (matrixTensor F (a ^ k) (b ^ k) (c ^ k)))
    have h' := h.pullback
      (fun x : Fin k → Fin c × Fin a => (fun i => (x i).1, fun i => (x i).2))
      (fun y : Fin k → Fin a × Fin b => (fun i => (y i).1, fun i => (y i).2))
      (fun z : Fin k → Fin b × Fin c => (fun i => (z i).1, fun i => (z i).2))
    convert h' using 1
    funext x y z
    exact Tensor.matrixCoefficients_power k
      (fun i => (x i).1, fun i => (x i).2)
      (fun i => (y i).1, fun i => (y i).2)
      (fun i => (z i).1, fun i => (z i).2)
  · exact matrixCoefficients_rankAtMost_reindex (e c).symm (e a).symm (e b).symm
      (matrix_power_rankAtMost F k)

end SpectralBooks
end LinearAlgebra
end OAI
