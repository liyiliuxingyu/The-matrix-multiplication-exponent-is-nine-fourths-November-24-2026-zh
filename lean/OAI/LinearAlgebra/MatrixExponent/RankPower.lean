-- 本文件所属证明环节：对方阵的秩分解作张量幂，把固定边长的分解用于更大边长，并记录秩随取幂的增长。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

/-!
将矩形矩阵乘法的秩构造特化到正方形情形。

**英文原文**

Square specializations of the rectangular rank constructions.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F K : Type*} [Field F] [Field K] {n m r s : ℕ}

-- 读法：在 `K` 上，边长为 `n` 的矩阵乘法张量的秩至多为 `r`。使用 `Rectangle.RankLE.map` 给出的结论。
theorem rank_map (f : F →+* K) (h : RankLE F n r) : RankLE K n r :=
  Rectangle.RankLE.map h f

-- 读法：在 `F` 上，边长为 `(n * m)` 的矩阵乘法张量的秩至多为 `(r * s)`。使用 `Rectangle.RankLE.tensor` 给出的结论。
theorem rank_mul (h : RankLE F n r) (h' : RankLE F m s) : RankLE F (n * m) (r * s) :=
  Rectangle.RankLE.tensor h h'

-- 读法：在 `F` 上，边长为 `(n ^ k)` 的矩阵乘法张量的秩至多为 `(r ^ k)`。使用 `Rectangle.RankLE.pow` 给出的结论。
theorem rank_pow (h : RankLE F n r) (k : ℕ) : RankLE F (n ^ k) (r ^ k) :=
  Rectangle.RankLE.pow h k

end OAI.LinearAlgebra.MatrixExponent
