-- 本文件所属证明环节：沿有限扩域把加权或普通秩分解降回基域，逐坐标展开扩域中的系数并核算基域分解的额外因子。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

-- 读法：要证明的命题是 `WeightedRankLE W (r * Module.finrank F L ^ 2)`。
/-- 对次数为 `d` 的扩域，将一个秩见证下降到基域时，成本至多增加一个 `d²` 因子。只将两条输入腿按基展开。用将一映到一的线性泛函恢复输出系数，即使域的特征整除 `d` 也适用。

英文原文：A degree-`d` extension increases the cost of descending a rank witness
by at most a factor of `d²`. Only the two input legs are expanded in a basis.
A linear functional sending one to one recovers the output coefficients,
even in characteristics dividing `d`.
-/
theorem descendWeighted {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
    {i j k r : ℕ} {W : Fin i → Fin j → Fin k → F}
    (h : WeightedRankLE (fun x y z => algebraMap F L (W x y z)) r) :
    WeightedRankLE W (r * Module.finrank F L ^ 2) := by
  classical
  obtain ⟨a, b, c, habc⟩ := h
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : L) ≠ 0)
  let d := Module.finrank F L
  let B := Module.finBasis F L
  have expand (u v w : L) :
      ∑ l : Fin d, ∑ m : Fin d, B.repr u l * B.repr v m * π (B l * B m * w) =
        π (u * v * w) := by
    conv_rhs =>
      rw [← B.sum_repr u, Finset.sum_mul, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    conv_rhs =>
      rw [← B.sum_repr v, Finset.mul_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [pow_two]
  let e : Fin r × Fin d × Fin d ≃ Fin (r * (d * d)) :=
    ((Equiv.refl (Fin r)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun l x => B.repr (a (e.symm l).1 x) (e.symm l).2.1,
    fun l y => B.repr (b (e.symm l).1 y) (e.symm l).2.2,
    fun l z => π (B (e.symm l).2.1 * B (e.symm l).2.2 * c (e.symm l).1 z), ?_⟩
  intro x y z
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, expand, ← map_sum, habc]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, hπ]

-- 读法：在 `F` 上，三个尺寸为 `i`、`j`、`k` 的矩阵乘法张量的秩至多为 `(r * Module.finrank F L ^ 2)`。
theorem descendRank {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
    {i j k r : ℕ} (h : RankLE L i j k r) : RankLE F i j k (r * Module.finrank F L ^ 2) := by
  have h' : WeightedRankLE (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => algebraMap F L 1) r := by
    simpa only [map_one, WeightedRankLE, RankLE] using h
  exact descendWeighted (F := F) (W := fun _ _ _ => 1) h'

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：在 `F` 上，边长为 `n` 的矩阵乘法张量的秩至多为 `(r * Module.finrank F L ^ 2)`。使用 `Rectangle.descendRank` 给出的结论。
theorem descendRank {F : Type*} {L : Type*} [Field F] [Field L] [Algebra F L] [Module.Finite F L]
    {n r : ℕ} (h : RankLE L n r) : RankLE F n (r * Module.finrank F L ^ 2) :=
  Rectangle.descendRank h

end OAI.LinearAlgebra.MatrixExponent
