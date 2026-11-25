-- 本文件所属证明环节：代数扩域上一个固定张量幂的有限秩分解只用到有限多个系数；这些系数落在某个有限维中间域中。逐幂使用有限扩域的秩估计并取极限，得到代数扩域前后的渐近秩相等。
import OAI.LinearAlgebra.SpectralBooks.FiniteExtensionRank
import OAI.LinearAlgebra.SpectralBooks.RankCoefficients
import OAI.LinearAlgebra.SpectralBooks.PowerRank

/-!
# 渐近秩在代数扩域下不变

一个固定次幂的分解只涉及有限多个系数。在代数扩域上，这些系数属于某个有限维中间域，因此可将有限扩域估计应用于该次幂。

**英文原文**

Asymptotic rank is invariant under algebraic scalar extension

A decomposition of a fixed power has only finitely many coefficients.
Over an algebraic extension they lie in a finite-dimensional intermediate
field, so the finite-extension estimate applies to that power.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

variable {F K X Y Z : Type*} [Field F] [Field K] [Algebra F K]

variable [Fintype X] [Fintype Y]

-- 读法：`asymptoticRank (fun x y z => algebraMap F K (T x y z))` 不超过 `asymptoticRank T`。这里调用 `le_ciInf`。
/-- 扩域后精确秩不会增加，因此渐近秩也不会增加。

英文原文：Exact rank does not increase under extension, hence neither does
asymptotic rank.
-/
theorem asymptoticRank_map_le (T : Tensor F X Y Z) :
    asymptoticRank (fun x y z => algebraMap F K (T x y z)) ≤ asymptoticRank T := by
  let U := fun x y z => algebraMap F K (T x y z)
  apply le_ciInf
  intro n
  have h := tensorRank_le_of_rankAtMost
    ((rankAtMost_tensorRank (Tensor.power T (n+1))).map (algebraMap F K))
  rw [← power_scalarExtension] at h
  apply (ciInf_le (f := fun k : ℕ => (tensorRank (Tensor.power U (k+1)) : ℝ) ^ ((k+1:ℝ)⁻¹))
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ n).trans
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast h

-- 读法：`asymptoticRank (fun x y z => algebraMap F K (T x y z))` 等于 `asymptoticRank T`。这里调用 `le_antisymm`。
/-- 代数扩张保持每个有限张量的渐近秩。

英文原文：An algebraic extension leaves the asymptotic rank of every finite tensor unchanged.
-/
theorem asymptoticRank_map_eq_of_isAlgebraic [Algebra.IsAlgebraic F K] [Finite Z]
    (T : Tensor F X Y Z) :
    asymptoticRank (fun x y z => algebraMap F K (T x y z)) = asymptoticRank T := by
  apply le_antisymm (asymptoticRank_map_le T)
  apply le_ciInf
  intro n
  let U := fun x y z => algebraMap F K (T x y z)
  let r := tensorRank (Tensor.power U (n+1))
  have h : Tensor.RankAtMost (fun x y z => algebraMap F K (Tensor.power T (n+1) x y z)) r := by
    rw [← power_scalarExtension]
    exact rankAtMost_tensorRank _
  obtain ⟨S, hS, hfin⟩ := exists_finiteDimensional_rankAtMost h
  have hle := asymptoticRank_le_of_finiteExtension hfin
  rw [asymptoticRank_power] at hle
  have hroot := Real.rpow_le_rpow (pow_nonneg (asymptoticRank_nonneg T) (n+1)) hle
    (inv_nonneg.mpr (Nat.cast_nonneg (n+1)))
  rw [Real.pow_rpow_inv_natCast (asymptoticRank_nonneg _) (Nat.succ_ne_zero n)] at hroot
  simpa only [Nat.cast_add, Nat.cast_one] using hroot

end

end SpectralBooks
end LinearAlgebra
end OAI
