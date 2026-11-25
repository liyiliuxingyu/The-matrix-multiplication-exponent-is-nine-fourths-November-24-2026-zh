-- 本文件所属证明环节：将双层指标数组展平，得到两次取张量幂与指数相乘后取一次幂的秩相等。正整数次幂时沿其倍数子序列使用秩根极限；零次幂另行处理，最终得到渐近秩的幂律。
import OAI.LinearAlgebra.SpectralBooks.RankLimit

/-!
# 渐近张量秩的幂

将矩形指标数组展平，可以把迭代取幂认作一次克罗内克幂。随后沿某正整数的所有倍数取秩的相应次方根的极限，就得到渐近秩的相应次幂。

**英文原文**

Powers of asymptotic tensor rank

Flattening a rectangular array of indices identifies iterated powers with a
single Kronecker power. The rank-root limit along the multiples of a positive
integer then gives the corresponding power of asymptotic rank.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Fin k → Fin n → A) ≃ (Fin (k * n) → A)`。
private def flattenWord {A : Type*} (k n : ℕ) :
    (Fin k → Fin n → A) ≃ (Fin (k * n) → A) where
  toFun x i := x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun x i j := x (finProdFinEquiv (i, j))
  left_inv x := by funext i j; simp
  right_inv x := by funext i; exact congrArg x (finProdFinEquiv.apply_symm_apply i)

-- 读法：`tensorRank (Tensor.power (Tensor.power T n) k)` 等于 `tensorRank (Tensor.power T (k * n))`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 对张量迭代取幂，其秩等于以各幂指数的乘积为指数时的秩。

英文原文：Iterated tensor powers have the rank of the power at the product of their indices.
-/
theorem tensorRank_power_power (T : Tensor F X Y Z) (n k : ℕ) :
    tensorRank (Tensor.power (Tensor.power T n) k) = tensorRank (Tensor.power T (k * n)) := by
  have heq : Tensor.power (Tensor.power T n) k = Tensor.pullback
      (flattenWord k n) (flattenWord k n) (flattenWord k n) (Tensor.power T (k * n)) := by
    funext x y z
    simp only [Tensor.power, Tensor.pullback]
    rw [← Fintype.prod_prod_type']
    exact finProdFinEquiv.symm.prod_comp
      (fun i : Fin k × Fin n => T (x i.1 i.2) (y i.1 i.2) (z i.1 i.2)) |>.symm
  apply le_antisymm
  · rw [heq]
    exact tensorRank_le_of_rankAtMost ((rankAtMost_tensorRank _).pullback _ _ _)
  · apply tensorRank_le_of_rankAtMost
    have h := (rankAtMost_tensorRank (Tensor.power (Tensor.power T n) k)).pullback
      (flattenWord k n).symm (flattenWord k n).symm (flattenWord k n).symm
    convert h using 1
    funext x y z
    simp [heq, Tensor.pullback]

-- 读法：`tensorRank (Tensor.power T 0)` 等于 `1`。这里调用 `le_antisymm`。
private theorem tensorRank_power_zero (T : Tensor F X Y Z) :
    tensorRank (Tensor.power T 0) = 1 := by
  apply le_antisymm
  · apply tensorRank_le_of_rankAtMost
    convert Tensor.rankOne_rankAtMost (fun _ => (1 : F)) (fun _ => (1 : F)) (fun _ => (1 : F))
      using 1
    funext x y z
    simp [Tensor.rankOne, Tensor.power]
  · by_contra! h
    have hz := rankAtMost_tensorRank (Tensor.power T 0)
    rw [show tensorRank (Tensor.power T 0) = 0 by omega] at hz
    obtain ⟨_, _, _, hzero⟩ := hz
    have he := congrFun (congrFun (congrFun hzero Fin.elim0) Fin.elim0) Fin.elim0
    simp [Tensor.power] at he

-- 读法：`asymptoticRank (Tensor.power T n)` 等于 `asymptoticRank T ^ n`。这里调用 `tendsto_nhds_unique`。
/-- 取张量幂后，渐近秩等于原渐近秩的相应次幂。零次幂也成立。

英文原文：Asymptotic rank is multiplicative on powers, including the zeroth power.
-/
theorem asymptoticRank_power (T : Tensor F X Y Z) (n : ℕ) :
    asymptoticRank (Tensor.power T n) = asymptoticRank T ^ n := by
  apply tendsto_nhds_unique (tendsto_tensorRank_power_root _)
  by_cases hn : n = 0
  · subst n
    simp [tensorRank_power_power, tensorRank_power_zero]
  · have hseq : Tendsto (fun k : ℕ => k * n) atTop atTop := by
      apply tendsto_atTop_mono (f := id) _ tendsto_id
      intro k
      exact Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hn)
    apply (((tendsto_tensorRank_power_root T).comp hseq).pow n).congr
    intro k
    simp only [Function.comp_apply, tensorRank_power_power, Nat.cast_mul]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    rw [mul_inv_rev]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

end

end

end SpectralBooks
end LinearAlgebra
end OAI
