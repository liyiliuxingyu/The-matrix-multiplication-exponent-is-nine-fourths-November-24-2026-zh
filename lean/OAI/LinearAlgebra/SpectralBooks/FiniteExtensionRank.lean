-- 本文件所属证明环节：在次数为 d 的有限扩域上给定秩分解。选取该扩域在基域上的一组基，在两个张量因子上分别展开，用一个把基域嵌入收回的线性映射处理第三个因子。返回基域时秩至多多出 d² 倍，取张量幂的根后该常数消失。
import OAI.LinearAlgebra.SpectralBooks.RankLimit
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# 有限扩域下的张量秩

选取扩域的一组基，将分解中的两个位置按此基展开。用域嵌入的一个线性收缩映射处理第三个位置。维数带来的成本不随张量幂次变化。

**英文原文**

Tensor rank under finite scalar extension

Expand two sites of a decomposition in a fixed basis of the extension.
A linear retraction of the field inclusion contracts the third site.
The dimension cost is constant across tensor powers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation Filter
open scoped Topology

section

variable {F K X Y Z : Type*} [Field F] [Field K] [Algebra F K]

-- 读法：`Tensor.power (fun x y z => algebraMap F K (T x y z)) n` 等于 `fun x y z => algebraMap F K (Tensor.power T n x y z)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 先取克罗内克幂再逐项扩张标量，与先扩张标量再取幂的结果相同。

英文原文：Kronecker powers commute with entrywise scalar extension.
-/
theorem power_scalarExtension (T : Tensor F X Y Z) (n : ℕ) :
    Tensor.power (fun x y z => algebraMap F K (T x y z)) n =
      fun x y z => algebraMap F K (Tensor.power T n x y z) := by
  funext x y z
  simp [Tensor.power]

-- 读法：张量 `T` 的秩至多为 `(r * (Module.finrank F K) ^ 2)`。
/-- 扩张次数为 `d` 的有限扩域至多使张量秩缩小 `d²` 倍。

英文原文：A finite extension of degree `d` saves at most a factor of `d²` in tensor rank.
-/
theorem rankAtMost_of_finiteExtension [FiniteDimensional F K] {T : Tensor F X Y Z}
    {r : ℕ} (h : Tensor.RankAtMost (fun x y z => algebraMap F K (T x y z)) r) :
    Tensor.RankAtMost T (r * (Module.finrank F K) ^ 2) := by
  classical
  let d := Module.finrank F K
  let b := Module.finBasis F K
  obtain ⟨P, hP⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F K))
  obtain ⟨A, B, C, hABC⟩ := h
  let a (j : Fin r × Fin d × Fin d) (x : X) := b.repr (A j.1 x) j.2.1
  let a' (j : Fin r × Fin d × Fin d) (y : Y) := b.repr (B j.1 y) j.2.2
  let c (j : Fin r × Fin d × Fin d) (z : Z) := P (b j.2.1 * b j.2.2 * C j.1 z)
  have hterm (i : Fin r) (x : X) (y : Y) (z : Z) :
      P (Tensor.rankOne (A i) (B i) (C i) x y z) =
      ∑ j : Fin d, ∑ k : Fin d, Tensor.rankOne (a (i,j,k)) (a' (i,j,k)) (c (i,j,k)) x y z := by
    unfold Tensor.rankOne
    conv_lhs => rw [← b.sum_repr (A i x), ← b.sum_repr (B i y)]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, a, a', c,
      smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [mul_left_comm]
    rfl
  -- 推导：记下中间结论 `heq`：`T = fun x y z => ∑ j, Tensor.rankOne (a j) (a' j) (c j) x y z`。
  have heq : T = fun x y z => ∑ j, Tensor.rankOne (a j) (a' j) (c j) x y z := by
    funext x y z
    have he := LinearMap.congr_fun hP (T x y z)
    change P (algebraMap F K (T x y z)) = T x y z at he
    rw [← he, congrFun (congrFun (congrFun hABC x) y) z, map_sum]
    simp only [Fintype.sum_prod_type, hterm]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, sq, d] using
    Tensor.rankAtMost_sum_rankOne a a' c

variable [Fintype X] [Fintype Y]

-- 读法：`asymptoticRank T` 不超过 `r`。这里调用 `le_of_tendsto_of_tendsto`。
/-- 对张量幂的秩界开相应次方根并取极限，固定因子的影响消失。

英文原文：A constant factor in a tensor-power rank bound disappears under roots.
-/
theorem asymptoticRank_le_of_power_bound (T : Tensor F X Y Z) {C r : ℕ}
    (hC : 0 < C) (h : ∀ n : ℕ, tensorRank (Tensor.power T n) ≤ C * r ^ n) :
    asymptoticRank T ≤ r := by
  have hc : Tendsto (fun n : ℕ => (C : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont := Real.continuousAt_const_rpow (a := (C : ℝ)) (b := 0) (by positivity)
    simpa only [Real.rpow_zero, Function.comp_def] using
      hcont.tendsto.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hlim := hc.mul_const (r : ℝ)
  rw [one_mul] at hlim
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root T) hlim
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  calc
    (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹) ≤
        ((C : ℝ) * (r : ℝ) ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h n) (by positivity)
    _ = (C : ℝ) ^ ((n : ℝ)⁻¹) * r := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.pow_rpow_inv_natCast (by positivity) hn]

-- 读法：`asymptoticRank T` 不超过 `r`。这里调用 `asymptoticRank_le_of_power_bound`。
/-- 在有限扩域上得到的任一精确分解，都给出原域上渐近秩的上界。

英文原文：Any exact decomposition over a finite extension bounds the asymptotic rank
over the original field.
-/
theorem asymptoticRank_le_of_finiteExtension [FiniteDimensional F K] {T : Tensor F X Y Z}
    {r : ℕ} (h : Tensor.RankAtMost (fun x y z => algebraMap F K (T x y z)) r) :
    asymptoticRank T ≤ r := by
  apply asymptoticRank_le_of_power_bound T (C := (Module.finrank F K) ^ 2)
    (pow_pos Module.finrank_pos 2)
  intro n
  have hpow := h.power n
  rw [power_scalarExtension] at hpow
  simpa only [mul_comm] using tensorRank_le_of_rankAtMost (rankAtMost_of_finiteExtension hpow)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
