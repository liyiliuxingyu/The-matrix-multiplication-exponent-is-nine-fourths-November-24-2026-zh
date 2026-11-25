-- 本文件所属证明环节：一方面，用形式电路给出的方阵秩增长界控制固定规格的渐近秩；另一方面，把秩分解的块递归用于反向不等式。合并得到对每个 n≥2，n 阶乘法张量的渐近秩恰为 n 的 formalOmega 次方。
import OAI.LinearAlgebra.SpectralBooks.FormalRecursion
import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank
import OAI.LinearAlgebra.SpectralBooks.MatrixPower

/-! # 张量幂与方阵的算术指数 -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation Filter
open scoped Topology

noncomputable section

-- 读法：`asymptoticRank (matrixTensor F n n n)` 不超过 `(n : ℝ) ^ ω`。这里调用 `hcont.continuousAt`。
/-- 在三条边的权重均为 1 时，秩若满足多项式增长界，就可以在每一个固定的方阵尺寸上，对各次张量幂取根得到渐近秩的上界。 -/
theorem square_asymptoticRank_le_of_rank_growth (F : Type*) [Field F] {n : ℕ} (hn : 0 < n)
    {ω : ℝ} (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N 1) (wireDimension N 1) (wireDimension N 1)) : ℝ)
        ≤ C * (N : ℝ) ^ (ω + ε)) :
    asymptoticRank (matrixTensor F n n n) ≤ (n : ℝ) ^ ω := by
  -- 因为 n 为正，ε ↦ n^(ω+ε) 在 ε=0 处连续。先对任意正 ε 证明上界，再令 ε 从右侧趋于 0。
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun ε : ℝ => (n : ℝ) ^ (ω + ε) :=
    (Real.continuous_const_rpow hn').comp (continuous_const.add continuous_id)
  have hlim : Tendsto (fun ε : ℝ => (n : ℝ) ^ (ω + ε)) (𝓝[>] 0) (𝓝 ((n : ℝ) ^ ω)) := by
    simpa using (hcont.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi 0)).tendsto
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  -- 固定 ε 以及增长估计的常数 C，记 r=n^(ω+ε)。单位权重下，wireDimension N 1 就等于 N。
  -- 推导：从 `hgrowth ε hε` 中取出 `C, hC, hbound`。
  obtain ⟨C, hC, hbound⟩ := hgrowth ε hε
  let r := (n : ℝ) ^ (ω + ε)
  have wd (N : ℕ) : wireDimension N 1 = N := by simp [wireDimension]
  have hr : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- 当 k 趋向无穷大时，1/k 趋向 0 且 C>0，因此 C^(1/k) 趋向 1。
  have hroot : Tendsto (fun k : ℕ => C ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := C) (b := 0) hC.ne').tendsto.comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  -- 一边取张量幂秩的 k 次方根，另一边取 C^(1/k)·r。由两边的极限及最终逐项成立的不等式得到比较。
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root _)
    (show Tendsto (fun k : ℕ => C ^ ((k : ℝ)⁻¹) * r) atTop (𝓝 r) by simpa using hroot.mul_const r)
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with k hk
  -- Tₙ 的 k 次幂与 n^k 阶方阵乘法具有相同的秩，故可在阶数 n^k 使用原有增长界。
  -- 推导：记下中间结论 `hg`：`(tensorRank (Tensor.power (matrixTensor F n n n) k) : ℝ) ≤ C * r ^ k`。
  have hg : (tensorRank (Tensor.power (matrixTensor F n n n) k) : ℝ) ≤ C * r ^ k := by
    rw [tensorRank_matrixTensor_power]
    have hb := hbound (n ^ k) (Nat.one_le_pow _ _ hn)
    rw [wd] at hb
    simpa only [Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), mul_comm (k : ℝ), Real.rpow_mul_natCast
      (Nat.cast_nonneg n)] using hb
  -- 对上述非负量取 k 次方根，再把 (r^k)^(1/k) 化为 r。这里只需最终的 k 非零。
  calc
    _ ≤ (C * r ^ k) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hg (by positivity)
    _ = _ := by rw [Real.mul_rpow hC.le (pow_nonneg hr _), Real.pow_rpow_inv_natCast hr hk]

-- 读法：`asymptoticRank (matrixTensor F n n n)` 不超过 `(n : ℝ) ^ formalOmega F 1 1 1`。
/-- 形式方阵算术电路给出其基域上渐近秩的上界。 -/
theorem square_asymptoticRank_le_rpow_formalOmega (F : Type*) [Field F] {n : ℕ} (hn : 0 < n) :
    asymptoticRank (matrixTensor F n n n) ≤ (n : ℝ) ^ formalOmega F 1 1 1 :=
  -- 把形式指数本身的容许性转成秩增长界，从而可直接使用上面的取根论证。
  square_asymptoticRank_le_of_rank_growth F hn
    (formalOmega_admissible F (by norm_num) (by norm_num) (by norm_num)).rank_growth

-- 读法：`(n : ℝ) ^ formalOmega F 1 1 1` 不超过 `asymptoticRank (matrixTensor F n n n)`。这里调用 `le_ciInf`。
/-- 每个有限阶方阵的秩公式都给出关于指数的统一界；逐一应用到固定阶数的各次幂，便得到对渐近秩的同向不等式。 -/
theorem rpow_formalOmega_le_asymptoticRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ formalOmega F 1 1 1 ≤ asymptoticRank (matrixTensor F n n n) := by
  -- 要给渐近秩的下确界作下界，固定第 k 项；换算回 n^(k+1) 阶矩阵的有限秩不等式。
  apply le_ciInf
  intro k
  rw [tensorRank_matrixTensor_power]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (Nat.cast_nonneg n), ← Nat.cast_pow]
  -- 因为 n≥2，n^(k+1) 也至少为 2，满足有限秩定理的阶数要求。
  apply rpow_formalOmega_le_tensorRank
  exact hn.trans (le_self_pow (by omega) (by omega))

-- 读法：`asymptoticRank (matrixTensor F n n n)` 等于 `(n : ℝ) ^ formalOmega F 1 1 1`。
/-- 对每个至少为 2 的方阵阶数，其渐近秩等于该阶数的形式算术指数次幂，底域取同一个域。 -/
theorem square_asymptoticRank_eq_rpow_formalOmega (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    asymptoticRank (matrixTensor F n n n) = (n : ℝ) ^ formalOmega F 1 1 1 :=
  -- 把上界和下界合并，得到等式。上界只要求 n>0，下界使用这里的 n≥2。
  le_antisymm (square_asymptoticRank_le_rpow_formalOmega F (by omega))
    (rpow_formalOmega_le_asymptoticRank F hn)

-- 读法：`formalOmega F 1 1 1` 等于 `formalOmega E 1 1 1`。这里调用 `Real.rpow_right_inj`。
/-- 由形式恒等式定义的方阵算术指数仅依赖于域的特征。 -/
theorem formalOmega_square_eq_of_ringChar_eq (F E : Type*) [Field F] [Field E]
    (hchar : ringChar F = ringChar E) : formalOmega F 1 1 1 = formalOmega E 1 1 1 := by
  -- 比较两个同特征域上二阶矩阵乘法的渐近秩。用刚证的等式替换两边，再用底数 2 的幂函数的单射性。
  have h := asymptoticRank_matrixTensor_eq_of_ringChar_eq F E hchar 2 2 2
  rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide),
      square_asymptoticRank_eq_rpow_formalOmega E (by decide)] at h
  exact (Real.rpow_right_inj (by norm_num) (by norm_num)).mp h

-- 读法：`3 / Real.sqrt 2` 不超过 `formalOmega F 1 1 1`。这里调用 `square_lower_bound`。
/-- 仅在二阶验证有限渐近秩的根式不等式，就足以在同一个域上推出一个严格超过二次的算术指数下界。 -/
theorem formalOmega_square_lower_bound_of_order_two (F : Type*) [Field F]
    (h : RadicalTest (fun _ => 2) (Real.logb 2 (asymptoticRank (matrixTensor F 2 2 2)))) :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 := by
  -- 把假设中的二阶渐近秩改写为 2 的形式指数次幂；以 2 为底的对数化简后即可使用 square_lower_bound。
  rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide), Nat.cast_ofNat,
    Real.logb_rpow (by norm_num) (by norm_num)] at h
  exact square_lower_bound h

end

end SpectralBooks
end LinearAlgebra
end OAI
