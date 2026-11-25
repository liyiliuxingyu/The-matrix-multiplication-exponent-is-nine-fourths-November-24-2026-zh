-- 本文件所属证明环节：合并分轮元数缩减、批量查表和排序成本，给出带独立外部比特的张量幂网络的对数幂次节省。
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.Finite.Extension
import OAI.LinearAlgebra.MatrixExponent.Shaving.Defs

section
/-!
压缩定理中的对数成本与次多项式批量大小。

**英文原文**

Logarithmic costs and subpolynomial batch sizes in the compression theorem.
-/

open Filter

namespace OAI.LinearAlgebra.MatrixExponent.Shaving

-- 读法：`(fun n : ℕ => (Nat.clog 2 n : ℝ))` 将滤子 `atTop` 映向滤子 `atTop`。这里调用 `tendsto_natCast_atTop_atTop.comp`。
theorem tendsto_height : Tendsto (fun n : ℕ => (Nat.clog 2 n : ℝ)) atTop atTop := by
  have h : Tendsto (Nat.clog 2) atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    filter_upwards [eventually_gt_atTop (2 ^ k)] with n hn
    exact ((Nat.lt_clog_iff_pow_lt (by decide)).2 hn).le
  exact tendsto_natCast_atTop_atTop.comp h

-- 读法：对每个 `ᶠ n : ℕ in atTop`，对每个 `u : ℕ`，由 `(u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ (1 / 2 : ℝ)` 推出 `(2 : ℝ) ^ u ≤ (n : ℝ) ^ ε`。
/-- 元数不超过高度平方根的表可以分批处理；批大小至多为输入大小的任何预先给定的正次幂。

英文原文：Tables with arity bounded by the square root of the height fit into
batches of size at most any fixed positive power of the input size.
-/
theorem batch_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℕ, (u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ (1 / 2 : ℝ) →
      (2 : ℝ) ^ u ≤ (n : ℝ) ^ ε := by
  filter_upwards [eventually_gt_atTop 1, tendsto_height.eventually_ge_atTop 2,
    (Real.tendsto_sqrt_atTop.comp tendsto_height).eventually_ge_atTop (2 / ε)]
    with n hn hh hs u hu
  let H := Nat.clog 2 n
  change 2 / ε ≤ Real.sqrt H at hs
  have hpred : (H.pred : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub (Nat.clog_pos (by decide) hn), Nat.cast_one]
  -- 推导：记下中间结论 `hstep`：`(u : ℝ) ≤ (H.pred : ℝ) * ε`。
  have hstep : (u : ℝ) ≤ (H.pred : ℝ) * ε := by
    rw [hpred]
    calc
      (u : ℝ) ≤ Real.sqrt H := by simpa only [Real.sqrt_eq_rpow] using hu
      _ ≤ (H : ℝ) / 2 * ε := by
        have hx := mul_le_mul_of_nonneg_left ((div_le_iff₀ hε).1 hs) (Real.sqrt_nonneg H)
        rw [← mul_assoc, Real.mul_self_sqrt (by positivity)] at hx
        linarith
      _ ≤ ((H : ℝ) - 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
  calc
    (2 : ℝ) ^ u = (2 : ℝ) ^ (u : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((H.pred : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hstep
    _ = ((2 : ℝ) ^ H.pred) ^ ε := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      exact_mod_cast (Nat.pow_pred_clog_lt_self (b := 2) (by decide) hn).le

-- 读法：对每个 `ᶠ h : ℝ in atTop`，`C * (Real.log h) ^ 2` 不超过 `h ^ ε`。这里调用 `le_abs_self`。
theorem cost_le (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in atTop, C * (Real.log h) ^ 2 ≤ h ^ ε := by
  have hl := (isLittleO_log_rpow_rpow_atTop 2 hε).const_mul_left C
  filter_upwards [eventually_ge_atTop 0, hl.eventuallyLE] with h hh hle
  rw [Real.rpow_two, Real.norm_of_nonneg (Real.rpow_nonneg hh ε)] at hle
  exact (le_abs_self _).trans hle

end OAI.LinearAlgebra.MatrixExponent.Shaving
end

/-!
# 所有宽度尺度共用的一个有限扩域

局部恒等式用到的固定扩域必须可嵌入工作域。将目标基数向上取整为该固定扩域阶数的幂次，既得到基数的多项式上界，也得到扩张次数的对数上界。

**英文原文**

A single finite extension for all width scales

A fixed extension for the local identities must embed into the working
field. Rounding a target cardinality up to a power of its order gives
both the polynomial upper bound and the logarithmic degree bound.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

-- 读法：证明中先建立 `hQ`，即 `1 < Q`。
theorem extension (F L : Type) [Field F] [Field L] [Finite L] [Algebra F L] (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ h : ℕ in atTop,
      ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K) (_ : Algebra F K)
        (_ : IsScalarTower F L K) (_ : Module.Finite F K),
        A * (1 + h ^ 4) ^ A ≤ Fintype.card K ∧ Fintype.card K ≤ h ^ (5 * A + 2) ∧
        (Module.finrank F K : ℝ) ≤ C * Real.log h := by
  let Q := Nat.card L
  have hQ : 1 < Q := Finite.one_lt_card
  let B := 5 * A + 1
  let C := (Module.finrank F L : ℝ) * (B + 1) / Real.log Q
  -- 推导：记下中间结论 `hlog`：`0 < Real.log (Q : ℝ)`。
  have hlog : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have : Module.Finite F L := Module.Finite.of_finite
  have hdim : 0 < Module.finrank F L := Module.finrank_pos
  refine ⟨C, by unfold C; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop Q] with h hA hq
  have hh : 1 < h := hQ.trans_le hq
  have hb : 0 < B := by dsimp [B]; omega
  have hl : 1 < h ^ B := Nat.one_lt_pow hb.ne' hh
  let n := Nat.clog Q (h ^ B)
  have hn : 0 < n := Nat.clog_pos hQ hl
  have : NeZero n := ⟨hn.ne'⟩
  let p := ringChar L
  have : Fact p.Prime := ⟨CharP.char_is_prime L p⟩
  let K := FiniteField.Extension L p n
  let : Fintype K := Fintype.ofFinite _
  let : Algebra F K := Algebra.compHom K (algebraMap F L)
  have : IsScalarTower F L K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- 推导：记下中间结论 `hc`：`Fintype.card K = Q ^ n`。
  have hc : Fintype.card K = Q ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact FiniteField.natCard_extension L p n
  have hlo : h ^ B ≤ Q ^ n := Nat.le_pow_clog hQ _
  have hhi : Q ^ n ≤ h ^ (B + 1) := by
    rw [show n = n.pred + 1 from (Nat.succ_pred_eq_of_pos hn).symm, pow_succ, pow_succ]
    exact Nat.mul_le_mul (Nat.pow_pred_clog_lt_self hQ hl).le hq
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.of_finite, ?_, by rwa [hc], ?_⟩
  · rw [hc]
    -- 推导：记下中间结论 `hp`：`1 + h ^ 4 ≤ h ^ 5`。
    have hp : 1 + h ^ 4 ≤ h ^ 5 := by
      rw [show h ^ 5 = h * h ^ 4 by ring]
      have := Nat.mul_le_mul_right (h ^ 4) hh
      have := Nat.one_le_pow 4 h (by omega)
      omega
    calc
      _ ≤ h * (h ^ 5) ^ A := Nat.mul_le_mul hA (Nat.pow_le_pow_left hp A)
      _ = h ^ B := by unfold B; rw [pow_succ' h (5 * A), pow_mul]
      _ ≤ _ := hlo
  · have he : (Q : ℝ) ^ n ≤ (h : ℝ) ^ (B + 1 : ℕ) := by exact_mod_cast hhi
    have hd := Real.log_le_log (by positivity) he
    rw [Real.log_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] at hd
    rw [← Module.finrank_mul_finrank F L K, Nat.cast_mul,
      show Module.finrank L K = n from FiniteField.finrank_extension L p n]
    calc
      _ ≤ (Module.finrank F L : ℝ) * ((B + 1) * Real.log h / Real.log Q) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hlog).mpr hd) (by positivity)
      _ = _ := by unfold C; ring

end OAI.LinearAlgebra.MatrixExponent.Shaving
end

section
/-!
# 在各阶段保持工作域固定

只会用到由有限多项组成的宽度指数序列。因此不要求阈值对连续变化的所有可能指数都统一适用。

**英文原文**

Keeping the working field fixed across stages

Only a finite progression of width exponents is used. Uniformity of
a cutoff in the continuum of possible exponents is unnecessary.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

-- 读法：`dictionary` 的取值由 `2 ^ ((Nat.clog 2 (Nat.clog 2 n)) ^ 2)` 给出。
/-- 名称的数量足以容纳任意多项式大小的字典。

英文原文：Enough names to include any polynomial-sized dictionary.
-/
def dictionary (n : ℕ) := 2 ^ ((Nat.clog 2 (Nat.clog 2 n)) ^ 2)

-- 读法：`UniformStage` 的结果类型为 `Prop`。
/-- 单个阶段的结论，对大小处于允许区间内的所有域一致。

英文原文：One stage, uniformly over fields in the permitted size window.
-/
def UniformStage (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ (α : ℝ) (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra F L),
      0 < α ∧ ∀ a b ξ : ℝ, 0 < a → a < α → β ≤ b → b ≤ 1 / 2 → 0 < ξ →
        ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Fintype K] [Algebra L K]
          [Algebra F K] [IsScalarTower F L K], let h := Nat.clog 2 n
          A * (1 + h ^ 4) ^ A ≤ Fintype.card K → Fintype.card K ≤ h ^ (5 * A + 2) →
          ArityStep K n (dictionary n) (dictionary n) b δ a ξ

-- 读法：要证明的命题是 `ArityReduction F`。
theorem UniformStage.reduction {F : Type} [Field F] (step : UniformStage F) :
    ArityReduction F := by
  intro δ β hd hd' hb hb'
  obtain ⟨α, A, L, _, _, _, hα, hs⟩ := step δ β hd hd' hb hb'
  refine ⟨α, hα, ?_⟩
  intro a J ha ha' _ hJ ξ hx
  have hs' (j : Fin J) := hs a (β + (1 + δ) * a * j.val) ξ ha ha'
    (le_add_of_nonneg_right (by positivity)) (le_trans (by gcongr; exact j.isLt.le) hJ) hx
  obtain ⟨C, hC, he⟩ := extension F L A
  have ht : Tendsto (Nat.clog 2) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [tendsto_height.eventually_ge_atTop (B : ℝ)] with n hn
    exact_mod_cast hn
  refine ⟨C, hC, ?_⟩
  filter_upwards [ht.eventually he, eventually_all.mpr hs'] with n hf hu
  -- 推导：从 `hf` 中取出 `K, _, _, _, _, _, _, hlo, hhi, hdeg`。
  obtain ⟨K, _, _, _, _, _, _, hlo, hhi, hdeg⟩ := hf
  exact ⟨K, inferInstance, inferInstance, inferInstance, fun _ => dictionary n, hdeg,
    fun j hj => hu ⟨j, hj⟩ K hlo hhi⟩

end OAI.LinearAlgebra.MatrixExponent.Shaving
end
