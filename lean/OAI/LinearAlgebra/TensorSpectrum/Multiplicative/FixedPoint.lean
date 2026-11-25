-- 本文件所属证明环节：从紧凸集中的轨道出发，以有限几何权重平均构造任意精确的近似特征态，再用紧致性得到精确的归一化乘法不动点。
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Averages
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Compactness
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Error

/-!
# 归一化乘法的紧凸不动点定理

这里直接证明附录 A.2 所需的特定不动点定理。有限几何加权平均给出近似特征状态，整个状态集的紧性则给出精确特征状态。证明无须假设一般的 Schauder 定理或其他不动点前提。

**英文原文**

A compact convex fixed-point theorem for normalized multiplication

This proves the particular fixed-point theorem needed in Appendix A.2 directly.
Finite geometric averages supply approximate eigenstates; compactness of the
whole state set supplies an exact eigenstate. No general Schauder theorem or
fixed-point premise is assumed.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

-- 读法：存在 `f ∈ K`，`projective z f` 等于 `f`。
/-- 若归一化正函数的非空紧凸集合在归一化乘法下保持不变，则该映射在其中存在不动点。

英文原文：A nonempty compact convex set of normalized positive functions, preserved by
normalized multiplication, contains a fixed point of that map.
-/
theorem projective_fixedPoint_of_compact_convex
    (K : Set (S → ℝ)) (z : S) (B : S → ℝ)
    (hK : K.Nonempty) (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hunit : ∀ f ∈ K, f 1 = 1)
    (hbound : ∀ f ∈ K, ∀ x, 0 ≤ f x ∧ f x ≤ B x)
    (hlower : ∀ f ∈ K, 1 ≤ f z)
    (hinvariant : MapsTo (projective z) K K) :
    ∃ f ∈ K, projective z f = f := by
  obtain ⟨f₀, hf₀⟩ := hK
  have hunit₀ : f₀ 1 = 1 := hunit f₀ hf₀
  -- 推导：记下中间结论 `hB`：`∀ x, 0 ≤ B x`。
  have hB : ∀ x, 0 ≤ B x := fun x => (hbound f₀ hf₀ x).1.trans (hbound f₀ hf₀ x).2
  have hM : 1 ≤ B z := (hlower f₀ hf₀).trans (hbound f₀ hf₀ z).2
  have ha : ∀ n, 1 ≤ projectiveMass z f₀ n :=
    projectiveMass_one_le K z f₀ hf₀ hunit₀ hlower hinvariant
  have haM : ∀ n, projectiveMass z f₀ n ≤ (B z) ^ n :=
    projectiveMass_le_pow K z f₀ hf₀ hunit₀ hlower hinvariant (B z)
      (fun f hf => (hbound f hf z).2)
  have ho : ∀ n, projectiveOrbit z f₀ n ∈ K :=
    projectiveOrbit_mem K z f₀ hf₀ hinvariant
  have hz : ∀ n, projectiveOrbit z f₀ n z ≠ 0 := fun n =>
    (zero_lt_one.trans_le (hlower _ (ho n))).ne'
  obtain ⟨r, hr1, hrM, hweights⟩ :=
    MultiplicativeGrowth.exists_approximate_weights (projectiveMass z f₀) (B z)
      ha hM haM
  have happrox : ∀ ε : ℝ, 0 < ε →
      ∃ f ∈ K, ∀ x, |f (z * x) - r * f x| ≤ ε * B x := by
    intro ε hε
    let η : ℝ := ε / (2 * B z + 1)
    -- 推导：记下中间结论 `hden`：`0 < 2 * B z + 1`。
    have hden : 0 < 2 * B z + 1 := by linarith
    have hη : 0 < η := div_pos hε hden
    have hηeq : (2 * B z + 1) * η = ε := by
      dsimp [η]
      field_simp [hden.ne']
    obtain ⟨s, n, hs, hsr, hclose, hlarge, hterminal⟩ := hweights η hη (1 / η)
    let A : ℝ := MultiplicativeGrowth.weightedSum (projectiveMass z f₀) s n
    have hA : 0 < A :=
      projective_weightedSum_pos K z f₀ hf₀ hunit₀ hlower hinvariant s hs n
    let q : ℝ := projectiveMass z f₀ (n + 1) / s ^ (n + 1) / A
    let d : ℝ := 1 / A
    -- 推导：记下中间结论 `hq0`：`0 ≤ q`。
    have hq0 : 0 ≤ q :=
      div_nonneg (div_nonneg (zero_le_one.trans (ha (n + 1))) (pow_nonneg hs.le _)) hA.le
    have hqη : q ≤ η := ((div_lt_iff₀ hA).mpr hterminal).le
    have hd0 : 0 ≤ d := div_nonneg zero_le_one hA.le
    have hdη : d ≤ η := by
      apply (div_le_iff₀ hA).mpr
      have h := (div_lt_iff₀ hη).mp hlarge
      nlinarith
    let f := projectiveAverage z f₀ s n
    have hf : f ∈ K := projectiveAverage_mem K hconvex z f₀ hf₀ hunit₀ hlower
      hinvariant s hs n
    refine ⟨f, hf, ?_⟩
    intro x
    have hres : f (z * x) - s * f x =
        s * (q * projectiveOrbit z f₀ (n + 1) x - d * f₀ x) := by
      calc
        f (z * x) - s * f x =
            s * (q * projectiveOrbit z f₀ (n + 1) x - f₀ x / A) :=
          projectiveAverage_residual z f₀ hunit₀ hz s hs n x
        _ = s * (q * projectiveOrbit z f₀ (n + 1) x - d * f₀ x) := by
          dsimp [d]
          ring
    have herr := projective_residual_error_bound
      (f (z * x)) (f x) (projectiveOrbit z f₀ (n + 1) x) (f₀ x)
      q d s r (B z) (B x) η (hbound f hf x)
      (hbound _ (ho (n + 1)) x) (hbound f₀ hf₀ x)
      ⟨hq0, hqη⟩ ⟨hd0, hdη⟩ ⟨hs.le, hsr.le.trans hrM⟩
      ⟨sub_nonneg.mpr hsr.le, hclose.le⟩ hres
    calc
      |f (z * x) - r * f x| ≤ (2 * B z + 1) * η * B x := herr
      _ = ε * B x := by rw [hηeq]
  -- 推导：从 `eigenstate_of_approximate K z r B hB hcompact happrox` 中取出 `f, hf, heigen`。
  obtain ⟨f, hf, heigen⟩ := eigenstate_of_approximate K z r B hB hcompact happrox
  refine ⟨f, hf, ?_⟩
  exact (projective_fixed_iff z f (zero_lt_one.trans_le (hlower f hf)).ne').mpr
    (eigenSlice_mem_multiplicativeSet z r f heigen (hunit f hf))

end OAI.LinearAlgebra.TensorSpectrum
