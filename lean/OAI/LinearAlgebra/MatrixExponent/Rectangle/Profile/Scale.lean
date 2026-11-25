-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum.FaceZero

section
/-!
# 伸缩与两个单坐标斜率

让一个宽度增大、另一个宽度减小，所用因子互为倒数。齐次性给出两个对数价格之差的精确值。对增量的有理下界取极限时，无需假定双宽度剖面可微。

**英文原文**

Dilation and the two one-coordinate slopes

Vary one width forward and the other backward by reciprocal factors.
Homogeneity gives the exact difference of the two log-prices. Taking
the limit in rational lower bounds on the increments needs no
differentiability of the two-width profile.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter
open scoped Topology

-- 读法：`p * r / (Real.exp (x / p) + r) ≤ y - x` 与 `p * r / Real.exp (y / p) ≤ y - x` 同时成立。
private theorem log_growth {x y p r : ℝ} (hp : 0 < p) (hr : 0 ≤ r)
    (h : r ≤ Real.exp (y / p) - Real.exp (x / p)) :
    p * r / (Real.exp (x / p) + r) ≤ y - x ∧ p * r / Real.exp (y / p) ≤ y - x := by
  let a := Real.exp (x / p)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < a + r := by positivity
  have hc : a + r ≤ Real.exp (y / p) := by unfold a; linarith
  have hd := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne', show Real.log a = x / p from Real.log_exp _] at hd
  have he := Real.log_le_log hb hc
  rw [Real.log_exp] at he
  have heq : a / (a + r) - 1 = -r / (a + r) := by field_simp; ring
  rw [heq, neg_div] at hd
  have hlo : p * r / (a + r) ≤ y - x := by
    rw [mul_div_assoc, mul_comm, ← le_div_iff₀ hp, sub_div]
    linarith
  exact ⟨hlo, (div_le_div_of_nonneg_left (by positivity) hb hc).trans hlo⟩

-- 读法：`a * y * (L / Real.exp (P x y / a)) + b * x * (M / Real.exp (P x y / b))` 不超过 `D`。
theorem pair_growth (P : ℝ → ℝ → ℝ) {x y a b L M D : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (hM : 0 < M) (hD : 0 ≤ D)
    (hscale : ∀ u : ℝ, 1 < u → P x (u * y) = P (x / u) y + D * Real.log u)
    (h₁ : ∀ t, y ≤ t → L * (t - y) ≤ Real.exp (P x t / a) - Real.exp (P x y / a))
    (h₂ : ∀ s, 0 < s → s ≤ x → M * (x - s) ≤ Real.exp (P x y / b) - Real.exp (P s y / b)) :
    a * y * (L / Real.exp (P x y / a)) + b * x * (M / Real.exp (P x y / b)) ≤ D := by
  let F (t : ℝ) := a * y * L / (Real.exp (P x y / a) + L * t * y) +
    b * x * M / ((1 + t) * Real.exp (P x y / b))
  have hbound (t : ℝ) (ht : 0 < t) : F t ≤ D := by
    -- 推导：记下中间结论 `hu`：`1 < 1 + t`。
    have hu : 1 < 1 + t := by linarith
    have hx' : x / (1 + t) ≤ x := div_le_self hx.le hu.le
    have hy' : y ≤ (1 + t) * y := le_mul_of_one_le_left hy.le hu.le
    have hl := (log_growth ha (mul_nonneg hL.le (sub_nonneg.mpr hy')) (h₁ _ hy')).1
    have hr := (log_growth hb (mul_nonneg hM.le (sub_nonneg.mpr hx'))
      (h₂ _ (by positivity) hx')).2
    rw [show L * ((1 + t) * y - y) = L * t * y by ring, hscale (1 + t) hu] at hl
    have hh : Real.log (1 + t) ≤ t := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t)]
    apply le_of_mul_le_mul_right _ ht
    calc
      F t * t = a * (L * t * y) / (Real.exp (P x y / a) + L * t * y) +
          b * (M * (x - x / (1 + t))) / Real.exp (P x y / b) := by
        unfold F
        rw [show x - x / (1 + t) = x * t / (1 + t) by field_simp; ring]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ D * Real.log (1 + t) := by linarith only [hl, hr]
      _ ≤ D * t := mul_le_mul_of_nonneg_left hh hD
  have hc : ContinuousAt F 0 := by unfold F; fun_prop (disch := positivity)
  -- 推导：记下中间结论 `hh`：`F 0 ≤ D`。
  have hh : F 0 ≤ D := le_of_tendsto (hc.continuousWithinAt (s := Set.Ioi 0))
    (Filter.Eventually.mono self_mem_nhdsWithin hbound)
  simpa [F, mul_div_assoc] using hh

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 由整数倍伸缩得到连续剖面

通过统一缩放格点，从下方逼近每条射线。作整数倍伸缩后，每个这样的下界都最终成立。从上方控制任意近似时，只需稍稍放大目标宽度。

**英文原文**

A continuum profile from integer dilations

Approximate each ray from below by a common rescaling of a lattice
point. Integer dilation makes every such lower bound valid eventually.
Slightly enlarging the target widths bounds arbitrary approximations
from above.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

-- 读法：结构的字段包括 `nonneg`、`mono`、`bound`、`dilate`。
structure Scaling (M : (ι → ℕ) → ℝ) : Prop where
  nonneg : ∀ L, 0 ≤ M L
  mono : Monotone M
  bound : ∀ L, M L ≤ ∑ i, (L i : ℝ)
  dilate : ∀ (k : ℕ) L, (k : ℝ) * M L ≤ M (fun i => k * L i)

-- 读法：`candidates` 的取值由 `{v | ∃ L : ι → ℕ, ∃ c : ℝ, 0 < c ∧ (∀ i, c * L i < t i) ∧ v = c * M L}` 给出。
private def candidates (M : (ι → ℕ) → ℝ) (t : ι → ℝ) : Set ℝ :=
  {v | ∃ L : ι → ℕ, ∃ c : ℝ, 0 < c ∧ (∀ i, c * L i < t i) ∧ v = c * M L}

-- 读法：`scale` 的取值由 `sSup (candidates M t)` 给出。
def scale (M : (ι → ℕ) → ℝ) (t : ι → ℝ) := sSup (candidates M t)

namespace Scaling

variable {M : (ι → ℕ) → ℝ} (h : Scaling M) {t u : ι → ℝ} {c : ℝ}

omit [Fintype ι] in
-- 读法：要证明的命题是 `(candidates M t).Nonempty`。
private theorem inhabited (ht : ∀ i, 0 < t i) : (candidates M t).Nonempty :=
  ⟨1 * M 0, 0, 1, zero_lt_one, by simpa using ht, rfl⟩

include h

-- 读法：结论为 `∑ i, t i ∈ upperBounds (candidates M t)`。
private theorem upper : ∑ i, t i ∈ upperBounds (candidates M t) := by
  rintro _ ⟨L, c, hc, hL, rfl⟩
  calc
    _ ≤ c * ∑ i, (L i : ℝ) := mul_le_mul_of_nonneg_left (h.bound L) hc.le
    _ ≤ _ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => (hL i).le)

-- 读法：`scale M t` 不超过 `∑ i, t i`。使用 `csSup_le` 给出的结论。
theorem scale_bound (ht : ∀ i, 0 < t i) : scale M t ≤ ∑ i, t i :=
  csSup_le (inhabited ht) h.upper

-- 读法：`c * M L` 不超过 `scale M t`。使用 `le_csSup` 给出的结论。
theorem le_scale {L : ι → ℕ} (hc : 0 < c) (hL : ∀ i, c * L i < t i) : c * M L ≤ scale M t :=
  le_csSup ⟨_, h.upper⟩ ⟨L, c, hc, hL, rfl⟩

-- 读法：`0` 不超过 `scale M t`。这里调用 `mul_nonneg`。
theorem scale_nonneg (ht : ∀ i, 0 < t i) : 0 ≤ scale M t := by
  have := h.le_scale (L := 0) (t := t) zero_lt_one (by simpa using ht)
  simpa using (mul_nonneg zero_le_one (h.nonneg 0)).trans this

-- 读法：`0` 严格小于 `scale M t`。这里调用 `eventually_all.mpr`。
theorem scale_pos (ht : ∀ i, 0 < t i) {L : ι → ℕ} (hL : 0 < M L) : 0 < scale M t := by
  have he : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ i, c * L i < t i := by
    apply eventually_all.mpr
    intro i
    have hd : Tendsto (fun c : ℝ => c * L i) (𝓝[>] 0) (𝓝 0) := by
      have h₀ : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using h₀.mul_const (L i : ℝ)
    exact hd.eventually_lt_const (ht i)
  obtain ⟨c, hc, hc'⟩ := (he.and self_mem_nhdsWithin).exists
  exact (mul_pos hc' hL).trans_le (h.le_scale hc' hc)

-- 读法：`scale M t` 不超过 `scale M u`。这里调用 `csSup_le`。
theorem scale_mono (ht : ∀ i, 0 < t i) (htu : t ≤ u) : scale M t ≤ scale M u := by
  apply csSup_le (inhabited ht)
  rintro _ ⟨L, c, hc, hL, rfl⟩
  exact h.le_scale hc (fun i => (hL i).trans_le (htu i))

-- 读法：`scale M (c • t)` 等于 `c * scale M t`。这里调用 `le_antisymm`。
theorem scale_smul (ht : ∀ i, 0 < t i) (hc : 0 < c) : scale M (c • t) = c * scale M t := by
  have hu : ∀ i, 0 < (c • t) i := fun i => mul_pos hc (ht i)
  apply le_antisymm
  · apply csSup_le (inhabited hu)
    rintro _ ⟨L, a, ha, hL, rfl⟩
    have he : ∀ i, (a / c) * L i < t i := by
      intro i
      rw [div_mul_eq_mul_div, div_lt_iff₀ hc, mul_comm (t i)]
      exact hL i
    have hh := h.le_scale (div_pos ha hc) he
    rwa [div_mul_eq_mul_div, div_le_iff₀ hc, mul_comm (scale M t)] at hh
  · rw [mul_comm, ← le_div_iff₀ hc]
    apply csSup_le (inhabited ht)
    rintro _ ⟨L, a, ha, hL, rfl⟩
    rw [le_div_iff₀ hc, mul_comm _ c, ← mul_assoc]
    apply h.le_scale (mul_pos hc ha)
    intro i
    rw [mul_assoc]
    exact mul_lt_mul_of_pos_left (hL i) hc

-- 读法：存在 `u : ι → ℝ`，`(∀ i, t i < u i)` 与 `scale M u < b` 同时成立。
private theorem enlarge (ht : ∀ i, 0 < t i) {b : ℝ} (hb : scale M t < b) :
    ∃ u : ι → ℝ, (∀ i, t i < u i) ∧ scale M u < b := by
  have he : ∀ᶠ c in 𝓝[>] (1 : ℝ), c * scale M t < b :=
    ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _).eventually_lt_const (by simpa using hb)
  obtain ⟨c, hc, hc'⟩ := (he.and self_mem_nhdsWithin).exists
  refine ⟨c • t, fun i => lt_mul_of_one_lt_left (ht i) hc', ?_⟩
  rwa [h.scale_smul ht (zero_lt_one.trans hc')]

-- 读法：要证明的命题是 `ContinuousAt (scale M) t`。这里调用 `tendsto_order.mpr`。
theorem scale_continuous (ht : ∀ i, 0 < t i) : ContinuousAt (scale M) t := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_, ⟨L, c, hc, hL, rfl⟩, ha'⟩ := exists_lt_of_lt_csSup (inhabited ht) ha
    have he : ∀ᶠ u in 𝓝 t, ∀ i, c * L i < u i := eventually_all.mpr
      (fun i => (continuous_apply i).continuousAt.tendsto.eventually_const_lt (hL i))
    exact he.mono fun _ hu => ha'.trans_le (h.le_scale hc hu)
  · intro b hb
    obtain ⟨u, hu, hu'⟩ := h.enlarge ht hb
    have he : ∀ᶠ v in 𝓝 t, ∀ i, 0 < v i ∧ v i < u i := eventually_all.mpr (fun i =>
      (continuous_apply i).continuousAt.tendsto.eventually (Ioo_mem_nhds (ht i) (hu i)))
    exact he.mono fun _ hv => (h.scale_mono (fun i => (hv i).1) (fun i => (hv i).2.le)).trans_lt hu'

-- 读法：`(fun n => M (L n) / N n)` 沿滤子 `l` 收敛到 `(scale M t)`。这里调用 `tendsto_order.mpr`。
theorem limit (ht : ∀ i, 0 < t i) {α : Type*} {l : Filter α} {N : α → ℝ}
    (hN : Tendsto N l atTop) {L : α → ι → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (t i))) :
    Tendsto (fun n => M (L n) / N n) l (𝓝 (scale M t)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_, ⟨W, c, hc, hW, rfl⟩, ha'⟩ := exists_lt_of_lt_csSup (inhabited ht) ha
    let k n := ⌈c * N n⌉₊
    have hk : Tendsto (fun n => (k n : ℝ) / N n) l (𝓝 c) :=
      (tendsto_nat_ceil_mul_div_atTop hc.le).comp hN
    -- 推导：记下中间结论 `he`：`∀ᶠ n in l, ∀ i, (k n : ℝ) / N n * W i < L n i / N n`。
    have he : ∀ᶠ n in l, ∀ i, (k n : ℝ) / N n * W i < L n i / N n :=
      eventually_all.mpr (fun i => (hk.mul_const _).eventually_lt (hL i) (hW i))
    filter_upwards [hN.eventually_gt_atTop 0, he] with n hn he
    have hw : (fun i => k n * W i) ≤ L n := by
      intro i
      specialize he i
      rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hn] at he
      exact_mod_cast he.le
    refine ha'.trans_le ((le_div_iff₀ hn).mpr ?_)
    rw [mul_right_comm]
    exact (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (h.nonneg W)).trans
      ((h.dilate _ _).trans (h.mono hw))
  · intro b hb
    -- 推导：从 `h.enlarge ht hb` 中取出 `u, hu, hu'`。
    obtain ⟨u, hu, hu'⟩ := h.enlarge ht hb
    have he := eventually_all.mpr (fun i => (hL i).eventually_lt_const (hu i))
    filter_upwards [hN.eventually_gt_atTop 0, he] with n hn he
    refine lt_of_le_of_lt ?_ hu'
    rw [div_eq_inv_mul]
    apply h.le_scale (inv_pos.mpr hn)
    simpa only [← div_eq_inv_mul] using he

-- 读法：`(fun N : ℝ => M (fun i => ⌊N * t i⌋₊) / N)` 沿滤子 `atTop` 收敛到 `(scale M t)`。这里调用 `h.limit`。
theorem floor_limit (ht : ∀ i, 0 < t i) :
    Tendsto (fun N : ℝ => M (fun i => ⌊N * t i⌋₊) / N) atTop (𝓝 (scale M t)) := by
  apply h.limit ht tendsto_id
  intro i
  simpa only [id_eq, mul_comm (t i)] using tendsto_nat_floor_mul_div_atTop (ht i).le

end Scaling
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 两个耦合行的公共斜率

取一个双宽度比值的上确界可得公共极限斜率。即使两宽度不同，也只需在待检验宽度之外使用一次三倍化，即可用每条更早的割线斜率给出该比值的上界。

**英文原文**

Common slope of two coupled rows

Taking the supremum of a two-width quotient gives the common limiting
slope. A single tripling beyond the widths under test bounds that
quotient by every earlier secant, even at unequal widths.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Set

-- 读法：结构的字段包括 `pos`、`concave`、`trip`。
structure Curve (f g : ℝ → ℝ) (a : ℝ) : Prop where
  pos : ∀ x, 0 < x → 0 < f x
  concave : ConcaveOn ℝ (Ioi 0) f
  trip : ∀ x, 0 < x → 2 * f x + g x ≤ f (3 * x + a)

variable {f g : ℝ → ℝ} {a L x y z s t N : ℝ}

-- 读法：`L * (t - s)` 不超过 `f t - f s`。这里调用 `le_div_iff₀`。
private theorem Curve.advance (h : Curve f g a) (ha : 0 < a) (hs : 0 < s) (ht : s < t)
    (hN : t ≤ N) (hL : L * (2 * N + a) = f N + g N) : L * (t - s) ≤ f t - f s := by
  have hN' : 0 < N := (hs.trans ht).trans_le hN
  have hz : N < 3 * N + a := by linarith
  have lo : L ≤ (f (3 * N + a) - f N) / (3 * N + a - N) :=
    (le_div_iff₀ (sub_pos.mpr hz)).2 (by linarith [h.trip N hN'])
  apply (le_div_iff₀ (sub_pos.mpr ht)).mp
  rcases eq_or_lt_of_le hN with rfl | hN
  · exact lo.trans (h.concave.slope_anti_adjacent hs (hs.trans (ht.trans hz)) ht hz)
  · exact lo.trans ((h.concave.slope_anti_adjacent (hs.trans ht) (hN'.trans hz) hN hz).trans
      (h.concave.slope_anti_adjacent hs hN' ht hN))

-- 读法：`ratios` 的取值由 `{v | ∃ y z : ℝ, 0 < y ∧ 0 < z ∧ v = (f y + g z) / (y + z + a)}` 给出。
private def ratios (f g : ℝ → ℝ) (a : ℝ) : Set ℝ :=
  {v | ∃ y z : ℝ, 0 < y ∧ 0 < z ∧ v = (f y + g z) / (y + z + a)}

-- 读法：`common` 的取值由 `sSup (ratios f g a)` 给出。
def common (f g : ℝ → ℝ) (a : ℝ) := sSup (ratios f g a)

-- 读法：`common f g a` 等于 `common g f a`。
theorem common_comm (f g : ℝ → ℝ) (a : ℝ) : common f g a = common g f a := by
  unfold common
  congr 1
  ext v
  constructor <;> rintro ⟨y, z, hy, hz, rfl⟩ <;> exact ⟨z, y, hz, hy, by ring⟩

-- 读法：`(f t - f s) / (t - s)` 属于 `upperBounds (ratios f g a)`。
private theorem upper (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a)
    (hs : 0 < s) (ht : s < t) : (f t - f s) / (t - s) ∈ upperBounds (ratios f g a) := by
  rintro _ ⟨y, z, hy, hz, rfl⟩
  let N := t + y + z
  have hN : 0 < N := by unfold N; linarith
  let L := (f N + g N) / (2 * N + a)
  have he : L * (2 * N + a) = f N + g N := div_mul_cancel₀ _ (by positivity)
  have h₁ := hf.advance ha hy (by unfold N; linarith : y < N) le_rfl he
  have h₂ := hg.advance ha hz (by unfold N; linarith : z < N) le_rfl (he.trans (add_comm _ _))
  have h₃ := hf.advance ha hs ht (by unfold N; linarith : t ≤ N) he
  refine le_trans ?_ ((le_div_iff₀ (sub_pos.mpr ht)).mpr h₃)
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h₁, h₂, he])

-- 读法：`f y + g z` 不超过 `common f g a * (y + z + a)`。这里调用 `div_le_iff₀`。
theorem common_bound (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a)
    (hy : 0 < y) (hz : 0 < z) : f y + g z ≤ common f g a * (y + z + a) := by
  apply (div_le_iff₀ (by positivity)).mp
  exact le_csSup ⟨_, upper ha hf hg zero_lt_one (by norm_num : (1 : ℝ) < 2)⟩ ⟨y, z, hy, hz, rfl⟩

-- 读法：`0` 严格小于 `common f g a`。
theorem common_pos (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a) : 0 < common f g a :=
  pos_of_mul_pos_left ((add_pos (hf.pos 1 zero_lt_one) (hg.pos 1 zero_lt_one)).trans_le
    (common_bound ha hf hg zero_lt_one zero_lt_one)) (by positivity)

-- 读法：`common f g a * (t - s)` 不超过 `f t - f s`。这里调用 `le_div_iff₀`。
theorem common_step (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a)
    (hs : 0 < s) (ht : s ≤ t) : common f g a * (t - s) ≤ f t - f s := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  apply (le_div_iff₀ (sub_pos.mpr ht)).mp
  exact csSup_le ⟨_, 1, 1, zero_lt_one, zero_lt_one, rfl⟩ (upper ha hf hg hs ht)

-- 读法：`common f g a * x` 不超过 `f x`。
theorem common_lower (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a) (hx : 0 < x) :
    common f g a * x ≤ f x := by
  by_contra! he
  let L := common f g a
  have hL := common_pos ha hf hg
  let s := x - f x / L
  have hs : 0 < s := sub_pos.mpr ((div_lt_iff₀ hL).2 (by linarith))
  have hs' : s ≤ x := sub_le_self _ (div_nonneg (hf.pos _ hx).le hL.le)
  have h := common_step ha hf hg hs hs'
  have hh : L * (x - s) = f x := by unfold s; rw [sub_sub_cancel, mul_div_cancel₀ _ hL.ne']
  rw [hh] at h
  linarith [hf.pos _ hs]

-- 读法：`f x` 不超过 `common f g a * (x + a)`。
theorem common_upper (ha : 0 < a) (hf : Curve f g a) (hg : Curve g f a) (hx : 0 < x) :
    f x ≤ common f g a * (x + a) := by
  have he := common_lower ha hg hf hx
  rw [common_comm g f] at he
  linarith only [he, common_bound ha hf hg hx hx]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

section
/-!
# 齐次缺损的强极小值原理

若在某条坐标射线上取正值，则径向伸缩时，其积分在一阶上严格下降。将三个坐标的增量相加并相消，可将这种下降量控制在伸缩参数的任意小倍数之内。

**英文原文**

Strong minimum principle for a homogeneous defect

A positive value on one coordinate ray makes its integral decrease
strictly at first order under radial dilation. Telescoping the three
coordinate increments bounds any such decrease by an arbitrarily
small multiple of the dilation parameter.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
open Filter Set

variable {D : Vec → ℝ} {v w : Vec}

-- 读法：`D (move v k t)` 等于 `0`。
private theorem ray_vanishes (h : Regular D) (hc : Comparison D)
    (hv : Positive v) (hz : D v = 0) (k : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    D (move v k t) = 0 := by
  change ray D v k t = 0
  rcases eq_or_lt_of_le ht with rfl | ht
  · simpa
  have hn : ∀ u, 0 ≤ u → 0 ≤ ray D v k u := fun _ hu => h.nonneg _ (hv.move k hu)
  by_contra hne
  obtain ⟨B, hB, hdrop⟩ := dilation (h.continuous _ hv k) hn (by simpa)
    ⟨t, ht, (hn t ht.le).lt_of_ne' hne⟩
  -- 推导：从 `h.convex v hv` 中取出 `C, hC, hconv`。
  obtain ⟨C, hC, hconv⟩ := h.convex v hv
  obtain ⟨E, hE, hswitch⟩ := hc v hv
  let S := v 0 + v 1 + v 2
  have hS : 0 < S := add_pos (add_pos (hv _) (hv _)) (hv _)
  have hmax (i : Fin 3) : v i ≤ S := by
    unfold S
    rw [← Fin.sum_univ_three]
    exact Finset.single_le_sum (fun j _ => (hv j).le) (Finset.mem_univ i)
  let R := B / (8 * (C * S + 1))
  have hR : 0 < R := by unfold R; positivity
  -- 推导：记下中间结论 `hcost`：`2 * C * S * R ≤ B / 4`。
  have hcost : 2 * C * S * R ≤ B / 4 := by
    have he : R * (8 * (C * S + 1)) = B := div_mul_cancel₀ _ (by positivity)
    linarith
  let r := R / (2 * Real.exp (2 * E + 4))
  have hr : 0 < r := by unfold r; positivity
  have hr' : 2 * r ≤ R := by
    have he : r * (2 * Real.exp (2 * E + 4)) = R := div_mul_cancel₀ _ (by positivity)
    have he' : 1 ≤ Real.exp (2 * E + 4) := Real.one_le_exp (by linarith)
    nlinarith only [he, he', hr]
  have hlog : Real.log (R / (2 * r)) = 2 * E + 4 := by
    -- 推导：记下中间结论 `he`：`R / (2 * r) = Real.exp (2 * E + 4)`。
    have he : R / (2 * r) = Real.exp (2 * E + 4) := by unfold r; field_simp
    rw [he, Real.log_exp]
  let ε := min 1 (r / (S * (2 * E + 6)))
  have hε : 0 < ε := by unfold ε; positivity
  have hε' : ε ≤ 1 := min_le_left _ _
  have hstep (i : Fin 3) : ε * v i * (2 * E + 6) ≤ r := calc
    _ ≤ ε * S * (2 * E + 6) := by gcongr; apply hmax
    _ ≤ r := by
      rw [mul_assoc]
      exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let ζ := ε * B / 16
  -- 推导：记下中间结论 `hζ`：`0 < ζ`。
  have hζ : 0 < ζ := by unfold ζ; positivity
  have hl := telescope h hv hz hC hE hconv
    (fun w hw i j => hswitch w hw i j ζ hζ) hε hε' hr hr' hlog hstep k
  obtain ⟨T, hT, hu, hl⟩ := ((eventually_ge_atTop 1).and ((hdrop ε hε hε').and hl)).exists
  have he : J D ((1 + ε) • v) k T =
      price (fun t => ray D v k (t / (1 + ε)) / (1 + ε)) (1 / T) T := by
    unfold J price
    apply intervalIntegral.integral_congr
    intro u hu
    have hu₀ : 0 ≤ u := (le_min (by positivity) (by positivity)).trans hu.1
    exact congrArg (· / u) (h.scale hv k (by positivity : 0 < 1 + ε) hu₀)
  rw [he] at hl
  change -2 * C * ε * S * R - 4 * ζ ≤ _ - price (ray D v k) (1 / T) T at hl
  unfold ζ at hl
  linarith only [hu, hl, mul_le_mul_of_nonneg_left hcost hε.le, mul_pos hε hB]

-- 读法：`D w` 等于 `0`。
private theorem vanishes_above (h : Regular D) (hc : Comparison D)
    (hv : Positive v) (hz : D v = 0) (hvw : v ≤ w) : D w = 0 := by
  let p (n : ℕ) (i : Fin 3) := if i.val < n then w i else v i
  have hp (n : ℕ) : Positive (p n) := by
    intro i
    unfold p
    split_ifs
    · exact (hv i).trans_le (hvw i)
    · exact hv i
  have hh (i : Fin 3) (hi : D (p i.val) = 0) : D (p (i.val + 1)) = 0 := by
    -- 推导：记下中间结论 `he`：`p (i.val + 1) = move (p i.val) i (w i - v i)`。
    have he : p (i.val + 1) = move (p i.val) i (w i - v i) := by
      funext j
      by_cases he : j = i
      · subst j; simp [move, p]
      · have hj : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp only [move, Function.update_of_ne he, p, hj]
    rw [he]
    exact ray_vanishes h hc (hp _) hi i (sub_nonneg.mpr (hvw i))
  have h₀ : p 0 = v := by funext i; simp [p]
  have h₃ : p 3 = w := by funext i; simp [p, i.isLt]
  rw [← h₃]
  exact hh 2 (hh 1 (hh 0 (h₀.symm ▸ hz)))

-- 读法：`D w` 等于 `0`。这里调用 `div_le_iff₀`。
/-- 只要内部有一个零点，在所有坐标均为正的整个区域内便恒为零。

英文原文：A single interior zero forces vanishing throughout the positive orthant.
-/
theorem vanishes (h : Regular D) (hc : Comparison D)
    (hv : Positive v) (hz : D v = 0) (hw : Positive w) : D w = 0 := by
  let s := ∑ i, v i / w i
  have hp (i) : 0 < v i / w i := div_pos (hv i) (hw i)
  have hs : 0 < s := Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
  have hvw : v ≤ s • w := by
    intro i
    exact (div_le_iff₀ (hw i)).mp
      (Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ i))
  have he := vanishes_above h hc hv hz hvw
  rw [h.homogeneous w hw s hs, div_eq_zero_iff] at he
  exact he.resolve_right hs.ne'

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum
end

section
/-!
# 三个临界宽度对处的截距匹配

将每个对数价格写成首个截距与归一化位移之和。每行中的两个位移之和至多为零。跨越一条边的两个位移之和至少为缩放后缺陷的相反数。若某个位移大于该误差的两倍，三个截距将沿一个环严格递增。

**英文原文**

Matching intercepts at the three critical width pairs

Write each log-price as its first intercept plus a normalized
displacement. The two displacements in each row sum to at most
zero. Across an edge the two displacements sum to at least minus
the scaled defect. A displacement exceeding twice this error would
force the three intercepts to increase strictly around a cycle.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Minimum

variable {u c d : Vec} {p : Fin 3 → Fin 3 → ℝ} {ε Δ : ℝ}

-- 读法：存在 `k : Fin 3`，`i ≠ k` 与 `j ≠ k` 同时成立。使用 `fin_cases` 给出的结论。
private theorem third (i j : Fin 3) (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

-- 读法：结构的字段包括 `symm`、`row`、`edge`。
/-- 一对临界宽度处的价格，其两种排列顺序共用这一价格。

英文原文：Price at a critical width pair, shared between its two orders.
-/
structure Critical (u c d : Vec) (p : Fin 3 → Fin 3 → ℝ) (Δ : ℝ) : Prop where
  symm : ∀ i j, p i j = p j i
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → p i j + p i k ≤ 2 * c i
  edge : ∀ i j, i ≠ j →
    d i * u j * Real.exp ((c i - p i j) / d i) + d j * u i * Real.exp ((c j - p j i) / d j) ≤
      d i * u j + d j * u i + Δ

-- 读法：`d * u + u * (c - p)` 不超过 `d * u * Real.exp ((c - p) / d)`。
private theorem linearize {d u c p : ℝ} (hd : 0 < d) (hu : 0 ≤ u) :
    d * u + u * (c - p) ≤ d * u * Real.exp ((c - p) / d) := by
  calc
    _ = d * u * ((c - p) / d + 1) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (mul_nonneg hd.le hu)

-- 读法：`w i j` 不超过 `2 * B`。
private theorem cycle_bound {w : Fin 3 → Fin 3 → ℝ} {c : Vec} {B : ℝ}
    (hB : 0 ≤ B) (he : ∀ i j, i ≠ j → -B ≤ w i j + w j i)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → w i j + w i k ≤ 0)
    (hc : ∀ i j, 0 < w i j → w j i < 0 → c i < c j)
    (i j : Fin 3) (h : i ≠ j) : w i j ≤ 2 * B := by
  by_contra! hh
  obtain ⟨k, hik, hjk⟩ := third i j h
  have h₁ := hr i j k h hik hjk
  have h₂ := he i k hik
  have h₃ := hr k i j hik.symm hjk.symm h
  have h₄ := he k j hjk.symm
  have h₅ := hr j k i hjk h.symm hik.symm
  have e₁ := hc i j (by linarith) (by linarith)
  have e₂ := hc j k (by linarith) (by linarith)
  have e₃ := hc k i (by linarith) (by linarith)
  exact (e₁.trans (e₂.trans e₃)).false

-- 读法：`-3 * (Δ / ε ^ 2) ≤ p i j - c i` 与 `p i j - c i ≤ 2 * (Δ / ε ^ 2)` 同时成立。
/-- 临界宽度对处的一致误差界，对臂长或距离都不要求有上界。

英文原文：Uniform error at a critical pair. No upper bound on the arm
lengths or distances is needed.
-/
theorem Critical.error (h : Critical u c d p Δ) (hd : Positive d) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hlo : ∀ i, ε ≤ u i) (hhi : ∀ i, u i ≤ 1) {i j : Fin 3} (hij : i ≠ j) :
    -3 * (Δ / ε ^ 2) ≤ p i j - c i ∧ p i j - c i ≤ 2 * (Δ / ε ^ 2) := by
  let w i j := (p i j - c i) / u i
  let B := Δ / ε ^ 2
  have hu i := hε.trans_le (hlo i)
  have hB : 0 ≤ B := by unfold B; positivity
  have heq i j : w i j * u i = p i j - c i := div_mul_cancel₀ _ (hu i).ne'
  have he i j (hij : i ≠ j) : -B ≤ w i j + w j i := by
    have hi := linearize (c := c i) (p := p i j) (hd i) (hu j).le
    -- 推导：记下中间结论 `hj`：`= linearize (c`。
    have hj := linearize (c := c j) (p := p j i) (hd j) (hu i).le
    have hlow : -Δ ≤ (w i j + w j i) * (u i * u j) := by
      rw [show (w i j + w j i) * (u i * u j) = (w i j * u i) * u j + (w j i * u j) * u i by ring,
        heq, heq]
      linarith only [hi, hj, h.edge i j hij]
    apply le_of_mul_le_mul_right _ (mul_pos (hu i) (hu j))
    refine le_trans ?_ hlow
    have he : ε ^ 2 ≤ u i * u j := by rw [pow_two]; exact mul_le_mul (hlo i) (hlo j) hε.le (hu i).le
    have := mul_le_mul_of_nonneg_left he hB
    rw [show B * ε ^ 2 = Δ from div_mul_cancel₀ _ (by positivity)] at this
    linarith
  have hr i j k (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : w i j + w i k ≤ 0 := by
    unfold w
    rw [← add_div]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [h.row i j k hij hik hjk]) (hu i).le
  have hc i j (hi : 0 < w i j) (hj : w j i < 0) : c i < c j := by
    have h₁ := mul_pos hi (hu i)
    have h₂ := mul_neg_of_neg_of_pos hj (hu j)
    rw [heq] at h₁ h₂
    linarith [h.symm i j]
  have h₁ := cycle_bound hB he hr hc i j hij
  -- 推导：记下中间结论 `h₂`：`-3 * B ≤ w i j`。
  have h₂ : -3 * B ≤ w i j := by linarith [cycle_bound hB he hr hc j i hij.symm, he i j hij]
  rw [← heq]
  have h₃ := mul_le_of_le_one_right hB (hhi i)
  constructor
  · exact (by linarith : -3 * B ≤ -3 * B * u i).trans (mul_le_mul_of_nonneg_right h₂ (hu i).le)
  · exact (mul_le_mul_of_nonneg_right h₁ (hu i).le).trans (by linarith : 2 * B * u i ≤ 2 * B)

-- 读法：`c i - c j` 不超过 `5 * (Δ / ε ^ 2)`。按 `i = j` 成立与否分情况。
theorem Critical.intercepts (h : Critical u c d p Δ) (hd : Positive d) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hlo : ∀ i, ε ≤ u i) (hhi : ∀ i, u i ≤ 1) (i j : Fin 3) :
    c i - c j ≤ 5 * (Δ / ε ^ 2) := by
  by_cases he : i = j
  · subst j; rw [sub_self]; positivity
  linarith only [(h.error hd hΔ hε hlo hhi he).1, (h.error hd hΔ hε hlo hhi (Ne.symm he)).2,
    h.symm i j]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 由多项式宽度剖面得到临界估计

**英文原文**

Critical estimates from polynomial width profiles
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Minimum

-- 读法：在后续公式中，`PairPrices` 是 `Fin 3 → Fin 3 → ℝ → ℝ → ℝ` 的缩写。
abbrev PairPrices := Fin 3 → Fin 3 → ℝ → ℝ → ℝ

-- 读法：`row` 的取值由 `Real.exp (P i j (u i) t / d i)` 给出。
def row (P : PairPrices) (d u : Vec) (i j : Fin 3) (t : ℝ) : ℝ :=
  Real.exp (P i j (u i) t / d i)

-- 读法：结构的字段包括 `symm`、`scale`、`curve`。
structure Family (P : PairPrices) (d u : Vec) (D : ℝ) : Prop where
  symm : ∀ i j x y, P i j x y = P j i y x
  scale : ∀ i j, i ≠ j → ∀ s x y : ℝ, 0 < s → 0 < x → 0 < y →
    P i j (s * x) (s * y) = P i j x y + D * Real.log s
  curve : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → Curve (row P d u i j) (row P d u i k) (u i)

-- 读法：`rate` 的取值由 `common (row P d u i (i + 1)) (row P d u i (i + 2)) (u i)` 给出。
/-- 第一宽度为 `u i` 时的公共斜率。

英文原文：Common slope at first width `u i`.
-/
def rate (P : PairPrices) (d u : Vec) (i : Fin 3) : ℝ :=
  common (row P d u i (i + 1)) (row P d u i (i + 2)) (u i)

-- 读法：`intercept` 的取值由 `d i * Real.log (rate P d u i)` 给出。
def intercept (P : PairPrices) (d u : Vec) (i : Fin 3) : ℝ :=
  d i * Real.log (rate P d u i)

variable {P : PairPrices} {d u : Vec} {D Δ : ℝ} {i j k : Fin 3}

-- 读法：`rate P d u i` 等于 `common (row P d u i j) (row P d u i k) (u i)`。
theorem rate_eq (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rate P d u i = common (row P d u i j) (row P d u i k) (u i) := by
  have he : (i + 1 = j ∧ i + 2 = k) ∨ (i + 1 = k ∧ i + 2 = j) := by omega
  unfold rate
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, common_comm]

-- 读法：`0` 严格小于 `rate P d u i`。
theorem Family.rate_pos (h : Family P d u D) (hu : Positive u) (i : Fin 3) :
    0 < rate P d u i :=
  common_pos (hu i) (h.curve i (i + 1) (i + 2) (by omega) (by omega) (by omega))
    (h.curve i (i + 2) (i + 1) (by omega) (by omega) (by omega))

-- 读法：存在 `k`，`i ≠ k` 与 `j ≠ k` 同时成立。按 `i + 1 = j` 成立与否分情况。
theorem other (_hij : i ≠ j) : ∃ k, i ≠ k ∧ j ≠ k := by
  by_cases he : i + 1 = j
  · exact ⟨i + 2, by omega, by omega⟩
  · exact ⟨i + 1, by omega, Ne.symm he⟩

-- 读法：`rate P d u i * (y - x)` 不超过 `row P d u i j y - row P d u i j x`。这里调用 `common_step`。
theorem Family.step (h : Family P d u D) (hu : Positive u) (hij : i ≠ j)
    {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) :
    rate P d u i * (y - x) ≤ row P d u i j y - row P d u i j x := by
  obtain ⟨k, hik, hjk⟩ := other hij
  rw [rate_eq hij hik hjk]
  exact common_step (hu i) (h.curve i j k hij hik hjk) (h.curve i k j hik hij hjk.symm) hx hy

-- 读法：`x + y` 不超过 `2 * (u * Real.log v)`。这里调用 `Real.add_one_le_exp`。
private theorem log_pair {x y u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : Real.exp (x / u) + Real.exp (y / u) ≤ 2 * v) : x + y ≤ 2 * (u * Real.log v) := by
  have he (z : ℝ) : z / u - Real.log v + 1 ≤ Real.exp (z / u) / v := by
    simpa [Real.exp_sub, Real.exp_log hv] using Real.add_one_le_exp (z / u - Real.log v)
  have hh := add_le_add (he x) (he y)
  rw [← add_div (Real.exp _)] at hh
  have hv' := (div_le_iff₀ hv).mpr h
  have he' : (x + y) / u ≤ 2 * Real.log v := by rw [add_div]; linarith only [hh, hv']
  linarith only [(div_le_iff₀ hu).mp he']

-- 读法：要证明的命题是 `Critical u (intercept P d u) d (fun i j => P i j (u i) (u j)) Δ`。这里调用 `log_pair`。
theorem Family.critical (h : Family P d u D) (hu : Positive u) (hd : Positive d)
    (hD : 0 ≤ D) (hs : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → u i + u j + u k = 2)
    (hg : ∀ i j, i ≠ j → D = d i * u j + d j * u i + Δ) :
    Critical u (intercept P d u) d (fun i j => P i j (u i) (u j)) Δ := by
  refine ⟨fun i j => h.symm _ _ _ _, ?_, ?_⟩
  · intro i j k hij hik hjk
    apply log_pair (hd i) (h.rate_pos hu i)
    have hb := common_bound (hu i) (h.curve i j k hij hik hjk) (h.curve i k j hik hij hjk.symm)
      (hu j) (hu k)
    rw [← rate_eq hij hik hjk, hs j k i hjk hij.symm hik.symm, mul_comm] at hb
    exact hb
  · intro i j hij
    have he (i j : Fin 3) :
        Real.exp ((intercept P d u i - P i j (u i) (u j)) / d i) =
          rate P d u i / Real.exp (P i j (u i) (u j) / d i) := by
      rw [intercept, sub_div, mul_div_cancel_left₀ _ (hd i).ne', Real.exp_sub,
        Real.exp_log (h.rate_pos hu i)]
    rw [he, he, h.symm j i, ← hg i j hij]
    apply pair_growth (P i j) (hu i) (hu j) (hd i) (hd j)
      (h.rate_pos hu i) (h.rate_pos hu j) hD
    · intro t ht
      have he := h.scale i j hij t (u i / t) (u j) (by linarith)
        (div_pos (hu i) (by linarith)) (hu j)
      rwa [mul_div_cancel₀ _ (by linarith : t ≠ 0)] at he
    · intro t ht
      exact h.step hu hij (hu j) ht
    · intro t ht ht'
      have hs := h.step hu hij.symm ht ht'
      simpa only [row, h.symm j i] using hs

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 双输入的全局包络与接触点附近的分区估计

**英文原文**

Global two-input envelope and a sector estimate near contact
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Minimum

variable {P : PairPrices} {d u : Vec} {D : ℝ} (h : Family P d u D)
  (hu : Positive u) (hd : Positive d) {i j k : Fin 3}

-- 读法：`ratio` 的取值由 `row P d u i j y / rate P d u i` 给出。
def ratio (P : PairPrices) (d u : Vec) (i j : Fin 3) (y : ℝ) : ℝ :=
  row P d u i j y / rate P d u i

-- 读法：`model` 的取值由 `intercept P d u i + (D - d i) * Real.log (x / u i) + d i * Real.log y` 给出。
def model (P : PairPrices) (d u : Vec) (D : ℝ) (i : Fin 3) (x y : ℝ) : ℝ :=
  intercept P d u i + (D - d i) * Real.log (x / u i) + d i * Real.log y

include h hu in
-- 读法：`0` 严格小于 `ratio P d u i j y`。使用 `div_pos` 给出的结论。
theorem Family.ratio_pos (i j) (y : ℝ) : 0 < ratio P d u i j y :=
  div_pos (Real.exp_pos _) (h.rate_pos hu i)

include h hu hd in
-- 读法：`ratio P d u i j y` 等于 `Real.exp ((P i j (u i) y - intercept P d u i) / d i)`。
theorem Family.ratio_eq (i j) (y : ℝ) :
    ratio P d u i j y = Real.exp ((P i j (u i) y - intercept P d u i) / d i) := by
  rw [intercept, sub_div, mul_div_cancel_left₀ _ (hd i).ne', Real.exp_sub,
    Real.exp_log (h.rate_pos hu i)]
  rfl

include h hu in
-- 读法：`y ≤ ratio P d u i j y` 与 `ratio P d u i j y ≤ y + u i` 同时成立。
theorem Family.ratio_bounds (hij : i ≠ j) {y : ℝ} (hy : 0 < y) :
    y ≤ ratio P d u i j y ∧ ratio P d u i j y ≤ y + u i := by
  obtain ⟨k, hik, hjk⟩ := other hij
  unfold ratio
  rw [le_div_iff₀ (h.rate_pos hu i), div_le_iff₀ (h.rate_pos hu i), rate_eq hij hik hjk]
  have h₁ := h.curve i j k hij hik hjk
  have h₂ := h.curve i k j hik hij hjk.symm
  exact ⟨by rw [mul_comm]; exact common_lower (hu i) h₁ h₂ hy,
    by rw [mul_comm]; exact common_upper (hu i) h₁ h₂ hy⟩

include h hu hd in
-- 读法：`P i j x y` 等于 `model P d u D i x ((x / u i) * ratio P d u i j (y / (x / u i)))`。
theorem Family.price_eq (hij : i ≠ j) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    P i j x y = model P d u D i x ((x / u i) * ratio P d u i j (y / (x / u i))) := by
  let t := x / u i
  have ht : 0 < t := div_pos hx (hu i)
  have he := h.scale i j hij t (u i) (y / t) ht (hu i) (div_pos hy ht)
  rw [show t * u i = x from div_mul_cancel₀ _ (hu i).ne', mul_div_cancel₀ _ ht.ne'] at he
  rw [he, model, Real.log_mul ht.ne' (h.ratio_pos hu i j _).ne',
    h.ratio_eq hu hd, Real.log_exp, mul_add, mul_div_cancel₀ _ (hd i).ne']
  unfold t
  ring

-- 读法：`model P d u D i x s` 不超过 `model P d u D i x t`。
private theorem model_mono (hp : 0 ≤ d i) {x s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    model P d u D i x s ≤ model P d u D i x t := by
  unfold model
  gcongr

include h hu hd in
-- 读法：`model P d u D i x y ≤ P i j x y` 与 `P i j x y ≤ model P d u D i x (y + x)` 同时成立。
theorem Family.envelope (hij : i ≠ j) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    model P d u D i x y ≤ P i j x y ∧ P i j x y ≤ model P d u D i x (y + x) := by
  rw [h.price_eq hu hd hij hx hy]
  let t := x / u i
  have ht : 0 < t := div_pos hx (hu i)
  obtain ⟨hl, hr⟩ := h.ratio_bounds hu hij (div_pos hy ht)
  have he : t * (y / t) = y := mul_div_cancel₀ _ ht.ne'
  have he' : t * u i = x := div_mul_cancel₀ _ (hu i).ne'
  have hlo := mul_le_mul_of_nonneg_left hl ht.le
  have hhi := mul_le_mul_of_nonneg_left hr ht.le
  rw [he] at hlo
  rw [mul_add, he, he'] at hhi
  exact ⟨model_mono (hd i).le hy hlo, model_mono (hd i).le (hy.trans_le hlo) hhi⟩

include h hu in
-- 读法：`ratio P d u i j x + ratio P d u i k y` 不超过 `x + y + u i`。这里调用 `common_bound`。
theorem Family.ratio_sum (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ratio P d u i j x + ratio P d u i k y ≤ x + y + u i := by
  unfold ratio
  rw [← add_div, div_le_iff₀ (h.rate_pos hu i), mul_comm, rate_eq hij hik hjk]
  exact common_bound (hu i) (h.curve i j k hij hik hjk) (h.curve i k j hik hij hjk.symm) hx hy

include h hu in
-- 读法：`y - x` 不超过 `ratio P d u i j y - ratio P d u i j x`。这里调用 `h.step`。
theorem Family.ratio_step (hij : i ≠ j) {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) :
    y - x ≤ ratio P d u i j y - ratio P d u i j x := by
  rw [ratio, ratio, ← sub_div, le_div_iff₀ (h.rate_pos hu i), mul_comm]
  exact h.step hu hij hx hy

include h hu hd in
-- 读法：`ratio P d u i j y ≤ y + 1 - u j + E / d i` 与 `(u j ≤ y → Real.exp (-E / d i) * (y + 1 - u j) ≤ ratio P d u i j y)` 同时成立。这里调用 `Real.exp_le_exp.mpr`。
/-- 用配对行在一个临界宽度处的超额值控制所有宽度的超额值。

英文原文：Control the excess at every width by its value in the companion
row at a single critical width.
-/
theorem Family.ratio_contact {E : ℝ} (hE : 0 ≤ E)
    (hs : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → u i + u j + u k = 2)
    (herr : ∀ i j, i ≠ j → -E ≤ P i j (u i) (u j) - intercept P d u i)
    (hij : i ≠ j) {y : ℝ} (hy : 0 < y) :
    ratio P d u i j y ≤ y + 1 - u j + E / d i ∧
      (u j ≤ y → Real.exp (-E / d i) * (y + 1 - u j) ≤ ratio P d u i j y) := by
  obtain ⟨k, hik, hjk⟩ := other hij
  have hlo {j : Fin 3} (hij : i ≠ j) : Real.exp (-E / d i) ≤ ratio P d u i j (u j) := by
    rw [h.ratio_eq hu hd]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (herr i j hij) (hd i).le)
  constructor
  · have he := (Real.add_one_le_exp (-E / d i)).trans (hlo hik)
    rw [neg_div] at he
    linarith only [he, hs i j k hij hik hjk, h.ratio_sum hu hij hik hjk hy (hu k)]
  · intro h'
    -- 推导：记下中间结论 `he`：`Real.exp (-E / d i) ≤ 1`。
    have he : Real.exp (-E / d i) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hE) (hd i).le)
    linarith only [hlo hij, h.ratio_step hu hij (hu j) h',
      mul_le_mul_of_nonneg_right he (sub_nonneg.mpr h')]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end
