-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Support
import OAI.LinearAlgebra.MatrixExponent.UpperBound
import Mathlib.Analysis.Convex.Continuous
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Scale
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Minimum.FaceZero
import Mathlib.Topology.Order.Monotone

section
/-!
# 由整数尺寸的矩形界导出对角不等式

经统一缩放再取极限，可将关于正整数权重的齐次二次不等式推广到正实数权重。

**英文原文**

The diagonal inequality from integer rectangular bounds

The homogeneous quadratic inequalities extend from positive integer
weights to positive real weights by a common rescaling and a limit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F : Type} [Field F] {x y z a b c : ℝ}

-- 读法：`4 * ((x + y) * a * b + (x + z) * a * c + (y + z) * b * c)` 不超过 `(a + b + c) ^ 2`。这里调用 `le_of_tendsto_of_tendsto`。
private theorem real_weights (h : DiscreteBound F) (hp : Prices F x y z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * ((x + y) * a * b + (x + z) * a * c + (y + z) * b * c) ≤ (a + b + c) ^ 2 := by
  have ha' := tendsto_nat_ceil_mul_div_atTop ha.le
  have hb' := tendsto_nat_ceil_mul_div_atTop hb.le
  have hc' := tendsto_nat_ceil_mul_div_atTop hc.le
  have h₁ := (ha'.const_mul (x + y)).mul hb'
  have h₂ := (ha'.const_mul (x + z)).mul hc'
  have h₃ := (hb'.const_mul (y + z)).mul hc'
  apply le_of_tendsto_of_tendsto (((h₁.add h₂).add h₃).const_mul 4) (((ha'.add hb').add hc').pow 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hd := h ⌈a * t⌉₊ ⌈b * t⌉₊ ⌈c * t⌉₊ (by positivity) (by positivity) (by positivity)
  have hl := ((support F).bound (by positivity) (by positivity) (by positivity) hp).trans hd
  unfold load at hl
  generalize ⌈a * t⌉₊ = A, ⌈b * t⌉₊ = B, ⌈c * t⌉₊ = C at hl ⊢
  field_simp
  linarith only [hl]

-- 读法：要证明的命题是 `DiagonalBound (Prices F)`。按 `x = 0 ∨ y = 0 ∨ z = 0` 成立与否分情况。
theorem diagonal_of_discrete (h : DiscreteBound F) : DiagonalBound (Prices F) := by
  intro x y z hp
  obtain ⟨hx, hy, hz⟩ := hp.nonneg
  by_cases hb : x = 0 ∨ y = 0 ∨ z = 0
  · obtain ⟨f, hf, hxy, hxz, hyz⟩ := hp
    rcases hb with rfl | rfl | rfl
    · simpa [dStar, hyz] using (dist_bounds hf 1 2).2
    · simpa [dStar, hxz] using (dist_bounds hf 0 2).2
    · simpa [dStar, hxy] using (dist_bounds hf 0 1).2
  push Not at hb
  have hx' := hx.lt_of_ne' hb.1
  have hy' := hy.lt_of_ne' hb.2.1
  have hz' := hz.lt_of_ne' hb.2.2
  have hd := real_weights h hp (by positivity : 0 < x * (y + z))
    (by positivity : 0 < y * (x + z)) (by positivity : 0 < z * (x + y))
  let p := x * y + y * z + z * x
  -- 推导：记下中间结论 `hpos`：`0 < p`。
  have hpos : 0 < p := by unfold p; positivity
  have he : (x + y) * (x + z) * (y + z) ≤ p := by
    apply le_of_mul_le_mul_right _ hpos
    unfold p
    linarith only [hd]
  unfold dStar
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hpos]
  unfold p at he
  linarith only [he]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# 方阵情形中唯一的接触价格

**英文原文**

The unique contact price at the square
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

-- 读法：`x = 3 / 8` 与 `y = 3 / 8 ∧ z = 3 / 8` 同时成立。
private theorem symmetric_maximizer {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : load 1 1 1 x y z = 9 / 4) (hD : dStar x y z ≤ 1) :
    x = 3 / 8 ∧ y = 3 / 8 ∧ z = 3 / 8 := by
  have hsum : x + y + z = 9 / 8 := by unfold load at h; linarith
  have hH : 1 / 8 ≤ x * y * z / (x * y + y * z + z * x) := by
    unfold dStar at hD
    linarith
  have hx' : 0 < x := hx.lt_of_ne (by rintro rfl; norm_num at hH)
  have hy' : 0 < y := hy.lt_of_ne (by rintro rfl; norm_num at hH)
  have hz' : 0 < z := hz.lt_of_ne (by rintro rfl; norm_num at hH)
  rw [le_div_iff₀ (by positivity)] at hH
  -- 推导：记下中间结论 `he`：`z * (x - y) ^ 2 + y * (x - z) ^ 2 + x * (y - z) ^ 2 ≤ 0`。
  have he : z * (x - y) ^ 2 + y * (x - z) ^ 2 + x * (y - z) ^ 2 ≤ 0 := by
    calc
      _ = (x + y + z) * (x * y + y * z + z * x) - 9 * x * y * z := by ring
      _ ≤ 0 := by rw [hsum]; linarith
  have h₁ : 0 ≤ z * (x - y) ^ 2 := by positivity
  have h₂ : 0 ≤ y * (x - z) ^ 2 := by positivity
  have h₃ : 0 ≤ x * (y - z) ^ 2 := by positivity
  have hxy : x = y :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp (le_antisymm (by linarith) h₁)).resolve_left hz'.ne'))
  have hxz : x = z :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp (le_antisymm (by linarith) h₂)).resolve_left hy'.ne'))
  exact ⟨by linarith, by linarith, by linarith⟩

-- 读法：要证明的命题是 `DiagonalBound (Prices F)`。使用 `diagonal_of_discrete` 给出的结论。
theorem diagonal (F : Type) [Field F] : DiagonalBound (Prices F) :=
  diagonal_of_discrete (discrete_bound F)

-- 读法：`MatrixExponent.omega F = 9 / 4` 与 `Prices F (3 / 8) (3 / 8) (3 / 8)` 等价。
theorem square_iff_contact (F : Type) [Field F] :
    MatrixExponent.omega F = 9 / 4 ↔ Prices F (3 / 8) (3 / 8) (3 / 8) := by
  have hD := diagonal F
  have h := support F
  rw [← square]
  constructor
  · intro hω
    obtain ⟨x, y, z, hp, he⟩ := h.attains zero_le_one zero_le_one zero_le_one
    obtain ⟨hx, hy, hz⟩ := hp.nonneg
    obtain ⟨rfl, rfl, rfl⟩ := symmetric_maximizer hx hy hz (he.trans hω) (hD _ _ _ hp)
    exact hp
  · intro hp
    have hl := h.bound zero_le_one zero_le_one zero_le_one hp
    have hu := upper_of_diagonal h hD zero_lt_one zero_lt_one zero_lt_one
    norm_num [U, benchmark] at hu
    norm_num [load] at hl
    exact le_antisymm hu hl

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# 齐次三脚架上的正谱接触

三条臂的长度决定三对端点间的连线距离。公共标签率是齐次的，在每条臂上都凸，且每单位距离的传输成本至多为一。在倒数坐标下，它超出调和基准的部分满足强极小值原理的正则性假设。

**英文原文**

Positive spectral contact on a homogeneous tripod

Lengths on the three arms determine three wire distances. The common-label
rate is homogeneous and convex along each arm, with transport cost at
most one per unit distance. In reciprocal coordinates its excess over
the harmonic benchmark satisfies the regularity hypotheses of the
strong minimum principle.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Minimum Set

-- 读法：结构的字段包括 `pos`、`prices`、`scale`、`convex`、`transport`。
/-- 传播所用的齐次谱三叉树上公共标签速率的各项性质。

英文原文：The properties of common-label rates on a homogeneous spectral tripod
used for propagation.
-/
structure Tripod (F : Type) [Field F] (D : Vec → ℝ) : Prop where
  pos : ∀ a, Positive a → 0 < D a
  prices : ∀ a, Positive a → Prices F (a 0 / D a) (a 1 / D a) (a 2 / D a)
  scale : ∀ a, Positive a → ∀ s : ℝ, 0 < s → D (s • a) = s * D a
  convex : ∀ a, Positive a → ∀ i, ConvexOn ℝ (Ioi 0) (fun t => D (Function.update a i t))
  transport : ∀ a, Positive a → ∀ i, MonotoneOn (fun t => D (Function.update a i t) + t) (Ioi 0)

-- 读法：`defect` 的取值由 `D v⁻¹ - ∑ i, (v i)⁻¹ + (∑ i, v i)⁻¹` 给出。
def defect (D : Vec → ℝ) (v : Vec) : ℝ :=
  D v⁻¹ - ∑ i, (v i)⁻¹ + (∑ i, v i)⁻¹

variable {F : Type} [Field F] {D : Vec → ℝ} {v a : Vec}

-- 读法：要证明的命题是 `Positive v⁻¹`。
private theorem inv_positive (hv : Positive v) : Positive v⁻¹ := fun i => inv_pos.mpr (hv i)

-- 读法：`0` 小于 `∑ i, v i`。使用 `Finset.sum_pos` 给出的结论。
private theorem total_pos (hv : Positive v) : 0 < ∑ i, v i :=
  Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty

-- 读法：`defect D a⁻¹` 等于 `D a - dStar (a 0) (a 1) (a 2)`。
theorem defect_inv (D : Vec → ℝ) (ha : Positive a) :
    defect D a⁻¹ = D a - dStar (a 0) (a 1) (a 2) := by
  have hx := ha 0
  have hy := ha 1
  have hz := ha 2
  simp only [defect, dStar, Fin.sum_univ_three, Pi.inv_apply, inv_inv]
  field_simp
  ring

-- 读法：`dStar (a 0) (a 1) (a 2)` 不超过 `D a`。
private theorem Tripod.lower (h : Tripod F D) (ha : Positive a) :
    dStar (a 0) (a 1) (a 2) ≤ D a := by
  have hD := h.pos _ ha
  have hx := ha 0
  have hy := ha 1
  have hz := ha 2
  have he : dStar (a 0 / D a) (a 1 / D a) (a 2 / D a) =
      dStar (a 0) (a 1) (a 2) / D a := by
    unfold dStar
    field_simp
  have hd := diagonal F _ _ _ (h.prices _ ha)
  rwa [he, div_le_one hD] at hd

-- 读法：`defect D (s • v)` 等于 `defect D v / s`。
private theorem Tripod.defect_scale (h : Tripod F D) (hv : Positive v) {s : ℝ} (hs : 0 < s) :
    defect D (s • v) = defect D v / s := by
  have he : (s • v)⁻¹ = s⁻¹ • v⁻¹ := by ext; simp [mul_comm]
  rw [defect, he, h.scale _ (inv_positive hv) _ (inv_pos.mpr hs), defect]
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

-- 读法：用函数外延性比较等号两侧在 `t` 处的取值。
theorem ray_defect (D : Vec → ℝ) (v : Vec) (i : Fin 3) :
    ray (defect D) v i = fun t =>
      D (Function.update v⁻¹ i (1 / (v i + t))) - 1 / (v i + t) + 1 / ((∑ j, v j) + t) -
        ∑ j ∈ Finset.univ.erase i, (v j)⁻¹ := by
  funext t
  have he : (move v i t)⁻¹ = Function.update v⁻¹ i (1 / (v i + t)) := by
    ext j
    by_cases h : j = i <;> simp [move, h]
  have hs (f : ℝ → ℝ) : ∑ j, f (move v i t j) = f (v i + t) + ∑ j ∈ Finset.univ.erase i, f (v j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [move, Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  -- 推导：记下中间结论 `ht`：`(∑ j, move v i t j) = (∑ j, v j) + t`。
  have ht : (∑ j, move v i t j) = (∑ j, v j) + t := by
    have := hs (fun x => x)
    rw [← Finset.add_sum_erase _ v (Finset.mem_univ i)]
    linarith
  rw [ray, defect, he, ht, hs (fun x => x⁻¹)]
  ring

-- 读法：要证明的命题是 `Regular (defect D)`。这里调用 `sub_nonneg.mpr`。
theorem Tripod.regular (h : Tripod F D) : Regular (defect D) := by
  refine ⟨?_, fun v hv s hs => h.defect_scale hv hs, ?_, ?_⟩
  · intro v hv
    have hi := inv_positive hv
    have he := defect_inv D hi
    rw [inv_inv] at he
    rw [he]
    exact sub_nonneg.mpr (h.lower hi)
  · intro v hv i
    rw [ray_defect]
    have hf := (h.convex _ (inv_positive hv) i).continuousOn isOpen_Ioi
    have hinv {a : ℝ} (ha : 0 < a) : ContinuousOn (fun t : ℝ => 1 / (a + t)) (Ici 0) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id)
        (fun _ ht => (add_pos_of_pos_of_nonneg ha ht).ne')
    exact (((hf.comp (hinv (hv i)) (fun t ht => one_div_pos.mpr
      (add_pos_of_pos_of_nonneg (hv i) ht))).sub (hinv (hv i))).add
        (hinv (total_pos hv))).sub continuousOn_const
  · intro v hv
    let C := ∑ i, 2 / (v i) ^ 3
    have hn (i) : 0 ≤ 2 / (v i) ^ 3 := div_nonneg (by norm_num) (pow_nonneg (hv i).le _)
    refine ⟨C, Finset.sum_nonneg fun i _ => hn i, ?_⟩
    intro w hw i
    have hw' : Positive w := fun j => (hv j).trans_le (hw.1 j)
    -- 推导：记下中间结论 `hC`：`2 / (w i) ^ 3 ≤ C`。
    have hC : 2 / (w i) ^ 3 ≤ C := calc
      _ ≤ 2 / (v i) ^ 3 := by have := hv i; gcongr; exact hw.1 i
      _ ≤ _ := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    rw [ray_defect]
    exact reciprocal_semiconvex (h.convex _ (inv_positive hw') i)
      (h.transport _ (inv_positive hw') i) (hw' i) (total_pos hw') hC

-- 读法：要证明的命题是 `Prices F (x / dStar x y z) (y / dStar x y z) (z / dStar x y z)`。
/-- 在一个接触点处没有缺陷。由此，方向比较迫使整个正极性边界包含在谱中。

英文原文：At one contact there is no defect. The directional comparison then
forces the full positive polar boundary into the spectrum.
-/
theorem Tripod.boundary (h : Tripod F D) (hc : Comparison (defect D))
    (ha : Positive a) (he : D a = dStar (a 0) (a 1) (a 2)) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Prices F (x / dStar x y z) (y / dStar x y z) (z / dStar x y z) := by
  let b : Vec := ![x, y, z]
  have hb : Positive b := by intro i; fin_cases i <;> assumption
  have hh := vanishes h.regular hc (inv_positive ha) (by rw [defect_inv D ha, he, sub_self])
    (inv_positive hb)
  rw [defect_inv D hb, sub_eq_zero] at hh
  have hp := h.prices _ hb
  rw [hh] at hp
  exact hp

-- 读法：要证明的命题是 `Propagation (Prices F)`。这里调用 `hD.boundary`。
/-- 只需在方向恒等式局部成立的一棵三叉树上实现初始接触。

英文原文：It is enough to realize the initial contact in one tripod where
the directional identity holds locally.
-/
theorem propagation_of_tripod
    (h : ∀ x y z, 0 < x → 0 < y → 0 < z → Prices F x y z → dStar x y z = 1 →
      ∃ D, Tripod F D ∧ D ![x, y, z] = 1 ∧ Comparison (defect D)) :
    Propagation (Prices F) := by
  rintro ⟨x, y, z, hx, hy, hz, hp, he⟩
  obtain ⟨D, hD, h₁, h₂⟩ := h x y z hx hy hz hp he
  have ha : Positive ![x, y, z] := by intro i; fin_cases i <;> assumption
  exact hD.boundary h₂ ha (h₁.trans he.symm)

-- 读法：要证明的命题是 `Propagation (Prices F)`。这里调用 `propagation_of_tripod`。
theorem propagation_of_potential
    (h : ∀ x y z, 0 < x → 0 < y → 0 < z → Prices F x y z → dStar x y z = 1 →
      ∃ D, Tripod F D ∧ D ![x, y, z] = 1 ∧ HasPotential (defect D)) :
    Propagation (Prices F) := by
  apply propagation_of_tripod
  intro x y z hx hy hz hp he
  obtain ⟨D, hD, h₁, h₂⟩ := h x y z hx hy hz hp he
  exact ⟨D, hD, h₁, comparison_of_potential hD.regular h₂⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# 由尖锐的对偶阈值得到无穷远处的接触

将两条短臂的长度和归一化为二。在略高于二分之一的内侧指数处检验谱公式，可迫使两条短臂趋于一、长臂趋于无穷，并使对角缺陷的绝对量趋于零。

**英文原文**

Contact at infinity from a sharp dual threshold

Normalize the sum of the two short arms to two. Testing the spectral
formula just above inner exponent one half forces these arms to converge
to one, the long arm to escape, and the *absolute* diagonal defect to vanish.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

-- 读法：`Escapes` 的结果类型为 `Prop`。
/-- 当一条臂趋于无穷时在极限中出现的接触。

英文原文：Contact in the limit as one arm escapes to infinity.
-/
def Escapes (F : Type) [Field F] : Prop :=
  ∀ ε M : ℝ, 0 < ε → 0 ≤ M → ∃ x y z D : ℝ,
    M < x ∧ 0 < y ∧ 0 < z ∧ 0 < D ∧ y + z = 2 ∧
    |y - 1| < ε ∧ |z - 1| < ε ∧ 0 ≤ D - dStar x y z ∧ D - dStar x y z < ε ∧
    Prices F (x / D) (y / D) (z / D)

variable {F : Type} [Field F] {x y z d : ℝ}

-- 读法：`2` 严格小于 `exponent F 1 1 (1 / 2 + d)`。
private theorem exceed (hd : dual F 1 1 ≤ 1 / 2) (h : 0 < d) (h' : d ≤ 1 / 2) :
    2 < exponent F 1 1 (1 / 2 + d) := by
  have hl := (bounds F zero_le_one zero_le_one (by linarith : 0 ≤ 1 / 2 + d)).1
  by_contra! hu
  have he : exponent F 1 1 (1 / 2 + d) = 1 + 1 := by
    rw [max_le_iff] at hl
    linarith [hl.1]
  have hh : 1 / 2 + d ≤ dual F 1 1 :=
    le_csSup ⟨_, fun _ hx => hx.1.2⟩ ⟨⟨by linarith, by simp; linarith⟩, he⟩
  linarith

-- 读法：`0 < x` 与 `0 < y ∧ 0 < z` 同时成立。
private theorem positive_arms (hp : Prices F x y z) (h : d ≤ 1 / 2)
    (hl : 2 < load 1 1 (1 / 2 + d) x y z) : 0 < x ∧ 0 < y ∧ 0 < z := by
  obtain ⟨hx, hy, hz⟩ := hp.nonneg
  have hs : 1 < x + y + z := by
    unfold load at hl
    linarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - d) (add_nonneg hy hz)]
  have hh := diagonal F _ _ _ hp
  refine ⟨hx.lt_of_ne ?_, hy.lt_of_ne ?_, hz.lt_of_ne ?_⟩ <;>
    rintro rfl <;> simp [dStar] at hh <;> linarith

-- 读法：结论为 `let g := y * z / 2 g ^ 2 / (x + g) + (y - 1) ^ 2 / 2 = dStar x y z - x - 3 / 2`。
/-- 配平方后可将损失分解为三个非负项。

英文原文：Completing the square separates three nonnegative losses.
-/
private theorem losses (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (he : y + z = 2) :
    let g := y * z / 2
    g ^ 2 / (x + g) + (y - 1) ^ 2 / 2 = dStar x y z - x - 3 / 2 := by
  dsimp only
  unfold dStar
  field_simp
  rw [show z = 2 - y by linarith]
  ring

-- 读法：结论为 `∃ x y z D : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < D ∧ y + z = 2 ∧ Prices F (x / D) (y / D) (z / D) ∧ 0 ≤ D - dStar x y z ∧ D - dStar x y z + ((y * z / 2) ^ 2 / (x + y * z / 2) + (y - 1) ^ 2 / 2) < d`。
private theorem near_contact (hd : dual F 1 1 ≤ 1 / 2) (h : 0 < d) (h' : d ≤ 1 / 2) :
    ∃ x y z D : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < D ∧ y + z = 2 ∧
      Prices F (x / D) (y / D) (z / D) ∧ 0 ≤ D - dStar x y z ∧
      D - dStar x y z + ((y * z / 2) ^ 2 / (x + y * z / 2) + (y - 1) ^ 2 / 2) < d := by
  obtain ⟨a, b, c, hp, he⟩ := (support F).attains zero_le_one zero_le_one
    (by linarith : 0 ≤ 1 / 2 + d)
  have hl := (exceed hd h h').trans_eq he.symm
  obtain ⟨ha, hb, hc⟩ := positive_arms hp h' hl
  let D := 2 / (b + c)
  have hD : 0 < D := by unfold D; positivity
  let x := a * D
  let y := b * D
  let z := c * D
  -- 推导：记下中间结论 `hx`：`0 < x`。
  have hx : 0 < x := mul_pos ha hD
  have hy : 0 < y := mul_pos hb hD
  have hz : 0 < z := mul_pos hc hD
  have hsum : y + z = 2 := by unfold y z D; field_simp
  have hs : dStar x y z = dStar a b c * D := by
    unfold x y z dStar
    field_simp
  have h' := mul_le_mul_of_nonneg_right (diagonal F _ _ _ hp) hD.le
  refine ⟨x, y, z, D, hx, hy, hz, hD, hsum, ?_, by rw [hs]; linarith, ?_⟩
  · simpa only [x, y, z, mul_div_cancel_right₀ _ hD.ne'] using hp
  rw [losses hx hy hz hsum]
  -- 推导：记下中间结论 `he'`：`load 1 1 (1 / 2 + d) a b c * D = 2 * x + (3 / 2 + d) * (y + z)`。
  have he' : load 1 1 (1 / 2 + d) a b c * D = 2 * x + (3 / 2 + d) * (y + z) := by
    unfold load x y z
    ring
  have hh := mul_lt_mul_of_pos_right hl hD
  rw [he', hsum] at hh
  linarith

-- 读法：要证明的命题是 `Escapes F`。
theorem escapes_of_dual (hd : dual F 1 1 ≤ 1 / 2) : Escapes F := by
  intro ε M hε hM
  let d := min (min ε (ε ^ 2 / 2)) (min (1 / 16) (1 / (16 * (M + 1))))
  have hd' : 0 < d := by unfold d; positivity
  have hd₁ : d ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hd₂ : d ≤ ε ^ 2 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hd₃ : d ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hd₄ : d ≤ 1 / (16 * (M + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨x, y, z, D, hx, hy, hz, hD, hs, hp, hl, hu⟩ := near_contact hd hd' (by linarith)
  let g := y * z / 2
  -- 推导：记下中间结论 `hg`：`0 < g`。
  have hg : 0 < g := by unfold g; positivity
  change D - dStar x y z + (g ^ 2 / (x + g) + (y - 1) ^ 2 / 2) < d at hu
  have h₁ : 0 ≤ g ^ 2 / (x + g) := by positivity
  have h₂ : 0 ≤ (y - 1) ^ 2 / 2 := by positivity
  have hsmall : (y - 1) ^ 2 < ε ^ 2 := by linarith
  have hy' : |y - 1| < ε := by
    rw [abs_lt]
    constructor <;> nlinarith only [hsmall, hε]
  have hz' : |z - 1| < ε := by rwa [show z - 1 = -(y - 1) by linarith, abs_neg]
  refine ⟨x, y, z, D, ?_, hy, hz, hD, hs, hy', hz', hl, by linarith, hp⟩
  -- 推导：记下中间结论 `he`：`g = (1 - (y - 1) ^ 2) / 2`。
  have he : g = (1 - (y - 1) ^ 2) / 2 := by unfold g; rw [show z = 2 - y by linarith]; ring
  have hgle : g ≤ 1 := by linarith
  have hgge : 1 / 4 ≤ g := by linarith
  have h₃ : g ^ 2 < d * (x + g) := (div_lt_iff₀ (by positivity)).mp (by linarith)
  have h₄ := (le_div_iff₀ (by positivity : 0 < 16 * (M + 1))).mp hd₄
  by_contra! hh
  nlinarith only [h₃, h₄, hgge, mul_le_mul_of_nonneg_left (add_le_add hh hgle) hd'.le]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# 逼近倒数坐标中的一个面

星形上界以及沿一条无界臂的凸性说明，对角速率减去臂长沿这条臂单调不增。在倒数坐标下，这给出开面上的极限。

**英文原文**

Approaching a reciprocal face

The star bound and convexity along an unbounded arm make the
diagonal rate minus the length nonincreasing along that arm.
In reciprocal coordinates this gives a limit at the open face.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Minimum Set Filter
open scoped Topology

-- 读法：结构的字段包括 `star`。
/-- 一棵三叉树，其公共标签速率满足星形生成树界。

英文原文：A tripod whose common-label rate satisfies the star spanning-tree bound.
-/
structure StarTripod (F : Type) [Field F] (D : Vec → ℝ) : Prop extends Tripod F D where
  star : ∀ a, Positive a → D a ≤ ∑ i, a i

variable {F : Type} [Field F] {D : Vec → ℝ} {v : Vec}

-- 读法：要证明的命题是 `AntitoneOn (fun x => f x - x) (Ioi 0)`。
private theorem growth_linear {f : ℝ → ℝ} (h : ConvexOn ℝ (Ioi 0) f)
    {L : ℝ} (hL : ∀ x, 0 < x → f x ≤ x + L) : AntitoneOn (fun x => f x - x) (Ioi 0) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · rfl
  by_contra! hbad
  let c := (f b - f a) / (b - a)
  have hc : 1 < c := (lt_div_iff₀ (sub_pos.mpr hab)).2 (by linarith)
  obtain ⟨t, ht⟩ := exists_gt (max b ((c * b + L - f b) / (c - 1)))
  obtain ⟨ht₁, ht₂⟩ := max_lt_iff.mp ht
  have ht : 0 < t := hb.trans ht₁
  have ht' := h.slope_mono_adjacent ha ht hab ht₁
  change c ≤ (f t - f b) / (t - b) at ht'
  rw [le_div_iff₀ (sub_pos.mpr ht₁)] at ht'
  rw [div_lt_iff₀ (sub_pos.mpr hc)] at ht₂
  linarith only [ht', ht₂, hL t ht]

-- 读法：要证明的命题是 `AntitoneOn (fun t => D (Function.update v i t) - t) (Ioi 0)`。这里调用 `growth_linear`。
theorem StarTripod.anti (h : StarTripod F D) (hv : Positive v) (i : Fin 3) :
    AntitoneOn (fun t => D (Function.update v i t) - t) (Ioi 0) := by
  apply growth_linear (h.convex _ hv i) (L := ∑ j ∈ Finset.univ \ {i}, v j)
  intro x hx
  have hp : Positive (Function.update v i x) := by
    intro j
    by_cases he : j = i
    · simpa [he] using hx
    · simpa [he] using hv j
  have ht := h.star _ hp
  rwa [Finset.sum_update_of_mem (Finset.mem_univ i)] at ht

-- 读法：`defect D v` 不超过 `(∑ i, v i)⁻¹`。
theorem StarTripod.cap (h : StarTripod F D) (hv : Positive v) :
    defect D v ≤ (∑ i, v i)⁻¹ := by
  have he := h.star v⁻¹ (fun i => inv_pos.mpr (hv i))
  unfold defect
  simp only [Pi.inv_apply] at he
  linarith

namespace Face

-- 读法：要证明的命题是 `Positive ![x, y, z]`。
theorem positive {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : Positive ![x, y, z] := by
  intro i; fin_cases i <;> assumption

-- 读法：`(![x, y, z] : Vec)⁻¹` 等于 `Function.update ![1, y⁻¹, z⁻¹] 0 x⁻¹`。
private theorem update_inv (x y z : ℝ) :
    (![x, y, z] : Vec)⁻¹ = Function.update ![1, y⁻¹, z⁻¹] 0 x⁻¹ := by
  ext i; fin_cases i <;> simp

variable (h : StarTripod F D) {x y z : ℝ}
include h

-- 读法：要证明的命题是 `MonotoneOn (fun x => defect D ![x, y, z] - (x + y + z)⁻¹) (Ioi 0)`。
theorem monotone (hy : 0 < y) (hz : 0 < z) :
    MonotoneOn (fun x => defect D ![x, y, z] - (x + y + z)⁻¹) (Ioi 0) := by
  intro a ha b hb hab
  have he := h.anti (positive zero_lt_one (inv_pos.mpr hy) (inv_pos.mpr hz)) 0
    (show 0 < b⁻¹ from inv_pos.mpr hb) (show 0 < a⁻¹ from inv_pos.mpr ha) (inv_anti₀ ha hab)
  change D _ - _ ≤ D _ - _ at he
  simp only [defect, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, update_inv]
  linarith

-- 读法：`limit` 的取值由 `limUnder (𝓝[>] 0) fun x => defect D ![x, y, z]` 给出。
def limit (D : Vec → ℝ) (y z : ℝ) : ℝ :=
  limUnder (𝓝[>] 0) fun x => defect D ![x, y, z]

-- 读法：`(fun x => defect D ![x, y, z])` 沿滤子 `(𝓝[>] 0)` 收敛到 `(limit D y z)`。
theorem tends (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun x => defect D ![x, y, z]) (𝓝[>] 0) (𝓝 (limit D y z)) := by
  let f x := defect D ![x, y, z] - (x + y + z)⁻¹
  have hb : BddBelow (f '' Ioi 0) := by
    refine ⟨-(y + z)⁻¹, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hd := h.toTripod.regular.nonneg _ (positive hx hy hz)
    have hi : (x + y + z)⁻¹ ≤ (y + z)⁻¹ := inv_anti₀ (by positivity) (by linarith [show 0 < x from hx])
    unfold f; linarith
  have ht := (monotone h hy hz).tendsto_nhdsGT hb
  have hi : ContinuousAt (fun x : ℝ => (x + y + z)⁻¹) 0 := by fun_prop (disch := positivity)
  apply tendsto_nhds_limUnder
  refine ⟨sInf (f '' Ioi 0) + (0 + y + z)⁻¹, ?_⟩
  simpa only [sub_add_cancel] using ht.add hi.continuousWithinAt

end Face
end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# 沿倒数坐标面的切向一致估计

**英文原文**

Uniform estimates tangential to a reciprocal face
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Minimum Set

variable {F : Type} [Field F] {D : Vec → ℝ} {v : Vec}

-- 读法：`0 ≤ 1 / (a + s) - 1 / (a + t)` 与 `1 / (a + s) - 1 / (a + t) ≤ (t - s) / a ^ 2` 同时成立。
private theorem inv_step {a s t : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (ht : s ≤ t) :
    0 ≤ 1 / (a + s) - 1 / (a + t) ∧ 1 / (a + s) - 1 / (a + t) ≤ (t - s) / a ^ 2 := by
  have h₁ : 0 < a + s := by linarith
  have h₂ : 0 < a + t := by linarith
  rw [show 1 / (a + s) - 1 / (a + t) = (t - s) / ((a + s) * (a + t)) by field_simp; ring]
  have h : a ^ 2 ≤ (a + s) * (a + t) := by rw [pow_two]; gcongr <;> linarith
  exact ⟨div_nonneg (sub_nonneg.mpr ht) (by positivity),
    div_le_div_of_nonneg_left (sub_nonneg.mpr ht) (by positivity) h⟩

-- 读法：`ray (defect D) v i s - ray (defect D) v i t ≤ (t - s) / (∑ j, v j) ^ 2` 与 `ray (defect D) v i t - ray (defect D) v i s ≤ 2 * ((t - s) / (v i) ^ 2)` 同时成立。
theorem StarTripod.step (h : StarTripod F D) (hv : Positive v) (i : Fin 3)
    {s t : ℝ} (hs : 0 ≤ s) (ht : s ≤ t) :
    ray (defect D) v i s - ray (defect D) v i t ≤ (t - s) / (∑ j, v j) ^ 2 ∧
    ray (defect D) v i t - ray (defect D) v i s ≤ 2 * ((t - s) / (v i) ^ 2) := by
  have h₁ : 0 < v i := hv i
  have h₂ : 0 < ∑ j, v j := Finset.sum_pos (fun j _ => hv j) Finset.univ_nonempty
  have hi : Positive v⁻¹ := fun j => inv_pos.mpr (hv j)
  have ht' := hs.trans ht
  have hs₀ : 1 / (v i + s) ∈ Ioi (0 : ℝ) := by apply mem_Ioi.mpr; positivity
  have ht₀ : 1 / (v i + t) ∈ Ioi (0 : ℝ) := by apply mem_Ioi.mpr; positivity
  obtain ⟨hi₁, hi₂⟩ := inv_step h₁ hs ht
  obtain ⟨hv₁, hv₂⟩ := inv_step h₂ hs ht
  have hinc := h.transport _ hi i ht₀ hs₀ (sub_nonneg.mp hi₁)
  have hdec := h.anti hi i ht₀ hs₀ (sub_nonneg.mp hi₁)
  rw [ray_defect]
  dsimp only at hinc hdec ⊢
  constructor <;> linarith

-- 读法：证明中先建立 `hi`，即 `v i ≤ ∑ j, v j`。
theorem StarTripod.ray_bound (h : StarTripod F D) (hv : Positive v) (i : Fin 3)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |ray (defect D) v i t - ray (defect D) v i s| ≤ (2 / (v i) ^ 2) * |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm, abs_sub_comm t]
    exact this ht hs (le_of_not_ge hst)
  have hi : v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ => (hv j).le) (Finset.mem_univ i)
  obtain ⟨h₁, h₂⟩ := h.step hv i hs hst
  have hp := hv i
  have he : (t - s) / (∑ j, v j) ^ 2 ≤ (t - s) / (v i) ^ 2 := by gcongr
  have he' : 0 ≤ (t - s) / (v i) ^ 2 := by positivity
  rw [abs_of_nonneg (sub_nonneg.mpr hst), abs_sub_le_iff]
  simp only [div_eq_mul_inv] at he he' h₁ h₂ ⊢
  constructor <;> linarith

-- 读法：`ray (defect D) v i t` 不超过 `1 / t`。这里调用 `inv_anti₀`。
theorem StarTripod.tail (h : StarTripod F D) (hv : Positive v) (i : Fin 3)
    {t : ℝ} (ht : 0 < t) : ray (defect D) v i t ≤ 1 / t := by
  have hp := hv.move i ht.le
  refine (h.cap hp).trans ?_
  rw [one_div]
  apply inv_anti₀ ht
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ i))
  simp [move, (hv i).le]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# 用三坐标缺损刻画正坐标面

将一个切向坐标分为两个地位相同的坐标，便可直接沿用内部的强极小值原理。

**英文原文**

The positive face as a three-coordinate defect

Splitting one tangential coordinate into two equal-role coordinates
allows the interior strong minimum principle to be used unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Face
open Minimum Set Filter
open scoped Topology

-- 读法：`atDepth` 的取值由 `![t, v 0, v 1 + v 2]` 给出。
def atDepth (t : ℝ) (v : Vec) : Vec := ![t, v 0, v 1 + v 2]

-- 读法：`lifted` 的取值由 `limit D (v 0) (v 1 + v 2)` 给出。
def lifted (D : Vec → ℝ) (v : Vec) : ℝ := limit D (v 0) (v 1 + v 2)

-- 读法：当 `i = 0` 成立时取 `1`，否则取 `2`。
def tangent (i : Fin 3) : Fin 3 := if i = 0 then 1 else 2

variable {v w : Vec} {t : ℝ}

-- 读法：要证明的命题是 `Positive (atDepth t v)`。
theorem depth_positive (hv : Positive v) (ht : 0 < t) : Positive (atDepth t v) :=
  positive ht (hv 0) (add_pos (hv 1) (hv 2))

-- 读法：`v i` 不超过 `atDepth t v (tangent i)`。使用 `fin_cases` 给出的结论。
theorem tangent_le (hv : Positive v) (t : ℝ) (i : Fin 3) : v i ≤ atDepth t v (tangent i) := by
  fin_cases i <;> simp [tangent, atDepth, (hv 1).le, (hv 2).le]

-- 读法：`move (atDepth r v) (tangent i) t` 等于 `atDepth r (move v i t)`。
theorem along (r : ℝ) (v : Vec) (i : Fin 3) (t : ℝ) :
    move (atDepth r v) (tangent i) t = atDepth r (move v i t) := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [atDepth, move, tangent, add_comm, add_left_comm, add_assoc]

variable {F : Type} [Field F] {D : Vec → ℝ} (h : StarTripod F D)
include h

-- 读法：`(fun r => defect D (atDepth r v))` 沿滤子 `(𝓝[>] 0)` 收敛到 `(lifted D v)`。
theorem lifted_limit (hv : Positive v) :
    Tendsto (fun r => defect D (atDepth r v)) (𝓝[>] 0) (𝓝 (lifted D v)) :=
  tends h (hv 0) (add_pos (hv 1) (hv 2))

-- 读法：`(fun r => ray (defect D) (atDepth r v) (tangent i) t)` 沿滤子 `(𝓝[>] 0)` 收敛到 `(ray (lifted D) v i t)`。这里调用 `lifted_limit`。
theorem ray_limit (hv : Positive v) (i : Fin 3) (ht : 0 ≤ t) :
    Tendsto (fun r => ray (defect D) (atDepth r v) (tangent i) t) (𝓝[>] 0)
      (𝓝 (ray (lifted D) v i t)) := by
  simpa only [ray, along] using lifted_limit h (hv.move i ht)

-- 读法：`lifted D (s • v)` 等于 `lifted D v / s`。这里调用 `tendsto_id.mono_left`。
private theorem lifted_scale (hv : Positive v) {s : ℝ} (hs : 0 < s) :
    lifted D (s • v) = lifted D v / s := by
  have hv' : Positive (s • v) := fun i => mul_pos hs (hv i)
  have he (r : ℝ) : atDepth (s * r) (s • v) = s • atDepth r v := by
    ext i; fin_cases i <;> simp [atDepth, mul_add]
  have ht : Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0)).const_mul s
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hs hr
  refine tendsto_nhds_unique ((lifted_limit h hv').comp ht) ?_
  refine ((lifted_limit h hv).div_const s).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Function.comp_apply, he, h.toTripod.regular.homogeneous _ (depth_positive hv hr) _ hs]

-- 读法：这里调用 `h.ray_bound`。
theorem ray_bound (hv : Positive v) (i : Fin 3) {r s t : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |ray (defect D) (atDepth r v) (tangent i) t - ray (defect D) (atDepth r v) (tangent i) s| ≤
      2 / (v i) ^ 2 * |t - s| := by
  apply (h.ray_bound (depth_positive hv hr) (tangent i) hs ht).trans
  have hp := hv i
  gcongr
  exact tangent_le hv r i

-- 读法：要证明的命题是 `ContinuousOn (ray (lifted D) v i) (Ici 0)`。这里调用 `LipschitzOnWith.continuousOn`。
private theorem ray_continuous (hv : Positive v) (i : Fin 3) :
    ContinuousOn (ray (lifted D) v i) (Ici 0) := by
  let C : NNReal := ⟨2 / (v i) ^ 2, by positivity⟩
  apply LipschitzOnWith.continuousOn (K := C)
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  simp only [Real.dist_eq]
  apply le_of_tendsto ((ray_limit h hv i ht).sub (ray_limit h hv i hs)).abs
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact ray_bound h hv i hr hs ht

-- 读法：要证明的命题是 `Semiconvex (ray (lifted D) v i) C`。这里调用 `reciprocal_semiconvex`。
private theorem ray_convex (hv : Positive v) (i : Fin 3) {C : ℝ} (hC : 2 / (v i) ^ 3 ≤ C) :
    Semiconvex (ray (lifted D) v i) C := by
  have hc (r : ℝ) (hr : 0 < r) : Semiconvex (ray (defect D) (atDepth r v) (tangent i)) C := by
    have hp := depth_positive hv hr
    have hi : Positive (atDepth r v)⁻¹ := fun j => inv_pos.mpr (hp j)
    have hsum : 0 < ∑ j, atDepth r v j := Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
    rw [ray_defect]
    apply reciprocal_semiconvex (h.convex _ hi (tangent i))
      (h.transport _ hi (tangent i)) (hp _) hsum
    apply le_trans _ hC
    have he := hv i
    gcongr
    exact tangent_le hv r i
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hf (t) (ht : 0 ≤ t) := (ray_limit h hv i ht).add_const (C * t ^ 2)
  apply le_of_tendsto_of_tendsto (hf _ (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)))
    (((hf x hx).const_mul a).add ((hf y hy).const_mul b))
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hc r hr).2 hx hy ha hb hab

-- 读法：要证明的命题是 `Regular (lifted D)`。这里调用 `ge_of_tendsto`。
theorem regular : Regular (lifted D) := by
  refine ⟨?_, fun _ hv _ hs => lifted_scale h hv hs, fun _ hv => ray_continuous h hv, ?_⟩
  · intro v hv
    apply ge_of_tendsto (lifted_limit h hv)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h.toTripod.regular.nonneg _ (depth_positive hv hr)
  · intro v hv
    let C := ∑ i, 2 / (v i) ^ 3
    have hp i : 0 ≤ 2 / (v i) ^ 3 := div_nonneg (by norm_num) (pow_nonneg (hv i).le _)
    refine ⟨C, Finset.sum_nonneg (fun i _ => hp i), ?_⟩
    intro w hw i
    apply ray_convex h (fun j => (hv j).trans_le (hw.1 j)) i
    apply le_trans _ (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i))
    have h' := hv i
    gcongr
    exact hw.1 i

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Face
end

section
/-!
# 把定向积分比较传到一个面上

**英文原文**

Passing the directional integral comparison to a face
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Face
open Minimum Set Filter
open scoped Topology

-- 读法：`Uniform` 的结果类型为 `Prop`。
/-- 当第一条臂长度的倒数趋于零，而另外两个倒数在正数构成的紧矩形内变化时，该常数保持有界。

英文原文：The constant stays bounded as the first reciprocal length tends to
zero while the other two range over a compact positive box.
-/
def Uniform (D : Vec → ℝ) : Prop :=
  ∀ v, Positive v → ∃ E : ℝ, 0 ≤ E ∧ ∀ w, Positive w → w ≤ (2 : ℝ) • v →
    v 1 ≤ w 1 → v 2 ≤ w 2 → ∀ i j, ∀ ζ : ℝ, 0 < ζ →
    ∀ᶠ T : ℝ in atTop, J D w i T - J D w j T ≤ E * D w + ζ

variable {F : Type} [Field F] {D : Vec → ℝ}

-- 读法：要证明的命题是 `Comparison D`。
theorem Uniform.interior (h : Uniform D) : Comparison D := by
  intro v hv
  obtain ⟨E, hE, hc⟩ := h v hv
  exact ⟨E, hE, fun w hw => hc w (fun i => (hv i).trans_le (hw.1 i)) hw.2 (hw.1 1) (hw.1 2)⟩

-- 读法：要证明的命题是 `Comparison (lifted D)`。
theorem comparison (h : StarTripod F D) (hc : Uniform (defect D)) :
    Comparison (lifted D) := by
  intro v hv
  obtain ⟨E, hE, he⟩ := hc (atDepth 1 v) (depth_positive hv zero_lt_one)
  refine ⟨E, hE, ?_⟩
  intro w hw i j ζ hζ
  have hw' : Positive w := fun i => (hv i).trans_le (hw.1 i)
  let f (i : Fin 3) (r : ℝ) := ray (defect D) (atDepth r w) (tangent i)
  have hp r (hr : r ∈ Ioc (0 : ℝ) 1) := depth_positive hw' hr.1
  let C := 2 / (w i) ^ 2 + 2 / (w j) ^ 2
  -- 推导：记下中间结论 `hC`：`0 ≤ C`。
  have hC : 0 ≤ C := by unfold C; positivity
  have hnear (r) (hr : r ∈ Ioc (0 : ℝ) 1) (t : ℝ) (ht : 0 < t) :
      -(C * t) ≤ f i r t - f j r t := by
    have h₁ := ray_bound h hw' i hr.1 le_rfl ht.le
    have h₂ := ray_bound h hw' j hr.1 le_rfl ht.le
    simp only [sub_zero, abs_of_pos ht, ray_zero, abs_le] at h₁ h₂
    unfold C f
    linarith only [h₁.1, h₂.2]
  have hr := h.toTripod.regular
  have hcon i r (hp : Positive (atDepth r w)) := hr.continuous _ hp (tangent i)
  have hnon i r (hp : Positive (atDepth r w)) t (ht : 0 ≤ t) : 0 ≤ f i r t :=
    hr.nonneg _ (hp.move _ ht)
  apply compare_limit (f := f i) (g := f j) hC
    (fun r h' => ⟨hcon _ _ (hp r h'), hcon _ _ (hp r h')⟩)
    (fun r h' t ht => ⟨hnon _ _ (hp r h') t ht, hnon _ _ (hp r h') t ht⟩)
    (fun r h' t ht => ⟨h.tail (hp r h') _ ht, h.tail (hp r h') _ ht⟩) hnear
    (fun t ht => ⟨ray_limit h hw' i ht.le, ray_limit h hw' j ht.le⟩)
    ((lifted_limit h hw').const_mul E) ?_ hζ
  intro r h'
  -- 推导：记下中间结论 `hu`：`atDepth r w ≤ (2 : ℝ) • atDepth 1 v`。
  have hu : atDepth r w ≤ (2 : ℝ) • atDepth 1 v := by
    have he (k : Fin 3) : w k ≤ 2 * v k := hw.2 k
    intro k
    fin_cases k <;> simp [atDepth] <;> linarith [h'.2, he 0, he 1, he 2]
  exact he _ (hp r h') hu (hw.1 0) (add_le_add (hw.1 1) (hw.1 2)) (tangent i) (tangent j)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Face
end

section
/-!
# 无穷远处的谱接触

局部化的速率估计在倒数坐标的一个面上给出一个零点。强极小值原理先沿切向传播该零点，再由法向比较得到三脚架上的有限接触点。

**英文原文**

Spectral contact at infinity

The localized rate estimate gives a zero at one point of a reciprocal
face. The strong minimum principle first propagates it tangentially;
normal comparison then gives a finite contact on the tripod.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Minimum Face Set Filter
open scoped Topology

variable {F : Type} [Field F] {D : Vec → ℝ}

-- 读法：存在 `v`，`Positive v` 与 `defect D v = 0` 同时成立。
private theorem StarTripod.face_zero (h : StarTripod F D)
    (hc : Uniform (defect D)) (hz : limit D 1 1 = 0) :
    ∃ v, Positive v ∧ defect D v = 0 := by
  have hl (y : ℝ) (hy : 0 < y) : Tendsto (fun r => defect D ![r, y, 1]) (𝓝[>] 0) (𝓝 0) := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have he := vanishes (regular h) (comparison h hc) (positive zero_lt_one hhalf hhalf)
      (by norm_num [lifted, Matrix.cons_val_two, hz]) (positive hy hhalf hhalf)
    norm_num [lifted, Matrix.cons_val_two] at he
    have hh := tends h hy zero_lt_one
    rwa [he] at hh
  have h₀ (r t : ℝ) : ray (defect D) ![r, 1, 1] 0 t = defect D ![r + t, 1, 1] := by
    unfold ray
    congr 1
    ext i; fin_cases i <;> simp [move]
  have h₁ (r t : ℝ) : ray (defect D) ![r, 1, 1] 1 t = defect D ![r, 1 + t, 1] := by
    unfold ray
    congr 1
    ext i; fin_cases i <;> simp [move]
  -- 推导：从 `hc _ (positive zero_lt_one zero_lt_one zero_lt_one)` 中取出 `E, _, he`。
  obtain ⟨E, _, he⟩ := hc _ (positive zero_lt_one zero_lt_one zero_lt_one)
  apply Minimum.face_zero h.toTripod.regular (E := E) (by norm_num : (0 : ℝ) ≤ 2) hl
  · intro r hr t ht
    have hh := (h.step (positive hr.1 zero_lt_one zero_lt_one) 0 le_rfl ht).1
    rw [ray_zero, h₀, Fin.sum_univ_three] at hh
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_zero] at hh
    have hd : t / (r + 1 + 1) ^ 2 ≤ t := div_le_self ht (by nlinarith [hr.1])
    linarith
  · intro r hr t ht
    have hh := (h.step (positive hr.1 zero_lt_one zero_lt_one) 1 le_rfl ht).2
    rw [ray_zero, h₁] at hh
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero, one_pow, div_one] at hh
    linarith
  · intro r hr t ht
    rw [← h₁]
    exact h.tail (positive hr.1 zero_lt_one zero_lt_one) 1 ht
  · intro r hr
    refine he _ (positive hr.1 zero_lt_one zero_lt_one) ?_ le_rfl le_rfl 0 1
    intro i
    fin_cases i <;> simp; linarith [hr.2]

-- 读法：`Localized` 表示以下条件：对每个 `x : ℝ`，由 `1 < x` 推出 `D ![x, 1, 1] ≤ x + 3 / 2 + 1 / (2 * x)`。
/-- 将长臂截断在长度 `x` 处，短臂的长度均为一。

英文原文：Truncation of the long arm at length `x`, with short arms of
unit length.
-/
def Localized (D : Vec → ℝ) : Prop :=
  ∀ x : ℝ, 1 < x → D ![x, 1, 1] ≤ x + 3 / 2 + 1 / (2 * x)

-- 读法：`limit D 1 1` 等于 `0`。这里调用 `ge_of_tendsto`。
theorem StarTripod.localized_zero (h : StarTripod F D) (hl : Localized D) : limit D 1 1 = 0 := by
  have ht := tends h zero_lt_one zero_lt_one
  have hpos : 0 ≤ limit D 1 1 := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h.toTripod.regular.nonneg _ (positive hr zero_lt_one zero_lt_one)
  refine le_antisymm ?_ hpos
  apply le_of_tendsto_of_tendsto ht (tendsto_id.mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with r hr
  obtain ⟨hr, hr'⟩ := hr
  have hu := hl r⁻¹ ((one_lt_inv₀ hr).mpr hr')
  -- 推导：记下中间结论 `he`：`(![r, 1, 1] : Vec)⁻¹ = ![r⁻¹, 1, 1]`。
  have he : (![r, 1, 1] : Vec)⁻¹ = ![r⁻¹, 1, 1] := by ext i; fin_cases i <;> simp
  rw [defect, he]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, inv_one, id_eq]
  have h₁ : (r + 1 + 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  have h₂ : 1 / (2 * r⁻¹) = r / 2 := by field_simp
  rw [h₂] at hu
  linarith

-- 读法：要证明的命题是 `Prices F (x / dStar x y z) (y / dStar x y z) (z / dStar x y z)`。这里调用 `h.toTripod.boundary`。
/-- 齐次三叉树在无穷远处的一个零点，使得整个正极性边界均在谱价格空间中得以实现。

英文原文：A zero at infinity on a homogeneous tripod realizes the entire
positive polar boundary in the space of spectral prices.
-/
theorem StarTripod.boundary_of_limit (h : StarTripod F D) (hc : Uniform (defect D))
    (hz : limit D 1 1 = 0) (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz' : 0 < z) :
    Prices F (x / dStar x y z) (y / dStar x y z) (z / dStar x y z) := by
  obtain ⟨v, hv, hz⟩ := h.face_zero hc hz
  have ha : Positive v⁻¹ := fun i => inv_pos.mpr (hv i)
  have he := defect_inv D ha
  rw [inv_inv, hz, eq_comm, sub_eq_zero] at he
  exact h.toTripod.boundary hc.interior ha he x y z hx hy hz'

-- 读法：要证明的命题是 `Rigidity F`。使用 `rigidity_of_contact` 给出的结论。
theorem StarTripod.rigidity_of_limit (h : StarTripod F D) (hc : Uniform (defect D))
    (hz : limit D 1 1 = 0) : Rigidity F :=
  rigidity_of_contact (support F) (diagonal F) (fun _ => h.boundary_of_limit hc hz)

-- 读法：`MatrixExponent.omega F` 等于 `9 / 4`。这里调用 `square_iff_contact`。
theorem StarTripod.square_of_limit (h : StarTripod F D) (hc : Uniform (defect D))
    (hz : limit D 1 1 = 0) : MatrixExponent.omega F = 9 / 4 := by
  have hp := h.boundary_of_limit hc hz 1 1 1 zero_lt_one zero_lt_one zero_lt_one
  norm_num [dStar] at hp
  exact (square_iff_contact F).mpr hp

-- 读法：`MatrixExponent.omega F` 等于 `9 / 4`。使用 `h.square_of_limit` 给出的结论。
theorem StarTripod.square (h : StarTripod F D) (hc : Uniform (defect D)) (hl : Localized D) :
    MatrixExponent.omega F = 9 / 4 :=
  h.square_of_limit hc (h.localized_zero hl)

-- 读法：`1 / 2` 严格小于 `dual F 1 1`。这里调用 `hs.ne`。
/-- 为证明对偶情形下的严格节省，所余的几何条件是存在一棵满足一致比较的局部化三叉树。

英文原文：A localized tripod with uniform comparison is the remaining
geometric input for the strict dual saving.
-/
theorem dual_of_localization (h : Escapes F → ∃ D,
    StarTripod F D ∧ Uniform (defect D) ∧ Localized D)
    (hs : MatrixExponent.omega F < 9 / 4) : 1 / 2 < dual F 1 1 := by
  by_contra! he
  obtain ⟨D, hD, hc, hl⟩ := h (escapes_of_dual he)
  exact hs.ne (hD.square hc hl)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
