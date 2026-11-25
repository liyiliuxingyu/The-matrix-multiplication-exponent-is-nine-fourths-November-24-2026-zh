-- 本文件所属证明环节：定义归一化乘法映射、特征值切片和乘法性条件集，验证其连续性、闭性和凸性，并证明冻结一个特征值后仍可继续寻找共同不动点。
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring

/-!
# 附录 A.2 中的射影映射与冻结仿射切片

以下引理给出构造特征标时实际使用的映射。固定特征值后所得切片是凸的；对整个非线性不动点集，这里只断言其闭性。最后一条引理是利用紧性处理有限交的一步，所需各有限族的公共不动点的存在性另行证明。

**英文原文**

The projective maps and frozen affine slices in Appendix A.2

These lemmas isolate the actual maps used by the character construction. A
frozen eigenvalue slice is convex; the full nonlinear fixed set is only claimed
to be closed. The last lemma is the compact finite-intersection step, not an
existence theorem for the required finite common fixed points.
-/

noncomputable section

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

-- 读法：输入 `x` 时返回 `f (z * x) / f z`。
/-- 附录 A.2 中的归一化乘法映射。

英文原文：The normalized multiplication map from Appendix A.2.
-/
def projective (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

-- 读法：`eigenSlice` 的取值由 `{f | ∀ x, f (z * x) = c * f x}` 给出。
/-- 将特征值固定为实常数，使所得方程仍为仿射方程。

英文原文：Freeze the eigenvalue as a real constant, retaining affine equations.
-/
def eigenSlice (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

-- 读法：`multiplicativeSet` 的取值由 `{f | ∀ x, f (z * x) = f z * f x}` 给出。
/-- 针对单个乘子的原始非线性乘法性方程。

英文原文：The original nonlinear multiplicativity equations for one multiplier.
-/
def multiplicativeSet (z : S) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = f z * f x}

-- 读法：`projective z f 1` 等于 `1`。
theorem projective_one (z : S) (f : S → ℝ) (hz : f z ≠ 0) :
    projective z f 1 = 1 := by
  simp [projective, hz]

-- 读法：`projective z f 0` 等于 `0`。
theorem projective_zero (z : S) (f : S → ℝ) (hzero : f 0 = 0) :
    projective z f 0 = 0 := by
  simp [projective, hzero]

-- 读法：`projective z f = f` 与 `f ∈ multiplicativeSet z` 等价。这里调用 `div_eq_iff`。
theorem projective_fixed_iff (z : S) (f : S → ℝ) (hz : f z ≠ 0) :
    projective z f = f ↔ f ∈ multiplicativeSet z := by
  constructor
  · intro h x
    have hx := congrFun h x
    change f (z * x) / f z = f x at hx
    exact (div_eq_iff hz).mp hx |>.trans (mul_comm _ _)
  · intro h
    funext x
    change f (z * x) / f z = f x
    rw [h x, mul_div_cancel_left₀ _ hz]

-- 读法：要证明的命题是 `ContinuousOn (projective z) K`。这里调用 `continuousOn_pi.2`。
theorem continuousOn_projective (z : S) (K : Set (S → ℝ))
    (hz : ∀ f ∈ K, f z ≠ 0) : ContinuousOn (projective z) K := by
  apply continuousOn_pi.2
  intro x
  exact (continuous_apply (z * x)).continuousOn.div
    (continuous_apply z).continuousOn hz

-- 读法：`(eigenSlice z c)` 是闭集。这里调用 `isClosed_iInter`。
theorem eigenSlice_isClosed (z : S) (c : ℝ) : IsClosed (eigenSlice z c) := by
  have h : eigenSlice z c = ⋂ x : S, {f : S → ℝ | f (z * x) = c * f x} := by
    ext f
    simp only [eigenSlice, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

-- 读法：要证明的命题是 `Convex ℝ (eigenSlice z c)`。
theorem eigenSlice_convex (z : S) (c : ℝ) : Convex ℝ (eigenSlice z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

-- 读法：`(multiplicativeSet z)` 是闭集。这里调用 `isClosed_iInter`。
theorem multiplicativeSet_isClosed (z : S) : IsClosed (multiplicativeSet z) := by
  have h : multiplicativeSet z =
      ⋂ x : S, {f : S → ℝ | f (z * x) = f z * f x} := by
    ext f
    simp only [multiplicativeSet, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun x => isClosed_eq (continuous_apply (z * x))
    ((continuous_apply z).mul (continuous_apply x))

-- 读法：`projective w f` 属于 `eigenSlice z c`。
/-- 其余每个射影映射都保持每个固定后的方程。证明这一代数事实，无需消去可能为零的坐标或除以该坐标。

英文原文：All other projective maps preserve every frozen equation. No cancellation
or division by a possibly zero coordinate is needed for this algebraic fact.
-/
theorem projective_mem_eigenSlice (z w : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) : projective w f ∈ eigenSlice z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

-- 读法：`f z` 等于 `c`。
theorem eigenSlice_eigenvalue (z : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) (hunit : f 1 = 1) : f z = c := by
  simpa only [mul_one, hunit] using hf 1

-- 读法：`f` 属于 `multiplicativeSet z`。
theorem eigenSlice_mem_multiplicativeSet (z : S) (c : ℝ) (f : S → ℝ)
    (hf : f ∈ eigenSlice z c) (hunit : f 1 = 1) :
    f ∈ multiplicativeSet z := by
  intro x
  rw [hf x, eigenSlice_eigenvalue z c f hf hunit]

-- 读法：结论为 `let L := K ∩ eigenSlice z (f z) f ∈ L ∧ IsCompact L ∧ Convex ℝ L ∧ (∀ w, w ≠ 0 → MapsTo (projective w) L L)`。
/-- 得到一个不动点后，把其特征值固定下来即可保留这个见证，并得到对每个射影映射都不变的紧凸切片。

英文原文：Once a fixed point is obtained, freezing its eigenvalue preserves that
witness and yields a compact convex slice invariant under every projective map.
-/
theorem freeze_fixedPoint (K : Set (S → ℝ)) (z : S) (f : S → ℝ)
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) (hf : f ∈ K)
    (hfixed : projective z f = f) (hz : f z ≠ 0)
    (hinvariant : ∀ w, w ≠ 0 → MapsTo (projective w) K K) :
    let L := K ∩ eigenSlice z (f z)
    f ∈ L ∧ IsCompact L ∧ Convex ℝ L ∧
      (∀ w, w ≠ 0 → MapsTo (projective w) L L) := by
  dsimp only
  refine ⟨⟨hf, (projective_fixed_iff z f hz).mp hfixed⟩,
    hcompact.inter_right (eigenSlice_isClosed z (f z)),
    hconvex.inter (eigenSlice_convex z (f z)), ?_⟩
  intro w hw g hg
  exact ⟨hinvariant w hw hg.1, projective_mem_eigenSlice z w (f z) g hg.2⟩

-- 读法：存在 `f ∈ K`，对每个 `z x`，`f (z * x)` 等于 `f z * f x`。这里调用 `hcompact.inter_iInter_nonempty`。
/-- 附录 A.2 中的紧性步骤。应用此引理时须另行给出每个有限族的公共不动点。

英文原文：The compactness step in Appendix A.2. Finite common fixed points are an
explicit obligation; this lemma does not assume or assert their existence.
-/
theorem multiplicative_of_finite_common_points
    (K : Set (S → ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ f ∈ K, f 0 = 0)
    (hfinite : ∀ F : Finset {z : S // z ≠ 0},
      ∃ f ∈ K, ∀ z ∈ F, f ∈ multiplicativeSet z.val) :
    ∃ f ∈ K, ∀ z x, f (z * x) = f z * f x := by
  have hnonempty : (K ∩ ⋂ z : {z : S // z ≠ 0}, multiplicativeSet z.val).Nonempty := by
    apply hcompact.inter_iInter_nonempty
      (fun z : {z : S // z ≠ 0} => multiplicativeSet z.val)
      (fun z => multiplicativeSet_isClosed z.val)
    intro F
    -- 推导：从 `hfinite F` 中取出 `f, hf, hF`。
    obtain ⟨f, hf, hF⟩ := hfinite F
    refine ⟨f, hf, ?_⟩
    simp only [mem_iInter]
    exact hF
  obtain ⟨f, hf, hall⟩ := hnonempty
  refine ⟨f, hf, ?_⟩
  intro z x
  by_cases hz : z = 0
  · simp [hz, hzero f hf]
  · exact (mem_iInter.mp hall ⟨z, hz⟩) x

end OAI.LinearAlgebra.TensorSpectrum
