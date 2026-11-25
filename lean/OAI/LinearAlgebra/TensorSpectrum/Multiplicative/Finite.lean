-- 本文件所属证明环节：对有限个归一化乘法映射做归纳。逐次固定一个特征值，并把下一次不动点构造限制在相应的紧凸仿射切片内，使已满足的方程继续成立。
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective

/-!
# 沿冻结仿射切片作有限次迭代

这里证明附录 A.2 所用的有限归纳。显式列出的局部不动点前提是为调用另行证明的射影特征状态定理而设置的接口；它既不是新增公理，也不等于特征标存在性的最终结论。

**英文原文**

Finite iteration through frozen affine slices

This is the finite induction in Appendix A.2. Its explicit local fixed-point
premise is the interface for the separately proved projective eigenstate theorem;
it is not an axiom or a completed character-existence result.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommMonoidWithZero S]

-- 读法：对每个 `F : Finset {z : S // z ≠ 0}`，存在 `f ∈ K`，对每个 `z ∈ F`，`f` 属于 `multiplicativeSet z.val`。对 `F` 作归纳，采用 `Finset.induction_on` 的归纳原则。
theorem finite_common_points_of_slice_fixedPoints
    (K : Set (S → ℝ)) (hK : K.Nonempty) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hunit : ∀ f ∈ K, f 1 = 1)
    (hpos : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hinvariant : ∀ z : S, z ≠ 0 → MapsTo (projective z) K K)
    (hfixed : ∀ L : Set (S → ℝ), L ⊆ K → L.Nonempty → IsCompact L →
      Convex ℝ L → (∀ z : S, z ≠ 0 → MapsTo (projective z) L L) →
      ∀ z : S, z ≠ 0 → ∃ f ∈ L, projective z f = f) :
    ∀ F : Finset {z : S // z ≠ 0},
      ∃ f ∈ K, ∀ z ∈ F, f ∈ multiplicativeSet z.val := by
  classical
  have hslices : ∀ F : Finset {z : S // z ≠ 0},
      ∃ L : Set (S → ℝ), L ⊆ K ∧ L.Nonempty ∧ IsCompact L ∧ Convex ℝ L ∧
        (∀ z : S, z ≠ 0 → MapsTo (projective z) L L) ∧
        (∀ f ∈ L, ∀ z ∈ F, f ∈ multiplicativeSet z.val) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨K, subset_rfl, hK, hcompact, hconvex, hinvariant, by simp⟩
    | @insert z F _ ih =>
      -- 推导：从 `ih` 中取出 `L, hLK, hL, hLc, hLv, hLi, hLF`。
      obtain ⟨L, hLK, hL, hLc, hLv, hLi, hLF⟩ := ih
      obtain ⟨f, hf, hfx⟩ := hfixed L hLK hL hLc hLv hLi z.val z.property
      let L' := L ∩ eigenSlice z.val (f z.val)
      have hfrozen := freeze_fixedPoint L z.val f hLc hLv hf hfx
        (hpos f (hLK hf) z.val z.property) hLi
      change f ∈ L' ∧ IsCompact L' ∧ Convex ℝ L' ∧
        (∀ w, w ≠ 0 → MapsTo (projective w) L' L') at hfrozen
      refine ⟨L', fun g hg => hLK hg.1, ⟨f, hfrozen.1⟩,
        hfrozen.2.1, hfrozen.2.2.1, hfrozen.2.2.2, ?_⟩
      intro g hg w hw
      rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw]
        exact eigenSlice_mem_multiplicativeSet z.val (f z.val) g hg.2
          (hunit g (hLK hg.1))
      · exact hLF g hg.1 w hw
  intro F
  -- 推导：从 `hslices F` 中取出 `L, hLK, ⟨f, hf⟩, _, _, _, hLF`。
  obtain ⟨L, hLK, ⟨f, hf⟩, _, _, _, hLF⟩ := hslices F
  exact ⟨f, hLK hf, hLF f hf⟩

end OAI.LinearAlgebra.TensorSpectrum
