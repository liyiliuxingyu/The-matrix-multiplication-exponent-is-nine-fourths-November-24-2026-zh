-- 本文件所属证明环节：逐条列出单位、可加性和序约束依赖哪些坐标，证明在这些坐标上一致即可判断约束。由此将紧致性给出的矛盾进一步压缩到有限坐标集。
import OAI.LinearAlgebra.TensorSpectrum.Additive.States
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Positivity

/-!
紧性障碍可以限制到包含单位元在内的有限多个坐标。在其余坐标处，零总是盒子允许的坐标值。这给出了有理线性消元所需的具体有限维输入。

**英文原文**

The compactness obstruction can be restricted to finitely many coordinates,
including the unit. Outside those coordinates, zero is a valid box coordinate.
This is the concrete finite-dimensional input to rational linear elimination.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

-- 读法：`StateConstraint.coordinates` 的结果类型为 `StateConstraint S → Finset S`。
noncomputable def StateConstraint.coordinates (T : S) : StateConstraint S → Finset S := by
  classical
  exact fun c => match c with
    | .zero => {0}
    | .one => {1}
    | .add x y => {x + y, x, y}
    | .order x y _ => {x, y}
    | .detect s => {T * s, s}

-- 读法：`c.Holds T k f` 与 `c.Holds T k g` 等价。对 `c` 分类讨论。
theorem StateConstraint.holds_congr (T : S) (k : ℕ) (c : StateConstraint S)
    {f g : S → ℝ} (h : ∀ x ∈ c.coordinates T, f x = g x) :
    c.Holds T k f ↔ c.Holds T k g := by
  classical
  cases c with
  | zero => simp only [StateConstraint.Holds, h 0 (by simp [StateConstraint.coordinates])]
  | one => simp only [StateConstraint.Holds, h 1 (by simp [StateConstraint.coordinates])]
  | add x y =>
    simp only [StateConstraint.Holds, h (x + y) (by simp [StateConstraint.coordinates]),
      h x (by simp [StateConstraint.coordinates]), h y (by simp [StateConstraint.coordinates])]
  | order x y hxy =>
    simp only [StateConstraint.Holds, h x (by simp [StateConstraint.coordinates]),
      h y (by simp [StateConstraint.coordinates])]
  | detect s =>
    simp only [StateConstraint.Holds, h (T * s) (by simp [StateConstraint.coordinates]),
      h s (by simp [StateConstraint.coordinates])]

-- 读法：存在 `(F : Finset (StateConstraint S)) (U : Finset S)`，由 `0 ∈ U ∧ 1 ∈ U ∧ (∀ c ∈ F, c.coordinates T ⊆ U) ∧ ¬ ∃ f : S` 推出 `ℝ, (∀ s ∈ U, f s ∈ Icc 0 (R s : ℝ)) ∧ ∀ c ∈ F, c.Holds T k f`。这里调用 `Finset.mem_union.mpr`。
/-- 有限障碍只包含这些坐标界，因此应用于有限有理锥定理的是一个有限系统。

英文原文：A finite obstruction includes only these coordinate bounds; no infinite
system is passed silently to the finite rational cone theorem.
-/
theorem finite_coordinate_obstruction (T : S) (k : ℕ) (R : S → ℕ)
    (hnone : stateSet T k = ∅) :
    ∃ (F : Finset (StateConstraint S)) (U : Finset S),
      0 ∈ U ∧ 1 ∈ U ∧
      (∀ c ∈ F, c.coordinates T ⊆ U) ∧
      ¬ ∃ f : S → ℝ, (∀ s ∈ U, f s ∈ Icc 0 (R s : ℝ)) ∧
        ∀ c ∈ F, c.Holds T k f := by
  classical
  obtain ⟨F, hF⟩ := finite_inconsistent_subsystem T k R hnone
  let U : Finset S := {0, 1} ∪ F.biUnion (fun c => c.coordinates T)
  -- 推导：记下中间结论 `hsub`：`∀ c ∈ F, c.coordinates T ⊆ U`。
  have hsub : ∀ c ∈ F, c.coordinates T ⊆ U := by
    intro c hc x hx
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨c, hc, hx⟩))
  refine ⟨F, U, by simp [U], by simp [U], hsub, ?_⟩
  rintro ⟨f, hbox, hconstraints⟩
  let g : S → ℝ := fun s => if s ∈ U then f s else 0
  apply hF
  refine ⟨g, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ U
    · simpa only [g, ite_eq_left hs] using hbox s hs
    · simp only [g, ite_eq_right hs, mem_Icc, le_refl, true_and]
      positivity
  · intro c hc
    apply (c.holds_congr T k (f := f) (g := g) ?_).mp (hconstraints c hc)
    intro x hx
    simp only [g, ite_eq_left (hsub c hc hx)]

end OAI.LinearAlgebra.TensorSpectrum
