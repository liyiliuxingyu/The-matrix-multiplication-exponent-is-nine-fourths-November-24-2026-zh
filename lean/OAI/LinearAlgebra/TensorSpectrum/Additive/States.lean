-- 本文件所属证明环节：把归一化、保序和可加条件写成实函数乘积空间中的闭约束，在各坐标上给出使状态空间紧致的盒子；若没有状态，有限多个约束已经矛盾。
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 附录 A.1 中的紧致加性态空间

本文件给出拓扑归约，将障碍化为一个不相容的有限系统。归约本身并不建立该系统的可解性；排除这种有限障碍还要用到整数锥证书和关于张量秩增长的论证。

**英文原文**

The compact additive-state space in Appendix A.1

This file proves the topological reduction to a finite inconsistent system. It
does not assert that this system has a solution: ruling out a finite obstruction
also requires the integer cone certificate and the tensor rank-growth argument.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

-- 读法：`stateSet` 的取值由 `{f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧ Monotone f ∧ ∀ s, (k : ℝ) * f s ≤ f (T * s)}` 给出。
/-- 归一化、可加且单调的状态还须满足检测不等式；此定义不要求乘法性。

英文原文：Normalized additive monotone states with the additional detection inequality.
Multiplicativity is deliberately not included.
-/
def stateSet (T : S) (k : ℕ) : Set (S → ℝ) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    Monotone f ∧ ∀ s, (k : ℝ) * f s ≤ f (T * s)}

-- 读法：归纳构造子包括 `zero`、`one`、`add`、`order`、`detect`。
/-- 逐项表述的条件，每项仅涉及有限多个坐标。

英文原文：Individual conditions, each of which uses only finitely many coordinates.
-/
inductive StateConstraint (S : Type*) [CommSemiring S] [PartialOrder S] where
  | zero
  | one
  | add (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detect (s : S)

-- 读法：逐一匹配输入模式，例如 `.zero`、`.one`、`.add x y`、`.order x y _`。
def StateConstraint.Holds (T : S) (k : ℕ) (f : S → ℝ) :
    StateConstraint S → Prop
  | .zero => f 0 = 0
  | .one => f 1 = 1
  | .add x y => f (x + y) = f x + f y
  | .order x y _ => f x ≤ f y
  | .detect s => (k : ℝ) * f s ≤ f (T * s)

-- 读法：`f ∈ stateSet T k` 与 `∀ c : StateConstraint S, c.Holds T k f` 等价。对 `c` 分类讨论。
theorem mem_stateSet_iff (T : S) (k : ℕ) (f : S → ℝ) :
    f ∈ stateSet T k ↔ ∀ c : StateConstraint S, c.Holds T k f := by
  constructor
  · rintro ⟨hzero, hone, hadd, hmono, hdetect⟩ c
    cases c with
    | zero => exact hzero
    | one => exact hone
    | add x y => exact hadd x y
    | order x y h => exact hmono h
    | detect s => exact hdetect s
  · intro h
    exact ⟨h .zero, h .one, fun x y => h (.add x y),
      fun _ _ hxy => h (.order _ _ hxy), fun s => h (.detect s)⟩

-- 读法：`{f : S → ℝ | c.Holds T k f}` 是闭集。对 `c` 分类讨论。
theorem StateConstraint.isClosed (T : S) (k : ℕ) (c : StateConstraint S) :
    IsClosed {f : S → ℝ | c.Holds T k f} := by
  cases c with
  | zero => exact isClosed_eq (continuous_apply 0) continuous_const
  | one => exact isClosed_eq (continuous_apply 1) continuous_const
  | add x y =>
    exact isClosed_eq (continuous_apply (x + y))
      ((continuous_apply x).add (continuous_apply y))
  | order x y _ => exact isClosed_le (continuous_apply x) (continuous_apply y)
  | detect s =>
    exact isClosed_le (continuous_const.mul (continuous_apply s))
      (continuous_apply (T * s))

-- 读法：`(stateSet T k)` 是闭集。这里调用 `isClosed_iInter`。
theorem stateSet_isClosed (T : S) (k : ℕ) : IsClosed (stateSet T k) := by
  have heq : stateSet T k = ⋂ c : StateConstraint S, {f | c.Holds T k f} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq, mem_stateSet_iff]
  rw [heq]
  exact isClosed_iInter fun c => c.isClosed T k

-- 读法：`f (n : S)` 等于 `(n : ℝ)`。对 `n` 作归纳。
theorem state_natCast {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (n : ℕ) : f (n : S) = (n : ℝ) := by
  induction n with
  | zero => simpa only [Nat.cast_zero] using hf.1
  | succ n ih =>
    rw [Nat.cast_succ, hf.2.2.1, ih, hf.2.1, Nat.cast_succ]

-- 读法：`coordinateBox` 的取值由 `{f | ∀ s, f s ∈ Icc 0 (R s : ℝ)}` 给出。
/-- 在坐标盒中，普通秩仅用于提供有限的上界。

英文原文：The coordinate box uses ordinary rank only as a finite upper bound.
-/
def coordinateBox (R : S → ℕ) : Set (S → ℝ) :=
  {f | ∀ s, f s ∈ Icc 0 (R s : ℝ)}

omit [CommSemiring S] [PartialOrder S] in
-- 读法：`(coordinateBox R)` 是紧集。使用 `isCompact_pi_infinite` 给出的结论。
theorem coordinateBox_isCompact (R : S → ℕ) : IsCompact (coordinateBox R) :=
  isCompact_pi_infinite fun _ => isCompact_Icc

-- 读法：`stateSet T k` 包含于 `coordinateBox R`。这里调用 `hf.2.2.2.1`。
theorem stateSet_subset_coordinateBox (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S)) :
    stateSet T k ⊆ coordinateBox R := by
  intro f hf s
  constructor
  · simpa only [hf.1] using hf.2.2.2.1 (hzero s)
  · simpa only [state_natCast hf] using hf.2.2.2.1 (hR s)

-- 读法：`(stateSet T k)` 是紧集。
theorem stateSet_isCompact (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S)) :
    IsCompact (stateSet T k) :=
  (coordinateBox_isCompact R).of_isClosed_subset (stateSet_isClosed T k)
    (stateSet_subset_coordinateBox T k R hzero hR)

-- 读法：要证明的命题是 `Convex ℝ (stateSet T k)`。
theorem stateSet_convex (T : S) (k : ℕ) : Convex ℝ (stateSet T k) := by
  intro f hf g hg a b ha hb hab
  change a * f 0 + b * g 0 = 0 ∧ a * f 1 + b * g 1 = 1 ∧
    (∀ x y, a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)) ∧
    Monotone (fun x => a * f x + b * g x) ∧
    ∀ s, (k : ℝ) * (a * f s + b * g s) ≤
      a * f (T * s) + b * g (T * s)
  refine ⟨by rw [hf.1, hg.1]; ring, by simpa [hf.2.1, hg.2.1] using hab, ?_, ?_, ?_⟩
  · intro x y
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 hxy) hb)
  · intro s
    have h := add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 s) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.2 s) hb)
    nlinarith

-- 读法：存在 `F : Finset (StateConstraint S)`，`¬ ∃ f` 属于 `coordinateBox R, ∀ c ∈ F, c.Holds T k f`。这里调用 `eq_empty_iff_forall_notMem.mpr`。
/-- 若状态不存在，紧性保证可取出一个实际的有限子系统。

英文原文：Compactness gives an actual finite subsystem when no state exists.
-/
theorem finite_inconsistent_subsystem (T : S) (k : ℕ) (R : S → ℕ)
    (hnone : stateSet T k = ∅) :
    ∃ F : Finset (StateConstraint S),
      ¬ ∃ f ∈ coordinateBox R, ∀ c ∈ F, c.Holds T k f := by
  have hempty : (coordinateBox R ∩
      ⋂ c : StateConstraint S, {f | c.Holds T k f}) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro f ⟨_, hf⟩
    have hstate : f ∈ stateSet T k := (mem_stateSet_iff T k f).mpr
      (by simpa only [mem_iInter, mem_ofPred_eq] using hf)
    rw [hnone] at hstate
    exact hstate
  -- 推导：从 `(coordinateBox_isCompact R).elim_finite_subfamily_closed` 中取出 `F, hF`。
  obtain ⟨F, hF⟩ := (coordinateBox_isCompact R).elim_finite_subfamily_closed
    (fun c : StateConstraint S => {f | c.Holds T k f})
    (fun c => c.isClosed T k) (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  refine ⟨F, ?_⟩
  rintro ⟨f, hf, hconstraints⟩
  have hmem : f ∈ coordinateBox R ∩
      ⋂ c ∈ F, {f | c.Holds T k f} :=
    ⟨hf, by simpa only [mem_iInter, mem_ofPred_eq] using hconstraints⟩
  exact Set.disjoint_left.mp hF hmem.1 hmem.2

end OAI.LinearAlgebra.TensorSpectrum
