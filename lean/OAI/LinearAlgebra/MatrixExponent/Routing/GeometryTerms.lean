-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Completion

section
/-!
# 距离平方的比较与方差

采用 CAT(0) 不等式的测地比较形式。期望均取为有限集上的均匀平均。

**英文原文**

Squared-distance comparison and variance

We use the geodesic comparison form of the CAT(0) inequality.
The expectations are uniform finite averages.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators

-- 读法：`Comparison` 的结果类型为 `Prop`。
def Comparison (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ (x y : Y) (t : ℝ), 0 ≤ t → t ≤ 1 →
    ∃ m : Y, dist x m = t * dist x y ∧
      ∀ z, dist m z ^ 2 ≤
        (1 - t) * dist x z ^ 2 + t * dist y z ^ 2 - t * (1 - t) * dist x y ^ 2

-- 读法：`Bary` 表示以下条件：对每个 `z`，`(𝔼 i, dist o (x i) ^ 2) + dist o z ^ 2` 不超过 `(𝔼 i, dist z (x i) ^ 2)`。
def Bary {Y A : Type*} [MetricSpace Y] [Fintype A] (x : A → Y) (o : Y) : Prop :=
  ∀ z, (𝔼 i, dist o (x i) ^ 2) + dist o z ^ 2 ≤ (𝔼 i, dist z (x i) ^ 2)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 测地项

固定分点比例后，在满足距离平方比较的空间中，测地插值对两个端点联合一致连续。

**英文原文**

Geodesic terms

For a fixed fraction, interpolation in a space satisfying squared
distance comparison is uniformly continuous in both endpoints.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open UniformSpace

-- 读法：在后续公式中，`Fraction` 是 `↥(Set.Icc (0 : ℝ) 1)` 的缩写。
abbrev Fraction := ↥(Set.Icc (0 : ℝ) 1)

-- 读法：`Along` 表示以下条件：对每个 `z`，`dist m z ^ 2` 不超过 `(1 - u.val) * dist x z ^ 2 + u.val * dist y z ^ 2 - u.val * (1 - u.val) * dist x y ^ 2`。
def Along {Y : Type*} [PseudoMetricSpace Y] (u : Fraction) (x y m : Y) : Prop :=
  ∀ z, dist m z ^ 2 ≤ (1 - u.val) * dist x z ^ 2 + u.val * dist y z ^ 2 -
    u.val * (1 - u.val) * dist x y ^ 2

section
variable {Y : Type*} [PseudoMetricSpace Y] {u : Fraction} {x y m x' y' m' : Y}

-- 读法：`Fraction.rev` 的取值由 `⟨1 - u.val, sub_nonneg.mpr u.2.2, sub_le_self _ u.2.1⟩` 给出。
def Fraction.rev (u : Fraction) : Fraction :=
  ⟨1 - u.val, sub_nonneg.mpr u.2.2, sub_le_self _ u.2.1⟩

-- 读法：要证明的命题是 `Along u.rev y x m`。
theorem Along.rev (h : Along u x y m) : Along u.rev y x m := by
  intro z
  rw [dist_comm y x]
  change dist m z ^ 2 ≤ (1 - (1 - u.val)) * dist y z ^ 2 + (1 - u.val) * dist x z ^ 2 -
    (1 - u.val) * (1 - (1 - u.val)) * dist x y ^ 2
  linarith only [h z]

-- 读法：`dist x m` 不超过 `u.val * dist x y`。这里调用 `sq_le_sq₀`。
private theorem Along.dist_le (h : Along u x y m) : dist x m ≤ u.val * dist x y := by
  have hh := h x
  rw [dist_self, dist_comm m x, dist_comm y x] at hh
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg u.2.1 dist_nonneg)).mp
  linarith only [hh]

-- 读法：`dist x m` 等于 `u.val * dist x y`。
theorem Along.start (h : Along u x y m) : dist x m = u.val * dist x y := by
  have hh := h.rev.dist_le
  change dist y m ≤ (1 - u.val) * dist y x at hh
  rw [dist_comm y m, dist_comm y x] at hh
  linarith [h.dist_le, dist_triangle x m y]

-- 读法：`dist m m'` 不超过 `u.val * dist y y'`。这里调用 `sq_le_sq₀`。
theorem Along.dist_right (h : Along u x y m) (h' : Along u x y' m') :
    dist m m' ≤ u.val * dist y y' := by
  have h₁ := h m'
  rw [h'.start, dist_comm y m'] at h₁
  have h₂ := mul_le_mul_of_nonneg_left (h' y) u.2.1
  rw [dist_comm y' y] at h₂
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg u.2.1 dist_nonneg)).mp
  linarith only [h₁, h₂]

-- 读法：要证明的命题是 `UniformContinuous₂ f`。这里调用 `LipschitzWith.uniformContinuous`。
theorem uniformContinuous_along (f : Y → Y → Y) (hf : ∀ x y, Along u x y (f x y)) :
    UniformContinuous₂ f := by
  apply LipschitzWith.uniformContinuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, w⟩
  have h₁ := (hf x y).rev.dist_right (hf z y).rev
  have h₂ := (hf z y).dist_right (hf z w)
  have h₃ := mul_le_mul_of_nonneg_left (le_max_left (dist x z) (dist y w)) u.rev.2.1
  have h₄ := mul_le_mul_of_nonneg_left (le_max_right (dist x z) (dist y w)) u.2.1
  change dist (f x y) (f z w) ≤ 1 * max (dist x z) (dist y w)
  dsimp only [Fraction.rev] at h₁ h₃
  linarith only [h₁, h₂, h₃, h₄, dist_triangle (f x y) (f z y) (f z w)]
end

variable {Y : Type*} [MetricSpace Y] (C : Comparison Y)

-- 读法：`Comparison.seg` 的取值由 `(C x y u u.2.1 u.2.2).choose` 给出。
def Comparison.seg (u : Fraction) (x y : Y) : Y := (C x y u u.2.1 u.2.2).choose

-- 读法：要证明的命题是 `Along u x y (C.seg u x y)`。
theorem Comparison.along (u : Fraction) (x y : Y) : Along u x y (C.seg u x y) :=
  (C x y u u.2.1 u.2.2).choose_spec.2

-- 读法：`m` 等于 `m'`。
theorem Along.unique {u : Fraction} {x y m m' : Y}
    (h : Along u x y m) (h' : Along u x y m') : m = m' := by
  have hh := h.dist_right h'
  simpa using hh

-- 读法：归纳构造子包括 `mark`、`seg`。
/-- 以标记站址构成表达式，无需为重心增添生成元。

英文原文：Expressions in marked sites, with no new generators for barycenters.
-/
inductive Term (G : Type*) where
  | mark (g : G)
  | seg (u : Fraction) (a b : Term G)

namespace Term
variable {G : Type*}

-- 读法：逐一匹配以下输入模式：`.mark g`、`.seg u a b`。
def eval (x : G → Y) : Term G → Y
  | .mark g => x g
  | .seg u a b => C.seg u (eval x a) (eval x b)

-- 读法：逐一匹配以下输入模式：`.mark g`、`.seg u a b`。
def map {G' : Type*} (f : G → G') : Term G → Term G'
  | .mark g => .mark (f g)
  | .seg u a b => .seg u (map f a) (map f b)

-- 读法：用字段 `smul`、`one_smul`、`mul_smul` 构造 `MulAction G (Term G)`。
instance [Group G] : MulAction G (Term G) where
  smul g := map (g * ·)
  one_smul t := by
    change map (1 * ·) t = t
    induction t with
    | mark => simp [map]
    | seg u a b ha hb => exact congrArg₂ (seg u) ha hb
  mul_smul g h t := by
    change map (g * h * ·) t = map (g * ·) (map (h * ·) t)
    induction t with
    | mark => simp [map, mul_assoc]
    | seg u a b ha hb => exact congrArg₂ (seg u) ha hb

end Term
end OAI.LinearAlgebra.MatrixExponent.Routing
end
