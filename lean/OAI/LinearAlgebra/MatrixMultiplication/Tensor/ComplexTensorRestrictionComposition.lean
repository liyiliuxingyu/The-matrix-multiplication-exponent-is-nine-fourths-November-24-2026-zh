-- 本文件所属证明环节：写出连续两次张量限制的系数矩阵乘积并整理有限和，证明限制与张量积可交换、恒等限制保持张量，并据此建立退化关系的自反性和传递性。
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor

namespace OAI

/-!
有限系数张量及其代数变换。

**英文原文**

Finite coefficient tensors and their algebraic transformations.
-/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

-- 读法：输入 `x'' x` 时返回 `∑ x', D x'' x' * A x' x`。
def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

-- 读法：`(∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t` 等于 `∑ x, ∑ y, ∑ z, a x * b y * c z * t`。
private theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

-- 读法：`(∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z)` 等于 `∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z`。
private theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (f : X' → Y' → Z' → X → Y → Z → K) :
    (∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z) =
      ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z := by
  calc
    _ = ∑ p : X' × Y' × Z', ∑ q : X × Y × Z,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : X × Y × Z, ∑ p : X' × Y' × Z',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

-- 读法：`(∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w)` 等于 `∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w`。这里调用 `Finset.sum_congr`。
private theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

-- 读法：`restrict D E F (restrict A B C T)` 等于 `restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B) (composeRestrictionMatrix F C) T`。用函数外延性比较等号两侧在 `x'' y'' z''` 处的取值。
theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := sum_six_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [sum_three_mul]
      apply Finset.sum_congr rfl
      intro x' hx'
      apply Finset.sum_congr rfl
      intro y' hy'
      apply Finset.sum_congr rfl
      intro z' hz'
      ring

-- 读法：用函数外延性比较等号两侧在 `x' y' z'` 处的取值。
theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

-- 读法：要证明的命题是 `restrict (fun x' x => if x = x' then 1 else 0) (fun y' y => if y = y' then 1 else 0) (fun z' z => if z = z' then 1 else 0) T = T`。
theorem restrict_identity [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    restrict (fun x' x => if x = x' then 1 else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T = T := by
  calc
    _ = pullback id id id T := (pullback_eq_restrict id id id T).symm
    _ = T := rfl

end Algebra

section ComplexTopology

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [Fintype X''] [Fintype Y''] [Fintype Z'']

-- 读法：要证明的命题是 `DegeneratesTo T (restrict A B C T)`。使用 `subset_closure` 给出的结论。
theorem degeneratesTo_restrict (T : Tensor ℂ X Y Z)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    DegeneratesTo T (restrict A B C T) :=
  subset_closure ⟨A, B, C, rfl⟩

-- 读法：要证明的命题是 `DegeneratesTo T T`。
theorem DegeneratesTo.refl (T : Tensor ℂ X Y Z) : DegeneratesTo T T := by
  classical
  have h := degeneratesTo_restrict T
    (fun x' x => if x = x' then 1 else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)
  simpa only [restrict_identity] using h

omit [Fintype X''] [Fintype Y''] [Fintype Z''] in
-- 读法：`restrict D E F U` 属于 `restrictionOrbit T`。
theorem mem_restrictionOrbit_restrict {T : Tensor ℂ X Y Z}
    {U : Tensor ℂ X' Y' Z'} (h : U ∈ restrictionOrbit T)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    restrict D E F U ∈ restrictionOrbit T := by
  rcases h with ⟨A, B, C, rfl⟩
  exact ⟨composeRestrictionMatrix D A, composeRestrictionMatrix E B,
    composeRestrictionMatrix F C, restrict_restrict A B C D E F T⟩

-- 读法：要证明的命题是 `DegeneratesTo T (Tensor.restrict D E F U)`。这里调用 `subset_closure`。
theorem DegeneratesTo.restrict {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : DegeneratesTo T U)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    DegeneratesTo T (Tensor.restrict D E F U) := by
  have hclosed : IsClosed {S : Tensor ℂ X' Y' Z' |
      DegeneratesTo T (Tensor.restrict D E F S)} :=
    isClosed_closure.preimage (continuous_restrict D E F)
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | DegeneratesTo T (Tensor.restrict D E F S)} := by
    intro S hS
    exact subset_closure (mem_restrictionOrbit_restrict hS D E F)
  exact closure_minimal hsubset hclosed h

-- 读法：要证明的命题是 `DegeneratesTo T V`。这里调用 `hTU.restrict`。
theorem DegeneratesTo.trans {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    {V : Tensor ℂ X'' Y'' Z''} (hTU : DegeneratesTo T U)
    (hUV : DegeneratesTo U V) : DegeneratesTo T V := by
  have hsubset : restrictionOrbit U ⊆
      {S : Tensor ℂ X'' Y'' Z'' | DegeneratesTo T S} := by
    rintro S ⟨D, E, F, rfl⟩
    exact hTU.restrict D E F
  exact closure_minimal hsubset isClosed_closure hUV

-- 读法：要证明的命题是 `DegeneratesTo T V`。通过传递性衔接 `degeneratesTo_restrict` 与 `h`。
theorem DegeneratesTo.of_restrict {T : Tensor ℂ X Y Z} {V : Tensor ℂ X'' Y'' Z''}
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ)
    (h : DegeneratesTo (Tensor.restrict A B C T) V) : DegeneratesTo T V :=
  (degeneratesTo_restrict T A B C).trans h

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end OAI
