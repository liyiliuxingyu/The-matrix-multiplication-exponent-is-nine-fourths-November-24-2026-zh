-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.TableMotion

/-!
# 具有确定能量的融合项

候选项数关于截断阶数至多按多项式增长。对一个选定的块作分割时，每个候选项都可经由单个中间能量空间分解。

**英文原文**

Fusion terms of definite energy

The candidate count depends polynomially on the truncation order.
Each candidate separates across a chosen block through a single
intermediate energy space.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset
open scoped Classical

variable {A F R : Type*} [Fintype A] [Field F] [CommRing R] [Algebra F R] {r n : ℕ}

-- 读法：在后续公式中，`Pattern` 是 `Fin n → Fin (N + 1)` 的缩写。
abbrev Pattern (n N : ℕ) := Fin n → Fin (N + 1)

-- 读法：`regroup` 的结果类型为 `(Σ t : Pattern n N, States r (fun i => (t i).val)) ≃ (Fin n → LevelLE r N)`。
private def regroup (r n N : ℕ) :
    (Σ t : Pattern n N, States r (fun i => (t i).val)) ≃ (Fin n → LevelLE r N) := by
  let f (z : Σ t : Pattern n N, States r (fun i => (t i).val)) (j : Fin n) : LevelLE r N :=
    ⟨(z.2 j).val, (z.2 j).2.le.trans (Nat.le_of_lt_succ (z.1 j).isLt)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨s, y⟩ h
    have he (j) : (x j).val = (y j).val := congrArg Subtype.val (congrFun h j)
    have hts : t = s := by
      funext j
      apply Fin.ext
      exact (x j).2.symm.trans ((congrArg (fun w : Wedge r => energy w.val) (he j)).trans (y j).2)
    subst s
    have : x = y := funext fun j => Subtype.ext (he j)
    rw [this]
  · intro y
    let t (j : Fin n) : Fin (N + 1) := ⟨energy (y j).val.val, Nat.lt_succ_of_le (y j).2⟩
    exact ⟨⟨t, fun j => ⟨(y j).val, rfl⟩⟩, rfl⟩

-- 读法：`outerForm` 的取值由 `wick fieldKernel (List.ofFn (fun j => (b j).val.val.map (c j, ·))).flatten` 给出。
def outerForm (c : Fin n → F) {g : Fin n → ℕ} (b : States r g) : F :=
  wick fieldKernel (List.ofFn (fun j => (b j).val.val.map (c j, ·))).flatten

-- 读法：`fusedTerm` 的取值由 `∑ b : States r g, (∏ j, blockCoeff (blockInputs f o x j) (b j).val) * outerForm c b` 给出。
def fusedTerm {e : A → ℕ} (c : Fin n → F) (f : A → Fin n) (o : A → F) (g : Fin n → ℕ)
    (x : States r e) : F :=
  ∑ b : States r g, (∏ j, blockCoeff (blockInputs f o x j) (b j).val) * outerForm c b

-- 读法：结论为 `∃ s : F, ∀ x : States r e, wick (clusterKernel u N (c ∘ f) o) (inputs x) = ∑ t : Pattern n N, u ^ (∑ j, (t j).val) * algebraMap F R (s * fusedTerm c f o (fun j => (t j).val) x)`。
theorem fusion_terms {e : A → ℕ} (c : Fin n → F) (hc : Function.Injective c)
    (f : A → Fin n) (o : A → F) (u : R) (N : ℕ) (hu : u ^ N = 0) :
    ∃ s : F, ∀ x : States r e, wick (clusterKernel u N (c ∘ f) o) (inputs x) =
      ∑ t : Pattern n N, u ^ (∑ j, (t j).val) *
        algebraMap F R (s * fusedTerm c f o (fun j => (t j).val) x) := by
  obtain ⟨s, hs⟩ := grouped_fusion (r := r) (e := e) c hc f o u N hu
  refine ⟨s, fun x => ?_⟩
  rw [hs, ← (regroup r n N).sum_comp, Fintype.sum_sigma, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp only [fusedTerm, mul_sum, map_sum, map_mul]
  refine sum_congr rfl fun b _ => ?_
  have hh (j : Fin n) : ((regroup r n N ⟨t, b⟩) j).val = (b j).val := rfl
  simp only [hh, outerForm, show ∀ j, energy (b j).val.val = (t j).val from fun j => (b j).2]
  ring

-- 读法：结论为 `∃ L R : Level r (g j) → States r e → F, (∀ x, fusedTerm c f o g x = ∑ t, L t x * R t x) ∧ (∀ t x y, (∀ i, f i = j → x i = y i) → L t x = L t y) ∧ (∀ t x y, (∀ i, f i ≠ j → x i = y i) → R t x = R t y)`。
theorem fused_separates {e : A → ℕ} (c : Fin n → F)
    (f : A → Fin n) (o : A → F) (g : Fin n → ℕ) (j : Fin n) :
    ∃ L R : Level r (g j) → States r e → F,
      (∀ x, fusedTerm c f o g x = ∑ t, L t x * R t x) ∧
      (∀ t x y, (∀ i, f i = j → x i = y i) → L t x = L t y) ∧
      (∀ t x y, (∀ i, f i ≠ j → x i = y i) → R t x = R t y) := by
  let fac (i : Fin n) (w : Level r (g i)) (x : States r e) := blockCoeff (blockInputs f o x i) w.val
  let rest (b : States r g) (x : States r e) :=
    (∏ i ∈ univ.erase j, fac i (b i) x) * outerForm c b
  refine ⟨fac j, fun t x => ∑ b with b j = t, rest b x, ?_, ?_, ?_⟩
  · intro x
    rw [fusedTerm, ← sum_fiberwise univ (fun b : States r g => b j)]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b hb => ?_
    rw [← (mem_filter.mp hb).2, ← mul_prod_erase _ _ (mem_univ j), mul_assoc]
  · intro t x y h
    unfold fac
    rw [blockInputs_eq f o x y j h]
  · intro t x y h
    refine sum_congr rfl fun b _ => ?_
    unfold rest
    congr 1
    refine prod_congr rfl fun i hi => ?_
    unfold fac
    rw [blockInputs_eq f o x y i (fun a ha => h a (ha ▸ (mem_erase.mp hi).1))]

end OAI.LinearAlgebra.MatrixExponent.Sphere
