-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import OAI.LinearAlgebra.MatrixExponent.Prices.Tensor
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# 在一个新增站点上同步一个多项式参数

**英文原文**

Synchronizing one polynomial parameter at a single new site
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices
open Spectral

variable {F S : Type} [Field F] [Fintype S] [Nonempty S]

-- 读法：`evalFamily` 的取值由 `Tensor.ofRaw (Raw.ofTable X (fun b => (P b).eval z))` 给出。
def evalFamily (X : S → Type) [∀ s, Fintype (X s)]
    (P : (∀ s, X s) → Polynomial F) (z : F) : Tensor F S :=
  Tensor.ofRaw (Raw.ofTable X (fun b => (P b).eval z))

-- 读法：`SharedPrice` 的结果类型为 `Prop`。
/-- 对每个有限乘积，在给定有限例外集外选取一个各因子共用的参数进行检验。必须由同一个普通延拓同时满足所有上界。

英文原文：Every finite product is tested at a common parameter outside the given
finite exceptional set. A single ordinary extension must satisfy all the
bounds at once.
-/
def SharedPrice (F : Type) [Field F] : Prop :=
  ∀ (S I : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (f : Tensor F S →+* ℝ), Monotone f →
    ∀ (B : Finset F) (X : I → S ⊕ Unit → Type) [∀ i s, Fintype (X i s)]
      (P : ∀ i, (∀ s, X i s) → Polynomial F) (p : I → ℝ),
      (∀ s ∉ B, ∀ w : List I, ∀ T, Tensor.pad Unit T ≤
        (w.map (fun i => evalFamily (X i) (P i) s)).prod → f T ≤ (w.map p).prod) →
      ∃ g : Tensor F (S ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
        (∀ i s, s ∉ B → g (evalFamily (X i) (P i) s) ≤ p i)

-- 读法：`Synchronization` 的结果类型为 `Prop`。
/-- 所有同步辅助成本的统一上界也是独立选取各参数时的成本上界。

英文原文：A bound for all synchronized assisted costs also bounds the cost with
independently chosen parameters.
-/
def Synchronization (F : Type) [Field F] : Prop :=
  ∀ (S I : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (f : Tensor F S →+* ℝ), Monotone f →
    ∀ (B : Finset F) (X : I → S ⊕ Unit → Type) [∀ i s, Fintype (X i s)]
      (P : ∀ i, (∀ s, X i s) → Polynomial F)
      (w : List (I × {z // z ∉ B})) (r : ℝ),
      (∀ s ∉ B, Tensor.assisted f (w.map (fun i => evalFamily (X i.1) (P i.1) s)).prod ≤ r) →
      Tensor.assisted f (w.map (fun i => evalFamily (X i.1) (P i.1) i.2)).prod ≤ r

-- 读法：要证明的命题是 `SharedPrice F`。
theorem Synchronization.sharedPrice (hs : Synchronization F) : SharedPrice F := by
  intro S I _ _ _ f hf B X _ P p h
  let ev i z := evalFamily (X i) (P i) z
  have ht (z : F) (hz : z ∉ B) : ∀ w : List I,
      Tensor.assisted f (w.map (fun i => ev i z)).prod ≤ (w.map p).prod :=
    (Tensor.assisted_extension_iff f hf _ p).mp ((Tensor.extension_iff f hf _ p).mpr (h z hz))
  let J := I × {z // z ∉ B}
  let E (i : J) := ev i.1 i.2
  obtain ⟨g, hg, he, ha⟩ := (Tensor.assisted_extension_iff f hf E (fun i => p i.1)).mpr
    (fun w => hs S I f hf B X P w _ fun z hz => by
      simpa only [List.map_map, Function.comp_def] using ht z hz (w.map Prod.fst))
  exact ⟨g, hg, he, fun i z hz => ha (i, ⟨z, hz⟩)⟩

end OAI.LinearAlgebra.MatrixExponent.Prices
