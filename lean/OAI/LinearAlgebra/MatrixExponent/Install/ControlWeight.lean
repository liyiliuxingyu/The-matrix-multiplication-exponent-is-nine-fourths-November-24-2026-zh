-- 本文件所属证明环节：把带名称的比特、局部权重、控制位与分批请求安装到共同网络中，对隐藏位求和并证明合成后仍给出规定的收缩值及成本。
import OAI.LinearAlgebra.MatrixExponent.Install.Products

/-!
# 用固定位数的控制比特选择网络

对每个控制字取一个因子并相乘。对非活动因子，在某个固定非零表项处求值，再除以该项。若表恒为零，只需检验控制比特。

**英文原文**

Selecting a network by a fixed number of control bits

Multiply one factor per control word. Inactive factors evaluate at a
fixed nonzero entry and divide by that entry. An identically zero table
only needs to test the control bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Install.Weight

open Classical

variable {K R I : Type} [Field K] [Fintype R] [Fintype I] {m : ℕ}

-- 读法：`switchCost` 的取值由 `r + 1 + 2 ^ r * (14 * (r + 1) + localCost (r + 1) + 8 * 2 ^ r + 1)` 给出。
def switchCost (r : ℕ) : ℕ := r + 1 + 2 ^ r * (14 * (r + 1) + localCost (r + 1) + 8 * 2 ^ r + 1)

-- 读法：按 `∀ x, f x = 0` 成立与否分情况。
private theorem activated (f : (I → Bool) → K) (hf : Weight K f m) (r : R → Bool) :
    Weight K (fun x : R ⊕ I → Bool => if x ∘ Sum.inl = r then f (x ∘ Sum.inr) else 1)
      (9 * Fintype.card (R ⊕ I) + localCost (Fintype.card R + 1) * Fintype.card I +
        8 * 2 ^ Fintype.card R + m) := by
  by_cases hz : ∀ x, f x = 0
  · simp only [hz]
    apply ((dense K R (fun y => if y = r then 0 else 1)).pull (Sum.inl : R → R ⊕ I)).mono
    rw [Fintype.card_sum]
    omega
  obtain ⟨x₀, h₀⟩ := not_forall.mp hz
  let g (x : R ⊕ I → Bool) := if x ∘ Sum.inl = r then x ∘ Sum.inr else x₀
  have hg : Depends g (Fintype.card R + 1) := by
    intro i
    let S := Finset.univ.image (Sum.inl : R → R ⊕ I)
    refine ⟨insert (.inr i) S, (Finset.card_insert_le ..).trans ?_, fun x y he => ?_⟩
    · exact Nat.add_le_add_right Finset.card_image_le 1
    -- 推导：记下中间结论 `h`：`x ∘ Sum.inl = y ∘ Sum.inl`。
    · have h : x ∘ Sum.inl = y ∘ Sum.inl := funext fun j =>
        he _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      simp only [g, ite_apply, h, Function.comp_apply, he _ (Finset.mem_insert_self ..)]
  let k (y : R → Bool) := if y = r then 1 else (f x₀)⁻¹
  have hk := (dense K R k).pull (Sum.inl : R → R ⊕ I)
  have he (x : R ⊕ I → Bool) : (f ∘ g) x * k (x ∘ Sum.inl) =
      if x ∘ Sum.inl = r then f (x ∘ Sum.inr) else 1 := by
    by_cases h : x ∘ Sum.inl = r <;> simp [g, k, h, h₀]
  have hp := ((hg.bnet K).weight hf).mul hk
  simp only [he] at hp
  apply hp.mono
  rw [Fintype.card_sum]
  omega

-- 读法：要证明的命题是 `Weight K (fun x : R ⊕ I → Bool => f (x ∘ Sum.inl) (x ∘ Sum.inr)) (switchCost (Fintype.card R) * (Fintype.card I + m + 1))`。这里调用 `h.mono`。
/-- 当控制比特的数量固定时，成本随载荷宽度与最大分支成本线性增长。

英文原文：The cost is linear in the payload width and the largest branch cost
when the number of control bits is fixed.
-/
theorem switch (f : (R → Bool) → (I → Bool) → K) (hf : ∀ r, Weight K (f r) m) :
    Weight K (fun x : R ⊕ I → Bool => f (x ∘ Sum.inl) (x ∘ Sum.inr))
      (switchCost (Fintype.card R) * (Fintype.card I + m + 1)) := by
  have h := finite_product _ (fun r => activated (f r) (hf r) r)
  simp only [Finset.prod_ite_eq, Finset.mem_univ, ite_true] at h
  apply h.mono
  simp only [switchCost, Fintype.card_sum, Fintype.card_fun, Fintype.card_bool]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Install.Weight
