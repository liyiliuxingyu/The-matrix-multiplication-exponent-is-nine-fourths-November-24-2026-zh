-- 本文件所属证明环节：给不同处理器和独立副本分配地址、切口、信道和广播资源，把虚拟连线送上实际网络，控制由固定模板带来的额外开销。
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Physical

/-!
# 重新连接处理器输入

处于同一输入位置的各副本具有相同的标签。因此，一个广播比特或物理比特的所有出现位置都归于同一工作处理器。只有字面量比特可能需要额外通信。

**英文原文**

Reconnecting processor inputs

Copies at the same input position have the same label. Consequently
all occurrences of a broadcast or physical bit are colocated at a
single worker. Only literal bits may require additional communication.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

-- 读法：在后续公式中，`Pin` 是 `(Fin (3 * r) × Fin l) ⊕ Fin b ⊕ Links.Slot (3 * r) N` 的缩写。
abbrev Pin (N l b r : ℕ) := (Fin (3 * r) × Fin l) ⊕ Fin b ⊕ Links.Slot (3 * r) N

namespace Pin

variable {N l b r : ℕ}

-- 读法：逐一匹配以下输入模式：`.inl (_, i)`、`.inr (.inl i)`、`.inr (.inr i)`。
def position : Pin N l b r → Fin l ⊕ Fin b ⊕ Fin (N / 4)
  | .inl (_, i) => .inl i
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr i) => .inr (.inr (Links.address i))

-- 读法：`literal` 的取值由 `y (.inl (u, i))` 给出。
def literal (y : Pin N l b r → Bool) (u : Fin (3 * r)) (i : Fin l) := y (.inl (u, i))

-- 读法：`broadcast` 的取值由 `y (.inr (.inl i))` 给出。
def broadcast (y : Pin N l b r → Bool) (i : Fin b) := y (.inr (.inl i))

-- 读法：`link` 的取值由 `y (.inr (.inr i))` 给出。
def link (y : Pin N l b r → Bool) (i : Links.Slot (3 * r) N) := y (.inr (.inr i))

variable (f : Fin l ⊕ Fin b ⊕ Fin (N / 4) → Worker r)

-- 读法：`dst` 的取值由 `f e.position` 给出。
def dst (e : Pin N l b r) : Worker r := f e.position

-- 读法：`src` 的取值由 `match e with | .inl (u, _) => (Worker.index r).symm u | .inr _ => dst f e` 给出。
def src (e : Pin N l b r) : Worker r :=
  match e with
  | .inl (u, _) => (Worker.index r).symm u
  | .inr _ => dst f e

end Pin
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 对字面输入比特的各副本求和

**英文原文**

Summing over copies of the literal bits
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin

open Finset
variable {F : Type} [Field F] {N l b r : ℕ}

-- 读法：当 `literal y (Worker.index r u) = s` 成立时取 `1`，否则取 `0`。
/-- 每个工作处理器只施加自身的字面量约束，无须知道提供给其他处理器的程序或接线信息。

英文原文：Each worker imposes only its own literal, without knowing the
program or wiring information provided to any other processor.
-/
def mask (F : Type) [Field F] (u : Worker r) (s : Fin l → Bool) (y : Pin N l b r → Bool) : F :=
  if literal y (Worker.index r u) = s then 1 else 0

-- 读法：`mask F u s y` 等于 `mask F u s z`。
theorem mask_local (u : Worker r) (s : Fin l → Bool) (y z : Pin N l b r → Bool)
    (f : Fin l ⊕ Fin b ⊕ Fin (N / 4) → Worker r) (he : ∀ e, src f e = u → y e = z e) :
    mask F u s y = mask F u s z := by
  have h : literal y (Worker.index r u) = literal z (Worker.index r u) :=
    funext (fun i => he (.inl (Worker.index r u, i)) ((Worker.index r).symm_apply_apply u))
  rw [mask, mask, h]

-- 读法：`(∏ u, mask F u (ξ (Worker.index r u)) y)` 等于 `if literal y = ξ then 1 else 0`。按 `literal y = ξ` 成立与否分情况。
private theorem masks (ξ : Fin (3 * r) → Fin l → Bool) (y : Pin N l b r → Bool) :
    (∏ u, mask F u (ξ (Worker.index r u)) y) = if literal y = ξ then 1 else 0 := by
  by_cases h : literal y = ξ
  · simp [mask, h]
  · rw [ite_eq_right h]
    obtain ⟨u, hu⟩ := Function.ne_iff.mp h
    refine prod_eq_zero (mem_univ ((Worker.index r).symm u)) ?_
    simp [mask, hu]

-- 读法：`coordinates` 的取值由 `(Equiv.sumPiEquivProdPi (fun _ => Bool)).trans ((Equiv.curry _ _ _).prodCongr (Equiv.sumPiEquivProdPi (fun _ => Bool)))` 给出。
private def coordinates (N l b r : ℕ) :
    (Pin N l b r → Bool) ≃ (Fin (3 * r) → Fin l → Bool) × (Fin b → Bool) × (Links.Slot (3 * r) N → Bool) :=
  (Equiv.sumPiEquivProdPi (fun _ => Bool)).trans
    ((Equiv.curry _ _ _).prodCongr (Equiv.sumPiEquivProdPi (fun _ => Bool)))

-- 读法：结论为 `(∑ y : Pin N l b r → Bool, (∏ u, mask F u (ξ (Worker.index r u)) y) * g (literal y) (broadcast y) (link y)) = ∑ z, ∑ t, g ξ z t`。
theorem sum_masks (ξ : Fin (3 * r) → Fin l → Bool)
    (g : (Fin (3 * r) → Fin l → Bool) → (Fin b → Bool) → (Links.Slot (3 * r) N → Bool) → F) :
    (∑ y : Pin N l b r → Bool, (∏ u, mask F u (ξ (Worker.index r u)) y) *
      g (literal y) (broadcast y) (link y)) = ∑ z, ∑ t, g ξ z t := by
  simp only [masks]
  rw [← (coordinates N l b r).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ a, ∑ x : (Fin b → Bool) × (Links.Slot (3 * r) N → Bool),
    (if a = ξ then (1 : F) else 0) * g a x.1 x.2) = _
  rw [sum_comm]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  rw [Fintype.sum_prod_type]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin
end
