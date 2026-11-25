-- 本文件所属证明环节：在带赋值的扩张中延拓和比较价格，研究参数变化时的连续性与共享价格；共享价格条件的失败给出方阵等式和矩形刚性。
import OAI.LinearAlgebra.MatrixExponent.Valued.Restriction
import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import OAI.LinearAlgebra.MatrixExponent.Prices.Padding
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Prices.Tensor

/-!
# 整限制半环

**英文原文**

The integral restriction semiring
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

section
variable {K S : Type} [Field K] [Fintype S] {O : Subring K} (A B C : Raw K S)

-- 读法：要证明的命题是 `(equiv O).r (A + B) (B + A)`。
private theorem comm_add : (equiv O).r (A + B) (B + A) := by
  refine relabel (Equiv.sumComm _ _) (fun _ => Equiv.sumComm _ _) ?_
  rintro (i | i) s (x | x) <;> rfl

-- 读法：要证明的命题是 `(equiv O).r ((A + B) + C) (A + (B + C))`。
private theorem assoc_add : (equiv O).r ((A + B) + C) (A + (B + C)) := by
  refine relabel (Equiv.sumAssoc _ _ _) (fun _ => Equiv.sumAssoc _ _ _) ?_
  rintro ((i | i) | i) s ((x | x) | x) <;> rfl

-- 读法：要证明的命题是 `(equiv O).r (0 + A) (A)`。这里调用 `i.elim`。
private theorem nil_add : (equiv O).r (0 + A) (A) := by
  refine relabel (Equiv.emptySum Empty _) (fun _ => Equiv.emptySum Empty _) ?_
  rintro (i | i)
  · exact i.elim
  rintro s (x | x)
  · exact x.elim
  rfl

-- 读法：要证明的命题是 `(equiv O).r (A * B) (B * A)`。这里调用 `mul_comm`。
private theorem comm_mul : (equiv O).r (A * B) (B * A) := by
  refine relabel (Equiv.prodComm _ _) (fun _ => Equiv.prodComm _ _) ?_
  intro i s x
  exact mul_comm _ _

-- 读法：要证明的命题是 `(equiv O).r ((A * B) * C) (A * (B * C))`。这里调用 `mul_assoc`。
private theorem assoc_mul : (equiv O).r ((A * B) * C) (A * (B * C)) := by
  refine relabel (Equiv.prodAssoc _ _ _) (fun _ => Equiv.prodAssoc _ _ _) ?_
  intro i s x
  exact mul_assoc _ _ _

-- 读法：要证明的命题是 `(equiv O).r (1 * A) (A)`。这里调用 `one_mul`。
private theorem unit_mul : (equiv O).r (1 * A) (A) := by
  refine relabel (Equiv.punitProd _) (fun _ => Equiv.punitProd _) ?_
  intro i s x
  exact one_mul _

-- 读法：要证明的命题是 `(equiv O).r (0 * A) (0)`。这里调用 `i.1.elim`。
private theorem nil_mul : (equiv O).r (0 * A) (0) := by
  refine relabel (Equiv.emptyProd _) (fun _ => Equiv.emptyProd _) ?_
  intro i
  exact i.1.elim

-- 读法：要证明的命题是 `(equiv O).r (A * (B + C)) (A * B + A * C)`。这里调用 `mul_zero`。
private theorem distrib_left : (equiv O).r (A * (B + C)) (A * B + A * C) := by
  refine relabel (Equiv.prodSumDistrib _ _ _) (fun _ => Equiv.prodSumDistrib _ _ _) ?_
  rintro ⟨i, j | j⟩ s ⟨x, y | y⟩
  · rfl
  · exact mul_zero _
  · exact mul_zero _
  · rfl

end

-- 读法：`ITensor` 的取值由 `Quotient (equiv O (S := S))` 给出。
/-- 按可相互局部线性限制的等价关系，对系数张量取商。

英文原文：Coefficient tensors modulo mutual local linear restriction.
-/
def ITensor {K : Type} [Field K] (O : Subring K) (S : Type) [Fintype S] :=
  Quotient (equiv O (S := S))

namespace ITensor

variable {K S : Type} [Field K] [Fintype S] {O : Subring K}

-- 读法：`ofRaw` 的取值由 `Quotient.mk _ A` 给出。
def ofRaw (A : Raw K S) : ITensor O S := Quotient.mk _ A

-- 读法：`ofRaw (O := O) A` 等于 `ofRaw B`。使用 `Quotient.sound` 给出的结论。
theorem ofRaw_eq {A B : Raw K S} (h : (equiv O).r A B) : ofRaw (O := O) A = ofRaw B :=
  Quotient.sound h

-- 读法：为 `LE (ITensor O S)` 构造类型类实例。
instance : LE (ITensor O S) :=
  ⟨Quotient.lift₂ (fun a b => Restricts O b a) fun _ _ _ _ h g => propext
    ⟨fun t => g.2.trans (t.trans h.1), fun t => g.1.trans (t.trans h.2)⟩⟩

-- 读法：`ofRaw (O := O) A ≤ ofRaw B` 与 `Restricts O B A` 等价。使用 `Iff.rfl` 给出的结论。
theorem ofRaw_le (A B : Raw K S) : ofRaw (O := O) A ≤ ofRaw B ↔ Restricts O B A := Iff.rfl

-- 读法：用字段 `le`、`le_refl`、`le_trans`、`le_antisymm` 构造 `PartialOrder (ITensor O S)`。
instance : PartialOrder (ITensor O S) where
  le := (· ≤ ·)
  le_refl A := Quotient.inductionOn A (fun a => Restricts.refl a)
  le_trans A B C := Quotient.inductionOn₃ A B C fun _ _ _ h g => Restricts.trans g h
  le_antisymm A B := Quotient.inductionOn₂ A B fun _ _ h g => Quotient.sound ⟨g, h⟩

-- 读法：`Zero (ITensor O S)` 的取值由 `⟨ofRaw 0⟩` 给出。
instance : Zero (ITensor O S) := ⟨ofRaw 0⟩
-- 读法：`One (ITensor O S)` 的取值由 `⟨ofRaw 1⟩` 给出。
instance : One (ITensor O S) := ⟨ofRaw 1⟩

-- 读法：`Add (ITensor O S)` 的取值由 `⟨Quotient.map₂ (· + ·) fun _ _ h _ _ g => ⟨h.1.add g.1, h.2.add g.2⟩⟩` 给出。
instance : Add (ITensor O S) :=
  ⟨Quotient.map₂ (· + ·) fun _ _ h _ _ g => ⟨h.1.add g.1, h.2.add g.2⟩⟩

-- 读法：`Mul (ITensor O S)` 的取值由 `⟨Quotient.map₂ (· * ·) fun _ _ h _ _ g => ⟨h.1.mul g.1, h.2.mul g.2⟩⟩` 给出。
instance : Mul (ITensor O S) :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h _ _ g => ⟨h.1.mul g.1, h.2.mul g.2⟩⟩

-- 读法：`ofRaw (O := O) (A + B)` 等于 `ofRaw A + ofRaw B`。两端由定义化简为同一项。
theorem ofRaw_add (A B : Raw K S) : ofRaw (O := O) (A + B) = ofRaw A + ofRaw B := rfl
-- 读法：`ofRaw (O := O) (A * B)` 等于 `ofRaw A * ofRaw B`。两端由定义化简为同一项。
theorem ofRaw_mul (A B : Raw K S) : ofRaw (O := O) (A * B) = ofRaw A * ofRaw B := rfl

-- 读法：`A + B` 等于 `B + A`。使用 `Quotient.inductionOn₂` 给出的结论。
private theorem comm_add (A B : ITensor O S) : A + B = B + A :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Valued.comm_add a b)

-- 读法：`A * B` 等于 `B * A`。使用 `Quotient.inductionOn₂` 给出的结论。
private theorem comm_mul (A B : ITensor O S) : A * B = B * A :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Valued.comm_mul a b)

-- 读法：`A * (B + C)` 等于 `A * B + A * C`。使用 `Quotient.inductionOn₃` 给出的结论。
private theorem distrib_left (A B C : ITensor O S) : A * (B + C) = A * B + A * C :=
  Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Valued.distrib_left a b c)

-- 读法：用字段 `add`、`mul`、`zero`、`one` 构造 `CommSemiring (ITensor O S)`。
instance : CommSemiring (ITensor O S) where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  nsmul := nsmulRec
  add_assoc A B C := Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Valued.assoc_add a b c)
  add_comm := comm_add
  zero_add A := Quotient.inductionOn A fun a => ofRaw_eq (Valued.nil_add a)
  add_zero A := (comm_add A 0).trans (Quotient.inductionOn A fun a => ofRaw_eq (Valued.nil_add a))
  mul_assoc A B C := Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Valued.assoc_mul a b c)
  mul_comm := comm_mul
  one_mul A := Quotient.inductionOn A fun a => ofRaw_eq (Valued.unit_mul a)
  mul_one A := (comm_mul A 1).trans (Quotient.inductionOn A fun a => ofRaw_eq (Valued.unit_mul a))
  zero_mul A := Quotient.inductionOn A fun a => ofRaw_eq (Valued.nil_mul a)
  mul_zero A := (comm_mul A 0).trans (Quotient.inductionOn A fun a => ofRaw_eq (Valued.nil_mul a))
  left_distrib := distrib_left
  right_distrib A B C := by rw [comm_mul, distrib_left, comm_mul C A, comm_mul C B]

-- 读法：由 `A ≤ B` 推出 `A + C ≤ B + C`。使用 `Quotient.inductionOn₃` 给出的结论。
theorem add_le_add_right (A B C : ITensor O S) : A ≤ B → A + C ≤ B + C :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Restricts.add h (.refl c)

-- 读法：由 `A ≤ B` 推出 `C * A ≤ C * B`。使用 `Quotient.inductionOn₃` 给出的结论。
theorem mul_le_mul_left (A B C : ITensor O S) : A ≤ B → C * A ≤ C * B :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Restricts.mul (.refl c) h

end ITensor
end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# 到填充张量的整限制

**英文原文**

Integral restrictions to a padded tensor
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Raw

variable {K S U : Type} [Field K] [Fintype S] [Fintype U] [Nonempty S] {O : Subring K}

-- 读法：`Integral` 表示以下条件：对每个 `u y`，`v u y` 属于 `O`。
def Integral {A : Raw K (S ⊕ U)} (O : Subring K) (v : A.Covectors) : Prop :=
  ∀ u y, v u y ∈ O

-- 读法：`Restricts O A (pad U B)` 与 `∃ v : A.Covectors, Integral O v ∧ Restricts O (A.close v) B` 等价。
theorem restricts_pad (A : Raw K (S ⊕ U)) (B : Raw K S) :
    Restricts O A (pad U B) ↔ ∃ v : A.Covectors, Integral O v ∧ Restricts O (A.close v) B := by
  constructor
  · rintro ⟨L, hl, h⟩
    let v : A.Covectors := fun u => L (.inr u) ()
    refine ⟨v, fun u y => hl _ _ _, fun s => L (.inl s), fun s => hl (.inl s), fun x => ?_⟩
    let x' : ∀ s, (pad U B).leg s := Sum.rec x (fun _ => ())
    refine Eq.trans ?_ (close_action A v (fun s => L (.inl s) (x s))).symm
    have hx := h x'
    rw [pad_coeff] at hx
    simp only [Fintype.prod_sum_type] at hx
    exact hx
  · rintro ⟨v, hv, L, hl, h⟩
    refine ⟨Sum.rec L (fun u _ => v u), ?_, fun x => ?_⟩
    · rintro (s | u) x y
      · exact hl s x y
      · exact hv u y
    · refine (pad_coeff B x).trans ((h _).trans ((close_action A v
        (fun s => L s (x (.inl s)))).trans ?_))
      simp only [Fintype.prod_sum_type]
      rfl

-- 读法：`Restricts O (pad U A) (pad U B)` 与 `Restricts O A B` 等价。
theorem pad_restricts (A B : Raw K S) :
    Restricts O (pad U A) (pad U B) ↔ Restricts O A B := by
  classical
  rw [restricts_pad]
  constructor
  · rintro ⟨v, hv, h⟩
    suffices Restricts O A ((pad U A).close v) from this.trans h
    refine ⟨fun s x y => if y = x then weight (∏ u, v u ()) s else 0, ?_, fun x => ?_⟩
    · intro s x y
      have H : (∏ u, v u ()) ∈ O := O.prod_mem fun u _ => hv u ()
      dsimp only [weight]
      split_ifs <;> simp [H]
    · change (∀ s, A.leg s) at x
      change (∑ i : A.term, ∏ s, A.factor i s (x s) * weight ((pad U A).scalar v i) s) = _
      simp [pad_scalar, mul_comm]
  · intro h
    let v : (pad U A).Covectors := fun _ _ => 1
    have he : (equiv O).r ((pad U A).close v) A := by
      refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
      change A.term at i
      change A.factor i s x * weight ((pad U A).scalar v i) s = A.factor i s x
      simp [pad_scalar, weight, v]
    exact ⟨v, fun _ _ => O.one_mem, he.1.trans h⟩

-- 读法：要证明的命题是 `(equiv O).r ((A + B).close v) (A.close (fun u x => v u (.inl x)) + B.close (fun u x => v u (.inr x)))`。这里调用 `Finset.prod_congr`。
theorem close_add (A B : Raw K (S ⊕ U)) (v : (A + B).Covectors) :
    (equiv O).r ((A + B).close v)
      (A.close (fun u x => v u (.inl x)) + B.close (fun u x => v u (.inr x))) := by
  have hl (i : A.term) :
      (A + B).scalar v (.inl i) = A.scalar (fun u x => v u (.inl x)) i := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ y : A.leg (.inr u) ⊕ B.leg (.inr u),
      v u y * Sum.elim (A.factor i (.inr u)) (fun _ => 0) y) = _
    simp [Fintype.sum_sum_type]
  have hr (i : B.term) :
      (A + B).scalar v (.inr i) = B.scalar (fun u x => v u (.inr x)) i := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ y : A.leg (.inr u) ⊕ B.leg (.inr u),
      v u y * Sum.elim (fun _ => 0) (B.factor i (.inr u)) y) = _
    simp [Fintype.sum_sum_type]
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_
  rintro (i | i) s (x | x)
  · exact congrArg (fun a => A.factor i (.inl s) x * weight a s) (hl i)
  · exact zero_mul _
  · exact zero_mul _
  · exact congrArg (fun a => B.factor i (.inl s) x * weight a s) (hr i)

-- 读法：要证明的命题是 `(equiv O).r ((pad U A * B).close v) (A * B.close (fun u x => v u ((), x)))`。这里调用 `Finset.prod_congr`。
theorem close_mul (A : Raw K S) (B : Raw K (S ⊕ U)) (v : (pad U A * B).Covectors) :
    (equiv O).r ((pad U A * B).close v) (A * B.close (fun u x => v u ((), x))) := by
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_
  rintro ⟨i, j⟩ s ⟨x, y⟩
  have h : (pad U A * B).scalar v (i, j) = B.scalar (fun u z => v u ((), z)) j := by
    apply Finset.prod_congr rfl
    intro u _
    change (∑ z : Unit × B.leg (.inr u), v u z * (1 * B.factor j (.inr u) z.2)) = _
    simp [Fintype.sum_prod_type]
    rfl
  change A.factor i s x * B.factor j (.inl s) y * weight ((pad U A * B).scalar v (i, j)) s = _
  rw [h, mul_assoc]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# 利用整限制增添位点

**英文原文**

Adding sites using integral restrictions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Raw

variable {K S : Type} [Field K] [Fintype S] (U : Type) [Fintype U] {O : Subring K}

-- 读法：要证明的命题是 `(equiv O).r (pad U (0 : Raw K S)) 0`。
theorem pad_zero : (equiv O).r (pad U (0 : Raw K S)) 0 := by
  constructor <;>
    exact ⟨fun _ _ _ => 0, fun _ _ _ => O.zero_mem, fun _ => Finset.sum_congr rfl fun i _ => Empty.elim i⟩

-- 读法：要证明的命题是 `(equiv O).r (pad U (1 : Raw K S)) 1`。
theorem pad_one : (equiv O).r (pad U (1 : Raw K S)) 1 := by
  let e (s : S ⊕ U) : (pad U (1 : Raw K S)).leg s ≃ Unit :=
    match s with
    | .inl _ => Equiv.refl Unit
    | .inr _ => Equiv.refl Unit
  refine relabel (Equiv.refl _) e ?_
  rintro i (s | u) x <;> rfl

-- 读法：要证明的命题是 `(equiv O).r (pad U (A * B)) (pad U A * pad U B)`。这里调用 `one_mul`。
theorem pad_mul (A B : Raw K S) : (equiv O).r (pad U (A * B)) (pad U A * pad U B) := by
  let e (s : S ⊕ U) : (pad U (A * B)).leg s ≃ (pad U A * pad U B).leg s :=
    match s with
    | .inl s => Equiv.refl (A.leg s × B.leg s)
    | .inr _ => (Equiv.punitProd Unit).symm
  refine relabel (Equiv.refl _) e ?_
  rintro i (s | u) x
  · rfl
  · exact (one_mul (1 : K)).symm

-- 读法：要证明的命题是 `Restricts O (pad U A + pad U B) (pad U (A + B))`。
theorem pad_add (A B : Raw K S) : Restricts O (pad U A + pad U B) (pad U (A + B)) := by
  classical
  let L (s : S ⊕ U) : (pad U (A + B)).leg s → (pad U A + pad U B).leg s → K :=
    match s with
    | .inl s => fun (x y : A.leg s ⊕ B.leg s) => if y = x then 1 else 0
    | .inr _ => fun _ _ => 1
  refine ⟨L, ?_, fun x => Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun s _ => ?_⟩
  · rintro (s | u) x y
    · change A.leg s ⊕ B.leg s at x y
      change (if y = x then (1 : K) else 0) ∈ O
      split_ifs <;> simp
    · exact O.one_mem
  change A.term ⊕ B.term at i
  cases s with
  | inl s =>
    have key (z : A.leg s ⊕ B.leg s) (f : A.leg s ⊕ B.leg s → K) :
        f z = ∑ y, (if y = z then (1 : K) else 0) * f y := by simp [ite_mul]
    exact key (x (.inl s)) ((A + B).factor i s)
  | inr u =>
    change 1 = ∑ y : Unit ⊕ Unit, 1 * (pad U A + pad U B).factor i (.inr u) y
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, one_mul]
    cases i
    · exact (add_zero (1 : K)).symm
    · exact (zero_add (1 : K)).symm

namespace ITensor

variable [Nonempty S]

-- 读法：`pad` 的取值由 `Quotient.map (Raw.pad U) fun _ _ h => ⟨(pad_restricts _ _).mpr h.1, (pad_restricts _ _).mpr h.2⟩` 给出。
def pad : ITensor O S → ITensor O (S ⊕ U) :=
  Quotient.map (Raw.pad U) fun _ _ h =>
    ⟨(pad_restricts _ _).mpr h.1, (pad_restricts _ _).mpr h.2⟩

-- 读法：`pad U (ofRaw (O := O) A)` 等于 `ofRaw (Raw.pad U A)`。两端由定义化简为同一项。
theorem pad_ofRaw (A : Raw K S) : pad U (ofRaw (O := O) A) = ofRaw (Raw.pad U A) := rfl

-- 读法：`pad U s ≤ ofRaw A` 与 `∃ v : A.Covectors, Integral O v ∧ s ≤ ofRaw (A.close v)` 等价。使用 `Quotient.inductionOn` 给出的结论。
theorem pad_le_ofRaw_iff (s : ITensor O S) (A : Raw K (S ⊕ U)) :
    pad U s ≤ ofRaw A ↔ ∃ v : A.Covectors, Integral O v ∧ s ≤ ofRaw (A.close v) :=
  Quotient.inductionOn s fun a => restricts_pad A a

-- 读法：`pad U (ofRaw (O := O) (A.close v))` 不超过 `ofRaw A`。使用 `pad_le_ofRaw_iff` 给出的结论。
theorem pad_close_le (A : Raw K (S ⊕ U)) (v : A.Covectors) (h : Integral O v) :
    pad U (ofRaw (O := O) (A.close v)) ≤ ofRaw A :=
  (pad_le_ofRaw_iff U _ A).mpr ⟨v, h, le_rfl⟩

-- 读法：要证明的命题是 `Prices.Padding (pad (O := O) (S := S) U)`。
theorem padding : Prices.Padding (pad (O := O) (S := S) U) where
  zero := ofRaw_eq (pad_zero U)
  one := ofRaw_eq (pad_one U)
  le_iff s t := Quotient.inductionOn₂ s t fun a b => pad_restricts b a
  mul s t := Quotient.inductionOn₂ s t fun a b => ofRaw_eq (pad_mul U a b)
  add_le s t := Quotient.inductionOn₂ s t fun a b => pad_add U a b
  split {s x y} := by
    refine Quotient.inductionOn₂ x y fun A B h => ?_
    obtain ⟨v, hi, hv⟩ := (pad_le_ofRaw_iff U s (A + B)).mp h
    rw [ofRaw_eq (close_add _ _ v), ofRaw_add] at hv
    exact ⟨_, _, pad_close_le U A _ (fun t z => hi t (.inl z)),
      pad_close_le U B _ (fun t z => hi t (.inr z)), hv⟩
  factor {s a x} := by
    refine Quotient.inductionOn₂ a x fun A B h => ?_
    obtain ⟨v, hi, hv⟩ := (pad_le_ofRaw_iff U s (Raw.pad U A * B)).mp h
    rw [ofRaw_eq (close_mul _ _ v), ofRaw_mul] at hv
    exact ⟨_, pad_close_le U B _ (fun t z => hi t ((), z)), hv⟩

end ITensor
end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# 系数的整选取与标量的价格

**英文原文**

Integral selection of coefficients and the price of a scalar
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype U] {O : Subring K}

-- 读法：`0` 不超过 `A`。
theorem zero_le (A : ITensor O S) : 0 ≤ A := by
  refine Quotient.inductionOn A fun a => ?_
  exact ⟨fun _ x => x.elim, fun _ x => x.elim, fun x => (x (Classical.arbitrary S)).elim⟩

-- 读法：`ofRaw (O := O) A = 0` 与 `∀ x, A.coeff x = 0` 等价。这里调用 `Raw.zero_restricts_iff`。
theorem ofRaw_eq_zero (A : Raw K S) : ofRaw (O := O) A = 0 ↔ ∀ x, A.coeff x = 0 := by
  constructor
  · intro h
    have h' : Restricts O 0 A := h.le
    exact (Raw.zero_restricts_iff A).mp h'.forget
  · intro h
    apply le_antisymm _ (zero_le _)
    refine ⟨fun _ _ _ => 0, fun _ _ _ => O.zero_mem, fun x => ?_⟩
    exact (h x).trans (Finset.sum_eq_zero fun i _ => Empty.elim i).symm

-- 读法：`scalar` 的取值由 `ofRaw (Raw.ofTable (fun _ => Unit) (fun _ => c))` 给出。
def scalar (O : Subring K) (S : Type) [Fintype S] [Nonempty S] (c : K) : ITensor O S :=
  ofRaw (Raw.ofTable (fun _ => Unit) (fun _ => c))

-- 读法：`scalar O S 1` 等于 `1`。这里调用 `ofRaw_eq`。
theorem scalar_one : scalar O S 1 = 1 := by
  apply ofRaw_eq
  refine equiv_coeff (fun _ => Equiv.refl Unit) fun x => ?_
  erw [Raw.coeff_ofTable]
  change 1 = ∑ _ : Unit, ∏ _ : S, (1 : K)
  simp

-- 读法：`scalar O S (c * d)` 等于 `scalar O S c * scalar O S d`。这里调用 `ofRaw_eq`。
theorem scalar_mul (c d : K) : scalar O S (c * d) = scalar O S c * scalar O S d := by
  apply ofRaw_eq
  refine equiv_coeff (fun _ => (Equiv.punitProd Unit).symm) fun x => ?_
  erw [Raw.coeff_mul, Raw.coeff_ofTable, Raw.coeff_ofTable, Raw.coeff_ofTable]

-- 读法：`pad U (scalar O S c)` 等于 `scalar O (S ⊕ U) c`。这里调用 `ofRaw_eq`。
theorem pad_scalar (c : K) : pad U (scalar O S c) = scalar O (S ⊕ U) c := by
  apply ofRaw_eq
  let e (s : S ⊕ U) : (Raw.pad U (Raw.ofTable (fun _ : S => Unit) (fun _ => c))).leg s ≃ Unit :=
    match s with
    | .inl _ => Equiv.refl Unit
    | .inr _ => Equiv.refl Unit
  refine equiv_coeff e fun x => ?_
  erw [Raw.pad_coeff, Raw.coeff_ofTable, Raw.coeff_ofTable]

-- 读法：`scalar O S (A.coeff x)` 不超过 `ofRaw A`。使用 `Restricts.pullback` 给出的结论。
theorem scalar_coeff (A : Raw K S) (x : ∀ s, A.leg s) :
    scalar O S (A.coeff x) ≤ ofRaw A :=
  Restricts.pullback (fun s _ => x s) (fun y => Raw.coeff_ofTable _ _ y)

-- 读法：`0` 严格小于 `f (scalar O S c)`。这里调用 `lt_of_le_of_ne`。
theorem positive_scalar (f : ITensor O S →+* ℝ) (hf : Monotone f) (c : K) (h : c ≠ 0) :
    0 < f (scalar O S c) := by
  apply lt_of_le_of_ne
  · simpa using hf (zero_le (scalar O S c))
  intro hz
  have he := congrArg f (scalar_mul (S := S) (O := O) c c⁻¹)
  rw [mul_inv_cancel₀ h, scalar_one, map_one, map_mul, ← hz, zero_mul] at he
  exact one_ne_zero he

-- 读法：存在 `B`，`pad U B ≤ A` 与 `0 < f B` 同时成立。
theorem lower_bound (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (A : ITensor O (S ⊕ U)) (hA : A ≠ 0) : ∃ B, pad U B ≤ A ∧ 0 < f B := by
  revert hA
  refine Quotient.inductionOn A fun a ha => ?_
  obtain ⟨x, hx⟩ := not_forall.mp fun he => ha ((ofRaw_eq_zero a).mpr he)
  exact ⟨scalar O S (a.coeff x), by rw [pad_scalar]; exact scalar_coeff a x,
    positive_scalar f hf _ hx⟩

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# 用整代换作坐标展开

**英文原文**

Coordinate expansion with integral substitutions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]
  (O : Subring K) (X : S → Type) [∀ s, Fintype (X s)]

-- 读法：`table` 的取值由 `ofRaw (Raw.ofTable X f)` 给出。
def table (f : (∀ s, X s) → K) : ITensor O S := ofRaw (Raw.ofTable X f)

-- 读法：`table O A.leg A.coeff` 等于 `ofRaw A`。使用 `ofRaw_eq` 给出的结论。
theorem table_coeff (A : Raw K S) : table O A.leg A.coeff = ofRaw A :=
  ofRaw_eq (equiv_coeff (fun _ => Equiv.refl _) (Raw.coeff_ofTable _ _))

-- 读法：`table O X 0` 等于 `0`。使用 `ofRaw_eq_zero` 给出的结论。
theorem table_zero : table O X 0 = 0 :=
  (ofRaw_eq_zero _).mpr (fun x => Raw.coeff_ofTable _ _ x)

-- 读法：`table O X (f + g)` 不超过 `table O X f + table O X g`。
theorem table_add (f g : (∀ s, X s) → K) : table O X (f + g) ≤ table O X f + table O X g := by
  classical
  let P := Raw.ofTable X f
  let Q := Raw.ofTable X g
  let R := Raw.ofTable X (f + g)
  let L (s : S) (x : X s) (y : X s ⊕ X s) := if Sum.elim id id y = x then (1 : K) else 0
  refine ⟨L, ?_, fun x => ?_⟩
  · intro s x y
    change X s at x
    change X s ⊕ X s at y
    unfold L
    split_ifs <;> simp
  · change ∀ s, X s at x
    change R.coeff x = (P + Q).applyLocal (B := R) L x
    erw [Raw.applyLocal_add, Raw.coeff_ofTable]
    have hs (t : (∀ s, X s) → K) :
        (Raw.ofTable X t).applyLocal (B := R)
          (fun s (a b : X s) => if b = a then 1 else 0) x = t x := by
      let T := Raw.ofTable X t
      change (∑ i : T.term, ∏ s, ∑ y : X s, (if y = x s then (1 : K) else 0) * T.factor i s y) = _
      have step (s : S) (q : X s → K) : (∑ y, (if y = x s then (1 : K) else 0) * q y) = q (x s) := by
        simp [ite_mul]
      refine (Finset.sum_congr rfl (fun i _ => Finset.prod_congr rfl (fun s _ => step s _))).trans ?_
      exact Raw.coeff_ofTable _ t x
    exact congrArg₂ (· + ·) (hs f).symm (hs g).symm

open Classical in
-- 读法：`table O X (fun x => if x = a then c else 0)` 不超过 `scalar O S c`。
theorem table_single (c : K) (a : ∀ s, X s) :
    table O X (fun x => if x = a then c else 0) ≤ scalar O S c := by
  classical
  let C := Raw.ofTable (fun _ : S => Unit) (fun _ => c)
  let L (s : S) (x : X s) (_ : Unit) : K := if x = a s then 1 else 0
  refine ⟨L, ?_, fun x => ?_⟩
  · intro s x y
    change X s at x
    unfold L
    split_ifs <;> simp
  · change ∀ s, X s at x
    rw [Raw.coeff_ofTable]
    change _ = ∑ i : C.term, ∏ s, ∑ y : Unit, L s (x s) y * C.factor i s y
    by_cases h : x = a
    · subst x
      simp only [↓reduceIte, L, one_mul]
      have e := (Raw.coeff_ofTable (fun _ : S => Unit) (fun _ => c) (fun _ => ())).symm
      refine e.trans (Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun s _ => ?_)
      exact (Fintype.sum_unique (fun x : Unit => C.factor i s x)).symm
    -- 推导：从 `Function.ne_iff.mp h` 中取出 `s, hs`。
    · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
      rw [ite_eq_right h]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.prod_eq_zero (Finset.mem_univ s) ?_
      simp [L, hs]

-- 读法：存在 `n : ℕ`，`table O X f` 不超过 `B * (n : ITensor O S)`。对 `t` 作归纳，采用 `Finset.induction_on` 的归纳原则。
theorem table_bound (f : (∀ s, X s) → K) (B : ITensor O S) (h : ∀ i, scalar O S (f i) ≤ B) :
    ∃ n : ℕ, table O X f ≤ B * (n : ITensor O S) := by
  classical
  let part (t : Finset (∀ s, X s)) (x : ∀ s, X s) := if x ∈ t then f x else 0
  have g (t : Finset (∀ s, X s)) : table O X (part t) ≤ B * (t.card : ITensor O S) := by
    induction t using Finset.induction_on with
    | empty =>
      rw [show part ∅ = 0 by ext; simp [part], table_zero]
      exact zero_le _
    | @insert i t hi ih =>
      let v (x : ∀ s, X s) := if x = i then f i else 0
      -- 推导：记下中间结论 `he`：`part (insert i t) = part t + v`。
      have he : part (insert i t) = part t + v := by
        ext x
        by_cases h : x = i <;> simp [part, v, h, hi]
      have succ (T : Type 1) [CommSemiring T] (X : T) (n : ℕ) :
          X * ((n + 1 : ℕ) : T) = X * n + X := by rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [he, Finset.card_insert_of_notMem hi, succ]
      refine (table_add _ _ _ _).trans ((add_le_add_right _ _ _ ih).trans ?_)
      have hv : table O X v ≤ B := (table_single O X _ _).trans (h i)
      rw [add_comm _ (table O X v), add_comm _ B]
      exact add_le_add_right _ _ _ hv
  have hv := g Finset.univ
  rw [show part Finset.univ = f by ext; simp [part]] at hv
  exact ⟨_, hv⟩

-- 读法：存在 `(s : ITensor O S) (n : ℕ)`，`A` 不超过 `pad U s * n`。这里调用 `add_le_add_right`。
theorem upper_bound {U : Type} [Fintype U] (A : ITensor O (S ⊕ U)) :
    ∃ (s : ITensor O S) (n : ℕ), A ≤ pad U s * n := by
  classical
  refine Quotient.inductionOn A fun a => ?_
  let L (i : ∀ s, a.leg s) := scalar O S (a.coeff i)
  let B := ∑ i, L i
  have hb (i : ∀ s, a.leg s) : L i ≤ B := by
    unfold B
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simpa only [zero_add] using add_le_add_right _ _ (L i)
      (zero_le (∑ j ∈ Finset.univ.erase i, L j))
  have hu i : scalar O (S ⊕ U) (a.coeff i) ≤ pad U B := by
    rw [← pad_scalar]
    exact ((padding U).le_iff _ _).mpr (hb i)
  obtain ⟨n, hn⟩ := table_bound O a.leg a.coeff (pad U B) hu
  rw [table_coeff] at hn
  exact ⟨B, n, hn⟩

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

section
/-!
# 在整限制下延拓

线性检验仅使用各分量属于 O 的余向量，无须由未经缩放的单位元给出秩的界。选取一个分量可得标量下界，而坐标展开给出若干标量之和作为上界。这些结论对任意子环也成立。

**英文原文**

Extension under integral restrictions

The linear test uses only covectors with entries in O. No rank bound
by unscaled units is needed. Selecting an entry yields a scalar lower
bound, and the coordinate expansion gives an upper bound by a sum of
scalars. These facts apply also to an arbitrary subring.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor

variable {K S U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype U] {O : Subring K}

-- 读法：要证明的命题是 `Prices.ExtensionData (pad U) f`。
theorem extensionData (f : ITensor O S →+* ℝ) (hf : Monotone f) :
    Prices.ExtensionData (pad U) f :=
  ⟨padding U, hf, add_le_add_right, mul_le_mul_left, zero_le, lower_bound f hf, upper_bound O⟩

-- 读法：结论为 `(∃ g : ITensor O (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔ ∀ w : List I, ∀ B, pad U B ≤ (w.map X).prod → f B ≤ (w.map p).prod`。
theorem extension_iff {I : Type*} (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (X : I → ITensor O (S ⊕ U)) (p : I → ℝ) :
    (∃ g : ITensor O (S ⊕ U) →+* ℝ, Monotone g ∧
      (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, ∀ B, pad U B ≤ (w.map X).prod → f B ≤ (w.map p).prod :=
  (extensionData f hf).extension_iff X p

-- 读法：要证明的命题是 `IsLeast {r | ∃ g : ITensor O (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ g A = r} (Prices.assisted (pad U) f A)`。
theorem assisted_minimum (f : ITensor O S →+* ℝ) (hf : Monotone f) (A : ITensor O (S ⊕ U)) :
    IsLeast {r | ∃ g : ITensor O (S ⊕ U) →+* ℝ,
      Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ g A = r} (Prices.assisted (pad U) f A) :=
  (extensionData f hf).assisted_minimum A

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end
