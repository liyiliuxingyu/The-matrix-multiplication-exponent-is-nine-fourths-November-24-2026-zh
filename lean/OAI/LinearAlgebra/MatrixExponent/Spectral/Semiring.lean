-- 本文件所属证明环节：在具有命名站点的张量半环中操作共享标签与连线，利用局部限制、运输和谱比较构造替换原布线的张量展开。
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-!
# 有限个具名位点上的系数张量

以纯张量的有限和作为存储形式。限制作在每个加项上，以局部矩阵作用，再比较所得系数数组。限制无需保持原先选定的分解。每个数组都有坐标展开，同一数组的两个展开可相互限制。

**英文原文**

Coefficient tensors on a finite set of named sites

We store a finite sum of pure tensors. Restriction acts by a local matrix
on every summand and compares the resulting coefficient arrays. It need
not preserve the chosen decomposition. Every array has a coordinate
expansion, and two expansions of the same array restrict to each other.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

-- 读法：结构的字段包括 `leg`、`term`、`factor`。
structure Raw (K S : Type) where
  leg : S → Type
  term : Type
  [fleg : ∀ s, Fintype (leg s)]
  [fterm : Fintype term]
  factor : term → (s : S) → leg s → K

attribute [instance] Raw.fleg Raw.fterm

namespace Raw

variable {K S : Type} [Field K] [Fintype S]

-- 读法：`coeff` 的取值由 `∑ i : A.term, ∏ s, A.factor i s (x s)` 给出。
def coeff (A : Raw K S) (x : ∀ s, A.leg s) : K :=
  ∑ i : A.term, ∏ s, A.factor i s (x s)

-- 读法：`Restricts` 表示以下条件：存在 `L : (s : S) → B.leg s → A.leg s → K`，对每个 `x : ∀ s`，`B.leg s, B.coeff x` 等于 `∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y`。
def Restricts (A B : Raw K S) : Prop :=
  ∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s,
    B.coeff x = ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y

-- 读法：`Zero (Raw K S)` 的取值由 `⟨⟨fun _ => Empty, Empty, fun i => i.elim⟩⟩` 给出。
instance : Zero (Raw K S) :=
  ⟨⟨fun _ => Empty, Empty, fun i => i.elim⟩⟩

-- 读法：`One (Raw K S)` 的取值由 `⟨⟨fun _ => Unit, Unit, fun _ _ _ => 1⟩⟩` 给出。
instance : One (Raw K S) :=
  ⟨⟨fun _ => Unit, Unit, fun _ _ _ => 1⟩⟩

-- 读法：用字段 `add` 构造 `Add (Raw K S)`。
instance : Add (Raw K S) where
  add A B := ⟨fun s => A.leg s ⊕ B.leg s, A.term ⊕ B.term,
    fun i s => Sum.elim
      (fun j => Sum.elim (A.factor j s) (fun _ => 0))
      (fun j => Sum.elim (fun _ => 0) (B.factor j s)) i⟩

-- 读法：用字段 `mul` 构造 `Mul (Raw K S)`。
instance : Mul (Raw K S) where
  mul A B := ⟨fun s => A.leg s × B.leg s, A.term × B.term,
    fun i s x => A.factor i.1 s x.1 * B.factor i.2 s x.2⟩

variable {A B C : Raw K S}

-- 读法：要证明的命题是 `A.Restricts B`。
/-- 复制或选取局部坐标给出一个限制。

英文原文：Copying or selecting local coordinates is a restriction.
-/
theorem Restricts.pullback (f : ∀ s, B.leg s → A.leg s)
    (h : ∀ x, B.coeff x = A.coeff (fun s => f s (x s))) : A.Restricts B := by
  classical
  refine ⟨fun s x y => if y = f s x then 1 else 0, fun x => ?_⟩
  rw [h]
  simp [coeff, ite_mul]

-- 读法：要证明的命题是 `A.Restricts A`。使用 `Restricts.pullback` 给出的结论。
theorem Restricts.refl (A : Raw K S) : A.Restricts A :=
  Restricts.pullback (fun _ x => x) (fun _ => rfl)

-- 读法：`(∑ i : A.term, ∏ s, ∑ y : A.leg s, v s y * A.factor i s y)` 等于 `∑ y : ∀ s, A.leg s, (∏ s, v s (y s)) * A.coeff y`。
theorem expand [DecidableEq S] (A : Raw K S) (v : ∀ s, A.leg s → K) :
    (∑ i : A.term, ∏ s, ∑ y : A.leg s, v s y * A.factor i s y) =
      ∑ y : ∀ s, A.leg s, (∏ s, v s (y s)) * A.coeff y := by
  simp only [Fintype.prod_sum, Finset.prod_mul_distrib, coeff, Finset.mul_sum]
  rw [Finset.sum_comm]

-- 读法：结论为 `A.Restricts B ↔ ∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s, B.coeff x = ∑ y : ∀ s, A.leg s, (∏ s, L s (x s) (y s)) * A.coeff y`。
/-- 该公式与两个数组各自所选的展开方式均无关。

英文原文：Formula independent of the chosen expansions of both arrays.
-/
theorem restricts_iff [DecidableEq S] (A B : Raw K S) :
    A.Restricts B ↔
      ∃ L : (s : S) → B.leg s → A.leg s → K, ∀ x : ∀ s, B.leg s,
        B.coeff x = ∑ y : ∀ s, A.leg s, (∏ s, L s (x s) (y s)) * A.coeff y := by
  simp only [Restricts, expand]

-- 读法：要证明的命题是 `A.Restricts C`。这里调用 `Finset.sum_congr`。
theorem Restricts.trans (h : A.Restricts B) (g : B.Restricts C) : A.Restricts C := by
  classical
  obtain ⟨L, hL⟩ := h
  obtain ⟨P, hP⟩ := (restricts_iff B C).mp g
  refine ⟨fun s x z => ∑ y, P s x y * L s y z, fun x => ?_⟩
  rw [hP]
  simp only [hL, Finset.mul_sum, ← Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.prod_sum (fun s y => ∑ z, P s (x s) y * (L s y z * A.factor i s z))]
  apply Finset.prod_congr rfl
  intro s _
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

-- 读法：用字段 `r`、`iseqv` 构造 `Setoid (Raw K S)`。
instance : Setoid (Raw K S) where
  r A B := A.Restricts B ∧ B.Restricts A
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩, fun h => ⟨h.2, h.1⟩,
    fun h g => ⟨h.1.trans g.1, g.2.trans h.2⟩⟩

-- 读法：要证明的命题是 `A ≈ B`。
theorem equiv_coeff (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ x, A.coeff x = B.coeff (fun s => f s (x s))) : A ≈ B := by
  refine ⟨Restricts.pullback (fun s => (f s).symm) ?_, Restricts.pullback (fun s => f s) h⟩
  intro x
  simp only [h, Equiv.apply_symm_apply]

-- 读法：要证明的命题是 `A ≈ B`。这里调用 `e.sum_comp`。
theorem relabel (e : A.term ≃ B.term) (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ i s x, A.factor i s x = B.factor (e i) s (f s x)) : A ≈ B := by
  refine equiv_coeff f fun x => ?_
  simp only [coeff, h]
  exact e.sum_comp (fun i => ∏ s, B.factor i s (f s (x s)))

end Raw
end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# 限制的直和与乘积

对于和使用分块对角矩阵，对于积使用 Kronecker 积。这些恒等式针对系数数组，不要求各分解中的项逐一对应。

**英文原文**

Direct sums and products of restrictions

Use block diagonal matrices for sums and Kronecker products for products.
The identities concern coefficient arrays and require no termwise
correspondence between the decompositions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] {A B C D : Raw K S}

-- 读法：`(A * B).coeff x` 等于 `A.coeff (fun s => (x s).1) * B.coeff (fun s => (x s).2)`。
theorem coeff_mul (A B : Raw K S) (x : ∀ s, (A * B).leg s) :
    (A * B).coeff x = A.coeff (fun s => (x s).1) * B.coeff (fun s => (x s).2) := by
  change (∑ i : A.term × B.term, ∏ s, A.factor i.1 s (x s).1 * B.factor i.2 s (x s).2) = _
  simp only [coeff, Fintype.sum_prod_type, Finset.prod_mul_distrib, Finset.sum_mul_sum]

-- 读法：要证明的命题是 `(A * C).Restricts (B * D)`。
theorem Restricts.mul (h : A.Restricts B) (g : C.Restricts D) :
    (A * C).Restricts (B * D) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := g
  refine ⟨fun s x y => L s x.1 y.1 * M s x.2 y.2, fun x => ?_⟩
  rw [coeff_mul, hL, hM]
  change _ = ∑ i : A.term × C.term, ∏ s, ∑ y : A.leg s × C.leg s,
    L s (x s).1 y.1 * M s (x s).2 y.2 * (A.factor i.1 s y.1 * C.factor i.2 s y.2)
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_mul_mul_comm _ _ _ _

-- 读法：`(∑ i, ∏ s, u i s)` 等于 `∑ j, ∏ s, v j s`。按 `∃ s, (∀ i, u i s = 0) ∧ (∀ j, v j s = 0)` 成立与否分情况。
/-- 把因子作零延拓仍保持系数数组的相等性。

英文原文：Equality of coefficient arrays survives extending the factors by zero.
-/
theorem extend {I J : Type} [Fintype I] [Fintype J] {Z : S → Type}
    (f : I → (s : S) → Z s → K) (g : J → (s : S) → Z s → K)
    (h : ∀ x : ∀ s, Z s, (∑ i, ∏ s, f i s (x s)) = ∑ j, ∏ s, g j s (x s))
    {u : I → S → K} {v : J → S → K}
    (huv : ∀ s, (∃ z, (∀ i, u i s = f i s z) ∧ (∀ j, v j s = g j s z)) ∨
      ((∀ i, u i s = 0) ∧ (∀ j, v j s = 0))) :
    (∑ i, ∏ s, u i s) = ∑ j, ∏ s, v j s := by
  classical
  by_cases he : ∃ s, (∀ i, u i s = 0) ∧ (∀ j, v j s = 0)
  · obtain ⟨s, hu, hv⟩ := he
    exact (Finset.sum_eq_zero fun i _ => Finset.prod_eq_zero (Finset.mem_univ s) (hu i)).trans
      (Finset.sum_eq_zero fun j _ => Finset.prod_eq_zero (Finset.mem_univ s) (hv j)).symm
  · have hx (s : S) := (huv s).resolve_right fun hs => he ⟨s, hs⟩
    choose x hu hv using hx
    simp only [hu, hv, h]

-- 读法：要证明的命题是 `(A + C).Restricts (B + D)`。
theorem Restricts.add (h : A.Restricts B) (g : C.Restricts D) :
    (A + C).Restricts (B + D) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := g
  let N (s : S) : B.leg s ⊕ D.leg s → A.leg s ⊕ C.leg s → K :=
    Sum.elim (fun b => Sum.elim (L s b) (fun _ => 0))
      (fun d => Sum.elim (fun _ => 0) (M s d))
  have left (i : A.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inl i) s y = Sum.elim (A.factor i s) (fun _ => 0) y := rfl
  have right (i : C.term) (s : S) (y : A.leg s ⊕ C.leg s) :
      (A + C).factor (.inr i) s y = Sum.elim (fun _ => 0) (C.factor i s) y := rfl
  refine ⟨N, fun x => ?_⟩
  change (∑ i : B.term ⊕ D.term, ∏ s, (B + D).factor i s (x s)) =
    ∑ i : A.term ⊕ C.term, ∏ s, ∑ y : A.leg s ⊕ C.leg s,
      N s (x s) y * (A + C).factor i s y
  simp only [Fintype.sum_sum_type, left, right]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine extend B.factor (fun i s z => ∑ y, L s z y * A.factor i s y) hL ?_
    intro s
    cases x s with
    | inl z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [N]⟩
    | inr z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [N]⟩
  · refine extend D.factor (fun i s z => ∑ y, M s z y * C.factor i s y) hM ?_
    intro s
    cases x s with
    | inl z => exact Or.inr ⟨fun _ => rfl, fun _ => by simp [N]⟩
    | inr z => exact Or.inl ⟨z, fun _ => rfl, fun _ => by simp [N]⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

section
/-!
# 按相互限制取等价后的半环律

对每条恒等式，用同一个和或积的等价映射同时重新编号各项与每个位点上的坐标。

**英文原文**

Semiring laws up to mutual restriction

Each identity reindexes the terms and the coordinates at every site by
the same sum or product equivalence.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] (A B C : Raw K S)

-- 读法：要证明的命题是 `A + B ≈ B + A`。
theorem comm_add : A + B ≈ B + A := by
  refine relabel (Equiv.sumComm _ _) (fun _ => Equiv.sumComm _ _) ?_
  rintro (i | i) s (x | x) <;> rfl

-- 读法：要证明的命题是 `(A + B) + C ≈ A + (B + C)`。
theorem assoc_add : (A + B) + C ≈ A + (B + C) := by
  refine relabel (Equiv.sumAssoc _ _ _) (fun _ => Equiv.sumAssoc _ _ _) ?_
  rintro ((i | i) | i) s ((x | x) | x) <;> rfl

-- 读法：要证明的命题是 `0 + A ≈ A`。这里调用 `i.elim`。
theorem nil_add : 0 + A ≈ A := by
  refine relabel (Equiv.emptySum Empty _) (fun _ => Equiv.emptySum Empty _) ?_
  rintro (i | i)
  · exact i.elim
  rintro s (x | x)
  · exact x.elim
  rfl

-- 读法：要证明的命题是 `A * B ≈ B * A`。这里调用 `mul_comm`。
theorem comm_mul : A * B ≈ B * A := by
  refine relabel (Equiv.prodComm _ _) (fun _ => Equiv.prodComm _ _) ?_
  intro i s x
  exact mul_comm _ _

-- 读法：要证明的命题是 `(A * B) * C ≈ A * (B * C)`。这里调用 `mul_assoc`。
theorem assoc_mul : (A * B) * C ≈ A * (B * C) := by
  refine relabel (Equiv.prodAssoc _ _ _) (fun _ => Equiv.prodAssoc _ _ _) ?_
  intro i s x
  exact mul_assoc _ _ _

-- 读法：要证明的命题是 `1 * A ≈ A`。这里调用 `one_mul`。
theorem unit_mul : 1 * A ≈ A := by
  refine relabel (Equiv.punitProd _) (fun _ => Equiv.punitProd _) ?_
  intro i s x
  exact one_mul _

-- 读法：要证明的命题是 `0 * A ≈ 0`。这里调用 `i.1.elim`。
theorem nil_mul : 0 * A ≈ 0 := by
  refine relabel (Equiv.emptyProd _) (fun _ => Equiv.emptyProd _) ?_
  intro i
  exact i.1.elim

-- 读法：要证明的命题是 `A * (B + C) ≈ A * B + A * C`。这里调用 `mul_zero`。
theorem distrib_left : A * (B + C) ≈ A * B + A * C := by
  refine relabel (Equiv.prodSumDistrib _ _ _) (fun _ => Equiv.prodSumDistrib _ _ _) ?_
  rintro ⟨i, j | j⟩ s ⟨x, y | y⟩
  · rfl
  · exact mul_zero _
  · exact mul_zero _
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# 固定位点有限集上的限制半环

**英文原文**

The restriction semiring on a fixed finite set of sites
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

-- 读法：`Tensor` 的取值由 `Quotient (inferInstance : Setoid (Raw K S))` 给出。
/-- 按可相互局部线性限制的等价关系，对系数张量取商。

英文原文：Coefficient tensors modulo mutual local linear restriction.
-/
def Tensor (K S : Type) [Field K] [Fintype S] :=
  Quotient (inferInstance : Setoid (Raw K S))

namespace Tensor

variable {K S : Type} [Field K] [Fintype S]

-- 读法：`ofRaw` 的取值由 `Quotient.mk _ A` 给出。
def ofRaw (A : Raw K S) : Tensor K S := Quotient.mk _ A

-- 读法：`ofRaw A` 等于 `ofRaw B`。使用 `Quotient.sound` 给出的结论。
theorem ofRaw_eq {A B : Raw K S} (h : A ≈ B) : ofRaw A = ofRaw B :=
  Quotient.sound h

-- 读法：为 `LE (Tensor K S)` 构造类型类实例。
instance : LE (Tensor K S) :=
  ⟨Quotient.lift₂ (fun a b => b.Restricts a) fun _ _ _ _ h g => propext
    ⟨fun t => g.2.trans (t.trans h.1), fun t => g.1.trans (t.trans h.2)⟩⟩

-- 读法：`ofRaw A ≤ ofRaw B` 与 `B.Restricts A` 等价。使用 `Iff.rfl` 给出的结论。
theorem ofRaw_le (A B : Raw K S) : ofRaw A ≤ ofRaw B ↔ B.Restricts A := Iff.rfl

-- 读法：用字段 `le`、`le_refl`、`le_trans`、`le_antisymm` 构造 `PartialOrder (Tensor K S)`。
instance : PartialOrder (Tensor K S) where
  le := (· ≤ ·)
  le_refl A := Quotient.inductionOn A (fun a => Raw.Restricts.refl a)
  le_trans A B C := Quotient.inductionOn₃ A B C fun _ _ _ h g => Raw.Restricts.trans g h
  le_antisymm A B := Quotient.inductionOn₂ A B fun _ _ h g => Quotient.sound ⟨g, h⟩

-- 读法：`Zero (Tensor K S)` 的取值由 `⟨ofRaw 0⟩` 给出。
instance : Zero (Tensor K S) := ⟨ofRaw 0⟩
-- 读法：`One (Tensor K S)` 的取值由 `⟨ofRaw 1⟩` 给出。
instance : One (Tensor K S) := ⟨ofRaw 1⟩

-- 读法：`Add (Tensor K S)` 的取值由 `⟨Quotient.map₂ (· + ·) fun _ _ h _ _ g => ⟨h.1.add g.1, h.2.add g.2⟩⟩` 给出。
instance : Add (Tensor K S) :=
  ⟨Quotient.map₂ (· + ·) fun _ _ h _ _ g => ⟨h.1.add g.1, h.2.add g.2⟩⟩

-- 读法：`Mul (Tensor K S)` 的取值由 `⟨Quotient.map₂ (· * ·) fun _ _ h _ _ g => ⟨h.1.mul g.1, h.2.mul g.2⟩⟩` 给出。
instance : Mul (Tensor K S) :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h _ _ g => ⟨h.1.mul g.1, h.2.mul g.2⟩⟩

-- 读法：`ofRaw (A + B)` 等于 `ofRaw A + ofRaw B`。两端由定义化简为同一项。
theorem ofRaw_add (A B : Raw K S) : ofRaw (A + B) = ofRaw A + ofRaw B := rfl
-- 读法：`ofRaw (A * B)` 等于 `ofRaw A * ofRaw B`。两端由定义化简为同一项。
theorem ofRaw_mul (A B : Raw K S) : ofRaw (A * B) = ofRaw A * ofRaw B := rfl

-- 读法：`A + B` 等于 `B + A`。使用 `Quotient.inductionOn₂` 给出的结论。
private theorem comm_add (A B : Tensor K S) : A + B = B + A :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.comm_add a b)

-- 读法：`A * B` 等于 `B * A`。使用 `Quotient.inductionOn₂` 给出的结论。
private theorem comm_mul (A B : Tensor K S) : A * B = B * A :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.comm_mul a b)

-- 读法：`A * (B + C)` 等于 `A * B + A * C`。使用 `Quotient.inductionOn₃` 给出的结论。
private theorem distrib_left (A B C : Tensor K S) : A * (B + C) = A * B + A * C :=
  Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Raw.distrib_left a b c)

-- 读法：用字段 `add`、`mul`、`zero`、`one` 构造 `CommSemiring (Tensor K S)`。
instance : CommSemiring (Tensor K S) where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  nsmul := nsmulRec
  add_assoc A B C := Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Raw.assoc_add a b c)
  add_comm := comm_add
  zero_add A := Quotient.inductionOn A fun a => ofRaw_eq (Raw.nil_add a)
  add_zero A := (comm_add A 0).trans (Quotient.inductionOn A fun a => ofRaw_eq (Raw.nil_add a))
  mul_assoc A B C := Quotient.inductionOn₃ A B C fun a b c => ofRaw_eq (Raw.assoc_mul a b c)
  mul_comm := comm_mul
  one_mul A := Quotient.inductionOn A fun a => ofRaw_eq (Raw.unit_mul a)
  mul_one A := (comm_mul A 1).trans (Quotient.inductionOn A fun a => ofRaw_eq (Raw.unit_mul a))
  zero_mul A := Quotient.inductionOn A fun a => ofRaw_eq (Raw.nil_mul a)
  mul_zero A := (comm_mul A 0).trans (Quotient.inductionOn A fun a => ofRaw_eq (Raw.nil_mul a))
  left_distrib := distrib_left
  right_distrib A B C := by rw [comm_mul, distrib_left, comm_mul C A, comm_mul C B]

-- 读法：由 `A ≤ B` 推出 `A + C ≤ B + C`。使用 `Quotient.inductionOn₃` 给出的结论。
theorem add_le_add_right (A B C : Tensor K S) : A ≤ B → A + C ≤ B + C :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Raw.Restricts.add h (.refl c)

-- 读法：由 `A ≤ B` 推出 `C * A ≤ C * B`。使用 `Quotient.inductionOn₃` 给出的结论。
theorem mul_le_mul_left (A B C : Tensor K S) : A ≤ B → C * A ≤ C * B :=
  Quotient.inductionOn₃ A B C fun _ _ c h => Raw.Restricts.mul (.refl c) h

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# 有限系数表

各位点坐标选择器的乘积为带权 Kronecker δ。只需在一个位点放置权重。

**英文原文**

Finite coefficient tables

The product of local coordinate selectors is a weighted Kronecker delta.
It suffices to put the weight at one site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]

open Classical in
-- 读法：`selector` 的取值由 `if y = x s then if s = Classical.arbitrary S then a else 1 else 0` 给出。
private def selector {X : S → Type} (x : ∀ s, X s) (a : K) (s : S) (y : X s) : K :=
  if y = x s then if s = Classical.arbitrary S then a else 1 else 0

open Classical in
-- 读法：`(∏ s, selector x a s (y s))` 等于 `if y = x then a else 0`。按 `y = x` 成立与否分情况。
private theorem prod_selector {X : S → Type} (x y : ∀ s, X s) (a : K) :
    (∏ s, selector x a s (y s)) = if y = x then a else 0 := by
  by_cases h : y = x
  · subst y
    simp [selector]
  · rw [ite_eq_right h]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs)

variable (X : S → Type) [∀ s, Fintype (X s)]

-- 读法：`ofTable` 的结果类型为 `Raw K S`。
/-- 将任意有限数组按坐标展开为纯张量之和。

英文原文：Coordinate expansion of any finite array as a sum of pure tensors.
-/
def ofTable (f : (∀ s, X s) → K) : Raw K S := by
  classical
  exact ⟨X, ∀ s, X s, fun i => selector i (f i)⟩

-- 读法：`(ofTable X f).coeff x` 等于 `f x`。
@[simp] theorem coeff_ofTable (f : (∀ s, X s) → K) (x : ∀ s, X s) :
    (ofTable X f).coeff x = f x := by
  classical
  change (∑ i : ∀ s, X s, ∏ s, selector i (f i) s (x s)) = _
  simp [prod_selector]

-- 读法：要证明的命题是 `A.Restricts 1`。
/-- 选一个非零系数，再乘以其逆元即可恢复单位张量。

英文原文：Selecting a nonzero coefficient and scaling by its inverse recovers the unit.
-/
theorem restricts_one (A : Raw K S) (h : ∃ x, A.coeff x ≠ 0) : A.Restricts 1 := by
  classical
  obtain ⟨x, hx⟩ := h
  refine (restricts_iff _ _).mpr ⟨fun s _ => selector x (A.coeff x)⁻¹ s, fun _ => ?_⟩
  change (∑ _ : Unit, ∏ _ : S, (1 : K)) = _
  simp [prod_selector, ite_mul, hx]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end
