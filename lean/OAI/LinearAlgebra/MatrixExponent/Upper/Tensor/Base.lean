-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Basic.NNReal.Defs

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 具体有限张量与相互限制

代表元以自然数为维数，因此商是小类型。该关系的见证是三个实际的局部系数矩阵。特别地，这一定义无须调用预先判定秩或限制关系的判定器。

**英文原文**

Concrete finite tensors and mutual restriction

Representatives use natural-number dimensions, so the quotient is a small type.
The relation is witnessed by the three actual local coefficient matrices. In
particular, no rank or restriction oracle occurs in this definition.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

namespace CoefficientTensor

variable {X Y Z U V W X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`Restricts` 表示以下条件：存在 `(a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff)`，`B` 等于 `Tensor.restrict a b c A`。
/-- `Restricts A B` 表示源张量 `A` 可以限制为目标张量 `B`。

英文原文：`Restricts A B` means that the source `A` restricts to the target `B`.
-/
def Restricts (A : Tensor Coeff X Y Z) (B : Tensor Coeff U V W) : Prop :=
  ∃ (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff),
    B = Tensor.restrict a b c A

-- 读法：要证明的命题是 `Restricts A A`。
theorem Restricts.refl (A : Tensor Coeff X Y Z) : Restricts A A := by
  classical
  exact ⟨_, _, _, (Tensor.restrict_identity A).symm⟩

-- 读法：要证明的命题是 `Restricts A C`。
theorem Restricts.trans [Fintype U] [Fintype V] [Fintype W]
    {A : Tensor Coeff X Y Z} {B : Tensor Coeff U V W} {C : Tensor Coeff X' Y' Z'}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C := by
  rcases hAB with ⟨a, b, c, rfl⟩
  rcases hBC with ⟨d, e, f, rfl⟩
  exact ⟨Tensor.composeRestrictionMatrix d a, Tensor.composeRestrictionMatrix e b,
    Tensor.composeRestrictionMatrix f c, Tensor.restrict_restrict a b c d e f A⟩

-- 读法：要证明的命题是 `Restricts A (Tensor.pullback f g h A)`。
theorem Restricts.pullback (A : Tensor Coeff X Y Z)
    (f : U → X) (g : V → Y) (h : W → Z) :
    Restricts A (Tensor.pullback f g h A) := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict f g h A⟩

-- 读法：张量 `B` 的秩至多为 `r`。这里调用 `hA.restrict`。
theorem Restricts.rankAtMost {A : Tensor Coeff X Y Z} {B : Tensor Coeff U V W}
    {r : ℕ} (hAB : Restricts A B) (hA : Tensor.RankAtMost A r) :
    Tensor.RankAtMost B r := by
  rcases hAB with ⟨a, b, c, rfl⟩
  exact hA.restrict a b c

end CoefficientTensor

-- 读法：结构的字段包括 `xDim`、`yDim`、`zDim`、`coeff`。
/-- 在每条腿上都显式给出维数的有限系数张量。

英文原文：A finite coefficient tensor with an explicit dimension on every leg.
-/
structure TensorRep where
  xDim : ℕ
  yDim : ℕ
  zDim : ℕ
  coeff : Tensor Coeff (Fin xDim) (Fin yDim) (Fin zDim)

namespace TensorRep

-- 读法：用字段 `xDim`、`yDim`、`zDim`、`coeff` 构造 `TensorRep`。
/-- 用规范的有限枚举为任意有限坐标集编码。

英文原文：Encode arbitrary finite coordinates by their canonical finite enumeration.
-/
noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) : TensorRep where
  xDim := Fintype.card X
  yDim := Fintype.card Y
  zDim := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

-- 读法：`Restricts` 表示以下条件：`CoefficientTensor.Restricts A.coeff B.coeff`。
def Restricts (A B : TensorRep) : Prop := CoefficientTensor.Restricts A.coeff B.coeff

-- 读法：要证明的命题是 `Restricts A A`。使用 `CoefficientTensor.Restricts.refl` 给出的结论。
theorem Restricts.refl (A : TensorRep) : Restricts A A :=
  CoefficientTensor.Restricts.refl A.coeff

-- 读法：要证明的命题是 `Restricts A C`。使用 `CoefficientTensor.Restricts.trans` 给出的结论。
theorem Restricts.trans {A B C : TensorRep}
    (hAB : Restricts A B) (hBC : Restricts B C) : Restricts A C :=
  CoefficientTensor.Restricts.trans hAB hBC

-- 读法：要证明的命题是 `CoefficientTensor.Restricts T (ofTensor T).coeff`。使用 `CoefficientTensor.Restricts.pullback` 给出的结论。
theorem restricts_ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) :
    CoefficientTensor.Restricts T (ofTensor T).coeff :=
  CoefficientTensor.Restricts.pullback T _ _ _

-- 读法：要证明的命题是 `CoefficientTensor.Restricts (ofTensor T).coeff T`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem ofTensor_restricts {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) :
    CoefficientTensor.Restricts (ofTensor T).coeff T := by
  have h := CoefficientTensor.Restricts.pullback (ofTensor T).coeff
    (Fintype.equivFin X) (Fintype.equivFin Y) (Fintype.equivFin Z)
  have heq : Tensor.pullback (Fintype.equivFin X) (Fintype.equivFin Y)
      (Fintype.equivFin Z) (ofTensor T).coeff = T := by
    funext x y z
    simp only [ofTensor, Tensor.pullback, Equiv.symm_apply_apply]
  rcases h with ⟨a, b, c, hc⟩
  exact ⟨a, b, c, heq.symm.trans hc⟩

-- 读法：要证明的命题是 `Restricts (ofTensor T) (ofTensor U')`。通过传递性衔接 `ofTensor_restricts` 与 `h.trans`。
theorem Restricts.ofTensor {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {U' : Tensor Coeff U V W}
    (h : CoefficientTensor.Restricts T U') : Restricts (ofTensor T) (ofTensor U') :=
  (ofTensor_restricts T).trans (h.trans (restricts_ofTensor U'))

-- 读法：`Equivalent` 表示以下条件：`Restricts A B` 与 `Restricts B A` 同时成立。
/-- 由实际局部映射实现的相互限制，允许有未使用或取零的坐标。

英文原文：Mutual actual restriction, allowing unused or zero coordinates.
-/
def Equivalent (A B : TensorRep) : Prop := Restricts A B ∧ Restricts B A

-- 读法：用字段 `r`、`iseqv` 构造 `Setoid TensorRep`。
instance mutualRestriction : Setoid TensorRep where
  r := Equivalent
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩,
    fun h => ⟨h.2, h.1⟩,
    fun hAB hBC => ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩⟩

-- 读法：要证明的命题是 `Equivalent (ofTensor A.coeff) A`。
theorem equivalent_ofTensor_coeff (A : TensorRep) : Equivalent (ofTensor A.coeff) A :=
  ⟨ofTensor_restricts A.coeff, restricts_ofTensor A.coeff⟩

end TensorRep

-- 读法：`TensorClass` 的取值由 `Quotient TensorRep.mutualRestriction` 给出。
/-- 论文中以相互限制为等价关系构造的有限张量商。

英文原文：The actual finite-tensor restriction quotient of the paper.
-/
def TensorClass := Quotient TensorRep.mutualRestriction

namespace TensorClass

-- 读法：`ofRep` 的取值由 `Quotient.mk _ A` 给出。
def ofRep (A : TensorRep) : TensorClass := Quotient.mk _ A

-- 读法：`ofTensor` 的取值由 `ofRep (TensorRep.ofTensor T)` 给出。
noncomputable def ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) : TensorClass := ofRep (TensorRep.ofTensor T)

-- 读法：`ofRep A` 等于 `ofRep B`。使用 `Quotient.sound` 给出的结论。
theorem ofRep_eq {A B : TensorRep} (h : TensorRep.Equivalent A B) :
    ofRep A = ofRep B := Quotient.sound h

-- 读法：`ofTensor A.coeff` 等于 `ofRep A`。使用 `ofRep_eq` 给出的结论。
theorem ofTensor_coeff (A : TensorRep) : ofTensor A.coeff = ofRep A :=
  ofRep_eq (TensorRep.equivalent_ofTensor_coeff A)

-- 读法：`ofTensor T` 等于 `ofTensor S`。使用 `ofRep_eq` 给出的结论。
theorem ofTensor_eq {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W}
    (hTS : CoefficientTensor.Restricts T S)
    (hST : CoefficientTensor.Restricts S T) : ofTensor T = ofTensor S :=
  ofRep_eq ⟨TensorRep.Restricts.ofTensor hTS, TensorRep.Restricts.ofTensor hST⟩

-- 读法：`ofTensor (Tensor.pullback f g h T)` 等于 `ofTensor T`。这里调用 `ofTensor_eq`。
theorem ofTensor_pullback_equiv {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor Coeff X Y Z) (f : U ≃ X) (g : V ≃ Y) (h : W ≃ Z) :
    ofTensor (Tensor.pullback f g h T) = ofTensor T := by
  apply ofTensor_eq
  · have h' := CoefficientTensor.Restricts.pullback (Tensor.pullback f g h T)
      f.symm g.symm h.symm
    have heq : Tensor.pullback f.symm g.symm h.symm (Tensor.pullback f g h T) = T := by
      funext x y z
      simp only [Tensor.pullback, Equiv.apply_symm_apply]
    rw [heq] at h'
    exact h'
  · exact CoefficientTensor.Restricts.pullback T f g h

-- 读法：用字段 `le` 构造 `LE TensorClass`。
instance : LE TensorClass where
  le A B := Quotient.liftOn₂ A B (fun a b => TensorRep.Restricts b a) (by
    intro A B A' B' hA hB
    apply propext
    exact ⟨fun h => hB.2.trans (h.trans hA.1),
      fun h => hB.1.trans (h.trans hA.2)⟩)

-- 读法：用字段 `le`、`le_refl`、`le_trans`、`le_antisymm` 构造 `PartialOrder TensorClass`。
instance : PartialOrder TensorClass where
  le := (· ≤ ·)
  le_refl := by
    intro A
    induction A using Quotient.inductionOn with | h a =>
      exact TensorRep.Restricts.refl a
  le_trans := by
    intro A B C
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        induction C using Quotient.inductionOn with | h C =>
          exact fun hAB hBC => TensorRep.Restricts.trans hBC hAB
  le_antisymm := by
    intro A B
    induction A using Quotient.inductionOn with | h A =>
      induction B using Quotient.inductionOn with | h B =>
        exact fun hAB hBA => Quotient.sound ⟨hBA, hAB⟩

-- 读法：`ofTensor S` 不超过 `ofTensor T`。使用 `TensorRep.Restricts.ofTensor` 给出的结论。
theorem ofTensor_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor Coeff X Y Z} {S : Tensor Coeff U V W}
    (h : CoefficientTensor.Restricts T S) : ofTensor S ≤ ofTensor T :=
  TensorRep.Restricts.ofTensor h

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Upper
