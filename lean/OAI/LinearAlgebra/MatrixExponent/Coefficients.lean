-- 本文件所属证明环节：给上界构造选择系数和插值节点，记录代数闭域中可实现的取值，并指定矩阵乘法张量。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import OAI.LinearAlgebra.TensorSpectrum.Additive.RankAnalysis
import OAI.LinearAlgebra.MatrixExponent.LocalTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# 选取上界证明所需的系数

张量半环的类型是单态的。为了在不假定特征为零时复用它，若存在反例，就选取一个代数闭域上的反例。张量论证仅使用域公理和代数闭性。

**英文原文**

Choosing coefficients for the upper bound

The tensor semiring is monomorphic. To reuse it without assuming
characteristic zero, choose an algebraically closed counterexample if one
exists. The tensor argument only uses the field axioms and algebraic closure.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：结构的字段包括 `carrier`。
structure ClosedField where
  carrier : Type
  [field : Field carrier]
  [closed : IsAlgClosed carrier]

attribute [instance] ClosedField.field ClosedField.closed

-- 读法：`Nonempty ClosedField` 的取值由 `⟨⟨AlgebraicClosure ℚ⟩⟩` 给出。
instance : Nonempty ClosedField := ⟨⟨AlgebraicClosure ℚ⟩⟩

-- 读法：`Rectangle.DiscreteBound` 表示以下条件：对每个 `A B C : ℕ`，由 `0 < A` 推出 `0 < B → 0 < C → Rectangle.exponent F ((A : ℝ) * B) ((A : ℝ) * C) ((B : ℝ) * C) ≤ ((A : ℝ) + B + C) ^ 2 / 4`。
def Rectangle.DiscreteBound (F : Type*) [Field F] : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
    Rectangle.exponent F ((A : ℝ) * B) ((A : ℝ) * C) ((B : ℝ) * C) ≤ ((A : ℝ) + B + C) ^ 2 / 4

-- 读法：结构的字段包括 `discrete`、`density`、`cells`、`binary`、`degrees`。
/-- 共享标签不等式在各个域上共同成立的推论。这里的各条性质均不以方阵情形的等式或任何关于谱接触的猜想为前提。

英文原文：Field-independent consequences of the shared-tag inequality. No
law assumes square equality or any conjecture about spectral contacts.
-/
structure Fulfills (F : Type) [Field F] : Prop where
  discrete : Rectangle.DiscreteBound F
  density : Rectangle.DensityBound F
  cells : Rectangle.CellBound F
  binary : Rectangle.Profile.BinaryLaw F
  degrees : Rectangle.Sparse.DegreeBound F

-- 读法：`candidate` 的取值由 `Classical.epsilon (fun k : ClosedField => ¬ Fulfills k.carrier)` 给出。
def candidate : ClosedField :=
  Classical.epsilon (fun k : ClosedField => ¬ Fulfills k.carrier)

-- 读法：在后续公式中，`Coeff` 是 `candidate.carrier` 的缩写。
abbrev Coeff := candidate.carrier

-- 读法：要证明的命题是 `Fulfills K`。这里调用 `Classical.epsilon_spec`。
theorem closed_laws (h : Fulfills Coeff) (K : Type) [Field K] [IsAlgClosed K] :
    Fulfills K := by
  by_contra bad
  have ex : ∃ k : ClosedField, ¬ Fulfills k.carrier := ⟨⟨K⟩, bad⟩
  exact Classical.epsilon_spec ex h

-- 读法：存在 `nodes : Fin n → F`，`Function.Injective nodes` 与 `∀ i, nodes i ≠ 0` 同时成立。
theorem exists_nonzero_nodes {F : Type*} [Field F] [Infinite F] (n : ℕ) :
    ∃ nodes : Fin n → F, Function.Injective nodes ∧ ∀ i, nodes i ≠ 0 := by
  let e : Fin n ↪ ({0}ᶜ : Set F) :=
    Fin.valEmbedding.trans ((Set.finite_singleton (0 : F)).infinite_compl.natEmbedding _)
  exact ⟨fun i => e i, Subtype.val_injective.comp e.injective, fun i => (e i).property⟩

end OAI.LinearAlgebra.MatrixExponent

namespace OAI.LinearAlgebra.MatrixExponent.Upper
open OAI.MatrixMultiplication.Foundation

-- 读法：`matrixTensor` 的取值由 `Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)` 给出。
def matrixTensor (a b c : ℕ) :
    Tensor Coeff (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end OAI.LinearAlgebra.MatrixExponent.Upper
