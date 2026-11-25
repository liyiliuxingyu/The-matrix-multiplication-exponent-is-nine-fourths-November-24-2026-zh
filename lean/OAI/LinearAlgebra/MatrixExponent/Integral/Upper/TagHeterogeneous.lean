-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Base
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialSectors
import Mathlib.Tactic.FinCases

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# 第一条腿共享的异型张量

为分支补零只会增加零坐标。分离构造使用的额外统一标签可以通过实际的独立局部映射去除。整个过程中各分支共享第一条腿，无须使用直和可加性。

**英文原文**

Heterogeneous shared-first-leg tensors

Padding a branch adds only zero coordinates. The extra uniform labels used by
the separation construction are removed by actual independent local maps.
The first leg is shared throughout; no direct-sum additivity is used here.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous

variable {X Y Z Y₀ Z₀ Y₁ Z₁ Y₂ Z₂ : Type*}

-- 读法：逐一匹配以下输入模式：`x, .inl y, .inl z`、`x, .inr y, .inr z`、`_, _, _`。
/-- 两个不同类型的分支，共用同一个第一坐标。

英文原文：Two heterogeneous branches with one common first coordinate.
-/
def sharedTwo (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁) :
    Tensor O X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inl y, .inl z => T x y z
  | x, .inr y, .inr z => S x y z
  | _, _, _ => 0

-- 读法：逐一匹配以下输入模式：`x, .inl y, .inl z`、`_, _, _`。
/-- 在后两条腿上用零延拓到左直和项。

英文原文：Zero extension into the left summand on the last two legs.
-/
def padLeft (T : Tensor O X Y₀ Z₀) : Tensor O X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inl y, .inl z => T x y z
  | _, _, _ => 0

-- 读法：逐一匹配以下输入模式：`x, .inr y, .inr z`、`_, _, _`。
/-- 在后两条腿上用零延拓到右直和项。

英文原文：Zero extension into the right summand on the last two legs.
-/
def padRight (T : Tensor O X Y₁ Z₁) : Tensor O X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁)
  | x, .inr y, .inr z => T x y z
  | _, _, _ => 0

section Padding

variable [Fintype X] [Fintype Y₀] [Fintype Z₀]
variable [Fintype Y₁] [Fintype Z₁]

-- 读法：`TensorClass.ofTensor (padLeft (Y₁ := Y₁) (Z₁ := Z₁) T)` 等于 `TensorClass.ofTensor T`。这里调用 `TensorClass.ofTensor_eq`。
/-- 在彼此均可实际限制得到对方的等价关系下，补零给出等价。

英文原文：Zero padding is an equivalence under mutual actual restriction.
-/
theorem ofTensor_padLeft (T : Tensor O X Y₀ Z₀) :
    TensorClass.ofTensor (padLeft (Y₁ := Y₁) (Z₁ := Z₁) T) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have h := CoefficientTensor.Restricts.pullback
      (padLeft (Y₁ := Y₁) (Z₁ := Z₁) T) id Sum.inl Sum.inl
    exact h
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => match y with
        | .inl v => if j = v then 1 else 0
        | .inr _ => 0),
      (fun z k => match z with
        | .inl v => if k = v then 1 else 0
        | .inr _ => 0), ?_⟩
    funext x y z
    cases y <;> cases z <;>
      simp [padLeft, Tensor.restrict, ite_mul, mul_ite]

-- 读法：`TensorClass.ofTensor (padRight (Y₀ := Y₀) (Z₀ := Z₀) T)` 等于 `TensorClass.ofTensor T`。这里调用 `TensorClass.ofTensor_eq`。
/-- 在右侧补零也有显式的嵌入映射与投影映射。

英文原文：Right zero padding also has explicit inclusion and projection maps.
-/
theorem ofTensor_padRight (T : Tensor O X Y₁ Z₁) :
    TensorClass.ofTensor (padRight (Y₀ := Y₀) (Z₀ := Z₀) T) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have h := CoefficientTensor.Restricts.pullback
      (padRight (Y₀ := Y₀) (Z₀ := Z₀) T) id Sum.inr Sum.inr
    exact h
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => match y with
        | .inl _ => 0
        | .inr v => if j = v then 1 else 0),
      (fun z k => match z with
        | .inl _ => 0
        | .inr v => if k = v then 1 else 0), ?_⟩
    funext x y z
    cases y <;> cases z <;>
      simp [padRight, Tensor.restrict, ite_mul, mul_ite]

end Padding

-- 读法：当 `ly y = h ∧ lz z = h` 成立时取 `T x y z`，否则取 `0`。
/-- 在同一个环境张量中只保留一对相匹配的分区。

英文原文：Keep just one matched pair of sectors in a common ambient tensor.
-/
def maskedFamily {M : ℕ} (ly : Y → Fin M) (lz : Z → Fin M)
    (T : Tensor O X Y Z) (h : Fin M) : Tensor O X Y Z :=
  fun x y z => if ly y = h ∧ lz z = h then T x y z else 0

section Labels

variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`TensorClass.ofTensor (Separation.shared (maskedFamily ly lz T))` 等于 `TensorClass.ofTensor T`。这里调用 `TensorClass.ofTensor_eq`。
/-- 为每个坐标选取其所属分区，即可去除冗余标签。反向映射是对应的零延拓。

英文原文：Redundant labels are removed by selecting each coordinate's own sector;
the reverse maps are the corresponding zero extensions.
-/
theorem ofTensor_shared_maskedFamily {M : ℕ}
    (ly : Y → Fin M) (lz : Z → Fin M) (T : Tensor O X Y Z)
    (hcross : ∀ x y z, ly y ≠ lz z → T x y z = 0) :
    TensorClass.ofTensor (Separation.shared (maskedFamily ly lz T)) =
      TensorClass.ofTensor T := by
  classical
  apply TensorClass.ofTensor_eq
  · have hp : Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
        (Separation.shared (maskedFamily ly lz T)) = T := by
      funext x y z
      by_cases h : ly y = lz z
      · simp [Tensor.pullback, Separation.shared, maskedFamily, h]
      · simp [Tensor.pullback, Separation.shared, h, hcross x y z h]
    simpa only [hp] using
      (CoefficientTensor.Restricts.pullback (Separation.shared (maskedFamily ly lz T))
        id (fun y => (ly y, y)) (fun z => (lz z, z)))
  · refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y j => if j = y.2 then if ly y.2 = y.1 then 1 else 0 else 0),
      (fun z k => if k = z.2 then if lz z.2 = z.1 then 1 else 0 else 0), ?_⟩
    funext x y z
    by_cases h : y.1 = z.1
    · simp [Tensor.restrict, Separation.shared, maskedFamily, h,
        ite_mul, mul_ite]
      split_ifs <;> simp_all
    · by_cases hy : ly y.2 = y.1
      · by_cases hz : lz z.2 = z.1
        · have hc : T x y.2 z.2 = 0 := hcross _ _ _ (by simpa [hy, hz] using h)
          simp [Tensor.restrict, Separation.shared, h, hy, hz,
            hc, ite_mul, mul_ite]
        · simp [Tensor.restrict, Separation.shared, h, hy, hz,
            mul_ite]
      · simp [Tensor.restrict, Separation.shared, h, hy,
          mul_ite]

end Labels

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr _`。
/-- 标识两个分区的标签，与该分区内部的坐标无关。

英文原文：A two-sector label independent of the coordinate inside the sector.
-/
def twoLabel : Y₀ ⊕ Y₁ → Fin 2
  | .inl _ => 0
  | .inr _ => 1

-- 读法：`twoFamily` 的取值由 `![padLeft T, padRight S]` 给出。
/-- 这时两个分支在后两条腿上采用相同的环境空间。

英文原文：Both branches now use the same ambient last two legs.
-/
def twoFamily (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁) :
    Fin 2 → Tensor O X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁) :=
  ![padLeft T, padRight S]

-- 读法：`twoFamily T S` 等于 `maskedFamily twoLabel twoLabel (sharedTwo T S)`。用函数外延性比较等号两侧在 `h x y z` 处的取值。
theorem twoFamily_eq_maskedFamily
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁) :
    twoFamily T S = maskedFamily twoLabel twoLabel (sharedTwo T S) := by
  funext h x y z
  fin_cases h <;> cases y <;> cases z <;>
    simp [twoFamily, maskedFamily, twoLabel, sharedTwo, padLeft, padRight]

-- 读法：`TensorClass.ofTensor (Separation.shared (twoFamily T S))` 等于 `TensorClass.ofTensor (sharedTwo T S)`。这里调用 `ofTensor_shared_maskedFamily`。
theorem ofTensor_shared_twoFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁) :
    TensorClass.ofTensor (Separation.shared (twoFamily T S)) =
      TensorClass.ofTensor (sharedTwo T S) := by
  rw [twoFamily_eq_maskedFamily]
  apply ofTensor_shared_maskedFamily
  intro x y z h
  cases y <;> cases z <;> simp_all [sharedTwo, twoLabel]

-- 读法：`TensorClass.ofTensor (twoFamily T S h)` 等于 `![TensorClass.ofTensor T, TensorClass.ofTensor S] h`。使用 `fin_cases` 给出的结论。
theorem ofTensor_twoFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁) (h : Fin 2) :
    TensorClass.ofTensor (twoFamily T S h) =
      ![TensorClass.ofTensor T, TensorClass.ofTensor S] h := by
  fin_cases h <;> simp [twoFamily, ofTensor_padLeft, ofTensor_padRight]

-- 读法：`sharedThree` 的取值由 `sharedTwo T (sharedTwo S U)` 给出。
/-- 三个不同类型的分支仍共享同一条第一腿。

英文原文：Three heterogeneous branches, still sharing one first leg.
-/
def sharedThree (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁)
    (U : Tensor O X Y₂ Z₂) :
    Tensor O X (Y₀ ⊕ (Y₁ ⊕ Y₂)) (Z₀ ⊕ (Z₁ ⊕ Z₂)) :=
  sharedTwo T (sharedTwo S U)

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr (.inl _)`、`.inr (.inr _)`。
def threeLabel : Y₀ ⊕ (Y₁ ⊕ Y₂) → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

-- 读法：`threeFamily` 的取值由 `![padLeft T, padRight (padLeft S), padRight (padRight U)]` 给出。
/-- 统一标签定理所用的三个填充后的分支。

英文原文：The three padded branches used by the uniform tag theorem.
-/
def threeFamily (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁)
    (U : Tensor O X Y₂ Z₂) :
    Fin 3 → Tensor O X (Y₀ ⊕ (Y₁ ⊕ Y₂)) (Z₀ ⊕ (Z₁ ⊕ Z₂)) :=
  ![padLeft T, padRight (padLeft S), padRight (padRight U)]

-- 读法：`threeFamily T S U` 等于 `maskedFamily threeLabel threeLabel (sharedThree T S U)`。用函数外延性比较等号两侧在 `h x y z` 处的取值。
theorem threeFamily_eq_maskedFamily
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁)
    (U : Tensor O X Y₂ Z₂) :
    threeFamily T S U = maskedFamily threeLabel threeLabel (sharedThree T S U) := by
  funext h x y z
  fin_cases h <;> rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [threeFamily, maskedFamily, threeLabel, sharedThree, sharedTwo, padLeft, padRight]

-- 读法：`TensorClass.ofTensor (Separation.shared (threeFamily T S U))` 等于 `TensorClass.ofTensor (sharedThree T S U)`。这里调用 `ofTensor_shared_maskedFamily`。
theorem ofTensor_shared_threeFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    [Fintype Y₂] [Fintype Z₂]
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁)
    (U : Tensor O X Y₂ Z₂) :
    TensorClass.ofTensor (Separation.shared (threeFamily T S U)) =
      TensorClass.ofTensor (sharedThree T S U) := by
  rw [threeFamily_eq_maskedFamily]
  apply ofTensor_shared_maskedFamily
  intro x y z h
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp_all [sharedThree, sharedTwo, threeLabel]

-- 读法：`TensorClass.ofTensor (threeFamily T S U h)` 等于 `![TensorClass.ofTensor T, TensorClass.ofTensor S, TensorClass.ofTensor U] h`。使用 `fin_cases` 给出的结论。
theorem ofTensor_threeFamily
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    [Fintype Y₂] [Fintype Z₂]
    (T : Tensor O X Y₀ Z₀) (S : Tensor O X Y₁ Z₁)
    (U : Tensor O X Y₂ Z₂) (h : Fin 3) :
    TensorClass.ofTensor (threeFamily T S U h) =
      ![TensorClass.ofTensor T, TensorClass.ofTensor S, TensorClass.ofTensor U] h := by
  fin_cases h <;> simp [threeFamily, ofTensor_padLeft, ofTensor_padRight]

-- 读法：输入 `x k j` 时返回 `polynomialTensor a h (triplingReverse x) j k`。
/-- 中间的多项式分支保留其原有的第一腿次序反转。

英文原文：The middle polynomial branch keeps its original first-leg reversal.
-/
def triplingMiddleTensor (a h : ℕ) :
    Tensor O (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun x k j => polynomialTensor a h (triplingReverse x) j k

-- 读法：`triplingSectorTensor a h` 等于 `sharedThree (polynomialTensor a h) (triplingMiddleTensor a h) (polynomialTensor a h)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 组装各多项式分区，所得恰是分支类型可以不同的共享张量，特别地，六个不匹配的分区块都仍为零。

英文原文：The actual polynomial sector assembly is exactly a heterogeneous shared
tensor; in particular all six mismatched sector blocks remain zero.
-/
theorem triplingSectorTensor_eq_sharedThree (a h : ℕ) :
    triplingSectorTensor a h = sharedThree (polynomialTensor a h)
      (triplingMiddleTensor a h) (polynomialTensor a h) := by
  funext x y z
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;> rfl

-- 读法：结论为 `TensorClass.ofTensor (Separation.shared (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h) (polynomialTensor a h))) = TensorClass.ofTensor (triplingSectorTensor a h)`。
/-- 这是表示三分区多项式退化的精确统一标签输入，各分支的第一输入空间确实是同一个空间。

英文原文：This is the exact uniform-tag input representing the three-sector
polynomial degeneration, with a literal common first-input space.
-/
theorem ofTensor_tripling_uniform (a h : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h))) = TensorClass.ofTensor (triplingSectorTensor a h) := by
  rw [ofTensor_shared_threeFamily, triplingSectorTensor_eq_sharedThree]

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous
