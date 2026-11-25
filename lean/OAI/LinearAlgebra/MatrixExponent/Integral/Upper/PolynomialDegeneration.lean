-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

open OAI.LinearAlgebra.MatrixExponent.Integral

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

variable {X Y Z : Type*}

-- 读法：当 `wx x + wy y + wz z = 0` 成立时取 `T x y z`，否则取 `0`。
/-- 张量中对角总权重为零的部分。

英文原文：The part of a tensor with total diagonal weight zero.
-/
def weightedLimit (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) : Tensor O X Y Z :=
  fun x y z => if wx x + wy y + wz z = 0 then T x y z else 0

-- 读法：输入 `x y z` 时返回 `t ^ (wx x + wy y + wz z).toNat * T x y z`。
/-- 多项式系数族。在退化定理中，总权重为负的坐标上系数必为零。

英文原文：The polynomial coefficient family. Negative total weights
occur only at zero coefficients in the degeneration theorem.
-/
def weightedFamily (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (t : O) : Tensor O X Y Z :=
  fun x y z => t ^ (wx x + wy y + wz z).toNat * T x y z

-- 读法：`weightedFamily T wx wy wz 0` 等于 `weightedLimit T wx wy wz`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem weightedFamily_zero (T : Tensor O X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z) :
    weightedFamily T wx wy wz 0 = weightedLimit T wx wy wz := by
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, weightedLimit, hT]
  · have hnonneg := h x y z hT
    by_cases hw : wx x + wy y + wz z = 0
    · simp [weightedFamily, weightedLimit, hw]
    · have hnatne : (wx x + wy y + wz z).toNat ≠ 0 := by
        intro he
        have hc := Int.toNat_of_nonneg hnonneg
        rw [he] at hc
        exact hw hc.symm
      simp [weightedFamily, weightedLimit, hw, zero_pow hnatne]

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 对角局部系数矩阵使三个对应的系数因子相乘，所有非对角贡献均为零。

英文原文：Diagonal local coefficient matrices multiply the three corresponding
coefficient factors, with all off-diagonal contributions vanishing.
-/
theorem restrict_diagonal [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor O X Y Z) (a : X → O) (b : Y → O) (c : Z → O) :
    Tensor.restrict (fun x' x => if x = x' then a x else 0)
      (fun y' y => if y = y' then b y else 0)
      (fun z' z => if z = z' then c z else 0) T =
      fun x y z => a x * b y * c z * T x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, ite_mul, mul_ite]

-- 读法：`weightedFamily T wx wy wz t` 属于 `LocalTensor.orbit T`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 对每个非零参数，这个族的取值都由显式局部代换实现，对角元分别取相应的整数次幂。

英文原文：At every nonzero parameter, the family is witnessed by actual
local substitutions: the diagonal entries are the respective integer powers.
-/
theorem weightedFamily_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : O} (ht : IsUnit t) :
    weightedFamily T wx wy wz t ∈ LocalTensor.orbit T := by
  classical
  refine ⟨(fun x' x => if x = x' then t ^ wx x else 0),
    (fun y' y => if y = y' then t ^ wy y else 0),
    (fun z' z => if z = z' then t ^ wz z else 0), ?_⟩
  rw [restrict_diagonal]
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, hT]
  · have hnonneg := h x y z hT
    dsimp [weightedFamily]
    rw [← upow_nat, Int.toNat_of_nonneg hnonneg,
      upow_add ht, upow_add ht]

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
