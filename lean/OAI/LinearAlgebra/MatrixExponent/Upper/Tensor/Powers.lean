-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.RankOrder

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 商中的张量幂与完全重复直和

这些联系保持了插值所用的具体系数张量。

**英文原文**

Tensor powers and full repeated direct sums in the quotient

These bridges preserve the actual coefficient tensors used by interpolation.
-/

open scoped BigOperators NNReal
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Fin (n + 1) → X) ≃ X × (Fin n → X)`。
private def finSuccFunctions (n : ℕ) (X : Type*) :
    (Fin (n + 1) → X) ≃ X × (Fin n → X) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨x, f⟩
    rfl

-- 读法：`ofTensor (Tensor.power T n)` 等于 `(ofTensor T) ^ n`。对 `n` 作归纳。
theorem ofTensor_power {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (n : ℕ) :
    ofTensor (Tensor.power T n) = (ofTensor T) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ofTensor (Tensor.power T 0) = ofTensor unitTensor
    have heq : Tensor.pullback (Equiv.ofUnique (Fin 0 → X) PUnit)
        (Equiv.ofUnique (Fin 0 → Y) PUnit) (Equiv.ofUnique (Fin 0 → Z) PUnit)
        unitTensor = Tensor.power T 0 := by
      funext x y z
      simp [Tensor.pullback, Tensor.power, unitTensor]
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _
  | succ n ih =>
    rw [pow_succ', ← ih, ofTensor_mul]
    have heq : Tensor.pullback (finSuccFunctions n X) (finSuccFunctions n Y)
        (finSuccFunctions n Z) (Tensor.product T (Tensor.power T n)) =
        Tensor.power T (n + 1) := by
      funext x y z
      simp [Tensor.pullback, Tensor.product, Tensor.power, finSuccFunctions,
        Fin.prod_univ_succ]
    rw [← heq]
    exact ofTensor_pullback_equiv _ _ _ _

-- 读法：`ofTensor (Tensor.directSum (fun _ : Fin n => T))` 等于 `(n : TensorClass) * ofTensor T`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem ofTensor_directSum_const {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (n : ℕ) :
    ofTensor (Tensor.directSum (fun _ : Fin n => T)) =
      (n : TensorClass) * ofTensor T := by
  rw [natCast_eq_ofTensor_natTensor, ofTensor_mul]
  congr 1
  funext x y z
  simp only [Tensor.directSum, Tensor.product, CoefficientTensor.natTensor]
  split_ifs <;> simp

-- 读法：`f (ofTensor (Tensor.power T n))` 等于 `(f (ofTensor T)) ^ n`。这里调用 `f.toHom.map_pow`。
theorem Character.map_power_tensor (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.power T n)) = (f (ofTensor T)) ^ n := by
  rw [ofTensor_power]
  exact f.toHom.map_pow _ _

-- 读法：`f (ofTensor (Tensor.directSum (fun _ : Fin n => T)))` 等于 `(n : ℝ≥0) * f (ofTensor T)`。
theorem Character.map_directSum_const (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.directSum (fun _ : Fin n => T))) =
      (n : ℝ≥0) * f (ofTensor T) := by
  rw [ofTensor_directSum_const, Character.map_mul, Character.map_natCast]

end OAI.LinearAlgebra.MatrixExponent.Upper.TensorClass
