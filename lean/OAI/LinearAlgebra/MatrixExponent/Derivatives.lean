-- 本文件所属证明环节：在矩阵输入变量的有理函数域中构造并使用偏导数，为从电路门提取双线性部分提供代数工具。
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# 泛点处的偏导数

用一个平方为零的变量扰动一个输入。投影到常数项是恒等映射，因而每个非零多项式都映到可逆元。这样，在任意特征下扰动都可延拓到有理函数。

**英文原文**

Partial derivatives at the generic point

Perturb one input by a square-zero variable. Projection to the constant
term is the identity, so every nonzero polynomial maps to a unit. The
perturbation thus extends to rational functions in any characteristic.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type*} [Field F] {σ : Type}

local notation "P" => MvPolynomial σ F
local notation "K" => FractionRing P

-- 读法：`shiftedX` 的结果类型为 `DualNumber K`。
private def shiftedX (i j : σ) : DualNumber K := by
  classical
  exact (algebraMap P K (MvPolynomial.X j), if i = j then 1 else 0)

-- 读法：`shiftPoly` 的取值由 `MvPolynomial.aeval (shiftedX i)` 给出。
private def shiftPoly (i : σ) : P →ₐ[F] DualNumber K :=
  MvPolynomial.aeval (shiftedX i)

-- 读法：`(shiftPoly i p).fst` 等于 `algebraMap P K p`。这里调用 `MvPolynomial.algHom_ext`。
private theorem fst_shiftPoly (i : σ) (p : P) :
    (shiftPoly i p).fst = algebraMap P K p := by
  have h : (TrivSqZeroExt.fstHom F K K).comp (shiftPoly i) = Algebra.algHom F P K := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, shiftPoly, MvPolynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun h p

-- 读法：要证明的命题是 `IsUnit (shiftPoly (F := F) i p)`。这里调用 `IsLocalization.map_units`。
private theorem shiftPoly_unit (i : σ) (p : nonZeroDivisors P) :
    IsUnit (shiftPoly (F := F) i p) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_shiftPoly]
  exact IsLocalization.map_units K p

-- 读法：`shift` 的取值由 `IsLocalization.liftAlgHom (shiftPoly_unit i)` 给出。
private def shift (i : σ) : K →ₐ[F] DualNumber K :=
  IsLocalization.liftAlgHom (shiftPoly_unit i)

-- 读法：`shift i (algebraMap P K p)` 等于 `shiftPoly i p`。使用 `IsLocalization.lift_eq` 给出的结论。
private theorem shift_poly (i : σ) (p : P) :
    shift i (algebraMap P K p) = shiftPoly i p :=
  IsLocalization.lift_eq (shiftPoly_unit i) p

-- 读法：`(shift i x).fst` 等于 `x`。这里调用 `IsLocalization.algHom_ext`。
private theorem fst_shift (i : σ) (x : K) : (shift i x).fst = x := by
  have h : (TrivSqZeroExt.fstHom F K K).comp (shift i) = AlgHom.id F K := by
    apply IsLocalization.algHom_ext (nonZeroDivisors P)
    apply AlgHom.ext
    intro p
    change (shift i (algebraMap P K p)).fst = algebraMap P K p
    rw [shift_poly, fst_shiftPoly]
  exact DFunLike.congr_fun h x

-- 读法：用字段 `toLinearMap`、`map_one_eq_zero'`、`change`、`simp` 构造 `Derivation F K K`。
/-- 有理函数域上的形式偏微分。

英文原文：Formal partial differentiation on the field of rational functions.
-/
def partialD (i : σ) : Derivation F K K where
  toLinearMap := ((TrivSqZeroExt.sndHom K K).restrictScalars F).comp (shift i).toLinearMap
  map_one_eq_zero' := by
    change (shift (F := F) i 1).snd = 0
    simp
  leibniz' x y := by
    change (shift i (x * y)).snd = x * (shift i y).snd + y * (shift i x).snd
    rw [map_mul, DualNumber.snd_mul, fst_shift, fst_shift, mul_comm _ y]

-- 读法：`partialD (F := F) i (algebraMap P K (MvPolynomial.X j))` 等于 `if i = j then 1 else 0`。按 `i = j <;> simp [shiftedX, h, TrivSqZeroExt.snd]` 成立与否分情况。
@[simp] theorem partialD_X [DecidableEq σ] (i j : σ) :
    partialD (F := F) i (algebraMap P K (MvPolynomial.X j)) = if i = j then 1 else 0 := by
  change (shift i (algebraMap P K (MvPolynomial.X j))).snd = _
  rw [shift_poly, shiftPoly, MvPolynomial.aeval_X]
  by_cases h : i = j <;> simp [shiftedX, h, TrivSqZeroExt.snd]

end OAI.LinearAlgebra.MatrixExponent
