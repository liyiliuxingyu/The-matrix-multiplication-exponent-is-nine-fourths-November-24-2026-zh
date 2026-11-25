-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Matrix
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.RankOrder

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 将三种辅助配对实现为具体张量类

每种配对都以其单点腿命名。比较维数时选取坐标，取乘积时将坐标配对，三个不同取向配对的乘积即为方阵乘法张量。

**英文原文**

The three auxiliary pairings as actual tensor classes

The singleton leg is named in each pairing. Dimension comparisons select
coordinates, multiplication pairs coordinates, and the product of the three
orientations is the square matrix multiplication tensor.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper
namespace CoefficientTensor

-- 读法：当 `y = z` 成立时取 `1`，否则取 `0`。
def dotXCoeff (n : ℕ) : Tensor O Unit (Fin n) (Fin n) :=
  fun _ y z => if y = z then 1 else 0

-- 读法：当 `x = z` 成立时取 `1`，否则取 `0`。
def dotYCoeff (n : ℕ) : Tensor O (Fin n) Unit (Fin n) :=
  fun x _ z => if x = z then 1 else 0

-- 读法：当 `x = y` 成立时取 `1`，否则取 `0`。
def dotZCoeff (n : ℕ) : Tensor O (Fin n) (Fin n) Unit :=
  fun x y _ => if x = y then 1 else 0

-- 读法：要证明的命题是 `Restricts (dotXCoeff n) (dotXCoeff m)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotX_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotXCoeff n) (dotXCoeff m) := by
  have hp := Restricts.pullback (dotXCoeff n) id (Fin.castLE h) (Fin.castLE h)
  have heq : Tensor.pullback id (Fin.castLE h) (Fin.castLE h) (dotXCoeff n) =
      dotXCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotXCoeff, Fin.ext_iff]
  rwa [heq] at hp

-- 读法：要证明的命题是 `Restricts (dotYCoeff n) (dotYCoeff m)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotY_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotYCoeff n) (dotYCoeff m) := by
  have hp := Restricts.pullback (dotYCoeff n) (Fin.castLE h) id (Fin.castLE h)
  have heq : Tensor.pullback (Fin.castLE h) id (Fin.castLE h) (dotYCoeff n) =
      dotYCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotYCoeff, Fin.ext_iff]
  rwa [heq] at hp

-- 读法：要证明的命题是 `Restricts (dotZCoeff n) (dotZCoeff m)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotZ_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotZCoeff n) (dotZCoeff m) := by
  have hp := Restricts.pullback (dotZCoeff n) (Fin.castLE h) (Fin.castLE h) id
  have heq : Tensor.pullback (Fin.castLE h) (Fin.castLE h) id (dotZCoeff n) =
      dotZCoeff m := by
    funext x y z
    simp [Tensor.pullback, dotZCoeff, Fin.ext_iff]
  rwa [heq] at hp

-- 读法：张量 `(dotXCoeff n)` 的秩至多为 `n`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotX_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotXCoeff n) n := by
  refine ⟨fun _ _ => 1, fun i y => if i = y then 1 else 0,
    fun i z => if i = z then 1 else 0, ?_⟩
  funext x y z
  simp [dotXCoeff, Tensor.rankOne, mul_ite, eq_comm]

-- 读法：张量 `(dotYCoeff n)` 的秩至多为 `n`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotY_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotYCoeff n) n := by
  refine ⟨fun i x => if i = x then 1 else 0, fun _ _ => 1,
    fun i z => if i = z then 1 else 0, ?_⟩
  funext x y z
  simp [dotYCoeff, Tensor.rankOne, mul_ite, eq_comm]

-- 读法：张量 `(dotZCoeff n)` 的秩至多为 `n`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotZ_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotZCoeff n) n := by
  refine ⟨fun i x => if i = x then 1 else 0,
    fun i y => if i = y then 1 else 0, fun _ _ => 1, ?_⟩
  funext x y z
  simp [dotZCoeff, Tensor.rankOne, mul_ite, eq_comm]

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Unit × Unit) ≃ Unit`。
def dotUnitProduct : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv x := by rcases x with ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv x := by cases x; rfl

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotX_product_pullback (m n : ℕ) :
    Tensor.pullback dotUnitProduct
      (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)) finProdFinEquiv
      (dotXCoeff (m * n)) = Tensor.product (dotXCoeff m) (dotXCoeff n) := by
  funext x y z
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  by_cases h₁ : y₁ = z₁ <;> by_cases h₂ : y₂ = z₂ <;>
    simp [Tensor.pullback, dotXCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotY_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      dotUnitProduct finProdFinEquiv (dotYCoeff (m * n)) =
      Tensor.product (dotYCoeff m) (dotYCoeff n) := by
  funext x y z
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  by_cases h₁ : x₁ = z₁ <;> by_cases h₂ : x₂ = z₂ <;>
    simp [Tensor.pullback, dotYCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotZ_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      finProdFinEquiv dotUnitProduct (dotZCoeff (m * n)) =
      Tensor.product (dotZCoeff m) (dotZCoeff n) := by
  funext x y z
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
    simp [Tensor.pullback, dotZCoeff, Tensor.product, Prod.mk.injEq, h₁, h₂]

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `((Unit × Fin n) × Fin n) ≃ (Fin n × Fin n)`。
/-- 第一条腿上的两个非单点坐标分别成为行指标和列指标。

英文原文：The two nonsingleton coordinates on the first leg become row and column.
-/
def dotTripleX (n : ℕ) : ((Unit × Fin n) × Fin n) ≃ (Fin n × Fin n) where
  toFun x := (x.1.2, x.2)
  invFun x := (((), x.1), x.2)
  left_inv x := by rcases x with ⟨⟨⟨⟩, i⟩, j⟩; rfl
  right_inv x := by cases x; rfl

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `((Fin n × Unit) × Fin n) ≃ (Fin n × Fin n)`。
/-- 中间一条腿将第二个索引与第三个配对。

英文原文：The middle leg pairs the second index with the third.
-/
def dotTripleY (n : ℕ) : ((Fin n × Unit) × Fin n) ≃ (Fin n × Fin n) where
  toFun y := (y.2, y.1.1)
  invFun y := ((y.2, ()), y.1)
  left_inv y := by rcases y with ⟨⟨i, ⟨⟩⟩, j⟩; rfl
  right_inv y := by cases y; rfl

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `((Fin n × Fin n) × Unit) ≃ (Fin n × Fin n)`。
/-- 最后一条腿将第三个索引与第一个配对。

英文原文：The final leg pairs the third index with the first.
-/
def dotTripleZ (n : ℕ) : ((Fin n × Fin n) × Unit) ≃ (Fin n × Fin n) where
  toFun z := z.1
  invFun z := (z, ())
  left_inv z := by rcases z with ⟨⟨i, j⟩, ⟨⟩⟩; rfl
  right_inv z := rfl

-- 读法：`Tensor.pullback (dotTripleX n) (dotTripleY n) (dotTripleZ n) (Upper.matrixTensor n n n)` 等于 `Tensor.product (Tensor.product (dotXCoeff n) (dotYCoeff n)) (dotZCoeff n)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem dotTriple_pullback (n : ℕ) :
    Tensor.pullback (dotTripleX n) (dotTripleY n) (dotTripleZ n)
      (Upper.matrixTensor n n n) =
      Tensor.product (Tensor.product (dotXCoeff n) (dotYCoeff n)) (dotZCoeff n) := by
  funext x y z
  by_cases hx : x.1.2 = z.1.2 <;>
    by_cases hy : y.1.1 = z.1.1 <;>
    by_cases hz : x.2 = y.2 <;>
    simp [Tensor.pullback, Upper.matrixTensor, Tensor.matrixCoefficients, Tensor.product,
      dotTripleX, dotTripleY, dotTripleZ, dotXCoeff, dotYCoeff, dotZCoeff,
      hx, hy, hz, eq_comm]

end CoefficientTensor

namespace TensorClass

-- 读法：`dotX` 的取值由 `ofTensor (CoefficientTensor.dotXCoeff n)` 给出。
noncomputable def dotX (n : ℕ) : TensorClass := ofTensor (CoefficientTensor.dotXCoeff n)
-- 读法：`dotY` 的取值由 `ofTensor (CoefficientTensor.dotYCoeff n)` 给出。
noncomputable def dotY (n : ℕ) : TensorClass := ofTensor (CoefficientTensor.dotYCoeff n)
-- 读法：`dotZ` 的取值由 `ofTensor (CoefficientTensor.dotZCoeff n)` 给出。
noncomputable def dotZ (n : ℕ) : TensorClass := ofTensor (CoefficientTensor.dotZCoeff n)

-- 读法：`dotX m` 不超过 `dotX n`。使用 `ofTensor_le` 给出的结论。
theorem dotX_mono {m n : ℕ} (h : m ≤ n) : dotX m ≤ dotX n :=
  ofTensor_le (CoefficientTensor.dotX_restricts_of_le h)

-- 读法：`dotY m` 不超过 `dotY n`。使用 `ofTensor_le` 给出的结论。
theorem dotY_mono {m n : ℕ} (h : m ≤ n) : dotY m ≤ dotY n :=
  ofTensor_le (CoefficientTensor.dotY_restricts_of_le h)

-- 读法：`dotZ m` 不超过 `dotZ n`。使用 `ofTensor_le` 给出的结论。
theorem dotZ_mono {m n : ℕ} (h : m ≤ n) : dotZ m ≤ dotZ n :=
  ofTensor_le (CoefficientTensor.dotZ_restricts_of_le h)

-- 读法：`rank (dotX n)` 不超过 `n`。这里调用 `CoefficientTensor.rank_le_iff`。
theorem rank_dotX_le (n : ℕ) : rank (dotX n) ≤ n := by
  rw [dotX, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotX_rankAtMost n)

-- 读法：`rank (dotY n)` 不超过 `n`。这里调用 `CoefficientTensor.rank_le_iff`。
theorem rank_dotY_le (n : ℕ) : rank (dotY n) ≤ n := by
  rw [dotY, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotY_rankAtMost n)

-- 读法：`rank (dotZ n)` 不超过 `n`。这里调用 `CoefficientTensor.rank_le_iff`。
theorem rank_dotZ_le (n : ℕ) : rank (dotZ n) ≤ n := by
  rw [dotZ, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.dotZ_rankAtMost n)

-- 读法：`dotX m * dotX n` 等于 `dotX (m * n)`。这里调用 `ofTensor_pullback_equiv`。
theorem dotX_mul (m n : ℕ) : dotX m * dotX n = dotX (m * n) := by
  unfold dotX
  rw [ofTensor_mul, ← CoefficientTensor.dotX_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

-- 读法：`dotY m * dotY n` 等于 `dotY (m * n)`。这里调用 `ofTensor_pullback_equiv`。
theorem dotY_mul (m n : ℕ) : dotY m * dotY n = dotY (m * n) := by
  unfold dotY
  rw [ofTensor_mul, ← CoefficientTensor.dotY_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

-- 读法：`dotZ m * dotZ n` 等于 `dotZ (m * n)`。这里调用 `ofTensor_pullback_equiv`。
theorem dotZ_mul (m n : ℕ) : dotZ m * dotZ n = dotZ (m * n) := by
  unfold dotZ
  rw [ofTensor_mul, ← CoefficientTensor.dotZ_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

-- 读法：`dotX 1` 等于 `1`。用函数外延性比较等号两侧在 `x y z` 处的取值。
@[simp] theorem dotX_one : dotX 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback u e e unitTensor = CoefficientTensor.dotXCoeff 1 := by
    funext x y z
    simp [Tensor.pullback, unitTensor, CoefficientTensor.dotXCoeff, Subsingleton.elim y z]
  change ofTensor (CoefficientTensor.dotXCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ u e e

-- 读法：`dotY 1` 等于 `1`。用函数外延性比较等号两侧在 `x y z` 处的取值。
@[simp] theorem dotY_one : dotY 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback e u e unitTensor = CoefficientTensor.dotYCoeff 1 := by
    funext x y z
    simp [Tensor.pullback, unitTensor, CoefficientTensor.dotYCoeff, Subsingleton.elim x z]
  change ofTensor (CoefficientTensor.dotYCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e u e

-- 读法：`dotZ 1` 等于 `1`。用函数外延性比较等号两侧在 `x y z` 处的取值。
@[simp] theorem dotZ_one : dotZ 1 = 1 := by
  let u : Unit ≃ PUnit := Equiv.ofUnique _ _
  let e : Fin 1 ≃ PUnit := Equiv.ofUnique _ _
  have heq : Tensor.pullback e e u unitTensor = CoefficientTensor.dotZCoeff 1 := by
    funext x y z
    simp [Tensor.pullback, unitTensor, CoefficientTensor.dotZCoeff, Subsingleton.elim x y]
  change ofTensor (CoefficientTensor.dotZCoeff 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e e u

-- 读法：`1` 不超过 `dotX n`。这里调用 `dotX_mono`。
theorem one_le_dotX {n : ℕ} (hn : 0 < n) : 1 ≤ dotX n := by
  simpa only [dotX_one] using dotX_mono (Nat.succ_le_iff.mpr hn)

-- 读法：`1` 不超过 `dotY n`。这里调用 `dotY_mono`。
theorem one_le_dotY {n : ℕ} (hn : 0 < n) : 1 ≤ dotY n := by
  simpa only [dotY_one] using dotY_mono (Nat.succ_le_iff.mpr hn)

-- 读法：`1` 不超过 `dotZ n`。这里调用 `dotZ_mono`。
theorem one_le_dotZ {n : ℕ} (hn : 0 < n) : 1 ≤ dotZ n := by
  simpa only [dotZ_one] using dotZ_mono (Nat.succ_le_iff.mpr hn)

-- 读法：`dotX n * dotY n * dotZ n` 等于 `square n`。这里调用 `ofTensor_pullback_equiv`。
theorem dotX_mul_dotY_mul_dotZ (n : ℕ) : dotX n * dotY n * dotZ n = square n := by
  unfold dotX dotY dotZ square
  rw [ofTensor_mul, ofTensor_mul, ← CoefficientTensor.dotTriple_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

namespace Character

-- 读法：`f (dotX n)` 不超过 `n`。通过传递性衔接 `f.le_rank` 与 `Nat.cast_le.mpr`。
theorem dotX_le (f : Character) (n : ℕ) : f (dotX n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotX_le n))

-- 读法：`f (dotY n)` 不超过 `n`。通过传递性衔接 `f.le_rank` 与 `Nat.cast_le.mpr`。
theorem dotY_le (f : Character) (n : ℕ) : f (dotY n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotY_le n))

-- 读法：`f (dotZ n)` 不超过 `n`。通过传递性衔接 `f.le_rank` 与 `Nat.cast_le.mpr`。
theorem dotZ_le (f : Character) (n : ℕ) : f (dotZ n) ≤ n :=
  (f.le_rank _).trans (Nat.cast_le.mpr (rank_dotZ_le n))

-- 读法：`1` 不超过 `f (dotX n)`。这里调用 `f.monotone'`。
theorem one_le_dotX (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotX n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotX hn)

-- 读法：`1` 不超过 `f (dotY n)`。这里调用 `f.monotone'`。
theorem one_le_dotY (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotY n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotY hn)

-- 读法：`1` 不超过 `f (dotZ n)`。这里调用 `f.monotone'`。
theorem one_le_dotZ (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotZ n) := by
  simpa only [map_one] using f.monotone' (TensorClass.one_le_dotZ hn)

-- 读法：`dotXValue` 的取值由 `f (dotX n)` 给出。
noncomputable def dotXValue (f : Character) (n : ℕ) : ℝ := f (dotX n)
-- 读法：`dotYValue` 的取值由 `f (dotY n)` 给出。
noncomputable def dotYValue (f : Character) (n : ℕ) : ℝ := f (dotY n)
-- 读法：`dotZValue` 的取值由 `f (dotZ n)` 给出。
noncomputable def dotZValue (f : Character) (n : ℕ) : ℝ := f (dotZ n)

-- 读法：`0` 不超过 `f.dotXValue n`。
theorem dotXValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotXValue n :=
  (f (dotX n)).coe_nonneg

-- 读法：`0` 不超过 `f.dotYValue n`。
theorem dotYValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotYValue n :=
  (f (dotY n)).coe_nonneg

-- 读法：`0` 不超过 `f.dotZValue n`。
theorem dotZValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotZValue n :=
  (f (dotZ n)).coe_nonneg

-- 读法：`f.dotXValue n` 不超过 `n`。
theorem dotXValue_le (f : Character) (n : ℕ) : f.dotXValue n ≤ n := by
  exact_mod_cast f.dotX_le n

-- 读法：`f.dotYValue n` 不超过 `n`。
theorem dotYValue_le (f : Character) (n : ℕ) : f.dotYValue n ≤ n := by
  exact_mod_cast f.dotY_le n

-- 读法：`f.dotZValue n` 不超过 `n`。
theorem dotZValue_le (f : Character) (n : ℕ) : f.dotZValue n ≤ n := by
  exact_mod_cast f.dotZ_le n

-- 读法：`1` 不超过 `f.dotXValue n`。
theorem one_le_dotXValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotXValue n := by
  exact_mod_cast f.one_le_dotX hn

-- 读法：`1` 不超过 `f.dotYValue n`。
theorem one_le_dotYValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotYValue n := by
  exact_mod_cast f.one_le_dotY hn

-- 读法：`1` 不超过 `f.dotZValue n`。
theorem one_le_dotZValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotZValue n := by
  exact_mod_cast f.one_le_dotZ hn

-- 读法：`f.dotXValue` 是单调不减的。
theorem dotXValue_mono (f : Character) : Monotone f.dotXValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotX_mono h)

-- 读法：`f.dotYValue` 是单调不减的。
theorem dotYValue_mono (f : Character) : Monotone f.dotYValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotY_mono h)

-- 读法：`f.dotZValue` 是单调不减的。
theorem dotZValue_mono (f : Character) : Monotone f.dotZValue := by
  intro m n h
  exact_mod_cast f.monotone' (TensorClass.dotZ_mono h)

-- 读法：`f.dotXValue (m * n)` 等于 `f.dotXValue m * f.dotXValue n`。
theorem dotXValue_mul (f : Character) (m n : ℕ) :
    f.dotXValue (m * n) = f.dotXValue m * f.dotXValue n := by
  simp only [dotXValue, ← dotX_mul, map_mul, NNReal.coe_mul]

-- 读法：`f.dotYValue (m * n)` 等于 `f.dotYValue m * f.dotYValue n`。
theorem dotYValue_mul (f : Character) (m n : ℕ) :
    f.dotYValue (m * n) = f.dotYValue m * f.dotYValue n := by
  simp only [dotYValue, ← dotY_mul, map_mul, NNReal.coe_mul]

-- 读法：`f.dotZValue (m * n)` 等于 `f.dotZValue m * f.dotZValue n`。
theorem dotZValue_mul (f : Character) (m n : ℕ) :
    f.dotZValue (m * n) = f.dotZValue m * f.dotZValue n := by
  simp only [dotZValue, ← dotZ_mul, map_mul, NNReal.coe_mul]

-- 读法：`f.dotXValue 1` 等于 `1`。
@[simp] theorem dotXValue_one (f : Character) : f.dotXValue 1 = 1 := by
  simp [dotXValue]

-- 读法：`f.dotYValue 1` 等于 `1`。
@[simp] theorem dotYValue_one (f : Character) : f.dotYValue 1 = 1 := by
  simp [dotYValue]

-- 读法：`f.dotZValue 1` 等于 `1`。
@[simp] theorem dotZValue_one (f : Character) : f.dotZValue 1 = 1 := by
  simp [dotZValue]

-- 读法：`f.dotXValue n * f.dotYValue n * f.dotZValue n` 等于 `f (square n)`。
theorem dotValues_product (f : Character) (n : ℕ) :
    f.dotXValue n * f.dotYValue n * f.dotZValue n = f (square n) := by
  simp only [dotXValue, dotYValue, dotZValue, ← NNReal.coe_mul, ← map_mul,
    dotX_mul_dotY_mul_dotZ]

end Character

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
