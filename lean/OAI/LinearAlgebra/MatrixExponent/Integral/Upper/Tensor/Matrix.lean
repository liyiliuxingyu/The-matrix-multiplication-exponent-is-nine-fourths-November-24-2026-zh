-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Rank
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import Mathlib.Logic.Equiv.Fin.Basic

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# 限制半环中的方阵乘法张量

维数比较与乘法均由具体的坐标映射给出见证。三次的秩上界来自对三个矩阵索引的通常求和。

**英文原文**

Square matrix tensors in the restriction semiring

Dimension comparisons and multiplication are witnessed by the actual coordinate
maps. The cubic rank bound uses the ordinary sum over the three matrix indices.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper
namespace CoefficientTensor

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 索引上的单射保持矩阵张量的三项共享索引相等条件，对取零的系数也成立。

英文原文：Injective index maps preserve all three shared-index equalities of a matrix
tensor, including its zero coefficients.
-/
theorem matrixCoefficients_pullback_injective
    {K A B C X Y Z : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (a : X → A) (b : Y → B) (c : Z → C)
    (ha : Function.Injective a) (hb : Function.Injective b) (hc : Function.Injective c) :
    Tensor.pullback (Prod.map a b) (Prod.map b c) (Prod.map c a)
      (Tensor.matrixCoefficients (K := K) A B C) =
      Tensor.matrixCoefficients (K := K) X Y Z := by
  funext x y z
  change (if b x.2 = b y.1 ∧ c y.2 = c z.1 ∧ a z.2 = a x.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  simp only [ha.eq_iff, hb.eq_iff, hc.eq_iff]

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `((Fin n × Fin n) × (Fin m × Fin m)) ≃ (Fin (n * m) × Fin (n * m))`。
/-- 分别将行索引配对、列索引配对，再用与 `Fin (n * m)` 的标准等价对每一对编号。

英文原文：Pair the row indices and column indices separately, then enumerate each
pair by the standard equivalence with `Fin (n * m)`.
-/
def squareProductCoordinates (n m : ℕ) :
    ((Fin n × Fin n) × (Fin m × Fin m)) ≃ (Fin (n * m) × Fin (n * m)) where
  toFun p := (finProdFinEquiv (p.1.1, p.2.1), finProdFinEquiv (p.1.2, p.2.2))
  invFun p :=
    ((((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.1).1,
        ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.2).1),
      (((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.1).2,
        ((finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m)).symm p.2).2))
  left_inv p := by
    rcases p with ⟨⟨i, j⟩, ⟨u, v⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨i, j⟩
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 对各个局部坐标空间作显式的双射重标号后，两个方阵乘法张量的积就是规模更大的方阵乘法张量。

英文原文：The product of two square matrix tensors is the larger square tensor under
an explicit bijective relabeling of each local coordinate space.
-/
theorem square_product_pullback (n m : ℕ) :
    Tensor.pullback (squareProductCoordinates n m) (squareProductCoordinates n m)
      (squareProductCoordinates n m) (Upper.matrixTensor (n * m) (n * m) (n * m)) =
      Tensor.product (Upper.matrixTensor n n n) (Upper.matrixTensor m m m) := by
  let e : (Fin n × Fin m) ≃ Fin (n * m) := finProdFinEquiv
  have he := matrixCoefficients_pullback_injective (K := O) e e e
    e.injective e.injective e.injective
  funext x y z
  let x' : (Fin n × Fin m) × (Fin n × Fin m) := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  let y' : (Fin n × Fin m) × (Fin n × Fin m) := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  let z' : (Fin n × Fin m) × (Fin n × Fin m) := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  calc
    _ = Tensor.matrixCoefficients (K := O) (Fin n × Fin m) (Fin n × Fin m)
        (Fin n × Fin m) x' y' z' := congrFun (congrFun (congrFun he x') y') z'
    _ = _ := (Tensor.matrixCoefficients_product (K := O) x' y' z').symm

-- 读法：要证明的命题是 `Restricts (Upper.matrixTensor m m m) (Upper.matrixTensor n n n)`。按 `Fin.ext` 的外延性准则比较各分量。
/-- 在每个矩阵方向上取前 `n` 个索引，即给出较大矩阵乘法张量的一个实际局部限制。

英文原文：Taking the first `n` indices in each matrix direction is an actual local
restriction of the larger matrix multiplication tensor.
-/
theorem square_restricts_of_le {n m : ℕ} (h : n ≤ m) :
    Restricts (Upper.matrixTensor m m m) (Upper.matrixTensor n n n) := by
  let e : Fin n → Fin m := fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin m => k.val) hij
  have hr := Restricts.pullback (Upper.matrixTensor m m m)
    (Prod.map e e) (Prod.map e e) (Prod.map e e)
  have hp := matrixCoefficients_pullback_injective (K := O) e e e he he he
  change Tensor.pullback (Prod.map e e) (Prod.map e e) (Prod.map e e)
    (Upper.matrixTensor m m m) = Upper.matrixTensor n n n at hp
  rwa [hp] at hr

-- 读法：张量 `(Upper.matrixTensor n n n)` 的秩至多为 `(n ^ 3)`。
/-- 通常的立方规模张量分解。每个矩阵索引三元组对应一项，无须为环境空间中的每个系数各设一项。

英文原文：The usual cubic tensor decomposition, with one term for each triple of
matrix indices rather than one term for each ambient coefficient.
-/
theorem square_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Upper.matrixTensor n n n) (n ^ 3) := by
  let a : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → O :=
    fun p x => if p.1 = x.1 ∧ p.2.1 = x.2 then 1 else 0
  let b : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → O :=
    fun p y => if p.2.1 = y.1 ∧ p.2.2 = y.2 then 1 else 0
  let c : (Fin n × Fin n × Fin n) → (Fin n × Fin n) → O :=
    fun p z => if p.2.2 = z.1 ∧ z.2 = p.1 then 1 else 0
  have hr := Tensor.rankAtMost_sum_rankOne a b c
  have heq : (fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z) =
      Upper.matrixTensor n n n := by
    funext x y z
    rw [Finset.sum_eq_single (x.1, x.2, y.2)]
    · by_cases hxy : x.2 = y.1 <;> by_cases hyz : y.2 = z.1 <;>
        by_cases hzx : z.2 = x.1 <;>
          simp [a, b, c, Tensor.rankOne, Upper.matrixTensor, Tensor.matrixCoefficients, hxy, hyz, hzx]
    · intro p hp hne
      by_cases hi : p.1 = x.1
      · by_cases hj : p.2.1 = x.2
        · by_cases hk : p.2.2 = y.2
          · exact (hne (Prod.ext hi (Prod.ext hj hk))).elim
          · simp [a, b, c, Tensor.rankOne, hk]
        · simp [a, b, c, Tensor.rankOne, hj]
      · simp [a, b, c, Tensor.rankOne, hi]
    · simp
  rw [heq] at hr
  simpa [Fintype.card_prod, Fintype.card_fin, pow_succ, mul_assoc] using hr

end CoefficientTensor

namespace TensorClass

-- 读法：`square` 的取值由 `ofTensor (Upper.matrixTensor n n n)` 给出。
/-- 实际的 `n` 乘 `n` 方阵乘法张量所属的类。

英文原文：The class of the actual `n` by `n` matrix multiplication tensor.
-/
noncomputable def square (n : ℕ) : TensorClass :=
  ofTensor (Upper.matrixTensor n n n)

-- 读法：`square n * square m` 等于 `square (n * m)`。这里调用 `ofTensor_pullback_equiv`。
theorem square_mul (n m : ℕ) : square n * square m = square (n * m) := by
  unfold square
  rw [ofTensor_mul, ← CoefficientTensor.square_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

-- 读法：`square n` 不超过 `square m`。使用 `ofTensor_le` 给出的结论。
theorem square_mono {n m : ℕ} (h : n ≤ m) : square n ≤ square m :=
  ofTensor_le (CoefficientTensor.square_restricts_of_le h)

-- 读法：`square 1` 等于 `1`。用函数外延性比较等号两侧在 `x y z` 处的取值。
@[simp] theorem square_one : square 1 = 1 := by
  let e : (Fin 1 × Fin 1) ≃ PUnit :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => (0, 0)
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  have heq : Tensor.pullback e e e unitTensor = Upper.matrixTensor 1 1 1 := by
    funext x y z
    have h₁ : x.2 = y.1 := Subsingleton.elim _ _
    have h₂ : y.2 = z.1 := Subsingleton.elim _ _
    have h₃ : z.2 = x.1 := Subsingleton.elim _ _
    simp [Tensor.pullback, unitTensor, Upper.matrixTensor, Tensor.matrixCoefficients, h₁, h₂, h₃]
  change ofTensor (Upper.matrixTensor 1 1 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e e e

-- 读法：`square (n ^ j)` 等于 `square n ^ j`。对 `j` 作归纳。
theorem square_pow (n j : ℕ) : square (n ^ j) = square n ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, ← square_mul, ih, pow_succ]

-- 读法：`rank (square n)` 不超过 `n ^ 3`。这里调用 `CoefficientTensor.rank_le_iff`。
/-- 这里的秩是实际秩一张量分解的最小项数。

英文原文：The rank here is the least size of an actual rank-one decomposition.
-/
theorem rank_square_le (n : ℕ) : rank (square n) ≤ n ^ 3 := by
  rw [square, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr
    (CoefficientTensor.square_rankAtMost_cubic n)

-- 读法：`rank (square n)` 不超过 `n ^ 3`。使用 `rank_square_le` 给出的结论。
theorem square_rank_upper (n : ℕ) : rank (square n) ≤ n ^ 3 := rank_square_le n

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
