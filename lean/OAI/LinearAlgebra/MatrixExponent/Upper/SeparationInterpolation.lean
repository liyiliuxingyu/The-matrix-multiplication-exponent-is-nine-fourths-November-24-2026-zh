-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Tactic.Choose

open OAI.LinearAlgebra.MatrixExponent

/-!
# 通过具体张量限制提取多项式系数

次数有界的多项式张量的每个系数，都可写成在同一组插值节点上的取值的线性组合。若各值都是同一源张量的局部限制，则该系数是相应数量的源副本的完整直和的限制。将这一论证用于张量幂，即得到关于限制单调的特征标所需的线性插值开销。无须假设特征标在欧氏闭包上连续。

**英文原文**

Polynomial coefficient extraction by actual restrictions

Every coefficient of a bounded polynomial tensor is a linear combination of
evaluations at common interpolation nodes. If those evaluations are local
restrictions of one source tensor, the coefficient is a restriction of the
full direct sum of that many source copies. Applying this to tensor powers
gives the linear interpolation overhead required by restriction-monotone
characters. No continuity of a character on a Euclidean closure is assumed.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.Separation

section RestrictionAlgebra

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：用函数外延性比较等号两侧在 `u v w` 处的取值。
/-- 各完整源副本上的独立映射可以具有相同的目标。其结果等于这些副本限制后张量之和，没有跨副本项。

英文原文：Independent maps on each full source copy may have the same target. The
result is the sum of their restricted tensors, with no cross-copy terms.
-/
theorem restrict_directSum_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor Coeff X Y Z)
    (a : ι → U → X → Coeff) (b : ι → V → Y → Coeff) (c : ι → W → Z → Coeff) :
    Tensor.restrict (fun u x => a x.1 u x.2)
      (fun v y => b y.1 v y.2) (fun w z => c z.1 w z.2)
      (Tensor.directSum T) =
      fun u v w => ∑ i, Tensor.restrict (a i) (b i) (c i) (T i) u v w := by
  classical
  funext u v w
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, mul_ite]

-- 读法：`Tensor.restrict (fun u x => s * a u x) b c T` 等于 `fun u v w => s * Tensor.restrict a b c T u v w`。用函数外延性比较等号两侧在 `u v w` 处的取值。
/-- 按比例缩放一个局部映射，也就按同一比例缩放整个限制后的系数张量。

英文原文：Scaling one local map scales the whole restricted coefficient tensor.
-/
theorem restrict_scale_first (T : Tensor Coeff X Y Z)
    (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff) (s : Coeff) :
    Tensor.restrict (fun u x => s * a u x) b c T =
      fun u v w => s * Tensor.restrict a b c T u v w := by
  funext u v w
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

-- 读法：用函数外延性比较等号两侧在 `u v w` 处的取值。
/-- 局部映射的张量积给出每次张量幂的局部限制。在每个位置上独立地对每一个输入坐标求和。

英文原文：Tensor products of the local maps give a local restriction of every power.
Every input coordinate in every position is summed independently.
-/
theorem restrict_power (T : Tensor Coeff X Y Z)
    (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff) (j : ℕ) :
    Tensor.restrict
      (fun u x => ∏ i, a (u i) (x i))
      (fun v y => ∏ i, b (v i) (y i))
      (fun w z => ∏ i, c (w i) (z i)) (Tensor.power T j) =
      Tensor.power (Tensor.restrict a b c T) j := by
  funext u v w
  simp only [Tensor.restrict, Tensor.power, Fintype.prod_sum,
    Finset.prod_mul_distrib]

-- 读法：`Tensor.power S j` 属于 `LocalTensor.orbit (Tensor.power T j)`。
theorem power_mem_restrictionOrbit {T : Tensor Coeff X Y Z}
    {S : Tensor Coeff U V W} (h : S ∈ LocalTensor.orbit T) (j : ℕ) :
    Tensor.power S j ∈ LocalTensor.orbit (Tensor.power T j) := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨(fun u x => ∏ i, a (u i) (x i)),
    (fun v y => ∏ i, b (v i) (y i)),
    (fun w z => ∏ i, c (w i) (z i)), (restrict_power T a b c j).symm⟩

end RestrictionAlgebra

section Interpolation

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`(fun u v w => (P u v w).coeff d)` 属于 `LocalTensor.orbit (Tensor.directSum (fun _ : ι => T))`。
/-- 在任取的一组共用、互异且非零的节点上进行插值，就能将实现各求值的限制映射合成为实现相应系数的单个限制。使用的全部源副本均明确计入成本。

英文原文：Interpolation at any common family of distinct nonzero nodes turns actual
restriction witnesses for the evaluations into one restriction witness for the
coefficient. The full number of source copies is charged explicitly.
-/
theorem polynomial_coeff_mem_restrictionOrbit {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Tensor Coeff X Y Z) (P : Tensor (Polynomial Coeff) U V W)
    (nodes : ι → Coeff) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (hdegree : ∀ u v w, (P u v w).degree < Fintype.card ι) (d : ℕ) :
    (fun u v w => (P u v w).coeff d) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : ι => T)) := by
  classical
  have hex : ∀ i : ι, ∃ (a : U → X → Coeff) (b : V → Y → Coeff)
      (c : W → Z → Coeff),
      (fun u v w => (P u v w).eval (nodes i)) = Tensor.restrict a b c T := by
    intro i
    exact heval (nodes i) (hnonzero i)
  choose a b c hrestriction using hex
  -- 推导：记下中间结论 `weight`：`ι → Coeff`。
  let weight : ι → Coeff := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  refine ⟨(fun u x => weight x.1 * a x.1 u x.2),
    (fun v y => b y.1 v y.2), (fun w z => c z.1 w z.2), ?_⟩
  rw [restrict_directSum_sum (fun _ : ι => T) (fun i u x => weight i * a i u x) b c]
  funext u v w
  rw [Tensor.coeff_eq_sum_eval nodes hinj _ d (hdegree u v w)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [restrict_scale_first]
  have h := congrFun (congrFun (congrFun (hrestriction i) u) v) w
  dsimp [weight]
  rw [h]
  ring

-- 读法：`(fun u v w => (Tensor.power P j u v w).coeff 0)` 等于 `Tensor.power (fun u v w => (P u v w).coeff 0) j`。用函数外延性比较等号两侧在 `u v w` 处的取值。
theorem polynomial_power_constant (P : Tensor (Polynomial Coeff) U V W) (j : ℕ) :
    (fun u v w => (Tensor.power P j u v w).coeff 0) =
      Tensor.power (fun u v w => (P u v w).coeff 0) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.coeff_zero_prod]

-- 读法：`(fun u v w => (Tensor.power P j u v w).eval t)` 等于 `Tensor.power (fun u v w => (P u v w).eval t) j`。用函数外延性比较等号两侧在 `u v w` 处的取值。
theorem polynomial_power_eval (P : Tensor (Polynomial Coeff) U V W) (j : ℕ) (t : Coeff) :
    (fun u v w => (Tensor.power P j u v w).eval t) =
      Tensor.power (fun u v w => (P u v w).eval t) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.eval_prod]

-- 读法：`(Tensor.power P j u v w).degree` 不超过 `K * j`。这里调用 `Polynomial.degree_le_of_natDegree_le`。
theorem polynomial_power_degree (P : Tensor (Polynomial Coeff) U V W) (K j : ℕ)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (u : Fin j → U) (v : Fin j → V) (w : Fin j → W) :
    (Tensor.power P j u v w).degree ≤ K * j := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (Tensor.power P j u v w).natDegree ≤
        ∑ i, (P (u i) (v i) (w i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin j, K := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_le_of_degree_le (hdegree (u i) (v i) (w i))
    _ = K * j := by simp [Nat.mul_comm]

-- 读法：`Tensor.power D j` 属于 `LocalTensor.orbit (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j))`。这里调用 `power_mem_restrictionOrbit`。
/-- 应用特征标前的有限插值界。对每个幂次 `j`，取原源张量的该次幂的恰好 `K*j+1` 个副本就足够了。所需的互异非零节点可从无限域中选取。

英文原文：The finite interpolation bound before applying any character. For every
power `j`, exactly `K*j+1` copies of the power of the original source suffice.
The infinite field supplies distinct nonzero nodes.
-/
theorem polynomial_power_mem_restrictionOrbit
    (T : Tensor Coeff X Y Z) (D : Tensor Coeff U V W)
    (P : Tensor (Polynomial Coeff) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (j : ℕ) :
    Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j)) := by
  classical
  -- 推导：从 `exists_nonzero_nodes (F := Coeff) (K * j + 1)` 中取出 `nodes, hinj, hnonzero`。
  obtain ⟨nodes, hinj, hnonzero⟩ := exists_nonzero_nodes (F := Coeff) (K * j + 1)
  have hevalpower : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (Tensor.power P j u v w).eval t) ∈
        LocalTensor.orbit (Tensor.power T j) := by
    intro t ht
    rw [polynomial_power_eval]
    exact power_mem_restrictionOrbit (heval t ht) j
  have hdegreepower : ∀ u v w, (Tensor.power P j u v w).degree <
      Fintype.card (Fin (K * j + 1)) := by
    intro u v w
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (polynomial_power_degree P K j hdegree u v w)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (K * j)))
  have h := polynomial_coeff_mem_restrictionOrbit (Tensor.power T j) (Tensor.power P j)
    nodes hinj hnonzero hevalpower hdegreepower 0
  -- 推导：记下中间结论 `hD`：`(fun u v w => (P u v w).coeff 0) = D`。
  have hD : (fun u v w => (P u v w).coeff 0) = D := by
    funext u v w
    exact hconstant u v w
  rw [polynomial_power_constant, hD] at h
  exact h

end Interpolation

end OAI.LinearAlgebra.MatrixExponent.Upper.Separation
