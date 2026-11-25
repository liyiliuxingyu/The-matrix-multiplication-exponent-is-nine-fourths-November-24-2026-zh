-- 本文件所属证明环节：把所有寄存器中的形式多项式投影到两组矩阵变量各为一次的双次数分量。一次乘法至多引入两个线性形式的乘积；所有输出共享这份乘积清单，因此矩阵乘法张量的秩至多为无除法程序乘法门数的两倍。
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.LinearAlgebra.SpectralBooks.Tensor
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# 从形式标量电路到张量秩

在每个乘法门处，只有两个新的线性形式乘积进入双次数为 `(1,1)` 的分量。*所有*寄存器共享一份这样的乘积列表，因此重复使用门的输出或同时计算多个矩阵分量都不会增加这项成本。

**英文原文**

From formal scalar circuits to tensor rank

At a product gate only two new products of linear forms enter the bidegree
`(1,1)` component. We maintain one shared list of these products across *all*
registers, so fan-out and multiple matrix entries incur no additional cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Foundation MvPolynomial
open scoped BigOperators
noncomputable section

variable {F A B I R : Type*} [Field F]

-- 读法：逐一匹配以下输入模式：`_, .nil`、`_, .step p (.mul _ _)`、`_, .step p _`。
/-- 标量乘法门的数目。寄存器载入、加法和减法的贡献均为零。

英文原文：Number of scalar multiplication gates. Register loads, additions and
subtractions contribute zero.
-/
def multiplicationCount : {r : ℕ} → Program F I r → ℕ
  | _, .nil => 0
  | _, .step p (.mul _ _) => multiplicationCount p + 1
  | _, .step p _ => multiplicationCount p

omit [Field F] in
-- 读法：`multiplicationCount p` 不超过 `p.cost`。对 `p` 作归纳。
theorem multiplicationCount_le_cost {r : ℕ} (p : Program F I r) :
    multiplicationCount p ≤ p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => cases g <;> simp [multiplicationCount, Gate.cost] <;> omega

-- 读法：在后续公式中，`InputPoly` 是 `MvPolynomial (A ⊕ B) F` 的缩写。
private abbrev InputPoly (F A B : Type*) [Field F] := MvPolynomial (A ⊕ B) F

-- 读法：`mixedPart` 的取值由 `constantCoeff (pderiv (Sum.inr y) (pderiv (Sum.inl x) p))` 给出。
/-- 由一个左输入和一个右输入共同标记的无平方因子单项式的系数。

英文原文：The coefficient of the squarefree monomial indexed by a left and a right input.
-/
def mixedPart (p : InputPoly F A B) (x : A) (y : B) : F :=
  constantCoeff (pderiv (Sum.inr y) (pderiv (Sum.inl x) p))

-- 读法：`leftPart` 的取值由 `constantCoeff (pderiv (Sum.inl x) p)` 给出。
private def leftPart (p : InputPoly F A B) (x : A) : F :=
  constantCoeff (pderiv (Sum.inl x) p)

-- 读法：`rightPart` 的取值由 `constantCoeff (pderiv (Sum.inr y) p)` 给出。
private def rightPart (p : InputPoly F A B) (y : B) : F :=
  constantCoeff (pderiv (Sum.inr y) p)

-- 读法：结论为 `mixedPart (p * q) x y = constantCoeff q * mixedPart p x y + constantCoeff p * mixedPart q x y + leftPart p x * rightPart q y + leftPart q x * rightPart p y`。
private theorem mixedPart_mul (p q : InputPoly F A B) (x : A) (y : B) :
    mixedPart (p * q) x y =
      constantCoeff q * mixedPart p x y + constantCoeff p * mixedPart q x y +
        leftPart p x * rightPart q y + leftPart q x * rightPart p y := by
  simp only [mixedPart, leftPart, rightPart, pderiv_mul, map_add, map_mul]
  ring

-- 读法：`mixedPart (X s : InputPoly F A B) x y` 等于 `0`。按 `s = Sum.inl x` 成立与否分情况。
private theorem mixedPart_X (s : A ⊕ B) (x : A) (y : B) :
    mixedPart (X s : InputPoly F A B) x y = 0 := by
  classical
  by_cases h : s = Sum.inl x
  · subst s
    simp [mixedPart]
  · simp [mixedPart, pderiv_X_of_ne h]

-- 读法：`InProductSpan` 表示以下条件：存在 `c : Fin r → F`，对每个 `x y`，`mixedPart p x y` 等于 `∑ t, a t x * b t y * c t`。
/-- 这个寄存器的值可以由一组共用乘积线性组合而成。

英文原文：A common collection of products can be linearly recombined to give this register.
-/
private def InProductSpan {r : ℕ} (a : Fin r → A → F) (b : Fin r → B → F)
    (p : InputPoly F A B) : Prop :=
  ∃ c : Fin r → F, ∀ x y, mixedPart p x y = ∑ t, a t x * b t y * c t

-- 读法：要证明的命题是 `InProductSpan a b (p + q)`。
private theorem inProductSpan_add {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan a b (p + q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨c + d, fun x y => ?_⟩
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hc, ← hd, mixedPart, map_add]

-- 读法：要证明的命题是 `InProductSpan a b (p - q)`。
private theorem inProductSpan_sub {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan a b (p - q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨c - d, fun x y => ?_⟩
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, ← hc, ← hd, mixedPart, map_sub]

-- 读法：要证明的命题是 `InProductSpan (Fin.cons u a) (Fin.cons v b) p`。
private theorem inProductSpan_insert {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p : InputPoly F A B} (hp : InProductSpan a b p) (u : A → F) (v : B → F) :
    InProductSpan (Fin.cons u a) (Fin.cons v b) p := by
  obtain ⟨c, hc⟩ := hp
  refine ⟨Fin.cons 0 c, fun x y => ?_⟩
  simp [Fin.sum_univ_succ, hc]

-- 读法：要证明的命题是 `InProductSpan (Fin.cons (leftPart p) (Fin.cons (leftPart q) a)) (Fin.cons (rightPart q) (Fin.cons (rightPart p) b)) (p * q)`。
private theorem inProductSpan_mul {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan (Fin.cons (leftPart p) (Fin.cons (leftPart q) a))
      (Fin.cons (rightPart q) (Fin.cons (rightPart p) b)) (p * q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨Fin.cons 1 (Fin.cons 1 (fun t => constantCoeff q * c t + constantCoeff p * d t)),
    fun x y => ?_⟩
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_one, mixedPart_mul,
    hc, hd, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring_nf

-- 读法：对 `p` 作归纳。
private theorem registerProducts {r : ℕ} (p : Program F (A ⊕ B) r) :
    ∃ (a : Fin (2 * multiplicationCount p) → A → F) (b : Fin (2 * multiplicationCount p) → B → F),
      ∀ i, InProductSpan a b (registerPolynomial p i) := by
  induction p with
  | nil => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | step p g ih =>
    obtain ⟨a, b, hab⟩ := ih
    cases g with
    | constant z =>
      refine ⟨a, b, Fin.cases ?_ hab⟩
      refine ⟨0, fun x y => ?_⟩
      simp [gatePolynomial, mixedPart]
    | input s =>
      refine ⟨a, b, Fin.cases ?_ hab⟩
      refine ⟨0, fun x y => ?_⟩
      simp [gatePolynomial, mixedPart_X]
    | add i j => exact ⟨a, b, Fin.cases (inProductSpan_add (hab i) (hab j)) hab⟩
    | sub i j => exact ⟨a, b, Fin.cases (inProductSpan_sub (hab i) (hab j)) hab⟩
    | mul i j =>
      simp only [multiplicationCount]
      refine ⟨_, _, Fin.cases (inProductSpan_mul (hab i) (hab j)) (fun k => ?_)⟩
      exact inProductSpan_insert (inProductSpan_insert (hab k) _ _) _ _

-- 读法：`mixedPart (∑ j : Fin b, X (Sum.inl (i,j)) * X (Sum.inr (j,k)) : InputPoly F _ _) x y` 等于 `matrixTensor F b c a x y (k, i)`。
private theorem matrixEntry_mixedPart {a b c : ℕ} (i : Fin a) (k : Fin c)
    (x : Fin a × Fin b) (y : Fin b × Fin c) :
    mixedPart (∑ j : Fin b, X (Sum.inl (i,j)) * X (Sum.inr (j,k)) : InputPoly F _ _) x y =
      matrixTensor F b c a x y (k, i) := by
  classical
  rcases x with ⟨u, v⟩
  rcases y with ⟨w, z⟩
  simp [mixedPart, map_sum, pderiv_X, Pi.single_apply, apply_ite,
    Tensor.matrixCoefficients, Prod.ext_iff, ite_and, eq_comm]
  split_ifs <;> simp_all

-- 读法：`tensorRank (matrixTensor F b c a)` 不超过 `2 * multiplicationCount P.program`。这里调用 `tensorRank_le_of_rankAtMost`。
/-- 若计算矩形矩阵乘积的形式无除法电路使用 `s` 次乘法，就可给出一个至多含 `2s` 个简单张量的精确秩分解。

英文原文：A formal division-free rectangular matrix multiplication circuit with `s`
products gives an exact rank decomposition with at most `2s` simple tensors.
-/
theorem matrixTensor_rank_le_twice_multiplicationCount {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (h : FormalCorrect P) : tensorRank (matrixTensor F b c a) ≤ 2 * multiplicationCount P.program := by
  classical
  obtain ⟨u, v, huv⟩ := registerProducts P.program
  choose w hw using huv
  apply tensorRank_le_of_rankAtMost
  refine ⟨u, v, fun t z => w (P.output z.2 z.1) t, ?_⟩
  funext x y z
  rw [← matrixEntry_mixedPart, ← h z.2 z.1]
  exact hw _ _ _

-- 读法：`tensorRank (matrixTensor F b c a)` 不超过 `2 * P.cost`。
/-- 总运算数的两倍同样是秩的上界。

英文原文：The total number of operations also bounds the rank, with the same factor two.
-/
theorem matrixTensor_rank_le_twice_cost {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (h : FormalCorrect P) : tensorRank (matrixTensor F b c a) ≤ 2 * P.cost :=
  (matrixTensor_rank_le_twice_multiplicationCount h).trans
    (Nat.mul_le_mul_left 2 (multiplicationCount_le_cost _))

end

end SpectralBooks
end LinearAlgebra
end OAI
