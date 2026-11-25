-- 本文件所属证明环节：将一个秩分解给出的两个输入线性变换、较小方阵的乘法及输出线性变换复合。逐坐标验证复合程序实现块矩阵乘积的形式多项式恒等式，并把额外的线性组合成本控制为小矩阵面积的常数倍。
import OAI.LinearAlgebra.SpectralBooks.FormalBlockFamily
import OAI.LinearAlgebra.SpectralBooks.Tensor

/-!
# 一次基于秩的分块递归的形式正确性

**英文原文**

Formal correctness of one rank-based block recursion
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Arithmetic.RecursiveBlock Foundation MvPolynomial
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
private theorem polynomial_block_identity {I : Type*}
    (a : Fin r → Fin n₁ × Fin n₂ → F) (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) (MvPolynomial I F))
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) (MvPolynomial I F))
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (∑ q, C (c q (k,i)) * ∑ t : Fin m₂,
      (∑ x, C (a q x) * A (join x.1 s) (join x.2 t)) *
      (∑ y, C (b q y) * B (join y.1 t) (join y.2 u))) =
      ∑ j, A (join i s) j * B j (join k u) := by
  let K := FractionRing (MvPolynomial I F)
  let ι := algebraMap (MvPolynomial I F) K
  let φ : F →+* K := ι.comp C
  have hK : Tensor.matrixCoefficients (K := K) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (φ ∘ a q) (φ ∘ b q) (φ ∘ c q) x y z := by
    funext x y z
    have he := congrArg φ (congrFun (congrFun (congrFun h x) y) z)
    simpa [Tensor.matrixCoefficients, Tensor.rankOne, apply_ite] using he
  apply IsFractionRing.injective (MvPolynomial I F) K
  simp only [map_sum, map_mul]
  exact block_identity (fun q => φ ∘ a q) (fun q => φ ∘ b q) (fun q => φ ∘ c q) hK
    (fun x y => ι (A x y)) (fun x y => ι (B x y)) i k s u

-- 读法：要证明的命题是 `FormalCorrect (algorithm a b c P)`。这里调用 `polynomial_block_identity`。
/-- 将三个分块线性映射与正确的小规模乘法算法复合，所得等式仍是基域上的多项式恒等式。

英文原文：Composing the three block linear maps with a correct smaller multiplication
algorithm preserves correctness as a polynomial identity over the ground field.
-/
theorem formalCorrect_blockAlgorithm (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (P : MatrixAlgorithm F m₁ m₂ m₃) (hP : FormalCorrect P) :
    FormalCorrect (algorithm a b c P) := by
  intro i k
  obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k,u⟩,rfl⟩ := finProdFinEquiv.surjective k
  change familyPolynomial ((recursiveProducts a b P).compose (outputFamily c)) (join i s, join k u) = _
  rw [familyPolynomial_compose, bind₁_outputFamily]
  simp_rw [familyPolynomial_recursiveProducts a b P hP]
  exact polynomial_block_identity (m₁ := m₁) (m₂ := m₂) (m₃ := m₃)
    (I := MatrixInput (n₁*m₁) (n₂*m₂) (n₃*m₃)) a b c h
    (fun x y => X (.inl (x,y))) (fun x y => X (.inr (x,y))) i k s u

-- 读法：存在 `Q : MatrixAlgorithm F (n*m) (n*m) (n*m)`，`FormalCorrect Q` 与 `Q.cost ≤ r * P.cost + 6 * r * n ^ 2 * m ^ 2` 同时成立。这里调用 `le_of_eq`。
/-- 方阵秩分解公式给出形式正确的递归步骤，所需线性组合的额外成本与较小矩阵的面积成正比。

英文原文：A square rank formula produces a formally correct recursion step with linear
combination overhead proportional to the smaller matrices' area.
-/
theorem square_formal_block_step {n m r : ℕ}
    (hr : Tensor.RankAtMost (matrixTensor F n n n) r) (P : MatrixAlgorithm F m m m)
    (hP : FormalCorrect P) : ∃ Q : MatrixAlgorithm F (n*m) (n*m) (n*m),
    FormalCorrect Q ∧ Q.cost ≤ r * P.cost + 6 * r * n ^ 2 * m ^ 2 := by
  obtain ⟨a,b,c,h⟩ := hr
  refine ⟨algorithm a b c P, formalCorrect_blockAlgorithm a b c h P hP, ?_⟩
  rw [algorithm_cost]
  exact le_of_eq (by ring)

end

end SpectralBooks
end LinearAlgebra
end OAI
