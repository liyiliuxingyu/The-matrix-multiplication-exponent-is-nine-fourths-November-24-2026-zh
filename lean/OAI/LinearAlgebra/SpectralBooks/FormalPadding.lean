-- 本文件所属证明环节：将较大规格的输入变量映成较小规格的变量或标量，对应于在寄存器的形式多项式中直接代入。利用这一点证明矩阵的零填充及相应输出截取保持 FormalCorrect。
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding

/-!
# 零填充保持形式矩阵恒等式

**英文原文**

Zero padding preserves formal matrix identities
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
noncomputable section

variable {F I J : Type*} [Field F]

-- 读法：`registerPolynomial (p.mapSource f) i` 等于 `aeval (fun j => Sum.elim X C (f j) : I → MvPolynomial J F) (registerPolynomial p i)`。对 `p` 作归纳。
/-- 将每个电路输入替换为变量或标量，会在其形式输出多项式上实现相应的代入。

英文原文：Replacing each circuit input by a variable or a scalar realizes the
corresponding substitution on its formal output polynomial.
-/
theorem registerPolynomial_mapSource (f : I → J ⊕ F) {r : ℕ}
    (p : Program F I r) (i : Fin r) :
    registerPolynomial (p.mapSource f) i =
      aeval (fun j => Sum.elim X C (f j) : I → MvPolynomial J F) (registerPolynomial p i) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g with
    | input j =>
      cases h : f j <;> simp [Program.mapSource, Gate.mapSource, gatePolynomial, h]
    | constant z => simp [Program.mapSource, Gate.mapSource, gatePolynomial]
    | add a b => simp [Program.mapSource, Gate.mapSource, gatePolynomial, ih]
    | sub a b => simp [Program.mapSource, Gate.mapSource, gatePolynomial, ih]
    | mul a b => simp [Program.mapSource, Gate.mapSource, gatePolynomial, ih]

-- 读法：要证明的命题是 `FormalCorrect (P.pad ha hb hc)`。
theorem FormalCorrect.pad {a b c A B C : ℕ} {P : MatrixAlgorithm F A B C}
    (hP : FormalCorrect P) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    FormalCorrect (P.pad ha hb hc) := by
  intro i k
  change registerPolynomial (P.program.mapSource _) (P.output (i.castLE ha) (k.castLE hc)) = _
  rw [registerPolynomial_mapSource, hP, map_sum]
  simp only [map_mul, aeval_X]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hb) (fun a b hab => Fin.ext (congrArg (fun v : Fin B => v.val) hab))
    _ _ ?_ ?_
  · intro j hj
    have hlarge : ¬ j.val < b := fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩
    simp [padSource, hlarge, i.isLt]
  · intro j
    simp [padSource, i.isLt, j.isLt, k.isLt]

end

end SpectralBooks
end LinearAlgebra
end OAI
