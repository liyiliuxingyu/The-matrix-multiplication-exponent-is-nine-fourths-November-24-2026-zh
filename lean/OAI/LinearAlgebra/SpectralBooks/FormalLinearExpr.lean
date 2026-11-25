-- 本文件所属证明环节：在线性表达式的形式语义中，输出多项式等于各输入变量乘以给定系数后的和。把这个结论推广至同时编译的一族表达式，使块乘法中的输入和输出线性变换可以直接使用。
import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms

/-!
# 线性表达式族计算的形式多项式

**英文原文**

Formal polynomials computed by families of linear expressions
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial
open scoped BigOperators

noncomputable section

variable {F I O : Type*} [Field F]

-- 读法：`expressionPolynomial (LinearExpression.sumFin n f)` 等于 `∑ i, expressionPolynomial (f i)`。对 `n` 作归纳。
private theorem expressionPolynomial_linear_sumFin (n : ℕ) (f : Fin n → Expression F I) :
    expressionPolynomial (LinearExpression.sumFin n f) = ∑ i, expressionPolynomial (f i) := by
  induction n with
  | zero => simp [LinearExpression.sumFin, expressionPolynomial]
  | succ n ih => simp [LinearExpression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

-- 读法：`expressionPolynomial (LinearExpression.linear a wire)` 等于 `∑ i, C (a i) * X (wire i)`。这里调用 `Fintype.equivFin`。
/-- 编译线性表达式得到各输入变量按其系数加权的和。

英文原文：A linear expression compiles to its coefficient-weighted sum of input variables.
-/
theorem expressionPolynomial_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → I) :
    expressionPolynomial (LinearExpression.linear a wire) = ∑ i, C (a i) * X (wire i) := by
  rw [LinearExpression.linear, expressionPolynomial_linear_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => C (a i) * X (wire i))

-- 读法：`registerPolynomial (Family.expressions e).program ((Family.expressions e).output o)` 等于 `expressionPolynomial (e o)`。使用 `registerPolynomial_compileFamily` 给出的结论。
/-- 编译所得电路族的一个输出多项式就是对应表达式的多项式。

英文原文：The output polynomial of a compiled family is the polynomial of the selected expression.
-/
theorem registerPolynomial_expressions [Fintype O] (e : O → Expression F I) (o : O) :
    registerPolynomial (Family.expressions e).program ((Family.expressions e).output o) =
      expressionPolynomial (e o) :=
  registerPolynomial_compileFamily e o

-- 读法：结论为 `let p := Family.expressions (fun j => LinearExpression.linear (a j) (wire j)) registerPolynomial p.program (p.output o) = ∑ i, C (a o i) * X (wire o i)`。
/-- 每个输出可对各自的有限输入项集求和。

英文原文：Each output may sum over its own finite set of input terms.
-/
theorem registerPolynomial_expressions_linear [Fintype O] {Term : O → Type*}
    [∀ o, Fintype (Term o)] (a : (o : O) → Term o → F) (wire : (o : O) → Term o → I) (o : O) :
    let p := Family.expressions (fun j => LinearExpression.linear (a j) (wire j))
    registerPolynomial p.program (p.output o) = ∑ i, C (a o i) * X (wire o i) :=
  (registerPolynomial_expressions _ o).trans (expressionPolynomial_linear _ _)

end

end SpectralBooks
end LinearAlgebra
end OAI
