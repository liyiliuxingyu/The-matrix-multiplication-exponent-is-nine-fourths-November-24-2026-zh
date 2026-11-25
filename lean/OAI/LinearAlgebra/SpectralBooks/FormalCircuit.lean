-- 本文件所属证明环节：为无除法直线程序的每个门和寄存器赋予输入变量的形式多项式，定义 FormalCorrect，并证明程序追加、表达式编译和朴素矩阵乘法保持这种语义。在有限域上也逐系数要求多项式相等。
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm

/-!
# 无除法算术电路的形式多项式语义

仓库中的直线程序可将各寄存器解释为以输入为变量的多项式环元素。这样就能区分有限域上的形式恒等式和多项式函数在该域所有有理点上取值相同这两个概念。

**英文原文**

Formal polynomial semantics for division-free arithmetic circuits

Registers in the repository's straight-line programs can be interpreted in the
polynomial ring on the inputs. This distinguishes formal identities over a finite
field from equality of polynomial functions on its rational points.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped BigOperators
noncomputable section

variable {F I R : Type*} [CommRing F]

-- 读法：`gatePolynomial` 的取值由 `g.casesOn (fun c => C c) (fun i => X i) (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)` 给出。
/-- 由一个门的各寄存器多项式算出的输出多项式。

英文原文：The polynomial produced at one gate from the polynomials in its registers.
-/
def gatePolynomial (g : Gate F I R) (v : R → MvPolynomial I F) : MvPolynomial I F :=
  g.casesOn (fun c => C c) (fun i => X i)
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

-- 读法：逐一匹配以下输入模式：`_, .nil`、`_, .step p g`。
/-- 直线程序各寄存器中存放的形式多项式。

英文原文：Formal polynomial in each register of a straight-line program.
-/
def registerPolynomial : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (registerPolynomial p)) (registerPolynomial p)

-- 读法：`registerPolynomial (p.step g) 0` 等于 `gatePolynomial g (registerPolynomial p)`。两端由定义化简为同一项。
@[simp] theorem registerPolynomial_zero {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    registerPolynomial (p.step g) 0 = gatePolynomial g (registerPolynomial p) := rfl

-- 读法：`registerPolynomial (p.step g) i.succ` 等于 `registerPolynomial p i`。两端由定义化简为同一项。
@[simp] theorem registerPolynomial_succ {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r))
    (i : Fin r) : registerPolynomial (p.step g) i.succ = registerPolynomial p i := rfl

-- 读法：`FormalCorrect` 表示以下条件：对每个 `i k`，`registerPolynomial P.program (P.output i k)` 等于 `∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))`。
/-- 论文所采用的形式正确性定义，也适用于有限基域。

英文原文：Formal correctness in the paper, including over a finite ground field.
-/
def FormalCorrect {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ i k, registerPolynomial P.program (P.output i k) =
    ∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))

-- 读法：`gatePolynomial (g.mapRegister f) v` 等于 `gatePolynomial g (v ∘ f)`。
private theorem gatePolynomial_mapRegister {S : Type*} (f : R → S)
    (v : S → MvPolynomial I F) (g : Gate F I R) :
    gatePolynomial (g.mapRegister f) v = gatePolynomial g (v ∘ f) := by
  cases g <;> rfl

-- 读法：`registerPolynomial (p.append q) (Program.newIndex r s i)` 等于 `registerPolynomial q i`。对 `q` 作归纳。
theorem registerPolynomial_append_new {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin s) :
    registerPolynomial (p.append q) (Program.newIndex r s i) = registerPolynomial q i := by
  induction q with
  | nil => exact i.elim0
  | @step s q g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.append, Program.newIndex_zero, registerPolynomial_zero,
        gatePolynomial_mapRegister]
      congr 1
      exact funext ih
    · simpa only [Program.append, Program.newIndex_succ, registerPolynomial_succ] using ih j

-- 读法：`registerPolynomial (p.append q) (Program.oldIndex r s i)` 等于 `registerPolynomial p i`。对 `q` 作归纳。
theorem registerPolynomial_append_old {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin r) :
    registerPolynomial (p.append q) (Program.oldIndex r s i) = registerPolynomial p i := by
  induction q with
  | nil => simp [Program.append]
  | @step s q g ih =>
    simpa only [Program.append, Program.oldIndex_succ, registerPolynomial_succ] using ih

end

noncomputable section

variable {F I : Type*} [Field F]

-- 读法：在后续公式中，`expressionPolynomial.match_1` 是 `@Expression.cost.match_1` 的缩写。
-- 保留本模块先前构建版本导出的模式匹配器名称。
set_option linter.auxLemma false in
abbrev expressionPolynomial.match_1 := @Expression.cost.match_1

-- 读法：`registerPolynomial e.compile.program e.compile.output` 等于 `expressionPolynomial e`。
theorem registerPolynomial_compile (e : Expression F I) :
    registerPolynomial e.compile.program e.compile.output = expressionPolynomial e := by
  induction e <;> simp_all [Expression.compile, expressionPolynomial, gatePolynomial,
    registerPolynomial_append_old, registerPolynomial_append_new]

-- 读法：要证明的命题是 `registerPolynomial (Expression.compileFinFamily n f).program ((Expression.compileFinFamily n f).output i) = expressionPolynomial (f i)`。对 `n` 作归纳。
private theorem registerPolynomial_compileFinFamily (n : ℕ) (f : Fin n → Expression F I)
    (i : Fin n) :
    registerPolynomial (Expression.compileFinFamily n f).program
      ((Expression.compileFinFamily n f).output i) = expressionPolynomial (f i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Expression.compileFinFamily, registerPolynomial_append_old, registerPolynomial_compile]
    · simp [Expression.compileFinFamily, registerPolynomial_append_new, ih]

-- 读法：要证明的命题是 `registerPolynomial (Expression.compileFamily f).program ((Expression.compileFamily f).output i) = expressionPolynomial (f i)`。
theorem registerPolynomial_compileFamily {O : Type*} [Fintype O]
    (f : O → Expression F I) (i : O) :
    registerPolynomial (Expression.compileFamily f).program ((Expression.compileFamily f).output i)
      = expressionPolynomial (f i) := by
  simp [Expression.compileFamily, registerPolynomial_compileFinFamily]

-- 读法：`expressionPolynomial (Expression.sumFin f)` 等于 `∑ i, expressionPolynomial (f i)`。对 `n` 作归纳。
theorem expressionPolynomial_sumFin {n : ℕ} (f : Fin n → Expression F I) :
    expressionPolynomial (Expression.sumFin f) = ∑ i, expressionPolynomial (f i) := by
  induction n with
  | zero => simp [Expression.sumFin, expressionPolynomial]
  | succ n ih => simp [Expression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

-- 读法：要证明的命题是 `FormalCorrect (naiveAlgorithm (F := F) a b c)`。
/-- 通常的逐项求和算法在每个域上都能算出形式矩阵乘积。

英文原文：The usual entrywise algorithm computes the formal matrix product over every field.
-/
theorem formalCorrect_naiveAlgorithm (F : Type*) [Field F] (a b c : ℕ) :
    FormalCorrect (naiveAlgorithm (F := F) a b c) := by
  intro i k
  simp [naiveAlgorithm, registerPolynomial_compileFamily, naiveEntry, expressionPolynomial_sumFin,
    expressionPolynomial]

end

end SpectralBooks
end LinearAlgebra
end OAI
