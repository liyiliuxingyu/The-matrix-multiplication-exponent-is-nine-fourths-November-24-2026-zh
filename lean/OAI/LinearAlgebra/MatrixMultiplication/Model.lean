-- 本文件所属证明环节：定义任意域上的无除法算术门、程序和矩阵乘法算法，并约定如何计数以及检验输出；再引入方阵指数、矩形内维、矩形指数和对偶指数所用的上确界。
import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

-- 读法：归纳构造子包括 `constant`、`input`、`add`、`sub`、`mul`。
inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

-- 读法：逐一匹配输入模式，例如 `.constant _`、`.input _`、`.add _ _`、`.sub _ _`。
def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add i j`、`.sub i j`。
def eval [Field F] (inputs : Input → F) (registers : Register → F) :
    Gate F Input Register → F
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

-- 读法：在后续公式中，`eval.match_1` 是 `@cost.match_1` 的缩写。
abbrev eval.match_1 := @cost.match_1

end Gate

-- 读法：归纳构造子包括 `nil`、`step`。
inductive Program (F Input : Type*) : ℕ → Type _ where
  | nil : Program F Input 0
  | step {r : ℕ} : Program F Input r → Gate F Input (Fin r) → Program F Input (r + 1)

namespace Program

variable {F Input : Type*}

-- 读法：逐一匹配以下输入模式：`0, .nil, _`、`_ + 1, .step p g, inputs`。
def eval [Field F] : {r : ℕ} → Program F Input r → (Input → F) → Fin r → F
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

-- 读法：逐一匹配以下输入模式：`0, .nil`、`_ + 1, .step p g`。
def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

-- 读法：在后续公式中，`MatrixInput` 是 `(Fin a × Fin b) ⊕ (Fin b × Fin c)` 的缩写。
abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

-- 读法：逐一匹配以下输入模式：`.inl (i, j)`、`.inr (j, k)`。
def matrixInputs {F : Type*} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    MatrixInput a b c → F
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

-- 读法：结构的字段包括 `registers`、`program`、`output`。
structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

-- 读法：输入 `i k` 时返回 `P.program.eval (matrixInputs A B) (P.output i k)`。
def eval (P : MatrixAlgorithm F a b c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    Matrix (Fin a) (Fin c) F :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

-- 读法：`Correct` 表示以下条件：对每个 `(A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)`，`P.eval A B` 等于 `A * B`。
def Correct (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F), P.eval A B = A * B

-- 读法：`cost` 的取值由 `P.program.cost` 给出。
def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

-- 读法：`AdmissibleExponent` 表示以下条件：对每个 `ε : ℝ`，由 `0 < ε` 推出 `∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n, P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)`。
/-- 允许正余量，使用同一个常数，并要求每个规模都存在正确的程序。

英文原文：Positive slack, one uniform constant, and a correct program at every size.
-/
def AdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

-- 读法：`omega` 的取值由 `sInf {τ : ℝ | AdmissibleExponent F τ}` 给出。
def omega (F : Type*) [Field F] : ℝ := sInf {τ : ℝ | AdmissibleExponent F τ}

-- 读法：`innerSize` 的取值由 `⌈(n : ℝ) ^ k⌉₊` 给出。
/-- `n × n^k` 矩阵与 `n^k × n` 矩阵相乘时的内部维数。

英文原文：The inner dimension of an `n × n^k` by `n^k × n` multiplication.
-/
def innerSize (n : ℕ) (k : ℝ) : ℕ := ⌈(n : ℝ) ^ k⌉₊

-- 读法：`RectangularAdmissibleExponent` 表示以下条件：对每个 `ε : ℝ`，要证明的命题是 `0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n, P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)`。
def RectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

-- 读法：`rectangularOmega` 的取值由 `sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}` 给出。
def rectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}

-- 读法：`complexAlpha` 的取值由 `sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2}` 给出。
/-- 对偶指数是使矩形乘法指数恰等于二的那些形状的上确界。

英文原文：The dual exponent is a supremum of exact exponent-two rectangular shapes.
-/
def complexAlpha : ℝ :=
  sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2}

end MatrixMultiplication.Arithmetic

end

end OAI
