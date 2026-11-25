-- 本文件所属证明环节：以复常数、输入、加减乘门构造带寄存器的直线程序；定义程序的求值、算术成本、矩阵程序正确性、可容许指数及其下确界，并给出复矩阵乘法系数。
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul

namespace OAI

/-!
复数域上的算术程序与矩阵乘法的渐近成本。

**英文原文**

Complex arithmetic programs and asymptotic matrix multiplication costs.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

-- 读法：归纳构造子包括 `constant`、`input`、`add`、`sub`、`mul`。
inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add i j`、`.sub i j`。
def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

-- 读法：逐一匹配输入模式，例如 `.constant _`、`.input _`、`.add _ _`、`.sub _ _`。
def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

-- 读法：归纳构造子包括 `nil`、`step`。
inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

-- 读法：逐一匹配以下输入模式：`0, .nil, _`、`_ + 1, .step p g, inputs`。
def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

-- 读法：逐一匹配以下输入模式：`0, .nil`、`_ + 1, .step p g`。
def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

-- 读法：`(p.step g).eval inputs 0` 等于 `g.eval inputs (p.eval inputs)`。两端由定义化简为同一项。
@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

-- 读法：`(p.step g).eval inputs i.succ` 等于 `p.eval inputs i`。两端由定义化简为同一项。
@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

-- 读法：`(p.step g).cost` 等于 `p.cost + g.cost`。两端由定义化简为同一项。
@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

-- 读法：在后续公式中，`MatrixInput` 是 `(Fin n × Fin n) ⊕ (Fin n × Fin n)` 的缩写。
abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

-- 读法：逐一匹配以下输入模式：`.inl (i, j)`、`.inr (j, k)`。
def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

-- 读法：结构的字段包括 `registers`、`program`、`output`。
structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

-- 读法：输入 `i k` 时返回 `P.program.eval (matrixInputs A B) (P.output i k)`。
def eval {n : ℕ} (P : MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

-- 读法：`Correct` 表示以下条件：对每个 `A B : Matrix (Fin n) (Fin n) ℂ`，`P.eval A B` 等于 `A * B`。
def Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, P.eval A B = A * B

-- 读法：`cost` 的取值由 `P.program.cost` 给出。
def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

-- 读法：用函数外延性比较等号两侧在 `i k` 处的取值。
theorem correct_iff_entries {n : ℕ} (P : MatrixAlgorithm n) :
    P.Correct ↔ ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

-- 读法：用字段 `registers`、`program`、`output` 构造 `MatrixAlgorithm 1`。
def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

-- 读法：要证明的命题是 `scalarAlgorithm.Correct`。用函数外延性比较等号两侧在 `i k` 处的取值。
theorem scalarAlgorithm_correct : scalarAlgorithm.Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

-- 读法：`AdmissibleExponent` 表示以下条件：对每个 `ε : ℝ`，由 `0 < ε` 推出 `∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n, P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)`。
-- 读法：`scalarAlgorithm.cost` 等于 `1`。两端由定义化简为同一项。
@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

-- 读法：`omega` 的取值由 `sInf {τ : ℝ | AdmissibleExponent τ}` 给出。
noncomputable def omega : ℝ := sInf {τ : ℝ | AdmissibleExponent τ}

end Arithmetic

namespace Tensor

-- 读法：当 `x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1` 成立时取 `1`，否则取 `0`。
def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

-- 读法：`matrixMultiplication a b c (i, j) (j, k) (k, i)` 等于 `1`。
@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
