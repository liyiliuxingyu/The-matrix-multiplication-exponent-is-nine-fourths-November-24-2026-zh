-- 本文件所属证明环节：对复数算术表达式定义求值和运算次数，递归编译为寄存器程序。追加一门时区分新旧寄存器，从而证明编译保留求值结果。
import OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
复数域上的算术程序与矩阵乘法的渐近成本。

**英文原文**

Complex arithmetic programs and asymptotic matrix multiplication costs.
-/

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

variable {Input R S : Type*}

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add i j`、`.sub i j`。
def mapRegister (f : R → S) : Gate Input R → Gate Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

-- 读法：`(g.mapRegister f).eval inputs registers` 等于 `g.eval inputs (fun i => registers (f i))`。
theorem eval_mapRegister (g : Gate Input R) (f : R → S)
    (inputs : Input → ℂ) (registers : S → ℂ) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

-- 读法：`(g.mapRegister f).cost` 等于 `g.cost`。
@[simp] theorem cost_mapRegister (g : Gate Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

-- 读法：`oldIndex` 的结果类型为 `Fin (r + s)`。
def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

-- 读法：`newIndex` 的结果类型为 `Fin (r + s)`。
def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

-- 读法：`oldIndex r 0 i` 等于 `i`。按 `Fin.ext` 的外延性准则比较各分量。
@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

-- 读法：`oldIndex r (s + 1) i` 等于 `(oldIndex r s i).succ`。按 `Fin.ext` 的外延性准则比较各分量。
@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

-- 读法：`newIndex r (s + 1) 0` 等于 `0`。按 `Fin.ext` 的外延性准则比较各分量。
@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

-- 读法：`newIndex r (s + 1) i.succ` 等于 `(newIndex r s i).succ`。按 `Fin.ext` 的外延性准则比较各分量。
@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

-- 读法：逐一匹配以下输入模式：`0, .nil`、`s + 1, .step q g`。
def append {r : ℕ} (p : Program Input r) : {s : ℕ} → Program Input s → Program Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

-- 读法：对每个 `i : Fin s`，`(p.append q).eval inputs (newIndex r s i)` 等于 `q.eval inputs i`。对 `q` 作归纳。
theorem eval_append_new {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

-- 读法：对每个 `i : Fin r`，`(p.append q).eval inputs (oldIndex r s i)` 等于 `p.eval inputs i`。对 `q` 作归纳。
theorem eval_append_old {r s : ℕ} (p : Program Input r) (q : Program Input s)
    (inputs : Input → ℂ) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

-- 读法：`(p.append q).cost` 等于 `p.cost + q.cost`。对 `q` 作归纳。
@[simp] theorem cost_append {r s : ℕ} (p : Program Input r) (q : Program Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

-- 读法：归纳构造子包括 `constant`、`input`、`add`、`sub`、`mul`。
inductive Expression (Input : Type*) where
  | constant : ℂ → Expression Input
  | input : Input → Expression Input
  | add : Expression Input → Expression Input → Expression Input
  | sub : Expression Input → Expression Input → Expression Input
  | mul : Expression Input → Expression Input → Expression Input

namespace Expression

variable {Input : Type*}

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add e f`、`.sub e f`。
def eval (inputs : Input → ℂ) : Expression Input → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

-- 读法：逐一匹配输入模式，例如 `.constant _`、`.input _`、`.add e f`、`.sub e f`。
def cost : Expression Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

-- 读法：结构的字段包括 `registers`、`program`、`output`、`correct`、`cost_eq`。
structure Compiled (e : Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add e f`、`.sub e f`。
def compile : (e : Expression Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Foundation.Arithmetic

end

end OAI
