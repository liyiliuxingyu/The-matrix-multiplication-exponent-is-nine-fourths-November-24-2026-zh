-- 本文件所属证明环节：把有穷多个复算术表达式编译进同一个程序，为每个输出指定寄存器。先对 Fin 编号的表达式族递归编译，再推广到任意有限输出指标。
import OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-!
多项式张量限制与系数的精确提取。

**英文原文**

Polynomial tensor restrictions and exact coefficient extraction.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.Expression

variable {Input Output : Type*}

-- 读法：结构的字段包括 `registers`、`program`、`output`、`correct`、`cost_eq`。
structure CompiledFamily [Fintype Output] (expressions : Output → Expression Input) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

-- 读法：逐一匹配以下输入模式：`0, _`、`n + 1, expressions`。
def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

-- 读法：`compileFamily` 的结果类型为 `CompiledFamily expressions`。
def compileFamily [Fintype Output] (expressions : Output → Expression Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Foundation.Arithmetic.Expression

end

end OAI
