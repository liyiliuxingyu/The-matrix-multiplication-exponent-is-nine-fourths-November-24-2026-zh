-- 本文件所属证明环节：给程序寄存器和输入重新编号，将前一个程序的输出代入后一个程序的输入。Substituted 同时记录原有寄存器和新输出的对应关系及求值证明。
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs

namespace OAI

/-!
域上的无除法算术程序及其运算次数。

**英文原文**

Division-free arithmetic programs over a field and their operation counts.
-/

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input Input' Register : Type*}

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.add i j`、`.sub i j`。
def mapInput (f : Input → Input') : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

-- 读法：`(g.mapInput f).eval inputs registers` 等于 `g.eval (inputs ∘ f) registers`。
@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

omit [Field F] in
-- 读法：`(g.mapInput f).cost` 等于 `g.cost`。
@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate F Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

-- 读法：逐一匹配输入模式，例如 `.constant z`、`.input i`、`.inl j`、`.inr z`。
def mapSource (f : Input → Input' ⊕ F) : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

-- 读法：`(g.mapSource f).eval inputs registers` 等于 `g.eval (fun i => Sum.elim inputs id (f i)) registers`。对 `g` 分类讨论。
@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

omit [Field F] in
-- 读法：`(g.mapSource f).cost` 等于 `g.cost`。对 `g` 分类讨论。
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

-- 读法：逐一匹配以下输入模式：`0, .nil`、`_ + 1, .step p g`。
def mapInput (f : Input → Input') : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

-- 读法：对每个 `i : Fin r`，`(p.mapInput f).eval inputs i` 等于 `p.eval (inputs ∘ f) i`。对 `p` 作归纳。
@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r)
    (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

omit [Field F] in
-- 读法：`(p.mapInput f).cost` 等于 `p.cost`。对 `p` 作归纳。
@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

-- 读法：逐一匹配以下输入模式：`0, .nil`、`_ + 1, .step p g`。
def mapSource (f : Input → Input' ⊕ F) : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

-- 读法：对每个 `i : Fin r`，`(p.mapSource f).eval inputs i` 等于 `p.eval (fun j => Sum.elim inputs id (f j)) i`。对 `p` 作归纳。
@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

omit [Field F] in
-- 读法：`(p.mapSource f).cost` 等于 `p.cost`。对 `p` 作归纳。
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

-- 读法：结构的字段包括 `registers`、`program`、`oldOutput`、`output`、`correctOld`。
structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program F Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

-- 读法：用字段 `registers`、`program`、`oldOutput`、`output` 构造 `Substituted p (q.step g) wires`。
def step {r s : ℕ} {p : Program F Input r} {q : Program F Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate F Mid (Fin s)) (h : Gate F Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

-- 读法：逐一匹配输入模式，例如 `0, .nil, wires`、`_ + 1, .step q g, wires`、`.input j`、`.constant z`。
def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Arithmetic

end

end OAI
