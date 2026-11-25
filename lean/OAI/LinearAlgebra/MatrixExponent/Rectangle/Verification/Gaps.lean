-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Model
import Mathlib.Data.Fin.Tuple.Basic

/-!
# 将公共随机种子限制在有限个结果上

保留质量大于三分之二的集合，仍能将每个正确输入与每个错误输入严格区分。无需重新归一化权重。

**英文原文**

Restricting a public seed to finitely many outcomes

A retained set of mass greater than two thirds still strictly
separates every correct input from every incorrect one. The weights
need not be normalized again.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open Finset
open scoped Classical
variable {ι X : Type*}

-- 读法：`Accurate` 表示以下条件：对每个 `x`，`2 / 3` 不超过 `∑' i, if (accept i x ↔ good x) then w i else 0`。
def Accurate (w : ι → ℝ) (accept : ι → X → Prop) (good : X → Prop) : Prop :=
  ∀ x, 2 / 3 ≤ ∑' i, if (accept i x ↔ good x) then w i else 0

-- 读法：`Gap` 表示以下条件：对每个 `x y`，使 `good x → ¬good y → (∑ i ∈ S, if accept i y then w i else 0) < ∑ i ∈ S, if accept i x then w i else 0` 成立。
def Gap (w : ι → ℝ) (accept : ι → X → Prop) (good : X → Prop) (S : Finset ι) : Prop :=
  ∀ x y, good x → ¬good y →
    (∑ i ∈ S, if accept i y then w i else 0) < ∑ i ∈ S, if accept i x then w i else 0

variable {w : ι → ℝ} {accept : ι → X → Prop} {good : X → Prop}
  (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (ha : Accurate w accept good)

include hw hs ha in
-- 读法：`(∑ i ∈ S, if (accept i x ↔ good x) then 0 else w i)` 不超过 `1 / 3`。
private theorem mistake (S : Finset ι) (x : X) :
    (∑ i ∈ S, if (accept i x ↔ good x) then 0 else w i) ≤ 1 / 3 := by
  let f i := if (accept i x ↔ good x) then w i else 0
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun i => by unfold f; split <;> simp [hw])
    (fun i => by unfold f; split <;> simp [hw]) hs.summable
  have he (i) : w i - f i = if (accept i x ↔ good x) then 0 else w i := by
    unfold f; split <;> simp_all
  have ht := hs.sub hf.hasSum
  simp_rw [he] at ht
  refine (sum_le_hasSum S (fun i _ => by split <;> simp [hw]) ht).trans ?_
  have hh : 2 / 3 ≤ ∑' i, f i := ha x
  linarith

include hw hs ha in
-- 读法：`(∑ i ∈ S, w i) - 2 / 3` 不超过 `(∑ i ∈ S, if accept i x then w i else 0) - (∑ i ∈ S, if accept i y then w i else 0)`。这里调用 `sum_congr`。
theorem retained_gap (S : Finset ι) {x y : X} (hx : good x) (hy : ¬good y) :
    (∑ i ∈ S, w i) - 2 / 3 ≤
      (∑ i ∈ S, if accept i x then w i else 0) - (∑ i ∈ S, if accept i y then w i else 0) := by
  have h := mistake hw hs ha S x
  have k := mistake hw hs ha S y
  simp only [hx, iff_true] at h
  simp only [hy, iff_false, ite_not] at k
  have he : (∑ i ∈ S, if accept i x then w i else 0) +
      (∑ i ∈ S, if accept i x then 0 else w i) = ∑ i ∈ S, w i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun i _ => by split <;> simp_all)
  linarith

include hw hs ha in
-- 读法：要证明的命题是 `Gap w accept good S`。
theorem mass_gap (S : Finset ι) (hm : 2 / 3 < ∑ i ∈ S, w i) : Gap w accept good S :=
  fun _ _ hx hy => sub_pos.mp ((sub_pos.mpr hm).trans_le (retained_gap hw hs ha S hx hy))

include hw hs ha in
-- 读法：要证明的命题是 `Gap w accept good univ`。这里调用 `mass_gap`。
theorem finite_gap [Fintype ι] : Gap w accept good univ := by
  apply mass_gap hw hs ha
  have hm := hs.tsum_eq
  rw [tsum_fintype] at hm
  rw [hm]
  norm_num

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 由有限路径族判定接受

一条路径是关于标量坐标的一组合取条件。中间寄存器和得知种子后选取的见证都用存在量词约束；验证器是有限条这类路径的析取。即使每个输入由不同的路径接受，其成本也控制最长路径。

**英文原文**

Acceptance by a finite family of paths

A path is a conjunction on scalar coordinates. Both intermediate
registers and post-seed witnesses are existentially quantified.
A verifier is their finite disjunction. Its cost bounds the longest
path, even if a different path accepts each input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

-- 读法：归纳构造子包括 `scalar`、`input`、`aux`。
inductive Operand (F : Type*) (n t : ℕ)
  | scalar (a : F)
  | input (i : Index n)
  | aux (j : Fin t)

-- 读法：归纳构造子包括 `add`。
inductive Op
  | add | sub | mul

-- 读法：归纳构造子包括 `eq`、`ne`、`op`、`div`。
inductive Instruction (F : Type*) (n t : ℕ)
  | eq (a b : Operand F n t)
  | ne (a b : Operand F n t)
  | op (f : Op) (a b c : Operand F n t)
  | div (a b c : Operand F n t)

-- 读法：结构的字段包括 `vars`、`code`。
structure Path (F : Type*) (n : ℕ) where
  vars : ℕ
  code : List (Instruction F n vars)

-- 读法：在后续公式中，`Verifier` 是 `List (Path F n)` 的缩写。
abbrev Verifier (F : Type*) (n : ℕ) := List (Path F n)

variable {F : Type*} {n t : ℕ}

-- 读法：逐一匹配以下输入模式：`.scalar a`、`.input i`、`.aux j`。
def Operand.eval (x : Index n → F) (w : Fin t → F) : Operand F n t → F
  | .scalar a => a
  | .input i => x i
  | .aux j => w j

-- 读法：`Op.eval` 的取值由 `match f with | .add => a + b | .sub => a - b | .mul => a * b` 给出。
def Op.eval [Ring F] (f : Op) (a b : F) : F :=
  match f with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

variable [Field F]

-- 读法：逐一匹配以下输入模式：`.eq a b`、`.ne a b`、`.op f a b c`、`.div a b c`。
def Instruction.holds (x : Index n → F) (w : Fin t → F) : Instruction F n t → Prop
  | .eq a b => a.eval x w = b.eval x w
  | .ne a b => a.eval x w ≠ b.eval x w
  | .op f a b c => f.eval (a.eval x w) (b.eval x w) = c.eval x w
  | .div a b c => b.eval x w ≠ 0 ∧ a.eval x w / b.eval x w = c.eval x w

-- 读法：`Path.accept` 表示以下条件：存在 `w`，对每个 `i ∈ p.code`，要证明的命题是 `i.holds x w`。
def Path.accept (p : Path F n) (x : Index n → F) : Prop :=
  ∃ w, ∀ i ∈ p.code, i.holds x w

-- 读法：`Verifier.accept` 表示以下条件：存在 `p ∈ A`，要证明的命题是 `p.accept x`。
def Verifier.accept (A : Verifier F n) (x : Index n → F) : Prop :=
  ∃ p ∈ A, p.accept x

-- 读法：`Verifier.cost` 表示以下条件：对每个 `p ∈ A`，`(p.code.length : ℝ)` 不超过 `c`。
def Verifier.cost (A : Verifier F n) (c : ℝ) : Prop :=
  ∀ p ∈ A, (p.code.length : ℝ) ≤ c

-- 读法：`Operand.names` 的取值由 `| .input i => {i} | _ => ∅` 给出。
private def Operand.names : Operand F n t → Finset (Index n)
  | .input i => {i}
  | _ => ∅

omit [Field F] in
-- 读法：由 `a.names.card ≤ 1 ∧ ∀ x y w, (∀ i ∈ a.names, x i = y i)` 推出 `a.eval x w = a.eval y w`。
private theorem Operand.read (a : Operand F n t) :
    a.names.card ≤ 1 ∧ ∀ x y w, (∀ i ∈ a.names, x i = y i) → a.eval x w = a.eval y w := by
  cases a <;> simp [names, eval]

-- 读法：存在 `W : Finset (Index n)`，由 `W.card ≤ 3 ∧ ∀ x y w, (∀ i ∈ W, x i = y i)` 推出 `a.holds x w → a.holds y w`。这里调用 `Finset.card_union_le`。
private theorem Instruction.read (a : Instruction F n t) :
    ∃ W : Finset (Index n), W.card ≤ 3 ∧
      ∀ x y w, (∀ i ∈ W, x i = y i) → a.holds x w → a.holds y w := by
  have pick (a b c : Operand F n t) :
      ∃ W : Finset (Index n), W.card ≤ 3 ∧ ∀ x y w, (∀ i ∈ W, x i = y i) →
        a.eval x w = a.eval y w ∧ b.eval x w = b.eval y w ∧ c.eval x w = c.eval y w := by
    refine ⟨a.names ∪ b.names ∪ c.names, ?_, fun x y w h => ?_⟩
    · exact (Finset.card_union_le ..).trans (Nat.add_le_add
        ((Finset.card_union_le ..).trans (Nat.add_le_add a.read.1 b.read.1)) c.read.1)
    · exact ⟨a.read.2 _ _ _ (fun i hi => h i (by simp [hi])),
        b.read.2 _ _ _ (fun i hi => h i (by simp [hi])),
        c.read.2 _ _ _ (fun i hi => h i (by simp [hi]))⟩
  cases a with
  | eq a b | ne a b =>
    -- 推导：从 `pick a b b` 中取出 `W, hW, h`。
    obtain ⟨W, hW, h⟩ := pick a b b
    refine ⟨W, hW, fun x y w he => ?_⟩
    simp only [holds, (h x y w he).1, (h x y w he).2.1, imp_self]
  | op _ a b c | div a b c =>
    obtain ⟨W, hW, h⟩ := pick a b c
    refine ⟨W, hW, fun x y w he => ?_⟩
    simp only [holds, (h x y w he).1, (h x y w he).2.1, (h x y w he).2.2, imp_self]

-- 读法：存在 `W : Finset (Index n)`，由 `W.card ≤ 3 * p.length ∧ ∀ x y w, (∀ i ∈ W, x i = y i)` 推出 `∀ i ∈ p, i.holds x w → i.holds y w`。对 `p` 作归纳。
private theorem read_code (p : List (Instruction F n t)) :
    ∃ W : Finset (Index n), W.card ≤ 3 * p.length ∧ ∀ x y w, (∀ i ∈ W, x i = y i) →
      ∀ i ∈ p, i.holds x w → i.holds y w := by
  induction p with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons a p ih =>
    obtain ⟨A, hA, ha⟩ := a.read
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨A ∪ B, (Finset.card_union_le ..).trans (by simp only [List.length_cons]; omega), ?_⟩
    intro x y w h i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact ha _ _ _ (fun j hj => h j (Finset.mem_union_left _ hj))
    · exact hb _ _ _ (fun j hj => h j (Finset.mem_union_right _ hj)) _ hi

-- 读法：存在 `W : Finset (Index n)`，由 `(W.card : ℝ) ≤ 3 * c ∧ ∀ y, (∀ i ∈ W, x i = y i)` 推出 `A.accept y`。
/-- 只要变动发生在路径未读取的坐标上，原先被接受的赋值仍能通过检验。

英文原文：One accepting assignment continues to work on any change outside
the coordinates read by its path.
-/
theorem Verifier.read (A : Verifier F n) {c : ℝ} (hc : A.cost c) {x} (hx : A.accept x) :
    ∃ W : Finset (Index n), (W.card : ℝ) ≤ 3 * c ∧ ∀ y, (∀ i ∈ W, x i = y i) → A.accept y := by
  obtain ⟨p, hp, w, hw⟩ := hx
  obtain ⟨W, hW, h⟩ := read_code p.code
  refine ⟨W, ?_, fun y he => ⟨p, hp, w, fun i hi => h x y w he i hi (hw i hi)⟩⟩
  exact (show (W.card : ℝ) ≤ 3 * p.code.length by exact_mod_cast hW).trans
    (mul_le_mul_of_nonneg_left (hc p hp) (by norm_num))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# 含相等性分支的有限算术树

初始辅助坐标作为存在见证。每次算术运算增加一个寄存器。除法按分母是否为零分支，且只在除法成功时添加寄存器。

**英文原文**

Finite arithmetic trees with equality branches

The initial auxiliary coordinates are existential witnesses. Each
arithmetic operation appends a register. Division branches on a
zero denominator and appends a register only on success.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped Classical

-- 读法：归纳构造子包括 `yes`、`no`、`test`、`op`、`divide`。
inductive Tree (F : Type*) (n : ℕ) : ℕ → Type _
  | yes {t} : Tree F n t
  | no {t} : Tree F n t
  | test {t} (a b : Operand F n t) (equal unequal : Tree F n t) : Tree F n t
  | op {t} (f : Op) (a b : Operand F n t) (next : Tree F n (t + 1)) : Tree F n t
  | divide {t} (a b : Operand F n t) (next : Tree F n (t + 1)) (failure : Tree F n t) : Tree F n t

variable {F : Type*} {n t : ℕ}

-- 读法：逐一匹配以下输入模式：`.scalar a`、`.input i`、`.aux j`。
def Operand.raise : Operand F n t → Operand F n (t + 1)
  | .scalar a => .scalar a
  | .input i => .input i
  | .aux j => .aux j.castSucc

-- 读法：`a.raise.eval x w` 等于 `a.eval x (Fin.init w)`。
@[simp] theorem Operand.eval_raise (a : Operand F n t) (x : Index n → F) (w : Fin (t + 1) → F) :
    a.raise.eval x w = a.eval x (Fin.init w) := by
  cases a <;> rfl

-- 读法：逐一匹配以下输入模式：`.yes | .no`、`.test _ _ u v`、`.op _ _ _ u`、`.divide _ _ u v`。
def Tree.depth {t : ℕ} : Tree F n t → ℕ
  | .yes | .no => 0
  | .test _ _ u v => max u.depth v.depth + 1
  | .op _ _ _ u => u.depth + 1
  | .divide _ _ u v => max u.depth v.depth + 1

variable [Field F]

-- 读法：逐一匹配输入模式，例如 `.yes, _, _`、`.no, _, _`、`.test a b u v, x, w`、`.op f a b u, x, w`。
def Tree.run {t : ℕ} : Tree F n t → (Index n → F) → (Fin t → F) → Prop
  | .yes, _, _ => True
  | .no, _, _ => False
  | .test a b u v, x, w => if a.eval x w = b.eval x w then u.run x w else v.run x w
  | .op f a b u, x, w => u.run x (Fin.snoc w (f.eval (a.eval x w) (b.eval x w)))
  | .divide a b u v, x, w => if b.eval x w = 0 then v.run x w
      else u.run x (Fin.snoc w (a.eval x w / b.eval x w))

-- 读法：`Tree.accept` 的取值由 `∃ w, u.run x w` 给出。
def Tree.accept (u : Tree F n t) (x : Index n → F) := ∃ w, u.run x w

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
