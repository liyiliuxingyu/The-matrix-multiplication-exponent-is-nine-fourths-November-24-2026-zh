-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Transport.System

section
/-!
# 确定性直线字程序

程序包含用作字面量的比特和字。一个门保存四个比特。一次制表的子程序构成有限数组，在求值前已固定。求值器只为每个结果数组分配并填充一次。按字计费时，用指针指向不可变的有序对与数组。

**英文原文**

Deterministic straight-line word programs

A program contains its literal bits and words. A gate stores four bits.
The children of a tabulation are a finite array of programs, fixed before
evaluation. The evaluator materializes each result array once. The word
accounting uses pointers to immutable pairs and arrays.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

-- 读法：归纳构造子包括 `id`、`fst`、`snd`、`comp`、`pair`、`select`、`tab`、`read`。
inductive Code (w : ℕ) : Type → Type → Type 1
  | id {A} : Code w A A
  | fst {A D} : Code w (A × D) A
  | snd {A D} : Code w (A × D) D
  | comp {A D E} : Code w A D → Code w D E → Code w A E
  | pair {A D E} : Code w A D → Code w A E → Code w A (D × E)
  | select {A} : Code w (Bool × A × A) A
  | tab {A D} {h} : h ≤ w → (B h → Code w A D) → Code w A (B h → D)
  | «at» {A} {h} : h ≤ w → B h → Code w (B h → A) A
  | read {A} {h} : h ≤ w → Code w ((B h → A) × B h) A
  | bit {A} : Bool → Code w A Bool
  | lit {A} {h} : h ≤ w → B h → Code w A (B h)
  | gate : Bool → Bool → Bool → Bool → Code w (Bool × Bool) Bool
  | lt {h} : h ≤ w → Code w (B h × B h) Bool
  | eq {h} : h ≤ w → Code w (B h × B h) Bool
  | add {h} : h ≤ w → Code w (B h × B h) (B h)
  | resize {h k} : h ≤ w → k ≤ w → Code w (B h) (B k)
  | odd {h} : h ≤ w → Code w (B h) Bool
  | halve {h} : h ≤ w → Code w (B h) (B h)

namespace Code
variable {w h : ℕ} {A D : Type}

-- 读法：`tabulate` 的取值由 `let a := Vector.ofFn f tab hh (fun i => a[i.val])` 给出。
/-- 先构造子项数组，此后即可按索引读取其元素。

英文原文：Materialize the child array, whose entries can then be read by index.
-/
def tabulate (hh : h ≤ w) (f : B h → Code w A D) : Code w A (B h → D) :=
  let a := Vector.ofFn f
  tab hh (fun i => a[i.val])

-- 读法：逐一匹配输入模式，例如 `_, _, .id, x`、`_, _, .fst, x`、`_, _, .snd, x`、`_, _, .comp f g, x`。
def eval : {A D : Type} → Code w A D → A → D
  | _, _, .id, x => x
  | _, _, .fst, x => x.1
  | _, _, .snd, x => x.2
  | _, _, .comp f g, x => g.eval (f.eval x)
  | _, _, .pair f g, x => (f.eval x, g.eval x)
  | _, _, .select, x => if x.1 then x.2.1 else x.2.2
  | _, _, .tab _ f, x =>
    let a := Vector.ofFn (fun i => (f i).eval x)
    fun i => a[i.val]
  | _, _, .at _ i, x => x i
  | _, _, .read _, x => x.1 x.2
  | _, _, .bit b, _ => b
  | _, _, .lit _ i, _ => i
  | _, _, .gate a b c d, x => if x.1 then (if x.2 then d else c) else (if x.2 then b else a)
  | _, _, .lt _, x => decide (x.1 < x.2)
  | _, _, .eq _, x => decide (x.1 = x.2)
  | _, _, .add _, x => x.1 + x.2
  | _, _, .resize _ _, x => Fin.ofNat _ x.val
  | _, _, .odd _, x => decide (x.val % 2 = 1)
  | _, _, .halve _, x => ⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩

-- 读法：逐一匹配以下输入模式：`_, _, .comp f g`、`_, _, .pair f g`、`_, _, .tab _ f`、`_, _, _`。
/-- 每条指令和每个表槽各计费一次。

英文原文：Charge each instruction once and each table slot once.
-/
def charge (header slot : ℕ) : {A D : Type} → Code w A D → ℕ
  | _, _, .comp f g => header + charge header slot f + charge header slot g
  | _, _, .pair f g => header + charge header slot f + charge header slot g
  | _, _, .tab _ f => header + ∑ i, (slot + charge header slot (f i))
  | _, _, _ => header

-- 读法：`advice` 的取值由 `charge 8 1 c` 给出。
/-- 在八个字长的头部中预留操作码、字面量与宽度字段以及子项引用。每次制表还需为每个子项增加一个引用。

英文原文：Reserve an opcode, literal/width fields, and child references in an
eight-word header. Each tabulation has one additional reference per child.
-/
def advice (c : Code w A D) := charge 8 1 c

-- 读法：`scratch` 的取值由 `charge 8 1 c` 给出。
/-- 每个帧保存操作数、结果和后续执行位置。成对的数据可以留在帧内。制表时每个槽另分配一个结果字。

英文原文：A frame holds operands, result and continuation. Pairs can stay in
the frame. Tabulation allocates one extra result word per slot.
-/
def scratch (c : Code w A D) := charge 8 1 c

-- 读法：`time` 的取值由 `charge 16 4 c` 给出。
/-- 按字计量的成本对指令分派、运算和帧访问收取固定费用。每个表槽的成本包括读取子项偏移和写入结果。

英文原文：Word cost with a fixed charge for dispatch, operations and frame
access. A table slot includes reading its child offset and writing its result.
-/
def time (c : Code w A D) := charge 16 4 c

end Code
end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# 外部宽度与通道宽度分别指定的置换系统

**英文原文**

A permutation system with distinct exterior and channel widths
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring
open scoped Classical
variable {F : Type} {h p w n : ℕ}

-- 读法：结构的字段包括 `selector`、`config`、`dispatch`、`group`、`kernel`。
/-- 外部记录与内部记录的长度可以不同。

英文原文：The exterior and interior record lengths may be different.
-/
structure PaddedSystem (F : Type) (h p w n : ℕ) where
  selector : Format
  config : Format
  dispatch : ((Perm h).pair selector).obj → (Controls h p config).obj
  group : Port h p → ℕ
  kernel : config.obj → (Fin w → Bool) → (Fin w → Bool) → Channels p n → F

-- 读法：在后续公式中，`PaddedPins` 是 `A.pins ⊕ Fin w ⊕ Fin w ⊕ (B p × Fin n)` 的缩写。
abbrev PaddedPins (A : Format) (p w n : ℕ) :=
  A.pins ⊕ Fin w ⊕ Fin w ⊕ (B p × Fin n)

namespace PaddedSystem
variable (S : PaddedSystem F h p w n)

-- 读法：`localWeight` 的结果类型为 `F`。
def localWeight (x : PaddedPins S.config p w n → Bool) : F :=
  S.kernel (S.config.code.symm (x ∘ Sum.inl)) (fun i => x (.inr (.inl i)))
    (fun i => x (.inr (.inr (.inl i)))) (fun i => x (.inr (.inr (.inr i))))

variable [Field F]

-- 读法：`value` 的取值由 `∏ i, S.kernel (v i).1 (x i) (y i) (c i)` 给出。
def value (v : (Controls h p S.config).obj) (x y : Site h → Fin w → Bool)
    (c : Site h → Channels p n) : F :=
  ∏ i, S.kernel (v i).1 (x i) (y i) (c i)

-- 读法：`Correct` 的结果类型为 `Prop`。
/-- 传输量按比特计数，每条连接的两端均计入。

英文原文：Transmission is counted in bits, including both ends of each link.
-/
def Correct (C : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (B h)) (x y : Site h → Fin w → Bool),
    (∀ t c, let v := S.dispatch (σ, t)
      S.value v x y c ≠ 0 → Valid S.group (commands v) ∧
        (Enabled (commands v)).card * n ≤ C * 2 ^ h * w) ∧
    (if ∀ i, x i = y (Routing.inflate h σ i) then (1 : F) else 0) =
      ∑ t : S.selector.pins → Bool, ∑ c : Site h → Channels p n,
        let v := S.dispatch (σ, S.selector.code.symm t)
        S.value v x y c * (if Joins (commands v) c then 1 else 0)

end PaddedSystem

end OAI.LinearAlgebra.MatrixExponent.Transport
end
