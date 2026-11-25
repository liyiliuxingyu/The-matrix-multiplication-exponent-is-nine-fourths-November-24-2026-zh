-- 本文件所属证明环节：定义三价比特网络及多表判重张量的实现关系，并通过表分解和基域转换比较不同实现的成本。
import OAI.LinearAlgebra.MatrixExponent.ListBounds

/-!
# 三价比特网络

比特束是一棵由比特位置构成的二叉树。重新布线只置换位置，并允许改变括号的结合方式。将顶点表并置、连接各条连线并对共享值求和，即构成网络。取迹允许内部成环。规模按顶点数与外部比特数计算。

**英文原文**

Trivalent bit networks

A bundle is a binary tree of bit positions. Rewiring only permutes the
positions (with changes of parenthesization). Networks are built by
juxtaposing vertex tables and joining wires, summing over their shared
values. Trace allows internal cycles. Size counts vertices and exterior bits.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：归纳构造子包括 `bit`、`unit`、`pair`。
inductive Wire
  | bit
  | unit
  | pair (a b : Wire)

-- 读法：在后续公式中，`Val` 是 `| .bit => Bool | .unit => Unit | .pair a b => Val a × Val b` 的缩写。
abbrev Val : Wire → Type
  | .bit => Bool
  | .unit => Unit
  | .pair a b => Val a × Val b

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
instance valFintype : (a : Wire) → Fintype (Val a)
  | .bit => inferInstanceAs (Fintype Bool)
  | .unit => inferInstanceAs (Fintype Unit)
  | .pair a b =>
    letI := valFintype a
    letI := valFintype b
    inferInstanceAs (Fintype (Val a × Val b))

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
instance valDecidableEq : (a : Wire) → DecidableEq (Val a)
  | .bit => inferInstanceAs (DecidableEq Bool)
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .pair a b =>
    letI := valDecidableEq a
    letI := valDecidableEq b
    inferInstanceAs (DecidableEq (Val a × Val b))

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
def wd : Wire → ℕ
  | .bit => 1
  | .unit => 0
  | .pair a b => wd a + wd b

-- 读法：归纳构造子包括 `id`、`swap`、`assoc`、`assoc'`、`unit`、`unit'`、`comp`、`par`。
inductive Rewire : (a b : Wire) → (Val a → Val b) → Prop
  | id (a) : Rewire a a (fun x => x)
  | swap (a b) : Rewire (.pair a b) (.pair b a) (fun x => (x.2, x.1))
  | assoc (a b c) : Rewire (.pair (.pair a b) c) (.pair a (.pair b c))
      (fun x => (x.1.1, x.1.2, x.2))
  | assoc' (a b c) : Rewire (.pair a (.pair b c)) (.pair (.pair a b) c)
      (fun x => ((x.1, x.2.1), x.2.2))
  | unit (a) : Rewire (.pair a .unit) a (fun x => x.1)
  | unit' (a) : Rewire a (.pair a .unit) (fun x => (x, ()))
  | comp {a b c f g} : Rewire a b f → Rewire b c g → Rewire a c (fun x => g (f x))
  | par {a b c d f g} : Rewire a b f → Rewire c d g →
      Rewire (.pair a c) (.pair b d) (fun x => (f x.1, g x.2))

-- 读法：归纳构造子包括 `empty`、`table`、`par`、`comp`、`trace`、`pre`、`post`。
/-- 最后一个索引只计顶点，不计外部连线。

英文原文：The last index counts vertices, excluding exterior wires.
-/
inductive Net (F : Type) [Field F] : (a b : Wire) → (Val a → Val b → F) → ℕ → Prop
  | empty : Net F .unit .unit (fun _ _ => 1) 0
  | table (a b) (k : Val a → Val b → F) (h : wd a + wd b ≤ 3) : Net F a b k 1
  | par {a b c d k l m n} : Net F a b k m → Net F c d l n →
      Net F (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n)
  | comp {a b c k l m n} : Net F a b k m → Net F b c l n →
      Net F a c (fun x z => ∑ y : Val b, k x y * l y z) (m + n)
  | trace {a b c k m} : Net F (.pair a c) (.pair b c) k m →
      Net F a b (fun x y => ∑ z : Val c, k (x, z) (y, z)) m
  | pre {a b c f k m} : Net F b c k m → Rewire a b f →
      Net F a c (fun x y => k (f x) y) m
  | post {a b c f k m} : Net F a b k m → Rewire c b f →
      Net F a c (fun x y => k x (f y)) m

-- 读法：在后续公式中，`word` 是 `| 0 => .unit | n + 1 => .pair .bit (word n)` 的缩写。
abbrev word : ℕ → Wire
  | 0 => .unit
  | n + 1 => .pair .bit (word n)

-- 读法：在后续公式中，`tree` 是 `| 0, a => a | w + 1, a => .pair (tree w a) (tree w a)` 的缩写。
abbrev tree : ℕ → Wire → Wire
  | 0, a => a
  | w + 1, a => .pair (tree w a) (tree w a)

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
def flatten {a : Wire} : (w : ℕ) → Val (tree w a) → List (Val a)
  | 0, x => [x]
  | w + 1, x => flatten w x.1 ++ flatten w x.2

-- 读法：在后续公式中，`lists` 是 `| 0 => .unit | t + 1 => .pair (tree w (word (2 * w))) (lists w t)` 的缩写。
abbrev lists (w : ℕ) : ℕ → Wire
  | 0 => .unit
  | t + 1 => .pair (tree w (word (2 * w))) (lists w t)

-- 读法：逐一匹配以下输入模式：`0, _`、`t + 1, x`。
def distinctPower (F : Type) [Field F] (w : ℕ) : (t : ℕ) → Val (lists w t) → F
  | 0, _ => 1
  | t + 1, x => (if (flatten w x.1).Nodup then 1 else 0) * distinctPower F w t x.2

-- 读法：`Realizes` 表示以下条件：存在 `v`，`Net F (lists w t) .unit (fun x _ => distinctPower F w t x) v` 与 `m = v + t * listBits w` 同时成立。
def Realizes (F : Type) [Field F] (w t m : ℕ) : Prop :=
  ∃ v, Net F (lists w t) .unit (fun x _ => distinctPower F w t x) v ∧ m = v + t * listBits w

end OAI.LinearAlgebra.MatrixExponent
