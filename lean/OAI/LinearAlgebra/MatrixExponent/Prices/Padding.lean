-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic

/-!
# 添入平凡张量腿后的限制

嵌入保持乘积。在更大的站点集上取直和，将为每条新增的腿赋予块标签。因此一个方向上只能得到不等式，另一个方向上则可使用相互独立的闭包。

**英文原文**

Restriction after adjoining trivial legs

The embedding preserves products. A direct sum over the larger site
set gives each extra leg a block label. This costs an inequality in
one direction and permits independent closures in the other.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices

-- 读法：结构的字段包括 `zero`、`one`、`le_iff`、`mul`、`add_le`。
structure Padding {S T : Type*} [CommSemiring S] [CommSemiring T]
    [PartialOrder S] [PartialOrder T] (pad : S → T) : Prop where
  zero : pad 0 = 0
  one : pad 1 = 1
  le_iff (s t) : pad s ≤ pad t ↔ s ≤ t
  mul (s t) : pad (s * t) = pad s * pad t
  add_le (s t) : pad (s + t) ≤ pad s + pad t
  split {s x y} : pad s ≤ x + y → ∃ a b, pad a ≤ x ∧ pad b ≤ y ∧ s ≤ a + b
  factor {s a x} : pad s ≤ pad a * x → ∃ b, pad b ≤ x ∧ s ≤ a * b

end OAI.LinearAlgebra.MatrixExponent.Prices
