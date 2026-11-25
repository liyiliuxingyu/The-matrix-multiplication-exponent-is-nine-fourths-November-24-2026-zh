-- 本文件所属证明环节：递归定义平衡数组上的双调排序，并证明比较交换和归并保持输入记录的重集。
import OAI.LinearAlgebra.MatrixExponent.Network

/-!
# 平衡数组上的 Batcher 双调排序网络

**英文原文**

Batcher's bitonic sorting network on balanced arrays
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
def reverseTree {a : Wire} : (w : ℕ) → Val (tree w a) → Val (tree w a)
  | 0, x => x
  | w + 1, x => (reverseTree w x.2, reverseTree w x.1)

-- 读法：`flatten w (reverseTree w x)` 等于 `(flatten w x).reverse`。对 `w` 作归纳。
theorem flatten_reverseTree {a : Wire} (w : ℕ) (x : Val (tree w a)) :
    flatten w (reverseTree w x) = (flatten w x).reverse := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [reverseTree, flatten, List.reverse_append, ih]

variable {a : Wire} [LinearOrder (Val a)]

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
/-- 比较相对位置上的条目，将较小者放入左子树。

英文原文：Compare opposite entries, putting the smaller one in the left subtree.
-/
def splitTree : (w : ℕ) → Val (tree (w + 1) a) → Val (tree (w + 1) a)
  | 0, x => (min x.1 x.2, max x.1 x.2)
  | w + 1, x =>
    let p := splitTree w (x.1.1, x.2.1)
    let q := splitTree w (x.1.2, x.2.2)
    ((p.1, q.1), (p.2, q.2))

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
def mergeTree : (w : ℕ) → Val (tree w a) → Val (tree w a)
  | 0, x => x
  | w + 1, x =>
    let p := splitTree w x
    (mergeTree w p.1, mergeTree w p.2)

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
def sortTree : (w : ℕ) → Val (tree w a) → Val (tree w a)
  | 0, x => x
  | w + 1, x =>
    mergeTree (w + 1) (sortTree w x.1, reverseTree w (sortTree w x.2))

-- 读法：要证明的命题是 `((l₁ ++ l₂) ++ (l₃ ++ l₄)).Perm ((l₁ ++ l₃) ++ (l₂ ++ l₄))`。
private theorem perm_swap_middle {α : Type} (l₁ l₂ l₃ l₄ : List α) :
    ((l₁ ++ l₂) ++ (l₃ ++ l₄)).Perm ((l₁ ++ l₃) ++ (l₂ ++ l₄)) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm_assoc l₂ l₃ l₄).append_left l₁

-- 读法：要证明的命题是 `(flatten (w + 1) (splitTree w x)).Perm (flatten (w + 1) x)`。对 `w` 作归纳。
theorem splitTree_perm (w : ℕ) (x : Val (tree (w + 1) a)) :
    (flatten (w + 1) (splitTree w x)).Perm (flatten (w + 1) x) := by
  induction w with
  | zero =>
    change [min x.1 x.2, max x.1 x.2].Perm [x.1, x.2]
    rcases le_total x.1 x.2 with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact List.Perm.swap ..
  | succ w ih =>
    let p := splitTree w (x.1.1, x.2.1)
    let q := splitTree w (x.1.2, x.2.2)
    exact (perm_swap_middle (flatten w p.1) (flatten w q.1)
      (flatten w p.2) (flatten w q.2)).trans
      (((ih (x.1.1, x.2.1)).append (ih (x.1.2, x.2.2))).trans
        (perm_swap_middle (flatten w x.1.1) (flatten w x.2.1)
          (flatten w x.1.2) (flatten w x.2.2)))

-- 读法：要证明的命题是 `(flatten w (mergeTree w x)).Perm (flatten w x)`。对 `w` 作归纳。
theorem mergeTree_perm (w : ℕ) (x : Val (tree w a)) :
    (flatten w (mergeTree w x)).Perm (flatten w x) := by
  induction w with
  | zero => exact List.Perm.refl _
  | succ w ih =>
    exact ((ih (splitTree w x).1).append (ih (splitTree w x).2)).trans (splitTree_perm w x)

-- 读法：要证明的命题是 `(flatten w (sortTree w x)).Perm (flatten w x)`。对 `w` 作归纳。
theorem sortTree_perm (w : ℕ) (x : Val (tree w a)) :
    (flatten w (sortTree w x)).Perm (flatten w x) := by
  induction w with
  | zero => exact List.Perm.refl _
  | succ w ih =>
    apply (mergeTree_perm (w + 1) (sortTree w x.1, reverseTree w (sortTree w x.2))).trans
    simp only [flatten, flatten_reverseTree]
    exact (ih x.1).append ((List.reverse_perm _).trans (ih x.2))

end OAI.LinearAlgebra.MatrixExponent
