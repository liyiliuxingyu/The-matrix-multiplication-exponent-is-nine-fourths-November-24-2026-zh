-- 本文件所属证明环节：按位段执行稳定排序，将短记录与宽记录的带标签置换问题分解成可安装的较小调用，并估计每阶段的槽位与成本。
import OAI.LinearAlgebra.MatrixExponent.Lookup.Defs
import OAI.LinearAlgebra.MatrixExponent.CompareExchange

/-!
# 带备用槽位的各趟稳定基数排序

存在标志被置位表示空槽。对每个数位，每个块都收到一整包分隔符。稳定排序把这些分隔符排在该数位的所有实际记录之后。

**英文原文**

Stable radix passes with spare slots

A set presence flag denotes an empty slot. Each block receives a
pack's worth of separators for every digit. Stability places these
after the real rows of that digit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：`Stable` 表示以下条件：`ys.Perm xs` 与 `ys.Pairwise (fun i j => d i ≤ d j) ∧ ∀ k, ys.filter (fun x => d x = k) = xs.filter (fun x => d x = k)` 同时成立。
def Stable {α : Type} {s : ℕ} (d : α → Val (word s)) (xs ys : List α) : Prop :=
  ys.Perm xs ∧ ys.Pairwise (fun i j => d i ≤ d j) ∧
    ∀ k, ys.filter (fun x => d x = k) = xs.filter (fun x => d x = k)

-- 读法：在后续公式中，`slot` 是 `Wire.pair .bit a` 的缩写。
abbrev slot (a : Wire) := Wire.pair .bit a
-- 读法：在后续公式中，`aug` 是 `Wire.pair (word (s + 1)) (slot a)` 的缩写。
abbrev aug (s : ℕ) (a : Wire) := Wire.pair (word (s + 1)) (slot a)

-- 读法：`real` 的取值由 `(xs.filter (fun r => !r.1)).map Prod.snd` 给出。
def real {α : Type} (xs : List (Bool × α)) : List α :=
  (xs.filter (fun r => !r.1)).map Prod.snd

-- 读法：`real (xs ++ ys)` 等于 `real xs ++ real ys`。
theorem real_append {α : Type} (xs ys : List (Bool × α)) :
    real (xs ++ ys) = real xs ++ real ys := by simp [real]

-- 读法：`decorate` 的取值由 `((x.1, d x.2), x)` 给出。
def decorate {α : Type} {s : ℕ} (d : α → Val (word s)) (x : Bool × α) :
    Val (word (s + 1)) × (Bool × α) := ((x.1, d x.2), x)

-- 读法：`filler` 的取值由 `keys.flatMap (fun k => List.replicate P ((false, k), true, junk)) ++ List.replicate e ((true, Lookup.zero s), true, junk)` 给出。
def filler {α : Type} {s : ℕ} (junk : α) (keys : List (Val (word s))) (P e : ℕ) :
    List (Val (word (s + 1)) × (Bool × α)) :=
  keys.flatMap (fun k => List.replicate P ((false, k), true, junk)) ++
    List.replicate e ((true, Lookup.zero s), true, junk)

-- 读法：`homogeneous` 表示以下条件：对每个 `x ∈ xs`，对每个 `y ∈ xs`，`d x` 等于 `d y`。
def homogeneous {α : Type} {s : ℕ} (d : α → Val (word s)) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, d x = d y

-- 读法：`live` 的取值由 `!(real b).isEmpty` 给出。
def live {α : Type} (b : List (Bool × α)) : Bool := !(real b).isEmpty

end OAI.LinearAlgebra.MatrixExponent.Radix
