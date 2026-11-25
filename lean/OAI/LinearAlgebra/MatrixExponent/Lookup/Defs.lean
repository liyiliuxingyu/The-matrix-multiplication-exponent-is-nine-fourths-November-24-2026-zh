-- 本文件所属证明环节：把批量查表的查询与字典记录排序和分组，用扫描、短标签及重数约束验证选取的表项，再将查表网络接回宽网络。
import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# 对字典记录与查询记录排序

字典行的标志位置一，载荷为一个计数。查询行以零填充。对于同一个键，所有查询行都排在唯一的字典行之前。下述排序假设只涉及这种形式的输入，并要求给出完整的有序输出。

**英文原文**

Sorting dictionary and query records

A dictionary row has its marker set and carries a count as payload. A query
row has zero padding. At a given key, all its queries precede the unique
dictionary row. The sorting hypothesis below concerns only inputs of this
form and requires the complete ordered output.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

-- 读法：在后续公式中，`count` 是 `word (wd a + 1)` 的缩写。
abbrev count (a : Wire) := word (wd a + 1)
-- 读法：在后续公式中，`row` 是 `Wire.pair a (.pair .bit (count a))` 的缩写。
abbrev row (a : Wire) := Wire.pair a (.pair .bit (count a))
-- 读法：在后续公式中，`state` 是 `Wire.pair .bit (count a)` 的缩写。
abbrev state (a : Wire) := Wire.pair .bit (count a)

-- 读法：逐一匹配以下输入模式：`0`、`n + 1`。
def zero : (n : ℕ) → Val (word n)
  | 0 => ()
  | n + 1 => (false, zero n)

-- 读法：逐一匹配以下输入模式：`0, _`、`n + 1, x`。
def inc : (n : ℕ) → Val (word n) → Val (word n)
  | 0, _ => ()
  | n + 1, x => (!x.1, if x.1 then inc n x.2 else x.2)

-- 读法：逐一匹配以下输入模式：`0, _`、`n + 1, x`。
def value : (n : ℕ) → Val (word n) → ℕ
  | 0, _ => 0
  | n + 1, x => x.1.toNat + 2 * value n x.2

-- 读法：`bits` 的取值由 `(inc n)^[k] (zero n)` 给出。
def bits (n k : ℕ) : Val (word n) := (inc n)^[k] (zero n)

-- 读法：当 `r.2.1` 成立时取 `(s.1 && decide (s.2 = r.2.2), zero _)`，否则取 `(s.1, inc _ s.2)`。
def step (a : Wire) (s : Val (state a)) (r : Val (row a)) : Val (state a) :=
  if r.2.1 then (s.1 && decide (s.2 = r.2.2), zero _) else (s.1, inc _ s.2)

-- 读法：`scan` 的取值由 `((flatten l x).foldl (step a) (true, zero _)).1` 给出。
def scan (a : Wire) (l : ℕ) (x : Val (tree l (row a))) : Bool :=
  ((flatten l x).foldl (step a) (true, zero _)).1

-- 读法：`query` 的取值由 `(x, false, zero _)` 给出。
def query (a : Wire) (x : Val a) : Val (row a) := (x, false, zero _)

-- 读法：逐一匹配以下输入模式：`0, x`、`l + 1, x`。
def queries (a : Wire) : (l : ℕ) → Val (tree l a) → Val (tree l (row a))
  | 0, x => query a x
  | l + 1, x => (queries a l x.1, queries a l x.2)

-- 读法：逐一匹配以下输入模式：`0, z, c`、`l + 1, z, c`。
def dict (a : Wire) :
    (l : ℕ) → Val (tree l a) → Val (tree l (count a)) → Val (tree l (row a))
  | 0, z, c => (z, true, c)
  | l + 1, z, c => (dict a l z.1 c.1, dict a l z.2 c.2)

-- 读法：`group` 的取值由 `List.replicate (xs.count r.1) (query a r.1) ++ [r]` 给出。
def group (a : Wire) (xs : List (Val a)) (r : Val (row a)) : List (Val (row a)) :=
  List.replicate (xs.count r.1) (query a r.1) ++ [r]

-- 读法：`Sorting` 的结果类型为 `Prop`。
/-- 将普通宽度的排序界限制到字典行与查询行。字典键按键序将所有地址恰好枚举一次。第二排序键为字典标志。完全相同的查询行无需另行区分先后。

英文原文：The ordinary-width sorting bound restricted to dictionary and query rows.
The keys enumerate all addresses once in key order. The second sort key is
the dictionary marker. Identical query rows require no tie breaking.
-/
def Sorting (F : Type) [Field F] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ a : Wire, let t := wd a
    ∃ (keys : Val (tree t a))
      (sort : Val (tree (t + 1) (row a)) → Val (tree (t + 1) (row a))) (m : ℕ),
      (flatten t keys).Nodup ∧ (∀ z : Val a, z ∈ flatten t keys) ∧
      DNet F (tree (t + 1) (row a)) (tree (t + 1) (row a)) sort m ∧
      (m : ℝ) ≤ C * (2 : ℝ) ^ t * (1 + (t : ℝ)) ^ p ∧
      ∀ (x : Val (tree t a)) (c : Val (tree t (count a))),
        flatten (t + 1) (sort (queries a t x, dict a t keys c)) =
          (flatten t (dict a t keys c)).flatMap (group a (flatten t x))

end OAI.LinearAlgebra.MatrixExponent.Lookup
