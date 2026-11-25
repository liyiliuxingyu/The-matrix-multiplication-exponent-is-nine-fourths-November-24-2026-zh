-- 本文件所属证明环节：把带标签置换、稳定排序和列表判重联系起来；通过给出的归约，把置换验证的困难性转化为批量判重下界。
import OAI.LinearAlgebra.MatrixExponent.Network

section
/-!
# 记录二叉树上的独立标志位

**英文原文**

Independent flags on a binary tree of records
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {a b c : Wire}

-- 读法：逐一匹配以下输入模式：`0, x`、`w + 1, x`。
def mapRows (f : Val a → Val b) : (w : ℕ) → Val (tree w a) → Val (tree w b)
  | 0, x => f x
  | w + 1, x => (mapRows f w x.1, mapRows f w x.2)

-- 读法：逐一匹配以下输入模式：`0, x, y`、`w + 1, x, y`。
def zipRows (f : Val a → Val b → Val c) :
    (w : ℕ) → Val (tree w a) → Val (tree w b) → Val (tree w c)
  | 0, x, y => f x y
  | w + 1, x, y => (zipRows f w x.1 y.1, zipRows f w x.2 y.2)

-- 读法：逐一匹配以下输入模式：`0, z`、`w + 1, z`。
/-- 标志为假时，保留实际记录并赋权负一；为真时，将它标记为虚记录并赋权一。

英文原文：A false flag retains a real record with weight minus one.
A true flag marks it as a dummy with weight one.
-/
def sign (F : Type) [Field F] : (w : ℕ) → Val (tree w .bit) → F
  | 0, z => if z = true then 1 else -1
  | w + 1, z => sign F w z.1 * sign F w z.2

-- 读法：`tested` 的取值由 `(mapRows (E false) w B, zipRows E w z A)` 给出。
def tested (E : Val .bit → Val a → Val b) (w : ℕ) (A B : Val (tree w a))
    (z : Val (tree w .bit)) : Val (tree (w + 1) b) :=
  (mapRows (E false) w B, zipRows E w z A)

-- 读法：当 `(flatten w B).Perm (flatten w A)` 成立时取 `1`，否则取 `0`。
def permuted (F : Type) [Field F] (w : ℕ) (A B : Val (tree w a)) : F :=
  if (flatten w B).Perm (flatten w A) then 1 else 0

-- 读法：`(flatten w x).length` 等于 `2 ^ w`。对 `w` 作归纳。
theorem length_flatten (w : ℕ) (x : Val (tree w a)) : (flatten w x).length = 2 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [flatten, ih, pow_succ, mul_two]

-- 读法：`flatten w (mapRows f w x)` 等于 `(flatten w x).map f`。对 `w` 作归纳。
theorem flatten_mapRows (f : Val a → Val b) (w : ℕ) (x : Val (tree w a)) :
    flatten w (mapRows f w x) = (flatten w x).map f := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [flatten, mapRows, List.map_append, ih]

-- 读法：存在 `p ∈ flatten w x`，存在 `q ∈ flatten w y`，`f p q` 等于 `v`。对 `w` 作归纳。
theorem mem_zipRows (f : Val a → Val b → Val c) (w : ℕ)
    (x : Val (tree w a)) (y : Val (tree w b)) {v : Val c}
    (h : v ∈ flatten w (zipRows f w x y)) :
    ∃ p ∈ flatten w x, ∃ q ∈ flatten w y, f p q = v := by
  induction w with
  | zero => exact ⟨x, by simp [flatten], y, by simp [flatten], (List.mem_singleton.mp h).symm⟩
  | succ w ih =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨p, hp, q, hq, he⟩ := ih _ _ h
      exact ⟨p, List.mem_append_left _ hp, q, List.mem_append_left _ hq, he⟩
    · obtain ⟨p, hp, q, hq, he⟩ := ih _ _ h
      exact ⟨p, List.mem_append_right _ hp, q, List.mem_append_right _ hq, he⟩

-- 读法：要证明的命题是 `(flatten w (zipRows f w x y)).Nodup`。对 `w` 作归纳。
theorem nodup_zipRows (f : Val a → Val b → Val c)
    (hf : ∀ p q x y, f p x = f q y → x = y) (w : ℕ)
    (x : Val (tree w a)) (y : Val (tree w b)) (hy : (flatten w y).Nodup) :
    (flatten w (zipRows f w x y)).Nodup := by
  induction w with
  | zero => simp [flatten]
  | succ w ih =>
    obtain ⟨h₁, h₂, h₃⟩ := List.nodup_append.mp hy
    refine List.nodup_append.mpr ⟨ih _ _ h₁, ih _ _ h₂, ?_⟩
    intro u hu v hv he
    obtain ⟨p, _, i, hi, rfl⟩ := mem_zipRows f _ _ _ hu
    obtain ⟨q, _, j, hj, rfl⟩ := mem_zipRows f _ _ _ hv
    exact h₃ _ hi _ hj (hf _ _ _ _ he)

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# 带标签的置换张量

**英文原文**

The tagged permutation tensor
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

-- 读法：在后续公式中，`row` 是 `Wire.pair (word w) a` 的缩写。
abbrev row (w : ℕ) (a : Wire) := Wire.pair (word w) a

-- 读法：在后续公式中，`inputs` 是 `Wire.pair (tree w a) (tree w (row w a))` 的缩写。
/-- 无标签的输入行，以及带标签的候选输出行。

英文原文：Untagged input rows and tagged proposed output rows.
-/
abbrev inputs (w : ℕ) (a : Wire) := Wire.pair (tree w a) (tree w (row w a))

-- 读法：逐一匹配以下输入模式：`0`、`w + 1`。
/-- 从零到 `2^w-1` 依次排列的二进制地址。

英文原文：The binary addresses in order from zero to `2^w-1`.
-/
def indices : (w : ℕ) → Val (tree w (word w))
  | 0 => ()
  | w + 1 =>
    (mapRows (a := word w) (b := word (w + 1)) (fun i => (false, i)) w (indices w),
     mapRows (a := word w) (b := word (w + 1)) (fun i => (true, i)) w (indices w))

-- 读法：要证明的命题是 `(flatten w (indices w)).Nodup`。对 `w` 作归纳。
theorem indices_nodup (w : ℕ) : (flatten w (indices w)).Nodup := by
  induction w with
  | zero => simp [flatten]
  | succ w ih =>
    simp only [indices, flatten, flatten_mapRows, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => congrArg Prod.snd h), ih.map (fun _ _ h => congrArg Prod.snd h), ?_⟩
    intro x hx y hy
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
    exact fun h => Bool.false_ne_true (congrArg Prod.fst h)

-- 读法：`label` 的取值由 `zipRows (c := row w a) (fun y i => (i, y)) w x (indices w)` 给出。
def label {a : Wire} (w : ℕ) (x : Val (tree w a)) : Val (tree w (row w a)) :=
  zipRows (c := row w a) (fun y i => (i, y)) w x (indices w)

-- 读法：要证明的命题是 `(flatten w (label w x)).Nodup`。使用 `nodup_zipRows` 给出的结论。
theorem label_nodup {a : Wire} (w : ℕ) (x : Val (tree w a)) :
    (flatten w (label w x)).Nodup :=
  nodup_zipRows _ (fun _ _ _ _ h => congrArg Prod.fst h) _ _ _ (indices_nodup w)

-- 读法：`tag` 的取值由 `permuted F w (label w x.1) x.2` 给出。
def tag (F : Type) [Field F] (w : ℕ) (a : Wire)
    (x : Val (inputs w a)) (_ : Val .unit) : F :=
  permuted F w (label w x.1) x.2

end OAI.LinearAlgebra.MatrixExponent.Tagged
end
