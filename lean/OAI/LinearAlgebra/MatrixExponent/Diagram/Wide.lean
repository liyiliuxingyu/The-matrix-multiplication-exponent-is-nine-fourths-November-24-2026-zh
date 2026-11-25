-- 本文件所属证明环节：用有限有向多重图表示带端口的比特张量网络，证明细分、重编号、替换及取幂对张量收缩和规模的影响。
import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork
import OAI.LinearAlgebra.MatrixExponent.Network

section
/-!
# 独立比特线束上的张量幂

乘积、连接与重新分组都由外部位置的结构置换实现。所有比特都保持独立且完整，无须用门合并或丢弃比特。

**英文原文**

Tensor powers on independent bit bundles

Products, concatenation and regrouping are witnessed by structural
permutations of the exterior positions. No gates identify or discard bits.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：在后续公式中，`copies` 是 `| 0 => .unit | d + 1 => .pair a (copies a d)` 的缩写。
abbrev copies (a : Wire) : ℕ → Wire
  | 0 => .unit
  | d + 1 => .pair a (copies a d)

-- 读法：`wd (copies a d)` 等于 `d * wd a`。对 `d` 作归纳。
@[simp] theorem wd_copies (a : Wire) (d : ℕ) : wd (copies a d) = d * wd a := by
  induction d with
  | zero => simp [wd]
  | succ d ih => simp [wd, ih, Nat.succ_mul, Nat.add_comm]

-- 读法：逐一匹配以下输入模式：`0`、`d + 1`。
def unitCopies : (d : ℕ) → Val (copies .unit d)
  | 0 => ()
  | d + 1 => ((), unitCopies d)

-- 读法：仅通过重新接线，从格式 `.unit` 变换到 `(copies .unit d)`，实现映射 `(fun _ => MatrixExponent.unitCopies d)`。对 `d` 作归纳。
theorem Rewire.unitCopies (d : ℕ) : Rewire .unit (copies .unit d) (fun _ => MatrixExponent.unitCopies d) := by
  induction d with
  | zero => exact .id .unit
  | succ d ih => exact (Rewire.unit' .unit).comp ((Rewire.id .unit).par ih)

-- 读法：仅通过重新接线，从格式 `(copies .unit d)` 变换到 `.unit`，实现映射 `(fun _ => ())`。
theorem Rewire.copiesUnit (d : ℕ) : Rewire (copies .unit d) .unit (fun _ => ()) := by
  obtain ⟨_, h, _⟩ := (unitCopies d).inverse
  exact h

-- 读法：`x` 等于 `unitCopies d`。对 `d` 作归纳。
theorem eq_unitCopies (d : ℕ) (x : Val (copies .unit d)) : x = unitCopies d := by
  induction d with
  | zero => rfl
  | succ d ih => exact Prod.ext rfl (ih x.2)

variable {F : Type} [Field F] {a b c d : Wire}

-- 读法：存在从 `c` 到 `d` 的网络，核为 `l`，顶点数为 `m`，系数取自 `F`。用函数外延性比较等号两侧在 `x y` 处的取值。
/-- 沿各置换的正方向搬运网络。

英文原文：Transport a network along permutations in the forward direction.
-/
theorem Net.rewire {k : Val a → Val b → F} {l : Val c → Val d → F}
    {f : Val a → Val c} {g : Val b → Val d} {m : ℕ}
    (h : Net F a b k m) (hf : Rewire a c f) (hg : Rewire b d g)
    (he : ∀ x y, l (f x) (g y) = k x y) : Net F c d l m := by
  obtain ⟨f', hf', ef⟩ := hf.inverse
  obtain ⟨g', hg', eg⟩ := hg.inverse
  have hl : l = fun x y => k (f' x) (g' y) := by
    funext x y
    rw [← he, (ef _ x).mpr rfl, (eg _ y).mpr rfl]
  rw [hl]
  exact (h.pre hf').post hg'

-- 读法：逐一匹配以下输入模式：`0, _, _`、`d + 1, x, y`。
def power (k : Val a → Val b → F) : (d : ℕ) → Val (copies a d) → Val (copies b d) → F
  | 0, _, _ => 1
  | d + 1, x, y => k x.1 y.1 * power k d x.2 y.2

-- 读法：存在从 `(copies a d)` 到 `(copies b d)` 的网络，核为 `(MatrixExponent.power k d)`，顶点数为 `(d * m)`，系数取自 `F`。对 `d` 作归纳。
theorem Net.power {k : Val a → Val b → F} {m : ℕ} (h : Net F a b k m) (d : ℕ) :
    Net F (copies a d) (copies b d) (MatrixExponent.power k d) (d * m) := by
  induction d with
  | zero => rw [Nat.zero_mul]; exact .empty
  | succ d ih => rw [Nat.succ_mul, Nat.add_comm (d * m) m]; exact h.par ih

-- 读法：逐一匹配以下输入模式：`0, _`、`t + 1, x`。
def zipCopies (a b : Wire) :
    (t : ℕ) → Val (.pair (copies a t) (copies b t)) → Val (copies (.pair a b) t)
  | 0, _ => ()
  | t + 1, x => ((x.1.1, x.2.1), zipCopies a b t (x.1.2, x.2.2))

-- 读法：仅通过重新接线，从格式 `(.pair (copies a t) (copies b t))` 变换到 `(copies (.pair a b) t)`，实现映射 `(MatrixExponent.zipCopies a b t)`。对 `t` 作归纳。
theorem Rewire.zipCopies (a b : Wire) (t : ℕ) :
    Rewire (.pair (copies a t) (copies b t)) (copies (.pair a b) t) (MatrixExponent.zipCopies a b t) := by
  induction t with
  | zero => exact .unit .unit
  | succ t ih =>
    exact (Rewire.middle a _ b _).comp ((Rewire.id (.pair a b)).par ih)

-- 读法：对 `t` 作归纳。
theorem power_zip (k : Val a → Val b → F) (l : Val c → Val d → F) (t : ℕ)
    (x : Val (.pair (copies a t) (copies c t))) (y : Val (.pair (copies b t) (copies d t))) :
    power (fun (s : Val (.pair a c)) (u : Val (.pair b d)) => k s.1 u.1 * l s.2 u.2) t
      (zipCopies a c t x) (zipCopies b d t y) = power k t x.1 y.1 * power l t x.2 y.2 := by
  induction t with
  | zero => simp [power]
  | succ t ih =>
    simp only [power, zipCopies, ih]
    exact mul_mul_mul_comm _ _ _ _

-- 读法：逐一匹配以下输入模式：`0, _, x`、`m + 1, n, x`。
/-- 第一块的长度为 m。将总长度写成 n+m，便可直接按第一块使用 Lean 的递归定义，无须作类型转换。

英文原文：The first block has length m. Writing the sum as n+m exposes Lean's
recursion on the first block without casts.
-/
def appendCopies (a : Wire) :
    (m n : ℕ) → Val (.pair (copies a m) (copies a n)) → Val (copies a (n + m))
  | 0, _, x => x.2
  | m + 1, n, x => (x.1.1, appendCopies a m n (x.1.2, x.2))

-- 读法：仅通过重新接线，从格式 `(.pair (copies a m) (copies a n))` 变换到 `(copies a (n + m))`，实现映射 `(MatrixExponent.appendCopies a m n)`。对 `m` 作归纳。
theorem Rewire.appendCopies (a : Wire) (m n : ℕ) :
    Rewire (.pair (copies a m) (copies a n)) (copies a (n + m)) (MatrixExponent.appendCopies a m n) := by
  induction m with
  | zero => exact (Rewire.swap .unit _).comp (.unit _)
  | succ m ih => exact (Rewire.assoc a _ _).comp ((Rewire.id a).par ih)

-- 读法：`power k (n + m) (appendCopies a m n x) (appendCopies b m n y)` 等于 `power k m x.1 y.1 * power k n x.2 y.2`。对 `m` 作归纳。
theorem power_append (k : Val a → Val b → F) (m n : ℕ)
    (x : Val (.pair (copies a m) (copies a n))) (y : Val (.pair (copies b m) (copies b n))) :
    power k (n + m) (appendCopies a m n x) (appendCopies b m n y) =
      power k m x.1 y.1 * power k n x.2 y.2 := by
  induction m with
  | zero => simp [appendCopies, power]
  | succ m ih =>
    change k x.1.1 y.1.1 * power k (n + m) (appendCopies a m n _) (appendCopies b m n _) = _
    rw [ih]
    exact (mul_assoc _ _ _).symm

-- 读法：逐一匹配以下输入模式：`0, _`、`t + 1, x`。
def joinCopies (a : Wire) (d : ℕ) :
    (t : ℕ) → Val (copies (copies a d) t) → Val (copies a (d * t))
  | 0, _ => ()
  | t + 1, x => appendCopies a d (d * t) (x.1, joinCopies a d t x.2)

-- 读法：仅通过重新接线，从格式 `(copies (copies a d) t)` 变换到 `(copies a (d * t))`，实现映射 `(MatrixExponent.joinCopies a d t)`。对 `t` 作归纳。
theorem Rewire.joinCopies (a : Wire) (d t : ℕ) :
    Rewire (copies (copies a d) t) (copies a (d * t)) (MatrixExponent.joinCopies a d t) := by
  induction t with
  | zero => exact .id .unit
  | succ t ih => exact ((Rewire.id _).par ih).comp (appendCopies a d (d * t))

-- 读法：`power k (d * t) (joinCopies a d t x) (joinCopies b d t y)` 等于 `power (power k d) t x y`。对 `t` 作归纳。
theorem power_join (k : Val a → Val b → F) (d t : ℕ)
    (x : Val (copies (copies a d) t)) (y : Val (copies (copies b d) t)) :
    power k (d * t) (joinCopies a d t x) (joinCopies b d t y) = power (power k d) t x y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change power k (d * t + d) (appendCopies a d (d * t) _) (appendCopies b d (d * t) _) = _
    rw [power_append, ih]
    rfl

-- 读法：逐一匹配以下输入模式：`0, _`、`t + 1, x`。
def mapCopies (f : Val a → Val b) : (t : ℕ) → Val (copies a t) → Val (copies b t)
  | 0, _ => ()
  | t + 1, x => (f x.1, mapCopies f t x.2)

-- 读法：仅通过重新接线，从格式 `(copies a t)` 变换到 `(copies b t)`，实现映射 `(MatrixExponent.mapCopies f t)`。对 `t` 作归纳。
theorem Rewire.mapCopies {f : Val a → Val b} (h : Rewire a b f) (t : ℕ) :
    Rewire (copies a t) (copies b t) (MatrixExponent.mapCopies f t) := by
  induction t with
  | zero => exact .id .unit
  | succ t ih => exact h.par ih

-- 读法：`power l t (mapCopies f t x) (mapCopies g t y)` 等于 `power k t x y`。对 `t` 作归纳。
theorem power_map {f : Val a → Val c} {g : Val b → Val d}
    {k : Val a → Val b → F} {l : Val c → Val d → F}
    (he : ∀ x y, l (f x) (g y) = k x y) (t : ℕ) (x : Val (copies a t)) (y : Val (copies b t)) :
    power l t (mapCopies f t x) (mapCopies g t y) = power k t x y := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [power, mapCopies, he, ih]

-- 读法：逐一匹配以下输入模式：`0, _`、`t + 1, x`。
def listCopies (w : ℕ) :
    (t : ℕ) → Val (lists w t) → Val (copies (tree w (word (2 * w))) t)
  | 0, _ => ()
  | t + 1, x => (x.1, listCopies w t x.2)

-- 读法：仅通过重新接线，从格式 `(lists w t)` 变换到 `(copies (tree w (word (2 * w))) t)`，实现映射 `(MatrixExponent.listCopies w t)`。对 `t` 作归纳。
theorem Rewire.listCopies (w t : ℕ) :
    Rewire (lists w t) (copies (tree w (word (2 * w))) t) (MatrixExponent.listCopies w t) := by
  induction t with
  | zero => exact .id .unit
  | succ t ih => exact (Rewire.id _).par ih

-- 读法：对 `t` 作归纳。
theorem power_distinct (F : Type) [Field F] (w t : ℕ) (x : Val (lists w t))
    (y : Val (copies .unit t)) :
    power (fun (z : Val (tree w (word (2 * w)))) (_ : Val .unit) =>
      if (flatten w z).Nodup then (1 : F) else 0) t (listCopies w t x) y =
        distinctPower F w t x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [power, listCopies, distinctPower, ih]
    rfl

-- 读法：存在从 `(lists w (t * d))` 到 `.unit` 的网络，核为 `(fun x _ => distinctPower F w (t * d) x)`，顶点数为 `v`，系数取自 `F`。
/-- 将含有 t 个列表的批次复制 d 份，所得 t*d 个列表仍彼此独立。

英文原文：Taking d copies of a batch of t lists keeps all t*d lists independent.
-/
theorem Net.power_lists {w t d v : ℕ}
    (h : Net F (copies (lists w t) d) (copies .unit d)
      (MatrixExponent.power (fun x (_ : Val .unit) => distinctPower F w t x) d) v) :
    Net F (lists w (t * d)) .unit (fun x _ => distinctPower F w (t * d) x) v := by
  let a := tree w (word (2 * w))
  let k (z : Val a) (_ : Val .unit) : F := if (flatten w z).Nodup then 1 else 0
  have h₁ : Net F (copies (copies a t) d) (copies (copies .unit t) d)
      (MatrixExponent.power (MatrixExponent.power k t) d) v :=
    h.rewire ((Rewire.listCopies w t).mapCopies d) ((Rewire.unitCopies t).mapCopies d)
      (power_map (fun x _ => power_distinct F w t x (unitCopies t)) d)
  have h₂ := h₁.rewire (Rewire.joinCopies a t d) (Rewire.joinCopies .unit t d) (power_join k t d)
  have h₃ := (h₂.pre (Rewire.listCopies w (t * d))).post (Rewire.unitCopies (t * d))
  have e : (fun x (_ : Val .unit) =>
      MatrixExponent.power k (t * d) (listCopies w (t * d) x) (unitCopies (t * d))) =
      (fun x _ => distinctPower F w (t * d) x) := by
    funext x y
    exact power_distinct F w (t * d) x (unitCopies (t * d))
  rw [← e]
  exact h₃


-- 读法：`castCopies` 的取值由 `h ▸ x` 给出。
private def castCopies (a : Wire) {m n : ℕ} (h : m = n) (x : Val (copies a m)) :
    Val (copies a n) := h ▸ x

-- 读法：仅通过重新接线，从格式 `(copies a m)` 变换到 `(copies a n)`，实现映射 `(castCopies a h)`。
private theorem rewire_castCopies (a : Wire) {m n : ℕ} (h : m = n) :
    Rewire (copies a m) (copies a n) (castCopies a h) := by
  subst n
  exact .id _

-- 读法：`power k n (castCopies a h x) y` 等于 `power k m x (unitCopies m)`。
private theorem power_cast (k : Val a → Val .unit → F) {m n : ℕ} (h : m = n) x y :
    power k n (castCopies a h x) y = power k m x (unitCopies m) := by
  subst n
  rw [eq_unitCopies _ y]
  rfl

-- 读法：`2 ^ u + 2 ^ u` 等于 `2 ^ (u + 1)`。
private theorem two_pow_add (u : ℕ) : 2 ^ u + 2 ^ u = 2 ^ (u + 1) := by rw [pow_succ, mul_two]

-- 读法：逐一匹配以下输入模式：`0, x`、`u + 1, x`。
def treeCopies (a : Wire) : (u : ℕ) → Val (tree u a) → Val (copies a (2 ^ u))
  | 0, x => (x, ())
  | u + 1, x => castCopies a (two_pow_add u)
      (appendCopies a (2 ^ u) (2 ^ u) (treeCopies a u x.1, treeCopies a u x.2))

-- 读法：仅通过重新接线，从格式 `(tree u a)` 变换到 `(copies a (2 ^ u))`，实现映射 `(MatrixExponent.treeCopies a u)`。对 `u` 作归纳。
theorem Rewire.treeCopies (a : Wire) (u : ℕ) :
    Rewire (tree u a) (copies a (2 ^ u)) (MatrixExponent.treeCopies a u) := by
  induction u with
  | zero => exact .unit' a
  | succ u ih =>
    exact ((ih.par ih).comp (appendCopies a _ _)).comp (rewire_castCopies a (two_pow_add u))

-- 读法：`power k (2 ^ u) (treeCopies a u x) y` 等于 `((flatten u x).map (fun z => k z ())).prod`。对 `u` 作归纳。
theorem power_tree (k : Val a → Val .unit → F) (u : ℕ)
    (x : Val (tree u a)) (y : Val (copies .unit (2 ^ u))) :
    power k (2 ^ u) (treeCopies a u x) y = ((flatten u x).map (fun z => k z ())).prod := by
  induction u with
  | zero =>
    change k x () * 1 = _
    simp [flatten]
  | succ u ih =>
    let z := unitCopies (2 ^ u)
    rw [treeCopies, power_cast, ← eq_unitCopies _ (appendCopies .unit (2 ^ u) (2 ^ u) (z, z)),
      power_append, ih, ih, flatten, List.map_append, List.prod_append]

end OAI.LinearAlgebra.MatrixExponent
end

section
/-!
# 任意元数的网络

站点成本是一加上该站点的元数。用表上的谓词记录允许的标签。连接和重排均不会使新的位置外露。

**英文原文**

Networks of arbitrary arity

The cost of a station is one plus its arity. A predicate on tables
tracks allowed labels. Joins and reordering expose no new positions.
-/

namespace OAI.LinearAlgebra.MatrixExponent

section
variable {F K : Type} [Field F] [Field K] {a b : Wire}
variable {k : Val a → Val b → F} {m : ℕ}

-- 读法：存在从 `a` 到 `b` 的网络，核为 `(fun x y => f (k x y))`，顶点数为 `m`，系数取自 `K`。对 `h` 作归纳。
theorem Net.map (h : Net F a b k m) (f : F →+* K) :
    Net K a b (fun x y => f (k x y)) m := by
  induction h with
  | empty => simpa only [map_one] using (Net.empty (F := K))
  | table _ _ _ ht => exact .table _ _ _ ht
  | par _ _ ih ig => simpa only [map_mul] using ih.par ig
  | comp _ _ ih ig => simpa only [map_sum, map_mul] using ih.comp ig
  | trace _ ih => simpa only [map_sum] using ih.trace
  | pre _ hr ih => exact ih.pre hr
  | post _ hr ih => exact ih.post hr

-- 读法：`wd a` 等于 `wd b`。
theorem Rewire.width {f : Val a → Val b} (h : Rewire a b f) : wd a = wd b := by
  induction h <;> simp_all only [wd] <;> omega

end

-- 读法：在后续公式中，`Table` 是 `Σ a b : Wire, Val a → Val b → K` 的缩写。
abbrev Table (K : Type) := Σ a b : Wire, Val a → Val b → K

-- 读法：归纳构造子包括 `empty`、`table`、`par`、`comp`、`trace`、`pre`、`post`。
inductive Wide (K : Type) [Field K] (u : ℕ) (labels : Set (Table K)) :
    (a b : Wire) → (Val a → Val b → K) → ℕ → Prop
  | empty : Wide K u labels .unit .unit (fun _ _ => 1) 0
  | table (a b) (k : Val a → Val b → K) (arity : wd a + wd b ≤ u)
      (label : wd a + wd b ≤ 3 ∨ ⟨a, b, k⟩ ∈ labels) :
      Wide K u labels a b k (1 + (wd a + wd b))
  | par {a b c d k l m n} : Wide K u labels a b k m → Wide K u labels c d l n →
      Wide K u labels (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n)
  | comp {a b c k l m n} : Wide K u labels a b k m → Wide K u labels b c l n →
      Wide K u labels a c (fun x z => ∑ y : Val b, k x y * l y z) (m + n)
  | trace {a b c k m} : Wide K u labels (.pair a c) (.pair b c) k m →
      Wide K u labels a b (fun x y => ∑ z : Val c, k (x, z) (y, z)) m
  | pre {a b c f k m} : Wide K u labels b c k m → Rewire a b f →
      Wide K u labels a c (fun x y => k (f x) y) m
  | post {a b c f k m} : Wide K u labels a b k m → Rewire c b f →
      Wide K u labels a c (fun x y => k x (f y)) m

variable {F : Type} [Field F] {a b : Wire} {k : Val a → Val b → F} {m : ℕ}

-- 读法：`wd a + wd b` 不超过 `m`。对 `h` 作归纳。
theorem Wide.width {u : ℕ} {L : Set (Table F)} (h : Wide F u L a b k m) :
    wd a + wd b ≤ m := by
  induction h with
  | empty => simp [wd]
  | table => omega
  | par _ _ ih ig => simp only [wd]; omega
  | comp _ _ ih ig => omega
  | trace _ ih => simp only [wd] at ih; omega
  | pre _ hf ih => rwa [hf.width]
  | post _ hf ih => rwa [hf.width]

-- 读法：存在 `s ≤ 4 * m`，要证明的命题是 `Wide F 3 ∅ a b k s`。对 `h` 作归纳。
theorem Net.wide (h : Net F a b k m) : ∃ s ≤ 4 * m, Wide F 3 ∅ a b k s := by
  induction h with
  | empty => exact ⟨_, le_rfl, .empty⟩
  | table _ _ _ ht => exact ⟨_, by omega, .table _ _ _ ht (.inl ht)⟩
  | par _ _ ih ig =>
    obtain ⟨s, hs, h⟩ := ih
    obtain ⟨t, ht, g⟩ := ig
    exact ⟨_, by omega, h.par g⟩
  | comp _ _ ih ig =>
    obtain ⟨s, hs, h⟩ := ih
    -- 推导：从 `ig` 中取出 `t, ht, g`。
    obtain ⟨t, ht, g⟩ := ig
    exact ⟨_, by omega, h.comp g⟩
  | trace _ ih =>
    obtain ⟨s, hs, h⟩ := ih
    exact ⟨s, hs, h.trace⟩
  | pre _ hr ih =>
    obtain ⟨s, hs, h⟩ := ih
    exact ⟨s, hs, h.pre hr⟩
  | post _ hr ih =>
    obtain ⟨s, hs, h⟩ := ih
    exact ⟨s, hs, h.post hr⟩

end OAI.LinearAlgebra.MatrixExponent
end
