-- 本文件所属证明环节：给控制器计算留下的地址、调用、匹配和恢复记录分配编码，检验记录的一致性与唯一性，并估计验证开销。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import Mathlib.Data.Fin.VecNotation
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats

section
/-!
# 按比特寻址的存储带

每行指定一个地址，以及该地址在访问前和访问后的比特。初始内容为零。读操作可将同一比特写回，依辅助信息初始化也可通过写操作实现。

**英文原文**

Bit-addressed memory tapes

A row specifies an address, the bit before the access and the bit
after it. Initial contents are zero. Reads can write back the same
bit, and initialization by advice can be implemented by writes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring

-- 读法：在后续公式中，`Row` 是 `Format.pair (.addr w) (.pair .bit .bit)` 的缩写。
abbrev Row (w : ℕ) := Format.pair (.addr w) (.pair .bit .bit)

-- 读法：在后续公式中，`Tape` 是 `Format.vec j (Row w)` 的缩写。
abbrev Tape (j w : ℕ) := Format.vec j (Row w)

variable {j w : ℕ}

-- 读法：逐一匹配以下输入模式：`0`、`n + 1`。
def cells (x : (Tape j w).obj) : ℕ → B w → Bool
  | 0 => fun _ => false
  | n + 1 => if h : n < 2 ^ j then
      Function.update (cells x n) (x ⟨n, h⟩).1 (x ⟨n, h⟩).2.2
    else cells x n

-- 读法：`Valid` 表示以下条件：对每个 `i`，`(x i).2.1` 等于 `cells x i.val (x i).1`。
def Valid (x : (Tape j w).obj) : Prop :=
  ∀ i, (x i).2.1 = cells x i.val (x i).1

-- 读法：为 `Decidable (Valid x)` 构造类型类实例。
instance (x : (Tape j w).obj) : Decidable (Valid x) := by unfold Valid; infer_instance

-- 读法：`cells x (i.val + 1) (x i).1` 等于 `(x i).2.2`。
theorem written (x : (Tape j w).obj) (i : B j) :
    cells x (i.val + 1) (x i).1 = (x i).2.2 := by
  rw [cells, dite_eq_left i.isLt, Function.update_self]

-- 读法：`cells x stop a` 等于 `cells x start a`。
theorem unchanged (x : (Tape j w).obj) (a : B w) {start stop : ℕ} (h : start ≤ stop)
    (hn : ∀ i : B j, start ≤ i.val → i.val < stop → (x i).1 ≠ a) :
    cells x stop a = cells x start a := by
  induction stop, h using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    have hh := ih (fun i h₁ h₂ => hn i h₁ (by omega))
    rw [cells]
    split
    · rename_i hi
      rw [Function.update_of_ne (hn ⟨n, hi⟩ h (Nat.lt_succ_self n)).symm]
      exact hh
    · exact hh

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

section
/-!
# 带随机存取存储器的确定性比特图程序

每个门读取有限个有序参数以及随机存取内存中的一个比特。它产生一个连线值，同时指定所访问单元的新值。将旧值写回即可实现只读访问。门可以使用常数，并可复用任何已有连线。

**英文原文**

Deterministic bit-graph programs with random-access memory

A gate sees a limited number of ordered arguments, plus one bit
of random-access memory. It produces one wire value and specifies
the new value of that cell. Returning the old value implements
read-only access. Gates may use constants and reuse any old wire.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring

-- 读法：在后续公式中，`Source` 是 `X ⊕ (Bool ⊕ B j)` 的缩写。
abbrev Source (X : Type) (j : ℕ) := X ⊕ (Bool ⊕ B j)

-- 读法：`Available` 的取值由 `| .inr (.inr k) => k < i | _ => True` 给出。
def Available {X : Type} {j : ℕ} (i : B j) : Source X j → Prop
  | .inr (.inr k) => k < i
  | _ => True

-- 读法：结构的字段包括 `address`、`args`、`instruction`、`address_ready`、`args_ready`。
structure Program (X : Type) (j w r : ℕ) where
  address : B j → slots (word w) → Source X j
  args : B j → Fin r → Source X j
  instruction : B j → (Fin r → Bool) → Bool → Bool × Bool
  address_ready : ∀ i k, Available i (address i k)
  args_ready : ∀ i k, Available i (args i k)

-- 读法：在后续公式中，`Trace` 是 `B j → Fin 3 → Bool` 的缩写。
/-- 各列分别给出访问前后的存储比特，以及门的输出连线上的值。

英文原文：The columns are the memory bit before and after the access and
the value on the gate's output wire.
-/
abbrev Trace (j : ℕ) := B j → Fin 3 → Bool

variable {X : Type} {j w r : ℕ}

-- 读法：`signal` 的取值由 `Sum.elim x (Sum.elim id (fun i => t i 2))` 给出。
def signal (x : X → Bool) (t : Trace j) : Source X j → Bool :=
  Sum.elim x (Sum.elim id (fun i => t i 2))

namespace Program
variable (P : Program X j w r) (x : X → Bool)

-- 读法：`addr` 的取值由 `Control.decode w (signal x t ∘ P.address i)` 给出。
def addr (t : Trace j) (i : B j) : B w := Control.decode w (signal x t ∘ P.address i)

-- 读法：输入 `i` 时返回 `(P.addr x t i, t i 0, t i 1)`。
def tape (t : Trace j) : (Tape j w).obj := fun i => (P.addr x t i, t i 0, t i 1)

-- 读法：`obeys` 表示以下条件：`Valid (P.tape x t)` 与 `∀ i, (t i 1, t i 2) = P.instruction i (signal x t ∘ P.args i) (t i 0)` 同时成立。
def obeys (t : Trace j) : Prop :=
  Valid (P.tape x t) ∧
    ∀ i, (t i 1, t i 2) = P.instruction i (signal x t ∘ P.args i) (t i 0)

-- 读法：`row` 的取值由 `let a := cells (P.tape x t) i.val (P.addr x t i) let b := P.instruction i (signal x t ∘ P.args i) a ![a, b.1, b.2]` 给出。
private def row (i : B j) (t : Trace j) : Fin 3 → Bool :=
  let a := cells (P.tape x t) i.val (P.addr x t i)
  let b := P.instruction i (signal x t ∘ P.args i) a
  ![a, b.1, b.2]

-- 读法：`P.obeys x t` 与 `∀ i, t i = P.row x i t` 等价。用函数外延性比较等号两侧在 `k` 处的取值。
private theorem obeys_iff (t : Trace j) : P.obeys x t ↔ ∀ i, t i = P.row x i t := by
  constructor
  · rintro ⟨ht, he⟩ i
    have h := ht i
    change t i 0 = cells (P.tape x t) i.val (P.addr x t i) at h
    dsimp only [row]
    rw [← h, ← he i]
    funext k
    fin_cases k <;> rfl
  · intro h
    constructor
    · intro i
      exact congrFun (h i) 0
    · intro i
      rw [h i]
      rfl

-- 读法：`cells u n` 等于 `cells v n`。对 `n` 作归纳。
private theorem cells_congr {u v : (Tape j w).obj} (n : ℕ)
    (h : ∀ i : B j, i.val < n → u i = v i) : cells u n = cells v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cells, cells, ih (fun i hi => h i (by omega))]
    split <;> rename_i hn
    · rw [h ⟨n, hn⟩ (Nat.lt_succ_self _)]
    · rfl

-- 读法：`P.row x i t` 等于 `P.row x i u`。
private theorem row_congr {t u : Trace j} (i : B j)
    (h : ∀ k, k < i → t k = u k) : P.row x i t = P.row x i u := by
  have hs (k : B j) (hk : k ≤ i) (z : Source X j) (hz : Available k z) :
      signal x t z = signal x u z := by
    rcases z with z | z | z
    · rfl
    · rfl
    · exact congrFun (h _ (lt_of_lt_of_le hz hk)) _
  have ha (k : B j) (hk : k ≤ i) : P.addr x t k = P.addr x u k := by
    unfold addr
    congr 1
    exact funext (fun z => hs k hk _ (P.address_ready k z))
  -- 推导：记下中间结论 `hm`：`cells (P.tape x t) i.val = cells (P.tape x u) i.val`。
  have hm : cells (P.tape x t) i.val = cells (P.tape x u) i.val := by
    apply cells_congr
    intro k hk
    change k < i at hk
    simp only [tape, ha k hk.le, h k hk]
  have he : signal x t ∘ P.args i = signal x u ∘ P.args i :=
    funext fun z => hs i le_rfl _ (P.args_ready i z)
  simp only [row, hm, ha i le_rfl, he]

-- 读法：`run` 的结果类型为 `Fin 3 → Bool`。
def run (i : B j) : Fin 3 → Bool :=
  P.row x i (fun k => if k < i then run k else fun _ => false)
termination_by i.val

-- 读法：要证明的命题是 `P.obeys x (P.run x)`。这里调用 `P.obeys_iff`。
theorem run_obeys : P.obeys x (P.run x) := by
  apply (P.obeys_iff x _).mpr
  intro i
  rw [run]
  exact P.row_congr x i (fun k hk => ite_eq_left hk)

-- 读法：`t` 等于 `P.run x`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem unique {t : Trace j} (h : P.obeys x t) : t = P.run x := by
  have h₁ := (P.obeys_iff x t).mp h
  have h₂ := (P.obeys_iff x _).mp (P.run_obeys x)
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih => rw [h₁, h₂, P.row_congr x i ih]

-- 读法：`eval` 的取值由 `signal x (P.run x)` 给出。
def eval : Source X j → Bool := signal x (P.run x)

end Program
end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

section
/-!
# 按地址稳定排序后相邻的访问

**英文原文**

Adjacent accesses in stable address order
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring

variable {j w : ℕ} (x : (Tape j w).obj)

-- 读法：`order` 的取值由 `permutation (fun i => (x i).1) (fun _ => true)` 给出。
def order : Equiv.Perm (B j) := permutation (fun i => (x i).1) (fun _ => true)

-- 读法：`sorted` 的取值由 `x ∘ order x` 给出。
def sorted : (Tape j w).obj := x ∘ order x

-- 读法：`i < k` 与 `(sorted x i).1 < (sorted x k).1 ∨ (sorted x i).1 = (sorted x k).1 ∧ order x i < order x k` 等价。
private theorem earlier (i k : B j) :
    i < k ↔ (sorted x i).1 < (sorted x k).1 ∨
      (sorted x i).1 = (sorted x k).1 ∧ order x i < order x k := by
  let f := fun i : B j => toLex (false, toLex ((x i).1, i))
  have hi : Function.Injective f := fun _ _ h => congrArg (fun t => t.2.2) h
  have hm : StrictMono (f ∘ order x) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hi.comp (order x).injective)
  rw [← hm.lt_iff_lt]
  simp [f, sorted, Prod.Lex.toLex_lt_toLex]

-- 读法：`prev` 的取值由 `⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩` 给出。
def prev (i : B j) : B j := ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

-- 读法：`0 < i.val` 与 `(sorted x (prev i)).1 = (sorted x i).1 ∧ k ≤ order x (prev i)` 同时成立。
/-- 对该地址的任何更早访问，按排序后的次序都不会晚于上一行；此时上一行具有相同地址。

英文原文：Any earlier access to this address lies no later than the previous
row in sorted order, which then has the same address.
-/
private theorem previous (i k : B j) (hk : k < order x i) (he : (x k).1 = (sorted x i).1) :
    0 < i.val ∧ (sorted x (prev i)).1 = (sorted x i).1 ∧ k ≤ order x (prev i) := by
  let t := (order x).symm k
  have ht : order x t = k := (order x).apply_symm_apply k
  have he' : (sorted x t).1 = (sorted x i).1 := by rw [sorted, Function.comp_apply, ht]; exact he
  have hi : t < i := (earlier x t i).mpr (.inr ⟨he', ht.trans_lt hk⟩)
  change t.val < i.val at hi
  have hpos : 0 < i.val := by omega
  have hpred : t ≤ prev i := by change t.val ≤ i.val - 1; omega
  have hpred' : prev i < i := by change i.val - 1 < i.val; omega
  -- 推导：记下中间结论 `hu`：`(sorted x (prev i)).1 ≤ (sorted x i).1`。
  have hu : (sorted x (prev i)).1 ≤ (sorted x i).1 := by
    rcases (earlier x _ _).mp hpred' with h | h
    · exact h.le
    · exact h.1.le
  refine ⟨hpos, ?_⟩
  rcases hpred.eq_or_lt with heq | hl
  · rw [← heq, ht]; exact ⟨he', le_rfl⟩
  rcases (earlier x _ _).mp hl with h | h
  · exact (hu.not_gt (he' ▸ h)).elim
  · exact ⟨h.1.symm.trans he', ht.symm.le.trans h.2.le⟩

-- 读法：当 `0 < i.val ∧ (x (prev i)).1 = (x i).1` 成立时取 `(x (prev i)).2.2`，否则取 `false`。
def expected (i : B j) : Bool :=
  if 0 < i.val ∧ (x (prev i)).1 = (x i).1 then (x (prev i)).2.2 else false

-- 读法：`cells x (order x i).val (sorted x i).1` 等于 `expected (sorted x) i`。
private theorem before (i : B j) :
    cells x (order x i).val (sorted x i).1 = expected (sorted x) i := by
  unfold expected
  split
  · rename_i h
    have hp : prev i < i := by change i.val - 1 < i.val; omega
    have htime := ((earlier x _ _).mp hp).resolve_left (not_lt_of_ge h.2.ge)
    rw [unchanged x _ (Nat.succ_le_of_lt htime.2) (by
      intro k hk hk' he
      have ht : k.val ≤ (order x (prev i)).val := (previous x i k hk' he).2.2
      omega), ← h.2]
    exact written x _
  · rename_i h
    rw [unchanged x _ (Nat.zero_le _) (by
      intro k _ hk he
      obtain ⟨h₁, h₂, _⟩ := previous x i k hk he
      exact h ⟨h₁, h₂⟩)]
    rfl

-- 读法：`Valid x` 与 `∀ i, (sorted x i).2.1 = expected (sorted x) i` 等价。
theorem valid_iff : Valid x ↔ ∀ i, (sorted x i).2.1 = expected (sorted x) i := by
  simp_rw [← before]
  constructor
  · exact fun h i => h (order x i)
  · intro h i
    obtain ⟨k, rfl⟩ := (order x).surjective i
    exact h k

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

section
/-!
# 按地址的稳定次序计算所有局部检验

**英文原文**

Computing all the local checks in stable address order
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring

variable (F : Type) [Field F] (j w : ℕ)

-- 读法：`(Tape j w).width` 不超过 `2 ^ j * (100 + (j + w + 2)) ^ 1`。这里调用 `Nat.mul_le_mul_left`。
private theorem tape_width : (Tape j w).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
  simp only [Tape, Row, Format.width_vec, Format.width_pair, Format.width_addr, pow_one]
  rw [Format.width_bit]
  exact Nat.mul_le_mul_left _ (by omega)

-- 读法：映射 `sorted` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (j) * (100 + ((j + w + 2))) ^ (43)` 为上界。这里调用 `Nat.mul_le_mul_left`。
private theorem cheap_sorted : Cheap F j (j + w + 2) (Tape j w) (Tape j w) sorted 43 := by
  have ha : (Format.vec j (.addr w)).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
    simp only [Format.width_vec, Format.width_addr, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have hb : (Format.vec j .bit).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 1 := by
    rw [Format.width_vec, Format.width_bit, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have pick : Cheap F j (j + w + 2) (Tape j w) (.vec j (.addr w)) (fun x i => (x i).1) 2 :=
    Cheap.project F (tape_width _ _) ha (fun i => (i.1, .inl i.2)) (fun _ _ => rfl)
  have mark := Cheap.const F (tape_width j w) hb (fun _ => true)
  have perm := (pick.pair mark).comp ((cheap_permutation F j w).widen (l := j + w + 2) (by omega))
  have read := Cheap.lookup F j (j + w + 2) (Row w) (by omega) (by simp [Row])
  have H := ((Cheap.id F (tape_width j w)).pair perm).comp read
  simp only [Function.comp_def, id_eq] at H
  exact H

-- 读法：在后续公式中，`Test` 是 `Format.pair (.pair (.addr w) (.addr w)) (.pair .bit .bit)` 的缩写。
private abbrev Test := Format.pair (.pair (.addr w) (.addr w)) (.pair .bit .bit)

-- 读法：`neighbors` 的取值由 `(((x (prev i)).1, (x i).1), ((x i).2.1, (x (prev i)).2.2))` 给出。
private def neighbors (x : (Tape j w).obj) (i : B j) : (Test w).obj :=
  (((x (prev i)).1, (x i).1), ((x i).2.1, (x (prev i)).2.2))

-- 读法：`(Test w).width` 不超过 `(100 + (j + w + 2)) ^ 2`。
private theorem test_width : (Test w).width ≤ (100 + (j + w + 2)) ^ 2 := by
  simp only [Test, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]
  ring_nf
  omega

-- 读法：映射 `(neighbors j w)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (j) * (100 + ((j + w + 2))) ^ (3)` 为上界。这里调用 `Nat.mul_le_mul_left`。
private theorem cheap_neighbors : Cheap F j (j + w + 2) (Tape j w) (.vec j (Test w))
    (neighbors j w) 3 := by
  have ha : (Tape j w).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 2 :=
    (tape_width _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide)))
  have hb : (Format.vec j (Test w)).width ≤ 2 ^ j * (100 + (j + w + 2)) ^ 2 := by
    rw [Format.width_vec]
    exact Nat.mul_le_mul_left _ (test_width j w)
  let e : (Format.vec j (Test w)).pins → (Tape j w).pins
    | (i, .inl (.inl a)) => (prev i, .inl a)
    | (i, .inl (.inr a)) => (i, .inl a)
    | (i, .inr (.inl a)) => (i, .inr (.inl a))
    | (i, .inr (.inr a)) => (prev i, .inr (.inr a))
  apply Cheap.project F ha hb e
  rintro x ⟨i, (a | a) | (a | a)⟩ <;> rfl

-- 读法：`test` 的取值由 `decide (x.2.1 = if 0 < i.val ∧ x.1.1 = x.1.2 then x.2.2 else false)` 给出。
private def test (i : B j) (x : (Test w).obj) : Bool :=
  decide (x.2.1 = if 0 < i.val ∧ x.1.1 = x.1.2 then x.2.2 else false)

-- 读法：映射 `(test j w i)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + ((j + w + 2))) ^ (2)` 为上界。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem cheap_test (i : B j) : Cheap F 0 (j + w + 2) (Test w) .bit (test j w i) 2 := by
  let g := fun x : Bool × Bool × Bool => decide (x.2.1 = if 0 < i.val ∧ x.1 then x.2.2 else false)
  have hc := (numeric_eq F w).par (Circuit.id F (.pair .bit .bit))
  have ho := hc.comp (small (F := F) (A := .pair .bit (.pair .bit .bit)) (by simp) g)
  have he : Circuit F (Test w) .bit (test j w i) (2 * w + 1 + 2 + 200) := by
    rw [Format.width_pair .bit .bit, Format.width_bit] at ho
    convert ho using 1
    funext x
    simp only [test, g, Function.comp_apply, Prod.map, id_eq, decide_eq_true_eq]
  refine ⟨_, he, ?_⟩
  simp only [Test, Format.width_pair, Format.width_addr, pow_zero, one_mul]
  rw [Format.width_bit]
  ring_nf
  omega

-- 读法：`checks` 的取值由 `decide ((sorted x i).2.1 = expected (sorted x) i)` 给出。
def checks (x : (Tape j w).obj) (i : B j) : Bool :=
  decide ((sorted x i).2.1 = expected (sorted x) i)

-- 读法：映射 `(checks j w)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (j) * (100 + ((j + w + 2))) ^ (45)` 为上界。
theorem cheap_checks : Cheap F j (j + w + 2) (Tape j w) (.vec j .bit) (checks j w) 45 :=
  ((cheap_sorted F j w).comp (cheap_neighbors F j w)).comp (Cheap.map _ (cheap_test F j w))

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

section
/-!
# 用三价网络核验一条已命名的存储带

**英文原文**

Trivalent verification of a named memory tape
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring Install

-- 读法：`2 ^ j * (100 + (j + w + 2)) ^ 45 + 2 ^ j * 16` 不超过 `2 ^ j * (100 + j + w) ^ 100`。这里调用 `Nat.mul_le_mul_left`。
private theorem estimate (j w : ℕ) :
    2 ^ j * (100 + (j + w + 2)) ^ 45 + 2 ^ j * 16 ≤ 2 ^ j * (100 + j + w) ^ 100 := by
  rw [← mul_add]
  apply Nat.mul_le_mul_left
  let k := 100 + j + w
  have hk : 100 ≤ k := by unfold k; omega
  have hh : 100 + (j + w + 2) ≤ k ^ 2 := by unfold k; ring_nf; omega
  calc
    _ ≤ (k ^ 2) ^ 45 + 16 := Nat.add_le_add_right (Nat.pow_le_pow_left hh _) _
    _ = k ^ 90 + 16 := by rw [← pow_mul]
    _ ≤ k ^ 90 * k := by
      -- 推导：记下中间结论 `h`：`0 < k ^ 90`。
      have h : 0 < k ^ 90 := pow_pos (by omega) _
      generalize k ^ 90 = v at h ⊢
      nlinarith
    _ ≤ k ^ 100 := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by decide)

-- 读法：要证明的命题是 `Weight F (fun b => if Valid ((Tape j w).code.symm b) then 1 else 0) (2 ^ j * (100 + j + w) ^ 100)`。用函数外延性比较等号两侧在 `b` 处的取值。
/-- 单个零一权重把每次读操作与同一地址最近一次写入相核对，在任何特征下都不会产生额外重数。

英文原文：One zero-one weight verifies every read against the most recent
write to the same address, with no multiplicity in any characteristic.
-/
theorem weight (F : Type) [Field F] (j w : ℕ) :
    Weight F (fun b => if Valid ((Tape j w).code.symm b) then 1 else 0)
      (2 ^ j * (100 + j + w) ^ 100) := by
  let pin : (Unit → Bool) → F := fun x => if x () then 1 else 0
  have hp : Weight F pin 16 := Weight.dense F Unit pin
  obtain ⟨m, hm, hb⟩ := cheap_checks F j w
  have hn : m + 2 ^ j * 16 ≤ 2 ^ j * (100 + j + w) ^ 100 :=
    (Nat.add_le_add_right ((Nat.le_add_left _ _).trans hb) _).trans (estimate j w)
  have h := (BNet.weight hm (hp.prod j)).mono hn
  convert h using 1
  funext b
  let x := (Tape j w).code.symm b
  change (if Valid x then (1 : F) else 0) = ∏ i : B j, if checks j w x i then 1 else 0
  by_cases hx : Valid x
  · have hc (i : B j) : checks j w x i = true := decide_eq_true ((valid_iff x).mp hx i)
    simp only [hx, hc, ite_true, Finset.prod_const_one]
  -- 推导：从 `not_forall.mp (mt (valid_iff x).mpr hx)` 中取出 `i, hi`。
  · obtain ⟨i, hi⟩ := not_forall.mp (mt (valid_iff x).mpr hx)
    rw [ite_eq_right hx]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [checks, hi])

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

/-!
# 带权的确定性处理器

从输出连线取值以检查是否接受，并给已安装的字典表提供参数。内部只需猜测两条常数连线和执行记录的三列。在任何特征下，一致性检查都恰好留下一个赋值。

**英文原文**

A weighted deterministic processor

Tap the output wires to check acceptance and to supply the arguments
of the installed dictionary tables. The only internal guesses are two
constant wires and the three columns of the execution. Their consistency
checks leave exactly one assignment, in every characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring Install
open scoped Classical

variable {X F D : Type} [Field F] {Z : D → Type} {j w r : ℕ}

-- 读法：在后续公式中，`Hidden` 是 `Bool ⊕ (B j × Fin 3)` 的缩写。
private abbrev Hidden (j : ℕ) := Bool ⊕ (B j × Fin 3)

-- 读法：`emit` 的取值由 `Sum.elim id (Function.uncurry t)` 给出。
private def emit (t : Trace j) : Hidden j → Bool := Sum.elim id (Function.uncurry t)
-- 读法：输入 `i k` 时返回 `y (.inr (i, k))`。
private def decode (y : Hidden j → Bool) : Trace j := fun i k => y (.inr (i, k))
-- 读法：`ref` 的取值由 `Sum.map id (Sum.map id (fun i => (i, 2)))` 给出。
private def ref : Source X j → X ⊕ Hidden j :=
  Sum.map id (Sum.map id (fun i => (i, 2)))

-- 读法：`Sum.elim x (emit t) (ref a)` 等于 `signal x t a`。
private theorem read_ref (x : X → Bool) (t : Trace j) (a : Source X j) :
    Sum.elim x (emit t) (ref a) = signal x t a := by rcases a with a | a | a <;> rfl

-- 读法：在后续公式中，`Tasks` 是 `Option (Option (B j ⊕ D))` 的缩写。
private abbrev Tasks (j : ℕ) (D : Type) := Option (Option (B j ⊕ D))

-- 读法：在后续公式中，`ports` 是 `| none => Bool | some none => (Tape j w).pins | some (some (.inl _)) => Fin r ⊕ Fin 3 | some (some (.inr d)) => Z d` 的缩写。
private abbrev ports (j w r : ℕ) (Z : D → Type) : Tasks j D → Type
  | none => Bool
  | some none => (Tape j w).pins
  | some (some (.inl _)) => Fin r ⊕ Fin 3
  | some (some (.inr d)) => Z d

-- 读法：为 `Fintype (ports j w r Z k)` 构造类型类实例。
private instance [∀ d, Fintype (Z d)] (k : Tasks j D) : Fintype (ports j w r Z k) := by
  rcases k with _ | (_ | (i | d)) <;> unfold ports <;> infer_instance

namespace Program
variable (P : Program X j w r)
    (data : (d : D) → (Z d → Bool) → F) (tap : (d : D) → Z d → Source X j)

-- 读法：逐一匹配输入模式，例如 `none, b`、`some none, (i, .inl a)`、`some none, (i, .inr (.inl _))`、`some none, (i, .inr (.inr _))`。
private def wiring : (k : Tasks j D) → ports j w r Z k → X ⊕ Hidden j
  | none, b => .inr (.inl b)
  | some none, (i, .inl a) => ref (P.address i a)
  | some none, (i, .inr (.inl _)) => .inr (.inr (i, 0))
  | some none, (i, .inr (.inr _)) => .inr (.inr (i, 1))
  | some (some (.inl i)), .inl a => ref (P.args i a)
  | some (some (.inl i)), .inr k => .inr (.inr (i, k))
  | some (some (.inr d)), a => ref (tap d a)

-- 读法：逐一匹配以下输入模式：`none, y`、`some none, y`、`some (some (.inl i)), y`、`some (some (.inr d)), y`。
private def factor : (k : Tasks j D) → (ports j w r Z k → Bool) → F
  | none, y => if y = id then 1 else 0
  | some none, y => if Valid ((Tape j w).code.symm y) then 1 else 0
  | some (some (.inl i)), y =>
    if (y (.inr 1), y (.inr 2)) = P.instruction i (y ∘ Sum.inl) (y (.inr 0)) then 1 else 0
  | some (some (.inr d)), y => data d y

-- 读法：`(Tape j w).code.symm (Sum.elim x (emit t) ∘ P.wiring tap (some none))` 等于 `P.tape x t`。用函数外延性比较等号两侧在 `⟨i, a⟩` 处的取值。
private theorem tape_layout (x : X → Bool) (t : Trace j) :
    (Tape j w).code.symm (Sum.elim x (emit t) ∘ P.wiring tap (some none)) = P.tape x t := by
  apply (Tape j w).code.injective
  rw [Equiv.apply_symm_apply]
  funext ⟨i, a⟩
  rcases a with a | a | a
  · change Sum.elim x (emit t) (ref (P.address i a)) =
      (Control.decode w).symm (P.addr x t i) a
    rw [read_ref, addr, Equiv.symm_apply_apply]
    rfl
  · rfl
  · rfl

-- 读法：结论为 `P.factor data (some (some (.inl i))) (Sum.elim x (emit t) ∘ P.wiring tap (some (some (.inl i)))) = if (t i 1, t i 2) = P.instruction i (signal x t ∘ P.args i) (t i 0) then 1 else 0`。
private theorem gate_layout (x : X → Bool) (t : Trace j) (i : B j) :
    P.factor data (some (some (.inl i))) (Sum.elim x (emit t) ∘ P.wiring tap (some (some (.inl i)))) =
      if (t i 1, t i 2) = P.instruction i (signal x t ∘ P.args i) (t i 0) then 1 else 0 := by
  have he : (Sum.elim x (emit t) ∘ P.wiring tap (some (some (.inl i)))) ∘ Sum.inl =
      signal x t ∘ P.args i := funext fun _ => read_ref _ _ _
  change (if (t i 1, t i 2) = P.instruction i
    ((Sum.elim x (emit t) ∘ P.wiring tap (some (some (.inl i)))) ∘ Sum.inl) (t i 0)
    then (1 : F) else 0) = _
  rw [he]

variable [Fintype D]

-- 读法：`products` 的取值由 `∏ d, data d (P.eval x ∘ tap d)` 给出。
/-- 每个因子只读取指定为其实参的连线。

英文原文：The factors only see the wires intended as their arguments.
-/
def products (x : X → Bool) : F := ∏ d, data d (P.eval x ∘ tap d)

-- 读法：`y` 等于 `emit (P.run x)`。
private theorem only_execution (x : X → Bool) (y : Hidden j → Bool)
    (h : ∏ i, P.factor data i (Sum.elim x y ∘ P.wiring tap i) ≠ 0) : y = emit (P.run x) := by
  have he (i) : P.factor data i (Sum.elim x y ∘ P.wiring tap i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  have hc : y ∘ Sum.inl = id := by
    have hh := he none
    change (if y ∘ Sum.inl = id then (1 : F) else 0) ≠ 0 at hh
    by_contra! hn
    exact hh (ite_eq_right hn)
  let t := decode y
  -- 推导：记下中间结论 `hy`：`y = emit t`。
  have hy : y = emit t := by
    funext k
    rcases k with b | ⟨i, l⟩
    · exact congrFun hc b
    · rfl
  rw [hy] at he ⊢
  apply congrArg emit
  apply P.unique x
  constructor
  · have h' := he (some none)
    change (if Valid ((Tape j w).code.symm (Sum.elim x (emit t) ∘ P.wiring tap (some none)))
      then (1 : F) else 0) ≠ 0 at h'
    rw [tape_layout] at h'
    by_contra! hn
    exact h' (ite_eq_right hn)
  · intro i
    have h' := he (some (some (.inl i)))
    rw [gate_layout] at h'
    by_contra! hn
    exact h' (ite_eq_right hn)

-- 读法：结论为 `∏ i, P.factor data i (Sum.elim x (emit (P.run x)) ∘ P.wiring tap i) = P.products data tap x`。
private theorem run_product (x : X → Bool) :
    ∏ i, P.factor data i (Sum.elim x (emit (P.run x)) ∘ P.wiring tap i) = P.products data tap x := by
  let t := P.run x
  let f := fun i => P.factor data i (Sum.elim x (emit t) ∘ P.wiring tap i)
  have hc : f none = 1 := by
    change (if (id : Bool → Bool) = id then (1 : F) else 0) = 1
    rw [ite_eq_left rfl]
  have ht : f (some none) = 1 := by
    change (if Valid ((Tape j w).code.symm (Sum.elim x (emit t) ∘ P.wiring tap (some none)))
      then (1 : F) else 0) = 1
    rw [tape_layout, ite_eq_left (P.run_obeys x).1]
  have hi (i : B j) : f (some (some (.inl i))) = 1 := by
    unfold f
    rw [gate_layout, ite_eq_left ((P.run_obeys x).2 i)]
  have hd (d : D) : f (some (some (.inr d))) = data d (P.eval x ∘ tap d) :=
    congrArg (data d) (funext fun _ => read_ref x t _)
  change ∏ i, f i = _
  rw [Fintype.prod_option, Fintype.prod_option, Fintype.prod_sum_type]
  simp only [hc, ht, hi, hd, Finset.prod_const_one, one_mul, products]

variable [Fintype X] [∀ d, Fintype (Z d)]

-- 读法：`expense` 的取值由 `2 ^ j * (3 + 4 * (100 + j + w) ^ 100 + 32 * 2 ^ (r + 3)) + 130` 给出。
def expense (j w r : ℕ) : ℕ :=
  2 ^ j * (3 + 4 * (100 + j + w) ^ 100 + 32 * 2 ^ (r + 3)) + 130

-- 读法：要证明的命题是 `WideWeight F u L (P.products data tap) (9 * (Fintype.card X + expense j w r + ∑ d, cost d))`。这里调用 `of_weight`。
/-- 所有 RAM 操作与有界元数布尔门均为三价。表集合只需收录输出因子已经使用的标签。

英文原文：All RAM operations and bounded-arity Boolean gates are trivalent.
The table set need only contain labels already used by the output factors.
-/
theorem build {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (cost : D → ℕ)
    (hc : ∀ d, WideWeight F u L (data d) (cost d)) :
    WideWeight F u L (P.products data tap) (9 * (Fintype.card X + expense j w r + ∑ d, cost d)) := by
  let m : Tasks j D → ℕ
    | none => 128
    | some none => 4 * (2 ^ j * (100 + j + w) ^ 100)
    | some (some (.inl _)) => 32 * 2 ^ (r + 3)
    | some (some (.inr d)) => cost d
  have hh (i) : WideWeight F u L (P.factor data i) (m i) := by
    rcases i with _ | (_ | (i | d))
    · exact of_weight hu (Weight.dense F Bool _)
    · exact of_weight hu (RAM.weight F j w)
    · have := of_weight (L := L) hu (Weight.dense F (Fin r ⊕ Fin 3) (P.factor data (some (some (.inl i)))))
      simpa only [m, Fintype.card_sum, Fintype.card_fin, ← mul_assoc, show 4 * 8 = 32 from rfl] using this
    · exact hc d
  -- 推导：记下中间结论 `he`：`weightedSum (P.factor data) (P.wiring tap) = P.products data tap`。
  have he : weightedSum (P.factor data) (P.wiring tap) = P.products data tap := by
    funext x
    unfold weightedSum
    rw [Finset.sum_eq_single (emit (P.run x))]
    · exact P.run_product data tap x
    · exact fun y _ hy => not_ne_iff.mp (mt (P.only_execution data tap x y) hy)
    · simp
  have h := wide_sum (P.factor data) (P.wiring tap) m hu hh
  rw [he] at h
  intro a i
  -- 推导：从 `h a i` 中取出 `n, hn, ht`。
  obtain ⟨n, hn, ht⟩ := h a i
  refine ⟨n, hn.trans ?_, ht⟩
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_sum_type]
  simp only [Hidden, m, expense, Fintype.card_sum, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  generalize (100 + j + w) ^ 100 = q
  ring_nf
  omega

end Program
end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

/-!
# 按二的幂分配的字典槽位

活跃比特用于区分空调用和未使用的席位。长度显式给出，同一宽度统一使用一个表标签。这种一致性同时涉及字典选择和槽位选择。

**英文原文**

Dyadic dictionary seats

The active bit distinguishes an empty call from an unused seat.
Lengths are explicit and each width uses one common table label.
Uniformity is in the choice of the dictionary as well as the slot.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open Coloring Install
open scoped Classical

-- 读法：在后续公式中，`token` 是 `Format.pair .bit (.pair (.addr (b + 1)) (.vec b .bit))` 的缩写。
abbrev token (b : ℕ) := Format.pair .bit (.pair (.addr (b + 1)) (.vec b .bit))

-- 读法：输入 `(active, n, x)` 时返回 `if !active then 1 else if n.val ≤ U ∧ n.val ≤ 2 ^ b then W ((List.ofFn x).take n.val) else 0`。
def tokenValue {F : Type} [Field F] (U : ℕ) (W : List Bool → F) (b : ℕ) :
    (token b).obj → F :=
  fun (active, n, x) => if !active then 1 else
    if n.val ≤ U ∧ n.val ≤ 2 ^ b then W ((List.ofFn x).take n.val) else 0

-- 读法：`(token b).width` 不超过 `4 * 2 ^ b`。
private theorem token_width (b : ℕ) : (token b).width ≤ 4 * 2 ^ b := by
  simp only [token, Format.width_pair, Format.width_vec]
  rw [Format.width_bit, Format.width_addr]
  have := Nat.lt_two_pow_self (n := b)
  omega

-- 读法：`ceiling` 的取值由 `Nat.clog 2 (U + 1)` 给出。
def ceiling (U : ℕ) := Nat.clog 2 (U + 1)
-- 读法：在后续公式中，`Calls` 是 `Slot t t (ceiling U)` 的缩写。
abbrev Calls (t U : ℕ) := Slot t t (ceiling U)

variable {F : Type} [Field F] (U : ℕ) (W : List Bool → F)

-- 读法：`sites` 的取值由 `Fintype.equivOfCardEq (by simp [Format.width])` 给出。
private def sites (b : ℕ) : (token b).pins ≃ slots (word (token b).width) :=
  Fintype.equivOfCardEq (by simp [Format.width])

-- 读法：`label` 的取值由 `⟨word (token b).width, .unit, fun x _ => tokenValue U W b ((token b).code.symm (bits (word (token b).width) x ∘ sites b))⟩` 给出。
def label (b : ℕ) : Table F :=
  ⟨word (token b).width, .unit,
    fun x _ => tokenValue U W b ((token b).code.symm (bits (word (token b).width) x ∘ sites b))⟩

-- 读法：`labels` 的取值由 `label U W '' Set.Iic (ceiling U)` 给出。
def labels : Set (Table F) := label U W '' Set.Iic (ceiling U)

-- 读法：要证明的命题是 `WideWeight F (8 * (U + 1)) (labels U W) (tokenValue U W b ∘ (token b).code.symm) (5 * 2 ^ b)`。这里调用 `Wide.table`。
theorem label_cost {b : ℕ} (hb : b ≤ ceiling U) :
    WideWeight F (8 * (U + 1)) (labels U W) (tokenValue U W b ∘ (token b).code.symm) (5 * 2 ^ b) := by
  have h₁ : 2 ^ b ≤ 2 * (U + 1) :=
    (Nat.pow_le_pow_right (by decide) hb).trans (pow_clog_le_twice (by omega))
  have hw := token_width b
  let a := word (token b).width
  let f := fun (x : Val a) (_ : Val .unit) =>
    tokenValue U W b ((token b).code.symm (bits a x ∘ sites b))
  have hn : Wide F (8 * (U + 1)) (labels U W) a .unit f (1 + wd a) := by
    apply Wide.table
    · simp only [a, wd_word, wd, add_zero]
      omega
    · exact .inr ⟨b, hb, rfl⟩
  intro c e
  refine ⟨1 + wd a, ?_, ?_⟩
  · show 1 + wd a ≤ 5 * 2 ^ b
    rw [show wd a = (token b).width from wd_word _]
    have := Nat.two_pow_pos b
    omega
  · simpa [f, Function.comp_def] using hn.pre (rewire_reindex ((sites b).symm.trans e))

-- 读法：结构的字段包括 `clock`、`addressBits`、`fanIn`、`program`、`accept`。
/-- 计费总量有界的处理器按给定数目为各长度预留槽位。抽头可以包括最后的存储读取。

英文原文：A processor with bounded total charge reserves the indicated
number of seats at each length. Taps can include final memory reads.
-/
structure Processor (a : Wire) (t U : ℕ) where
  clock : ℕ
  addressBits : ℕ
  fanIn : ℕ
  program : Program (slots a) clock addressBits fanIn
  accept : Source (slots a) clock
  call : ∀ s : Calls t U, (token s.1.val).pins → Source (slots a) clock

variable {a : Wire} {t U : ℕ}
namespace Processor
variable (p : Processor a t U)

-- 读法：`cost` 的取值由 `9 * (wd a + Program.expense p.clock p.addressBits p.fanIn + 64 + 10 * (ceiling U + 1) * t)` 给出。
def cost := 9 * (wd a + Program.expense p.clock p.addressBits p.fanIn + 64 +
  10 * (ceiling U + 1) * t)

-- 读法：`value` 的结果类型为 `F`。
def value (x : slots a → Bool) : F :=
  let y := p.program.eval x
  if y p.accept then ∏ s : Calls t U, tokenValue U W s.1.val
    ((token s.1.val).code.symm (y ∘ p.call s)) else 0

-- 读法：在后续公式中，`pins` 是 `match k with | none => Unit | some s => (token s.1.val).pins` 的缩写。
private abbrev pins (k : Option (Calls t U)) : Type :=
  match k with
  | none => Unit
  | some s => (token s.1.val).pins

-- 读法：为 `Fintype (pins k)` 构造类型类实例。
private instance (k : Option (Calls t U)) : Fintype (pins k) := by
  cases k <;> unfold pins <;> infer_instance

-- 读法：要证明的命题是 `WideWeight F (8 * (U + 1)) (labels U W) (p.value W) p.cost`。
theorem build : WideWeight F (8 * (U + 1)) (labels U W) (p.value W) p.cost := by
  let data : (i : Option (Calls t U)) → (pins i → Bool) → F
    | none, x => if x () then 1 else 0
    | some s, x => tokenValue U W s.1.val ((token s.1.val).code.symm x)
  let tap : (i : Option (Calls t U)) → pins i → Source (slots a) p.clock
    | none, _ => p.accept
    | some s, i => p.call s i
  let c : Option (Calls t U) → ℕ
    | none => 64
    | some s => 5 * capacity s
  -- 推导：记下中间结论 `hu`：`3 ≤ 8 * (U + 1)`。
  have hu : 3 ≤ 8 * (U + 1) := by omega
  have hc (k) : WideWeight F (8 * (U + 1)) (labels U W) (data k) (c k) := by
    cases k with
    | none => exact of_weight hu (Weight.dense F Unit _)
    | some s => exact label_cost U W (Nat.lt_succ_iff.mp s.1.isLt)
  have hv : p.program.products data tap = p.value W := by
    funext x
    unfold Program.products value
    rw [Fintype.prod_option]
    simp only [data, tap, Function.comp_apply, ite_mul, one_mul, zero_mul]
  have hn := p.program.build data tap hu c hc
  rw [hv, MatrixExponent.card_slots, Fintype.sum_option] at hn
  intro b e
  -- 推导：从 `hn b e` 中取出 `n, h, he`。
  obtain ⟨n, h, he⟩ := hn b e
  refine ⟨n, h.trans ?_, he⟩
  simp only [c, cost, ← Finset.mul_sum]
  have hb := sum_capacity t t (ceiling U)
  linarith only [hb]

end Processor
end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end

/-!
# 对变长调用进行装包

每次调用至少按一个比特计费。在每个按二的幂次划分的桶中，按调用发出的顺序使用已设置席位的一个初始段。未用席位的贡献为一。

**英文原文**

Packing variable-length calls

Every call costs at least one bit of charge. Within each dyadic bucket
we use an initial segment of the installed seats, in issuance order.
Unused seats contribute one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.RAM

open scoped Classical
variable {F : Type} [Field F] {n t U : ℕ}

-- 读法：`callCharge` 的取值由 `max 1 x.length` 给出。
def callCharge (x : List Bool) := max 1 x.length

-- 读法：`emptyToken` 的取值由 `(false, 0, fun _ => false)` 给出。
def emptyToken (b : ℕ) : (token b).obj := (false, 0, fun _ => false)

-- 读法：当 `h : x.length < 2 ^ (b + 1)` 成立时取 `(true, ⟨x.length, h⟩, fun i => x[i.val]?.getD false)`，否则取 `emptyToken b`。
def encodeToken (b : ℕ) (x : List Bool) : (token b).obj :=
  if h : x.length < 2 ^ (b + 1) then
    (true, ⟨x.length, h⟩, fun i => x[i.val]?.getD false)
  else emptyToken b

-- 读法：`tokenValue U W b (encodeToken b x)` 等于 `W x`。这里调用 `List.ext_getElem`。
theorem tokenValue_encode (W : List Bool → F) (b : ℕ) (x : List Bool)
    (hx : x.length ≤ U) (hb : x.length ≤ 2 ^ b) :
    tokenValue U W b (encodeToken b x) = W x := by
  have hn : x.length < 2 ^ (b + 1) := lt_of_le_of_lt hb (by rw [pow_succ]; have := Nat.two_pow_pos b; omega)
  simp only [encodeToken, dite_eq_left hn, tokenValue, Bool.not_true, Bool.false_eq_true, ite_false,
    hx, hb, and_self, ite_true]
  congr 1
  apply List.ext_getElem
  · simp [hb]
  · intro i h₁ h₂
    simp [h₂]

-- 读法：`Issuance` 表示以下条件：对每个 `b : Fin (ceiling U + 1)`，要证明的命题是 `OrderedSeats (bucket (fun i => callCharge (x i)) b) (fun s => p ⟨b, s⟩)`。
/-- 槽位记录其调用的序号；若槽位未用，则记录一个哨兵值。

英文原文：A slot stores the ordinal of its call, or a sentinel for an unused seat.
-/
def Issuance (x : Fin n → List Bool) (p : Calls t U → Fin (n + 1)) : Prop :=
  ∀ b : Fin (ceiling U + 1), OrderedSeats (bucket (fun i => callCharge (x i)) b)
    (fun s => p ⟨b, s⟩)

-- 读法：存在唯一的 `p : Calls t U → Fin (n + 1)`，要证明的命题是 `Issuance x p`。这里调用 `Finset.sum_le_sum`。
theorem unique_issuance (x : Fin n → List Bool) (h : ∑ i, callCharge (x i) ≤ t) :
    ∃! p : Calls t U → Fin (n + 1), Issuance x p := by
  have hp (i : Fin n) : 1 ≤ callCharge (x i) := le_max_left _ _
  have hn : n ≤ t := by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)).trans h
  have hh (b : Fin (ceiling U + 1)) := unique_seats (n := seats t t b)
    (bucket (fun i => callCharge (x i)) b.val)
    ((bucket_capacity hp h b.val).trans (min_le_min_right _ hn))
  let p := fun s : Calls t U => (hh s.1).choose s.2
  refine ⟨p, fun b => (hh b).choose_spec.1, ?_⟩
  intro q hq
  funext ⟨b, i⟩
  exact congrFun ((hh b).choose_spec.2 _ (hq b)) i

variable {x : Fin n → List Bool} {p : Calls t U → Fin (n + 1)}

-- 读法：`Nat.clog 2 (callCharge (x i))` 等于 `s.1.val`。
private theorem Issuance.index (h : Issuance x p) {i s} (he : p s = i.castSucc) :
    Nat.clog 2 (callCharge (x i)) = s.1.val := by
  have hh := ((h s.1).2.1 i).mp ⟨s.2, he⟩
  simpa [bucket] using hh

-- 读法：存在唯一的 `s`，`p s` 等于 `i.castSucc`。这里调用 `Nat.clog_mono_right`。
theorem Issuance.covers (h : Issuance x p) (hu : ∀ i, (x i).length ≤ U) (i : Fin n) :
    ∃! s, p s = i.castSucc := by
  have hb : Nat.clog 2 (callCharge (x i)) ≤ ceiling U := by
    apply Nat.clog_mono_right
    exact max_le (by omega) ((hu i).trans (Nat.le_succ _))
  let b : Fin (ceiling U + 1) := ⟨_, Nat.lt_succ_of_le hb⟩
  obtain ⟨s, hs⟩ := ((h b).2.1 i).mpr (by simp [bucket, b])
  refine ⟨⟨b, s⟩, hs, ?_⟩
  rintro ⟨d, z⟩ hz
  have hd : d = b := Fin.ext (h.index hz).symm
  subst d
  have he : z = s := (h b).2.2 _ _ (hz.trans hs.symm) (hz.trans_ne (Fin.castSucc_ne_last i))
  rw [he]

-- 读法：`tokens` 的取值由 `Fin.lastCases (emptyToken _) (fun i => encodeToken _ (x i)) (p s)` 给出。
def tokens (x : Fin n → List Bool) (p : Calls t U → Fin (n + 1)) (s : Calls t U) :
    (token s.1.val).obj :=
  Fin.lastCases (emptyToken _) (fun i => encodeToken _ (x i)) (p s)

-- 读法：`(∏ s, tokenValue U W s.1.val (tokens x p s))` 等于 `∏ i, W (x i)`。按 `p s = Fin.last n` 成立与否分情况。
theorem Issuance.product (h : Issuance x p) (hu : ∀ i, (x i).length ≤ U) (W : List Bool → F) :
    (∏ s, tokenValue U W s.1.val (tokens x p s)) = ∏ i, W (x i) := by
  have he (s : Calls t U) : tokenValue U W s.1.val (tokens x p s) =
      ∏ i : Fin n, if p s = i.castSucc then W (x i) else 1 := by
    by_cases hn : p s = Fin.last n
    · simp [tokens, hn, emptyToken, tokenValue, Ne.symm (Fin.castSucc_ne_last _)]
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hn
    have hb : (x i).length ≤ 2 ^ s.1.val := by
      rw [← h.index hi.symm]
      exact (le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
    simp [tokens, ← hi, tokenValue_encode W _ _ (hu i) hb]
  simp_rw [he]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  -- 推导：从 `h.covers hu i` 中取出 `s, hs, hu`。
  obtain ⟨s, hs, hu⟩ := h.covers hu i
  rw [Finset.prod_eq_single s]
  · exact ite_eq_left hs
  · intro z _ hz
    exact ite_eq_right (mt (hu z) hz)
  · simp

end OAI.LinearAlgebra.MatrixExponent.Transcript.RAM
end
