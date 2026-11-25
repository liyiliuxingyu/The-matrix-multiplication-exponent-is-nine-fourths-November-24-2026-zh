-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Code
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift
import OAI.LinearAlgebra.MatrixExponent.Coloring.Formula
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Decor
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryControl
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Transport.System

section
/-!
# 具有索引读取指令的直线字程序

数据类型有单比特、有界无符号字、有序对和长度为二的幂的数组。有序对和数组不可变，可通过地址共享。程序与其输入无关。制表按索引递增顺序写入新数组，各个索引对应的程序均计入指令数。每个字面量（包括静态索引）占一个字。布尔门具有四比特真值表。规则同时给出程序的语义与费用。宽度上界适用于算术操作数及字面量。为存储寻址时，可取该宽度与表示输入及已分配字数所需二进制位数中的最大值。大表求值、搜索和排序均未被当成单位成本的原语。

**英文原文**

Straight-line word programs with indexed loads

Data are single bits, bounded unsigned words, pairs, and dyadic
arrays. Pairs and arrays are immutable and can be shared by address.
A program is independent of its input. Tabulation writes a fresh
array in increasing index order, with the program for each index
included in the instruction count. A literal, including a static
index, occupies one word. Boolean gates have four-bit truth tables.

The rules give the denotation and charge of a program simultaneously.
The width bounds apply to arithmetic operands and literals. To address
storage one may take the maximum of this width and the binary length
of the input and the allocated words. There is no unit-cost primitive
for evaluating large tables, searching, or sorting.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

-- 读法：归纳构造子包括 `id`、`fst`、`snd`、`comp`、`pair`、`select`、`tab`、`read`。
inductive RAM (w : ℕ) : {A D : Type} → (A → D) → ℕ → Prop
  | id {A} : RAM w (_root_.id : A → A) 1
  | fst {A D} : RAM w (Prod.fst : A × D → A) 1
  | snd {A D} : RAM w (Prod.snd : A × D → D) 1
  | comp {A D E} {f : A → D} {g : D → E} {m n} :
      RAM w f m → RAM w g n → RAM w (g ∘ f) (m + n)
  | pair {A D E} {f : A → D} {g : A → E} {m n} :
      RAM w f m → RAM w g n → RAM w (fun x => (f x, g x)) (m + n + 1)
  | select {A} : RAM w (fun x : Bool × A × A => if x.1 then x.2.1 else x.2.2) 1
  | tab {A D} {h m : ℕ} (hh : h ≤ w) (f : B h → A → D) (hf : ∀ i, RAM w (f i) m) :
      RAM w (fun x i => f i x) (2 ^ h * (m + 1))
  | «at» {A} {h : ℕ} (hh : h ≤ w) (i : B h) : RAM w (fun x : B h → A => x i) 1
  | read {A} {h : ℕ} (hh : h ≤ w) : RAM w (fun x : (B h → A) × B h => x.1 x.2) 1
  | bit {A} (b : Bool) : RAM w (fun _ : A => b) 1
  | lit {A} {h : ℕ} (hh : h ≤ w) (i : B h) : RAM w (fun _ : A => i) 1
  | gate (f : Bool × Bool → Bool) : RAM w f 1
  | lt {h : ℕ} (hh : h ≤ w) : RAM w (fun x : B h × B h => decide (x.1 < x.2)) 1
  | eq {h : ℕ} (hh : h ≤ w) : RAM w (fun x : B h × B h => decide (x.1 = x.2)) 1
  | add {h : ℕ} (hh : h ≤ w) : RAM w (fun x : B h × B h => x.1 + x.2) 1
  | resize {h k : ℕ} (hh : h ≤ w) (hk : k ≤ w) : RAM w (fun x : B h => Fin.ofNat (2 ^ k) x.val) 1
  | odd {h : ℕ} (hh : h ≤ w) : RAM w (fun x : B h => decide (x.val % 2 = 1)) 1
  | halve {h : ℕ} (hh : h ≤ w) : RAM w (fun x : B h =>
      (⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩ : B h)) 1
  | mono {A D} {f : A → D} {m n} : RAM w f m → m ≤ n → RAM w f n

namespace RAM
variable {w h k m n : ℕ} {A D E : Type}

-- 读法：要证明的命题是 `RAM v f n`。对 `h` 作归纳。
theorem widen {f : A → D} (h : RAM w f n) {v : ℕ} (hw : w ≤ v) : RAM v f n := by
  induction h with
  | id => exact .id
  | fst => exact .fst
  | snd => exact .snd
  | comp _ _ h j => exact h.comp j
  | pair _ _ h j => exact h.pair j
  | select => exact .select
  | tab hh f _ ih => exact .tab (hh.trans hw) f ih
  | «at» h i => exact .at (h.trans hw) i
  | read h => exact .read (h.trans hw)
  | bit b => exact .bit b
  | lit h i => exact .lit (h.trans hw) i
  | gate g => exact .gate g
  | lt h => exact .lt (h.trans hw)
  | eq h => exact .eq (h.trans hw)
  | add h => exact .add (h.trans hw)
  | resize h k => exact .resize (h.trans hw) (k.trans hw)
  | odd h => exact .odd (h.trans hw)
  | halve h => exact .halve (h.trans hw)
  | mono _ hn ih => exact ih.mono hn

-- 读法：要证明的命题是 `RAM w (fun x => (x, f x)) (1 + n + 1)`。使用 `RAM.id.pair` 给出的结论。
theorem keep {f : A → D} (h : RAM w f n) : RAM w (fun x => (x, f x)) (1 + n + 1) := RAM.id.pair h

-- 读法：要证明的命题是 `RAM w (fun x : (B h → A) × (B k → B h) => x.1 ∘ x.2) (2 ^ k * 6)`。
theorem gather (hh : h ≤ w) (hk : k ≤ w) :
    RAM w (fun x : (B h → A) × (B k → B h) => x.1 ∘ x.2) (2 ^ k * 6) :=
  .tab hk _ (fun i => (RAM.fst.pair (RAM.snd.comp (.at hk i))).comp (.read hh))

end RAM

-- 读法：`Computable` 的取值由 `RAM (3 * h + 10) f (2 ^ h * (100 + h) ^ c)` 给出。
def Computable (h : ℕ) (f : (B h → B h) → (B h → B h)) (c : ℕ) :=
  RAM (3 * h + 10) f (2 ^ h * (100 + h) ^ c)

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

section
/-!
# 近线性字程序的界

**英文原文**

Bounds for near-linear word programs
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm

-- 读法：`2 ^ h * (100 + w) ^ c` 不超过 `2 ^ h * (100 + w) ^ d`。使用 `Nat.mul_le_mul_left` 给出的结论。
theorem budget_mono (h w : ℕ) {c d : ℕ} (hc : c ≤ d) :
    2 ^ h * (100 + w) ^ c ≤ 2 ^ h * (100 + w) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hc)

-- 读法：`100 * (2 ^ h * (100 + w) ^ c)` 不超过 `2 ^ h * (100 + w) ^ (c + 1)`。这里调用 `Nat.mul_le_mul_left`。
theorem budget_step (h w c : ℕ) :
    100 * (2 ^ h * (100 + w) ^ c) ≤ 2 ^ h * (100 + w) ^ (c + 1) := by
  rw [pow_succ, ← mul_assoc (2 ^ h), mul_comm 100]
  exact Nat.mul_le_mul_left _ (by omega)

-- 读法：`2 ^ h` 不超过 `2 ^ h * (100 + w) ^ c`。这里调用 `budget_mono`。
theorem budget_base (h w c : ℕ) : 2 ^ h ≤ 2 ^ h * (100 + w) ^ c := by
  simpa using budget_mono h w (Nat.zero_le c)

-- 读法：`2 ^ h * (100 + (3 * h + 10)) ^ c` 不超过 `2 ^ h * (100 + h) ^ (2 * c)`。这里调用 `Nat.mul_le_mul_left`。
theorem budget_width (h c : ℕ) :
    2 ^ h * (100 + (3 * h + 10)) ^ c ≤ 2 ^ h * (100 + h) ^ (2 * c) := by
  rw [pow_mul]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by ring_nf; omega) _)

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

section
/-!
# 提取确定性代码，并估计其建议串长度与工作内存

**英文原文**

Extracting deterministic code and a bound on its advice and working memory
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

namespace Code
variable {w h : ℕ} {A D : Type}

-- 读法：`tabulate hh f` 等于 `tab hh f`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem tabulate_eq (hh : h ≤ w) (f : B h → Code w A D) : tabulate hh f = tab hh f := by
  unfold tabulate
  apply congrArg (tab hh)
  funext i
  exact Vector.getElem_ofFn i.isLt

-- 读法：`c.advice + c.scratch` 不超过 `c.time`。这里调用 `Nat.add_le_add`。
/-- 时间预算同时覆盖程序字和临时存储分配，也包括所有制表操作增加的字。

英文原文：The time allowance covers both the program words and the scratch
allocation, including the extra words of all tabulations.
-/
theorem advice_scratch (c : Code w A D) : c.advice + c.scratch ≤ c.time := by
  change charge 8 1 c + charge 8 1 c ≤ charge 16 4 c
  rw [← two_mul]
  induction c <;> try {simp only [charge]; omega}
  case tab hh f ih =>
    simp only [charge, mul_add, Finset.mul_sum]
    apply Nat.add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i _
    have := ih i
    omega

end Code

variable {A D : Type} {w m : ℕ} {f : A → D}

-- 读法：存在 `c : Code w A D`，`c.eval = f` 与 `∀ a ≤ 16, ∀ b ≤ 4, Code.charge a b c + 16 ≤ 32 * m` 同时成立。对 `hf` 作归纳。
private theorem code_size (hf : RAM w f m) :
    ∃ c : Code w A D, c.eval = f ∧
      ∀ a ≤ 16, ∀ b ≤ 4, Code.charge a b c + 16 ≤ 32 * m := by
  have leaf : ∀ a ≤ 16, ∀ _b : ℕ, _b ≤ 4 → a + 16 ≤ 32 * 1 := by omega
  induction hf with
  | id => exact ⟨.id, rfl, leaf⟩
  | fst => exact ⟨.fst, rfl, leaf⟩
  | snd => exact ⟨.snd, rfl, leaf⟩
  | comp _ _ ih ih' =>
    obtain ⟨x, rfl, hx⟩ := ih
    -- 推导：从 `ih'` 中取出 `y, rfl, hy`。
    obtain ⟨y, rfl, hy⟩ := ih'
    refine ⟨.comp x y, rfl, fun a ha b hb => ?_⟩
    change a + Code.charge a b x + Code.charge a b y + 16 ≤ _
    have := hx a ha b hb
    have := hy a ha b hb
    omega
  | pair _ _ ih ih' =>
    obtain ⟨x, rfl, hx⟩ := ih
    obtain ⟨y, rfl, hy⟩ := ih'
    refine ⟨.pair x y, rfl, fun a ha b hb => ?_⟩
    change a + Code.charge a b x + Code.charge a b y + 16 ≤ _
    have := hx a ha b hb
    have := hy a ha b hb
    omega
  | select => exact ⟨.select, rfl, leaf⟩
  | @tab A D h m hh f _ ih =>
    choose c hc he using ih
    refine ⟨Code.tabulate hh c, ?_⟩
    rw [Code.tabulate_eq]
    constructor
    · funext x i
      change (Vector.ofFn (fun j => (c j).eval x))[i.val] = _
      rw [Vector.getElem_ofFn, hc]
    · intro a ha b hb
      have e (i) : b + Code.charge a b (c i) ≤ 32 * m := by
        have := he i a ha b hb
        omega
      change a + (∑ i, (b + Code.charge a b (c i))) + 16 ≤ _
      -- 推导：记下中间结论 `es`：`(∑ i, (b + Code.charge a b (c i))) ≤ 2 ^ h * (32 * m)`。
      have es : (∑ i, (b + Code.charge a b (c i))) ≤ 2 ^ h * (32 * m) := calc
        _ ≤ ∑ _i : B h, 32 * m := Finset.sum_le_sum (fun i _ => e i)
        _ = _ := by simp
      nlinarith only [es, ha, Nat.two_pow_pos h]
  | «at» hh i => exact ⟨.at hh i, rfl, leaf⟩
  | read hh => exact ⟨.read hh, rfl, leaf⟩
  | bit b => exact ⟨.bit b, rfl, leaf⟩
  | lit hh i => exact ⟨.lit hh i, rfl, leaf⟩
  | gate g =>
    refine ⟨.gate (g (false, false)) (g (false, true)) (g (true, false)) (g (true, true)), ?_, leaf⟩
    funext x
    rcases x with ⟨_ | _, _ | _⟩ <;> rfl
  | lt hh => exact ⟨.lt hh, rfl, leaf⟩
  | eq hh => exact ⟨.eq hh, rfl, leaf⟩
  | add hh => exact ⟨.add hh, rfl, leaf⟩
  | resize hh hk => exact ⟨.resize hh hk, rfl, leaf⟩
  | odd hh => exact ⟨.odd hh, rfl, leaf⟩
  | halve hh => exact ⟨.halve hh, rfl, leaf⟩
  | mono _ hn ih =>
    -- 推导：从 `ih` 中取出 `c, hc, he`。
    obtain ⟨c, hc, he⟩ := ih
    exact ⟨c, hc, fun a ha b hb => (he a ha b hb).trans (Nat.mul_le_mul_left _ hn)⟩

-- 读法：存在 `c : Code w A D`，`c.eval = f` 与 `c.time ≤ 32 * m ∧ c.advice ≤ 32 * m` 同时成立。
/-- 同一固定程序处理所有输入。其时间、静态辅助信息量与临时空间分配量均在原费用上线性有界。

英文原文：One fixed program handles every input. Its time, static advice and
scratch allocation are linear in the original charge.
-/
theorem RAM.code (hf : RAM w f m) :
    ∃ c : Code w A D, c.eval = f ∧ c.time ≤ 32 * m ∧ c.advice ≤ 32 * m := by
  obtain ⟨c, hc, he⟩ := code_size hf
  exact ⟨c, hc, (Nat.le_add_right _ _).trans (he 16 le_rfl 4 le_rfl),
    (Nat.le_add_right _ _).trans (he 8 (by decide) 1 (by decide))⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

section
/-!
# 按颜色统计有效的虚设边

在得知输入前即可展开整个扫描。一个计数器有 h+1 位，所以即使将全部 2^h 个索引计入也不会溢出。

**英文原文**

Counting active dummy edges by colour

The scan can be unrolled before the input is known. A counter has
h+1 bits, so even a count of all 2^h indices fits without overflow.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
open Coloring

variable {h w : ℕ}

-- 读法：在后续公式中，`Masks` 是 `(B h → Bool) × (B h → Bool)` 的缩写。
private abbrev Masks (h : ℕ) := (B h → Bool) × (B h → Bool)

-- 读法：`countBits` 的取值由 `Fin.ofNat _ (s.filter (fun i => δ i = true ∧ x.1 i = true ∧ x.2 i = b)).card` 给出。
private def countBits (δ : B h → Bool) (b : Bool) (s : Finset (B h)) (x : Masks h) : B (h + 1) :=
  Fin.ofNat _ (s.filter (fun i => δ i = true ∧ x.1 i = true ∧ x.2 i = b)).card

-- 读法：`(countBits δ b s x).val` 等于 `(s.filter (fun i => δ i = true ∧ x.1 i = true ∧ x.2 i = b)).card`。这里调用 `Nat.mod_eq_of_lt`。
private theorem countBits_val (δ : B h → Bool) (b : Bool) (s : Finset (B h)) (x : Masks h) :
    (countBits δ b s x).val = (s.filter (fun i => δ i = true ∧ x.1 i = true ∧ x.2 i = b)).card := by
  apply Nat.mod_eq_of_lt
  refine (Finset.card_le_univ _).trans_lt ?_
  simp only [Fintype.card_fin, pow_succ]
  have := Nat.two_pow_pos h
  omega

-- 读法：要证明的命题是 `RAM w (countBits δ b s) (1 + 16 * s.card)`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
private theorem counters (hh : h + 1 ≤ w) (δ : B h → Bool) (b : Bool) (s : Finset (B h)) :
    RAM w (countBits δ b s) (1 + 16 * s.card) := by
  have hr : h ≤ w := by omega
  induction s using Finset.induction_on with
  | empty =>
    have e : countBits δ b ∅ = fun _ => (0 : B (h + 1)) := by
      funext x
      simp [countBits]
    rw [e, Finset.card_empty]
    exact .lit hh _
  | @insert i s hi ih =>
    -- 推导：记下中间结论 `g`：`RAM w (fun x : Masks h => decide (δ i = true ∧ x.1 i = true ∧ x.2 i = b)) 6`。
    have g : RAM w (fun x : Masks h => decide (δ i = true ∧ x.1 i = true ∧ x.2 i = b)) 6 :=
      ((RAM.fst.comp (.at hr i)).pair (RAM.snd.comp (.at hr i))).comp
        (.gate (fun y => decide (δ i = true ∧ y.1 = true ∧ y.2 = b)))
    have inc := (g.pair ((RAM.lit hh 1).pair (RAM.lit hh 0))).comp RAM.select
    have H := (ih.pair inc).comp (.add hh)
    have e : countBits δ b (insert i s) = fun x => countBits δ b s x +
        if decide (δ i = true ∧ x.1 i = true ∧ x.2 i = b) then 1 else 0 := by
      funext x
      by_cases hv : δ i = true ∧ x.1 i = true ∧ x.2 i = b
      · simp only [countBits, Finset.filter_insert, decide_eq_true_eq, ite_eq_left hv]
        rw [Finset.card_insert_of_notMem (fun he => hi (Finset.mem_filter.mp he).1)]
        apply Fin.ext
        exact Nat.add_mod _ _ _
      · simp only [countBits, Finset.filter_insert, decide_eq_true_eq, ite_eq_right hv, add_zero]
    rw [e, Finset.card_insert_of_notMem hi]
    exact H.mono (by omega)

-- 读法：要证明的命题是 `RAM w (fun x : (B h → Bool) × (B h → Bool) => Coloring.minority δ x.1 x.2) (2 ^ h * (100 + w) ^ 10)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem minority (hh : h + 1 ≤ w) (δ : B h → Bool) :
    RAM w (fun x : (B h → Bool) × (B h → Bool) => Coloring.minority δ x.1 x.2)
      (2 ^ h * (100 + w) ^ 10) := by
  have C := ((counters hh δ false Finset.univ).pair (counters hh δ true Finset.univ)).comp (.lt hh)
  have neg : RAM w (fun b : Bool => !b) 4 := (RAM.id.pair RAM.id).comp (.gate (fun x => !x.1))
  have he : (fun x : Masks h => Coloring.minority δ x.1 x.2) =
      fun x => !(decide (countBits δ false Finset.univ x < countBits δ true Finset.univ x)) := by
    funext x
    rw [Bool.eq_iff_iff]
    simp [Coloring.minority, Fin.lt_def, countBits_val]
  rw [he]
  apply (C.comp neg).mono
  simp only [Finset.card_univ, Fintype.card_fin]
  have M := budget_step h w 0
  have N := budget_mono h w (by decide : 1 ≤ 10)
  simp only [pow_zero, mul_one, Nat.zero_add] at M
  have := Nat.two_pow_pos h
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
end

section
/-!
# 控制器对地址表的操作

**英文原文**

Controller operations on tables of addresses
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm

open Coloring

-- 读法：在后续公式中，`Endo` 是 `(B h → B h) → (B h → B h)` 的缩写。
abbrev Endo (h : ℕ) := (B h → B h) → (B h → B h)

-- 读法：结构的字段包括 `ident`、`const`、`comp`、`point`、`mask`。
/-- 成本上界与高度和固定表无关。逆操作只需在置换输入上正确。

英文原文：The cost bounds are independent of the height and the fixed tables.
The inverse need only be correct on permutations.
-/
structure Computability (P : ∀ h, Endo h → ℕ → Prop) : Prop where
  ident : ∃ c, ∀ h, P h id c
  const : ∃ c, ∀ h (x : B h → B h), P h (fun _ => x) c
  comp : ∀ c d, ∃ a, ∀ h (f g : Endo h), P h f c → P h g d → P h (g ∘ f) a
  point : ∀ c d, ∃ a, ∀ h (f g : Endo h), P h f c → P h g d →
    P h (fun x => f x ∘ g x) a
  mask : ∃ c, ∀ h (m : B h → Bool), P h (fun x i => if m i then x i else i) c
  charts : ∃ c d, ∀ h, ∃ inv : Endo h, P h inv c ∧
    (∀ g : Equiv.Perm (B h), inv g = ⇑g.symm) ∧ ∀ p : Coloring.Chart h,
      P h (fun x => (p.run inv x).1) d ∧
      P h (fun x => (p.run inv x).2.1) d ∧
      P h (fun x => (p.run inv x).2.2) d

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# 编译局部观测

在给定高度或置换之前，就固定群元素列表以及记录其中何者重合的表。

**英文原文**

Compiling local observations

The list of group elements and the table on their coincidences are
fixed before the height or the permutation is given.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Root
open Coloring

-- 读法：存在 `(t : ℕ) (g : B t → G) (b : (B t → B t → Bool) → B q)`，对每个 `r`，`b (fun i j => r.see (g i) (g j))` 等于 `f r`。
private theorem Local.table {G : Type} [Group G] {q : ℕ} {f : Root G → B q} (hf : Local f) :
    ∃ (t : ℕ) (g : B t → G) (b : (B t → B t → Bool) → B q),
      ∀ r, b (fun i j => r.see (g i) (g j)) = f r := by
  classical
  obtain ⟨E, hE⟩ := hf
  let e := encode ↥E
  let g := Function.extend e (fun i : ↥E => i.val) (fun _ => 1)
  have hg (x : G) (hx : x ∈ E) : g (e ⟨x, hx⟩) = x :=
    e.injective.extend_apply _ _ _
  let obs (r : Root G) i j := r.see (g i) (g j)
  have same (r s : Root G) (he : obs r = obs s) : f r = f s := by
    apply hE
    intro i hi j hj
    simpa only [obs, hg] using congrFun (congrFun he (e ⟨i, hi⟩)) (e ⟨j, hj⟩)
  let b z := if h : ∃ r, obs r = z then f h.choose else 0
  refine ⟨_, g, b, fun r => ?_⟩
  -- 推导：记下中间结论 `ex`：`∃ s, obs s = obs r`。
  have ex : ∃ s, obs s = obs r := ⟨r, rfl⟩
  change b (obs r) = _
  simp only [b, dite_eq_left ex]
  exact same _ _ ex.choose_spec

-- 读法：结论为 `∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v, Cheap F (h + 1) (h + 1) (Perm h) (.vec (h + 1) (.addr q)) v c ∧ ∀ π : Equiv.Perm (B h), ∀ i, v π i = e (f (@Root.mk _ _ (B (h + 1)) (T.action h π) i))`。
theorem Local.compile {F : Type} [Field F] {m q : ℕ} {T : Routes F m}
    {V : Type*} {f : Root (controllers F T.embed) → V} (hf : Local f) (e : V ↪ B q) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (Perm h) (.vec (h + 1) (.addr q)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ i, v π i = e (f (@Root.mk _ _ (B (h + 1)) (T.action h π) i)) := by
  obtain ⟨t, g, b, hb⟩ := (hf.map e).table
  obtain ⟨c, hc⟩ := T.controllers_net t g
  obtain ⟨k, hk⟩ := Cheap.equalityTable F t q
  refine ⟨max c 30 + 1, max (2 ^ t) k, fun h hh => ?_⟩
  obtain ⟨v, hv, he⟩ := hc h (by omega)
  have net := hv.comp (hk (h + 1) (h + 1) le_rfl (by omega) b)
  refine ⟨_, net, fun π i => ?_⟩
  let r := @Root.mk _ _ (B (h + 1)) (T.action h π) i
  refine Eq.trans ?_ (hb r)
  apply congrArg b
  funext j l
  rw [Bool.eq_iff_iff]
  simp only [see, decide_eq_true_eq, he]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Root
end

/-!
# 编译标记位点的局部函数

由置换确定地址。先比较这些地址，并收集地址处的标记，再应用固定的局部表。

**英文原文**

Compiling local functions of marked sites

The permutation determines the addresses. Compare them and gather the
marks there before applying the fixed local table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Decor
open Coloring

-- 读法：在后续公式中，`pattern` 是 `B t → B t → Bool` 的缩写。
private abbrev pattern (t : ℕ) := B t → B t → Bool

-- 读法：在后续公式中，`frame` 是 `Format.pair (.addr (Fintype.card (pattern t))) (.vec t (.addr q))` 的缩写。
private abbrev frame (t q : ℕ) :=
  Format.pair (.addr (Fintype.card (pattern t))) (.vec t (.addr q))

-- 读法：`observe` 的取值由 `(encode (pattern t) (fun i j => r.toRoot.see (g i) (g j)), fun i => r.mark (r.toRoot.label (g i)))` 给出。
private def observe {G : Type} [Group G] {t q : ℕ} (g : B t → G) (r : Decor G q) :
    (frame t q).obj :=
  (encode (pattern t) (fun i j => r.toRoot.see (g i) (g j)), fun i => r.mark (r.toRoot.label (g i)))

-- 读法：存在 `(t : ℕ) (g : B t → G) (b : (frame t q).obj → B l)`，对每个 `r`，`b (observe g r)` 等于 `enc (f r)`。
private theorem Local.table {G : Type} [Group G] {q l : ℕ} {V : Type*} {f : Decor G q → V}
    (hf : Local f) (enc : V ↪ B l) :
    ∃ (t : ℕ) (g : B t → G) (b : (frame t q).obj → B l),
      ∀ r, b (observe g r) = enc (f r) := by
  classical
  obtain ⟨E, hE⟩ := hf
  let e := encode ↥E
  let g := Function.extend e (fun i : ↥E => i.val) (fun _ => 1)
  have hg (x : G) (hx : x ∈ E) : g (e ⟨x, hx⟩) = x :=
    e.injective.extend_apply _ _ _
  have same (r s : Decor G q) (he : observe g r = observe g s) : f r = f s := by
    apply hE
    · intro i hi j hj
      have hp := (encode _).injective (congrArg Prod.fst he)
      simpa only [hg] using congrFun (congrFun hp (e ⟨i, hi⟩)) (e ⟨j, hj⟩)
    · intro i hi
      simpa only [observe, hg] using congrFun (congrArg Prod.snd he) (e ⟨i, hi⟩)
  let b z := if h : ∃ r, observe g r = z then enc (f h.choose) else 0
  refine ⟨_, g, b, fun r => ?_⟩
  -- 推导：记下中间结论 `ex`：`∃ s, observe g s = observe g r`。
  have ex : ∃ s, observe g s = observe g r := ⟨r, rfl⟩
  simp only [b, dite_eq_left ex]
  exact congrArg enc (same _ _ ex.choose_spec)

-- 读法：结论为 `∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v, Cheap F (h + 1) (h + 1) (.pair (Perm h) (.vec (h + 1) (.addr q))) (.vec (h + 1) (.addr l)) v c ∧ ∀ π : Equiv.Perm (B h), ∀ z i, v (π, z) i = e (f ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩)`。
theorem Local.compile {F : Type} [Field F] {m l q : ℕ} {T : Routes F m}
    {V : Type*} {f : Decor (controllers F T.embed) q → V} (hf : Local f) (e : V ↪ B l) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (.pair (Perm h) (.vec (h + 1) (.addr q))) (.vec (h + 1) (.addr l)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ z i,
        v (π, z) i = e (f ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩) := by
  obtain ⟨t, g, b, hb⟩ := hf.table e
  obtain ⟨c, hc⟩ := T.controllers_net t g
  obtain ⟨k, hk⟩ := Cheap.equalityTable F t (Fintype.card (pattern t))
  let Y := frame t q
  let cost := 2 * Y.width + (Format.addr l).width + Install.localCost Y.width * (Format.addr l).width
  refine ⟨c + 50, 2 ^ t + k + q + cost, fun h hh => ?_⟩
  have ht := Nat.two_pow_pos t
  let X := Format.pair (Perm h) (.vec (h + 1) (.addr q))
  -- 推导：记下中间结论 `hw`：`X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ 2`。
  have hw : X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ 2 := by
    simp only [X, Format.width_pair, Format.width_vec, Format.width_addr]
    have hu := Nat.mul_le_mul_left (2 ^ (h + 1)) (show q ≤ h by omega)
    ring_nf at hu ⊢
    omega
  have input := Cheap.id F hw
  obtain ⟨v, hv, he⟩ := hc h (by omega)
  have addr := input.fst.comp hv
  have eqs := addr.comp (hk (h + 1) (h + 1) le_rfl (by omega) (encode (pattern t)))
  have marks := (input.snd.pair addr).comp (Cheap.neighbors F (.addr q) (h + 1) (h + 1) t
    le_rfl (by rw [Format.width_addr]; omega) (by omega))
  have tab : Cheap F 0 (h + 1) Y (.addr l) b 1 :=
    Cheap.fixed F b (show cost ≤ h + 1 by omega)
  have net := (eqs.pair marks).zip.comp (Cheap.map _ (fun _ => tab))
  refine ⟨_, net.mono (by omega), fun π z i => ?_⟩
  let r : Decor (controllers F T.embed) q := ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩
  refine Eq.trans ?_ (hb r)
  apply congrArg b
  apply Prod.ext
  · apply congrArg (encode (pattern t))
    funext j l
    rw [Bool.eq_iff_iff]
    simp only [Root.see, decide_eq_true_eq, Function.comp_apply, id_eq, he]
    rfl
  · funext j
    exact congrArg z (he π j i)

end OAI.LinearAlgebra.MatrixExponent.Routing.Decor
end

section
/-!
# 在每个位点执行各自选定的操作

每个局部决策指定固定动作列表中的一个成员。要构造地址的一个比特，电路只需读取编码后的决策和各候选地址的对应比特。

**英文原文**

Dispatching to an action chosen at each site

A local decision names a member of a fixed list of actions. To
materialize one address bit the circuit needs only the encoded decision
and the corresponding bit of each candidate address.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Decor
open Coloring

-- 读法：在后续公式中，`Plan` 是 `B l × (B p → Bool × Bool × B k × B p)` 的缩写。
abbrev Plan (l p k : ℕ) := B l × (B p → Bool × Bool × B k × B p)

-- 读法：`resolve` 的取值由 `(x.1, fun j => let t := x.2 j; (t.1, t.2.1, a t.2.2.1, t.2.2.2))` 给出。
def resolve {l p k h : ℕ} (x : Plan l p k) (a : B k → B (h + 1)) :
    B l × (B p → (Transport.Command h p).obj) :=
  (x.1, fun j => let t := x.2 j; (t.1, t.2.1, a t.2.2.1, t.2.2.2))

-- 读法：在后续公式中，`Row` 是 `Format.pair (.addr l) (.vec p (Transport.Command h p))` 的缩写。
private abbrev Row (h p l : ℕ) := Format.pair (.addr l) (.vec p (Transport.Command h p))
-- 读法：在后续公式中，`Source` 是 `Format.pair (.vec (h + 1) (.addr s)) (.vec k (Perm (h + 1)))` 的缩写。
private abbrev Source (h k s : ℕ) := Format.pair (.vec (h + 1) (.addr s)) (.vec k (Perm (h + 1)))

variable {l p k h s : ℕ}

-- 读法：结论为 `∃ d : slots (word (h + 1)), ∀ (x : Plan l p k) (a b : B k → B (h + 1)), (∀ i, (Format.addr (h + 1)).code (a i) d = (Format.addr (h + 1)).code (b i) d) → (Row h p l).code (resolve x a) z = (Row h p l).code (resolve x b) z`。
private theorem resolve_bit (z : (Row h p l).pins) :
    ∃ d : slots (word (h + 1)), ∀ (x : Plan l p k) (a b : B k → B (h + 1)),
      (∀ i, (Format.addr (h + 1)).code (a i) d = (Format.addr (h + 1)).code (b i) d) →
      (Row h p l).code (resolve x a) z = (Row h p l).code (resolve x b) z := by
  rcases z with z | ⟨j, z | z | z | z⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨z, fun x a b he => he ((x.2 j).2.2.1)⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩

-- 读法：输入 `i` 时返回 `resolve (g (x.1 i)) (fun j => x.2 j i)`。
private def select (g : B s → Plan l p k) (x : (Source h k s).obj) :
    (Transport.Controls h p (.addr l)).obj :=
  fun i => resolve (g (x.1 i)) (fun j => x.2 j i)

-- 读法：要证明的命题是 `Install.Depends ((Transport.Controls h p (.addr l)).code ∘ select g ∘ (Source h k s).code.symm) (s + 2 ^ k)`。这里调用 `Finset.card_union_le`。
private theorem select_depends (g : B s → Plan l p k) :
    Install.Depends ((Transport.Controls h p (.addr l)).code ∘ select g ∘
      (Source h k s).code.symm) (s + 2 ^ k) := by
  classical
  rintro ⟨i, z⟩
  obtain ⟨d, hd⟩ := resolve_bit (k := k) z
  let key (u : slots (word s)) : (Source h k s).pins := .inl (i, u)
  let val (u : B k) : (Source h k s).pins := .inr (u, i, d)
  refine ⟨Finset.univ.image key ∪ Finset.univ.image val, ?_, fun x y he => ?_⟩
  · apply (Finset.card_union_le _ _).trans
    -- 推导：记下中间结论 `hl`：`= Finset.card_image_le (s`。
    have hl := Finset.card_image_le (s := Finset.univ) (f := key)
    have hr := Finset.card_image_le (s := Finset.univ) (f := val)
    simpa only [Finset.card_univ, card_slots, wd_word, Fintype.card_fin] using Nat.add_le_add hl hr
  · let a := (Source h k s).code.symm x
    let b := (Source h k s).code.symm y
    have hl : a.1 i = b.1 i := by
      apply congrArg (Control.decode s)
      funext u
      exact he (key u) (by simp)
    have hr (j : B k) : (Format.addr (h + 1)).code (a.2 j i) d =
        (Format.addr (h + 1)).code (b.2 j i) d := by
      change (Source h k s).code a (val j) = (Source h k s).code b (val j)
      simp only [a, b, Equiv.apply_symm_apply]
      exact he (val j) (by simp)
    change (Row h p l).code (resolve (g (a.1 i)) (fun j => a.2 j i)) z =
      (Row h p l).code (resolve (g (b.1 i)) (fun j => b.2 j i)) z
    rw [hl]
    exact hd _ _ _ hr

-- 读法：存在 `k₀ : ℕ`，对每个 `h ≥ k₀`，映射 `(select g)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((h + 1)) * (100 + ((h + 1))) ^ (5)` 为上界。
private theorem cheap_select (F : Type) [Field F] (g : B s → Plan l p k) :
    ∃ k₀ : ℕ, ∀ h ≥ k₀, Cheap F (h + 1) (h + 1) (Source h k s)
      (Transport.Controls h p (.addr l)) (select g) 5 := by
  let C := Install.localCost (s + 2 ^ k)
  refine ⟨max s (max l (max p (max (2 ^ k) (max (2 ^ p) C)))), fun h hb => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hb
  obtain ⟨hs, hl, hp, hk, hr, hc⟩ := hb
  refine ⟨_, (select_depends (h := h) g).bnet F, ?_⟩
  change (Source h k s).width + (Transport.Controls h p (.addr l)).width +
    ((Source h k s).width + C * (Transport.Controls h p (.addr l)).width) ≤ _
  simp only [Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, Format.width_addr (h + 1)]
  calc
    _ = 2 ^ (h + 1) * (2 * (s + 2 ^ k * (h + 1)) + (C + 1) * (l + 2 ^ p * (2 + (h + 1) + p))) := by ring
    _ ≤ 2 ^ (h + 1) * (2 * (h + h * (h + 1)) + (h + 1) * (h + h * (2 + (h + 1) + h))) := by gcongr
    _ ≤ _ := by gcongr; ring_nf; omega

-- 读法：证明中先建立 `hx`，即 `X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ c`。
theorem Local.dispatch {F : Type} [Field F] {m q : ℕ} {T : Routes F m}
    {f : Decor (controllers F T.embed) q → Plan l p k} (hf : Local f)
    (w : B k → controllers F T.embed) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (.pair (Perm h) (.vec (h + 1) (.addr q))) (Transport.Controls h p (.addr l)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ z i,
        v (π, z) i = resolve (f ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩)
          (fun j => (T.action h π).smul (w j) i) := by
  let e := encode (Plan l p k)
  let g := Function.invFun e
  -- 推导：从 `hf.compile e` 中取出 `c, h₀, hl`。
  obtain ⟨c, h₀, hl⟩ := hf.compile e
  obtain ⟨c', hr⟩ := T.controllers_net k w
  obtain ⟨h₁, hs⟩ := cheap_select F g
  refine ⟨c + c' + 10, max h₀ (max h₁ (2 ^ k)), fun h hh => ?_⟩
  obtain ⟨u, hu, eu⟩ := hl h (by omega)
  obtain ⟨v, hv, ev⟩ := hr h (by omega)
  let X := Format.pair (Perm h) (.vec (h + 1) (.addr q))
  have hx : X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ c := by
    obtain ⟨_, _, hw⟩ := hu
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hw)
  have addresses := (Cheap.id F hx).fst.comp hv
  have net := (hu.pair addresses).comp (hs h (by omega))
  refine ⟨_, net.mono (by omega), fun π z i => ?_⟩
  change resolve (g (u (π, z) i)) (fun j => v π j i) = _
  rw [eu, show ∀ x, g (e x) = x from Function.leftInverse_invFun e.injective]
  exact congrArg _ (funext fun j => ev π j i)

end OAI.LinearAlgebra.MatrixExponent.Routing.Decor
end

/-!
# 局部操作程序的固定决策表

这张表的输入仅含相等性比特和选择器标记，其形状与高度无关。将输入与其有限多个可能值逐一比较，即可编译此表；每次比较都计费。

**英文原文**

A fixed decision table for a local action program

The input to this table contains only equality bits and selector marks.
Its shape is independent of the height. Compile by exhaustive tests
against its finitely many possible inputs, charging for every test.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
open Coloring
open scoped Classical

variable {w t p q l : ℕ} {A D : Type}

-- 读法：`Tested` 表示以下条件：对每个 `a : A`，存在 `c`，要证明的命题是 `RAM w (fun x : A => decide (x = a)) c`。
private def Tested (w : ℕ) (A : Type) [DecidableEq A] : Prop :=
  ∀ a : A, ∃ c, RAM w (fun x : A => decide (x = a)) c

-- 读法：要证明的命题是 `Tested w Bool`。
private theorem tested_bool : Tested w Bool := by
  intro a
  exact ⟨_, (RAM.id.pair RAM.id).comp (.gate (fun x => decide (x.1 = a)))⟩

-- 读法：要证明的命题是 `Tested w (B q)`。
private theorem tested_word (hq : q ≤ w) : Tested w (B q) := by
  intro a
  exact ⟨_, (RAM.id.pair (.lit hq a)).comp (.eq hq)⟩

-- 读法：要证明的命题是 `Tested w (A × D)`。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem Tested.prod [DecidableEq A] [DecidableEq D] (ha : Tested w A) (hd : Tested w D) :
    Tested w (A × D) := by
  rintro ⟨a, d⟩
  obtain ⟨c, hf⟩ := ha a
  obtain ⟨d', hg⟩ := hd d
  have H := ((RAM.fst.comp hf).pair (RAM.snd.comp hg)).comp (.gate (fun x => x.1 && x.2))
  refine ⟨1 + c + (1 + d') + 1 + 1, ?_⟩
  convert H using 1
  funext x
  rw [Bool.eq_iff_iff]
  simp [Prod.ext_iff]

-- 读法：要证明的命题是 `Tested w (B t → A)`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
private theorem Tested.arr [DecidableEq A] (ha : Tested w A) (ht : t ≤ w) :
    Tested w (B t → A) := by
  intro a
  have scan (s : Finset (B t)) :
      ∃ c, RAM w (fun x : B t → A => decide (∀ i ∈ s, x i = a i)) c := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_⟩
      simpa using (RAM.bit (w := w) (A := B t → A) true)
    | insert i s hi ih =>
      -- 推导：从 `ha (a i)` 中取出 `c, hf`。
      obtain ⟨c, hf⟩ := ha (a i)
      obtain ⟨d, hg⟩ := ih
      have H := (((RAM.at ht i).comp hf).pair hg).comp (.gate (fun x => x.1 && x.2))
      refine ⟨1 + c + d + 1 + 1, ?_⟩
      convert H using 1
      funext x
      rw [Bool.eq_iff_iff]
      simp
  obtain ⟨c, hc⟩ := scan Finset.univ
  refine ⟨c, ?_⟩
  convert hc using 1
  funext x
  rw [Bool.eq_iff_iff]
  simp [funext_iff]

-- 读法：存在 `c`，要证明的命题是 `RAM w f c`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
private theorem fixed_lookup [Fintype A] [Nonempty A] [DecidableEq A] (ha : Tested w A)
    (hd : ∀ d : D, ∃ c, RAM w (fun _ : A => d) c) (f : A → D) : ∃ c, RAM w f c := by
  have scan (s : Finset A) : ∃ c g, RAM w g c ∧ ∀ a ∈ s, g a = f a := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨c, hc⟩ := hd (f (Classical.arbitrary A))
      exact ⟨c, _, hc, by simp⟩
    | insert i s hi ih =>
      obtain ⟨c, g, hg, he⟩ := ih
      obtain ⟨_, ht⟩ := ha i
      obtain ⟨_, hv⟩ := hd (f i)
      refine ⟨_, _, (ht.pair (hv.pair hg)).comp RAM.select, fun a h => ?_⟩
      by_cases ha' : a = i
      · simp [ha']
      · simpa [ha'] using he a ((Finset.mem_insert.mp h).resolve_left ha')
  obtain ⟨c, g, hg, he⟩ := scan Finset.univ
  rw [funext fun i => he i (Finset.mem_univ i)] at hg
  exact ⟨c, hg⟩

-- 读法：存在 `c`，要证明的命题是 `RAM w (fun _ : A => v) c`。
private theorem literal_plan (hl : l ≤ w) (hp : p ≤ w) (v : Decor.Plan l p p) :
    ∃ c, RAM w (fun _ : A => v) c := by
  have H : RAM w (fun _ : A => v.2) (2 ^ p * 8) :=
    .tab hp _ (fun i => (RAM.bit (v.2 i).1).pair ((RAM.bit (v.2 i).2.1).pair
      ((RAM.lit hp (v.2 i).2.2.1).pair (RAM.lit hp (v.2 i).2.2.2))))
  exact ⟨_, (RAM.lit hl v.1).pair H⟩

-- 读法：在后续公式中，`Observation` 是 `(B t → B t → Bool) × (B t → B q)` 的缩写。
abbrev Observation (t q : ℕ) := (B t → B t → Bool) × (B t → B q)

variable {G : Type} [Group G]

-- 读法：`observe` 的取值由 `(fun i j => r.see (g i) (g j), fun i => r.mark (r.label (g i)))` 给出。
def observe (g : B t → G) (r : Decor G q) : Observation t q :=
  (fun i j => r.see (g i) (g j), fun i => r.mark (r.label (g i)))

-- 读法：`∃ (t : ℕ) (g : B t → G) (b : Observation t q → Decor.Plan l p p) (w c : ℕ), RAM w b c` 与 `∀ r, b (observe g r) = f r` 同时成立。
theorem menu {f : Decor G q → Decor.Plan l p p} (hf : Decor.Local f) :
    ∃ (t : ℕ) (g : B t → G) (b : Observation t q → Decor.Plan l p p) (w c : ℕ),
      RAM w b c ∧ ∀ r, b (observe g r) = f r := by
  obtain ⟨E, hE⟩ := hf
  let e := Coloring.encode ↥E
  let g := Function.extend e (fun i : ↥E => i.val) (fun _ => 1)
  have hg (x : G) (hx : x ∈ E) : g (e ⟨x, hx⟩) = x := e.injective.extend_apply _ _ _
  have same (r s : Decor G q) (he : observe g r = observe g s) : f r = f s := by
    apply hE
    · intro i hi j hj
      simpa only [observe, hg] using congrFun (congrFun (congrArg Prod.fst he) (e ⟨i, hi⟩)) (e ⟨j, hj⟩)
    · intro i hi
      simpa only [observe, hg] using congrFun (congrArg Prod.snd he) (e ⟨i, hi⟩)
  let b z := if h : ∃ r, observe g r = z then f h.choose else Classical.arbitrary (Decor.Plan l p p)
  let t := Fintype.card ↥E
  let w := t + q + l + p
  -- 推导：记下中间结论 `ht`：`t ≤ w`。
  have ht : t ≤ w := by unfold w; omega
  have hq : q ≤ w := by unfold w; omega
  have H : Tested w (Observation t q) :=
    ((tested_bool.arr ht).arr ht).prod ((tested_word hq).arr ht)
  obtain ⟨c, hc⟩ := fixed_lookup H (literal_plan (l := l) (p := p) (by unfold w; omega)
    (by unfold w; omega)) b
  refine ⟨t, g, b, w, c, hc, fun r => ?_⟩
  have ex : ∃ s, observe g s = observe g r := ⟨r, rfl⟩
  simp only [b, dite_eq_left ex]
  exact same _ _ ex.choose_spec

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.RAM
end
