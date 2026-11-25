-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.RetagStore
import OAI.LinearAlgebra.MatrixExponent.Assembly.ChannelPlan
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood

section
/-!
对小端序地址进行截断或补零扩展。

**英文原文**

Truncate or zero-extend little-endian addresses.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
open Coloring

-- 读法：逐一匹配以下输入模式：`0, m, _`、`_ + 1, 0, _`、`n + 1, m + 1, x`。
private def resize : (n m : ℕ) → Val (word n) → Val (word m)
  | 0, m, _ => Lookup.bits m 0
  | _ + 1, 0, _ => ()
  | n + 1, m + 1, x => (x.1, resize n m x.2)

-- 读法：`Lookup.value m (resize n m x)` 等于 `Lookup.value n x % 2 ^ m`。对 `n` 作归纳，并把 `m` 保持为任意参数。
private theorem resize_value (n m : ℕ) (x : Val (word n)) :
    Lookup.value m (resize n m x) = Lookup.value n x % 2 ^ m := by
  induction n generalizing m with
  | zero => simp [resize, Lookup.value_bits, Lookup.value]
  | succ n ih =>
    cases m with
    | zero => simp [Lookup.value, Nat.mod_one]
    | succ m =>
      have hh := Nat.mod_add_div (Lookup.value n x.2) (2 ^ m)
      rw [← ih] at hh
      have e : Lookup.value (n + 1) x = Lookup.value (m + 1) (resize (n + 1) (m + 1) x) +
          2 ^ (m + 1) * (Lookup.value n x.2 / 2 ^ m) := by
        change x.1.toNat + 2 * Lookup.value n x.2 =
          x.1.toNat + 2 * Lookup.value m (resize n m x.2) + _
        rw [pow_succ']
        nlinarith only [hh]
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Control.value_lt _ _)]

variable (F : Type) [Field F]

-- 读法：在 `F` 上，函数 `(resize n m)` 从 `(word n)` 到 `(word m)` 的图张量可由至多 `(n + m)` 个顶点实现。对 `n` 作归纳，并把 `m` 保持为任意参数。
private theorem resize_net (n m : ℕ) : DNet F (word n) (word m) (resize n m) (n + m) := by
  induction n generalizing m with
  | zero => simpa [resize] using Lookup.const_net F (word m) (Lookup.bits m 0)
  | succ n ih =>
    cases m with
    | zero => have h := DNet.discard F (word (n + 1)); rw [wd_word] at h; exact h
    | succ m => exact ((DNet.id F .bit).par (ih m)).mono (by simp [wd]; omega)

-- 读法：映射 `(shrink m)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (2)` 为上界。这里调用 `Circuit.of_dnet`。
theorem cheap_shrink {n m t : ℕ} (hn : n ≤ t) (hm : m ≤ t) :
    Cheap F 0 t (.addr n) (.addr m) (shrink m) 2 := by
  refine ⟨n + m, ?_, by simp; ring_nf; omega⟩
  apply Circuit.of_dnet (.refl _) (.refl _) (resize_net F n m)
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_addr, ← code_addr]
  congr 1
  exact Fin.ext (resize_value n m x)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Intervals
end

/-!
在端口表中读取两个端点，再并行展开各个二进层级。

**英文原文**

Read both endpoints in the port table, then expand each dyadic level in parallel.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

namespace Peers
variable {p q : ℕ}

-- 读法：在后续公式中，`desc` 是 `Format.pair .bit (.pair R R)` 的缩写。
abbrev desc (R : Format) := Format.pair .bit (.pair R R)

-- 读法：`indexRow` 的取值由 `(x.1, v x.2.1, v x.2.2)` 给出。
def indexRow {R : Format} (v : R.obj → B q) (x : (desc R).obj) : (row q).obj :=
  (x.1, v x.2.1, v x.2.2)

-- 读法：`decode` 的取值由 `eval (indexRow v ∘ x)` 给出。
def decode {R : Format} (v : R.obj → B q) (x : B p → (desc R).obj) := eval (indexRow v ∘ x)

-- 读法：`height` 的取值由 `max p (max q R.width)` 给出。
def height (p q : ℕ) (R : Format) := max p (max q R.width)
-- 读法：`width` 的取值由 `height p q R + 3 * q + 1` 给出。
def width (p q : ℕ) (R : Format) := height p q R + 3 * q + 1

-- 读法：映射 `(fun x i => (x.1 i, x.2 i))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (t)) ^ (4)` 为上界。这里调用 `Nat.mul_le_mul_left`。
theorem zipper (F : Type) [Field F] (p : ℕ) {n t : ℕ} (hp : p ≤ n)
    (A D : Format) (h : A.width + D.width ≤ (100 + t) ^ 2) :
    Cheap F n t (.pair (.vec p A) (.vec p D)) (.vec p (.pair A D))
      (fun x i => (x.1 i, x.2 i)) 4 := by
  have hw : (Format.pair (.vec p A) (.vec p D)).width ≤ 2 ^ p * (100 + t) ^ 2 := by
    rw [Format.width_pair, Format.width_vec, Format.width_vec, ← mul_add]
    exact Nat.mul_le_mul_left _ h
  exact lift F (Cheap.id F hw).zip hp

-- 读法：对每个 `(n t : ℕ)`，要证明的命题是 `p ≤ n → max p R.width ≤ n → max p R.width + q + 1 ≤ t → Cheap F n t (.vec p (desc R)) (.vec p (row q)) (fun x => indexRow v ∘ x) 25`。
private theorem index_rows (F : Type) [Field F] (p : ℕ) (R : Format) (v : R.obj → B q) :
    ∀ (n t : ℕ), p ≤ n → max p R.width ≤ n → max p R.width + q + 1 ≤ t →
    Cheap F n t (.vec p (desc R)) (.vec p (row q)) (fun x => indexRow v ∘ x) 25 := by
  intro n t hp hv hu
  have hr : R.width ≤ t := by omega
  have hd : (desc R).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [desc]; ring_nf; omega
  have h := Cheap.id F hd
  have flag₀ := Cheap.map (h := p) (A := desc R) (D := .bit) (fun _ z => z.1) (fun _ => h.fst)
  have src₀ := Cheap.map (h := p) (A := desc R) (D := R) (fun _ z => z.2.1) (fun _ => h.snd.fst)
  have dst₀ := Cheap.map (h := p) (A := desc R) (D := R) (fun _ z => z.2.2) (fun _ => h.snd.snd)
  have tab := (lift F (cheap_table F p R v) hv).widen hu
  have src := (lift F src₀ hp).comp tab
  have dst := (lift F dst₀ hp).comp tab
  -- 推导：记下中间结论 `hq`：`q ≤ t`。
  have hq : q ≤ t := by omega
  have both := (src.pair dst).comp (zipper F p (t := t) hp (.addr q) (.addr q)
    (by simp; ring_nf; omega))
  have rows := ((lift F flag₀ hp).pair both).comp (zipper F p (t := t) hp .bit
    (.pair (.addr q) (.addr q)) (by simp; ring_nf; omega))
  have result := rows.mono (d := 25) (by decide)
  exact result

-- 读法：映射 `(decode v)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((height p q R)) * (100 + ((width p q R))) ^ (111)` 为上界。
theorem cheap_decode (F : Type) [Field F] (p : ℕ) (R : Format) (v : R.obj → B q) :
    Cheap F (height p q R) (width p q R) (.vec p (desc R)) (Perm q) (decode v) 111 := by
  let n := height p q R
  let t := width p q R
  have hq : max p q ≤ n := by unfold n height; omega
  have rows := index_rows F p R v n t (le_max_left _ _) (by unfold n height; omega)
    (by unfold t width height; omega)
  have endp := (lift F (cheap F p q) hq).widen (show max p q + 3 * q ≤ t by
    change _ ≤ n + 3 * q + 1; omega)
  have hr := (rows.comp endp).mono (d := 111) (by decide)
  rw [show eval ∘ (fun x : B p → (desc R).obj => indexRow v ∘ x) = decode v from rfl] at hr
  exact hr

end Peers

namespace Channels
variable {A D : Format} (S : Channels A D) (n : S.Levels → ℕ) (R : S.Levels → Format)

-- 读法：在后续公式中，`commands` 是 `Fmt.pi (fun i => .vec (n i) (Peers.desc (R i)))` 的缩写。
abbrev commands := Fmt.pi (fun i => .vec (n i) (Peers.desc (R i)))
-- 读法：在后续公式中，`peers` 是 `Fmt.pi (fun i => Perm (S.count i))` 的缩写。
abbrev peers := Fmt.pi (fun i => Perm (S.count i))

-- 读法：输入 `i` 时返回 `Peers.decode (v i) (x i)`。
def readCommands (v : ∀ i, (R i).obj → B (S.count i)) (x : (S.commands n R).obj) : S.peers.obj :=
  fun i => Peers.decode (v i) (x i)

-- 读法：`commandsCost` 的取值由 `∑ i, 4 * (2 ^ Peers.height (n i) (S.count i) (R i) * (100 + Peers.width (n i) (S.count i) (R i)) ^ 111)` 给出。
def commandsCost := ∑ i, 4 * (2 ^ Peers.height (n i) (S.count i) (R i) *
  (100 + Peers.width (n i) (S.count i) (R i)) ^ 111)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(S.commands n R)` 到 `S.peers` 实现映射 `(S.readCommands n R v)` 的开销至多为 `(S.commandsCost n R)`。这里调用 `Map.family`。
theorem peer_commands {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}
    (v : ∀ i, (R i).obj → B (S.count i)) (hu : 3 ≤ u) :
    Map F u L (S.commands n R) S.peers (S.readCommands n R v) (S.commandsCost n R) := by
  apply Map.family
  intro i
  obtain ⟨m, hm, hcost⟩ := Peers.cheap_decode F (n i) (R i) (v i)
  exact (Map.circuit hu hm).mono (Nat.mul_le_mul_left _ (by omega))

-- 读法：`S.commandsCost n R` 不超过 `Fintype.card S.Levels * (4 * (2 ^ t * (101 + 4 * t) ^ 111))`。
theorem commands_bound {t : ℕ} (hn : ∀ i, n i ≤ t) (hr : ∀ i, (R i).width ≤ t)
    (hc : ∀ i, S.count i ≤ t) :
    S.commandsCost n R ≤ Fintype.card S.Levels * (4 * (2 ^ t * (101 + 4 * t) ^ 111)) := by
  unfold commandsCost
  rw [← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum fun i _ => ?_
  have hh : Peers.height (n i) (S.count i) (R i) ≤ t := max_le (hn i) (max_le (hc i) (hr i))
  have hw : 100 + Peers.width (n i) (S.count i) (R i) ≤ 101 + 4 * t := by
    have := hc i
    unfold Peers.width
    omega
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hh)
    (Nat.pow_le_pow_left hw _))

end Channels
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
对行数和查询数可以不同的数据并行执行间接读取。

**英文原文**

Parallel indirect reads with different numbers of rows and queries.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Peers
open Coloring Intervals

variable (F : Type) [Field F] {a b n t : ℕ}

-- 读法：`(Format.vec a R).width` 不超过 `2 ^ n * (100 + t) ^ 1`。
theorem bound_vec (R : Format) (hr : R.width ≤ t) (ha : a ≤ n) :
    (Format.vec a R).width ≤ 2 ^ n * (100 + t) ^ 1 :=
  (vec_bound a (hr.trans (Nat.le_add_left _ _))).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) ha))

-- 读法：映射 `(fun x => x ∘ f)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (t)) ^ (2)` 为上界。使用 `Cheap.project` 给出的结论。
theorem reindex (R : Format) (hr : R.width ≤ t) (ha : a ≤ n) (hb : b ≤ n) (f : B b → B a) :
    Cheap F n t (.vec a R) (.vec b R) (fun x => x ∘ f) 2 :=
  Cheap.project F (bound_vec R hr ha) (bound_vec R hr hb) (fun y => (f y.1, y.2)) (fun _ _ => rfl)

-- 读法：映射 `(fun u => u.1 ∘ u.2)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (t)) ^ (12)` 为上界。这里调用 `Nat.mul_le_mul_left`。
theorem read (R : Format) (hr : R.width ≤ t) (ha : a ≤ n) (hb : b ≤ n) (hn : n ≤ t) :
    Cheap F n t (.pair (.vec a R) (.vec b (.addr a))) (.vec b R) (fun u => u.1 ∘ u.2) 12 := by
  let A := Format.pair (.vec a R) (.vec b (.addr a))
  have hh : (Format.addr a).width ≤ t := by simpa using ha.trans hn
  have hw : A.width ≤ 2 ^ n * (100 + t) ^ 2 := by
    rw [show A.width = _ from Format.width_pair ..]
    refine (Nat.add_le_add (bound_vec R hr ha) (bound_vec _ hh hb)).trans ?_
    rw [← mul_add]
    exact Nat.mul_le_mul_left _ (by ring_nf; omega)
  have x := Cheap.id F hw
  have table := x.fst.comp (reindex F R hr ha le_rfl (shrink a))
  have idx := x.snd.comp (reindex F (.addr a) hh hb le_rfl (shrink b))
  -- 推导：记下中间结论 `resize`：`= Cheap.map (h`。
  have resize := Cheap.map (h := n) _ (fun _ => cheap_shrink F (ha.trans hn) hn)
  have fetch := (table.pair (idx.comp resize)).comp (Cheap.lookup F n t R hn hr)
  have out := fetch.comp (reindex F R hr le_rfl hb (extend hb))
  convert out.mono (d := 12) (by decide) using 1
  funext y i
  simp only [Function.comp_apply, id_eq, shrink_extend]
  have e (x : B a) : shrink n x = extend ha x :=
    Fin.ext (Nat.mod_eq_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) ha)))
  rw [e, shrink_extend]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Peers
end

/-!
# 在数据包缓冲区内放置逻辑片段

一个片段指定所属接触项、在该接触项上的偏移量、长度以及在存储区中的起始地址。组内的序号决定实际通道。

**英文原文**

Placing logical fragments in a packet buffer

A fragment specifies the contact, offset on the contact, length
and starting bank address. Group ranks determine the physical lane.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Fragments

open Coloring
variable {p w n t : ℕ}

-- 读法：在后续公式中，`Rank` 是 `Format.pair (.addr w) (.addr p)` 的缩写。
abbrev Rank (w p : ℕ) := Format.pair (.addr w) (.addr p)
-- 读法：在后续公式中，`Entry` 是 `Format.pair (.addr p) (Intervals.span w)` 的缩写。
abbrev Entry (w p : ℕ) := Format.pair (.addr p) (Intervals.span w)
-- 读法：在后续公式中，`Item` 是 `Format.pair (Rank w p) (Intervals.span w)` 的缩写。
abbrev Item (w p : ℕ) := Format.pair (Rank w p) (Intervals.span w)
-- 读法：在后续公式中，`Input` 是 `Format.pair (.vec p (.addr w)) (.vec n (Entry w p))` 的缩写。
abbrev Input (w p n : ℕ) := Format.pair (.vec p (.addr w)) (.vec n (Entry w p))

-- 读法：`items` 的取值由 `(PackRank.lanes x.1 (x.2 i).1, (x.2 i).2)` 给出。
def items (x : (Input w p n).obj) (i : B n) : (Item w p).obj :=
  (PackRank.lanes x.1 (x.2 i).1, (x.2 i).2)

-- 读法：`shift` 的取值由 `(fun y : B t => y + y)^[s] x` 给出。
private def shift (s : ℕ) (x : B t) := (fun y : B t => y + y)^[s] x

-- 读法：`(shift s x).val` 等于 `(2 ^ s * x.val) % 2 ^ t`。对 `s` 作归纳。
private theorem shift_val (s : ℕ) (x : B t) : (shift s x).val = (2 ^ s * x.val) % 2 ^ t := by
  induction s with
  | zero => simp [shift, Nat.mod_eq_of_lt x.isLt]
  | succ s ih =>
    rw [shift, Function.iterate_succ_apply', ← shift, Fin.val_add, ih, ← Nat.add_mod,
      pow_succ', mul_assoc, two_mul]

-- 读法：`adjust` 的结果类型为 `(Intervals.span t).obj`。
def adjust (s t : ℕ) (x : (Item w p).obj) : (Intervals.span t).obj :=
  (Intervals.shrink t x.2.1 + shift s (Intervals.shrink t x.1.2),
    if x.1.1.val = s then Intervals.shrink t x.2.2.1 else 0,
    Intervals.shrink t x.2.2.2)

-- 读法：`runs` 的取值由 `adjust s t ∘ items x` 给出。
def runs (s t : ℕ) (x : (Input w p n).obj) := adjust s t ∘ items x

-- 读法：结论为 `(adjust s t x).1.val = (x.2.1.val + 2 ^ s * x.1.2.val) % 2 ^ t ∧ (adjust s t x).2.1.val = (if x.1.1.val = s then x.2.2.1.val % 2 ^ t else 0) ∧ (adjust s t x).2.2.val = x.2.2.2.val % 2 ^ t`。
theorem adjust_val (s t : ℕ) (x : (Item w p).obj) :
    (adjust s t x).1.val = (x.2.1.val + 2 ^ s * x.1.2.val) % 2 ^ t ∧
    (adjust s t x).2.1.val = (if x.1.1.val = s then x.2.2.1.val % 2 ^ t else 0) ∧
    (adjust s t x).2.2.val = x.2.2.2.val % 2 ^ t := by
  simp only [adjust, Fin.val_add, shift_val, Intervals.shrink]
  constructor
  · simp only [Nat.mul_mod_mod, ← Nat.add_mod]
  · split <;> simp

variable (F : Type) [Field F] {b s : ℕ}

-- 读法：映射 `(shift s)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (b)) ^ (6)` 为上界。这里调用 `hd.iterate`。
private theorem cheap_shift (hs : s ≤ b) (ht : t ≤ b) :
    Cheap F 0 b (.addr t) (.addr t) (shift s) 6 := by
  have hi := Cheap.id F (show (Format.addr t).width ≤ 2 ^ 0 * (100 + b) ^ 1 by simp; omega)
  have hd := (hi.pair hi).comp (Intervals.cheap_add F ht)
  exact hd.iterate hs

-- 读法：映射 `(adjust s t)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (b)) ^ (24)` 为上界。
private theorem cheap_adjust (hs : s ≤ b) (hh : 4 * w + p + t ≤ b) :
    Cheap F 0 b (Item w p) (Intervals.span t) (adjust s t) 24 := by
  have hw : w ≤ b := by omega
  have ht : t ≤ b := by omega
  have hp : p ≤ b := by omega
  have h : (Item w p).width ≤ 2 ^ 0 * (100 + b) ^ 1 := by
    simp [Item, Rank, Intervals.span]; omega
  have h' : (Format.addr t).width ≤ 2 ^ 0 * (100 + b) ^ 1 := by simp; omega
  have x := Cheap.id F h
  have same : Cheap F 0 b (Item w p) .bit (fun x => decide (x.1.1.val = s)) 7 := by
    by_cases he : s < 2 ^ w
    · have k := Cheap.const F h (show (Format.addr w).width ≤ 2 ^ 0 * (100 + b) ^ 1 by simp; omega) ⟨s, he⟩
      have a := (x.fst.fst.pair k).comp (cheap_eq F hw)
      convert a.mono (d := 7) (by decide) using 1
      funext i
      simp [Fin.ext_iff]
    · have k := Cheap.const F h (show Format.bit.width ≤ 2 ^ 0 * (100 + b) ^ 1 by simp; omega) false
      convert k.mono (d := 7) (by decide) using 1
      funext i
      simp only [decide_eq_false_iff_not]
      have := i.1.1.isLt
      omega
  have resize := Intervals.cheap_shrink F hw ht
  have lane := (x.fst.snd.comp (Intervals.cheap_shrink F hp ht)).comp (cheap_shift F hs ht)
  have start := ((x.snd.fst.comp resize).pair lane).comp (Intervals.cheap_add F ht)
  have len := (x.snd.snd.fst.comp resize).pair (Cheap.const F h h' 0)
  have size := (len.pair same).comp ((cheap_select F t).widen ht)
  have z := start.pair (size.pair (x.snd.snd.snd.comp resize))
  convert z.mono (d := 24) (by decide) using 1
  funext i
  simp only [adjust, Function.comp_apply, id_eq, decide_eq_true_eq]

-- 读法：映射 `(runs s t)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((max p n)) * (100 + (b)) ^ (118)` 为上界。
theorem cheap (s t : ℕ) (hs : s ≤ b) (hb : n + 4 * w + 2 * p + t + 1 ≤ b) :
    Cheap F (max p n) b (Input w p n) (.vec n (Intervals.span t)) (runs s t) 118 := by
  have hr : (Rank w p).width ≤ b := by simp [Rank]; omega
  have he : (Entry w p).width ≤ b := by simp [Entry, Intervals.span]; omega
  have hv : (Intervals.span w).width ≤ b := by simp [Intervals.span]; omega
  have ha : (Input w p n).width ≤ 2 ^ max p n * (100 + b) ^ 2 := by
    rw [Format.width_pair]
    refine (Nat.add_le_add (Peers.bound_vec (t := b) (.addr w) (by simp; omega) (le_max_left p n))
      (Peers.bound_vec _ he (le_max_right p n))).trans ?_
    rw [← mul_add]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have x := Cheap.id F ha
  -- 推导：记下中间结论 `rank`：`= Peers.lift F ((PackRank.cheap_lanes F p w).widen (l`。
  have rank := Peers.lift F ((PackRank.cheap_lanes F p w).widen (l := b) (by omega)) (le_max_left p n)
  have u := Cheap.id F (show (Entry w p).width ≤ 2 ^ 0 * (100 + b) ^ 1 by simp only [pow_zero, pow_one, one_mul]; omega)
  have key := Peers.lift F (Cheap.map (h := n) _ (fun _ => u.fst)) (le_max_right p n)
  have cost := Peers.lift F (Cheap.map (h := n) _ (fun _ => u.snd)) (le_max_right p n)
  have v := ((x.fst.comp rank).pair (x.snd.comp key)).comp
    (Peers.read F (Rank w p) hr (le_max_left p n) (le_max_right p n) (by omega))
  have get := (v.pair (x.snd.comp cost)).comp (Peers.zipper F n (le_max_right p n) _ _ (by nlinarith))
  have conv := Cheap.map (h := n) _ (fun _ => cheap_adjust (w := w) (p := p) (t := t) F hs (by omega))
  exact (get.comp (Peers.lift F conv (le_max_right p n))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Fragments
end

/-!
将一条通道的局部序号换算为其全局数据包地址。

**英文原文**

Translating a lane's local ordinal into its global packet address.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank.Links

open Coloring
variable {A D : Format} {P : Bank A D} {k d h p w : ℕ} (L : P.Links k d)
    (i : P.Level k d) (host : P.Slot ↪ B h) (hd : d ≤ 2 ^ p)

-- 读法：`descriptor` 的取值由 `(true, P.codePort i host hd (L.location i e), P.codePort i host hd (L.location i (L.opposite i e)))` 给出。
def descriptor (e : L.At i × Bool) : (Peers.desc (pairCode h p)).obj :=
  (true, P.codePort i host hd (L.location i e), P.codePort i host hd (L.location i (L.opposite i e)))

-- 读法：`Peers.indexRow (P.portTable i host hd) (L.descriptor i host hd e)` 等于 `L.peerRow i e`。这里调用 `Prod.ext`。
theorem index_descriptor (e : L.At i × Bool) :
    Peers.indexRow (P.portTable i host hd) (L.descriptor i host hd e) = L.peerRow i e := by
  exact Prod.ext rfl (Prod.ext (P.portTable_at i host hd _) (P.portTable_at i host hd _))

-- 读法：`P.codePort i host hd (L.location i e)` 等于 `(host (L.place (e.1.val, e.2)).1, (PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).2)`。使用 `Prod.ext` 给出的结论。
theorem codePort_of_fits (e : L.At i × Bool) (x : B p → B w)
    (he : L.FitsLengths (L.site i e).val hd x) :
    P.codePort i host hd (L.location i e) =
      (host (L.place (e.1.val, e.2)).1, (PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).2) :=
  Prod.ext rfl (Fin.ext (L.lanes_correct i e he).2.symm)

-- 读法：`Peers.decode (P.portTable i host hd) x` 等于 `L.plan.control.2.1 i`。这里调用 `L.peers_correct`。
theorem decoded {t : ℕ} (x : B t → (Peers.desc (pairCode h p)).obj)
    (ok : ∀ j, (x j).1 = true → ∃ a, x j = L.descriptor i host hd a)
    (cover : ∀ a, ∃ j, x j = L.descriptor i host hd a) :
    Peers.decode (P.portTable i host hd) x = L.plan.control.2.1 i := by
  apply L.peers_correct
  · intro j h
    obtain ⟨a, ha⟩ := ok j h
    exact ⟨a, by rw [Function.comp_apply, ha, index_descriptor]⟩
  · intro a
    obtain ⟨j, hj⟩ := cover a
    exact ⟨j, by rw [Function.comp_apply, hj, index_descriptor]⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank.Links
end

/-!
# 一组受控传输的统一规模上界

**英文原文**

Uniform size allowance for a bank of controlled transfers
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical
variable {A D : Format}

-- 读法：`S.control.width` 等于 `(∑ i, 2 ^ S.localWidth i * S.localWidth i) + (∑ i, 2 ^ S.count i * S.count i) + D.width`。
theorem Channels.width (S : Channels A D) :
    S.control.width = (∑ i, 2 ^ S.localWidth i * S.localWidth i) +
      (∑ i, 2 ^ S.count i * S.count i) + D.width := by
  simp only [Channels.control, Format.width_pair, Fmt.width_pi, Format.width_vec, Format.width_addr,
    add_assoc]

-- 读法：`S.cost v m` 不超过 `20000 * T * (1 + A.width + D.width + (∑ i, 2 ^ S.localWidth i) + (∑ i, 2 ^ S.count i * v i))`。这里调用 `Nat.mul_le_mul_right`。
private theorem Channels.budget (S : Channels A D) {T : ℕ} (hT : 0 < T)
    (v m : S.Levels → ℕ) (hi : ∀ i, (101 + S.localWidth i) ^ 8 ≤ T)
    (hv : ∀ i, S.count i + 1 ≤ v i) (hm : ∀ i, m i ≤ T * (2 ^ (S.count i) * v i)) :
    S.cost v m ≤ 20000 * T * (1 + A.width + D.width + (∑ i, 2 ^ S.localWidth i) + (∑ i, 2 ^ S.count i * v i)) := by
  let X := ∑ i, 2 ^ S.localWidth i
  let Y := ∑ i, 2 ^ S.count i * v i
  have hl : (∑ i, Channels.localCost (S.localWidth i)) ≤ T * X := by
    unfold X
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Channels.localCost, show 100 + (S.localWidth i + 1) = 101 + S.localWidth i by omega, mul_comm]
    exact Nat.mul_le_mul_right _ (hi i)
  -- 推导：记下中间结论 `hg`：`(∑ i, Channels.globalCost (m i) (S.count i) (v i)) ≤ 201 * T * Y`。
  have hg : (∑ i, Channels.globalCost (m i) (S.count i) (v i)) ≤ 201 * T * Y := by
    unfold Y
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold Channels.globalCost
    have hb := Nat.mul_le_mul_left (2 ^ S.count i) (hv i)
    have hh := Nat.le_mul_of_pos_left (2 ^ S.count i * v i) hT
    linarith only [hm i, hb, hh]
  have hw : S.control.width ≤ T * X + Y + D.width := by
    rw [S.width, show T * X = ∑ i, T * 2 ^ S.localWidth i from Finset.mul_sum ..]
    refine Nat.add_le_add_right (Nat.add_le_add ?_ ?_) _
    · apply Finset.sum_le_sum
      intro i _
      rw [mul_comm]
      apply Nat.mul_le_mul_right
      exact le_trans (by omega : S.localWidth i ≤ 101 + S.localWidth i)
        ((Nat.le_pow (by decide)).trans (hi i))
    · exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (le_trans (by omega) (hv i))
  unfold cost
  rw [Format.width_pair]
  change 8 * (S.control.width + A.width + D.width + X + 1) + 36 * (16 + _ + _ + 32 * D.width) + 4 * D.width ≤
    20000 * T * (1 + A.width + D.width + X + Y)
  have ht (n : ℕ) : n ≤ T * n := Nat.le_mul_of_pos_left n hT
  linarith only [hw, hl, hg, ht A.width, ht D.width, ht X, ht Y, hT, Nat.zero_le X, Nat.zero_le Y,
    Nat.zero_le A.width, Nat.zero_le D.width]

namespace Bank

-- 读法：结论为 `let S := P.channels k d Kernel F u L (S.control.pair A) D (S.kernel F) (20000 * T * (1 + A.width + D.width + (k + 1) * (10 * P.capacity + 4 * d * Fintype.card P.Slot * v)))`。这里调用 `le_trans`。
/-- 分别计算宽有效载荷的成本和分配给每个参与宿主的预算。`v` 是全局置换的宽度阈值。

英文原文：Separate the cost of wide payloads from the allowance per
participating host. `v` is the threshold width for global permutations.
-/
theorem realize {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} (P : Bank A D) (k d n T v : ℕ)
    (hu : 3 ≤ u) (hk : ∀ i, P.depth i ≤ k) (hn : d * Fintype.card P.Slot < 2 ^ n)
    (hT : (102 + k) ^ 8 ≤ T) (hv : n + 1 ≤ v)
    (ht : ∀ j w, 1 ≤ j → j ≤ n → v ≤ w → ∃ s ≤ T * (2 ^ j * w), Radix.Tag F j w s) :
    let S := P.channels k d
    Kernel F u L (S.control.pair A) D (S.kernel F)
      (20000 * T * (1 + A.width + D.width + (k + 1) * (10 * P.capacity + 4 * d * Fintype.card P.Slot * v))) := by
  intro S
  let w := fun i : P.Level k d => 2 ^ i.1.val + v
  choose m hm ht using fun i => ht (P.count k d i) (w i) (P.count_range k d hn i).1
    (P.count_range k d hn i).2 (Nat.le_add_left v _)
  -- 推导：记下中间结论 `hb`：`= S.realize F (L`。
  have hb := S.realize F (L := L) hu w m (fun _ => Nat.le_add_right _ _) ht
  refine hb.mono (le_trans (Channels.budget S (lt_of_lt_of_le (by positivity) hT) w m ?_ ?_ hm) ?_)
  · intro i
    apply le_trans _ hT
    apply Nat.pow_le_pow_left
    change 101 + (P.depth i.2.val + 1) ≤ 102 + k
    have := hk i.2.val
    omega
  · intro i
    exact ((Nat.add_le_add_right (P.count_range k d hn i).2 1).trans hv).trans (Nat.le_add_left _ _)
  apply Nat.mul_le_mul_left
  change 1 + A.width + D.width + (∑ i, 2 ^ P.localWidth k d i) +
    (∑ i, 2 ^ P.count k d i * (2 ^ i.1.val + v)) ≤ _
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  linarith only [P.local_volume k d, P.packet_volume k d, Nat.mul_le_mul_right v (P.packet_count k d)]

end Bank
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 在每个宿主上实现有界个数的有效载荷接触

**英文原文**

Realizing a bounded number of payload contacts per host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Transcript
open scoped Classical

-- 读法：用字段 `Slot`、`depth` 构造 `Bank (Fmt.payload m V k) (Fmt.payload m' V' k')`。
def payloadBank (m V k m' V' k' : ℕ) : Bank (Fmt.payload m V k) (Fmt.payload m' V' k') where
  Slot := Slot (2 ^ m) V k ⊕ Slot (2 ^ m') V' k'
  depth := Sum.elim (fun s => s.1.val) (fun s => s.1.val)
  atBit
    | .inl s, i => .inl ⟨s, i⟩
    | .inr s, i => .inr ⟨s, i⟩

variable {m V k m' V' k' d : ℕ} {x : Payload m V k} {y : Payload m' V' k'}

namespace Payload

-- 读法：结构的字段包括 `E`、`src`、`dst`、`length`、`send`。
/-- 在每个接触项中，两端位置按同一传输次序列出。每个比特至多属于一个接触项。

英文原文：Within a contact, positions at each end are listed in common
transmission order. Each bit belongs to at most one contact.
-/
structure Traffic (x : Payload m V k) (y : Payload m' V' k') (d : ℕ) where
  E : Type
  src : E ↪ B m × Fin d
  dst : E ↪ B m' × Fin d
  length : E → ℕ
  send : ∀ i, Fin (length i) ↪ Fin (x.length (src i).1)
  get : ∀ i, Fin (length i) ↪ Fin (y.length (dst i).1)
  disjoint_send : ∀ e e' i j, (src e).1 = (src e').1 →
    (send e i).val = (send e' j).val → e = e' ∧ i.val = j.val
  disjoint_get : ∀ e e' i j, (dst e).1 = (dst e').1 →
    (get e i).val = (get e' j).val → e = e' ∧ i.val = j.val
  covers : ∀ j : y.Bit, ∃ e t, (⟨(dst e).1, get e t⟩ : y.Bit) = j

namespace Traffic
variable (p : Traffic x y d)

-- 读法：`source` 的取值由 `⟨(p.src e).1, p.send e i⟩` 给出。
def source (e : p.E) (i : Fin (p.length e)) : x.Bit := ⟨(p.src e).1, p.send e i⟩
-- 读法：`target` 的取值由 `⟨(p.dst e).1, p.get e i⟩` 给出。
def target (e : p.E) (i : Fin (p.length e)) : y.Bit := ⟨(p.dst e).1, p.get e i⟩

-- 读法：用字段 `inj'` 构造 `p.E × Bool ↪ (payloadBank m V k m' V' k').Slot × Fin d`。
private def place : p.E × Bool ↪ (payloadBank m V k m' V' k').Slot × Fin d where
  toFun
    | (e, false) => (.inl (x.seat.write (p.src e).1), (p.src e).2)
    | (e, true) => (.inr (y.seat.write (p.dst e).1), (p.dst e).2)
  inj' := by
    rintro ⟨a, _ | _⟩ ⟨b, _ | _⟩ h
    · have he := x.seat.injective (Sum.inl.inj (Prod.mk.inj h).1)
      exact Prod.ext (p.src.injective (Prod.ext he (Prod.mk.inj h).2)) rfl
    · cases (Prod.mk.inj h).1
    · cases (Prod.mk.inj h).1
    · have he := y.seat.injective (Sum.inr.inj (Prod.mk.inj h).1)
      exact Prod.ext (p.dst.injective (Prod.ext he (Prod.mk.inj h).2)) rfl

-- 读法：用字段 `E`、`place`、`length`、`pointer` 构造 `(payloadBank m V k m' V' k').Links (max k k') d`。
def links : (payloadBank m V k m' V' k').Links (max k k') d where
  E := p.E
  place := p.place
  length := p.length
  pointer e b i := match b with
    | false => (p.send e i).castLE (x.fits _)
    | true => (p.get e i).castLE (y.fits _)
  small e b := by
    cases b
    · have he : p.length e ≤ x.length (p.src e).1 := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (p.send e)
      exact he.trans (x.fits _)
    · have he : p.length e ≤ y.length (p.dst e).1 := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (p.get e)
      exact he.trans (y.fits _)
  bounded e b := by
    cases b
    · exact (Nat.lt_succ_iff.mp (x.seat.write (p.src e).1).1.isLt).trans (le_max_left _ _)
    · exact (Nat.lt_succ_iff.mp (y.seat.write (p.dst e).1).1.isLt).trans (le_max_right _ _)
  distinct := by
    rintro ⟨e, _ | _⟩ ⟨e', _ | _⟩ i j hs ht
    · obtain ⟨he, hj⟩ := p.disjoint_send _ _ i j (x.seat.injective (Sum.inl.inj hs)) ht
      exact ⟨congrArg (fun z => (z, false)) he, hj⟩
    · cases hs
    · cases hs
    · obtain ⟨he, hj⟩ := p.disjoint_get _ _ i j (y.seat.injective (Sum.inr.inj hs)) ht
      exact ⟨congrArg (fun z => (z, true)) he, hj⟩
  pad i := decide (i ∉ Set.range y.wire)

-- 读法：`p.links.Matches (x.store a) b` 与 `b = y.store (a ∘ f)` 等价。
theorem matches_iff (f : y.Bit → x.Bit) (h : ∀ e t, f (p.target e t) = p.source e t)
    (a : x.Bit → Bool) (b : (Fmt.payload m' V' k').obj) :
    p.links.Matches (x.store a) b ↔ b = y.store (a ∘ f) := by
  have he : p.links.Matches (x.store a) b ↔
      (∀ i ∉ Set.range y.wire, b i = false) ∧
      ∀ e i, x.store a (x.wire (p.source e i)) = b (y.wire (p.target e i)) := by
    unfold Bank.Links.Matches
    simp only [show ∀ i, p.links.pad i = true ↔ i ∉ Set.range y.wire from
      fun _ => decide_eq_true_iff]
    rfl
  rw [he]
  constructor
  · rintro ⟨hp, hb⟩
    refine y.store_unique _ _ ?_ hp
    intro i
    -- 推导：从 `p.covers i` 中取出 `e, t, ht`。
    obtain ⟨e, t, ht⟩ := p.covers i
    change p.target e t = i at ht
    rw [← ht, ← hb, read_store, Function.comp_apply, h]
  · rintro rfl
    exact ⟨y.padding _, fun e t => by rw [read_store, read_store, Function.comp_apply, h]⟩

-- 读法：结论为 `((payloadBank m V k m' V' k').channels (max k k') d).kernel F (p.links.plan.control, x.store a) b = if b = y.store (a ∘ f) then 1 else 0`。
theorem kernel (F : Type) [Field F] (f : y.Bit → x.Bit)
    (h : ∀ e t, f (p.target e t) = p.source e t)
    (a : x.Bit → Bool) (b : (Fmt.payload m' V' k').obj) :
    ((payloadBank m V k m' V' k').channels (max k k') d).kernel F (p.links.plan.control, x.store a) b =
      if b = y.store (a ∘ f) then 1 else 0 := by
  simp only [Channels.kernel, p.links.carries, p.matches_iff f h]

end Traffic
end Payload
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 按目的偏移量排列接触项

给定从各接触项到目的地的分配，用其相对序号为数据包编制索引。同一数据包的源列表恰好采用此次序。不同接触项所占的源位置互不重叠，所占的目的位置也互不重叠。

**英文原文**

Ordering a contact by destination offset

Given an assignment of destinations to contacts, use their relative
ranks to index packets. The source list for the same packet uses
exactly this order. Source and destination positions do not overlap between contacts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

namespace Payload
variable {m V k m' V' k' d : ℕ} {x : Payload m V k} {y : Payload m' V' k'}

-- 读法：结构的字段包括 `E`、`src`、`dst`、`edge`、`from_host`。
/-- 在每个宿主上，为每个接触项配置一条信道。

英文原文：One channel per contact at each host.
-/
structure Contacts (f : y.Bit → x.Bit) (d : ℕ) where
  E : Type
  src : E ↪ B m × Fin d
  dst : E ↪ B m' × Fin d
  edge : y.Bit → E
  from_host : ∀ i, (f i).1 = (src (edge i)).1
  to_host : ∀ i, i.1 = (dst (edge i)).1
  no_repeat : Function.Injective f

namespace Contacts
variable {f : y.Bit → x.Bit} (M : Contacts f d)

-- 读法：在后续公式中，`Fiber` 是 `{i : Fin (y.length (M.dst e).1) // M.edge ⟨(M.dst e).1, i⟩ = e}` 的缩写。
abbrev Fiber (e : M.E) :=
  {i : Fin (y.length (M.dst e).1) // M.edge ⟨(M.dst e).1, i⟩ = e}

-- 读法：`ordinal` 的取值由 `Fintype.orderIsoFinOfCardEq _ rfl` 给出。
def ordinal (e : M.E) : Fin (Fintype.card (M.Fiber e)) ≃o M.Fiber e :=
  Fintype.orderIsoFinOfCardEq _ rfl

-- 读法：`receive` 的取值由 `(M.ordinal e).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)` 给出。
def receive (e : M.E) : Fin (Fintype.card (M.Fiber e)) ↪ Fin (y.length (M.dst e).1) :=
  (M.ordinal e).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

-- 读法：`atDest` 的取值由 `⟨(M.dst e).1, M.receive e t⟩` 给出。
def atDest (e : M.E) (t : Fin (Fintype.card (M.Fiber e))) : y.Bit :=
  ⟨(M.dst e).1, M.receive e t⟩

-- 读法：`M.edge (M.atDest e t)` 等于 `e`。使用 `M.ordinal` 给出的结论。
theorem edge_at (e : M.E) (t : Fin (Fintype.card (M.Fiber e))) :
    M.edge (M.atDest e t) = e := (M.ordinal e t).2

-- 读法：`(f (M.atDest e t)).1` 等于 `(M.src e).1`。
theorem source_at (e : M.E) (t : Fin (Fintype.card (M.Fiber e))) :
    (f (M.atDest e t)).1 = (M.src e).1 := by rw [M.from_host, M.edge_at]

-- 读法：`atSource` 的取值由 `(f (M.atDest e t)).2.cast (congrArg x.length (M.source_at e t))` 给出。
private def atSource (e : M.E) (t : Fin (Fintype.card (M.Fiber e))) :
    Fin (x.length (M.src e).1) :=
  (f (M.atDest e t)).2.cast (congrArg x.length (M.source_at e t))

-- 读法：`f (M.atDest e t)` 等于 `⟨(M.src e).1, M.atSource e t⟩`。按 `Sigma.ext` 的外延性准则比较各分量。
private theorem source_eq (e : M.E) (t : Fin (Fintype.card (M.Fiber e))) :
    f (M.atDest e t) = ⟨(M.src e).1, M.atSource e t⟩ := by
  refine Sigma.ext (M.source_at e t) ?_
  exact (Fin.heq_ext_iff (congrArg x.length (M.source_at e t))).mpr rfl

-- 读法：用字段 `toFun`、`inj'`、`have` 构造 `Fin (Fintype.card (M.Fiber e)) ↪ Fin (x.length (M.src e).1)`。
def send (e : M.E) : Fin (Fintype.card (M.Fiber e)) ↪ Fin (x.length (M.src e).1) where
  toFun := M.atSource e
  inj' i j h := by
    have he : f (M.atDest e i) = f (M.atDest e j) := by rw [M.source_eq, M.source_eq, h]
    have hi := M.no_repeat he
    exact (M.receive e).injective (eq_of_heq (Sigma.mk.inj hi).2)

-- 读法：`e = z` 与 `i.val = j.val` 同时成立。
private theorem dest_eq {e z : M.E} {i : Fin (Fintype.card (M.Fiber e))}
    {j : Fin (Fintype.card (M.Fiber z))} (h : M.atDest e i = M.atDest z j) :
    e = z ∧ i.val = j.val := by
  have hh := congrArg M.edge h
  rw [M.edge_at, M.edge_at] at hh
  subst z
  exact ⟨rfl, congrArg Fin.val ((M.receive e).injective (eq_of_heq (Sigma.mk.inj h).2))⟩

-- 读法：用字段 `E`、`src`、`dst`、`length` 构造 `Traffic x y d`。
def traffic : Traffic x y d where
  E := M.E
  src := M.src
  dst := M.dst
  length e := Fintype.card (M.Fiber e)
  send := M.send
  get := M.receive
  disjoint_send e z i j hs ht := by
    apply M.dest_eq
    apply M.no_repeat
    rw [M.source_eq, M.source_eq]
    exact Sigma.ext hs ((Fin.heq_ext_iff (congrArg x.length hs)).mpr ht)
  disjoint_get e z i j hs ht := by
    apply M.dest_eq
    exact Sigma.ext hs ((Fin.heq_ext_iff (congrArg y.length hs)).mpr ht)
  covers j := by
    generalize he : M.edge j = e
    have hh := M.to_host j
    rw [he] at hh
    obtain ⟨a, b⟩ := j
    change a = (M.dst e).1 at hh
    subst a
    obtain ⟨i, hi⟩ := (M.ordinal e).surjective ⟨b, he⟩
    exact ⟨e, i, congrArg (fun u : M.Fiber e => (⟨(M.dst e).1, u.val⟩ : y.Bit)) hi⟩

-- 读法：`f (M.traffic.target e t)` 等于 `M.traffic.source e t`。使用 `M.source_eq` 给出的结论。
theorem consistent (e : M.traffic.E) (t : Fin (M.traffic.length e)) :
    f (M.traffic.target e t) = M.traffic.source e t := M.source_eq _ _

end Contacts
end Payload

namespace Scheme
variable {F : Type} (S S' : Scheme F) {r : S.format.obj} {r' : S'.format.obj} {V k V' k' d : ℕ}
  (h : S.Fits r V k) (h' : S'.Fits r' V' k') (f : S'.exposed r' → S.exposed r)

-- 读法：`transfer` 的取值由 `S.index r h ∘ f ∘ (S'.index r' h').symm` 给出。
def transfer := S.index r h ∘ f ∘ (S'.index r' h').symm

-- 读法：用函数外延性比较等号两侧在 `i` 处的取值。
theorem transfer_kernel [Field F] (M : Payload.Contacts (S.transfer S' h h' f) d)
    (a : S.exposed r → Bool) (b : (Fmt.payload S'.m V' k').obj) :
    ((payloadBank S.m V k S'.m V' k').channels (max k k') d).kernel F
      (M.traffic.links.plan.control, S.store r h a) b = if b = S'.store r' h' (a ∘ f) then 1 else 0 := by
  unfold store
  rw [M.traffic.kernel F _ M.consistent]
  have he : (a ∘ (S.index r h).symm) ∘ S.transfer S' h h' f = (a ∘ f) ∘ (S'.index r' h').symm := by
    funext i
    simp [transfer]
  rw [he]

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 逻辑端点地址

一个地址包含侧别、宿主的二进层级、在该层级内的序号以及接触项在其数据包层级内的序号。由同一个正向对端索引生成该接触项的两个方向。

**英文原文**

Logical endpoint addresses

An address contains the side, dyadic host level, ordinal in that
level and ordinal of the contact at its packet level. Both directions
of a contact are generated from a single forward peer index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
open Coloring
open scoped Classical

variable {m m' V V' k k' d p w : ℕ}

-- 读法：在后续公式中，`lengths` 是 `Format.pair (.vec m (.addr w)) (.vec m (.vec p (.addr w)))` 的缩写。
abbrev lengths (m p w : ℕ) := Format.pair (.vec m (.addr w)) (.vec m (.vec p (.addr w)))
-- 读法：在后续公式中，`input` 是 `Format.pair (.pair (lengths m p w) (lengths m' p w)) (.vec (m + p) (.addr (m' + p)))` 的缩写。
abbrev input (m m' p w : ℕ) := Format.pair (.pair (lengths m p w) (lengths m' p w))
  (.vec (m + p) (.addr (m' + p)))

-- 读法：在后续公式中，`hostFmt` 是 `Format.pair .bit (.pair (.addr b) (.addr a))` 的缩写。
abbrev hostFmt (a b : ℕ) := Format.pair .bit (.pair (.addr b) (.addr a))
-- 读法：在后续公式中，`keyFmt` 是 `Bank.pairCode (hostFmt a b).width p` 的缩写。
abbrev keyFmt (a b p : ℕ) := Bank.pairCode (hostFmt a b).width p
-- 读法：在后续公式中，`bits` 是 `Nat.clog 2 (max k k' + 1)` 的缩写。
abbrev bits (k k' : ℕ) := Nat.clog 2 (max k k' + 1)

-- 读法：`hostCode` 的取值由 `(hostFmt a b).serial (side, Intervals.shrink b v.1, Intervals.shrink a v.2)` 给出。
def hostCode (a b : ℕ) (side : Bool) (v : B w × B m) : B (hostFmt a b).width :=
  (hostFmt a b).serial (side, Intervals.shrink b v.1, Intervals.shrink a v.2)

-- 读法：`address` 的取值由 `let h := Match.rowIndex m p i (hostCode a b side (PackRank.assign x.1 h.1), (PackRank.lanes (x.2 h.1) h.2).2)` 给出。
def address (a b : ℕ) (side : Bool) (x : (lengths m p w).obj) (i : B (m + p)) :
    (keyFmt a b p).obj :=
  let h := Match.rowIndex m p i
  (hostCode a b side (PackRank.assign x.1 h.1), (PackRank.lanes (x.2 h.1) h.2).2)

-- 读法：`enabled` 的取值由 `decide (0 < v.val ∧ Nat.clog 2 v.val = l)` 给出。
def enabled (l : ℕ) (v : B w) := decide (0 < v.val ∧ Nat.clog 2 v.val = l)

-- 读法：`active` 的取值由 `enabled l (x.2 (Match.rowIndex m p i).1 (Match.rowIndex m p i).2)` 给出。
def active (l : ℕ) (x : (lengths m p w).obj) (i : B (m + p)) :=
  enabled l (x.2 (Match.rowIndex m p i).1 (Match.rowIndex m p i).2)

-- 读法：`rows` 的结果类型为 `(Peers.desc (keyFmt a b p)).obj`。
def rows (a b l : ℕ) (x : (input m m' p w).obj) (j : B (m + p + 1)) :
    (Peers.desc (keyFmt a b p)).obj :=
  let i := Match.rowIndex (m + p) 1 j
  let L := address a b false x.1.1 i.1
  let R := address a b true x.1.2 (x.2 i.1)
  (active l x.1.1 i.1, if i.2 = 0 then (L, R) else (R, L))

-- 读法：`slotCode` 的取值由 `(hostFmt a b).serial (side, Fin.ofNat (2 ^ b) u.1.val, Fin.ofNat (2 ^ a) u.2.val)` 给出。
def slotCode (a b : ℕ) (side : Bool) (u : Transcript.Slot (2 ^ m) V k) : B (hostFmt a b).width :=
  (hostFmt a b).serial (side, Fin.ofNat (2 ^ b) u.1.val, Fin.ofNat (2 ^ a) u.2.val)

-- 读法：`(slotCode (m := m) (V := V) (k := k) a b side)` 是单射。按 `Fin.ext` 的外延性准则比较各分量。
private theorem slotCode_inj (a b : ℕ) (side : Bool) (hm : m ≤ a) (hk : k < 2 ^ b) :
    Function.Injective (slotCode (m := m) (V := V) (k := k) a b side) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ he
  have h := (Prod.mk.inj ((hostFmt a b).serial.injective he)).2
  have hi : i.val < 2 ^ b := (Nat.le_of_lt_succ i.isLt).trans_lt hk
  have hj : j.val < 2 ^ b := (Nat.le_of_lt_succ j.isLt).trans_lt hk
  have hij : i = j := by
    apply Fin.ext
    have hv := congrArg (fun z => z.1.val) h
    change i.val % 2 ^ b = j.val % 2 ^ b at hv
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  subst j
  -- 推导：记下中间结论 `hr`：`Transcript.seats (2 ^ m) V i.val ≤ 2 ^ a`。
  have hr : Transcript.seats (2 ^ m) V i.val ≤ 2 ^ a :=
    (min_le_left _ _).trans (Nat.pow_le_pow_right (by decide) hm)
  have hst : s = t := by
    apply Fin.ext
    have hv := congrArg (fun z => z.2.val) h
    change s.val % 2 ^ a = t.val % 2 ^ a at hv
    rwa [Nat.mod_eq_of_lt (s.isLt.trans_le hr), Nat.mod_eq_of_lt (t.isLt.trans_le hr)] at hv
  rw [hst]

-- 读法：用字段 `toFun`、`inj'` 构造 `(payloadBank m V k m' V' k').Slot ↪ B (hostFmt (max m m') (bits k k')).width`。
def host (m V k m' V' k' : ℕ) :
    (payloadBank m V k m' V' k').Slot ↪ B (hostFmt (max m m') (bits k k')).width where
  toFun := Sum.elim (slotCode _ _ false) (slotCode _ _ true)
  inj' := by
    have h : max k k' < 2 ^ bits k k' := Nat.le_pow_clog (by decide : 1 < 2) (max k k' + 1)
    rintro (s|s) (t|t) he
    · exact congrArg Sum.inl (slotCode_inj _ _ _ (le_max_left _ _) ((le_max_left _ _).trans_lt h) he)
    · exact Bool.false_ne_true (Prod.mk.inj ((hostFmt _ _).serial.injective he)).1 |>.elim
    · exact Bool.false_ne_true (Prod.mk.inj ((hostFmt _ _).serial.injective he.symm)).1 |>.elim
    · exact congrArg Sum.inr (slotCode_inj _ _ _ (le_max_right _ _) ((le_max_right _ _).trans_lt h) he)

-- 读法：`hostCode a b side (PackRank.assign x i)` 等于 `slotCode a b side (v.seat.write i)`。
theorem assigned_slot (a b : ℕ) (side : Bool) (v : Payload m V k) (x : B m → B w)
    (h : ∀ i, (x i).val = v.length i) (i : B m) :
    hostCode a b side (PackRank.assign x i) = slotCode a b side (v.seat.write i) := by
  obtain ⟨h₁, h₂⟩ := PackRank.correct v x h i
  unfold hostCode slotCode
  exact congrArg _ (Prod.ext rfl (Prod.ext (Fin.ext (congrArg (· % 2 ^ b) h₁)) (Fin.ext (congrArg (· % 2 ^ a) h₂))))

-- 读法：`post` 的取值由 `(Match.rowIndex m p).symm (e.1, e.2.castLE hd)` 给出。
def post (hd : d ≤ 2 ^ p) (e : B m × Fin d) := (Match.rowIndex m p).symm (e.1, e.2.castLE hd)

variable {x : Payload m V k} {y : Payload m' V' k'} (L : Payload.Traffic x y d) (hd : d ≤ 2 ^ p)

-- 读法：结构的字段包括 `from_size`、`to_size`、`send`、`receive`、`all_send`。
structure Fits (v : (input m m' p w).obj) : Prop where
  from_size : ∀ i, (v.1.1.1 i).val = x.length i
  to_size : ∀ i, (v.1.2.1 i).val = y.length i
  send : ∀ e, (v.1.1.2 (L.src e).1 ((L.src e).2.castLE hd)).val = L.length e
  receive : ∀ e, (v.1.2.2 (L.dst e).1 ((L.dst e).2.castLE hd)).val = L.length e
  all_send : ∀ i j, 0 < (v.1.1.2 i j).val → ∃ e, (L.src e).1 = i ∧ (L.src e).2.castLE hd = j
  all_receive : ∀ i j, 0 < (v.1.2.2 i j).val → ∃ e, (L.dst e).1 = i ∧ (L.dst e).2.castLE hd = j
  peer : ∀ e, 0 < L.length e → v.2 (post hd (L.src e)) = post hd (L.dst e)

-- 读法：在后续公式中，`P` 是 `payloadBank m V k m' V' k'` 的缩写。
abbrev P (m V k m' V' k' : ℕ) := payloadBank m V k m' V' k'
-- 读法：在后续公式中，`S` 是 `(P m V k m' V' k').channels (max k k') d` 的缩写。
abbrev S (m V k m' V' k' d : ℕ) := (P m V k m' V' k').channels (max k k') d

-- 读法：输入 `i` 时返回 `Peers.decode ((P m V k m' V' k').portTable i (host _ _ _ _ _ _) hd) (rows (max m m') (bits k k') i.1.val v)`。
def control (hd : d ≤ 2 ^ p) (v : (input m m' p w).obj) : (S m V k m' V' k' d).peers.obj :=
  fun i => Peers.decode ((P m V k m' V' k').portTable i (host _ _ _ _ _ _) hd)
    (rows (max m m') (bits k k') i.1.val v)

end OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
end

/-!
并行处理每个宿主和接触项的局部地址与活跃标志。

**英文原文**

Local addresses and activity flags in parallel at every host and contact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout

open Coloring
variable (F : Type) [Field F] {p m w a b t : ℕ}

-- 读法：映射 `(hostCode a b side)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (10)` 为上界。
private theorem cheap_host (side : Bool) (ht : m + w + a + b + 1 ≤ t) :
    Cheap F 0 t (.pair (.addr w) (.addr m)) (.addr (hostFmt a b).width)
      (hostCode a b side) 10 := by
  let X := Format.pair (.addr w) (.addr m)
  have hw : X.width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp [X]; omega
  have x := Cheap.id F hw
  have first := x.fst.comp (Intervals.cheap_shrink F (show w ≤ t by omega) (show b ≤ t by omega))
  have second := x.snd.comp (Intervals.cheap_shrink F (show m ≤ t by omega) (show a ≤ t by omega))
  have flag := Cheap.const F hw (show Format.bit.width ≤ 2 ^ 0 * (100 + t) ^ 1 by simp; omega) side
  let V := hostFmt a b
  -- 推导：记下中间结论 `hV`：`V.width ≤ t`。
  have hV : V.width ≤ t := by simp [V, hostFmt]; omega
  have hserial : Cheap F 0 t V (.addr V.width) V.serial 5 := by
    have hi : V.width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
    have hj : (Format.addr V.width).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
    have input := Cheap.project F hi (Intervals.vec_bound 0 (show V.width ≤ 100 + t by omega))
      (f := fun (x : V.obj) (_ : B 0) => x) (fun i => i.2) (fun _ _ => rfl)
    have output := Cheap.project F (A := Column 0 V.width) (D := .addr V.width) (column_width 0 hV) hj (f := fun x => x 0)
      (fun i => (0, i)) (fun _ _ => rfl)
    exact ((input.comp (cheap_keys V F 0 hV)).comp output).mono (by decide)
  exact ((flag.pair (first.pair second)).comp hserial).mono (by decide)

-- 读法：映射 `(enabled l)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (24)` 为上界。按 `l < 2 ^ w` 成立与否分情况。
private theorem cheap_enabled (l : ℕ) (hw : w ≤ t) :
    Cheap F 0 t (.addr w) .bit (enabled l) 24 := by
  have ha : (Format.addr w).width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
  have hc : Format.bit.width ≤ 2 ^ 0 * (100 + t) ^ 1 := by simp; omega
  by_cases h : l < 2 ^ w
  · let c : B w := ⟨l, h⟩
    have hp := ((Cheap.const F ha ha 0).pair (Cheap.id F ha)).comp (Intervals.cheap_compare F hw)
    have he := (((PackRank.cheap_code F w).widen hw).pair (Cheap.const F ha ha c)).comp (cheap_eq F hw)
    have hand : Cheap F 0 t (.pair .bit .bit) .bit (fun z => z.1 && z.2) 2 := by
      refine ⟨_, small (by simp) _, ?_⟩
      simp; ring_nf; omega
    convert ((hp.pair he).comp hand).mono (d := 24) (by decide) using 1
    funext x
    simp [enabled, c, PackRank.code, Fin.ext_iff]
  · convert (Cheap.const F ha hc false).mono (d := 24) (by decide) using 1
    funext x
    have he : Nat.clog 2 x.val ≠ l := ne_of_lt ((PackRank.code x).isLt.trans_le (le_of_not_gt h))
    simp [enabled, he]

-- 读法：`(lengths m p w).width` 不超过 `2 ^ (m + p) * (100 + t) ^ 2`。这里调用 `Nat.mul_le_mul_left`。
theorem lengths_bound (h : w ≤ t) : (lengths m p w).width ≤ 2 ^ (m + p) * (100 + t) ^ 2 := by
  simp only [lengths, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, pow_add, mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ 2 ^ p * (w + w) := by rw [mul_add]; exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by positivity)) _
    _ ≤ 2 ^ p * (100 + t) ^ 2 := Nat.mul_le_mul_left _ (by ring_nf; omega)

-- 读法：映射 `(active l)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((m + p)) * (100 + (t)) ^ (28)` 为上界。这里调用 `Nat.mul_le_mul_left`。
theorem cheap_active (l : ℕ) (h : w ≤ t) :
    Cheap F (m + p) t (lengths m p w) (.vec (m + p) .bit) (active l) 28 := by
  have ha := lengths_bound (m := m) (p := p) h
  have hw : (Column (m + p) w).width ≤ 2 ^ (m + p) * (100 + t) ^ 2 := by
    simp only [Column, Format.width_vec, Format.width_addr]
    exact Nat.mul_le_mul_left _ (by ring_nf; omega)
  have get := Cheap.project F (A := lengths m p w) (D := Column (m + p) w) ha hw
    (f := fun x i => x.2 (Match.rowIndex m p i).1 (Match.rowIndex m p i).2)
    (fun z => .inr ((Match.rowIndex m p z.1).1, (Match.rowIndex m p z.1).2, z.2)) (fun _ _ => rfl)
  exact (get.comp (Cheap.map _ (fun _ : B (m + p) => cheap_enabled F l h))).mono (by decide)

-- 读法：映射 `(address a b side)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((m + p)) * (100 + (t)) ^ (120)` 为上界。
theorem cheap_address (side : Bool) (ht : m + p + w + a + b + 1 ≤ t) :
    Cheap F (m + p) t (lengths m p w) (.vec (m + p) (keyFmt a b p)) (address a b side) 120 := by
  have x := Cheap.id F (lengths_bound (m := m) (p := p) (show w ≤ t by omega))
  have name := ((PackRank.cheap F m w).widen (show m + w ≤ t by omega)).comp
    (Cheap.map _ (fun _ : B m => cheap_host F side (show m + w + a + b + 1 ≤ t by omega)))
  have host := x.fst.comp (Peers.lift F name (by omega : m ≤ m + p))
  have hw : (hostFmt a b).width ≤ t := by simp [hostFmt]; omega
  have ha : (Column m (hostFmt a b).width).width ≤ 2 ^ (m + p) * (100 + t) ^ 1 :=
    (column_width _ hw).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega)))
  have spread := Cheap.project F (A := Column m (hostFmt a b).width) (D := Column (m + p) (hostFmt a b).width) ha (column_width (m + p) hw)
    (f := fun x i => x (Match.rowIndex m p i).1) (fun z => ((Match.rowIndex m p z.1).1, z.2))
    (fun _ _ => rfl)
  let K := Format.vec m (.vec p (.pair (.addr w) (.addr p)))
  -- 推导：记下中间结论 `ranks`：`Cheap F (m + p) t (.vec m (.vec p (.addr w))) K (fun x i => PackRank.lanes (x i)) 110`。
  have ranks : Cheap F (m + p) t (.vec m (.vec p (.addr w))) K (fun x i => PackRank.lanes (x i)) 110 := by
    obtain ⟨l, hl, hb⟩ := (PackRank.cheap_lanes F p w).widen (show p + w ≤ t by omega)
    refine ⟨_, Circuit.map (A := .vec p (.addr w)) (D := .vec p (.pair (.addr w) (.addr p))) (fun _ : B m => PackRank.lanes) (fun _ => hl), ?_⟩
    simpa only [K, Format.width_vec, ← mul_add, pow_add, mul_assoc] using Nat.mul_le_mul_left (2 ^ m) hb
  have hK : K.width ≤ 2 ^ (m + p) * (100 + t) ^ 1 := by
    simp only [K, Format.width_vec, Format.width_pair, Format.width_addr, ← mul_assoc, ← pow_add, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have lane := Cheap.project F (A := K) (D := Column (m + p) p) hK (column_width (m + p) (show p ≤ t by omega))
    (f := fun x i => (x (Match.rowIndex m p i).1 (Match.rowIndex m p i).2).2)
    (fun z => ((Match.rowIndex m p z.1).1, (Match.rowIndex m p z.1).2, .inr z.2)) (fun _ _ => rfl)
  exact ((host.comp spread).pair ((x.snd.comp ranks).comp lane)).zip.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
end
