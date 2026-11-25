-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Fragments
import OAI.LinearAlgebra.MatrixExponent.Assembly.RetagStore
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes

/-!
# 槽位中的逻辑片段及其打包坐标

**英文原文**

Logical fragments at a slot and their packed coordinates
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical

variable {A D : Format} (P : Bank A D) {k d p w n : ℕ}

-- 读法：在后续公式中，`records` 是 `Fmt.pi (fun _ : P.Slot => Fragments.Input w p n)` 的缩写。
abbrev records (w p n : ℕ) := Fmt.pi (fun _ : P.Slot => Fragments.Input w p n)

-- 读法：输入 `i` 时返回 `Fragments.runs i.1.1.val (P.localWidth k d i) (x i.2.val)`。
def distribute (x : (P.records w p n).obj) : (P.intervals k d (fun _ => n)).obj :=
  fun i => Fragments.runs i.1.1.val (P.localWidth k d i) (x i.2.val)

namespace Links
variable {P} (L : P.Links k d) (hd : d ≤ 2 ^ p) (x : (P.records w p n).obj)

-- 读法：`portName` 的取值由 `(L.place e).2.castLE hd` 给出。
def portName (e : L.E × Bool) : B p := (L.place e).2.castLE hd

-- 读法：结构的字段包括 `lengths`、`inside`、`apart`、`live`。
/-- 所有长度和偏移量均相对于各自宿主。不相交性与覆盖性条件针对的是逻辑数据包的偏移位置。

英文原文：All lengths and offsets are local to a host. The disjointness
and coverage conditions concern logical packet offsets.
-/
structure Pieces : Prop where
  lengths : ∀ s, L.FitsLengths s hd (x s).1
  inside : ∀ s i, let a := (x s).2 i
    a.2.1.val + a.2.2.1.val ≤ ((x s).1 a.1).val
  apart : ∀ s i j t, ((x s).2 i).1 = ((x s).2 j).1 →
    Intervals.covers ((x s).2 i).2 t → Intervals.covers ((x s).2 j).2 t → j = i
  live : ∀ (e : L.E × Bool) (t : Fin (L.length e.1)), let s := (L.place e).1
    ∃ i, ((x s).2 i).1 = L.portName hd e ∧ Intervals.covers ((x s).2 i).2 t.val ∧
      ((x s).2 i).2.2.2.val + (t.val - ((x s).2 i).2.1.val) = (L.pointer e.1 e.2 t).val

-- 读法：`base` 的取值由 `2 ^ i.1.val * (L.location i e).2.val` 给出。
def base (i : P.Level k d) (e : L.At i × Bool) := 2 ^ i.1.val * (L.location i e).2.val

-- 读法：在后续公式中，`pair` 是 `(e.1.val, e.2)` 的缩写。
abbrev pair {i : P.Level k d} (e : L.At i × Bool) : L.E × Bool := (e.1.val, e.2)

-- 读法：`assigned` 表示以下条件：`L.site i.1 e = i.2` 与 `((x i.2.val).2 a).1 = L.portName hd (L.pair e)` 同时成立。
def assigned (i : P.Endpoint k d) (a : B n) (e : L.At i.1 × Bool) : Prop :=
  L.site i.1 e = i.2 ∧ ((x i.2.val).2 a).1 = L.portName hd (L.pair e)

variable {L hd x} (h : L.Pieces hd x)

-- 读法：`L.base i e + L.length e.1.val` 严格小于 `2 ^ (P.depth (L.site i e).val + 1)`。这里调用 `lt_of_le_of_lt`。
theorem end_lt (L : P.Links k d) (i : P.Level k d) (e : L.At i × Bool) :
    L.base i e + L.length e.1.val < 2 ^ (P.depth (L.site i e).val + 1) := by
  have hb := L.lane_end i e
  have he : L.depth e.1.val = i.1.val := congrArg (fun i : P.Level k d => i.1.val) e.1.2.1
  have hf := L.fits e.1.val
  rw [he] at hf
  simp only [mul_add, mul_one] at hb
  exact lt_of_le_of_lt (Nat.add_le_add_left hf _) hb

include h in
-- 读法：`((x i.2.val).2 a).2.1.val + ((x i.2.val).2 a).2.2.1.val` 不超过 `L.length e.1.val`。这里调用 `hb.trans_eq`。
theorem Pieces.bound {i : P.Endpoint k d} {a : B n} {e : L.At i.1 × Bool}
    (he : L.assigned hd x i a e) :
    ((x i.2.val).2 a).2.1.val + ((x i.2.val).2 a).2.2.1.val ≤ L.length e.1.val := by
  have hu : (L.place (L.pair e)).1 = i.2.val := congrArg Subtype.val he.1
  have hv := (h.lengths _).1 _ hu
  have hb := h.inside i.2.val a
  change _ ≤ ((x i.2.val).1 ((x i.2.val).2 a).1).val at hb
  rw [he.2] at hb
  exact hb.trans_eq hv

include h in
-- 读法：结论为 `let v := P.distribute x i a let u := ((x i.2.val).2 a).2 v.1.val = u.1.val + L.base i.1 e ∧ v.2.1.val = u.2.1.val ∧ v.2.2.val = u.2.2.val % 2 ^ P.localWidth k d i`。
theorem Pieces.shifted {i : P.Endpoint k d} {a : B n} {e : L.At i.1 × Bool}
    (he : L.assigned hd x i a e) :
    let v := P.distribute x i a
    let u := ((x i.2.val).2 a).2
    v.1.val = u.1.val + L.base i.1 e ∧ v.2.1.val = u.2.1.val ∧
      v.2.2.val = u.2.2.val % 2 ^ P.localWidth k d i := by
  have hr := L.lanes_correct i.1 e (he.1.symm ▸ h.lengths i.2.val)
  rw [he.1] at hr
  have hend := L.end_lt i.1 e
  rw [he.1] at hend
  have hb := h.bound he
  change _ < 2 ^ P.localWidth k d i at hend
  -- 推导：记下中间结论 `h₁`：`((x i.2.val).2 a).2.1.val + L.base i.1 e < 2 ^ P.localWidth k d i`。
  have h₁ : ((x i.2.val).2 a).2.1.val + L.base i.1 e < 2 ^ P.localWidth k d i := by omega
  have h₂ : ((x i.2.val).2 a).2.2.1.val < 2 ^ P.localWidth k d i := by omega
  have hv := Fragments.adjust_val i.1.1.val (P.localWidth k d i) (Fragments.items (x i.2.val) a)
  have eq : (Fragments.items (x i.2.val) a).1 = PackRank.lanes (x i.2.val).1 (L.portName hd (L.pair e)) :=
    congrArg (PackRank.lanes (x i.2.val).1) he.2
  rw [eq] at hv
  simp only [portName, pair, hr.1, hr.2, ite_true] at hv
  exact ⟨hv.1.trans (Nat.mod_eq_of_lt h₁), hv.2.1.trans (Nat.mod_eq_of_lt h₂), hv.2.2⟩

include h in
-- 读法：存在 `e`，要证明的命题是 `L.assigned hd x i a e`。
theorem Pieces.active (i : P.Endpoint k d) (a : B n) (hu : 0 < (P.distribute x i a).2.1.val) :
    ∃ e, L.assigned hd x i a e := by
  let u := (x i.2.val).2 a
  have hv := (Fragments.adjust_val i.1.1.val (P.localWidth k d i) (Fragments.items (x i.2.val) a)).2.1
  change (P.distribute x i a).2.1.val =
    if Nat.clog 2 ((x i.2.val).1 u.1).val = i.1.1.val then u.2.2.1.val % _ else 0 at hv
  split at hv
  swap
  · omega
  rename_i hl
  -- 推导：记下中间结论 `hp`：`0 < ((x i.2.val).1 u.1).val`。
  have hp : 0 < ((x i.2.val).1 u.1).val := by
    have he : u.2.1.val + u.2.2.1.val ≤ ((x i.2.val).1 u.1).val := h.inside _ _
    have hm := Nat.mod_le u.2.2.1.val (2 ^ P.localWidth k d i)
    omega
  obtain ⟨⟨e, b⟩, hs, ha⟩ := (h.lengths _).2 u.1 hp
  have hi := (h.lengths _).1 (e, b) hs
  rw [ha] at hi
  have he : L.level e = i.1 := by
    apply Subtype.ext
    apply Fin.ext
    change Nat.clog 2 (L.length e) = _
    rwa [hi] at hl
  exact ⟨(⟨e, he, hi ▸ hp⟩, b), Subtype.ext hs, ha.symm⟩

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-!
# 由逻辑数据包片段执行局部汇集检查

**英文原文**

The local gather checks from logical packet fragments
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank.Links

open Coloring
open scoped Classical

variable {A D : Format} {P : Bank A D} {k d p w n : ℕ}
  {L : P.Links k d} {hd : d ≤ 2 ^ p} {x : (P.records w p n).obj} (h : L.Pieces hd x)

-- 读法：`interval` 的取值由 `L.base i e ≤ t ∧ t < L.base i e + 2 ^ i.1.val` 给出。
private def interval (L : P.Links k d) {i : P.Level k d} (e : L.At i × Bool) (t : ℕ) :=
  L.base i e ≤ t ∧ t < L.base i e + 2 ^ i.1.val

-- 读法：`a` 等于 `b`。
private theorem lane_eq {q : ℕ} {i : P.Level k d} {a b : L.At i × Bool}
    (hs : L.site i a = L.site i b) (ha : L.interval a q) (hb : L.interval b q) : a = b := by
  have hf : (L.location i a).1 = (L.location i b).1 := hs
  have ht : (L.location i a).2.val = (L.location i b).2.val := by
    unfold interval base at ha hb
    rcases lt_trichotomy (L.location i a).2.val (L.location i b).2.val with h | h | h
    · have := Nat.mul_le_mul_left (2 ^ i.1.val) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ i.1.val) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
  exact (L.location i).injective (Sigma.ext hf ((Fin.heq_ext_iff (congrArg (P.lanes d _) hf)).mpr ht))

include h in
-- 读法：存在 `e : L.At i.1 × Bool`，`L.assigned hd x i a e` 与 `L.interval e t ∧ Intervals.covers ((x i.2.val).2 a).2 (t - L.base i.1 e)` 同时成立。这里调用 `L.fits`。
private theorem Pieces.logical (i : P.Endpoint k d) (a : B n) (t : ℕ)
    (hc : Intervals.covers (P.distribute x i a) t) :
    ∃ e : L.At i.1 × Bool, L.assigned hd x i a e ∧ L.interval e t ∧
      Intervals.covers ((x i.2.val).2 a).2 (t - L.base i.1 e) := by
  unfold Intervals.covers at hc
  obtain ⟨e, he⟩ := h.active i a (by omega)
  obtain ⟨h₁, h₂, _⟩ := h.shifted he
  rw [h₁, h₂] at hc
  have hlen : L.length e.1.val ≤ 2 ^ i.1.1.val := by
    have he : L.depth e.1.val = i.1.1.val := congrArg (fun j : P.Level k d => j.1.val) e.1.2.1
    rw [← he]
    exact L.fits _
  have hb := h.bound he
  refine ⟨e, he, ?_, ?_⟩
  · unfold interval; omega
  · unfold Intervals.covers; omega

include h in
-- 读法：要证明的命题是 `L.Runs (fun _ => n) (P.distribute x)`。
theorem Pieces.runs : L.Runs (fun _ => n) (P.distribute x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a
    cases (Nat.zero_le (P.distribute x i a).2.1.val).eq_or_lt with
    | inl hz => rw [← hz, add_zero]; exact (P.distribute x i a).1.isLt
    | inr hp =>
      obtain ⟨e, he⟩ := h.active _ _ hp
      obtain ⟨h₁, h₂, _⟩ := h.shifted he
      rw [h₁, h₂]
      have hlen := L.end_lt i.1 e
      rw [he.1] at hlen
      have hb := h.bound he
      change _ < 2 ^ (P.depth i.2.val + 1)
      omega
  · intro i a b t ha hb
    -- 推导：从 `h.logical _ _ _ ha` 中取出 `e, h₁, h₂, h₃`。
    obtain ⟨e, h₁, h₂, h₃⟩ := h.logical _ _ _ ha
    obtain ⟨f, h₄, h₅, h₆⟩ := h.logical _ _ _ hb
    have := lane_eq (h₁.1.trans h₄.1.symm) h₂ h₅
    subst f
    exact h.apart _ _ _ _ (h₁.2.trans h₄.2.symm) h₃ h₆
  · intro i e b hb
    let t := L.vector i e
    have he : (L.place (L.pair e)).1 = t.2.val := rfl
    obtain ⟨a, h₁, h₂, h₃⟩ := h.live (L.pair e) ⟨b.val, hb⟩
    have ha : L.assigned hd x t a e := ⟨rfl, h₁⟩
    -- 推导：从 `h.shifted ha` 中取出 `hs, hl, hpos`。
    obtain ⟨hs, hl, hpos⟩ := h.shifted ha
    have ht : (L.offset i e b).val = b.val + L.base i e := L.offset_val _ _ _
    change Intervals.covers ((x t.2.val).2 a).2 b.val at h₂
    change ((x t.2.val).2 a).2.2.2.val + (b.val - ((x t.2.val).2 a).2.1.val) =
      (L.pointer e.1.val e.2 ⟨b.val, hb⟩).val at h₃
    change _ = _ + L.base i e at hs
    have hbnd : (L.pointer e.1.val e.2 ⟨b.val, hb⟩).val < 2 ^ P.localWidth k d t :=
      (L.pointer _ _ _).isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    rw [Nat.mod_eq_of_lt (show ((x t.2.val).2 a).2.2.2.val < 2 ^ P.localWidth k d t by omega)] at hpos
    refine ⟨a, ?_, ?_⟩
    · change Intervals.covers (P.distribute x t a) _
      unfold Intervals.covers at h₂ ⊢
      rw [hs, hl, ht]
      omega
    · change (P.distribute x t a).2.2.val + (_ - (P.distribute x t a).1.val) = _
      rw [hpos, ht, hs, Nat.add_sub_add_right]
      exact h₃
  · intro i e b hb v hcov
    -- 推导：从 `h.logical _ _ _ hcov` 中取出 `a, h₁, h₂, h₃`。
    obtain ⟨a, h₁, h₂, h₃⟩ := h.logical _ _ _ hcov
    have ht : (L.offset i e b).val = b.val + L.base i e := L.offset_val _ _ _
    have he : L.interval e (L.offset i e b).val := by
      unfold interval
      have := b.isLt
      omega
    have eq : a = e := lane_eq h₁.1 h₂ he
    subst a
    have hu := h.bound h₁
    unfold Intervals.covers at h₃
    change _ ∧ (L.offset i e b).val - L.base i e < _ at h₃
    change _ ≤ L.length e.1.val at hu
    omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank.Links
end

/-!
# 在每个符合条件的层级构造简短的区间描述

**英文原文**

Forming short interval descriptions at every eligible level
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical
variable {A D : Format} (P : Bank A D) (k d w p n : ℕ)

-- 读法：在后续公式中，`copies` 是 `Fmt.pi (fun _ : P.Endpoint k d => Fragments.Input w p n)` 的缩写。
abbrev copies := Fmt.pi (fun _ : P.Endpoint k d => Fragments.Input w p n)
-- 读法：`distributionCost` 的构造用到 `P.records`、`P.copies`、`Fintype.card`。
def distributionCost :=
  4 * ((P.records w p n).width + 2 * (P.copies k d w p n).width) +
    Fintype.card (P.Endpoint k d) * (4 * (2 ^ max p n * (100 + (n + 4 * w + 2 * p + k + 2)) ^ 118))

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(P.records w p n)` 到 `(P.intervals k d (fun _ => n))` 实现映射 `P.distribute` 的开销至多为 `(P.distributionCost k d w p n)`。
theorem distribute_net {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}
    (hu : 3 ≤ u) (hk : ∀ i, P.depth i ≤ k) :
    Map F u L (P.records w p n) (P.intervals k d (fun _ => n))
      P.distribute (P.distributionCost k d w p n) := by
  let X := P.records w p n
  let Y := P.copies k d w p n
  let f := fun (x : X.obj) (i : P.Endpoint k d) => x i.2.val
  have hc : Circuit F X Y f (X.width + 2 * Y.width) :=
    Circuit.project (fun v => ⟨v.1.2.val, v.2⟩) fun _ _ => rfl
  let b := n + 4 * w + 2 * p + k + 2
  have hd (i : P.Endpoint k d) : Map F u L (Fragments.Input w p n) (.vec n (Intervals.span (P.localWidth k d i)))
      (Fragments.runs i.1.1.val (P.localWidth k d i)) (4 * (2 ^ max p n * (100 + b) ^ 118)) := by
    -- 推导：从 `Fragments.cheap F (p := p) (n := n) (w := w) (b := b) i.1.1.val` 中取出 `s, hs, ht`。
    obtain ⟨s, hs, ht⟩ := Fragments.cheap F (p := p) (n := n) (w := w) (b := b) i.1.1.val
      (P.localWidth k d i) (by unfold b; have := i.1.1.isLt; omega)
      (by unfold b localWidth; have := hk i.2.val; omega)
    exact (Map.circuit hu hs).mono (by omega)
  have he := ((Map.circuit (L := L) hu hc).comp (Map.family hd))
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at he
  exact he

end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-!
逻辑宿主布局产生的指令与实际传输方案一致。

**英文原文**

The commands generated by the logical host layout agree with the physical plan.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
open Coloring
open scoped Classical

variable {m m' V V' k k' d p w : ℕ} {x : Payload m V k} {y : Payload m' V' k'}
  {L : Payload.Traffic x y d} {hd : d ≤ 2 ^ p} {v : (input m m' p w).obj}

local notation "bank" => P m V k m' V' k'
local notation "H" => host m V k m' V' k'
local notation "n" => max m m'
local notation "b" => bits k k'

-- 读法：要证明的命题是 `L.links.FitsLengths (.inl (x.seat.write a)) hd (v.1.1.2 a)`。这里调用 `h.send`。
theorem Fits.left (h : Fits L hd v) (a : B m) :
    L.links.FitsLengths (.inl (x.seat.write a)) hd (v.1.1.2 a) := by
  constructor
  · rintro ⟨e, _ | _⟩ he
    · have ha := x.seat.injective (Sum.inl.inj he)
      change (L.src e).1 = a at ha
      subst a
      exact h.send e
    · exact (Sum.inr_ne_inl he).elim
  · intro j hj
    obtain ⟨e, he, he'⟩ := h.all_send a j hj
    exact ⟨(e, false), congrArg (fun a => Sum.inl (x.seat.write a)) he, he'⟩

-- 读法：要证明的命题是 `L.links.FitsLengths (.inr (y.seat.write a)) hd (v.1.2.2 a)`。这里调用 `Sum.inl_ne_inr`。
theorem Fits.right (h : Fits L hd v) (a : B m') :
    L.links.FitsLengths (.inr (y.seat.write a)) hd (v.1.2.2 a) := by
  constructor
  · rintro ⟨e, _ | _⟩ he
    · exact (Sum.inl_ne_inr he).elim
    · have ha := y.seat.injective (Sum.inr.inj he)
      change (L.dst e).1 = a at ha
      subst a
      exact h.receive e
  · intro j hj
    obtain ⟨e, he, he'⟩ := h.all_receive a j hj
    exact ⟨(e, true), congrArg (fun a => Sum.inr (y.seat.write a)) he, he'⟩

variable (i : (P m V k m' V' k').Level (max k k') d)

-- 读法：`address n b false v.1.1 (post hd (L.src e.val))` 等于 `(bank).codePort i H hd (L.links.location i (e, false))`。
theorem Fits.source (h : Fits L hd v) (e : L.links.At i) :
    address n b false v.1.1 (post hd (L.src e.val)) =
      (bank).codePort i H hd (L.links.location i (e, false)) := by
  rw [L.links.codePort_of_fits i H hd (e, false) _ (h.left (L.src e.val).1)]
  simp only [address, post, Equiv.apply_symm_apply, assigned_slot _ _ _ _ _ h.from_size]
  rfl

-- 读法：`address n b true v.1.2 (post hd (L.dst e.val))` 等于 `(bank).codePort i H hd (L.links.location i (e, true))`。
theorem Fits.destination (h : Fits L hd v) (e : L.links.At i) :
    address n b true v.1.2 (post hd (L.dst e.val)) =
      (bank).codePort i H hd (L.links.location i (e, true)) := by
  rw [L.links.codePort_of_fits i H hd (e, true) _ (h.right (L.dst e.val).1)]
  simp only [address, post, Equiv.apply_symm_apply, assigned_slot _ _ _ _ _ h.to_size]
  rfl

-- 读法：`PeerLayout.active i.1.val v.1.1 a = true` 与 `∃ e : L.links.At i, post hd (L.src e.val) = a` 等价。
theorem Fits.active (h : Fits L hd v) (a : B (m + p)) :
    PeerLayout.active i.1.val v.1.1 a = true ↔ ∃ e : L.links.At i, post hd (L.src e.val) = a := by
  simp only [PeerLayout.active, enabled, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, he⟩
    obtain ⟨e, he₁, he₂⟩ := h.all_send _ _ hp
    have eq : post hd (L.src e) = a := (Match.rowIndex m p).symm_apply_eq.mpr (Prod.ext he₁ he₂)
    rw [← he₁, ← he₂, h.send] at hp he
    exact ⟨⟨e, Subtype.ext (Fin.ext he), hp⟩, eq⟩
  · rintro ⟨e, rfl⟩
    simp only [post, Equiv.apply_symm_apply]
    rw [h.send e.val]
    exact ⟨e.2.2, congrArg (fun i : (bank).Level (max k k') d => i.1.val) e.2.1⟩

-- 读法：`rows n b i.1.val v ((Match.rowIndex (m + p) 1).symm (post hd (L.src e.val), z))` 等于 `L.links.descriptor i H hd (e, decide (z ≠ 0))`。按 `z = 0 <;> simp [hz, Bank.Links.descriptor, Bank.Links.opposite]` 成立与否分情况。
private theorem Fits.rows_at (h : Fits L hd v) (e : L.links.At i) (z : B 1) :
    rows n b i.1.val v ((Match.rowIndex (m + p) 1).symm (post hd (L.src e.val), z)) =
      L.links.descriptor i H hd (e, decide (z ≠ 0)) := by
  have ha := (h.active i _).mpr ⟨e, rfl⟩
  simp only [rows, Equiv.apply_symm_apply, ha, h.peer e.val e.2.2, h.source i e, h.destination i e]
  by_cases hz : z = 0 <;> simp [hz, Bank.Links.descriptor, Bank.Links.opposite]

-- 读法：`control hd v` 等于 `L.links.plan.control.2.1`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem Fits.correct (h : Fits L hd v) : control hd v = L.links.plan.control.2.1 := by
  funext i
  apply L.links.decoded
  · intro j hj
    let u := Match.rowIndex (m + p) 1 j
    obtain ⟨e, he⟩ := (h.active i u.1).mp hj
    have eq : (Match.rowIndex (m + p) 1).symm (post hd (L.src e.val), u.2) = j :=
      (Match.rowIndex (m + p) 1).symm_apply_eq.mpr (Prod.ext he rfl)
    exact ⟨(e, decide (u.2 ≠ 0)), eq ▸ h.rows_at i e u.2⟩
  · rintro ⟨e, _|_⟩
    · exact ⟨_, h.rows_at i e 0⟩
    · exact ⟨_, h.rows_at i e 1⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
end

/-!
# 打包来自逻辑宿主的传输元数据

每条记录与所属宿主的范围信息一同传送。空的物理槽位收到零长度与空片段。打包后原对端网格仍完整可用。

**英文原文**

Packing transfer metadata from logical hosts

Each record travels with its host's extent. Empty physical slots
receive zero lengths and empty fragments. The original peer grid
is available unchanged after packing.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload
open Coloring Transcript

-- 读法：`Script` 的构造用到 `Format.pair`、`PeerLayout.input`、`Fragments.Entry`。
abbrev Script (m m' p w n : ℕ) :=
  Format.pair (PeerLayout.input m m' p w)
    (.pair (.vec m (.vec n (Fragments.Entry w p))) (.vec m' (.vec n (Fragments.Entry w p))))

namespace Script
variable {m V k m' V' k' d p w n : ℕ}

-- 读法：在后续公式中，`item` 是 `Format.pair (Fragments.Input w p n) (.addr w)` 的缩写。
abbrev item (w p n : ℕ) := Format.pair (Fragments.Input w p n) (.addr w)
-- 读法：在后续公式中，`Out` 是 `Format.pair ((payloadBank m V k m' V' k').records w p n) (.pair (PeerLayout.input m m' p w) (Lengths m' V' k'))` 的缩写。
abbrev Out (m V k m' V' k' p w n : ℕ) :=
  Format.pair ((payloadBank m V k m' V' k').records w p n)
    (.pair (PeerLayout.input m m' p w) (Lengths m' V' k'))

-- 读法：`empty` 的取值由 `(fun _ => 0, fun _ => (0, 0, 0, 0))` 给出。
def empty (w p n : ℕ) : (Fragments.Input w p n).obj :=
  (fun _ => 0, fun _ => (0, 0, 0, 0))

-- 读法：`pad` 的取值由 `(empty w p n, 0)` 给出。
def pad (w p n : ℕ) : (item w p n).obj := (empty w p n, 0)

-- 读法：`left` 的取值由 `(v.1.1.1.1, fun i => ((v.1.1.1.2 i, v.2.1 i), v.1.1.1.1 i))` 给出。
def left (v : (Script m m' p w n).obj) : (Redistribute.input m w (item w p n)).obj :=
  (v.1.1.1.1, fun i => ((v.1.1.1.2 i, v.2.1 i), v.1.1.1.1 i))

-- 读法：`right` 的取值由 `(v.1.1.2.1, fun i => ((v.1.1.2.2 i, v.2.2 i), v.1.1.2.1 i))` 给出。
def right (v : (Script m m' p w n).obj) : (Redistribute.input m' w (item w p n)).obj :=
  (v.1.1.2.1, fun i => ((v.1.1.2.2 i, v.2.2 i), v.1.1.2.1 i))

-- 读法：`pack` 的结果类型为 `(Out m V k m' V' k' p w n).obj`。
def pack (v : (Script m m' p w n).obj) : (Out m V k m' V' k' p w n).obj :=
  let l := Redistribute.eval (V := V) (k := k) _ (pad w p n) (left v)
  let r := Redistribute.eval (V := V') (k := k') _ (pad w p n) (right v)
  (Sum.elim (fun i => (l i).1) (fun i => (r i).1), v.1, fun i => Intervals.shrink (k' + 1) (r i).2)

variable {x : Payload m V k} {y : Payload m' V' k'} {M : Traffic x y d}
    {hd : d ≤ 2 ^ p} {v : (Script m m' p w n).obj} (h : PeerLayout.Fits M hd v.1)

local notation "packed" => pack (V := V) (k := k) (V' := V') (k' := k') v

include h

-- 读法：`(packed).1 (.inl (x.seat.write i))` 等于 `(v.1.1.1.2 i, v.2.1 i)`。
theorem source (i : B m) : (packed).1 (.inl (x.seat.write i)) = (v.1.1.1.2 i, v.2.1 i) := by
  have he := congrFun (Redistribute.correct x _ (pad w p n) (left v) h.from_size) (x.seat.write i)
  rw [(x.seat.valid _ _).mpr rfl] at he
  exact congrArg Prod.fst he

-- 读法：`(packed).1 (.inr (y.seat.write i))` 等于 `(v.1.1.2.2 i, v.2.2 i)`。
theorem destination (i : B m') : (packed).1 (.inr (y.seat.write i)) = (v.1.1.2.2 i, v.2.2 i) := by
  have he := congrFun (Redistribute.correct y _ (pad w p n) (right v) h.to_size) (y.seat.write i)
  rw [(y.seat.valid _ _).mpr rfl] at he
  exact congrArg Prod.fst he

-- 读法：`(packed).1 (.inl s)` 等于 `empty w p n`。
theorem empty_source (s : Slot (2 ^ m) V k) (hs : x.seat.read s = none) :
    (packed).1 (.inl s) = empty w p n := by
  have he := congrFun (Redistribute.correct x _ (pad w p n) (left v) h.from_size) s
  rw [hs] at he
  exact congrArg Prod.fst he

-- 读法：`(packed).1 (.inr s)` 等于 `empty w p n`。
theorem empty_destination (s : Slot (2 ^ m') V' k') (hs : y.seat.read s = none) :
    (packed).1 (.inr s) = empty w p n := by
  have he := congrFun (Redistribute.correct y _ (pad w p n) (right v) h.to_size) s
  rw [hs] at he
  exact congrArg Prod.fst he

-- 读法：`(packed).2.2` 等于 `y.lengths`。用函数外延性比较等号两侧在 `s` 处的取值。
theorem lengths : (packed).2.2 = y.lengths := by
  funext s
  have he := congrFun (Redistribute.correct y _ (pad w p n) (right v) h.to_size) s
  apply Fin.ext
  change (Redistribute.eval _ (pad w p n) (right v) s).2.val % 2 ^ (k' + 1) = y.used s
  rw [he, used]
  cases hr : y.seat.read s with
  | none => simp [pad]
  | some i =>
    change (v.1.1.2.1 i).val % 2 ^ (k' + 1) = y.length i
    rw [h.to_size, Nat.mod_eq_of_lt ((y.longest i).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)))]

-- 读法：要证明的命题是 `M.links.FitsLengths s hd ((packed).1 s).1`。
theorem fits (s : (payloadBank m V k m' V' k').Slot) :
    M.links.FitsLengths s hd ((packed).1 s).1 := by
  have absent (s : (payloadBank m V k m' V' k').Slot)
      (ha : ∀ a, (M.links.place a).1 ≠ s) : M.links.FitsLengths s hd (empty w p n).1 :=
    ⟨fun a h => (ha a h).elim, fun _ h => (Nat.lt_irrefl _ h).elim⟩
  rcases s with s|s
  · cases he : x.seat.read s with
    | some i => rw [(x.seat.valid _ _).mp he, source h i]; exact h.left i
    | none =>
      rw [empty_source h s he]
      apply absent
      rintro ⟨e, _|_⟩ he'
      · have hh := (x.seat.valid s (M.src e).1).mpr (Sum.inl.inj he').symm
        rw [he] at hh
        contradiction
      · exact Sum.inr_ne_inl he'
  · cases he : y.seat.read s with
    | some i => rw [(y.seat.valid _ _).mp he, destination h i]; exact h.right i
    | none =>
      rw [empty_destination h s he]
      apply absent
      rintro ⟨e, _|_⟩ he'
      · exact Sum.inl_ne_inr he'
      · have hh := (y.seat.valid s (M.dst e).1).mpr (Sum.inr.inj he').symm
        rw [he] at hh
        contradiction

end Script
end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload
end

/-!
为每个活跃对端描述符构造两个方向。

**英文原文**

Form both directions of each active peer descriptor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
open Coloring
variable (F : Type) [Field F] {m m' a b p w n t : ℕ}

-- 读法：`(input m m' p w).width` 不超过 `2 ^ n * (100 + t) ^ 3`。
theorem input_bound (hm : m + p ≤ n) (hm' : m' + p ≤ n) (hw : w ≤ t) (hn : n ≤ t) :
    (input m m' p w).width ≤ 2 ^ n * (100 + t) ^ 3 := by
  let C := 2 ^ n * (100 + t) ^ 2
  have h (k : ℕ) (hk : k + p ≤ n) : (lengths k p w).width ≤ C :=
    (lengths_bound hw).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hk))
  have h₁ : (Column (m + p) (m' + p)).width ≤ C :=
    (Peers.bound_vec _ (by simpa using hm'.trans hn) hm).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by decide)))
  have h₂ : C * 3 ≤ 2 ^ n * (100 + t) ^ 3 := calc
    _ ≤ C * (100 + t) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by unfold C; rw [mul_assoc, ← pow_succ]
  unfold input
  rw [Format.width_pair, Format.width_pair]
  exact (Nat.add_le_add (Nat.add_le_add (h m hm) (h m' hm')) h₁).trans (by omega)

-- 读法：`turn` 的取值由 `(x.1, if side = 0 then x.2 else (x.2.2, x.2.1))` 给出。
private def turn {R : Format} (side : B 1) (x : (Peers.desc R).obj) : (Peers.desc R).obj :=
  (x.1, if side = 0 then x.2 else (x.2.2, x.2.1))

-- 读法：映射 `(turn side)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (6)` 为上界。按 `side = 0` 成立与否分情况。
private theorem cheap_turn (R : Format) (side : B 1) (hr : (Peers.desc R).width ≤ t) :
    Cheap F 0 t (Peers.desc R) (Peers.desc R) (turn side) 6 := by
  have x := Cheap.id F (show (Peers.desc R).width ≤ 2 ^ 0 * (100 + t) ^ 1 by simp only [pow_zero, pow_one, one_mul]; omega)
  by_cases h : side = 0
  · rw [show turn (R := R) side = id by funext x; simp [turn, h]]
    exact x.mono (by decide)
  · rw [show turn (R := R) side = fun x => (x.1, (x.2.2, x.2.1)) by funext x; simp [turn, h]]
    exact x.fst.pair (x.snd.snd.pair x.snd.fst)

-- 读法：`straight` 的取值由 `(active l x.1.1 i, address a b false x.1.1 i, address a b true x.1.2 (x.2 i))` 给出。
private def straight (a b l : ℕ) (x : (input m m' p w).obj) (i : B (m + p)) :
    (Peers.desc (keyFmt a b p)).obj :=
  (active l x.1.1 i, address a b false x.1.1 i, address a b true x.1.2 (x.2 i))

-- 读法：映射 `(straight a b l)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (t)) ^ (130)` 为上界。
private theorem cheap_straight (hm : m + p ≤ n) (hm' : m' + p ≤ n)
    (h : n + w + a + b + 1 ≤ t) (ht : (Peers.desc (keyFmt a b p)).width ≤ t) (l : ℕ) :
    Cheap F n t (input m m' p w) (.vec (m + p) (Peers.desc (keyFmt a b p))) (straight a b l) 130 := by
  have hw : w ≤ t := by omega
  have hn : n ≤ t := by omega
  let K := keyFmt a b p
  have hK : K.width ≤ t := by change (Peers.desc K).width ≤ t at ht; simp only [Peers.desc, Format.width_pair] at ht; omega
  have x := Cheap.id F (input_bound hm hm' hw hn)
  have old := x.fst.fst
  have flag := old.comp (Peers.lift F (cheap_active F l hw (m := m) (p := p)) hm)
  have a₁ := cheap_address F false (show m + p + w + a + b + 1 ≤ t by omega)
  have a₂ := cheap_address F true (show m' + p + w + a + b + 1 ≤ t by omega)
  have src := old.comp (Peers.lift F a₁ hm)
  have dst := x.fst.snd.comp (Peers.lift F a₂ hm')
  have remote := (dst.pair x.snd).comp (Peers.read F K hK hm' hm hn)
  -- 推导：记下中间结论 `hay`：`Format.bit.width + (Format.pair K K).width ≤ (100 + t) ^ 2`。
  have hay : Format.bit.width + (Format.pair K K).width ≤ (100 + t) ^ 2 :=
    (by rw [← Format.width_pair]; exact ht.trans (by ring_nf; omega))
  have hk' : K.width + K.width ≤ (100 + t) ^ 2 := by rw [Format.width_pair] at hay; omega
  have pair := (src.pair remote).comp (Peers.zipper F _ hm K K hk')
  have res := (flag.pair pair).comp (Peers.zipper F _ hm .bit (.pair K K) hay)
  exact res.mono (by decide)

-- 读法：映射 `(rows a b l)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (t)) ^ (132)` 为上界。这里调用 `done.mono`。
theorem cheap_rows (hm : m + p + 1 ≤ n) (hm' : m' + p ≤ n)
    (h : n + w + a + b + 1 ≤ t) (ht : (Peers.desc (keyFmt a b p)).width ≤ t) (l : ℕ) :
    Cheap F n t (input m m' p w) (.vec (m + p + 1) (Peers.desc (keyFmt a b p))) (rows a b l) 132 := by
  have hh : m + p ≤ n := by omega
  have prep := cheap_straight F hh hm' h ht l
  let z := Match.rowIndex (m + p) 1
  have spread := Peers.reindex F (Peers.desc (keyFmt a b p)) ht hh hm (fun i => (z i).1)
  have tw := Cheap.map _ (fun i : B (m + p + 1) => cheap_turn F (keyFmt a b p) (z i).2 ht)
  have finish := Peers.lift F tw hm
  have done := (prep.comp spread).comp finish
  exact done.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
end

/-!
# 由宿主范围与接触长度生成全局对端指令

两组宿主存储区的大小可以不同。表的高度只取决于二进层数的对数。

**英文原文**

Global peer commands from host extents and contact lengths

The two host banks can have different sizes. The table height uses
only the logarithm of the number of dyadic levels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout

open Coloring
open scoped Classical
variable {m V k m' V' k' d p w : ℕ}

-- 读法：`height` 的取值由 `max m m' + bits k k' + p + 2` 给出。
def height (m k m' k' p : ℕ) := max m m' + bits k k' + p + 2
-- 读法：`size` 的取值由 `let n := height m k m' k' p 16 * (max k k' + 2) * (2 ^ n * (101 + 5 * n + w) ^ 134)` 给出。
def size (m k m' k' p w : ℕ) :=
  let n := height m k m' k' p
  16 * (max k k' + 2) * (2 ^ n * (101 + 5 * n + w) ^ 134)

-- 读法：`(P m V k m' V' k').count _ d i` 不超过 `height m k m' k' p`。这里调用 `Nat.clog_le_of_le_pow`。
theorem count_bound (hd : d ≤ 2 ^ p) (i : (P m V k m' V' k').Level (max k k') d) :
    (P m V k m' V' k').count _ d i ≤ height m k m' k' p := by
  let K := keyFmt (max m m') (bits k k') p
  let e := ((P m V k m' V' k').codePort i (host _ _ _ _ _ _) hd).trans K.serial.toEmbedding
  have h := Fintype.card_le_of_injective e e.injective
  rw [Fintype.card_fin] at h
  have he : height m k m' k' p = K.width + 1 := by simp [K, height, keyFmt, Bank.pairCode, hostFmt]; omega
  unfold Bank.count
  apply Nat.clog_le_of_le_pow
  rw [he, pow_succ]
  have := Nat.two_pow_pos K.width
  omega

-- 读法：结论为 `let n := height m k m' k' p Cheap F n (1 + 5 * n + w) (input m m' p w) (Perm ((P m V k m' V' k').count _ d i)) (fun x => control (V := V) (k := k) (V' := V') (k' := k') hd x i) 134`。
private theorem level_cost (F : Type) [Field F] (hd : d ≤ 2 ^ p)
    (i : (P m V k m' V' k').Level (max k k') d) :
    let n := height m k m' k' p
    Cheap F n (1 + 5 * n + w) (input m m' p w) (Perm ((P m V k m' V' k').count _ d i))
      (fun x => control (V := V) (k := k) (V' := V') (k' := k') hd x i) 134 := by
  intro n
  let t := 1 + 5 * n + w
  let K := keyFmt (max m m') (bits k k') p
  let q := (P m V k m' V' k').count _ d i
  have hK : K.width ≤ n := by simp [K, keyFmt, Bank.pairCode, hostFmt, n, height]; omega
  -- 推导：记下中间结论 `hq`：`q ≤ n`。
  have hq : q ≤ n := count_bound hd i
  have h₁ : m + p + 1 ≤ n := by unfold n height; omega
  have h₂ : m' + p ≤ n := by unfold n height; omega
  have h₃ : n + w + max m m' + bits k k' + 1 ≤ t := by unfold t n height; omega
  have h₄ : (Peers.desc K).width ≤ t := by simp only [Peers.desc, Format.width_pair]; change 1 + (K.width + K.width) ≤ _; omega
  have gen := cheap_rows F h₁ h₂ h₃ h₄ i.1.val
  have hn : Peers.height (m + p + 1) q K ≤ n := max_le h₁ (max_le hq hK)
  have ht : Peers.width (m + p + 1) q K ≤ t := by unfold Peers.width; omega
  let tab := (P m V k m' V' k').portTable i (host _ _ _ _ _ _) hd
  have dec := (Peers.lift F (Peers.cheap_decode F (m + p + 1) K tab) hn).widen ht
  exact (gen.comp dec).mono (by decide)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `(Fmt.pi X)` 实现映射 `f` 的开销至多为 `(16 * (J + 2) * C)`。这里调用 `Nat.mul_le_mul`。
private theorem broadcast {F I : Type} [Field F] [Fintype I] {u : ℕ} {L : Set (Table F)}
    (hu : 3 ≤ u) (A : Format) (X : I → Format) (f : A.obj → (Fmt.pi X).obj) (J C : ℕ)
    (hI : Fintype.card I ≤ J + 1) (hA : A.width ≤ C)
    (hslot : ∀ i : I, Map F u L A (X i) (fun x => f x i) (4 * C)) :
    Map F u L A (Fmt.pi X) f (16 * (J + 2) * C) := by
  let R := Fmt.pi (fun _ : I => A)
  have hc := Map.family hslot
  have copy : Circuit F A R (fun x _ => x) (A.width + 2 * R.width) :=
    Circuit.project (A := A) (D := R) (fun v => v.2) (fun _ _ => rfl)
  have h := ((Map.circuit (L := L) hu copy).comp hc)
  have hR : R.width ≤ (J + 1) * C := by
    simp only [R, Fmt.width_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_le_mul hI hA
  refine h.mono ?_
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  linarith only [hR, hA, Nat.mul_le_mul_right C hI, Nat.zero_le (J * C), Nat.zero_le C]

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(input m m' p w)` 到 `(S m V k m' V' k' d).peers` 实现映射 `(control hd)` 的开销至多为 `(size m k m' k' p w)`。
theorem realize {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (hd : d ≤ 2 ^ p) :
    Map F u L (input m m' p w) (S m V k m' V' k' d).peers (control hd) (size m k m' k' p w) := by
  let n := height m k m' k' p
  let t := 1 + 5 * n + w
  let C := 2 ^ n * (100 + t) ^ 134
  let A := input m m' p w
  let Z := S m V k m' V' k' d
  let I := Z.Levels
  have hslot (i : I) : Map F u L A (Perm (Z.count i))
      (fun x => control (V := V) (k := k) (V' := V') (k' := k') hd x i) (4 * C) := by
    -- 推导：从 `level_cost F hd i (w := w)` 中取出 `r, hr, hb`。
    obtain ⟨r, hr, hb⟩ := level_cost F hd i (w := w)
    change _ + _ + r ≤ C at hb
    have H := Map.circuit (L := L) hu hr
    have ht : r ≤ C := (Nat.le_add_left _ _).trans hb
    exact H.mono (Nat.mul_le_mul_left 4 ht)
  have hI : Fintype.card I ≤ max k k' + 1 := by
    let f : Z.Levels → Fin (max k k' + 1) := fun i => i.1
    have hf : Function.Injective f := Subtype.val_injective
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hA : A.width ≤ C := by
    unfold A C
    refine (input_bound (n := n) (t := t) (by unfold n height; omega)
      (by unfold n height; omega) (by unfold t; omega) (by unfold t; omega)).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
  -- 推导：记下中间结论 `he`：`size m k m' k' p w = 16 * (max k k' + 2) * C`。
  have he : size m k m' k' p w = 16 * (max k k' + 2) * C := by
    unfold size
    dsimp only
    rw [show 101 + 5 * height m k m' k' p + w = 100 + t by unfold t n; omega]
  rw [he]
  have done := broadcast (F := F) (L := L) hu A (fun i : I => Perm (Z.count i))
    (control (m := m) (m' := m') (V := V) (k := k) (V' := V') (k' := k') (w := w) hd) (max k k') C hI hA hslot
  dsimp only [I, Z, A] at done
  unfold Channels.peers
  exact done

-- 读法：`size m k m' k' p w` 不超过 `2 ^ (max m m' + p) * (100 + t) ^ 274`。
/-- 在填充后接触项数的基础上产生的多项式额外开销。

英文原文：Polynomial overhead above the number of padded contacts.
-/
theorem size_le {t : ℕ} (hm : max m m' ≤ t) (hk : max k k' ≤ t)
    (hp : p ≤ t) (hw : w ≤ t) :
    size m k m' k' p w ≤ 2 ^ (max m m' + p) * (100 + t) ^ 274 := by
  let n := height m k m' k' p
  let a := 100 + t
  have hb : 2 ^ bits k k' ≤ 2 * (max k k' + 1) := Transcript.pow_clog_le_twice (by omega)
  have hc := Nat.lt_two_pow_self (n := bits k k')
  have hn : n ≤ 4 * t + 4 := by unfold n height; omega
  have hu : 101 + 5 * n + w ≤ a ^ 2 := by unfold a; ring_nf; omega
  have hv : 16 * (max k k' + 2) ≤ a ^ 2 := by unfold a; ring_nf; omega
  -- 推导：记下中间结论 `ha`：`2 ^ (bits k k' + 2) ≤ a ^ 4`。
  have ha : 2 ^ (bits k k' + 2) ≤ a ^ 4 := by
    have hh : 2 ^ bits k k' * 4 ≤ a ^ 2 := by unfold a; ring_nf; omega
    rw [pow_add]
    exact hh.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have he : 2 ^ n = 2 ^ (max m m' + p) * 2 ^ (bits k k' + 2) := by
    rw [← pow_add]; congr 1; unfold n height; omega
  change 16 * (max k k' + 2) * (2 ^ n * (101 + 5 * n + w) ^ 134) ≤ _
  rw [he]
  calc
    _ ≤ a ^ 2 * ((2 ^ (max m m' + p) * a ^ 4) * (a ^ 2) ^ 134) :=
      Nat.mul_le_mul hv (Nat.mul_le_mul (Nat.mul_le_mul_left _ ha) (Nat.pow_le_pow_left hu 134))
    _ = _ := by rw [← pow_mul, mul_assoc _ (a ^ 4), mul_left_comm, ← pow_add, ← pow_add]

end OAI.LinearAlgebra.MatrixExponent.Assembly.PeerLayout
end

/-!
# 编译有效载荷传输

全局列表为每个接触项设置一个条目。局部地址流以互不相交的区间给出，无须为传输的每个比特单独给出全局地址。

**英文原文**

Compiling a payload transfer

The global list has one entry per contact. Locally the address
stream is supplied as disjoint intervals, without a global
address for each transmitted bit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script

open Coloring PeerLayout
open scoped Classical
variable {m V k m' V' k' d p w n : ℕ} (hd : d ≤ 2 ^ p)

-- 读法：`prepare` 的取值由 `Prod.map (P m V k m' V' k').distribute (Prod.map (PeerLayout.control hd) mask)` 给出。
private def prepare : (Out m V k m' V' k' p w n).obj →
    ((S m V k m' V' k' d).shortControl (fun _ => n)).obj :=
  Prod.map (P m V k m' V' k').distribute (Prod.map (PeerLayout.control hd) mask)

-- 读法：`command` 的取值由 `(S m V k m' V' k' d).expandControl (fun _ => n) (fun _ => id) ((P m V k m' V' k').sentinel (max k k') d) ∘ prepare hd` 给出。
def command : (Out m V k m' V' k' p w n).obj → (S m V k m' V' k' d).control.obj :=
  (S m V k m' V' k' d).expandControl (fun _ => n) (fun _ => id)
    ((P m V k m' V' k').sentinel (max k k') d) ∘ prepare hd

-- 读法：`setupCost` 的构造用到 `PeerLayout.size`、`Fmt.payload`。
private def setupCost (m V k m' V' k' d p w n : ℕ) :=
  (P m V k m' V' k').distributionCost (max k k') d w p n +
    (PeerLayout.size m k m' k' p w + 8000 * (k' + 2) * (Fmt.payload m' V' k').width)

-- 读法：`commandCost` 的取值由 `setupCost m V k m' V' k' d p w n + (S m V k m' V' k' d).expandCost (fun _ => n)` 给出。
def commandCost (m V k m' V' k' d p w n : ℕ) :=
  setupCost m V k m' V' k' d p w n + (S m V k m' V' k' d).expandCost (fun _ => n)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(Out m V k m' V' k' p w n)` 到 `((S m V k m' V' k' d).shortControl (fun _ => n))` 实现映射 `(prepare hd)` 的开销至多为 `(setupCost m V k m' V' k' d p w n)`。这里调用 `Nat.lt_succ_iff.mp`。
private theorem setup_net {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) :
    Map F u L (Out m V k m' V' k' p w n) ((S m V k m' V' k' d).shortControl (fun _ => n))
      (prepare hd) (setupCost m V k m' V' k' d p w n) := by
  let b := P m V k m' V' k'
  have hk (i : b.Slot) : b.depth i ≤ max k k' := by
    rcases i with i | i
    · exact (Nat.lt_succ_iff.mp i.1.isLt).trans (le_max_left _ _)
    · exact (Nat.lt_succ_iff.mp i.1.isLt).trans (le_max_right _ _)
  have ha := b.distribute_net (max k k') d w p n (F := F) (L := L) hu hk
  have hp := PeerLayout.realize (F := F) (L := L) (m := m) (m' := m') (V := V) (V' := V')
    (k := k) (k' := k') (w := w) hu hd
  have hm := mask_net (F := F) (L := L) (m := m') (V := V') (k := k') hu
  have h := ha.par (hp.par hm)
  intro a b i j
  exact h a b i j

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(Out m V k m' V' k' p w n)` 到 `(S m V k m' V' k' d).control` 实现映射 `(command hd)` 的开销至多为 `(commandCost m V k m' V' k' d p w n)`。这里调用 `h.comp`。
theorem command_net {F : Type} [Field F] {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) :
    Map F u L (Out m V k m' V' k' p w n) (S m V k m' V' k' d).control
      (command hd) (commandCost m V k m' V' k' d p w n) := by
  have h := setup_net (m := m) (m' := m') (V := V) (V' := V') (k := k) (k' := k')
    (w := w) (n := n) hd (F := F) (L := L) hu
  have he := (S m V k m' V' k' d).expand_control (fun _ => n) (F := F) (L := L) hu
    (fun _ => id) ((P m V k m' V' k').sentinel (max k k') d)
  exact h.comp he

variable {x : Payload m V k} {y : Payload m' V' k'} (M : Traffic x y d)

-- 读法：要证明的命题是 `M.links.Represents (command hd (pack q))`。这里调用 `Bank.Links.Runs.represents`。
theorem represents {q : (Script m m' p w n).obj} (hq : PeerLayout.Fits M hd q.1)
    (h : M.links.Pieces hd (pack q).1) : M.links.Represents (command hd (pack q)) := by
  have hm : mask (pack (V := V) (k := k) (V' := V') (k' := k') q).2.2 = M.links.pad := by
    rw [Script.lengths hq]
    exact funext y.mask_eq
  have he : prepare hd (pack q) = ((P m V k m' V' k').distribute (pack q).1, M.links.plan.control.2) :=
    Prod.ext rfl (Prod.ext hq.correct hm)
  rw [command, Function.comp_apply, he]
  exact Bank.Links.Runs.represents (fun _ => n) M.links _ h.runs

end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
end

/-!
分别进行两次彼此独立的宿主重分配，并按固定方式重编元数据的索引。

**英文原文**

Two independent host redistributions and fixed reindexings of the metadata.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
open Coloring Transcript

-- 读法：`first` 的构造用到 `Format.pair`、`Redistribute.input`、`PeerLayout.input`。
abbrev first (m m' p w n : ℕ) :=
  Format.pair (.pair (Redistribute.input m w (item w p n)) (Redistribute.input m' w (item w p n)))
    (PeerLayout.input m m' p w)

-- 读法：`moved` 的构造用到 `Format.pair`、`Redistribute.output`、`PeerLayout.input`。
abbrev moved (m V k m' V' k' p w n : ℕ) :=
  Format.pair (.pair (Redistribute.output m V k (item w p n)) (Redistribute.output m' V' k' (item w p n)))
    (PeerLayout.input m m' p w)

-- 读法：`staged` 的构造用到 `Format.pair`、`PeerLayout.input`、`Fmt.pi`。
abbrev staged (m V k m' V' k' p w n : ℕ) :=
  Format.pair ((payloadBank m V k m' V' k').records w p n)
    (.pair (PeerLayout.input m m' p w) (Fmt.pi (fun _ : Slot (2 ^ m') V' k' => .addr w)))

variable {F : Type} [Field F] {m V k m' V' k' p w n : ℕ}

-- 读法：逐一匹配输入模式，例如 `.inr j`、`.inl (.inl (.inl j))`、`.inl (.inl (.inr (i, .inl (.inl j))))`、`.inl (.inl (.inr (i, .inl (.inr j))))`。
private def firstPin : (first m m' p w n).pins → (Script m m' p w n).pins
  | .inr j => .inl j
  | .inl (.inl (.inl j)) => .inl (.inl (.inl (.inl j)))
  | .inl (.inl (.inr (i, .inl (.inl j)))) => .inl (.inl (.inl (.inr (i, j))))
  | .inl (.inl (.inr (i, .inl (.inr j)))) => .inr (.inl (i, j))
  | .inl (.inl (.inr (i, .inr j))) => .inl (.inl (.inl (.inl (i, j))))
  | .inl (.inr (.inl j)) => .inl (.inl (.inr (.inl j)))
  | .inl (.inr (.inr (i, .inl (.inl j)))) => .inl (.inl (.inr (.inr (i, j))))
  | .inl (.inr (.inr (i, .inl (.inr j)))) => .inr (.inr (i, j))
  | .inl (.inr (.inr (i, .inr j))) => .inl (.inl (.inr (.inl (i, j))))

-- 读法：在 `F` 上按格式 `(Script m m' p w n)`、`(first m m' p w n)` 编码输入输出，映射 `(fun x => ((left x, right x), x.1))` 的电路规模至多为 `((Script m m' p w n).width + 2 * (first m m' p w n).width)`。这里调用 `Circuit.project`。
private theorem first_net :
    Circuit F (Script m m' p w n) (first m m' p w n) (fun x => ((left x, right x), x.1))
      ((Script m m' p w n).width + 2 * (first m m' p w n).width) := by
  apply Circuit.project firstPin
  rintro x (((j | ⟨i, (t|t)|t⟩) | (j | ⟨i, (t|t)|t⟩)) | j) <;> rfl

-- 读法：`stage` 的取值由 `(Sum.elim (fun i => (x.1.1 i).1) (fun i => (x.1.2 i).1), x.2, fun i => (x.1.2 i).2)` 给出。
private def stage (x : (moved m V k m' V' k' p w n).obj) :
    (staged m V k m' V' k' p w n).obj :=
  (Sum.elim (fun i => (x.1.1 i).1) (fun i => (x.1.2 i).1), x.2, fun i => (x.1.2 i).2)

-- 读法：逐一匹配以下输入模式：`.inl ⟨.inl s, j⟩`、`.inl ⟨.inr s, j⟩`、`.inr (.inl j)`、`.inr (.inr ⟨s, j⟩)`。
private def stagePin : (staged m V k m' V' k' p w n).pins → (moved m V k m' V' k' p w n).pins
  | .inl ⟨.inl s, j⟩ => .inl (.inl ⟨s, .inl j⟩)
  | .inl ⟨.inr s, j⟩ => .inl (.inr ⟨s, .inl j⟩)
  | .inr (.inl j) => .inr j
  | .inr (.inr ⟨s, j⟩) => .inl (.inr ⟨s, .inr j⟩)

-- 读法：在 `F` 上按格式 `(moved m V k m' V' k' p w n)`、`(staged m V k m' V' k' p w n)` 编码输入输出，映射 `stage` 的电路规模至多为 `((moved m V k m' V' k' p w n).width + 2 * (staged m V k m' V' k' p w n).width)`。这里调用 `Circuit.project`。
private theorem stage_net :
    Circuit F (moved m V k m' V' k' p w n) (staged m V k m' V' k' p w n) stage
      ((moved m V k m' V' k' p w n).width + 2 * (staged m V k m' V' k' p w n).width) := by
  apply Circuit.project stagePin
  rintro x (⟨s|s, j⟩|j|⟨s, j⟩) <;> rfl

variable {u v c c' : ℕ} {L : Set (Table F)}

-- 读法：`rawCost` 的构造用到 `Redistribute.cost`、`PeerLayout.input`、`Fintype.card`。
def rawCost (m V k m' V' k' p w n v c c' : ℕ) :=
  4 * ((Script m m' p w n).width + 2 * (first m m' p w n).width) +
  (Redistribute.cost m k w v c + Redistribute.cost m' k' w v c' + 4 * (PeerLayout.input m m' p w).width) +
  4 * ((moved m V k m' V' k' p w n).width + 2 * (staged m V k m' V' k' p w n).width) +
  (4 * ((payloadBank m V k m' V' k').records w p n).width +
    (4 * (PeerLayout.input m m' p w).width + Fintype.card (Slot (2 ^ m') V' k') * (4 * (100 + (w + k' + 1)) ^ 2)))

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(Script m m' p w n)` 到 `(Out m V k m' V' k' p w n)` 实现映射 `pack` 的开销至多为 `(rawCost m V k m' V' k' p w n v c c')`。
theorem build (hu : 3 ≤ u) (ht : Radix.Tag F m v c) (ht' : Radix.Tag F m' v c')
    (ha : (item w p n).width ≤ v) :
    Map F u L (Script m m' p w n) (Out m V k m' V' k' p w n) pack (rawCost m V k m' V' k' p w n v c c') := by
  let mid := PeerLayout.input m m' p w
  have peer := Map.circuit (L := L) hu (Circuit.id F mid)
  have entries := Map.circuit (L := L) hu (Circuit.id F ((payloadBank m V k m' V' k').records w p n))
  obtain ⟨r, hr, hb⟩ := Intervals.cheap_shrink F (show w ≤ w + k' + 1 by omega) (show k' + 1 ≤ w + k' + 1 by omega)
  have hs := (Map.circuit (L := L) hu hr).mono (n := 4 * (100 + (w + k' + 1)) ^ 2) (by omega)
  have hall := Map.family (fun _ : Slot (2 ^ m') V' k' => hs)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hall
  have r₁ := Redistribute.realize (L := L) (V := V) (k := k) (w := w) hu ht _ ha (pad w p n)
  have r₂ := Redistribute.realize (L := L) (V := V') (k := k') (w := w) hu ht' _ ha (pad w p n)
  have pre := Map.circuit (L := L) hu (first_net (F := F) (m := m) (m' := m') (p := p) (w := w) (n := n))
  have rows := pre.comp ((r₁.par r₂).par peer)
  have after := rows.comp (Map.circuit hu stage_net)
  have result := after.comp (entries.par (peer.par hall))
  exact result

end OAI.LinearAlgebra.MatrixExponent.Assembly.Payload.Script
end
