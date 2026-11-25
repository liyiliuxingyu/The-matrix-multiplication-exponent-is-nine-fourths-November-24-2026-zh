-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import Mathlib.GroupTheory.Perm.ViaEmbedding
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Graph
import OAI.LinearAlgebra.MatrixExponent.Install.Products

/-!
# 受控的有效载荷传输

局部指针从存储区汇集比特并装入数据包。每个尺度上的数据包置换配对两端，掩码将未使用的输出比特固定为零。只有数据包索引是全局地址。

**英文原文**

A controlled payload transfer

Local pointers gather bits from a bank into packets. A permutation
of packets at each scale pairs their ends, and the mask pins unused
output bits to zero. Only the packet indices are global addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring

-- 读法：在后续公式中，`Fmt.raw` 是 `⟨I → Bool, I, Equiv.refl _⟩` 的缩写。
abbrev Fmt.raw (I : Type) [Fintype I] : Format := ⟨I → Bool, I, Equiv.refl _⟩

-- 读法：结构的字段包括 `I`、`localWidth`、`bank`、`Levels`、`count`。
structure Channels (A D : Format) where
  I : Type
  [fi : Fintype I]
  localWidth : I → ℕ
  bank : ∀ i, B (localWidth i) → Option (A.pins ⊕ D.pins)
  Levels : Type
  [fl : Fintype Levels]
  count : Levels → ℕ
  size : Levels → ℕ
  tap : ∀ k, B (count k) → Fin (size k) → Option (Σ i, B (localWidth i))

attribute [instance] Channels.fi Channels.fl

namespace Channels
variable {A D : Format} (S : Channels A D)

-- 读法：在后续公式中，`Index` 是 `Σ i, B (S.localWidth i)` 的缩写。
abbrev Index := Σ i, B (S.localWidth i)

-- 读法：在后续公式中，`control` 是 `.pair (Fmt.pi (fun i => Perm (S.localWidth i))) (.pair (Fmt.pi (fun k => Perm (S.count k))) (Fmt.raw D.pins))` 的缩写。
abbrev control : Format :=
  .pair (Fmt.pi (fun i => Perm (S.localWidth i)))
    (.pair (Fmt.pi (fun k => Perm (S.count k))) (Fmt.raw D.pins))

-- 读法：`point` 的取值由 `S.bank i.1 (q.1 i.1 i.2)` 给出。
def point (q : S.control.obj) (i : S.Index) := S.bank i.1 (q.1 i.1 i.2)

-- 读法：`atPort` 的取值由 `(S.tap k i b).bind (S.point q)` 给出。
def atPort (q : S.control.obj) (k : S.Levels) (i : B (S.count k)) (b : Fin (S.size k)) :=
  (S.tap k i b).bind (S.point q)

-- 读法：输入 `i` 时返回 `i.elim false (Sum.elim (A.code x) (D.code y))`。
def value (x : A.obj) (y : D.obj) : Option (A.pins ⊕ D.pins) → Bool :=
  fun i => i.elim false (Sum.elim (A.code x) (D.code y))

-- 读法：`Carries` 表示以下条件：`(∀ i, q.2.2 i = true → D.code y i = false)` 与 `∀ k, Function.Bijective (q.2.1 k) ∧ ∀ i b, value x y (S.atPort q k i b) = value x y (S.atPort q k (q.2.1 k i) b)` 同时成立。
def Carries (q : S.control.obj) (x : A.obj) (y : D.obj) : Prop :=
  (∀ i, q.2.2 i = true → D.code y i = false) ∧
    ∀ k, Function.Bijective (q.2.1 k) ∧
      ∀ i b, value x y (S.atPort q k i b) = value x y (S.atPort q k (q.2.1 k i) b)

-- 读法：`copy` 的取值由 `D.code.symm (fun i => (f i).elim false (A.code x))` 给出。
/-- 读取指定名称的输入比特，若为填充则读作零。同一个输入名称可以出现多次。

英文原文：Read the named input bit, or zero for padding. Repetition of an
input name is allowed.
-/
def copy (f : D.pins → Option A.pins) (x : A.obj) : D.obj :=
  D.code.symm (fun i => (f i).elim false (A.code x))

-- 读法：逐一匹配以下输入模式：`none`、`some (.inl i)`、`some (.inr i)`。
private def origin (f : D.pins → Option A.pins) : Option (A.pins ⊕ D.pins) → Option A.pins
  | none => none
  | some (.inl i) => some i
  | some (.inr i) => f i

-- 读法：结构的字段包括 `pad`、`bij`、`pair`、`covers`。
/-- 控制检查独立于数据取值进行。未使用的目的位置被固定，其余每个目的位置都有对应的来源。

英文原文：Check the controls independently of the data values. Unused
destinations are pinned, and every other destination has a source.
-/
structure Covers (q : S.control.obj) (f : D.pins → Option A.pins) : Prop where
  pad : ∀ i, q.2.2 i = true ↔ f i = none
  bij : ∀ k, Function.Bijective (q.2.1 k)
  pair : ∀ k i b, origin f (S.atPort q k i b) = origin f (S.atPort q k (q.2.1 k i) b)
  covers : ∀ i j, f i = some j → ∃ k a b,
    S.atPort q k a b = some (.inr i) ∧ S.atPort q k (q.2.1 k a) b = some (.inl j)

-- 读法：`S.Carries q x y` 与 `y = copy f x` 等价。这里调用 `D.code.injective`。
theorem carries_iff {q : S.control.obj} {f : D.pins → Option A.pins} (h : S.Covers q f)
    (x : A.obj) (y : D.obj) : S.Carries q x y ↔ y = copy f x := by
  constructor
  · intro hh
    apply D.code.injective
    simp only [copy, Equiv.apply_symm_apply]
    funext i
    cases he : f i with
    | none => exact hh.1 i ((h.pad i).mpr he)
    | some j =>
      -- 推导：从 `h.covers i j he` 中取出 `k, a, b, hd, hs`。
      obtain ⟨k, a, b, hd, hs⟩ := h.covers i j he
      have := (hh.2 k).2 a b
      rwa [hd, hs] at this
  · rintro rfl
    have he (v : Option (A.pins ⊕ D.pins)) :
        value x (copy f x) v = (origin f v).elim false (A.code x) := by
      rcases v with _ | (i | i) <;> simp [value, origin, copy]
    refine ⟨?_, fun k => ⟨h.bij k, fun i b => by rw [he, he, h.pair]⟩⟩
    intro i hi
    simp [copy, (h.pad i).mp hi]

end Channels
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 容量可变的信道槽位

深度为 `s` 的槽位参与所有满足 `i ≤ s` 的数据包宽度 `2^i`。无论邻居有多少，每个端点在每一尺度上预留的空间至多为其容量的两倍。额外的局部地址位用于填充。

**英文原文**

Channel slots at variable capacities

A slot of depth `s` participates at every packet width `2^i`
with `i ≤ s`. Each endpoint reserves at most twice its capacity at
each scale, regardless of the number of neighbors. The extra local
address bit allows padding.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

-- 读法：结构的字段包括 `Slot`、`depth`、`atBit`。
structure Bank (A D : Format) where
  Slot : Type
  [finite : Fintype Slot]
  depth : Slot → ℕ
  atBit : ∀ i, B (depth i) → A.pins ⊕ D.pins

attribute [instance] Bank.finite

namespace Bank
variable {A D : Format} (P : Bank A D) (k d : ℕ)

-- 读法：在后续公式中，`AtDepth` 是 `{s // i ≤ P.depth s}` 的缩写。
abbrev AtDepth (i : ℕ) := {s // i ≤ P.depth s}
-- 读法：在后续公式中，`lanes` 是 `min d (2 ^ (P.depth s.val + 1 - i))` 的缩写。
abbrev lanes (i : ℕ) (s : P.AtDepth i) := min d (2 ^ (P.depth s.val + 1 - i))
-- 读法：在后续公式中，`Port` 是 `Σ s : P.AtDepth i, Fin (P.lanes d i s)` 的缩写。
abbrev Port (i : ℕ) := Σ s : P.AtDepth i, Fin (P.lanes d i s)
-- 读法：在后续公式中，`Level` 是 `{i : Fin (k + 1) // Nonempty (P.Port d i)}` 的缩写。
abbrev Level := {i : Fin (k + 1) // Nonempty (P.Port d i)}
-- 读法：在后续公式中，`Endpoint` 是 `Σ i : P.Level k d, P.AtDepth i.1.val` 的缩写。
abbrev Endpoint := Σ i : P.Level k d, P.AtDepth i.1.val

-- 读法：`count` 的取值由 `Nat.clog 2 (Fintype.card (P.Port d i.1.val) + 1)` 给出。
def count (i : P.Level k d) : ℕ := Nat.clog 2 (Fintype.card (P.Port d i.1.val) + 1)

-- 读法：`index` 的取值由 `(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)))` 给出。
def index (i : P.Level k d) : P.Port d i.1.val ↪ B (P.count k d i) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)))

-- 读法：`localWidth` 的取值由 `P.depth i.2.val + 1` 给出。
def localWidth (i : P.Endpoint k d) := P.depth i.2.val + 1

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
def encode {n : ℕ} : Option (B n) → B (n + 1)
  | none => ⟨2 ^ n, by rw [pow_succ]; have := Nat.two_pow_pos n; omega⟩
  | some i => i.castLE (Nat.pow_le_pow_right (by decide) (by omega))

-- 读法：当 `h : i.val < 2 ^ n` 成立时取 `some ⟨i.val, h⟩`，否则取 `none`。
private def decode {n : ℕ} (i : B (n + 1)) : Option (B n) :=
  if h : i.val < 2 ^ n then some ⟨i.val, h⟩ else none

-- 读法：`decode (encode i)` 等于 `i`。
private theorem decode_encode {n : ℕ} (i : Option (B n)) : decode (encode i) = i := by
  cases i <;> simp [decode, encode, Fin.is_lt]

-- 读法：`P.lanes d i s * 2 ^ i` 不超过 `2 ^ (P.depth s.val + 1)`。
theorem lanes_fit (i : ℕ) (s : P.AtDepth i) :
    P.lanes d i s * 2 ^ i ≤ 2 ^ (P.depth s.val + 1) := by
  calc
    _ ≤ 2 ^ (P.depth s.val + 1 - i) * 2 ^ i := Nat.mul_le_mul_right _ (min_le_right _ _)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel (Nat.le_succ_of_le s.2)]

-- 读法：`bitIndex` 的取值由 `finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (P.lanes_fit d i.1.1.val i.2))` 给出。
def bitIndex (i : P.Endpoint k d) :
    Fin (P.lanes d i.1.1.val i.2) × B i.1.1.val ↪ B (P.localWidth k d i) :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (P.lanes_fit d i.1.1.val i.2))

-- 读法：用字段 `I`、`localWidth`、`bank`、`Levels` 构造 `Channels A D`。
def channels : Channels A D where
  I := P.Endpoint k d
  localWidth := P.localWidth k d
  bank i a := (decode a).map (P.atBit i.2.val)
  Levels := P.Level k d
  count := P.count k d
  size i := 2 ^ i.1.val
  tap i a b := Function.extend (P.index k d i)
    (fun x => some ⟨⟨i, x.1⟩, P.bitIndex k d ⟨i, x.1⟩ (x.2, b)⟩) (fun _ => none) a

-- 读法：结构的字段包括 `peer`、`pointer`、`pad`。
/-- 指针与对端属于控制数据，其取值与各比特的值无关。

英文原文：Pointers and peers are control data, independent of the bit values.
-/
structure Plan where
  peer : ∀ i : P.Level k d, Equiv.Perm (P.Port d i.1.val)
  pointer : ∀ (i : P.Level k d) (e : P.Port d i.1.val),
    B i.1.val → Option (B (P.depth e.1.val))
  pad : D.pins → Bool

variable {P k d} (M : P.Plan k d)

-- 读法：`Plan.control` 的结果类型为 `(P.channels k d).control.obj`。
def Plan.control : (P.channels k d).control.obj :=
  (fun i a => encode (Function.extend (P.bitIndex k d i)
    (fun t => M.pointer i.1 ⟨i.2, t.1⟩ t.2) (fun _ => none) a),
   fun i => ⇑((M.peer i).viaEmbedding (P.index k d i)), M.pad)

-- 读法：`Plan.atBit` 的取值由 `(M.pointer i e b).map (P.atBit e.1.val)` 给出。
def Plan.atBit (i : P.Level k d) (e : P.Port d i.1.val) (b : B i.1.val) :=
  (M.pointer i e b).map (P.atBit e.1.val)

-- 读法：`(P.channels k d).atPort M.control i (P.index k d i e) b` 等于 `M.atBit i e b`。这里调用 `P.index`。
theorem Plan.atPort (i : P.Level k d) (e : P.Port d i.1.val) (b : B i.1.val) :
    (P.channels k d).atPort M.control i (P.index k d i e) b = M.atBit i e b := by
  have h : (P.channels k d).tap i (P.index k d i e) b =
      some ⟨⟨i, e.1⟩, P.bitIndex k d ⟨i, e.1⟩ (e.2, b)⟩ := by
    unfold channels
    dsimp only
    exact (P.index k d i).injective.extend_apply _ _ e
  change ((P.channels k d).tap i (P.index k d i e) b).bind _ = _
  rw [h, Option.bind_some]
  change (decode (encode (Function.extend (P.bitIndex k d ⟨i, e.1⟩)
    (fun t => M.pointer i ⟨e.1, t.1⟩ t.2)
    (fun _ => none) (P.bitIndex k d ⟨i, e.1⟩ (e.2, b))))).map (P.atBit e.1.val) = _
  rw [decode_encode, (P.bitIndex k d _).injective.extend_apply]
  rfl

-- 读法：结论为 `(P.channels k d).Carries M.control x y ↔ (∀ i, M.pad i = true → D.code y i = false) ∧ ∀ i e b, Channels.value x y (M.atBit i e b) = Channels.value x y (M.atBit i (M.peer i e) b)`。
theorem Plan.carries (x : A.obj) (y : D.obj) :
    (P.channels k d).Carries M.control x y ↔
      (∀ i, M.pad i = true → D.code y i = false) ∧
      ∀ i e b, Channels.value x y (M.atBit i e b) = Channels.value x y (M.atBit i (M.peer i e) b) := by
  have he (i : P.Level k d) (e : P.Port d i.1.val) :
      M.control.2.1 i (P.index k d i e) = P.index k d i (M.peer i e) :=
    Equiv.Perm.viaEmbedding_apply _ _ _
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun i e b => ?_⟩
    have h := (h₂ i).2 (P.index k d i e) b
    rwa [he, M.atPort, M.atPort] at h
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun i => ⟨((M.peer i).viaEmbedding _).bijective, fun e b => ?_⟩⟩
    by_cases hh : e ∈ Set.range (P.index k d i)
    -- 推导：从 `hh` 中取出 `a, rfl`。
    · obtain ⟨a, rfl⟩ := hh
      rw [he i a, M.atPort i a b, M.atPort i (M.peer i a) b]
      exact h₂ _ _ _
    · rw [show M.control.2.1 i e = e from Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hh]

end Bank
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 打包同一大小且互不相交的接触项

长度类别与序号确定实际通道。各通道所用比特互不相交，因此每种大小的已占通道数都有上界。

**英文原文**

Packing disjoint contacts of one size

The length class and ordinal determine the physical lane. Disjoint
use of bits bounds the number of occupied lanes of each size.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical
variable {A D : Format} (P : Bank A D) (k d : ℕ)

-- 读法：结构的字段包括 `E`、`place`、`length`、`pointer`、`small`。
structure Links where
  E : Type
  place : E × Bool ↪ P.Slot × Fin d
  length : E → ℕ
  pointer : ∀ e b, Fin (length e) → B (P.depth (place (e, b)).1)
  small : ∀ e b, length e ≤ 2 ^ P.depth (place (e, b)).1
  bounded : ∀ e b, P.depth (place (e, b)).1 ≤ k
  distinct : ∀ (p q : E × Bool) (i : Fin (length p.1)) (j : Fin (length q.1)),
    (place p).1 = (place q).1 → (pointer p.1 p.2 i).val = (pointer q.1 q.2 j).val →
    p = q ∧ i.val = j.val
  pad : D.pins → Bool

namespace Links
variable {P k d} (L : P.Links k d)

-- 读法：为 `Fintype L.E` 构造类型类实例。
instance : Fintype L.E := by
  have : Finite L.E := Finite.of_injective (fun e => L.place (e, false))
    (fun _ _ h => (Prod.mk.inj (L.place.injective h)).1)
  exact Fintype.ofFinite _

-- 读法：`depth` 的取值由 `Nat.clog 2 (L.length e)` 给出。
def depth (e : L.E) := Nat.clog 2 (L.length e)

-- 读法：`L.depth e` 不超过 `P.depth (L.place (e, b)).1`。使用 `Nat.clog_le_of_le_pow` 给出的结论。
theorem depth_le (e : L.E) (b : Bool) : L.depth e ≤ P.depth (L.place (e, b)).1 :=
  Nat.clog_le_of_le_pow (L.small e b)

-- 读法：`L.length e` 不超过 `2 ^ L.depth e`。使用 `Nat.le_pow_clog` 给出的结论。
theorem fits (e : L.E) : L.length e ≤ 2 ^ L.depth e := Nat.le_pow_clog (by decide) _

-- 读法：`level` 的结果类型为 `P.Level k d`。
def level (e : L.E) : P.Level k d := by
  have hd := (L.place (e, false)).2.isLt
  let t : P.AtDepth (L.depth e) := ⟨_, L.depth_le e false⟩
  exact ⟨⟨L.depth e, Nat.lt_succ_of_le ((L.depth_le e false).trans (L.bounded e false))⟩,
    ⟨⟨t, 0, lt_min (by omega) (by positivity)⟩⟩⟩

-- 读法：在后续公式中，`At` 是 `{e // L.level e = i ∧ 0 < L.length e}` 的缩写。
abbrev At (i : P.Level k d) := {e // L.level e = i ∧ 0 < L.length e}

-- 读法：`site` 的取值由 `⟨(L.place (e.1.val, e.2)).1, (congrArg (fun i : P.Level k d => i.1.val) e.1.2.1).symm.le.trans (L.depth_le _ _)⟩` 给出。
def site (i : P.Level k d) (e : L.At i × Bool) : P.AtDepth i.1.val :=
  ⟨(L.place (e.1.val, e.2)).1,
    (congrArg (fun i : P.Level k d => i.1.val) e.1.2.1).symm.le.trans (L.depth_le _ _)⟩

variable (i : P.Level k d) (s : P.AtDepth i.1.val)

-- 读法：在后续公式中，`Here` 是 `{e : L.At i × Bool // L.site i e = s}` 的缩写。
abbrev Here := {e : L.At i × Bool // L.site i e = s}

-- 读法：`item` 的取值由 `(a.val.1.val, a.val.2)` 给出。
private def item (a : L.Here i s) : L.E × Bool := (a.val.1.val, a.val.2)

-- 读法：`(L.item i s)` 是单射。这里调用 `Subtype.ext`。
private theorem item_inj : Function.Injective (L.item i s) := by
  intro a b h
  exact Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2)

-- 读法：`(L.place (L.item i s a)).1` 等于 `s.val`。
private theorem here_eq (a : L.Here i s) : (L.place (L.item i s a)).1 = s.val :=
  congrArg Subtype.val a.property

-- 读法：`serial` 的取值由 `(L.place (L.item i s a)).2` 给出。
private def serial (a : L.Here i s) := (L.place (L.item i s a)).2

-- 读法：`(L.serial i s)` 是单射。这里调用 `L.item_inj`。
private theorem serial_inj : Function.Injective (L.serial i s) := by
  intro a b h
  exact L.item_inj i s (L.place.injective (Prod.ext ((L.here_eq _ _ _).trans (L.here_eq _ _ _).symm) h))

-- 读法：`(∑ a : L.Here i s, L.length (L.item i s a).1)` 不超过 `2 ^ P.depth s.val`。
private theorem total_length : (∑ a : L.Here i s, L.length (L.item i s a).1) ≤ 2 ^ P.depth s.val := by
  let t := L.item i s
  let X := Σ a, Fin (L.length (t a).1)
  let f : X → B (P.depth s.val) := fun p =>
    (L.pointer (t p.1).1 (t p.1).2 p.2).cast (congrArg (fun z => 2 ^ P.depth z) (L.here_eq _ _ _))
  have hi : Function.Injective f := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    obtain ⟨he, h'⟩ := L.distinct (t a) (t b) x y ((L.here_eq _ _ a).trans (L.here_eq _ _ b).symm)
      (congrArg Fin.val h)
    have : a = b := L.item_inj i s he
    subst b
    rw [Fin.ext h']
  simpa only [X, t, Fintype.card_sigma, Fintype.card_fin] using Fintype.card_le_of_injective f hi

-- 读法：`2 ^ (Nat.clog 2 t)` 严格小于 `2 * t`。这里调用 `Nat.mul_lt_mul_of_pos_left`。
private theorem strict_round (t : ℕ) (ht : 0 < t) : 2 ^ (Nat.clog 2 t) < 2 * t := by
  cases he : Nat.clog 2 t with
  | zero => simp; omega
  | succ j =>
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_of_lt_clog (by omega : j < Nat.clog 2 t)) (by decide)

-- 读法：`Fintype.card (L.Here i s) * 2 ^ i.1.val` 严格小于 `2 ^ (P.depth s.val + 1)`。
private theorem active_lanes : Fintype.card (L.Here i s) * 2 ^ i.1.val < 2 ^ (P.depth s.val + 1) := by
  cases isEmpty_or_nonempty (L.Here i s) with
  | inl h => simp
  | inr h =>
    rw [pow_succ']
    calc
      _ = ∑ _ : L.Here i s, 2 ^ i.1.val := by simp
      _ < ∑ a : L.Here i s, 2 * L.length (L.item i s a).1 := by
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => ?_
        have he : L.depth (L.item i s a).1 = i.1.val :=
          congrArg (fun j : P.Level k d => j.1.val) a.val.1.2.1
        exact he ▸ strict_round _ a.val.1.2.2
      _ ≤ _ := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left 2 (L.total_length i s)

-- 读法：`Fintype.card (L.Here i s)` 不超过 `P.lanes d i.1.val s`。这里调用 `le_min`。
private theorem lanes_enough : Fintype.card (L.Here i s) ≤ P.lanes d i.1.val s := by
  apply le_min
  · simpa using Fintype.card_le_of_injective _ (L.serial_inj i s)
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos i.1.val)
  rw [← pow_add, Nat.sub_add_cancel (Nat.le_succ_of_le s.2)]
  exact (L.active_lanes i s).le

-- 读法：`lane` 的结果类型为 `L.Here i s ↪ Fin (P.lanes d i.1.val s)`。
private def lane : L.Here i s ↪ Fin (P.lanes d i.1.val s) :=
  letI : LinearOrder (L.Here i s) := LinearOrder.lift' _ (L.serial_inj i s)
  (Fintype.orderIsoFinOfCardEq _ rfl).symm.toEquiv.toEmbedding.trans
    (Fin.castLEEmb (L.lanes_enough i s))

-- 读法：`location` 的结果类型为 `L.At i × Bool ↪ P.Port d i.1.val`。
def location : L.At i × Bool ↪ P.Port d i.1.val :=
  (Equiv.sigmaFiberEquiv (L.site i)).symm.toEmbedding.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) (L.lane i))

-- 读法：`2 ^ i.1.val * ((L.location i e).2.val + 1)` 严格小于 `2 ^ (P.depth (L.site i e).val + 1)`。这里调用 `Nat.mul_le_mul_right`。
/-- 每条活跃通道的右开区间终点都可用地址字表示。

英文原文：The exclusive end of any active lane fits in the address word.
-/
theorem lane_end (e : L.At i × Bool) :
    2 ^ i.1.val * ((L.location i e).2.val + 1) < 2 ^ (P.depth (L.site i e).val + 1) := by
  let s := L.site i e
  let a : L.Here i s := ⟨e, rfl⟩
  let : LinearOrder (L.Here i s) := LinearOrder.lift' _ (L.serial_inj i s)
  have h : (L.location i e).2.val < Fintype.card (L.Here i s) :=
    ((Fintype.orderIsoFinOfCardEq (L.Here i s) rfl).symm a).isLt
  rw [mul_comm]
  exact (Nat.mul_le_mul_right (2 ^ i.1.val) (Nat.succ_le_of_lt h)).trans_lt (L.active_lanes i s)

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-!
# 为一对端口预留一个数据包

将实际传输长度向上取整为二的幂。读取数据包中未使用的位置时得到零。未参与配对的端口与自身配对。

**英文原文**

Reserving a packet for a pair of ports

Round the actual transmission length up to a power of two. The unused packet
positions read zero. Ports outside the pairing match themselves.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical
variable {A D : Format} (P : Bank A D) (k d : ℕ)

namespace Links
variable {P k d} (L : P.Links k d)

-- 读法：`opposite` 的取值由 `(Equiv.refl _).prodCongr (Equiv.mk Bool.not Bool.not Bool.not_not Bool.not_not)` 给出。
def opposite (i : P.Level k d) : Equiv.Perm (L.At i × Bool) :=
  (Equiv.refl _).prodCongr (Equiv.mk Bool.not Bool.not Bool.not_not Bool.not_not)

-- 读法：当 `h : j < L.length e` 成立时取 `some (L.pointer e b ⟨j, h⟩).val`，否则取 `none`。
private def address (e : L.E) (b : Bool) (j : ℕ) : Option ℕ :=
  if h : j < L.length e then some (L.pointer e b ⟨j, h⟩).val else none

-- 读法：当 `h : z < 2 ^ w` 成立时取 `some ⟨z, h⟩`，否则取 `none`。
private def limit (w z : ℕ) : Option (B w) := if h : z < 2 ^ w then some ⟨z, h⟩ else none

-- 读法：用字段 `peer`、`pointer`、`pad` 构造 `P.Plan k d`。
def plan : P.Plan k d where
  peer i := (L.opposite i).viaEmbedding (L.location i)
  pointer i e b := (Function.extend (L.location i) (fun q => L.address q.1.val q.2 b.val)
    (fun _ => none) e).bind (limit (P.depth e.1.val))
  pad := L.pad

-- 读法：`atBit` 的取值由 `P.atBit (L.place (e, b)).1 (L.pointer e b j)` 给出。
def atBit (e : L.E) (b : Bool) (j : Fin (L.length e)) :=
  P.atBit (L.place (e, b)).1 (L.pointer e b j)

-- 读法：`L.plan.peer i (L.location i (e, b))` 等于 `L.location i (e, !b)`。使用 `Equiv.Perm.viaEmbedding_apply` 给出的结论。
theorem peer_at (i : P.Level k d) (e : L.At i) (b : Bool) :
    L.plan.peer i (L.location i (e, b)) = L.location i (e, !b) :=
  Equiv.Perm.viaEmbedding_apply (L.opposite i) (L.location i) (e, b)

-- 读法：结论为 `(encode (L.plan.pointer i (L.location i e) j)).val = if h : j.val < L.length e.1.val then (L.pointer e.1.val e.2 ⟨j.val, h⟩).val else 2 ^ P.depth (L.place (e.1.val, e.2)).1`。
theorem pointer_at (i : P.Level k d) (e : L.At i × Bool) (j : B i.1.val) :
    (encode (L.plan.pointer i (L.location i e) j)).val =
      if h : j.val < L.length e.1.val then (L.pointer e.1.val e.2 ⟨j.val, h⟩).val
      else 2 ^ P.depth (L.place (e.1.val, e.2)).1 := by
  unfold plan
  dsimp only
  rw [(L.location i).injective.extend_apply]
  change (encode ((L.address e.1.val e.2 j.val).bind
    (limit (P.depth (L.place (e.1.val, e.2)).1)))).val = _
  unfold address
  split
  · rename_i hj
    simp only [Option.bind_some, limit, dite_eq_left (L.pointer e.1.val e.2 ⟨j.val, hj⟩).isLt]
    rfl
  · rfl

-- 读法：`L.plan.atBit i (L.location i (e, b)) j` 等于 `if h : j.val < L.length e.val then some (L.atBit e.val b ⟨j.val, h⟩) else none`。
theorem bit_at (i : P.Level k d) (e : L.At i) (b : Bool) (j : B i.1.val) :
    L.plan.atBit i (L.location i (e, b)) j =
      if h : j.val < L.length e.val then some (L.atBit e.val b ⟨j.val, h⟩) else none := by
  unfold Plan.atBit plan
  dsimp only
  rw [(L.location i).injective.extend_apply]
  change ((L.address e.val b j.val).bind (limit (P.depth (L.place (e.val, b)).1))).map _ = _
  unfold address
  split
  · rename_i hj
    simp only [Option.bind_some, limit, dite_eq_left (L.pointer e.val b ⟨j.val, hj⟩).isLt]
    rfl
  · rfl

-- 读法：`Matches` 表示以下条件：`(∀ i, L.pad i = true → D.code y i = false)` 与 `∀ e j, Sum.elim (A.code x) (D.code y) (L.atBit e false j) = Sum.elim (A.code x) (D.code y) (L.atBit e true j)` 同时成立。
def Matches (x : A.obj) (y : D.obj) : Prop :=
  (∀ i, L.pad i = true → D.code y i = false) ∧ ∀ e j,
    Sum.elim (A.code x) (D.code y) (L.atBit e false j) =
      Sum.elim (A.code x) (D.code y) (L.atBit e true j)

-- 读法：`(P.channels k d).Carries L.plan.control x y` 与 `L.Matches x y` 等价。
theorem carries (x : A.obj) (y : D.obj) :
    (P.channels k d).Carries L.plan.control x y ↔ L.Matches x y := by
  rw [L.plan.carries]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun e j => ?_⟩
    let i := L.level e
    let t : L.At i := ⟨e, rfl, lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩
    let a : B i.1.val := j.castLE (L.fits e)
    have he := h i (L.location i (t, false)) a
    -- 推导：记下中间结论 `hj`：`a.val < L.length t.val`。
    have hj : a.val < L.length t.val := j.isLt
    rw [L.peer_at, L.bit_at, L.bit_at, dite_eq_left hj, dite_eq_left hj] at he
    exact he
  · rintro ⟨hm, h⟩
    refine ⟨hm, fun i t j => ?_⟩
    by_cases ht : t ∈ Set.range (L.location i)
    · obtain ⟨⟨e, b⟩, rfl⟩ := ht
      rw [L.peer_at, L.bit_at, L.bit_at]
      split
      · cases b
        · exact h _ _
        · exact (h _ _).symm
      · rfl
    · rw [show L.plan.peer i t = t from Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ht]

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end

/-!
# 分配活跃信道的通道位

与承载有效载荷的宿主不同，空信道不占位置。最大地址不可能是正长度所属的层级，因而可用它统一收纳所有非活跃或填充信道。

**英文原文**

Assigning active channel lanes

Unlike payload hosts, empty channels do not take a seat.
The largest address is never a positive length's level, so it can
serve as the bucket for every inactive or padded channel.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

namespace PackRank

variable {p w : ℕ}

-- 读法：当 `0 < x` 成立时取 `code x`，否则取 `⊤`。
def bucket (x : B w) : B w := if 0 < x then code x else ⊤

-- 读法：`code x` 不等于 `⊤`。这里调用 `he.trans_le`。
theorem code_ne_top (x : B w) (hx : 0 < x.val) : code x ≠ ⊤ := by
  have h : x.val ≤ 2 ^ (x.val - 1) := by
    have := Nat.lt_two_pow_self (n := x.val - 1)
    omega
  have he : code x < x := by
    change Nat.clog 2 x.val < x.val
    have := Nat.clog_le_of_le_pow h
    omega
  exact (he.trans_le le_top).ne

-- 读法：`bucket x = bucket y` 与 `0 < x.val ∧ (code x).val = (code y).val` 等价。按 `0 < x` 成立与否分情况。
theorem bucket_eq (x y : B w) (hy : 0 < y.val) :
    bucket x = bucket y ↔ 0 < x.val ∧ (code x).val = (code y).val := by
  have hy' : 0 < y := hy
  by_cases h : 0 < x
  · simp [bucket, h, hy', show 0 < x.val from h, Fin.ext_iff]
  · simp [bucket, h, hy', show ¬ 0 < x.val from h, Ne.symm (code_ne_top y hy)]

-- 读法：`lanes` 的取值由 `(code (x i), groupRank (bucket ∘ x) i)` 给出。
def lanes (x : B p → B w) (i : B p) := (code (x i), groupRank (bucket ∘ x) i)

-- 读法：映射 `bucket` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (w)) ^ (20)` 为上界。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem cheap_bucket (F : Type) [Field F] (w : ℕ) :
    Cheap F 0 w (.addr w) (.addr w) bucket 20 := by
  have hw : (Format.addr w).width ≤ 2 ^ 0 * (100 + w) ^ 1 := by simp
  have lt := ((Cheap.const F hw hw 0).pair (Cheap.id F hw)).comp (Intervals.cheap_compare F le_rfl)
  have h := (((cheap_code F w).pair (Cheap.const F hw hw ⊤)).pair lt).comp (cheap_select F w)
  convert h.mono (d := 20) (by decide) using 1
  funext x
  by_cases he : 0 < x <;> simp [bucket, he]

-- 读法：映射 `lanes` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (p) * (100 + ((p + w))) ^ (110)` 为上界。这里调用 `levels.pair`。
theorem cheap_lanes (F : Type) [Field F] (p w : ℕ) :
    Cheap F p (p + w) (.vec p (.addr w)) (.vec p (.pair (.addr w) (.addr p))) lanes 110 := by
  have h : w ≤ p + w := by omega
  have levels := Cheap.map _ (fun _ : B p => (cheap_code F w).widen h)
  have buckets := Cheap.map _ (fun _ : B p => (cheap_bucket F w).widen h)
  exact (levels.pair (buckets.comp (cheap_groupRank F p w))).zip.mono (by decide)

end PackRank

namespace Bank.Links

variable {A D : Format} {P : Bank A D} {k d p w : ℕ} (L : P.Links k d)

-- 读法：`FitsLengths` 的结果类型为 `Prop`。
def FitsLengths (s : P.Slot) (hd : d ≤ 2 ^ p) (x : B p → B w) : Prop :=
  (∀ e : L.E × Bool, (L.place e).1 = s → (x ((L.place e).2.castLE hd)).val = L.length e.1) ∧
    ∀ i, 0 < (x i).val → ∃ e : L.E × Bool, (L.place e).1 = s ∧ (L.place e).2.castLE hd = i

-- 读法：`(PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).1.val = i.1.val` 与 `(PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).2.val = (L.location i e).2.val` 同时成立。
theorem lanes_correct (i : P.Level k d) (e : L.At i × Bool) {hd : d ≤ 2 ^ p} {x : B p → B w}
    (h : L.FitsLengths (L.site i e).val hd x) :
    (PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).1.val = i.1.val ∧
      (PackRank.lanes x ((L.place (e.1.val, e.2)).2.castLE hd)).2.val = (L.location i e).2.val := by
  let s := L.site i e
  let S := L.Here i s
  let e₀ : S := ⟨e, rfl⟩
  let name (a : S) := (a.val.1.val, a.val.2)
  let serial (a : S) := (L.place (name a)).2
  let idx (a : S) := (serial a).castLE hd
  have slot (a : S) : (L.place (name a)).1 = s.val := congrArg Subtype.val a.2
  have length (a : S) : (x (idx a)).val = L.length a.val.1.val := h.1 _ (slot a)
  have pos (a : S) : 0 < (x (idx a)).val := (length a).symm ▸ a.val.1.property.2
  have code (a : S) : (PackRank.code (x (idx a))).val = i.1.val := by
    change Nat.clog 2 (x (idx a)).val = _
    rw [length]
    exact congrArg (fun i : P.Level k d => i.1.val) a.val.1.property.1
  refine ⟨code e₀, ?_⟩
  let z := PackRank.bucket ∘ x
  have eq (a b : S) : z (idx a) = z (idx b) :=
    (PackRank.bucket_eq _ _ (pos b)).mpr ⟨pos a, (code a).trans (code b).symm⟩
  let f (a : S) : {u // z u = z (idx e₀)} := ⟨idx a, eq a e₀⟩
  have onto : Function.Surjective f := by
    rintro ⟨u, hu⟩
    -- 推导：从 `(PackRank.bucket_eq _ _ (pos e₀)).mp hu` 中取出 `hp, he`。
    obtain ⟨hp, he⟩ := (PackRank.bucket_eq _ _ (pos e₀)).mp hu
    obtain ⟨a, ha, hidx⟩ := h.2 u hp
    have hlen : (x u).val = L.length a.1 := by rw [← hidx]; exact h.1 a ha
    have hl : L.level a.1 = i := by
      apply Subtype.ext
      apply Fin.ext
      change Nat.clog 2 (L.length a.1) = _
      rw [← hlen]
      exact he.trans (code e₀)
    let v : L.At i × Bool := (⟨a.1, hl, hlen ▸ hp⟩, a.2)
    exact ⟨⟨v, Subtype.ext ha⟩, Subtype.ext hidx⟩
  have hinj : Function.Injective serial := by
    intro a b hab
    have he := L.place.injective (Prod.ext ((slot a).trans (slot b).symm) hab)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj he).1) (Prod.mk.inj he).2)
  let _ : LinearOrder S := LinearOrder.lift' serial hinj
  let E := Fintype.orderIsoFinOfCardEq S rfl
  let rank (a : S) : Fin (Fintype.card S) := ⟨Control.rank z (idx a), by
    have hb := Fintype.card_le_of_surjective f onto
    rw [Fintype.card_subtype, ← Control.histogram_none] at hb
    exact (Control.rank_lt z (idx a)).trans_le ((eq a e₀) ▸ hb)⟩
  have hm : StrictMono rank := fun a b hab => Control.rank_mono z (eq a b) hab
  have he := congrFun (hm.comp E.strictMono).eq_id (E.symm e₀)
  simp only [Function.comp_apply, OrderIso.apply_symm_apply, id_eq] at he
  change (groupRank z (idx e₀)).val = (E.symm e₀).val
  rw [groupRank_val]
  exact congrArg Fin.val he

end Bank.Links
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 局部汇集与全局检查

汇集操作的地址仅指向局部存储区。所有恒取零的取样端共用一个隐藏比特，其他每个隐藏比特都恰好是一次确定性汇集的输出。

**英文原文**

Local gathers and global checks

The addresses of a gather refer only to the local bank. A single
hidden bit is shared by all constant-zero taps. Every other hidden
bit is the output of exactly one deterministic gather.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Channels

open Coloring Install
open scoped Classical

variable {A D : Format} (S : Channels A D)

-- 读法：在后续公式中，`gatherIn` 是 `Format.pair (.vec k .bit) (Perm k)` 的缩写。
private abbrev gatherIn (k : ℕ) := Format.pair (.vec k .bit) (Perm k)
-- 读法：在后续公式中，`gatherOut` 是 `Format.vec k .bit` 的缩写。
private abbrev gatherOut (k : ℕ) := Format.vec k .bit

-- 读法：`gather` 的取值由 `x.1 ∘ x.2` 给出。
private def gather (k : ℕ) (x : (gatherIn k).obj) : (gatherOut k).obj := x.1 ∘ x.2

-- 读法：在后续公式中，`row` 是 `Fmt.raw (Fin (S.size k))` 的缩写。
private abbrev row (k : S.Levels) := Fmt.raw (Fin (S.size k))

-- 读法：在后续公式中，`Tasks` 是 `Option (S.I ⊕ S.Levels ⊕ D.pins)` 的缩写。
private abbrev Tasks := Option (S.I ⊕ S.Levels ⊕ D.pins)
-- 读法：在后续公式中，`Hidden` 是 `Option S.Index` 的缩写。
private abbrev Hidden := Option S.Index
-- 读法：在后续公式中，`Name` 是 `((S.control.pins ⊕ A.pins) ⊕ D.pins) ⊕ S.Hidden` 的缩写。
private abbrev Name := ((S.control.pins ⊕ A.pins) ⊕ D.pins) ⊕ S.Hidden

-- 读法：逐一匹配以下输入模式：`none`、`some (.inl i)`、`some (.inr (.inl k))`、`some (.inr (.inr _))`。
private abbrev pins : S.Tasks → Type
  | none => Unit
  | some (.inl i) => (gatherIn (S.localWidth i)).pins ⊕ (gatherOut (S.localWidth i)).pins
  | some (.inr (.inl k)) => (exchangeIn (S.row k) (S.count k)).pins ⊕ (exchangeOut (S.row k) (S.count k)).pins
  | some (.inr (.inr _)) => Bool

-- 读法：为 `Fintype (S.pins i)` 构造类型类实例。
private instance (i : S.Tasks) : Fintype (S.pins i) := by
  rcases i with _ | (i | k | a) <;> unfold pins <;> infer_instance

-- 读法：逐一匹配以下输入模式：`none`、`some (.inl i)`、`some (.inr i)`。
private def port : Option (A.pins ⊕ D.pins) → S.Name
  | none => .inr none
  | some (.inl i) => .inl (.inl (.inr i))
  | some (.inr i) => .inl (.inr i)

-- 读法：逐一匹配输入模式，例如 `none, _`、`some (.inl i), .inl (.inl (a, _))`、`some (.inl i), .inl (.inr a)`、`some (.inl i), .inr (a, _)`。
private def wiring : (i : S.Tasks) → S.pins i → S.Name
  | none, _ => .inr none
  | some (.inl i), .inl (.inl (a, _)) => S.port (S.bank i a)
  | some (.inl i), .inl (.inr a) => .inl (.inl (.inl (.inl ⟨i, a⟩)))
  | some (.inl i), .inr (a, _) => .inr (some ⟨i, a⟩)
  | some (.inr (.inl k)), .inl (.inl a) => .inl (.inl (.inl (.inr (.inl ⟨k, a⟩))))
  | some (.inr (.inl k)), .inl (.inr (i, b)) => .inr (S.tap k i b)
  | some (.inr (.inl k)), .inr (i, b) => .inr (S.tap k i b)
  | some (.inr (.inr a)), true => .inl (.inl (.inl (.inr (.inr a))))
  | some (.inr (.inr a)), false => .inl (.inr a)

-- 读法：逐一匹配以下输入模式：`none, z`、`some (.inl i), z`、`some (.inr (.inl k)), z`、`some (.inr (.inr _)), z`。
private def agrees : (i : S.Tasks) → (S.pins i → Bool) → Prop
  | none, z => z () = false
  | some (.inl i), z => gather _ ((gatherIn _).code.symm (z ∘ Sum.inl)) =
      (gatherOut (S.localWidth i)).code.symm (z ∘ Sum.inr)
  | some (.inr (.inl k)), z =>
    let x := (exchangeIn (S.row k) (S.count k)).code.symm (z ∘ Sum.inl)
    let y := (exchangeOut (S.row k) (S.count k)).code.symm (z ∘ Sum.inr)
    Function.Bijective x.1 ∧ y = x.2 ∘ x.1
  | some (.inr (.inr _)), z => z true = true → z false = false

-- 读法：输入 `i` 时返回 `value x y (i.bind (S.point q))`。
private def trace (q : S.control.obj) (x : A.obj) (y : D.obj) : S.Hidden → Bool :=
  fun i => value x y (i.bind (S.point q))

variable (q : S.control.obj) (x : A.obj) (y : D.obj) (z : S.Hidden → Bool)

-- 读法：`run` 的取值由 `Sum.elim (Sum.elim ((S.control.pair A).code (q, x)) (D.code y)) z` 给出。
private def run : S.Name → Bool :=
  Sum.elim (Sum.elim ((S.control.pair A).code (q, x)) (D.code y)) z

-- 读法：`S.run q x y z (S.port i)` 等于 `value x y i`。
private theorem read_port (h : z none = false) (i : Option (A.pins ⊕ D.pins)) :
    S.run q x y z (S.port i) = value x y i := by
  rcases i with _ | (i | i)
  · exact h
  · rfl
  · rfl

-- 读法：`S.agrees (some (.inl i)) (S.run q x y z ∘ S.wiring (some (.inl i)))` 与 `∀ a, z (some ⟨i, a⟩) = S.trace q x y (some ⟨i, a⟩)` 等价。
private theorem gather_iff (h : z none = false) (i : S.I) :
    S.agrees (some (.inl i)) (S.run q x y z ∘ S.wiring (some (.inl i))) ↔
      ∀ a, z (some ⟨i, a⟩) = S.trace q x y (some ⟨i, a⟩) := by
  let u := S.run q x y z ∘ S.wiring (some (.inl i))
  let v := (gatherIn (S.localWidth i)).code.symm (u ∘ Sum.inl)
  have hs (a) : v.1 a = value x y (S.bank i a) := S.read_port q x y z h _
  have ht (a) : v.2 a = q.1 i a := (Format.addr (S.localWidth i)).code.symm_apply_apply (q.1 i a)
  change (fun a => v.1 (v.2 a)) = (fun a => z (some ⟨i, a⟩)) ↔ _
  simp only [funext_iff, hs, ht, trace, Option.bind_some, point, eq_comm]

-- 读法：`S.agrees (some (.inr (.inl k))) (S.run q x y z ∘ S.wiring (some (.inr (.inl k))))` 与 `Function.Bijective (q.2.1 k) ∧ ∀ i b, z (S.tap k i b) = z (S.tap k (q.2.1 k i) b)` 等价。
private theorem exchange_iff (k : S.Levels) :
    S.agrees (some (.inr (.inl k))) (S.run q x y z ∘ S.wiring (some (.inr (.inl k)))) ↔
      Function.Bijective (q.2.1 k) ∧ ∀ i b, z (S.tap k i b) = z (S.tap k (q.2.1 k i) b) := by
  let u := S.run q x y z ∘ S.wiring (some (.inr (.inl k)))
  let v := (exchangeIn (S.row k) (S.count k)).code.symm (u ∘ Sum.inl)
  have ht : v.1 = q.2.1 k := funext fun a => (Format.addr (S.count k)).code.symm_apply_apply (q.2.1 k a)
  change Function.Bijective v.1 ∧
    (fun i b => z (S.tap k i b)) = (fun i b => z (S.tap k (v.1 i) b)) ↔ _
  rw [ht]
  simp only [funext_iff]

-- 读法：`(∀ i, S.agrees i (S.run q x y z ∘ S.wiring i))` 与 `z = S.trace q x y ∧ S.Carries q x y` 等价。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem agrees_iff :
    (∀ i, S.agrees i (S.run q x y z ∘ S.wiring i)) ↔ z = S.trace q x y ∧ S.Carries q x y := by
  constructor
  · intro h
    have h₀ : z none = false := h none
    have hz : z = S.trace q x y := by
      funext i
      rcases i with _ | ⟨i, a⟩
      · exact h₀
      · exact (S.gather_iff q x y z h₀ i).mp (h _) a
    refine ⟨hz, fun i => h (some (.inr (.inr i))), fun k => ?_⟩
    have he := (S.exchange_iff q x y z k).mp (h _)
    rw [hz] at he
    exact he
  · rintro ⟨rfl, h₀, h₁⟩ (_ | (i | k | a))
    · rfl
    · exact (S.gather_iff q x y _ rfl i).mpr (fun _ => rfl)
    · exact (S.exchange_iff q x y _ k).mpr (h₁ k)
    · exact h₀ a

variable (F : Type) [Field F]

-- 读法：当 `S.Carries x.1 x.2 y` 成立时取 `1`，否则取 `0`。
def kernel (x : (S.control.pair A).obj) (y : D.obj) : F :=
  if S.Carries x.1 x.2 y then 1 else 0

-- 读法：当 `S.agrees i z` 成立时取 `1`，否则取 `0`。
private def check (i : S.Tasks) (z : S.pins i → Bool) : F := if S.agrees i z then 1 else 0

-- 读法：`(∏ i, S.check F i (S.run q x y z ∘ S.wiring i))` 等于 `if z = S.trace q x y then S.kernel F (q, x) y else 0`。按 `∀ i, S.agrees i (S.run q x y z ∘ S.wiring i)` 成立与否分情况。
private theorem all_checks :
    (∏ i, S.check F i (S.run q x y z ∘ S.wiring i)) =
      if z = S.trace q x y then S.kernel F (q, x) y else 0 := by
  by_cases he : ∀ i, S.agrees i (S.run q x y z ∘ S.wiring i)
  · obtain ⟨h₁, h₂⟩ := (S.agrees_iff q x y z).mp he
    simp only [check, he, ite_true, Finset.prod_const_one, ite_eq_left h₁, kernel, h₂]
  · have hn := mt (S.agrees_iff q x y z).mpr he
    obtain ⟨i, hi⟩ := not_forall.mp he
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (show S.check F i (S.run q x y z ∘ S.wiring i) = 0 from ite_eq_right hi)]
    simp only [kernel, ← ite_and, hn, ite_false]

-- 读法：`localCost` 的取值由 `2 ^ n * (100 + (n + 1)) ^ 8` 给出。
def localCost (n : ℕ) := 2 ^ n * (100 + (n + 1)) ^ 8

-- 读法：`globalCost` 的取值由 `m + 100 * 2 ^ n * (n + v + 1)` 给出。
def globalCost (m n v : ℕ) := m + 100 * 2 ^ n * (n + v + 1)

-- 读法：`cost` 的构造用到 `S.control.pair`、`D.width`、`S.localWidth`。
def cost (v m : S.Levels → ℕ) :=
  8 * ((S.control.pair A).width + D.width + (∑ i, 2 ^ (S.localWidth i)) + 1) +
    36 * (16 + (∑ i, localCost (S.localWidth i)) +
      (∑ k, globalCost (m k) (S.count k) (v k)) + 32 * D.width) + 4 * D.width

-- 读法：要证明的命题是 `Kernel F u L (S.control.pair A) D (S.kernel F) (S.cost v m)`。这里调用 `Weight.dense`。
/-- 在每个数据包尺度上执行一次带标签置换即可。

英文原文：One tagged permutation per packet scale suffices.
-/
theorem realize {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (v m : S.Levels → ℕ) (hv : ∀ k, S.size k ≤ v k)
    (ht : ∀ k, Radix.Tag F (S.count k) (v k) (m k)) :
    Kernel F u L (S.control.pair A) D (S.kernel F) (S.cost v m) := by
  let c : S.Tasks → ℕ
    | none => 16
    | some (.inl i) => localCost (S.localWidth i)
    | some (.inr (.inl k)) => globalCost (m k) (S.count k) (v k)
    | some (.inr (.inr _)) => 32
  have hc (i) : Weight F (S.check F i) (c i) := by
    rcases i with _ | (i | k | a)
    · exact Weight.dense F Unit _
    · let n := S.localWidth i
      have hg : Cheap F n (n + 1) (gatherIn n) (gatherOut n) (gather n) 8 :=
        Cheap.lookup F n (n + 1) .bit (by omega) (by rw [Format.width_bit]; omega)
      exact hg.weight
    · have he := exchange_weight (S.row k) (ht k) (by simpa [row, Fmt.raw, Format.width] using hv k)
      convert he using 1
      · funext z
        simp only [check, agrees, exchangeCheck, exchange]
        congr 1
      · rfl
    · exact Weight.dense F Bool _
  -- 推导：记下中间结论 `hw`：`= Kernel.factors (A`。
  have hw := Kernel.factors (A := S.control.pair A) (B := D) (L := L) (S.check F) S.wiring
    (fun i => 4 * c i) hu (fun i => Transcript.of_weight hu (hc i))
  have he (a : (S.control.pair A).obj) (b : D.obj) :
      Transcript.weightedSum (S.check F) S.wiring (Sum.elim ((S.control.pair A).code a) (D.code b)) =
        S.kernel F a b := by
    rcases a with ⟨q, x⟩
    have eq (z : S.Hidden → Bool) :
        (∏ i, S.check F i (Sum.elim (Sum.elim ((S.control.pair A).code (q, x)) (D.code b)) z ∘ S.wiring i)) =
          if z = S.trace q x b then S.kernel F (q, x) b else 0 := S.all_checks q x b z F
    unfold Transcript.weightedSum
    simp only [eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [he] at hw
  refine hw.mono ?_
  rw [← Finset.mul_sum, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [c, cost, Hidden, Index, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  unfold Format.width
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Channels
end

/-!
# 预留所有较小信道的总成本

全局地址按端点计费。把二进列表中的占位数据包也计入后，比特总体量仍以总容量、层数与端口数三者之积为上界。

**英文原文**

Total cost of reserving all the smaller channels

Global addresses are paid per endpoint. The bit volume, including
dummy packets in the dyadic lists, is bounded by the total capacity
times the number of levels and ports.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Bank

open Coloring
open scoped Classical

variable {A D : Format} (P : Bank A D) (k d : ℕ)

-- 读法：`capacity` 的取值由 `∑ i, 2 ^ P.depth i` 给出。
def capacity := ∑ i, 2 ^ P.depth i

-- 读法：`Fintype.card (P.Port d s)` 不超过 `d * Fintype.card P.Slot`。这里调用 `Nat.mul_le_mul_left`。
theorem port_count (s : ℕ) : Fintype.card (P.Port d s) ≤ d * Fintype.card P.Slot := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : P.AtDepth s, d := Finset.sum_le_sum fun i _ => by
      rw [Fintype.card_fin]; exact min_le_left _ _
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, mul_comm]
      exact Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)

-- 读法：`Fintype.card (P.Level k d)` 不超过 `k + 1`。使用 `Fintype.card_subtype_le` 给出的结论。
theorem level_count : Fintype.card (P.Level k d) ≤ k + 1 :=
  (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)

-- 读法：`1 ≤ P.count k d i` 与 `P.count k d i ≤ n` 同时成立。
theorem count_range {n : ℕ} (h : d * Fintype.card P.Slot < 2 ^ n) (i : P.Level k d) :
    1 ≤ P.count k d i ∧ P.count k d i ≤ n := by
  have := i.property
  have hp : 0 < Fintype.card (P.Port d i.1.val) := Fintype.card_pos
  have hc := P.port_count d i.1.val
  exact ⟨Nat.clog_pos (by decide) (by omega), Nat.clog_le_of_le_pow (by omega)⟩

-- 读法：`2 ^ (P.count k d i)` 不超过 `4 * Fintype.card (P.Port d i.1.val)`。
private theorem count_bound (i : P.Level k d) :
    2 ^ (P.count k d i) ≤ 4 * Fintype.card (P.Port d i.1.val) := by
  have := i.property
  have hp : 0 < Fintype.card (P.Port d i.1.val) := Fintype.card_pos
  have h := Transcript.pow_clog_le_twice (x := Fintype.card (P.Port d i.1.val) + 1) (by omega)
  unfold count
  omega

-- 读法：`(∑ i : P.AtDepth s, 2 ^ P.depth i.val)` 不超过 `P.capacity`。这里调用 `Finset.sum_le_sum_of_subset`。
private theorem slot_sum (s : ℕ) :
    (∑ i : P.AtDepth s, 2 ^ P.depth i.val) ≤ P.capacity := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => s ≤ P.depth i)) Finset.mem_filter_univ
    (fun i => 2 ^ P.depth i)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

-- 读法：结论为 `∑ i, f i ≤ (k + 1) * Q`。
private theorem level_sum (f : P.Level k d → ℕ) {Q : ℕ} (h : ∀ i, f i ≤ Q) :
    ∑ i, f i ≤ (k + 1) * Q := by
  refine (Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)).trans ?_
  simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using
    Nat.mul_le_mul_right Q (P.level_count k d)

-- 读法：`(∑ i, 2 ^ P.localWidth k d i)` 不超过 `(k + 1) * (2 * P.capacity)`。这里调用 `P.level_sum`。
theorem local_volume :
    (∑ i, 2 ^ P.localWidth k d i) ≤ (k + 1) * (2 * P.capacity) := by
  rw [Fintype.sum_sigma]
  apply P.level_sum k d
  intro i
  simp only [localWidth, pow_succ', ← Finset.mul_sum]
  exact Nat.mul_le_mul_left 2 (P.slot_sum i.1.val)

-- 读法：`(∑ i, 2 ^ P.count k d i)` 不超过 `(k + 1) * (4 * d * Fintype.card P.Slot)`。这里调用 `P.level_sum`。
theorem packet_count :
    (∑ i, 2 ^ P.count k d i) ≤ (k + 1) * (4 * d * Fintype.card P.Slot) := by
  apply P.level_sum k d
  intro i
  rw [mul_assoc]
  exact (P.count_bound k d i).trans (Nat.mul_le_mul_left 4 (P.port_count d i.1.val))

-- 读法：`(∑ i, 2 ^ P.count k d i * 2 ^ i.1.val)` 不超过 `(k + 1) * (8 * P.capacity)`。这里调用 `P.level_sum`。
theorem packet_volume :
    (∑ i, 2 ^ P.count k d i * 2 ^ i.1.val) ≤ (k + 1) * (8 * P.capacity) := by
  apply P.level_sum k d
  intro i
  let j := i.1.val
  have ha : Fintype.card (P.Port d j) * 2 ^ j ≤ 2 * P.capacity := by
    simp only [Port, Fintype.card_sigma, Fintype.card_fin, Finset.sum_mul]
    calc
      _ ≤ ∑ s : P.AtDepth j, 2 ^ (P.depth s.val + 1) :=
        Finset.sum_le_sum (fun s _ => P.lanes_fit d j s)
      _ ≤ _ := by simp only [pow_succ', ← Finset.mul_sum]; exact Nat.mul_le_mul_left 2 (P.slot_sum j)
  calc
    _ ≤ 4 * Fintype.card (P.Port d j) * 2 ^ j := Nat.mul_le_mul_right _ (P.count_bound k d i)
    _ ≤ _ := by linarith only [ha]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Bank
end
