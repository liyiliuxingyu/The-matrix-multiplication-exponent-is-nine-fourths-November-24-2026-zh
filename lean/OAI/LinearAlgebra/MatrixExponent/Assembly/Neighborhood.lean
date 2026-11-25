-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

/-!
# 单个阶段的外部有效载荷组

每个获分配的槽位仅用其被占用的前缀存储数据，其余位置均固定为零。实际宽度由总长度预算控制，至多额外乘上与二进层数有关的因子。

**英文原文**

The exterior payload bank of a stage

Only the occupied prefix of each assigned slot stores data.
All other positions are pinned to zero. The physical width
depends on the total length allowance, up to a factor for the
number of dyadic levels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Transcript
open scoped Classical

namespace Fmt

-- 读法：在后续公式中，`Port` 是 `Σ s : Slot (2 ^ m) V k, Fin (capacity s)` 的缩写。
abbrev Port (m V k : ℕ) := Σ s : Slot (2 ^ m) V k, Fin (capacity s)

-- 读法：在后续公式中，`payload` 是 `⟨Port m V k → Bool, Port m V k, Equiv.refl _⟩` 的缩写。
abbrev payload (m V k : ℕ) : Format := ⟨Port m V k → Bool, Port m V k, Equiv.refl _⟩

-- 读法：`(payload m V k).width` 不超过 `(k + 1) * (2 * V)`。
theorem width_payload (m V k : ℕ) : (payload m V k).width ≤ (k + 1) * (2 * V) := by
  simpa only [Format.width, payload, Fintype.card_sigma, Fintype.card_fin] using
    sum_capacity (2 ^ m) V k

end Fmt

variable {m V k : ℕ}

-- 读法：结构的字段包括 `length`、`total`、`longest`。
/-- 即使宿主为空也占用一个单位，因此通常的二进容量界在零点也适用。

英文原文：An empty host takes one unit, so the usual dyadic capacity
bounds apply without an exception at zero.
-/
structure Payload (m V k : ℕ) where
  length : B m → ℕ
  total : ∑ i, max 1 (length i) ≤ V
  longest : ∀ i, length i ≤ 2 ^ k

namespace Payload
variable (p : Payload m V k)

-- 读法：在后续公式中，`Bit` 是 `Σ i, Fin (p.length i)` 的缩写。
abbrev Bit := Σ i, Fin (p.length i)

-- 读法：`seat` 的结果类型为 `Selector (B m) (Slot (2 ^ m) V k)`。
def seat : Selector (B m) (Slot (2 ^ m) V k) :=
  Selector.packed (fun i => max 1 (p.length i)) (fun _ => lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (by simp)
    p.total (fun i => max_le (Nat.two_pow_pos k) (p.longest i))

-- 读法：`p.length i` 不超过 `capacity (p.seat.write i)`。通过传递性衔接 `le_max_right` 与 `Selector.packed_size`。
theorem fits (i : B m) : p.length i ≤ capacity (p.seat.write i) :=
  (le_max_right 1 _).trans (Selector.packed_size (fun t => max 1 (p.length t)) _ _ _ _ i)

-- 读法：`wire` 的取值由 `Function.Embedding.sigmaMap ⟨p.seat.write, p.seat.injective⟩ (fun i => Fin.castLEEmb (p.fits i))` 给出。
/-- 按原有次序为每条信道的比特编号。

英文原文：Number each channel's bits in their original order.
-/
def wire : p.Bit ↪ Fmt.Port m V k :=
  Function.Embedding.sigmaMap ⟨p.seat.write, p.seat.injective⟩ (fun i => Fin.castLEEmb (p.fits i))

-- 读法：`store` 的取值由 `Function.extend p.wire f (fun _ => false)` 给出。
def store (f : p.Bit → Bool) : (Fmt.payload m V k).obj :=
  Function.extend p.wire f (fun _ => false)

-- 读法：`p.store f (p.wire i)` 等于 `f i`。使用 `p.wire.injective.extend_apply` 给出的结论。
@[simp] theorem read_store (f : p.Bit → Bool) (i : p.Bit) : p.store f (p.wire i) = f i :=
  p.wire.injective.extend_apply _ _ _

-- 读法：`p.store f i` 等于 `false`。使用 `Function.extend_apply'` 给出的结论。
theorem padding (f : p.Bit → Bool) (i : Fmt.Port m V k) (hi : i ∉ Set.range p.wire) :
    p.store f i = false := Function.extend_apply' _ _ _ hi

-- 读法：`x` 等于 `p.store f`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem store_unique (f : p.Bit → Bool) (x : (Fmt.payload m V k).obj)
    (hr : ∀ i, x (p.wire i) = f i) (hz : ∀ i ∉ Set.range p.wire, x i = false) :
    x = p.store f := by
  funext i
  by_cases hi : i ∈ Set.range p.wire
  · obtain ⟨j, rfl⟩ := hi
    rw [hr, read_store]
  · rw [hz _ hi, padding _ _ _ hi]

-- 读法：`p.store` 是单射。用函数外延性比较等号两侧在 `i` 处的取值。
theorem store_injective : Function.Injective p.store := by
  intro x y he
  funext i
  simpa using congrFun he (p.wire i)

end Payload
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 公共宿主上的有序线束

在每个出现位置，模式均使用短邻居索引。解码表与全局宿主名称及块编号无关。每个区段的两端具有相同的内部端口次序。允许宽度为零，就可容纳未使用的位置，也能表示没有参数的标量。

**英文原文**

Ordered bundles on a common host

Patterns use short neighbor indices at every occurrence. The decoding
table is independent of the global host names and the block number.
Port order inside each span is the same at its two ends. Width zero
permits unused seats, including a scalar with no arguments.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

-- 读法：结构的字段包括 `width`、`direction`、`peer`、`value`。
structure Pattern (F : Type) (d k e : ℕ) where
  width : B k → B e → ℕ
  direction : B k → B e → Bool
  peer : B k → B e → Option (B d × B k × B e)
  value : (j : B k) → (∀ s : B e, Fin (width j s) → Bool) → F

-- 读法：结构的字段包括 `m`、`d`、`h`、`k`、`e`。
structure Scheme (F : Type) where
  m : ℕ
  d : ℕ
  h : ℕ
  k : ℕ
  e : ℕ
  ℓ : ℕ
  decode : B ℓ → Pattern F d k e

namespace Scheme
variable {F : Type} (S : Scheme F)

-- 读法：在后续公式中，`format` 是 `Fmt.rows S.m S.d S.h (.addr S.ℓ)` 的缩写。
abbrev format := Fmt.rows S.m S.d S.h (.addr S.ℓ)
-- 读法：在后续公式中，`Vtx` 是 `B S.m × B S.h × B S.k` 的缩写。
abbrev Vtx := B S.m × B S.h × B S.k
-- 读法：在后续公式中，`Span` 是 `S.Vtx × B S.e` 的缩写。
abbrev Span := S.Vtx × B S.e

variable (r : S.format.obj)

-- 读法：`pattern` 的取值由 `S.decode ((r v.1).2 v.2.1)` 给出。
def pattern (v : S.Vtx) := S.decode ((r v.1).2 v.2.1)

-- 读法：`width` 的取值由 `(S.pattern r p.1).width p.1.2.2 p.2` 给出。
def width (p : S.Span) := (S.pattern r p.1).width p.1.2.2 p.2

-- 读法：`direction` 的取值由 `(S.pattern r p.1).direction p.1.2.2 p.2` 给出。
def direction (p : S.Span) := (S.pattern r p.1).direction p.1.2.2 p.2

-- 读法：`peer` 的取值由 `((S.pattern r p.1).peer p.1.2.2 p.2).map fun t => (((r p.1.1).1 t.1, p.1.2.1, t.2.1), t.2.2)` 给出。
def peer (p : S.Span) : Option S.Span :=
  ((S.pattern r p.1).peer p.1.2.2 p.2).map
    fun t => (((r p.1.1).1 t.1, p.1.2.1, t.2.1), t.2.2)

-- 读法：`Proper` 表示以下条件：对每个 `p q`，由 `S.peer r p = some q` 推出 `S.peer r q = some p ∧ S.width r p = S.width r q ∧ S.direction r p ≠ S.direction r q`。
def Proper : Prop := ∀ p q, S.peer r p = some q →
  S.peer r q = some p ∧ S.width r p = S.width r q ∧ S.direction r p ≠ S.direction r q

-- 读法：在后续公式中，`Pin` 是 `Σ p : S.Span, Fin (S.width r p)` 的缩写。
abbrev Pin := Σ p : S.Span, Fin (S.width r p)
-- 读法：在后续公式中，`LocalPin` 是 `Σ s : B S.e, Fin (S.width r (v, s))` 的缩写。
abbrev LocalPin (v : S.Vtx) := Σ s : B S.e, Fin (S.width r (v, s))
-- 读法：在后续公式中，`exposed` 是 `{p : S.Pin r // S.peer r p.1 = none}` 的缩写。
abbrev exposed := {p : S.Pin r // S.peer r p.1 = none}

-- 读法：`port` 的取值由 `⟨(v, p.1), p.2⟩` 给出。
def port (v : S.Vtx) (p : S.LocalPin r v) : S.Pin r := ⟨(v, p.1), p.2⟩

-- 读法：`table` 的取值由 `(S.pattern r v).value v.2.2 fun s i => x ⟨s, i⟩` 给出。
def table (v : S.Vtx) (x : S.LocalPin r v → Bool) :=
  (S.pattern r v).value v.2.2 fun s i => x ⟨s, i⟩

-- 读法：`Joins` 表示以下条件：`S.peer r p.1 = some q.1` 与 `p.2.val = q.2.val` 同时成立。
def Joins (p q : S.Pin r) : Prop := S.peer r p.1 = some q.1 ∧ p.2.val = q.2.val

-- 读法：`Agrees` 表示以下条件：由 `(∀ p, y p.val = x p) ∧ ∀ p q, S.Joins r p q` 推出 `y p = y q`。
def Agrees (x : S.exposed r → Bool) (y : S.Pin r → Bool) : Prop :=
  (∀ p, y p.val = x p) ∧ ∀ p q, S.Joins r p q → y p = y q

-- 读法：`eval` 的取值由 `∑ y : S.Pin r → Bool, if S.Agrees r x y then ∏ v, S.table r v (y ∘ S.port r v) else 0` 给出。
def eval [Field F] (x : S.exposed r → Bool) :=
  ∑ y : S.Pin r → Bool, if S.Agrees r x y then ∏ v, S.table r v (y ∘ S.port r v) else 0

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 按区段次序排列的站点表

两侧均按区段编号的递增次序列出区段，再在每个区段内按偏移量的递增次序列出比特。构造此表只需要模式与局部站点标签。

**英文原文**

Station tables in span order

Each side lists the spans in increasing order and the bits of each
span in increasing offset. Only the pattern and local station label
are needed to construct the table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Pattern
open Coloring Transcript

variable {F : Type} {d k e : ℕ} (P : Pattern F d k e) (j : B k)

-- 读法：在后续公式中，`Pin` 是 `Σ s, Fin (P.width j s)` 的缩写。
abbrev Pin := Σ s, Fin (P.width j s)
-- 读法：在后续公式中，`Side` 是 `{s // P.direction j s = b}` 的缩写。
private abbrev Side (b : Bool) := {s // P.direction j s = b}
-- 读法：在后续公式中，`lengths` 是 `P.width j s.1` 的缩写。
private abbrev lengths (b : Bool) (s : P.Side j b) := P.width j s.1
-- 读法：在后续公式中，`Group` 是 `Σ s, Fin (P.lengths j b s)` 的缩写。
private abbrev Group (b : Bool) := Σ s, Fin (P.lengths j b s)

-- 读法：`wire` 的取值由 `word (Fintype.card (Lex (P.Group j b)))` 给出。
def wire (b : Bool) := word (Fintype.card (Lex (P.Group j b)))

-- 读法：`serial` 的结果类型为 `slots (P.wire j b) ≃ P.Group j b`。
private def serial (b : Bool) : slots (P.wire j b) ≃ P.Group j b :=
  ((positions (P.wire j b)).trans (finCongr (wd_word _))).trans
    ((Fintype.orderIsoFinOfCardEq (Lex (P.Group j b)) rfl).toEquiv.trans ofLex)

-- 读法：`flat` 的取值由 `⟨q.1.1, q.2⟩` 给出。
private def flat (b : Bool) (q : P.Group j b) : P.Pin j := ⟨q.1.1, q.2⟩

-- 读法：`(P.flat j b)` 是单射。
private theorem flat_inj (b : Bool) : Function.Injective (P.flat j b) := by
  rintro ⟨⟨s, h⟩, i⟩ ⟨⟨t, h'⟩, l⟩ he
  have eq : s = t := congrArg Sigma.fst he
  subst t
  have : i = l := Fin.ext (congrArg (fun x => x.2.val) he)
  rw [this]

-- 读法：`sides` 的结果类型为 `P.Group j false ⊕ P.Group j true ≃ P.Pin j`。
private def sides : P.Group j false ⊕ P.Group j true ≃ P.Pin j :=
  Equiv.ofBijective (Sum.elim (P.flat j false) (P.flat j true)) (by
    constructor
    · rintro (i|i) (l|l) h
      · exact congrArg Sum.inl (P.flat_inj j _ h)
      · have he : i.1.1 = l.1.1 := congrArg Sigma.fst h
        have := i.1.2
        rw [he, l.1.2] at this
        cases this
      · have he : i.1.1 = l.1.1 := congrArg Sigma.fst h
        have := i.1.2
        rw [he, l.1.2] at this
        cases this
      · exact congrArg Sum.inr (P.flat_inj j _ h)
    · rintro ⟨s, i⟩
      cases h : P.direction j s
      · exact ⟨.inl ⟨⟨s, h⟩, i⟩, rfl⟩
      · exact ⟨.inr ⟨⟨s, h⟩, i⟩, rfl⟩)

-- 读法：`orderedPin` 的取值由 `((P.serial j false).sumCongr (P.serial j true)).trans (P.sides j)` 给出。
def orderedPin : slots (P.wire j false) ⊕ slots (P.wire j true) ≃ P.Pin j :=
  ((P.serial j false).sumCongr (P.serial j true)).trans (P.sides j)

-- 读法：`P.direction j (P.orderedPin j i).1` 等于 `i.isRight`。对 `i` 分类讨论。
theorem pin_side (i : slots (P.wire j false) ⊕ slots (P.wire j true)) :
    P.direction j (P.orderedPin j i).1 = i.isRight := by
  cases i with
  | inl i => exact (P.serial j false i).1.2
  | inr i => exact (P.serial j true i).1.2

-- 读法：`orderedTable` 的结果类型为 `Table F`。
def orderedTable : Table F :=
  ⟨P.wire j false, P.wire j true, fun x y => P.value j fun s i =>
    Sum.elim (bits (P.wire j false) x) (bits (P.wire j true) y) ((P.orderedPin j).symm ⟨s, i⟩)⟩

-- 读法：`sample (P.orderedTable j) (t ∘ P.orderedPin j)` 等于 `P.value j (fun s i => t ⟨s, i⟩)`。用函数外延性比较等号两侧在 `s i` 处的取值。
theorem sample_ordered (t : P.Pin j → Bool) :
    sample (P.orderedTable j) (t ∘ P.orderedPin j) = P.value j (fun s i => t ⟨s, i⟩) := by
  unfold sample orderedTable
  apply congrArg (P.value j)
  funext s i
  simp only [Equiv.apply_symm_apply]
  have h (x : slots (P.wire j false) ⊕ slots (P.wire j true)) :
      Sum.elim (t ∘ P.orderedPin j ∘ Sum.inl) (t ∘ P.orderedPin j ∘ Sum.inr) x =
        t (P.orderedPin j x) := by cases x <;> rfl
  rw [← Function.comp_assoc, ← Function.comp_assoc] at h
  rw [h, Equiv.apply_symm_apply]

-- 读法：`start` 的取值由 `Processor.start (P.lengths j (P.direction j s)) ⟨s, rfl⟩` 给出。
def start (s : B e) :=
  Processor.start (P.lengths j (P.direction j s)) ⟨s, rfl⟩

-- 读法：`P.start j s.1` 等于 `Processor.start (P.lengths j b) s`。
private theorem start_eq (b : Bool) (s : P.Side j b) :
    P.start j s.1 = Processor.start (P.lengths j b) s := by
  obtain ⟨s, h⟩ := s
  subst b
  rfl

-- 读法：`P.start j s + P.width j s` 不超过 `P.start j t`。这里调用 `Processor.start_left`。
theorem start_left {s t : B e} (h : P.direction j s = P.direction j t) (ht : s < t) :
    P.start j s + P.width j s ≤ P.start j t := by
  rw [P.start_eq j _ ⟨s, h⟩]
  exact Processor.start_left (P.lengths j _) ⟨s, h⟩ ⟨t, rfl⟩ ht

-- 读法：`(positions (P.wire j b) i).val` 等于 `P.start j (P.serial j b i).1.1 + (P.serial j b i).2.val`。
private theorem serial_position (b : Bool) (i : slots (P.wire j b)) :
    (positions (P.wire j b) i).val = P.start j (P.serial j b i).1.1 + (P.serial j b i).2.val := by
  rw [P.start_eq]
  let g := Fintype.orderIsoFinOfCardEq (Lex (P.Group j b)) rfl
  let x := (finCongr (wd_word (Fintype.card (Lex (P.Group j b))))) (positions (P.wire j b) i)
  calc
    _ = (g.symm (g x)).val := by rw [OrderIso.symm_apply_apply]; rfl
    _ = _ := Processor.serial_rank (P.lengths j b) rfl (g x)

-- 读法：`(positions (P.wire j false) i).val` 等于 `P.start j (P.orderedPin j (.inl i)).1 + (P.orderedPin j (.inl i)).2.val`。使用 `P.serial_position` 给出的结论。
theorem position_left (i : slots (P.wire j false)) :
    (positions (P.wire j false) i).val = P.start j (P.orderedPin j (.inl i)).1 +
      (P.orderedPin j (.inl i)).2.val := P.serial_position j false i

-- 读法：`(positions (P.wire j true) i).val` 等于 `P.start j (P.orderedPin j (.inr i)).1 + (P.orderedPin j (.inr i)).2.val`。使用 `P.serial_position` 给出的结论。
theorem position_right (i : slots (P.wire j true)) :
    (positions (P.wire j true) i).val = P.start j (P.orderedPin j (.inr i)).1 +
      (P.orderedPin j (.inr i)).2.val := P.serial_position j true i

end OAI.LinearAlgebra.MatrixExponent.Assembly.Pattern
end

/-!
# 计算单个宿主位置上的匹配

同一位置的所有块共用一份邻居列表。写入一行的只有该列表的短索引与邻居的群落键。

**英文原文**

Computing the matching at one host position

The neighbor list is common to all blocks of the position. Only a
short index into that list and the neighbor's colony key enter a row.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring

-- 读法：在后续公式中，`Input` 是 `Format.pair (.vec h .bit) (.pair (.vec h (Fmt.occ d h e k ℓ)) (.vec h (.vec d (.addr ℓ))))` 的缩写。
abbrev Input (d h e k ℓ : ℕ) :=
  Format.pair (.vec h .bit) (.pair (.vec h (Fmt.occ d h e k ℓ)) (.vec h (.vec d (.addr ℓ))))

-- 读法：在后续公式中，`Labels` 是 `Format.pair (.addr h) (.pair (.addr ℓ) (.addr d))` 的缩写。
abbrev Labels (h ℓ d : ℕ) := Format.pair (.addr h) (.pair (.addr ℓ) (.addr d))

-- 读法：`rowIndex` 的取值由 `(finCongr (pow_add 2 h e)).trans finProdFinEquiv.symm` 给出。
def rowIndex (h e : ℕ) : B (h + e) ≃ B h × B e :=
  (finCongr (pow_add 2 h e)).trans finProdFinEquiv.symm

variable {d h e k ℓ : ℕ}

-- 读法：`rows` 的结果类型为 `Rows (h + e) (Labels h ℓ d).width`。
def rows (x : (Input d h e k ℓ).obj) : Rows (h + e) (Labels h ℓ d).width :=
  let block i := (rowIndex h e i).1
  let stub i := (x.2.1 (block i)).2 (rowIndex h e i).2
  let code := (Labels h ℓ d).serial
  (fun i => (stub i).1, fun i => x.1 (block i),
   fun i => code (0, (x.2.1 (block i)).1, 0), fun i => code (block i, 0, 0),
   fun i => code (0, x.2.2 (block i) (stub i).2.1, (stub i).2.1))

-- 读法：`(Labels h ℓ d).width` 等于 `h + (ℓ + d)`。
theorem width_labels (h ℓ d : ℕ) : (Labels h ℓ d).width = h + (ℓ + d) := by simp [Labels]

variable (F : Type) [Field F]

-- 读法：映射 `(fun x => x.2 x.1)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (12)` 为上界。
theorem read_one (U : Format) {t : ℕ} (hh : d ≤ t) (hl : U.width ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F 0 t (.pair (.addr d) (.vec d U)) U (fun x => x.2 x.1) 12 := by
  let A := Format.pair (.addr d) (.vec d U)
  have ha : A.width ≤ 2 ^ d * (100 + t) ^ 2 := by
    simp only [A, Format.width_pair, Format.width_vec, Format.width_addr]
    calc
      _ ≤ 2 ^ d * d + 2 ^ d * U.width := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by positivity)) _
      _ ≤ _ := by rw [← mul_add]; gcongr; ring_nf; omega
  have hi : (Perm d).width ≤ 2 ^ d * (100 + t) ^ 2 :=
    (column_width _ hh).trans (by gcongr; omega)
  -- 推导：记下中间结论 `hv`：`Cheap F d t A (Perm d) (fun x _ => x.1) 3`。
  have hv : Cheap F d t A (Perm d) (fun x _ => x.1) 3 :=
    Cheap.project F ha hi (fun j => Sum.inl j.2) (fun _ _ => rfl)
  have hs := ((Cheap.id F ha).snd.pair hv).comp (Cheap.lookup F d t U hh hl)
  have hk : U.width ≤ 2 ^ d * (100 + t) ^ 1 := by
    rw [pow_one]
    exact (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.mul_le_mul_left _ (by omega))
  have hm : (Format.vec d U).width ≤ 2 ^ d * (100 + t) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have out : Cheap F d t (.vec d U) U (fun x => x 0) 2 :=
    Cheap.project F hm hk (fun j => (0, j)) (fun _ _ => rfl)
  -- 推导：从 `(hs.comp out).mono (d := 11) (by decide)` 中取出 `m, hm, hc`。
  obtain ⟨m, hm, hc⟩ := (hs.comp out).mono (d := 11) (by decide)
  refine ⟨m, hm, hc.trans ?_⟩
  rw [pow_zero, one_mul, show 12 = 11 + 1 from rfl, pow_succ' (100 + t) 11]
  exact Nat.mul_le_mul_right _ (by omega)

-- 读法：`(Input d h e k ℓ).width` 不超过 `2 ^ (h + e) * (100 + t) ^ 2`。这里调用 `Nat.mul_le_mul_left`。
theorem input_bound (t : ℕ) (h₁ : d ≤ t) (h₂ : k ≤ t) (h₃ : ℓ ≤ t) (hd : 2 ^ d ≤ t) :
    (Input d h e k ℓ).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
  unfold Input
  rw [Format.width_pair, Format.width_pair, Format.width_vec, Format.width_bit, Format.width_vec,
    Fmt.width_occ, Format.width_vec, Format.width_vec, Format.width_addr, ← mul_add, ← mul_add,
    pow_add, mul_assoc]
  apply Nat.mul_le_mul_left
  have he : 0 < 2 ^ e := by positivity
  calc
    _ ≤ 2 ^ e * (1 + (ℓ + (1 + (d + k)) + 2 ^ d * ℓ)) := by
      simp only [mul_add]
      have := Nat.le_mul_of_pos_left ℓ he
      have := Nat.le_mul_of_pos_left (2 ^ d * ℓ) he
      omega
    _ ≤ _ := by gcongr; nlinarith only [h₁, h₂, h₃, Nat.mul_le_mul hd h₃]

-- 读法：映射 `rows` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((h + e)) * (100 + (t)) ^ (30)` 为上界。
theorem cheap_rows (d h e k ℓ t : ℕ) (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t)
    (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Input d h e k ℓ) (RowFmt (h + e) (Labels h ℓ d).width) rows 30 := by
  let A := Input d h e k ℓ
  let b i := (rowIndex h e i).1
  let j i := (rowIndex h e i).2
  let stub (x : A.obj) i := (x.2.1 (b i)).2 (j i)
  have wt := ht
  rw [Rows.overhead, width_labels] at wt
  have ha := input_bound (h := h) (e := e) t (show d ≤ t by omega) hw (show ℓ ≤ t by omega) hd
  have hc (i : ℕ) (hi : i ≤ t) : (Column (h + e) i).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 :=
    (column_width _ hi).trans (by gcongr; omega)
  -- 推导：记下中间结论 `hb`：`(Format.vec (h + e) .bit).width ≤ 2 ^ (h + e) * (100 + t) ^ 2`。
  have hb : (Format.vec (h + e) .bit).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_bit]
    exact Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  have hn : (Format.vec (h + e) (.vec d (.addr ℓ))).width ≤ 2 ^ (h + e) * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have active : Cheap F (h + e) t A (.vec (h + e) .bit) (fun x i => (stub x i).1) 3 :=
    Cheap.project F ha hb (fun z => .inr (.inl (b z.1, .inr (j z.1, .inl z.2)))) (fun _ _ => rfl)
  have thick : Cheap F (h + e) t A (.vec (h + e) .bit) (fun x i => x.1 (b i)) 3 :=
    Cheap.project F ha hb (fun z => .inl (b z.1, z.2)) (fun _ _ => rfl)
  -- 推导：记下中间结论 `label`：`Cheap F (h + e) t A (Column (h + e) ℓ) (fun x i => (x.2.1 (b i)).1) 3`。
  have label : Cheap F (h + e) t A (Column (h + e) ℓ) (fun x i => (x.2.1 (b i)).1) 3 :=
    Cheap.project F ha (hc ℓ (by omega)) (fun z => .inr (.inl (b z.1, .inl z.2))) (fun _ _ => rfl)
  have near : Cheap F (h + e) t A (Column (h + e) d) (fun x i => (stub x i).2.1) 3 :=
    Cheap.project F ha (hc d (by omega))
      (fun z => .inr (.inl (b z.1, .inr (j z.1, .inr (.inl z.2))))) (fun _ _ => rfl)
  have remote : Cheap F (h + e) t A (.vec (h + e) (.vec d (.addr ℓ))) (fun x i => x.2.2 (b i)) 3 :=
    Cheap.project F ha hn (fun z => .inr (.inr (b z.1, z.2))) (fun _ _ => rfl)
  have addr := (near.pair remote).zip.comp
    (Cheap.map (fun _ => _) (fun _ => read_one (d := d) F (.addr ℓ) (by omega) (by simp; omega) hd))
  have zero (i : ℕ) (hi : i ≤ t) : Cheap F (h + e) t A (Column (h + e) i) (fun _ _ => 0) 3 :=
    Cheap.const F ha (hc i hi) (fun _ => 0)
  have keys := cheap_keys (Labels h ℓ d) F (h + e) (show (Labels h ℓ d).width ≤ t by rw [width_labels]; omega)
  have block := Cheap.const F ha (hc h (by omega)) b
  have src := ((zero h (by omega)).pair (label.pair (zero d (by omega))).zip).zip.comp keys
  have item := (block.pair ((zero ℓ (by omega)).pair (zero d (by omega))).zip).zip.comp keys
  have dest := ((zero h (by omega)).pair (addr.pair near).zip).zip.comp keys
  exact (active.pair (thick.pair (src.pair (item.pair dest)))).mono (by decide)

-- 读法：映射 `(fun x => (rows x).control)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((h + e)) * (100 + (t)) ^ (151)` 为上界。
theorem cheap_match (d h e k ℓ t : ℕ) (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t)
    (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Input d h e k ℓ) (.pair (.vec (h + e) .bit) (Perm (h + e)))
      (fun x => (rows x).control) 151 :=
  ((cheap_rows F d h e k ℓ t ht hw hd).comp ((Rows.cheap_control F _ _).widen ht)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-!
# 按宿主和出现位置打包方案的外部比特

**英文原文**

Packing the exterior bits of a scheme by host and occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme

open Coloring
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

-- 读法：`owner` 的取值由 `i.val.1.1.1` 给出。
def owner (i : S.exposed r) : B S.m := i.val.1.1.1

-- 读法：在后续公式中，`fiber` 是 `{a : S.exposed r // S.owner r a = i}` 的缩写。
abbrev fiber (i : B S.m) := {a : S.exposed r // S.owner r a = i}

-- 读法：`load` 的取值由 `Fintype.card (S.fiber r i)` 给出。
def load (i : B S.m) := Fintype.card (S.fiber r i)

-- 读法：`Fits` 表示以下条件：`(∑ i, max 1 (S.load r i)) ≤ V` 与 `∀ i, S.load r i ≤ 2 ^ k` 同时成立。
def Fits (V k : ℕ) : Prop :=
  (∑ i, max 1 (S.load r i)) ≤ V ∧ ∀ i, S.load r i ≤ 2 ^ k

-- 读法：`spanRows` 的取值由 `S.h + S.k + S.e` 给出。
def spanRows := S.h + S.k + S.e

-- 读法：`hostSpan` 的结果类型为 `B S.m × B S.spanRows ≃ S.Span`。
def hostSpan : B S.m × B S.spanRows ≃ S.Span :=
  ((Equiv.refl _).prodCongr
    ((Match.rowIndex (S.h + S.k) S.e).trans
      ((Match.rowIndex S.h S.k).prodCongr (.refl _)))).trans (Equiv.prodAssoc _ _ _).symm

-- 读法：`spanIndex` 的取值由 `(S.hostSpan.symm p).2` 给出。
def spanIndex (p : S.Span) := (S.hostSpan.symm p).2

-- 读法：`S.spanIndex (S.hostSpan (i, t))` 等于 `t`。
-- 读法：`(S.hostSpan (i, t)).1.1` 等于 `i`。两端由定义化简为同一项。
@[simp] theorem hostSpan_owner (i : B S.m) (t : B S.spanRows) : (S.hostSpan (i, t)).1.1 = i := rfl

@[simp] theorem spanIndex_hostSpan (i : B S.m) (t : B S.spanRows) :
    S.spanIndex (S.hostSpan (i, t)) = t := by rw [spanIndex, Equiv.symm_apply_apply]

-- 读法：`S.hostSpan (p.1.1, S.spanIndex p)` 等于 `p`。使用 `S.hostSpan.apply_symm_apply` 给出的结论。
@[simp] theorem hostSpan_spanIndex (p : S.Span) : S.hostSpan (p.1.1, S.spanIndex p) = p :=
  S.hostSpan.apply_symm_apply p

-- 读法：`extent` 的取值由 `let p := S.hostSpan (i, t) if S.peer r p = none then S.width r p else 0` 给出。
def extent (i : B S.m) (t : B S.spanRows) :=
  let p := S.hostSpan (i, t)
  if S.peer r p = none then S.width r p else 0

-- 读法：`localBits` 的结果类型为 `S.fiber r i ≃ Σ t, Fin (S.extent r i t)`。
private def localBits (i : B S.m) : S.fiber r i ≃ Σ t, Fin (S.extent r i t) := by
  have he (a : S.fiber r i) : S.hostSpan (i, S.spanIndex a.val.val.1) = a.val.val.1 :=
    (congrArg (fun z => S.hostSpan (z, S.spanIndex a.val.val.1)) a.2.symm).trans
      (S.hostSpan_spanIndex _)
  let f : S.fiber r i → Σ t, Fin (S.extent r i t) := fun a =>
    ⟨S.spanIndex a.val.val.1, a.val.val.2.val, by
      unfold extent
      rw [he]
      simp only [a.val.property, ite_true]
      exact a.val.val.2.isLt⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b heq
    have h₁ : S.spanIndex a.val.val.1 = S.spanIndex b.val.val.1 := congrArg Sigma.fst heq
    have h₂ : a.val.val.2.val = b.val.val.2.val := congrArg (fun i => i.2.val) heq
    have h₃ : a.val.val.1 = b.val.val.1 := by rw [← he a, ← he b, h₁]
    exact Subtype.ext (Subtype.ext (Sigma.ext h₃ ((Fin.heq_ext_iff (congrArg _ h₃)).mpr h₂)))
  · rintro ⟨t, b⟩
    let u := S.hostSpan (i, t)
    have hb : b.val < if S.peer r u = none then S.width r u else 0 := b.isLt
    split at hb
    swap
    · omega
    rename_i hu
    let p : S.fiber r i := ⟨⟨⟨u, ⟨b.val, hb⟩⟩, hu⟩, rfl⟩
    have hp : (f p).1 = t := S.spanIndex_hostSpan _ _
    exact ⟨p, Sigma.ext hp ((Fin.heq_ext_iff (congrArg _ hp)).mpr rfl)⟩

-- 读法：`S.load r i` 等于 `∑ j, S.extent r i j`。
theorem load_eq (i : B S.m) : S.load r i = ∑ j, S.extent r i j := by
  unfold load
  rw [Fintype.card_congr (S.localBits r i), Fintype.card_sigma]
  simp

-- 读法：`serial` 的取值由 `(S.localBits r i).trans (finSigmaFinEquiv.trans (finCongr (S.load_eq r i).symm))` 给出。
/-- 同一宿主中的条目依次按块、站点、区段、区段内偏移量作字典序排列。

英文原文：Order within one host is lexicographic by block, station, span
and offset within the span.
-/
def serial (i : B S.m) : S.fiber r i ≃ Fin (S.load r i) :=
  (S.localBits r i).trans (finSigmaFinEquiv.trans (finCongr (S.load_eq r i).symm))

variable {V k : ℕ} (h : S.Fits r V k)

-- 读法：`payload` 的取值由 `⟨S.load r, h.1, h.2⟩` 给出。
def payload : Payload S.m V k := ⟨S.load r, h.1, h.2⟩

-- 读法：`index` 的取值由 `(Equiv.sigmaFiberEquiv (S.owner r)).symm.trans (Equiv.sigmaCongrRight (S.serial r))` 给出。
def index : S.exposed r ≃ (S.payload r h).Bit :=
  (Equiv.sigmaFiberEquiv (S.owner r)).symm.trans (Equiv.sigmaCongrRight (S.serial r))

-- 读法：`start` 的取值由 `∑ j with j < t, S.extent r i j` 给出。
def start (i : B S.m) (t : B S.spanRows) := ∑ j with j < t, S.extent r i j

-- 读法：`(∑ i : Fin b.val, f (i.castLE b.isLt.le))` 等于 `∑ i with i < b, f i`。这里调用 `Fintype.sum_equiv`。
private theorem strict_sum {n : ℕ} (f : Fin n → ℕ) (b : Fin n) :
    (∑ i : Fin b.val, f (i.castLE b.isLt.le)) = ∑ i with i < b, f i := by
  let e : Fin b.val ≃ {i // i < b} :=
    { toFun := fun i => ⟨i.castLE b.isLt.le, i.isLt⟩
      invFun := fun i => ⟨i.val.val, i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.sum_subtype (p := (· < b)) _ Finset.mem_filter_univ]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

-- 读法：`(S.index r h a).2.val` 等于 `S.start r (S.owner r a) (S.spanIndex a.val.1) + a.val.2.val`。
theorem index_val (a : S.exposed r) :
    (S.index r h a).2.val = S.start r (S.owner r a) (S.spanIndex a.val.1) + a.val.2.val := by
  let i := S.owner r a
  let q := S.localBits r i ⟨a, rfl⟩
  change (finSigmaFinEquiv q).val = _
  rw [finSigmaFinEquiv_apply, strict_sum]
  rfl

-- 读法：`wire` 的取值由 `(S.index r h).toEmbedding.trans (S.payload r h).wire` 给出。
def wire : S.exposed r ↪ Fmt.Port S.m V k :=
  (S.index r h).toEmbedding.trans (S.payload r h).wire

-- 读法：`store` 的取值由 `(S.payload r h).store (x ∘ (S.index r h).symm)` 给出。
def store (x : S.exposed r → Bool) : (Fmt.payload S.m V k).obj :=
  (S.payload r h).store (x ∘ (S.index r h).symm)

-- 读法：`S.store r h x (S.wire r h i)` 等于 `x i`。
@[simp] theorem read_store (x : S.exposed r → Bool) (i : S.exposed r) :
    S.store r h x (S.wire r h i) = x i := by
  simp [store, wire]

-- 读法：`y` 等于 `S.store r h x`。这里调用 `Payload.store_unique`。
theorem store_unique (x : S.exposed r → Bool) (y : (Fmt.payload S.m V k).obj)
    (hx : ∀ i, y (S.wire r h i) = x i) (hy : ∀ i ∉ Set.range (S.wire r h), y i = false) :
    y = S.store r h x := by
  apply Payload.store_unique
  · intro i
    simpa [wire] using hx ((S.index r h).symm i)
  · intro i hi
    exact hy i fun ⟨j, hj⟩ => hi ⟨S.index r h j, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# 匹配互为邻居的名称

用无序名称对作键排序，并取回具有相同键的另一行。命名自身宿主的行保持原位，因此自接触的重数可以任意。

**英文原文**

Matching reciprocal neighbor names

Sort by the unordered pair of names and return the other row with
that key. A row naming its own host stays fixed, so self-contacts
may have arbitrary multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

-- 读法：在后续公式中，`Names` 是 `Format.pair (.addr m) (.addr m)` 的缩写。
private abbrev Names (m : ℕ) := Format.pair (.addr m) (.addr m)

-- 读法：当 `z.1 < z.2` 成立时取 `z`，否则取 `z.swap`。
private def sorted {m : ℕ} (z : B m × B m) := if z.1 < z.2 then z else z.swap

-- 读法：`sorted (a, b)` 等于 `sorted (b, a)`。
private theorem sorted_swap {m : ℕ} (a b : B m) : sorted (a, b) = sorted (b, a) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [sorted, h, not_lt.mpr h.le]
  · rfl
  · simp [sorted, h, not_lt.mpr h.le]

-- 读法：映射 `sorted` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (t)) ^ (12)` 为上界。
private theorem cheap_sorted (F : Type) [Field F] {m t : ℕ} (hm : m ≤ t) :
    Cheap F 0 t (Names m) (Names m) sorted 12 := by
  have lt : Cheap F 0 t (Names m) .bit (fun z => decide (z.1 < z.2)) 3 := by
    refine ⟨_, numeric_lt F m, ?_⟩
    simp only [Format.width_pair, Format.width_addr]
    rw [Format.width_bit]
    ring_nf
    omega
  have hw : (Names m).width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [Names]; ring_nf; omega
  have a := Cheap.id F hw
  have l := (a.pair lt).comp ((cheap_select F m).widen hm)
  have r := ((a.snd.pair a.fst).pair lt).comp ((cheap_select F m).widen hm)
  convert (l.pair r).mono (d := 12) (by decide) using 1
  funext z
  obtain ⟨x, y⟩ := z
  by_cases he : x < y <;> simp [sorted, he]

variable {j m : ℕ} (host p : B j → B m)

-- 读法：`keys` 的取值由 `(Names m).keys (fun i => sorted (host i, p i))` 给出。
private def keys := (Names m).keys (fun i => sorted (host i, p i))

-- 读法：当 `host i = p i` 成立时取 `i`，否则取 `other (keys host p) i`。
private def neighbor (i : B j) :=
  if host i = p i then i else other (keys host p) i

-- 读法：`neighbor host p i` 等于 `l`。
private theorem reverse_eq
    (h : ∀ i, p i ≠ host i → ∃! l, p i = host l ∧ p l = host i)
    (i l : B j) (hi : p i ≠ host i) (hl : p i = host l ∧ p l = host i) :
    neighbor host p i = l := by
  have hn : l ≠ i := fun he => hi (he ▸ hl.1)
  have he : keys host p l = keys host p i := by
    unfold keys Format.keys
    simp only [Function.comp_apply, ← hl.1, hl.2, sorted_swap]
  rw [neighbor, ite_eq_right hi.symm]
  let t := other (keys host p) i
  -- 推导：从 `other_spec (keys host p) i` 中取出 `ht, hne`。
  obtain ⟨ht, hne⟩ := other_spec (keys host p) i
  have hti : t ≠ i := hne l he hn
  have hh : sorted (host t, p t) = sorted (host i, p i) := (Names m).serial.injective ht
  have hk : (host t = host i ∧ p t = p i) ∨ (p i = host t ∧ p t = host i) := by
    unfold sorted at hh
    split_ifs at hh <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hh <;> tauto
  rcases hk with hk | hk
  · have hn' : p l ≠ host l := by rw [hl.2, ← hl.1]; exact hi.symm
    exact (hti ((h l hn').unique ⟨hl.2.trans hk.1.symm, hk.2.trans hl.1⟩ ⟨hl.2, hl.1⟩)).elim
  · exact (h i hi).unique hk hl

-- 读法：结论为 `∃ f : (B j → B m) → B j → B j, Cheap F j (j + 3 * m + 1) (.vec j (.addr m)) (Perm j) f 200 ∧ ∀ p, (∀ i, p i ≠ host i → ∃! l, p i = host l ∧ p l = host i) → Function.Bijective (f p) ∧ ∀ i, host (f p i) = p i`。
theorem contacts (F : Type) [Field F] (j m : ℕ) (host : B j → B m) :
    ∃ f : (B j → B m) → B j → B j,
      Cheap F j (j + 3 * m + 1) (.vec j (.addr m)) (Perm j) f 200 ∧
      ∀ p, (∀ i, p i ≠ host i → ∃! l, p i = host l ∧ p l = host i) →
        Function.Bijective (f p) ∧ ∀ i, host (f p i) = p i := by
  refine ⟨neighbor host, ?_, fun p h => ?_⟩
  · let t := j + 3 * m + 1
    have hm : m ≤ t := by omega
    have hj : j ≤ t := by omega
    have hw : j + (Names m).width ≤ t := by simp [Names]; omega
    have a := column_width j hm
    have pair := ((Cheap.const F a a host).pair (Cheap.id F a)).zip
    have sort := pair.comp (Cheap.map _ (fun _ => cheap_sorted F hm))
    -- 推导：记下中间结论 `key`：`= sort.comp (cheap_keys (Names m) F j (k`。
    have key := sort.comp (cheap_keys (Names m) F j (k := t) (by omega))
    have peer := key.comp ((cheap_other F j _).widen hw)
    have eq := pair.comp (Cheap.map _ (fun _ => cheap_eq F hm))
    have self := Cheap.const F a (column_width j hj) id
    have pick := (((self.pair peer).zip.pair eq).zip.comp (Cheap.map _ (fun _ => (cheap_select F j).widen hj)))
    convert pick.mono (d := 200) (by decide) using 1
    funext p i
    simp [neighbor, keys]
  · have both (i : B j) : neighbor host p (neighbor host p i) = i ∧
        host (neighbor host p i) = p i := by
      by_cases he : p i = host i
      -- 推导：记下中间结论 `hi`：`neighbor host p i = i`。
      · have hi : neighbor host p i = i := ite_eq_left he.symm
        rw [hi, hi]
        exact ⟨rfl, he.symm⟩
      · obtain ⟨l, hl, _⟩ := h i he
        have hn : p l ≠ host l := by rw [hl.2, ← hl.1]; exact Ne.symm he
        rw [reverse_eq host p h i l he hl]
        exact ⟨reverse_eq host p h l i hn ⟨hl.2, hl.1⟩, hl.1.symm⟩
    exact ⟨Function.Involutive.bijective (fun i => (both i).1), fun i => (both i).2⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 在可变宿主的相邻位置间交换完整的块记录

每个关联邻居只需为长名称布线一次，与一条记录包含的块数无关。用于填充的邻居条目以自身宿主为名，这些条目可以重复。

**英文原文**

Exchanging full block records across a variable host

Long names are routed only once per incident neighbor, independently
of the number of blocks carried by a record. Empty neighbor entries
name their own host. They need not be distinct.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u v n m d : ℕ} {L : Set (Table F)}
  {I : Type*} (A : Format)

-- 读法：在后续公式中，`Fmt.bank` 是 `Format.vec m (.pair (.vec d (.addr m)) A)` 的缩写。
abbrev Fmt.bank (m d : ℕ) (A : Format) := Format.vec m (.pair (.vec d (.addr m)) A)

namespace Fmt

-- 读法：`Reciprocal` 的取值由 `∀ i j, (x i).1 j ≠ i → ∃! l, (x ((x i).1 j)).1 l = i` 给出。
def Reciprocal (x : (bank m d A).obj) := ∀ i j, (x i).1 j ≠ i →
  ∃! l, (x ((x i).1 j)).1 l = i

-- 读法：`gather` 的取值由 `(x ((x i).1 j)).2` 给出。
def gather (x : (bank m d A).obj) (i : B m) (j : B d) := (x ((x i).1 j)).2

end Fmt

-- 读法：在后续公式中，`Col` 是 `Format.vec (m + d) (.addr m)` 的缩写。
private abbrev Col (m d : ℕ) := Format.vec (m + d) (.addr m)
-- 读法：在后续公式中，`Vec` 是 `Format.vec (m + d) A` 的缩写。
private abbrev Vec (m d : ℕ) (A : Format) := Format.vec (m + d) A

-- 读法：`targets` 的取值由 `(x (Match.rowIndex m d j).1).1 (Match.rowIndex m d j).2` 给出。
private def targets (x : (Fmt.bank m d A).obj) (j : B (m + d)) :=
  (x (Match.rowIndex m d j).1).1 (Match.rowIndex m d j).2

-- 读法：`hosts` 的取值由 `(Match.rowIndex m d j).1` 给出。
private def hosts (m d : ℕ) (j : B (m + d)) := (Match.rowIndex m d j).1

-- 读法：存在唯一的 `l`，`targets A x i = hosts m d l` 与 `targets A x l = hosts m d i` 同时成立。这里调用 `e.injective`。
private theorem reciprocal_edges (x : (Fmt.bank m d A).obj) (h : Fmt.Reciprocal A x)
    (i : B (m + d)) (hi : targets A x i ≠ hosts m d i) :
    ∃! l, targets A x i = hosts m d l ∧ targets A x l = hosts m d i := by
  let e := Match.rowIndex m d
  obtain ⟨t, ht, hu⟩ := h (e i).1 (e i).2 hi
  refine ⟨e.symm (targets A x i, t), ?_, fun j hj => ?_⟩
  · simpa only [targets, hosts, e, Equiv.apply_symm_apply, true_and] using ht
  · apply e.injective
    rw [e.apply_symm_apply]
    refine Prod.ext hj.1.symm (hu _ ?_)
    change (x (targets A x i)).1 (e j).2 = (e i).1
    rw [hj.1]
    exact hj.2

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(Fmt.bank m d A)` 到 `(exchangeIn A (m + d))` 实现映射 `(fun x => (f (targets A x), fun j => (x (hosts m d j)).2))` 的开销至多为 `(4 * (7 * (Fmt.bank m d A).width + 2 * ((Col m d).width + (Vec m d A).width) + n))`。
private theorem packets (hu : 3 ≤ u) (f : (Col m d).obj → (Perm (m + d)).obj)
    (hf : Circuit F (Col m d) (Perm (m + d)) f n) :
    Map F u L (Fmt.bank m d A) (exchangeIn A (m + d))
      (fun x => (f (targets A x), fun j => (x (hosts m d j)).2))
      (4 * (7 * (Fmt.bank m d A).width + 2 * ((Col m d).width + (Vec m d A).width) + n)) := by
  let X := Fmt.bank m d A
  have select : Circuit F X (Col m d) (targets A) (X.width + 2 * (Col m d).width) :=
    Circuit.project (fun p => let q := Match.rowIndex m d p.1; (q.1, .inl (q.2, p.2))) (fun _ _ => rfl)
  have data : Circuit F X (Vec m d A) (fun x j => (x (hosts m d j)).2)
      (X.width + 2 * (Vec m d A).width) :=
    Circuit.project (fun p => (hosts m d p.1, .inr p.2)) (fun _ _ => rfl)
  exact (Map.circuit hu ((select.comp hf).pair data)).mono (by unfold X; omega)

-- 读法：`gatherCost` 的取值由 `4 * n + 4 * (2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200) + 1100 * 2 ^ (m + d) * (m + d + v + 1)` 给出。
def gatherCost (m d v n : ℕ) :=
  4 * n + 4 * (2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200) + 1100 * 2 ^ (m + d) * (m + d + v + 1)

-- 读法：要证明的命题是 `Computes F u L (Fmt.bank m d A) (.vec m (.vec d A)) X (fun i => Fmt.gather A (X i)) (fun _ => 1) (gatherCost m d v n)`。
theorem gather_neighbors (hu : 3 ≤ u) (ht : Access F u L (m + d) v n) (ha : A.width ≤ v)
    (X : I → (Fmt.bank m d A).obj) (hx : ∀ i, Fmt.Reciprocal A (X i)) :
    Computes F u L (Fmt.bank m d A) (.vec m (.vec d A)) X (fun i => Fmt.gather A (X i))
      (fun _ => 1) (gatherCost m d v n) := by
  obtain ⟨f, ⟨c, hf, hc⟩, he⟩ := contacts F (m + d) m (hosts m d)
  let out := Format.vec m (.vec d A)
  have post : Map F u L (exchangeOut A (m + d)) out
      (fun x i j => x ((Match.rowIndex m d).symm (i, j)))
      (4 * ((Vec m d A).width + 2 * out.width)) :=
    Map.circuit hu (Circuit.project (fun z => ((Match.rowIndex m d).symm (z.1, z.2.1), z.2.2))
      fun _ _ => rfl)
  -- 推导：记下中间结论 `pre`：`= packets (L`。
  have pre := packets (L := L) A hu f hf
  have k := pre.then_kernel (ht A ha)
  let y i j := (X i (targets A (X i) j)).2
  have relay : Computes F u L (Fmt.bank m d A) (exchangeOut A (m + d))
      X y (fun _ => 1) _ := ⟨_, k, fun i z => by
        obtain ⟨hh, hh'⟩ := he _ (reciprocal_edges A (X i) (hx i))
        have hy : (fun j => (X i (hosts m d j)).2) ∘ f (targets A (X i)) = y i :=
          funext fun j => congrArg (fun l => (X i l).2) (hh' j)
        simp only [exchange, hh, true_and, hy, eq_comm]⟩
  have h := relay.comp (Computes.of_map (x := y) post (y := fun i => Fmt.gather A (X i)) (by
    intro i; funext j l
    simp only [y, targets, Fmt.gather, Equiv.apply_symm_apply]))
  simp only [mul_one] at h
  refine h.mono ?_
  -- 推导：记下中间结论 `hc'`：`c ≤ 2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200`。
  have hc' : c ≤ 2 ^ (m + d) * (100 + (m + d + 3 * m + 1)) ^ 200 :=
    (Nat.le_add_left _ _).trans hc
  have hv : 2 ^ m * A.width ≤ 2 ^ (m + d) * v :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) ha
  have ha' := Nat.mul_le_mul_left (2 ^ (m + d)) ha
  simp only [out, Fmt.bank, Col, Vec, Format.width_vec, Format.width_pair, Format.width_addr,
    gatherCost, mul_add, ← mul_assoc, ← pow_add]
  simp only [mul_assoc]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 互反宿主图的闭邻域

游走中的任一步都可以停留原地。固定的字典枚举所有游走指令。在每个中心处，只保留每一目的地的首次出现，将之后的各次出现均替换为中心。

**英文原文**

Closed neighborhoods of a reciprocal host graph

A walk may stay put at any step. A fixed dictionary enumerates all
walk instructions. At each center keep the first occurrence of each
destination and replace every repeated occurrence by the center.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
open Coloring

-- 读法：在后续公式中，`Rows` 是 `Format.vec m (.vec d (.addr m))` 的缩写。
abbrev Rows (m d : ℕ) := Format.vec m (.vec d (.addr m))

variable {m d : ℕ} (g : B m → B d → B m)

-- 读法：逐一匹配以下输入模式：`0, x, y`、`r + 1, x, y`。
def Reach : ℕ → B m → B m → Prop
  | 0, x, y => x = y
  | r + 1, x, y => ∃ z, (z = x ∨ ∃ i, g x i = z) ∧ Reach r z y

-- 读法：要证明的命题是 `Reach g r x x`。对 `r` 作归纳。
theorem Reach.refl (r : ℕ) (x : B m) : Reach g r x x := by
  induction r with
  | zero => rfl
  | succ r ih => exact ⟨x, Or.inl rfl, ih⟩

variable {g} {r : ℕ} {x y z : B m}

-- 读法：要证明的命题是 `Reach g (r + 1) x z`。对 `r` 作归纳，并把 `x` 保持为任意参数。
theorem Reach.tail (h : Reach g r x y) (he : z = y ∨ ∃ i, g y i = z) :
    Reach g (r + 1) x z := by
  induction r generalizing x with
  | zero =>
    change x = y at h
    subst x
    exact ⟨z, he, rfl⟩
  | succ r ih =>
    obtain ⟨a, ha, h⟩ := h
    exact ⟨a, ha, ih h⟩

-- 读法：要证明的命题是 `Reach g r y x`。对 `r` 作归纳，并把 `x` 保持为任意参数。
theorem Reach.symm (h : Reach g r x y) (hg : ∀ i j, g i j ≠ i → ∃ l, g (g i j) l = i) :
    Reach g r y x := by
  induction r generalizing x with
  | zero => exact Eq.symm h
  | succ r ih =>
    obtain ⟨a, ha, h⟩ := h
    apply (ih h).tail
    by_cases he : a = x
    · exact .inl he.symm
    · obtain ⟨i, rfl⟩ := ha.resolve_left he
      exact .inr (hg _ _ he)

-- 读法：逐一匹配以下输入模式：`0`、`r + 1`。
def Walk (d : ℕ) : ℕ → Type
  | 0 => Unit
  | r + 1 => Option (B d) × Walk d r

-- 读法：逐一匹配以下输入模式：`0`、`r + 1`。
instance walkFinite (d : ℕ) : (r : ℕ) → Fintype (Walk d r)
  | 0 => inferInstanceAs (Fintype Unit)
  | r + 1 =>
    let _ := walkFinite d r
    inferInstanceAs (Fintype (Option (B d) × Walk d r))

-- 读法：逐一匹配以下输入模式：`0`、`r + 1`。
private def stay (d : ℕ) : (r : ℕ) → Walk d r
  | 0 => ()
  | r + 1 => (none, stay d r)

-- 读法：`Nonempty (Walk d r)` 的取值由 `⟨stay d r⟩` 给出。
instance (d r : ℕ) : Nonempty (Walk d r) := ⟨stay d r⟩

-- 读法：`Fintype.card (Walk d r)` 不超过 `2 ^ ((d + 1) * r)`。对 `r` 作归纳。
private theorem walk_card (d r : ℕ) : Fintype.card (Walk d r) ≤ 2 ^ ((d + 1) * r) := by
  induction r with
  | zero => exact (Fintype.card_unit).le
  | succ r ih =>
    change Fintype.card (Option (B d) × Walk d r) ≤ _
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.mul_succ, pow_add,
      Nat.mul_comm (2 ^ ((d + 1) * r))]
    apply Nat.mul_le_mul _ ih
    rw [pow_succ]
    have := Nat.two_pow_pos d
    omega

-- 读法：`code` 的结果类型为 `Walk d r ↪ B ((d + 1) * r)`。
private def code (d r : ℕ) : Walk d r ↪ B ((d + 1) * r) :=
  let e := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (walk_card d r))
  e.trans (Equiv.swap (e (stay d r)) 0).toEmbedding

-- 读法：`path` 的取值由 `Function.invFun (code d r)` 给出。
def path (d r : ℕ) := Function.invFun (code d r)

-- 读法：逐一匹配以下输入模式：`0, _, x`、`r + 1, w, x`。
def run (g : B m → B d → B m) : (r : ℕ) → Walk d r → B m → B m
  | 0, _, x => x
  | r + 1, w, x => run g r w.2 (w.1.elim x (g x))

-- 读法：`(path d r)` 是满射。
theorem path_surjective (d r : ℕ) : Function.Surjective (path d r) :=
  fun w => ⟨code d r w, Function.leftInverse_invFun (code d r).injective w⟩

-- 读法：`walks` 的取值由 `run g r (path d r i) x` 给出。
def walks (r : ℕ) (g : B m → B d → B m) (x : B m) (i : B ((d + 1) * r)) :=
  run g r (path d r i) x

-- 读法：`Reach g r x y` 与 `∃ w, run g r w x = y` 等价。对 `r` 作归纳，并把 `x` 保持为任意参数。
private theorem reach_iff : Reach g r x y ↔ ∃ w, run g r w x = y := by
  induction r generalizing x with
  | zero => exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  | succ r ih =>
    constructor
    · rintro ⟨a, ha, h⟩
      obtain ⟨w, hw⟩ := ih.mp h
      rcases ha with rfl | ⟨i, rfl⟩
      · exact ⟨(none, w), hw⟩
      · exact ⟨(some i, w), hw⟩
    · rintro ⟨⟨_|i, w⟩, hw⟩
      · exact ⟨x, Or.inl rfl, ih.mpr ⟨w, hw⟩⟩
      · exact ⟨g x i, Or.inr ⟨i, rfl⟩, ih.mpr ⟨w, hw⟩⟩

-- 读法：当 `groupFirst a i = i` 成立时取 `a i`，否则取 `x`。
def dedup {q : ℕ} (x : B m) (a : B q → B m) (i : B q) :=
  if groupFirst a i = i then a i else x

-- 读法：`expand` 的取值由 `dedup x (fun i => run g r (path d r i) x)` 给出。
def expand (r : ℕ) (g : B m → B d → B m) (x : B m) : B ((d + 1) * r) → B m :=
  dedup x (fun i => run g r (path d r i) x)

-- 读法：`expand r g x 0` 等于 `x`。这里调用 `Function.leftInverse_invFun`。
theorem origin : expand r g x 0 = x := by
  have hc : code d r (stay d r) = 0 := Equiv.swap_apply_left _ _
  have he : path d r 0 = stay d r := by
    rw [← hc]
    exact Function.leftInverse_invFun (code d r).injective _
  have hx (n : ℕ) : run g n (stay d n) x = x := by
    induction n with
    | zero => rfl
    | succ _ ih => exact ih
  simp only [expand, dedup, he, hx, ite_self]

-- 读法：`(∃ i, expand r g x i = y)` 与 `Reach g r x y` 等价。这里调用 `reach_iff.mpr`。
theorem mem : (∃ i, expand r g x i = y) ↔ Reach g r x y := by
  let a i := run g r (path d r i) x
  constructor
  · rintro ⟨i, rfl⟩
    unfold expand dedup
    split
    · exact reach_iff.mpr ⟨_, rfl⟩
    · exact Reach.refl _ _ _
  · intro h
    obtain ⟨w, hw⟩ := reach_iff.mp h
    let i := code d r w
    -- 推导：记下中间结论 `hi`：`a i = y`。
    have hi : a i = y := by
      unfold a path i
      rw [Function.leftInverse_invFun (code d r).injective]
      exact hw
    let j := groupFirst a i
    have hj : a j = a i := (first_spec a i).1
    have hfix : groupFirst a j = j := le_antisymm ((first_spec a j).2 j rfl)
      ((first_spec a i).2 _ ((first_spec a j).1.trans hj))
    exact ⟨j, (ite_eq_left hfix).trans (hj.trans hi)⟩

-- 读法：`i` 等于 `j`。这里调用 `le_antisymm`。
theorem unique {i j : B ((d + 1) * r)} (hi : expand r g x i = y) (hj : expand r g x j = y)
    (hy : y ≠ x) : i = j := by
  let a i := run g r (path d r i) x
  have least (t : B ((d + 1) * r)) (ht : expand r g x t = y) :
      a t = y ∧ ∀ v, a v = y → t ≤ v := by
    change (if groupFirst a t = t then a t else x) = y at ht
    split at ht
    next h => exact ⟨ht, fun v hv => h ▸ (first_spec a t).2 v (hv.trans ht.symm)⟩
    next => exact (hy ht.symm).elim
  exact le_antisymm ((least i hi).2 j (least j hj).1) ((least j hj).2 i (least i hi).1)

-- 读法：要证明的命题是 `Fmt.Reciprocal D (fun i => (expand r (fun j => (a j).1) i, b i))`。
theorem reciprocal {A D : Format} {a : (Fmt.bank m d A).obj} (ha : Fmt.Reciprocal A a)
    (r : ℕ) (b : B m → D.obj) :
    Fmt.Reciprocal D (fun i => (expand r (fun j => (a j).1) i, b i)) := by
  intro i j h
  let g k := (a k).1
  have he : Reach g r i (expand r g i j) := mem.mp ⟨j, rfl⟩
  obtain ⟨l, hl⟩ := mem.mpr (he.symm fun i j h => (ha i j h).exists)
  exact ⟨l, hl, fun k hk => unique hk hl (Ne.symm h)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
end
