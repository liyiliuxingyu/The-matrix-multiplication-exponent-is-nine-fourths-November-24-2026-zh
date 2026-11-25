-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Assembly.Merge.Program
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Rate
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep

/-!
若边界区段上的一个映射保持具名比特及其偏移量，则它在正长度区段上必为双射。考察偏移量零即可证明唯一性。

**英文原文**

A map on border spans that respects the named bits and their offsets
must be a bijection on positive lengths. Offset zero proves uniqueness.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} (p : S.Presentation x G) (q : U.Presentation y H)

-- 读法：存在 `i`，`(p.boundary i).val.1 = t` 与 `(p.boundary i).val.2.val = j` 同时成立。
private theorem bit_exists (t : S.Span) (j : ℕ) (hj : j < S.borderLen x t) :
    ∃ i, (p.boundary i).val.1 = t ∧ (p.boundary i).val.2.val = j := by
  unfold borderLen at hj
  split_ifs at hj with he
  · obtain ⟨i, hi⟩ := p.boundary.surjective ⟨⟨t, ⟨j, hj⟩⟩, he⟩
    exact ⟨i, by rw [hi], by rw [hi]⟩
  · omega

-- 读法：`(p.boundary i).val.2.val` 严格小于 `S.borderLen x (p.boundary i).val.1`。这里调用 `p.boundary`。
private theorem bit_lt (i : slots a ⊕ slots b) :
    (p.boundary i).val.2.val < S.borderLen x (p.boundary i).val.1 := by
  rw [S.len_at]
  exact (p.boundary i).val.2.isLt

-- 读法：结构的字段包括 `span`、`bit`。
structure Pull (f : U.Span → S.Span) : Prop where
  span : ∀ i, f (q.boundary i).val.1 = (p.boundary i).val.1
  bit : ∀ i, (q.boundary i).val.2.val = (p.boundary i).val.2.val

namespace Pull
variable {p q} {f : U.Span → S.Span} (h : p.Pull q f)

include h in
-- 读法：`s` 等于 `t`。
theorem inj {s t : U.Span} (hs : 0 < U.borderLen y s) (ht : 0 < U.borderLen y t) (e : f s = f t) :
    s = t := by
  obtain ⟨i, rfl, hi⟩ := bit_exists q s 0 hs
  obtain ⟨j, rfl, hj⟩ := bit_exists q t 0 ht
  rw [h.span, h.span] at e
  have hb := (h.bit i).symm.trans (hi.trans (hj.symm.trans (h.bit j)))
  have he : p.boundary i = p.boundary j :=
    Subtype.ext (Sigma.ext e ((Fin.heq_ext_iff (congrArg _ e)).mpr hb))
  rw [p.boundary.injective he]

-- 读法：当 `ht : 0 < S.borderLen x t` 成立时取 `(q.boundary ((p.border_pos t).mp ht).choose).val.1`，否则取 `((0, 0, 0), 0)`。
def shift (_ : p.Pull q f) (t : S.Span) : U.Span :=
  if ht : 0 < S.borderLen x t then (q.boundary ((p.border_pos t).mp ht).choose).val.1 else ((0, 0, 0), 0)

-- 读法：`0` 严格小于 `U.borderLen y (h.shift t)`。这里调用 `q.border_pos`。
theorem shift_pos (t : S.Span) (ht : 0 < S.borderLen x t) :
    0 < U.borderLen y (h.shift t) := by
  rw [shift, dite_eq_left ht]
  exact (q.border_pos _).mpr ⟨_, rfl⟩

-- 读法：`f (h.shift t)` 等于 `t`。
theorem left_inv (t : S.Span) (ht : 0 < S.borderLen x t) : f (h.shift t) = t := by
  rw [shift, dite_eq_left ht, h.span]
  exact ((p.border_pos t).mp ht).choose_spec

include h in
-- 读法：`0` 严格小于 `S.borderLen x (f s)`。这里调用 `p.border_pos`。
theorem pos (s : U.Span) (hs : 0 < U.borderLen y s) : 0 < S.borderLen x (f s) := by
  obtain ⟨i, rfl⟩ := (q.border_pos s).mp hs
  exact (p.border_pos _).mpr ⟨i, (h.span i).symm⟩

-- 读法：`h.shift (f s)` 等于 `s`。使用 `h.inj` 给出的结论。
theorem right_inv (s : U.Span) (hs : 0 < U.borderLen y s) : h.shift (f s) = s :=
  h.inj (h.shift_pos _ (h.pos s hs)) hs (h.left_inv _ (h.pos s hs))

-- 读法：`h.shift (p.boundary i).val.1` 等于 `(q.boundary i).val.1`。这里调用 `h.right_inv`。
theorem at_pin (i : slots a ⊕ slots b) :
    h.shift (p.boundary i).val.1 = (q.boundary i).val.1 := by
  rw [← h.span i]
  exact h.right_inv _ ((q.border_pos _).mpr ⟨i, rfl⟩)

-- 读法：`U.borderLen y (h.shift t)` 等于 `S.borderLen x t`。这里调用 `le_antisymm`。
theorem length (t : S.Span) (ht : 0 < S.borderLen x t) :
    U.borderLen y (h.shift t) = S.borderLen x t := by
  apply le_antisymm <;> apply le_of_not_gt
  · intro hh
    obtain ⟨i, hi, hj⟩ := bit_exists q _ _ hh
    have hb := p.bit_lt i
    rw [← h.bit i, hj, ← h.span i, hi, h.left_inv t ht] at hb
    exact hb.false
  · intro hh
    obtain ⟨i, hi, hj⟩ := bit_exists p _ _ hh
    have hb := q.bit_lt i
    rw [h.bit i, hj, ← h.at_pin i, hi] at hb
    exact hb.false

end Pull
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
目的块按原有局部地址通告其外露区段。

**英文原文**

A destination block advertises its exposed spans by their old local addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (Y : Template F)
  (k z height : ℕ)

-- 读法：在后续公式中，`carryRows` 是 `max (D.scheme.h + (A.k + A.e)) (Y.scheme.h + (k + A.spanBits Y))` 的缩写。
abbrev carryRows := max (D.scheme.h + (A.k + A.e)) (Y.scheme.h + (k + A.spanBits Y))

namespace Carry

-- 读法：在后续公式中，`Ask` 是 `Format.pair (.addr (A.transport Y k).ℓ) (.vec k A.pointer)` 的缩写。
abbrev Ask := Format.pair (.addr (A.transport Y k).ℓ) (.vec k A.pointer)
-- 读法：在后续公式中，`Reply` 是 `Format.vec k (.vec (A.spanBits Y) (SpanPlan.header (height + 1) z (A.carryRows Y k)))` 的缩写。
abbrev Reply := Format.vec k (.vec (A.spanBits Y) (SpanPlan.header (height + 1) z (A.carryRows Y k)))
-- 读法：在后续公式中，`Grid` 是 `Format.vec Y.scheme.m (.vec Y.scheme.h M)` 的缩写。
abbrev Grid (M : Format) := Format.vec Y.scheme.m (.vec Y.scheme.h M)
-- 读法：在后续公式中，`Entry` 是 `SpanPlan.entries (height + 1) z (A.carryRows Y k)` 的缩写。
abbrev Entry := SpanPlan.entries (height + 1) z (A.carryRows Y k)

-- 读法：`left` 的取值由 `(A.scheme.spanOrd i).castLE (Nat.pow_le_pow_right (by decide) (le_max_left ..))` 给出。
def left (i : A.scheme.Span) : B (A.carryRows Y k) :=
  (A.scheme.spanOrd i).castLE (Nat.pow_le_pow_right (by decide) (le_max_left ..))

-- 读法：`right` 的取值由 `((A.transport Y k).scheme.spanOrd i).castLE (Nat.pow_le_pow_right (by decide) (le_max_right ..))` 给出。
def right (i : (A.transport Y k).scheme.Span) : B (A.carryRows Y k) :=
  ((A.transport Y k).scheme.spanOrd i).castLE (Nat.pow_le_pow_right (by decide) (le_max_right ..))

-- 读法：`source` 的取值由 `((s, v.2), Fin.ofNat _ b.val)` 给出。
def source (s : B D.scheme.m) (v : A.pointer.obj) (b : B (A.spanBits Y)) : A.scheme.Span :=
  ((s, v.2), Fin.ofNat _ b.val)

-- 读法：`reply` 的结果类型为 `(Reply A Y k z height).obj`。
def reply (x : (Ask A Y k).obj) : (Reply A Y k z height).obj := fun j b =>
  let r := (A.transport Y k).decode x.1
  let w := if r.peer j b = none then r.width j b else 0
  (0, Fin.ofNat _ w, left A Y k (source A Y 0 (x.2 j) b))

end Carry
open Carry

-- 读法：`carryWidth` 的取值由 `(Ask A Y k).width + (Reply A Y k z height).width` 给出。
def carryWidth := (Ask A Y k).width + (Reply A Y k z height).width

-- 读法：`carryGate` 的取值由 `weightTable (A := Ask A Y k) (D := Reply A Y k z height) (reply A Y k z height) (fun _ => (1 : F))` 给出。
def carryGate := weightTable (A := Ask A Y k) (D := Reply A Y k z height)
  (reply A Y k z height) (fun _ => (1 : F))

-- 读法：`wd (A.carryGate Y k z height).1 + wd (A.carryGate Y k z height).2.1` 等于 `A.carryWidth Y k z height`。
theorem carry_arity : wd (A.carryGate Y k z height).1 + wd (A.carryGate Y k z height).2.1 =
    A.carryWidth Y k z height := by
  simp only [carryGate, carryWidth, weightTable, lookup, wd_word]

-- 读法：在后续公式中，`carryInput` 是 `(A.Requests Y k p).pair (A.transport Y k).format` 的缩写。
abbrev carryInput (p : ℕ) := (A.Requests Y k p).pair (A.transport Y k).format

-- 读法：`carryPrep` 的构造用到 `A.carryRows`、`A.carryInput`、`Y.scheme.m`。
def carryPrep (p : ℕ) :=
  let n := A.carryRows Y k
  1000 * ((A.carryInput Y k p).width + 2 ^ Y.scheme.m * 2 ^ Y.scheme.h * (1 + A.carryWidth Y k z height) +
    (2 ^ Y.scheme.m + 2 ^ D.scheme.m * 2 ^ z) * 2 ^ n * (110 + 4 * (z + n + height)) ^ 200 +
    SpanPlan.emitCost D.scheme.m Y.scheme.m (height + 1) z n)

-- 读法：`carryCost` 的构造用到 `A.carryPrep`、`W.shipment`、`A.transport`。
def carryCost (A : Attachment D) (Y : Template F) (k p z : ℕ)
    (x y : Wire) (height : ℕ) (W : Rounds.Contraction.Prices F) :=
  A.carryPrep Y k z height p +
    W.shipment (A.transport Y k).format.width D.scheme.m (volume x y D.scheme.m) height
      Y.scheme.m (volume x y Y.scheme.m) height z (height + 1) (A.carryRows Y k)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
直接从重定位凭据中读取外部区段地址。

**英文原文**

Exterior span addresses read directly from the relocation tickets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {k p z height : ℕ}
local notation "U" => A.transport Y k
local notation "V" => scheme (A.transport Y k)
local notation "n" => A.carryRows Y k

-- 读法：输入 `v b` 时返回 `(x.2.2 v b, (x.1.2.2 v b).2.2)`。
def ask (x : (A.carryInput Y k p).obj) : (Grid Y (Ask A Y k)).obj :=
  fun v b => (x.2.2 v b, (x.1.2.2 v b).2.2)

-- 读法：`list` 的结果类型为 `SpanPlan.Entries Y.scheme.m (height + 1) z n`。
def list (x : (Grid Y (Reply A Y k z height)).obj) : SpanPlan.Entries Y.scheme.m (height + 1) z n :=
  fun v j => if h : j.val < 2 ^ (Y.scheme.h + (k + A.spanBits Y)) then
    let t := (V).spanItem v ⟨j.val, h⟩
    x v t.1.2.1 t.1.2.2 t.2
  else (0, 0, 0)

-- 读法：`take` 的取值由 `list (A := A) (Y := Y) (k := k) (z := z) (height := height) (fun v b => reply A Y k z height (ask x v b))` 给出。
def take (z height : ℕ) (x : (A.carryInput Y k p).obj) :=
  list (A := A) (Y := Y) (k := k) (z := z) (height := height)
    (fun v b => reply A Y k z height (ask x v b))

-- 读法：`list x t.1.1 (right A Y k t)` 等于 `x t.1.1 t.1.2.1 t.1.2.2 t.2`。
theorem list_at (x : (Grid Y (Reply A Y k z height)).obj) (t : (V).Span) :
    list x t.1.1 (right A Y k t) = x t.1.1 t.1.2.1 t.1.2.2 t.2 := by
  unfold list
  have ht : (right A Y k t).val < 2 ^ (Y.scheme.h + (k + A.spanBits Y)) := ((V).spanOrd t).isLt
  rw [dite_eq_left ht]
  change (let s := (V).spanItem t.1.1 ((V).spanOrd t); x t.1.1 s.1.2.1 s.1.2.2 s.2) = _
  rw [Scheme.spanItem_spanOrd]

-- 读法：存在 `t : (V).Span`，`t.1.1 = v` 与 `right A Y k t = i` 同时成立。按 `Fin.ext` 的外延性准则比较各分量。
theorem list_cover (x : (Grid Y (Reply A Y k z height)).obj) (v : B Y.scheme.m) (i : B n)
    (hi : 0 < (list x v i).2.1.val) : ∃ t : (V).Span, t.1.1 = v ∧ right A Y k t = i := by
  unfold list at hi
  split at hi
  · rename_i he
    refine ⟨(V).spanItem v ⟨i.val, he⟩, rfl, ?_⟩
    apply Fin.ext
    change ((V).spanOrd _).val = _
    rw [Scheme.spanOrd_spanItem]
  · simp at hi

-- 读法：`pull` 的取值由 `source A Y (R.parent t.1.1) (R.flags t.1.1 t.1.2.1 t.1.2.2) t.2` 给出。
def pull (R : A.Relocation Y k) (t : (V).Span) : A.scheme.Span :=
  source A Y (R.parent t.1.1) (R.flags t.1.1 t.1.2.1 t.1.2.2) t.2

-- 读法：`pull R t` 等于 `s`。按 `Prod.ext` 的外延性准则比较各分量。
theorem pull_at (R : A.Relocation Y k) (old : A.format.obj) (t : (V).Span) (s : A.scheme.Span)
    (hk : R.kept old t.1 = some s.1) (hs : t.2 = A.outer Y s.2) : pull R t = s := by
  obtain ⟨v, hv, hp⟩ := Option.map_eq_some_iff.mp (Option.filter_eq_some_iff.mp hk).1
  unfold pull source Relocation.flags
  apply Prod.ext
  · rw [hv]
    exact hp
  · apply Fin.ext
    change t.2.val % 2 ^ A.e = s.2.val
    rw [hs]
    exact Nat.mod_eq_of_lt s.2.isLt

-- 读法：结论为 `let v := take z height (Q.requests, r) t.1.1 (right A Y k t) v.1 = 0 ∧ v.2.1.val = (V).borderLen ((U).rows r) t ∧ v.2.2 = left A Y k (pull Q.R t)`。
theorem message (Q : A.Query Y k p) (r : (U).format.obj)
    {size : ℕ} (fit : (V).Fits ((U).rows r) size height) (t : (V).Span) :
    let v := take z height (Q.requests, r) t.1.1 (right A Y k t)
    v.1 = 0 ∧ v.2.1.val = (V).borderLen ((U).rows r) t ∧ v.2.2 = left A Y k (pull Q.R t) := by
  have len : (V).borderLen ((U).rows r) t < 2 ^ (height + 1) :=
    (((V).border_le _ t).trans (fit.2 _)).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  unfold take
  rw [list_at]
  refine ⟨rfl, ?_, rfl⟩
  let label := (U).decode (r.2 t.1.1 t.1.2.1)
  let w := if label.peer t.1.2.2 t.2 = none then label.width t.1.2.2 t.2 else 0
  have eq : (V).borderLen ((U).rows r) t = w := by
    unfold Scheme.borderLen Scheme.peer
    simp only [Option.map_eq_none_iff]
    rfl
  change w % 2 ^ (height + 1) = _
  rw [← eq, Nat.mod_eq_of_lt len]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
end

/-!
目的端声明确定两份区段首部列表。

**英文原文**

A destination declaration determines the two lists of span headers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} {p : S.Presentation x G} {q : U.Presentation y H}
  {m m' w z n : ℕ}

-- 读法：输入 `c` 时返回 `take (child.symm (v, c))`。
def family (child : B m' ≃ B m × B z) (take : Entries m' w z n) (v : B m) :
    (Scatter.Family w z n).obj := fun c => take (child.symm (v, c))

-- 读法：输入 `v` 时返回 `Scatter.run (family child take v)`。
def returnTo (child : B m' ≃ B m × B z) (take : Entries m' w z n) : Entries m w z n :=
  fun v => Scatter.run (family child take v)

-- 读法：要证明的命题是 `Spec p q child h.shift (fun _ => 0) left (right ∘ h.shift) (returnTo child take) take`。
theorem spec_of_pull {f : U.Span → S.Span} (h : p.Pull q f)
    (child : B U.m ≃ B S.m × B z) (left : S.Span → B n) (right : U.Span → B n)
    (take : Entries U.m w z n)
    (hl : ∀ i, (left i).val = (S.spanOrd i).val) (hr : ∀ i, (right i).val = (U.spanOrd i).val)
    (parent : ∀ t, (child t.1.1).1 = (f t).1.1)
    (message : ∀ t, let v := take t.1.1 (right t)
      v.1 = 0 ∧ v.2.1.val = U.borderLen y t ∧ v.2.2 = left (f t))
    (cover : ∀ v i, 0 < (take v i).2.1.val → ∃ t, t.1.1 = v ∧ right t = i) :
    Spec p q child h.shift (fun _ => 0) left (right ∘ h.shift) (returnTo child take) take := by
  have owner (t) (ht : 0 < S.borderLen x t) : (child (h.shift t).1.1).1 = t.1.1 := by
    rw [parent, h.left_inv t ht]
  have incoming (v i) (hi : 0 < (take v i).2.1.val) :
      ∃ t, 0 < S.borderLen x t ∧ (h.shift t).1.1 = v ∧ right (h.shift t) = i := by
    -- 推导：从 `cover v i hi` 中取出 `s, rfl, rfl`。
    obtain ⟨s, rfl, rfl⟩ := cover v i hi
    rw [(message s).2.1] at hi
    exact ⟨f s, h.pos s hi, by rw [h.right_inv s hi], by rw [h.right_inv s hi]⟩
  have msg (t) (ht : 0 < S.borderLen x t) :
      let v := take (h.shift t).1.1 (right (h.shift t))
      v.1 = 0 ∧ v.2.1.val = S.borderLen x t ∧ v.2.2 = left t := by
    simpa only [h.left_inv t ht, h.length t ht] using message (h.shift t)
  have source (v i) (hi : 0 < (returnTo child take v i).2.1.val) :
      ∃ t, 0 < S.borderLen x t ∧ t.1.1 = v ∧ left t = i ∧
        returnTo child take v i = ((child (h.shift t).1.1).2, (take (h.shift t).1.1 (right (h.shift t))).2) := by
    -- 推导：从 `Scatter.origin (family child take v) i hi` 中取出 `c, j, hj, hk, he`。
    obtain ⟨c, j, hj, hk, he⟩ := Scatter.origin (family child take v) i hi
    obtain ⟨t, ht, hv, hj'⟩ := incoming _ _ hj
    have eq : child (h.shift t).1.1 = (v, c) := (congrArg child hv).trans (child.apply_symm_apply _)
    refine ⟨t, ht, (owner t ht).symm.trans (congrArg Prod.fst eq), ?_, ?_⟩
    · rw [← (msg t ht).2.2, hv, hj']
      exact hk
    · rw [eq, hv, hj']
      exact he
  refine ⟨owner, fun i => ⟨(h.at_pin i).symm, by simpa using h.bit i⟩, ?_, ?_, ?_, msg, ?_, incoming⟩
  · intro i j _ _ _ he
    change (left i).val < (left j).val
    rwa [hl, hl]
  · intro i j _ _ _ he
    left
    change (right (h.shift i)).val < (right (h.shift j)).val at he
    rwa [hr, hr] at he
  · intro t ht
    let c := (child (h.shift t).1.1).2
    -- 推导：记下中间结论 `he`：`child.symm (t.1.1, c) = (h.shift t).1.1`。
    have he : child.symm (t.1.1, c) = (h.shift t).1.1 := by
      rw [← owner t ht]
      exact child.symm_apply_apply _
    have hm := msg t ht
    have hv : 0 < (returnTo child take t.1.1 (left t)).2.1.val := by
      rw [← hm.2.2, ← he]
      apply Scatter.positive (family child take t.1.1) c (right (h.shift t))
      unfold family
      rw [he, hm.2.1]
      exact ht
    -- 推导：从 `source _ _ hv` 中取出 `s, hs, ho, hl', hi`。
    obtain ⟨s, hs, ho, hl', hi⟩ := source _ _ hv
    have eq : s = t := S.ext_span ho (Fin.ext ((hl s).symm.trans ((congrArg Fin.val hl').trans (hl t))))
    subst s
    rw [hi]
    exact ⟨rfl, hm.2⟩
  · intro v i hi
    obtain ⟨t, ht, hv, hj, _⟩ := source v i hi
    exact ⟨t, ht, hv, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-!
在每个父宿主上执行一次分散写入。

**英文原文**

Running a single scatter at each parent.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring

-- 读法：`returnBudget` 的取值由 `(2 ^ m' + 2 ^ m * 2 ^ z) * 2 ^ n * (110 + 4 * (z + n + w)) ^ 200` 给出。
def returnBudget (m m' w z n : ℕ) :=
  (2 ^ m' + 2 ^ m * 2 ^ z) * 2 ^ n * (110 + 4 * (z + n + w)) ^ 200

variable (F : Type) [Field F] {m m' w z n : ℕ} (child : B m' ≃ B m × B z)
local notation "H" => entries (w + 1) z n
local notation "I" => Format.vec m' H
local notation "P" => Format.vec m (Scatter.Family (w + 1) z n)
local notation "O" => Ports m m' H H
local notation "Bgt" => returnBudget m m' w z n

-- 读法：`(header (w + 1) z n).width` 不超过 `(110 + 4 * (z + n + w)) ^ 200`。
private theorem cap_header : (header (w + 1) z n).width ≤ (110 + 4 * (z + n + w)) ^ 200 := by
  calc
    _ ≤ 110 + 4 * (z + n + w) := by rw [header, Format.width_pair, Format.width_pair, Format.width_addr z, Format.width_addr (w + 1), Format.width_addr n]; omega
    _ ≤ _ := by exact Nat.le_self_pow (by decide) _

-- 读法：`(I).width` 不超过 `Bgt`。这里调用 `Nat.mul_le_mul`。
theorem return_width : (I).width ≤ Bgt := by
  simp only [entries, Format.width_vec, returnBudget, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_add_right ..)) cap_header

-- 读法：`(P).width` 不超过 `Bgt`。这里调用 `Nat.mul_le_mul`。
private theorem family_width : (P).width ≤ Bgt := by
  simp only [Scatter.Family, entries, Format.width_vec, returnBudget, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_add_left ..)) cap_header

-- 读法：在 `F` 上按格式 `I`、`O` 编码输入输出，映射 `(fun x => (returnTo child x, x))` 的电路规模至多为 `(16 * Bgt)`。这里调用 `hc.mono`。
theorem return_net : Circuit F I O (fun x => (returnTo child x, x)) (16 * Bgt) := by
  let budget := 2 ^ (Scatter.depth z n) * (110 + 4 * (z + n + w)) ^ 200
  have one : Circuit F (Scatter.Family (w + 1) z n) H Scatter.run budget := by
    obtain ⟨c, hc, ht⟩ := Scatter.cheap F (w + 1) z n
    apply hc.mono
    calc
      _ ≤ 2 ^ (Scatter.depth z n) * (100 + (4 + 3 * (z + n + (w + 1)))) ^ 200 := (Nat.le_add_left _ _).trans ht
      _ ≤ budget := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have split : Circuit F I P (family child) ((I).width + 2 * (P).width) := by
    exact Circuit.project (fun i => (child.symm (i.1, i.2.1), i.2.2)) (fun _ _ => rfl)
  have move := (split.comp (Circuit.map _ (fun _ : B m => one))).pair (Circuit.id F I)
  -- 推导：记下中间结论 `hw`：`2 ^ m * budget ≤ 2 * Bgt`。
  have hw : 2 ^ m * budget ≤ 2 * Bgt := by
    simp only [budget, Scatter.depth, returnBudget, pow_add, pow_one]
    rw [show ∀ v : ℕ, 2 ^ m * (2 * (2 ^ z * 2 ^ n) * v) = 2 * ((2 ^ m * 2 ^ z) * 2 ^ n * v) by intro v; ac_rfl]
    gcongr
    exact Nat.le_add_left ..
  have hi : (I).width ≤ Bgt := return_width
  have hp : (P).width ≤ Bgt := family_width
  exact move.mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-!
# 两种片段次序的正确性

**英文原文**

Correctness of the two fragment orders
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F) (r : S.format.obj)

-- 读法：在后续公式中，`skip` 是 `start S r q.1 q.2` 的缩写。
abbrev skip (q : S.Span) := start S r q.1 q.2

-- 读法：`pos S r false t` 严格小于 `pos S r false u`。
private theorem left_order (t u : S.Span) (h : S.spanOrd t < S.spanOrd u) :
    pos S r false t < pos S r false u := by
  simpa [pos, slot, cat, Scheme.rowIndex_lt, Scheme.spanOrd, Scheme.row] using h

-- 读法：`(scheme S).spanOrd (span S r t) < (scheme S).spanOrd (span S r u)`、`(span S r t = span S r u ∧ skip S r t + S.borderLen r t ≤ skip S r u)` 至少有一项成立。
private theorem right_order (t u : S.Span) (ht : 0 < S.borderLen r t) (hu : 0 < S.borderLen r u)
    (he : t.1.1 = u.1.1) (h : pos S r true t < pos S r true u) :
    (scheme S).spanOrd (span S r t) < (scheme S).spanOrd (span S r u) ∨
      (span S r t = span S r u ∧ skip S r t + S.borderLen r t ≤ skip S r u) := by
  obtain ⟨v, i⟩ := t
  obtain ⟨w, j⟩ := u
  simp only [pos, slot, cat, Scheme.rowIndex_lt, ite_true] at h
  have go : v.2.1 < w.2.1 ∨ v.2.1 = w.2.1 ∧
      (v.2.2 < w.2.2 ∨ v.2.2 = w.2.2 ∧ band S r v i < band S r w j) →
      (scheme S).spanOrd (span S r (v, i)) < (scheme S).spanOrd (span S r (w, j)) := by
    intro h
    simpa [Scheme.spanOrd, Scheme.row, Scheme.rowIndex_lt, span] using h
  rcases h with h|⟨a, h|⟨b, h|⟨c, h⟩⟩⟩
  · exact .inl (go (.inl h))
  · exact .inl (go (.inr ⟨a, .inl h⟩))
  · exact .inl (go (.inr ⟨a, .inr ⟨b, h⟩⟩))
  -- 推导：记下中间结论 `he'`：`v = w`。
  · have he' : v = w := Prod.ext he (Prod.ext a b)
    subst w
    have border (q : S.Span) (hq : 0 < S.borderLen r q) : S.peer r q = none := by
      by_contra hh; simp [Scheme.borderLen, hh] at hq
    refine .inr ⟨Prod.ext rfl c, ?_⟩
    rw [Scheme.borderLen, ite_eq_left (border _ ht)]
    exact ordered S r (border _ ht) (border _ hu) c h

variable [Field F] {x y : Wire} {D : Template F} {data : D.format.obj}
  {P : Rounds.Board F x y D.scheme.h} (p : D.Presents data P)
  (hl : ∀ e, P.diagram.source e ≠ P.diagram.target e) (hk : D.scheme.k = 0)

-- 读法：结论为 `let a := (p.pres.boundary i).val let b := ((present p hl hk).pres.boundary i).val b.1 = span D.scheme data.1 a.1 ∧ b.2.val = skip D.scheme data.1 a.1 + a.2.val`。对 `i` 分类讨论。
theorem boundary (i : slots x ⊕ slots y) :
    let a := (p.pres.boundary i).val
    let b := ((present p hl hk).pres.boundary i).val
    b.1 = span D.scheme data.1 a.1 ∧ b.2.val = skip D.scheme data.1 a.1 + a.2.val := by
  cases i with
  | inl i => exact ends p hl hk (.inl (.inl i))
  | inr i => exact ends p hl hk (.inr (.inl i))

include p hl hk in
-- 读法：`(scheme D.scheme).load (rows D.scheme data.1) i` 等于 `D.scheme.load data.1 i`。这里调用 `Fintype.card_congr`。
theorem load (i : B D.scheme.m) :
    (scheme D.scheme).load (rows D.scheme data.1) i = D.scheme.load data.1 i := by
  let e := ((present p hl hk).pres.boundary.symm.trans p.pres.boundary)
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv e
  intro a
  obtain ⟨t, rfl⟩ := (present p hl hk).pres.boundary.surjective a
  have he := congrArg (fun p => p.1.1) (boundary p hl hk t).1
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Iff.of_eq (congrArg (· = i) he)

-- 读法：`spec` 的证明用到 `D.scheme`、`data.1`、`S.Span`。
theorem spec {w K V : ℕ} (fit : D.scheme.Fits data.1 V K) (hw : K < w) :
    SpanPlan.Spec p.pres (present p hl hk).pres (Match.rowIndex D.scheme.m 0)
      (span D.scheme data.1) (skip D.scheme data.1) (pos D.scheme data.1 false) (pos D.scheme data.1 true)
      ((program D.scheme w).send data.1) ((program D.scheme w).take data.1) := by
  let S := D.scheme
  let r := data.1
  have width (q : S.Span) : S.borderLen r q < 2 ^ w := (S.border_le r q).trans_lt
    ((fit.2 _).trans_lt (Nat.pow_lt_pow_right (by decide) hw))
  rw [send, take]
  refine ⟨?_, boundary p hl hk, fun t u _ _ _ => left_order _ _ t u, right_order S r, ?_, ?_, ?_, ?_⟩
  · intro t _; rw [no_suffix]; rfl
  · intro t _
    rw [row_entry, no_suffix]
    exact ⟨rfl, Nat.mod_eq_of_lt (width t), rfl⟩
  · intro t _
    change let a := list S r w true t.1.1 (pos S r true t)
      a.1 = 0 ∧ a.2.1.val = S.borderLen r t ∧ a.2.2 = pos S r false t
    rw [row_entry]
    exact ⟨rfl, Nat.mod_eq_of_lt (width t), rfl⟩
  · exact row_cover S r w false
  · exact row_cover S r w true

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-!
# 将区段合并实现为精确的层变换

**英文原文**

Implementing the span merge as an exact layer transformation
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Coloring Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (L : Layer F x y)
  (hl : L.Loopless) (hk : L.template.scheme.k = 0)

local notation "D" => L.template
local notation "S" => L.template.scheme
local notation "m" => L.template.scheme.m

-- 读法：用字段 `template`、`volume`、`height`、`State` 构造 `Layer F x y`。
/-- 这一层更换表示和字典，同时保持状态、板以及分配给外部比特的空间。

英文原文：The layer changes its presentation and dictionary while preserving
the state, the board and the space allocated for exterior bits.
-/
abbrev layer : Layer F x y where
  template := template (D)
  volume := L.volume
  height := L.height
  State := L.State
  board := L.board
  data i := record (D) (L.data i)
  presents i := present (L.presents i) (hl i) hk
  fits i := by
    have he := funext (load (L.presents i) (hl i) hk)
    change (scheme (S)).Fits (rows (S) (L.data i).1) _ _
    unfold Scheme.Fits
    rw [he]
    exact L.fits i

-- 读法：要证明的命题是 `(layer L hl hk).Ready g T H θ`。
theorem ready {g T : ℕ} {H θ : ℝ} (h : L.Ready g T H θ) :
    (layer L hl hk).Ready g T H θ := h

-- 读法：要证明的命题是 `(layer L hl hk).Loopless`。
theorem loopless : (layer L hl hk).Loopless := hl

-- 读法：在后续公式中，`script` 是 `program (S) (L.height + 1)` 的缩写。
abbrev script := program (S) (L.height + 1)

-- 读法：要证明的命题是 `(L.presents i).pres.Supplies ((layer L hl hk).presents i).pres (L.fits i) ((layer L hl hk).fits i) ((script L).commands (L.data i).1)`。
theorem supplies (i : L.State) :
    (L.presents i).pres.Supplies ((layer L hl hk).presents i).pres
      (L.fits i) ((layer L hl hk).fits i) ((script L).commands (L.data i).1) := by
  have hd := spec (L.presents i) (hl i) hk (L.fits i) (Nat.lt_succ_self _)
  have h := hd.supplies (L.fits i) ((layer L hl hk).fits i)
    (Nat.lt_succ_self _) (Nat.lt_succ_self _)
  simp only [Equiv.symm_apply_apply] at h
  exact h

variable (W : Contraction.Prices F)

-- 读法：`controlCost` 的构造用到 `format.width`、`SpanProgram.cost`、`L.height`。
def controlCost := 20 * (D).format.width + (4 * cost (D) +
  (4 * ((D).format.width + 2 * (S).format.width) + SpanProgram.cost (S) 0 (L.height + 1) (dim (S))))

-- 读法：`layerCost` 的构造用到 `W.shipment`、`format.width`、`L.volume`。
def layerCost := controlCost L + W.shipment (template (D)).format.width
  m L.volume L.height m L.volume L.height 0 (L.height + 1) ((S).h + dim (S))

variable {u : ℕ} {A : Set (Table F)} (hu : 3 ≤ u)
  (size : SpanProgram.size L.template.scheme 0 (L.height + 1) (dim L.template.scheme) ≤ u)
  (gate : (script L).gate ∈ A)

include hu size gate in
-- 读法：结论为 `Computes F u A (D).format ((template (D)).format.pair (Payload.Script m m 0 (L.height + 1) ((S).h + dim (S)))) L.data (fun i => (record (D) (L.data i), (script L).commands (L.data i).1)) (fun _ => 1) (controlCost L)`。
private theorem controls :
    Computes F u A (D).format
      ((template (D)).format.pair (Payload.Script m m 0 (L.height + 1) ((S).h + dim (S))))
      L.data (fun i => (record (D) (L.data i), (script L).commands (L.data i).1))
      (fun _ => 1) (controlCost L) := by
  have rows : Circuit F (D).format (S).format Prod.fst ((D).format.width + 2 * (S).format.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have metaNet := Map.circuit (L := A) hu (record_net (D))
  have cmd := (Map.circuit (L := A) hu rows).comp ((script L).action hu size gate)
  have h := Computes.pair hu (Computes.of_map (x := L.data) (y := record (D) ∘ L.data) metaNet (fun _ => rfl))
    (Computes.of_map (x := L.data) (y := fun i => (script L).commands (L.data i).1) cmd (fun _ => rfl))
  simp only [mul_one] at h
  exact h

include hu size gate in
-- 读法：要证明的命题是 `Transforms F u A L.snapshot (layer L hl hk).snapshot (layerCost L W)`。
theorem transforms (hm : 1 ≤ m) (ht : (L.height + 1) * (2 ^ m + 2 ^ m) < 2 ^ W.w) :
    Transforms F u A L.snapshot (layer L hl hk).snapshot (layerCost L W) := by
  let J := L.State × Val x × Val y
  let Q := layer L hl hk
  have hp := (controls L hu size gate).restrict (fun i : J => i.1)
  have hs := W.ship (p := 0) (k := L.height) (k' := L.height)
    (V := L.volume) (V' := L.volume) hu hm hm (by simpa using ht)
    (y := fun i : J => Q.data i.1) (cmd := fun i : J => (script L).commands (L.data i.1).1)
    (f := fun i : J => (L.encoding.frame i.1 i.2.1 i.2.2).2)
    (g := fun i : J => (Q.encoding.frame i.1 i.2.1 i.2.2).2)
    hp (fun i b => (supplies L hl hk i.1).carries i.2.1 i.2.2 b)
  exact Transforms.deterministic id (fun _ => rfl) hs

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end

/-!
重定位生成的指令与具名边界一致。

**英文原文**

The commands generated by the relocation agree with the named boundaries.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {k p z height : ℕ}
local notation "U" => A.transport Y k
local notation "n" => A.carryRows Y k

-- 读法：`peer` 的取值由 `(Match.rowIndex m' z).symm (child.symm (Match.rowIndex m z i), 0)` 给出。
def peer {m m' z : ℕ} (child : B m' ≃ B m × B z) (i : B (m + z)) :=
  (Match.rowIndex m' z).symm (child.symm (Match.rowIndex m z i), 0)

variable (child : B Y.scheme.m ≃ B D.scheme.m × B z)

-- 读法：`commands` 的取值由 `let t := take z height i SpanPlan.emit (peer child) (SpanPlan.returnTo child t, t)` 给出。
def commands (height : ℕ) (i : (A.carryInput Y k p).obj) :
    (Payload.Script D.scheme.m Y.scheme.m z (height + 1) n).obj :=
  let t := take z height i
  SpanPlan.emit (peer child) (SpanPlan.returnTo child t, t)

variable {x y : Wire} {v v' : ℕ} (Q : A.Query Y k p) (X : A.Data x y v) (Z : Data (A.transport Y k) x y v')

-- 读法：`Preserved` 的结果类型为 `Prop`。
def Preserved : Prop := ∀ i, let j := (Z.q.pres.boundary i).val; let t := (X.q.pres.boundary i).val
  Q.R.kept Q.old j.1.1 = some t.1.1 ∧ j.1.2 = A.outer Y t.1.2 ∧ j.2.val = t.2.val

-- 读法：要证明的命题是 `X.q.pres.Supplies Z.q.pres hx hz (commands child height (Q.requests, Z.raw))`。这里调用 `spec.supplies`。
theorem supplies (hx : X.Fits height) (hz : Z.Fits height)
    (parent : ∀ i, Q.R.parent i = (child i).1) (ok : Preserved Q X Z) :
    X.q.pres.Supplies Z.q.pres hx hz (commands child height (Q.requests, Z.raw)) := by
  have h : X.q.pres.Pull Z.q.pres (pull Q.R) :=
    ⟨fun i => pull_at Q.R Q.old _ _ (ok i).1 (ok i).2.1, fun i => (ok i).2.2⟩
  have spec := SpanPlan.spec_of_pull h child (left A Y k) (right A Y k)
    (take z height (Q.requests, Z.raw)) (fun _ => rfl) (fun _ => rfl)
    (fun t => (parent t.1.1).symm) (message Q _ hz) (list_cover _)
  exact spec.supplies hx hz (Nat.lt_succ_self _) (Nat.lt_succ_self _)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
end

/-!
将重定位记录接入一份字典和两次前缀扫描。

**英文原文**

Wiring the relocation records into a single dictionary and two prefix scans.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {k p z height : ℕ}
local notation "U" => A.transport Y k
local notation "N" => A.carryRows Y k
local notation "X" => A.carryInput Y k p
local notation "I" => Ask A Y k
local notation "O" => Reply A Y k z height
local notation "T" => Format.vec Y.scheme.m (Entry A Y k z height)
local notation "C" => Payload.Script D.scheme.m Y.scheme.m z (height + 1) N

-- 读法：在 `F` 上按格式 `X`、`(Grid Y I)` 编码输入输出，映射 `ask` 的电路规模至多为 `((X).width + 2 * (Grid Y I).width)`。这里调用 `Circuit.project`。
private theorem ask_net : Circuit F X (Grid Y I) ask ((X).width + 2 * (Grid Y I).width) := by
  let tap : (Grid Y I).pins → (X).pins
    | (v, b, .inl i) => .inr (.inr (v, b, i))
    | (v, b, .inr i) => .inl (.inr (.inr (v, b, .inr (.inr i))))
  exact Circuit.project tap (by rintro _ ⟨v, b, i|i⟩ <;> rfl)

-- 读法：在 `F` 上按格式 `(Grid Y O)`、`T` 编码输入输出，映射 `list` 的电路规模至多为 `((Grid Y O).width + 34 * (T).width)`。这里调用 `Window.Tile.project_const`。
private theorem list_net : Circuit F (Grid Y O) T list ((Grid Y O).width + 34 * (T).width) := by
  let H := SpanPlan.header (height + 1) z N
  apply Window.Tile.project_const
  rintro ⟨v, j, i⟩
  by_cases h : j.val < 2 ^ (Y.scheme.h + (k + A.spanBits Y))
  · let t := (U).scheme.spanItem v ⟨j.val, h⟩
    refine .inl ⟨(v, t.1.2.1, t.1.2.2, t.2, i), ?_⟩
    intro x
    change H.code (list x v j) i = _
    rw [list, dite_eq_left h]
    rfl
  · refine .inr ⟨H.code (0, 0, 0) i, ?_⟩
    intro x
    change H.code (list x v j) i = _
    rw [list, dite_eq_right h]

omit [Field F] in
-- 读法：`(Grid Y R).width` 等于 `2 ^ Y.scheme.m * 2 ^ Y.scheme.h * R.width`。
private theorem grid_width (R : Format) : (Grid Y R).width = 2 ^ Y.scheme.m * 2 ^ Y.scheme.h * R.width := by
  rw [Grid, Format.width_vec, Format.width_vec, mul_assoc]

-- 读法：要证明的命题是 `Computes F u L X (.pair (U).format C) x (fun i => ((x i).2, commands child height (x i))) (fun _ => 1) (A.carryPrep Y k z height p)`。
theorem prepare {J : Type*} {u : ℕ} {L : Set (Table F)}
    (child : B Y.scheme.m ≃ B D.scheme.m × B z) (x : J → (X).obj)
    (hu : 3 ≤ u) (hw : A.carryWidth Y k z height ≤ u) (hg : A.carryGate Y k z height ∈ L) :
    Computes F u L X (.pair (U).format C) x (fun i => ((x i).2, commands child height (x i)))
      (fun _ => 1) (A.carryPrep Y k z height p) := by
  let r := SpanPlan.returnBudget D.scheme.m Y.scheme.m height z N
  let e := SpanPlan.emitCost D.scheme.m Y.scheme.m (height + 1) z N
  let a := 2 ^ Y.scheme.m * 2 ^ Y.scheme.h
  have one : Map F u L I O (reply A Y k z height) (1 + (I).width + (O).width) :=
    Kernel.lookup hw hg
  have all := Map.vec _ (fun _ : B Y.scheme.m => Map.vec _ (fun _ : B Y.scheme.h => one))
  -- 推导：记下中间结论 `start`：`= Map.circuit (L`。
  have start := Map.circuit (L := L) hu (ask_net (A := A) (Y := Y) (k := k) (p := p))
  have end' := (list_net (A := A) (Y := Y) (k := k) (z := z) (height := height)).comp
    ((SpanPlan.return_net F (w := height) (n := N) child).comp (SpanPlan.emit_net (peer child) F))
  have map' := (start.comp all).comp (Map.circuit hu end')
  have cmd := Computes.of_map (x := x) (y := fun i => commands child height (x i)) map' (fun _ => rfl)
  have back : Circuit F X (U).format Prod.snd ((X).width + 2 * (U).format.width) :=
    Circuit.project Sum.inr (fun _ _ => rfl)
  have keep := Computes.of_map (x := x) (L := L) (Map.circuit hu back) (fun _ => rfl)
  have both := keep.pair hu cmd
  simp only [mul_one] at both
  refine both.mono ?_
  -- 推导：记下中间结论 `he`：`(T).width ≤ r`。
  have he : (T).width ≤ r := SpanPlan.return_width
  have hy : (U).format.width ≤ (X).width :=
    (Nat.le_add_left _ _).trans_eq (Format.width_pair (A.Requests Y k p) (U).format).symm
  rw [grid_width, grid_width, ← mul_assoc (2 ^ Y.scheme.m)]
  change 20 * (X).width + (4 * ((X).width + 2 * (U).format.width)+
    (4 * ((X).width + 2 * (a * (I).width)) + a * (1 + (I).width + (O).width)+
    4 * (a * (O).width + 34 * (T).width + (16 * r + e)))) ≤
    1000 * ((X).width + a * (1 + ((I).width + (O).width)) + r + e)
  simp only [mul_add, mul_one]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
end

/-!
# 在更换挂接方式时传递外部比特

**英文原文**

Transporting exterior bits through a change of attachment
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {k p z height : ℕ}
  {x y : Wire} {v v' u : ℕ} {L : Set (Table F)} {W : Rounds.Contraction.Prices F}

-- 读法：证明中先建立 `run`，即 `= W.ship (f`。
theorem carry {I : Type*} (Q : I → A.Query Y k p) (X : I → A.Data x y v)
    (Z : I → Data (A.transport Y k) x y v')
    (hx : ∀ i, (X i).Fits height) (hz : ∀ i, (Z i).Fits height)
    (child : B Y.scheme.m ≃ B D.scheme.m × B z)
    (new : ∀ i, (Z i).raw = (Q i).result)
    (parent : ∀ i t, (Q i).R.parent t = (child t).1)
    (pins : ∀ i, Carry.Preserved (Q i) (X i) (Z i))
    (hu : 3 ≤ u) (hm : 1 ≤ D.scheme.m) (hm' : 1 ≤ Y.scheme.m)
    (ht : 2 ^ z * ((height + 1) * (2 ^ D.scheme.m + 2 ^ Y.scheme.m)) < 2 ^ W.w)
    (hw : A.carryWidth Y k z height ≤ u) (gate : A.carryGate Y k z height ∈ L) :
    Computes F u L ((A.carryInput Y k p).pair (payload x y height D.scheme.m))
      ((A.transport Y k).port x y height)
      (fun i : I × Val x × Val y => (((Q i.1).requests, (Q i.1).result), (X i.1).data (hx i.1) i.2.1 i.2.2))
      (fun i => ((Z i.1).raw, (Z i.1).data (hz i.1) i.2.1 i.2.2))
      (fun _ => 1) (A.carryCost Y k p z x y height W) := by
  let src (i : I × Val x × Val y) : (A.carryInput Y k p).obj := ((Q i.1).requests, (Z i.1).raw)
  let a (i : I × Val x × Val y) := (X i.1).data (hx i.1) i.2.1 i.2.2
  let b (i : I × Val x × Val y) := (Z i.1).data (hz i.1) i.2.1 i.2.2
  have prep := Carry.prepare child src hu hw gate
  have ok (i : I) := Carry.supplies child (Q i) (X i) (Z i) (hx i) (hz i) (parent i) (pins i)
  -- 推导：记下中间结论 `run`：`= W.ship (f`。
  have run := W.ship (f := a) (g := b) hu hm hm' (by simpa only [max_self] using ht) prep
    (fun i out => (ok i.1).carries i.2.1 i.2.2 out)
  simp only [← new]
  exact run

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# 合并已还原层的成本

每个宿主只计一次全局地址比较的成本。块的开销仅取决于局部标签与宽度，外部体量前的系数与标签字母表无关。

**英文原文**

Cost of merging the restored layer

Charge global address comparisons once per host. The block charge
uses only local labels and widths, and the coefficient on exterior
volume is independent of the label alphabet.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
open Rounds Rounds.Contraction BatchDescent.Phase

variable (i : Restore.Measure)
-- 读法：在后续公式中，`sites` 是 `i.m + i.l` 的缩写。
private abbrev sites := i.m + i.l
-- 读法：在后续公式中，`bits` 是 `i.h + i.snd + 1` 的缩写。
private abbrev bits := i.h + i.snd + 1
-- 读法：在后续公式中，`lanes` 是 `5 + (1 + i.A.e)` 的缩写。
private abbrev lanes := 5 + (1 + i.A.e)
-- 读法：在后续公式中，`rank` 是 `i.h + lanes i` 的缩写。
private abbrev rank := i.h + lanes i
-- 读法：在后续公式中，`label` 是 `(Restore.script i.A.scheme).width` 的缩写。
private abbrev label := (Restore.script i.A.scheme).width

-- 读法：`gateSize` 的取值由 `label i + i.h + 2 * 2 ^ (lanes i) * (bits i + rank i)` 给出。
private def gateSize := label i + i.h + 2 * 2 ^ (lanes i) * (bits i + rank i)

-- 读法：`hostCost` 的取值由 `776 * sites i + 1224 + 8 * (100 + sites i + 8) ^ 24 + 560 * bits i` 给出。
private def hostCost := 776 * sites i + 1224 + 8 * (100 + sites i + 8) ^ 24 + 560 * bits i

-- 读法：本声明给出 `blockCost` 的构造。
private def blockCost :=
  285 * label i + 289 + 137 * i.h + 26 * 2 ^ (lanes i) * (bits i + rank i) +
    8 * 2 ^ (lanes i) * (100 + (2 * rank i + bits i)) ^ 140 + 840 * 2 ^ (lanes i) * bits i

-- 读法：结论为 `SpanProgram.size L.template.scheme 0 (L.height + 1) (dim L.template.scheme) = gateSize i ∧ controlCost L + 4 * (template L.template).format.width = 2 ^ (sites i) * hostCost i + 2 ^ (sites i + i.h) * blockCost i`。
private theorem costs {x y : Wire} (L : Layer i.F x y) (u : ℕ)
    (ht : L.template = (Restore.result i.A i.N i.r i.s u).sweep) (hh : L.height = i.h + i.snd) :
    SpanProgram.size L.template.scheme 0 (L.height + 1) (dim L.template.scheme) = gateSize i ∧
    controlCost L + 4 * (template L.template).format.width =
      2 ^ (sites i) * hostCost i + 2 ^ (sites i + i.h) * blockCost i := by
  have hm : L.template.scheme.m = sites i := by rw [ht]
  have hH : L.template.scheme.h = i.h := by rw [ht]
  have hd : L.template.scheme.d = 3 := by rw [ht]
  have he : dim L.template.scheme = lanes i := by
    rw [ht]; change 0 + (3 + 2 + (1 + i.A.e)) = _; rw [zero_add]
  -- 推导：记下中间结论 `hL`：`L.template.scheme.ℓ = label i`。
  have hL : L.template.scheme.ℓ = label i := by rw [ht]
  have hc : L.template.count = label i := by rw [ht]
  have hbits : L.height + 1 = bits i := by rw [hh]
  constructor
  · simp only [SpanProgram.size_eq, hL, hbits, he, hH, pow_zero, zero_add, gateSize, rank]; rfl
  have width : (template L.template).format.width =
      2 ^ (sites i) * (8 * (sites i + 2) + 2 + 2 ^ i.h * (label i + 24 + label i)) := by
    rw [Template.width]
    change 2 ^ L.template.scheme.m *
      (2 ^ L.template.scheme.d * (L.template.scheme.m + 2) + 2 +
        2 ^ L.template.scheme.h * ((scheme L.template.scheme).ℓ + L.template.count)) = _
    rw [label_width, hm, hd, hH, hL, hc]
    rfl
  unfold controlCost cost
  rw [width, Template.width, SpanProgram.price, SpanPlan.emit_price]
  have form : L.template.scheme.format.width =
      2 ^ L.template.scheme.m * (2 ^ L.template.scheme.d * L.template.scheme.m +
        2 ^ L.template.scheme.h * L.template.scheme.ℓ) := by
    simp [Scheme.format, Fmt.rows]
  rw [form, he, hL, hc, hbits, hm, hH, hd]
  simp only [hostCost, blockCost, rank, zero_add, add_zero, pow_add, pow_zero,
    show 2 ^ 3 = 8 by decide]
  generalize (100 + sites i + 8) ^ 24 = a, (100 + (2 * (i.h + lanes i) + bits i)) ^ 140 = b
  ring

-- 读法：`outer` 的取值由 `1000 + i.c.W + (i.h + i.snd) + (i.h + i.snd) + bits i + rank i` 给出。
private def outer := 1000 + i.c.W + (i.h + i.snd) + (i.h + i.snd) + bits i + rank i
-- 读法：`long` 的取值由 `outer i + sites i + sites i + i.c.w + i.c.w ^ i.c.power` 给出。
private def long := outer i + sites i + sites i + i.c.w + i.c.w ^ i.c.power
-- 读法：`host` 的取值由 `2 ^ i.l * (hostCost i + 2 * (long i) ^ j + 2 * (outer i) ^ j)` 给出。
private def host (j : ℕ) := 2 ^ i.l * (hostCost i + 2 * (long i) ^ j + 2 * (outer i) ^ j)
-- 读法：`block` 的取值由 `2 ^ i.l * (blockCost i + 2 * 2 ^ (lanes i) * (outer i) ^ j)` 给出。
private def block (j : ℕ) := 2 ^ i.l * (blockCost i + 2 * 2 ^ (lanes i) * (outer i) ^ j)

-- 读法：证明中先建立 `hm`，即 `L.template.scheme.m = sites i`。
private theorem certificate : ∃ j, ∀ (i : Restore.Measure) {x y : Wire} (L : Layer i.F x y) (u : ℕ),
    L.template = (Restore.result i.A i.N i.r i.s u).sweep →
    L.volume = Attachment.volume x y (i.m + i.l) → L.height = i.h + i.snd →
    layerCost L i.c ≤ 2 ^ i.m * host i j + 2 ^ (i.m + i.h) * block i j + (wd x + wd y) * (2 * (outer i) ^ j) := by
  obtain ⟨j, hj⟩ := Prices.shipment_bound
  refine ⟨j, fun i {x y} L u ht hv hh => ?_⟩
  let w := (template L.template).format.width
  have hm : L.template.scheme.m = sites i := by rw [ht]
  have hH : L.template.scheme.h = i.h := by rw [ht]
  have he : dim L.template.scheme = lanes i := by
    rw [ht]; change 0 + (3 + 2 + (1 + i.A.e)) = _; rw [zero_add]
  have hc := (costs i L u ht hh).2
  have h := hj i.F i.c w (sites i) L.volume (i.h + i.snd) (sites i) L.volume (i.h + i.snd)
    0 (bits i) (rank i)
  simp only [add_zero, pow_zero, mul_one] at h
  unfold layerCost
  rw [he, hm, hH, hh]
  refine (Nat.add_le_add_left h _).trans_eq ?_
  rw [←add_assoc, ←add_assoc, hc]
  change 2 ^ (sites i) * hostCost i + 2 ^ (sites i + i.h) * blockCost i +
    (2 ^ (sites i) + 2 ^ (sites i)) * ((long i) ^ j + 2 ^ (rank i) * (outer i) ^ j) +
      (L.volume + L.volume) * (outer i) ^ j = _
  rw [hv]
  unfold host block sites rank Attachment.volume
  simp only [pow_add]
  ring

open Restore.Measure

-- 读法：`Fast gateSize` 与 `Slow hostCost ∧ Fast blockCost ∧ Fast (fun i => 2 ^ (lanes i))` 同时成立。这里调用 `Poly.exp_add`。
private theorem sizes : Fast gateSize ∧ Slow hostCost ∧ Fast blockCost ∧ Fast (fun i => 2 ^ (lanes i)) := by
  have a : Fast bits := small_num fun i => by unfold bits Restore.Measure.outer; omega
  have b : Fast (fun i => 2 ^ (lanes i)) := by
    have hh : Fast (fun i => 2 ^ (1 + i.A.e)) := lines.mono fun i =>
      Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
    exact Poly.exp_add (f := fun _ => 5) (constant 32) hh
  have c : Fast rank := height.add b.of_exp
  have d : Slow sites := hosts.add hardware.slow
  have C := constant
  have L j := (constant j).slow
  refine ⟨(script_size.add height).add (((C 2).mul b).mul (a.add c)), ?_, ?_, b⟩
  · have t := ((L 776).mul d).add (L 1224)
    exact (t.add ((L 8).mul ((((L 100).add d).add (L 8)).pow 24))).add ((L 560).mul a.slow)
  · have t := (((C 285).mul script_size).add (C 289)).add ((C 137).mul height)
    have y := ((C 26).mul b).mul (a.add c)
    have z := ((C 8).mul b).mul (((C 100).add (((C 2).mul c).add a)).pow 140)
    exact ((t.add y).add z).add (((C 840).mul b).mul a)

-- 读法：`Slow (fun i => host i j)` 与 `Fast (fun i => block i j) ∧ Poly Restore.Measure.outer (fun i => 2 * (outer i) ^ j)` 同时成立。这里调用 `t.mono`。
private theorem bounds (j : ℕ) :
    Slow (fun i => host i j) ∧ Fast (fun i => block i j) ∧ Poly Restore.Measure.outer (fun i => 2 * (outer i) ^ j) := by
  have s : Poly Restore.Measure.outer outer := by
    have t := (Poly.const two 5).mul (Poly.of_le two (fun _ => le_rfl))
    apply t.mono
    intro i
    unfold outer bits rank lanes Restore.Measure.outer Restore.Measure.n Restore.lineBits
    omega
  have sf : Fast outer := s.grow small
  have r : Slow long := by
    have t := (constant 8).slow.mul (Poly.of_le long_two (fun _ => le_rfl))
    apply t.mono
    intro i
    have h := i.small
    have h' := Nat.zero_le (i.c.w ^ i.c.power)
    unfold long outer bits rank lanes sites Restore.Measure.long
    unfold Restore.Measure.outer Restore.Measure.n Restore.lineBits at h
    omega
  have C := constant 2
  have h := sizes
  exact ⟨Restore.Measure.copies.slow.mul ((h.2.1.add (C.slow.mul (r.pow j))).add (C.slow.mul (sf.slow.pow j))),
    Restore.Measure.copies.mul (h.2.2.1.add ((C.mul h.2.2.2).mul (sf.pow j))), (Poly.const two 2).mul (s.pow j)⟩

-- 读法：`price` 的证明用到 `sizes.1.bound`、`i.long_two`、`i.short_two`。
/-- 标记、控制与传输三项开销都可由同一个多项式控制。

英文原文：A common polynomial suffices for labeling, control and transport.
-/
theorem price : ∃ K, ∀ (i : Restore.Measure) {x y : Wire} (L : Layer i.F x y) (u : ℕ),
    L.template = (Restore.result i.A i.N i.r i.s u).sweep →
    L.volume = Attachment.volume x y (i.m + i.l) → L.height = i.h + i.snd →
    SpanProgram.size L.template.scheme 0 (L.height + 1) (dim L.template.scheme) ≤ i.short ^ K ∧
    layerCost L i.c ≤ 2 ^ i.m * i.long ^ K + 2 ^ (i.m + i.h) * i.short ^ K + (wd x + wd y) * i.outer ^ K := by
  obtain ⟨j, hj⟩ := certificate
  obtain ⟨f, hf⟩ := sizes.1.bound
  obtain ⟨t, ht⟩ := (bounds j).1.bound
  obtain ⟨s, hs⟩ := (bounds j).2.1.bound
  obtain ⟨o, ho⟩ := (bounds j).2.2.bound
  refine ⟨f + t + s + o, fun i {x y} L u h hv hh => ?_⟩
  have hl := i.long_two
  have hb := i.short_two
  have he := i.two
  rw [(costs i L u h hh).1]
  refine ⟨(hf i).trans (Nat.pow_le_pow_right (by omega) (by omega)), (hj i L u h hv hh).trans ?_⟩
  gcongr
  · exact (ht i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (hs i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (ho i).trans (Nat.pow_le_pow_right (by omega) (by omega))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Merge
end
