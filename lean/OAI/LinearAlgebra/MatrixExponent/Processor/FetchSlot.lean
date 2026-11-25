-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Processor.PinIndexRead
import OAI.LinearAlgebra.MatrixExponent.Processor.Slots
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases
import OAI.LinearAlgebra.MatrixExponent.Processor.LocalBank

/-!
# 在任一端点读取原有的物理比特

**英文原文**

Reading old physical bits at either endpoint
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Diagonal
variable {N l r : ℕ}

-- 读法：`value` 的取值由 `Sum.elim (Pin.literal y u) (Sum.elim (Pin.broadcast y) (Links.view u (Pin.link y)))` 给出。
def value (y : Pin N l l r → Bool) (u : Fin (3 * r)) : Machine.Ports N l l → Bool :=
  Sum.elim (Pin.literal y u) (Sum.elim (Pin.broadcast y) (Links.view u (Pin.link y)))

-- 读法：`number` 的结果类型为 `Option (Fin (3 * r))`。
/-- 匹配 `a` 将 `u` 与 `a-u` 配对，缺失的自连接除外。

英文原文：Matching `a` pairs `u` with `a-u`, except for a missing self-link.
-/
def number (k : Kind r) (u : Fin (3 * r)) : Option (Fin (3 * r)) :=
  match k with
  | .empty => none
  | .literal => some u
  | .broadcast => some ⟨0, u.pos⟩
  | .link a => if u = a - u then none else some (min u (a - u))

-- 读法：`kind (r := r) (l := l) (some (.inr (.inr h)))` 等于 `.link (e.1.val.1 + e.1.val.2)`。
private theorem match_of_address (e : Links.Slot (3 * r) N) (h : Fin (N / 4))
    (he : Links.address e = h) : kind (r := r) (l := l) (some (.inr (.inr h))) =
      .link (e.1.val.1 + e.1.val.2) := by
  subst h
  let k := finProdFinEquiv (e.1.val.1 + e.1.val.2, e.2)
  have hp : (Links.address e).val < 3 * r * (N / (4 * (3 * r))) := k.isLt
  have hk : (⟨(Links.address e).val, hp⟩ : Fin _) = k := rfl
  simp [kind, hp, hk, k]

-- 读法：`number (kind (l := l) (some (.inr (.inr (Links.address e))))) u` 等于 `some e.1.val.1`。
private theorem covered (u : Fin (3 * r)) (e : Links.Slot (3 * r) N) (he : Links.sees u e.1) :
    number (kind (l := l) (some (.inr (.inr (Links.address e))))) u = some e.1.val.1 := by
  let _ : NeZero (3 * r) := ⟨u.pos.ne'⟩
  rw [match_of_address e _ rfl]
  have h := e.1.property
  rcases he with rfl | rfl <;> simp [number, h.ne, h.ne', min_eq_left h.le, min_eq_right h.le]

-- 读法：存在 `e : Links.Slot (3 * r) N`，`Links.sees u e.1` 与 `Links.address e = p ∧ e.1.val.1 = j` 同时成立。按 `p.val < 3 * r * (N / (4 * (3 * r)))` 成立与否分情况。
private theorem has_position (u j : Fin (3 * r)) (p : Fin (N / 4))
    (he : number (kind (l := l) (some (.inr (.inr p)))) u = some j) :
    ∃ e : Links.Slot (3 * r) N, Links.sees u e.1 ∧ Links.address e = p ∧ e.1.val.1 = j := by
  let _ : NeZero (3 * r) := ⟨u.pos.ne'⟩
  by_cases hp : p.val < 3 * r * (N / (4 * (3 * r)))
  swap; · simp [kind, hp, number] at he
  let z := finProdFinEquiv.symm (⟨p.val, hp⟩ : Fin (3 * r * (N / (4 * (3 * r)))))
  let v := z.1 - u
  simp only [kind, dite_eq_left hp, number] at he
  change (if u = v then none else some (min u v)) = some j at he
  have hn : u ≠ v := by intro h; rw [ite_eq_left h] at he; contradiction
  rw [ite_eq_right hn, Option.some.injEq] at he
  -- 推导：记下中间结论 `hi`：`min u v < max u v`。
  have hi : min u v < max u v := by grind
  let e : Links.Slot (3 * r) N := (⟨(min u v, max u v), hi⟩, z.2)
  refine ⟨e, ?_, Fin.ext ?_, he⟩
  · change u = min u v ∨ u = max u v
    grind
  · change (finProdFinEquiv (min u v + max u v, z.2)).val = p.val
    rw [min_add_max, show u + v = z.1 by simp [v]]
    exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply _)

-- 读法：结论为 `match number (kind (some p)) u with`。
theorem number_spec (y : Pin N l l r → Bool) (u : Fin (3 * r)) (p : Machine.Ports N l l) :
    match number (kind (some p)) u with
    | none => value y u p = false
    | some j => ∃ q, prior p j = some q ∧ value y u p = y q := by
  rcases p with k | k | k
  · exact ⟨.inl (u, k), rfl, rfl⟩
  · exact ⟨.inr (.inl k), rfl, rfl⟩
  · cases he : number (kind (l := l) (some (.inr (.inr k)))) u with
    | some j =>
      obtain ⟨e, hu, rfl, rfl⟩ := has_position u j k he
      exact ⟨.inr (.inr e), prior_old (l := l) (.inr (.inr e)) _ rfl, Links.view_address u (Pin.link y) e hu⟩
    | none =>
      have hh : ¬∃ s : {s : Links.Slot (3 * r) N // Links.sees u s.1}, Links.address s.val = k := by
        rintro ⟨s, rfl⟩
        rw [covered u s.val s.property] at he
        contradiction
      change Links.view u (Pin.link y) k = false
      exact Function.extend_apply' (fun s => Pin.link y s.val) (fun _ => false) _ hh

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 检验与接收紧凑编号引脚的成本

**英文原文**

Cost of testing and receiving compactly indexed pins
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Controller Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n} (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (hb : 100 * N ≤ 2 ^ w)
  [NeZero r] [NeZero (3 * r)] [NeZero (N / 4)] [LinearOrder (Name n r)]
  (idx : Name n r ↪ Coloring.B w) (cell : Coloring.B w → Domain N l r)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

include hw hi hb idx in
-- 读法：证明中先建立 `hk`，即 `= packed_query (i`。
theorem packed_pins :
    packed (U := raw _) F C.input (fun (s : X) j => (decode s (cell j)).isSome.toNat) 512 ∧
    packed (U := raw _) F C.input (fun (s : X) j => (shared s (cell j)).toNat) 512 ∧
    packed (U := raw _) F C.input (fun (s : X) j => (expected C s (cell j)).toNat) 512 := by
  let k (s : X) j := query s (cell j)
  let off (s : X) j := placeInClass P.colors (cellPort s (cell j))
  have hk := packed_query (i := i) C hw hi hb cell idx
  have ho := packed_port (i := i) C hw hi hb cell (placeInClass P.colors)
  have hget := C.packed_get hw hi k idx off hk (ho.mono (by decide))
  have hstatus : packed (U := raw _) F C.input (fun (s : X) j => status s (cell j)) 188 :=
    C.packed_pair hw hi k idx hk state
  -- 推导：记下中间结论 `hm`：`= packed_mark (i`。
  have hm := packed_mark (i := i) C hw hi hb cell
  have hw' : 12 ≤ 2 ^ w := by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega
  have hmark (s : X) j : mark s (cell j) < 4 := by
    unfold mark
    rw [mode_spec]
    split
    · decide
    · unfold tag; split <;> decide
  have hstate (s : X) j : status s (cell j) < 3 := by
    simp only [status, state]
    split_ifs <;> decide
  -- 推导：记下中间结论 `H`：`= packed.binary activity (m`。
  have H := packed.binary activity (m := 4) (n := 3) hw' hm hstatus hmark hstate
  have val (s : X) j : activity (mark s (cell j)) (status s (cell j)) < 3 := by
    rw [activity_eq]
    split_ifs <;> decide
  have hfit : fits (fun (s : X) j => activity (mark s (cell j)) (status s (cell j))) :=
    fun s j => (val s j).trans_le (by omega)
  have hs (s : X) j : (decode s (cell j)).isSome = false → shared s (cell j) = false := by
    unfold shared
    cases decode s (cell j) <;> simp
  refine ⟨?_, ?_, ?_⟩
  · convert (H.unary hfit (fun k => if k = 0 then 0 else 1)).mono (n := 512) (by decide) using 1
    funext s j
    rw [activity_eq]
    cases (decode s (cell j)).isSome <;> cases shared s (cell j) <;> rfl
  · convert (H.unary hfit (fun k => if k = 2 then 1 else 0)).mono (n := 512) (by decide) using 1
    funext s j
    rw [activity_eq]
    cases he : (decode s (cell j)).isSome
    · rw [hs s j he]; rfl
    · cases shared s (cell j) <;> rfl
  -- 推导：记下中间结论 `hl`：`= packed.binary (fun k x => if k = 2 then x else 0) (m`。
  · have hl := packed.binary (fun k x => if k = 2 then x else 0) (m := 3) (n := 2)
      (by omega) H hget val (fun s j => by cases get w s (k s j) (off s j) <;> decide)
    convert hl.mono (n := 512) (by decide) using 1
    funext s j
    rw [expected_eq s C hw.bits, activity_eq]
    cases he : (decode s (cell j)).isSome
    · rw [hs s j he]; rfl
    · cases shared s (cell j) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 候选槽位比特的活动性与传输检验

**英文原文**

The activity and transfer checks for candidate slot bits
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.SlotKey
open Diagonal Controller Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "D" => SlotKey.Domain n r (B * P.count) h

-- 读法：`edge` 的取值由 `.inr (.inl (expand hn i (workerAt s) t))` 给出。
def edge (s : X) (t : D) : Edge P B := .inr (.inl (expand hn i (workerAt s) t))

-- 读法：`active` 的取值由 `decide (incident s (edge s t))` 给出。
def active (s : X) (t : D) := decide (incident s (edge s t))

-- 读法：`shared` 的取值由 `decide (incident s (edge s t) ∧ source s (edge s t) ≠ target s (edge s t))` 给出。
def shared (s : X) (t : D) := decide (incident s (edge s t) ∧ source s (edge s t) ≠ target s (edge s t))

variable [LinearOrder (Name n r)] [NeZero (N / 4)] [NeZero (3 * r)]

-- 读法：`expected` 的取值由 `Controller.get w s (Controller.key P B (edge s t)) (t.2.2.val + h * t.2.1.val)` 给出。
def expected (w : ℕ) (s : X) (t : D) : Bool :=
  Controller.get w s (Controller.key P B (edge s t)) (t.2.2.val + h * t.2.1.val)

omit [NeZero (3 * r)] in
-- 读法：`expected w s t` 等于 `C.numberInOrder.physicalBit s (edge s t) 0`。
theorem expected_eq (hw : N ≤ 2 ^ w) (s : X) (t : D) (hs : shared s t = true) :
    expected w s t = C.numberInOrder.physicalBit s (edge s t) 0 := by
  obtain ⟨hi, hn⟩ := of_decide_eq_true hs
  have he : width s (edge s t) = 1 := rfl
  have hf : source s (edge s t) ≠ target s (edge s t) ∧ incident s (edge s t) ∧ 0 < width s (edge s t) :=
    ⟨hn, hi, he.ge⟩
  rw [physicalBit, dite_eq_left hf, C.get_eq hw]
  simp only [he, mul_one, add_zero]
  rfl

-- 读法：这里调用 `le_trans`。
theorem packed_slots (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (hc : 3 * r * Fintype.card (Name n r) ≤ 2 ^ w)
    (idx : Name n r ↪ Coloring.B w) (cell : Coloring.B w → D) :
    packed (U := raw _) F (C.input (i := i)) (fun s j => (active s (cell j)).toNat) 129 ∧
    packed (U := raw _) F (C.input (i := i)) (fun s j => (shared s (cell j)).toNat) 129 ∧
    packed (U := raw _) F (C.input (i := i)) (fun s j => (expected w s (cell j)).toNat) (37 + 250) := by
  let keys (s : X) (j : Coloring.B w) := Controller.key P B (edge s (cell j))
  have hsize : 3 * r * Fintype.card (Fin (count n r)) ≤ 2 ^ w := by
    apply le_trans _ hc
    apply Nat.mul_le_mul_left
    rw [Fintype.card_fin]
    refine (Nat.div_le_self _ _).trans ?_
    exact Fintype.card_le_of_injective (fun k : SlotKey n r => (Sum.inr (.inl k) : Name n r))
      (fun _ _ h => Sum.inl.inj (Sum.inr.inj h))
  have hk : packed (U := raw _) F (C.input (i := i)) (fun s j => (idx (keys s j)).val) 37 :=
    C.workerTable hw hi (fun j => (cell j).1) hsize
      (fun u t => (idx (.inr (.inl (enumerate hn i ((Worker.index r).symm u) t).val))).val)
  have ht := C.packed_pair hw hi keys idx hk
  have ha := ht (fun u x y => (decide (x = u ∨ y = u)).toNat)
  have hs := ht (fun u x y => (decide ((x = u ∨ y = u) ∧ x ≠ y)).toNat)
  simp only [keys, ends_eq] at ha hs
  refine ⟨ha, hs, ?_⟩
  -- 推导：记下中间结论 `he`：`= packed.const (U`。
  have he := packed.const (U := raw _) F (C.input (i := i)) (fun j => (cell j).2.2.val + h * (cell j).2.1.val)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  exact C.packed_get hw hi keys idx _ hk (he.mono (by decide))

end OAI.LinearAlgebra.MatrixExponent.Processor.SlotKey
end

/-!
# 各工作单元与所有可行报告共用的固定私有带

**英文原文**

A fixed private tape shared by all workers and feasible reports
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w k : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：在后续公式中，`Guess` 是 `PinIndex.Domain N l r ⊕ SlotKey.Domain n r (B * P.count) h` 的缩写。
abbrev Guess (P : Format N l d n r h) (B : ℕ) :=
  PinIndex.Domain N l r ⊕ SlotKey.Domain n r (B * P.count) h

-- 读法：在后续公式中，`XIn` 是 `Machine.Ports N l l ⊕ Guess P B` 的缩写。
abbrev XIn (P : Format N l d n r h) (B : ℕ) := Machine.Ports N l l ⊕ Guess P B

-- 读法：在后续公式中，`WithGuess` 是 `Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i × (Guess P B → Bool)` 的缩写。
abbrev WithGuess (P : Format N l d n r h) (A : Expansion F n h) (hn : 2 ≤ n)
    (M : Bank (Fin n)) (B : ℕ) (i : Fin n) :=
  Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i × (Guess P B → Bool)

-- 读法：`tapeIn` 的取值由 `Sum.elim (C.input z.1) z.2` 给出。
def tapeIn (z : WithGuess P A hn M B i) : XIn P B → Bool := Sum.elim (C.input z.1) z.2

-- 读法：要证明的命题是 `packed (U := raw _) F C.tapeIn (fun z => f z.1) (k + 2)`。使用 `hf.lift` 给出的结论。
theorem lift (hx : Fintype.card (XIn P B) ≤ 2 ^ w) {f : Array X w}
    (hf : packed (U := raw _) F C.input f k) :
    packed (U := raw _) F C.tapeIn (fun z => f z.1) (k + 2) :=
  hf.lift C.tapeIn Prod.fst Sum.inl hx (fun _ => rfl)

-- 读法：`collect` 的取值由 `Equiv.subtypeSum.toEmbedding.trans (p.sumMap (SlotKey.encode s))` 给出。
def collect (s : X) (p : {e : Pin N l l r // incident s (.inl e)} ↪ PinIndex.Domain N l r) :
    LocalBit s ↪ Guess P B :=
  Equiv.subtypeSum.toEmbedding.trans (p.sumMap (SlotKey.encode s))

-- 读法：在后续公式中，`gather` 是 `collect s (PinIndex.encode hfa s)` 的缩写。
abbrev gather (hfa : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N) (s : X) : LocalBit s ↪ Guess P B :=
  collect s (PinIndex.encode hfa s)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 用固定私有带检验可变的局部比特集合

**英文原文**

Checking a fixed private tape in place of a variable set of local bits
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal Finset

variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}

variable (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

-- 读法：`used` 的取值由 `Sum.elim (fun j => (PinIndex.decode s j).isSome) (SlotKey.active s)` 给出。
def used : Guess P B → Bool := Sum.elim (fun j => (PinIndex.decode s j).isSome) (SlotKey.active s)

-- 读法：`sent` 的取值由 `Sum.elim (PinIndex.shared s) (SlotKey.shared s)` 给出。
def sent : Guess P B → Bool := Sum.elim (PinIndex.shared s) (SlotKey.shared s)

omit [Fintype F] in
-- 读法：`used s j = true` 与 `∃ e, gather hf s e = j` 等价。对 `j` 分类讨论。
theorem used_iff (j : Guess P B) : used s j = true ↔ ∃ e, gather hf s e = j := by
  constructor
  · intro hu
    cases j with
    | inl j =>
      obtain ⟨q, h⟩ := Option.isSome_iff_exists.mp hu
      obtain ⟨hq, he⟩ := (PinIndex.decode_eq hf s j q).mp h
      exact ⟨⟨.inl q, hq⟩, congrArg Sum.inl he⟩
    | inr j =>
      obtain ⟨q, he⟩ := (SlotKey.range_encode s j).mpr (of_decide_eq_true hu)
      exact ⟨⟨.inr q.1, q.2⟩, congrArg Sum.inr he⟩
  · rintro ⟨⟨q|q, h⟩, rfl⟩
    · change (PinIndex.decode s (PinIndex.encode hf s ⟨q, h⟩)).isSome = true
      rw [PinIndex.decode_encode]; rfl
    · change decide (incident s (.inr (.inl (SlotKey.expand hn i (workerAt s)
        (SlotKey.encode s ⟨q, h⟩))))) = true
      rw [SlotKey.expand_encode, decide_eq_true_eq]
      exact h

omit [Fintype F] in
-- 读法：`sent s (gather hf s e) = true` 与 `source s (wrap e.1) ≠ target s (wrap e.1)` 等价。
theorem sent_iff (e : LocalBit s) :
    sent s (gather hf s e) = true ↔ source s (wrap e.1) ≠ target s (wrap e.1) := by
  rcases e with ⟨q|q, h⟩
  · change PinIndex.shared s (PinIndex.encode hf s ⟨q, h⟩) = true ↔ _
    simp only [PinIndex.shared, PinIndex.decode_encode, Option.any_some, decide_eq_true_eq, wrap]
  · change SlotKey.shared s (SlotKey.encode s ⟨q, h⟩) = true ↔ _
    have he : incident s (.inr (.inl q)) := h
    simp only [SlotKey.shared, SlotKey.edge, SlotKey.expand_encode, decide_eq_true_eq, he, true_and, wrap]

omit [Fintype F] in
-- 读法：`Pin.literal (localPins s (x ∘ gather hf s)) s.site` 等于 `fun j => x (.inl (.inl j))`。用函数外延性比较等号两侧在 `j` 处的取值。
theorem literal_eq (x : Guess P B → Bool) :
    Pin.literal (localPins s (x ∘ gather hf s)) s.site = fun j => x (.inl (.inl j)) := by
  funext j
  obtain ⟨he, hv⟩ := (PinIndex.decode_eq hf s _ _).mp (PinIndex.decode_left s j)
  change fullBit s _ (.inl (.inl (s.site, j))) = _
  have ht : incident s (wrap (.inl (.inl (s.site, j)))) := he
  rw [fullBit, dite_eq_left ht]
  exact congrArg (fun i => x (.inl i)) hv

variable [LinearOrder (Name n r)] [NeZero (N / 4)]

-- 读法：`expected` 的取值由 `Sum.elim (PinIndex.expected C s) (SlotKey.expected w s)` 给出。
def expected (w : ℕ) : Guess P B → Bool := Sum.elim (PinIndex.expected C s) (SlotKey.expected w s)

-- 读法：`C.expected s w (gather hf s e)` 等于 `C.numberInOrder.physicalBit s (wrap e.1) 0`。这里调用 `SlotKey.expected_eq`。
private theorem assigned (hw : N ≤ 2 ^ w) (e : LocalBit s) (he : sent s (gather hf s e) = true) :
    C.expected s w (gather hf s e) = C.numberInOrder.physicalBit s (wrap e.1) 0 := by
  rcases e with ⟨q|q, h⟩
  · change PinIndex.expected C s (PinIndex.encode hf s ⟨q, h⟩) = _
    simp only [PinIndex.expected, PinIndex.decode_encode, Option.any_some, wrap]
  · let v : SlotKey.Here s := ⟨q, h⟩
    exact (SlotKey.expected_eq C hw s (SlotKey.encode s v) he).trans
      (congrArg (fun t => C.numberInOrder.physicalBit s (.inr (.inl t)) 0)
        (SlotKey.expand_encode s v))

-- 读法：当 `used` 成立时取 `(!sent || (expected == bit))`，否则取 `!bit`。
def accept (used sent expected bit : Bool) : Bool :=
  if used then (!sent || (expected == bit)) else !bit

-- 读法：`pass` 表示以下条件：对每个 `j`，`accept (used s j) (sent s j) (C.expected s w j) (x j)` 等于 `true`。
def pass (w : ℕ) (x : Guess P B → Bool) : Prop :=
  ∀ j, accept (used s j) (sent s j) (C.expected s w j) (x j) = true

-- 读法：`C.pass s w x` 与 `C.numberInOrder.Matches s (x ∘ gather hf s) ∧ ∀ j, x j = false ∨ ∃ e, gather hf s e = j` 等价。
private theorem pass_iff (hw : N ≤ 2 ^ w) (x : Guess P B → Bool) :
    C.pass s w x ↔ C.numberInOrder.Matches s (x ∘ gather hf s) ∧
      ∀ j, x j = false ∨ ∃ e, gather hf s e = j := by
  have h₁ (e : LocalBit s) := (used_iff hf s _).mpr ⟨e, rfl⟩
  constructor
  · intro hp
    constructor
    · intro e he
      have he' := (sent_iff hf s e).mpr he
      have ht := hp (gather hf s e)
      simp only [accept, h₁, he', ite_true, Bool.not_true, Bool.false_or, beq_iff_eq] at ht
      exact ht.symm.trans (C.assigned hf s hw e he')
    · intro j
      by_cases h : used s j = true
      · exact .inr ((used_iff hf s j).mp h)
      · left
        simpa [accept, h] using hp j
  · rintro ⟨hm, hx⟩ j
    by_cases h : used s j = true
    -- 推导：从 `(used_iff hf s j).mp h` 中取出 `e, rfl`。
    · obtain ⟨e, rfl⟩ := (used_iff hf s j).mp h
      by_cases hp : sent s (gather hf s e) = true
      · have he := hm e ((sent_iff hf s e).mp hp)
        simp [accept, h, hp, C.assigned hf s hw e hp, ←he]
      · simp [accept, h, hp]
    · have he := (hx j).resolve_right (mt (used_iff hf s j).mpr h)
      simp [accept, h, he]

-- 读法：`(∑ x : Guess P B → Bool, if C.pass s w x then f (x ∘ gather hf s) else 0)` 等于 `∑ x, if C.numberInOrder.Matches s x then f x else 0`。这里调用 `sum_congr`。
theorem sum_pass (hw : N ≤ 2 ^ w) (f : (LocalBit s → Bool) → F) :
    (∑ x : Guess P B → Bool, if C.pass s w x then f (x ∘ gather hf s) else 0) =
      ∑ x, if C.numberInOrder.Matches s x then f x else 0 := by
  rw [← sum_padded (gather hf s) (fun x => if C.numberInOrder.Matches s x then f x else 0)]
  apply sum_congr rfl
  intro x _
  simp only [C.pass_iff hf s hw, unused, prod_ite_zero, prod_const_one, mem_univ, forall_const,
    ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 检验固定私有带

未使用单元的值固定为零，共享单元的值必须匹配路由送达的比特，各工作单元均检查自己的字面值。电路将工作单元标识符与报告作为输入。

**英文原文**

Checking the fixed private tape

Unused cells are pinned to zero, shared cells must match their routed
bits, and every worker checks its own literal. The circuit treats the
worker identifier and the report as inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal Classical Install OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] {w : ℕ}

-- 读法：`b.toNat` 严格小于 `2`。
private theorem bit_lt (b : Bool) : b.toNat < 2 := by cases b <;> decide

-- 读法：要证明的命题是 `packed (U := raw _) F inp (fun s j => (accept (a s j) (b s j) (c s j) (d s j)).toNat) (k + 64)`。
private theorem packed_accept {S I : Type} [Fintype I] {inp : S → I → Bool}
    {a b c d : S → Coloring.B w → Bool} {k : ℕ} (hw : 16 ≤ 2 ^ w)
    (ha : packed (U := raw _) F inp (fun s j => (a s j).toNat) k)
    (hb : packed (U := raw _) F inp (fun s j => (b s j).toNat) k)
    (hc : packed (U := raw _) F inp (fun s j => (c s j).toNat) k)
    (hd : packed (U := raw _) F inp (fun s j => (d s j).toNat) k) :
    packed (U := raw _) F inp
      (fun s j => (accept (a s j) (b s j) (c s j) (d s j)).toNat) (k + 64) := by
  let pair (x y : ℕ) := 2 * x + y
  have h (x y : Bool) : pair x.toNat y.toNat < 4 := by cases x <;> cases y <;> decide
  -- 推导：记下中间结论 `h₁`：`= packed.binary pair (m`。
  have h₁ := packed.binary pair (m := 2) (n := 2) (by omega) ha hb
    (fun _ _ => bit_lt _) (fun _ _ => bit_lt _)
  have h₂ := packed.binary pair (m := 2) (n := 2) (by omega) hc hd
    (fun _ _ => bit_lt _) (fun _ _ => bit_lt _)
  let join (x y : ℕ) := (accept (x / 2 == 1) (x % 2 == 1) (y / 2 == 1) (y % 2 == 1)).toNat
  have H := packed.binary join (m := 4) (n := 4) hw h₁ h₂ (fun _ _ => h _ _) (fun _ _ => h _ _)
  convert H.mono (n := k + 64) (by omega) using 1
  funext s j
  cases a s j <;> cases b s j <;> cases c s j <;> cases d s j <;> simp [join, pair, accept]

variable [Fintype F] {N l d B n r h : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}
  [NeZero r] [NeZero (3 * r)] [NeZero (N / 4)] [LinearOrder (Name n r)]

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

-- 读法：在后续公式中，`Test` 是 `Guess P B ⊕ Fin l` 的缩写。
private abbrev Test (P : Format N l d n r h) (B : ℕ) := Guess P B ⊕ Fin l

-- 读法：逐一匹配以下输入模式：`.inl q`、`.inr j`。
private def checkCell (w : ℕ) (z : Y) : Test P B → Bool
  | .inl q => accept (used z.1 q) (sent z.1 q) (C.expected z.1 w q) (z.2 q)
  | .inr j => z.2 (.inl (.inl j)) == C.code (some (z.1.site, z.1.script)) j

variable (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (hb : 100 * N ≤ 2 ^ w)
  (hx : Fintype.card (XIn P B) ≤ 2 ^ w) (hc : 3 * r * Fintype.card (Name n r) ≤ 2 ^ w)
  (idx : Name n r ↪ Coloring.B w) (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N)

include hw hi hb hx hc idx in
-- 读法：要证明的命题是 `packed (U := raw _) F C.tapeIn (fun (z : Y) j => (C.checkCell w z (p j)).toNat) 606`。
private theorem packed_cells (p : Coloring.B w → Test P B) :
    packed (U := raw _) F C.tapeIn (fun (z : Y) j => (C.checkCell w z (p j)).toNat) 606 := by
  have hw' : 16 ≤ 2 ^ w := by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega
  have hw1 : 1 ≤ w := by have := hw.large; omega
  have read (f : Coloring.B w → XIn P B) :
      packed (U := raw _) F C.tapeIn (fun (z : Y) j => (C.tapeIn z (f j)).toNat) 514 :=
    (packed.named F C.tapeIn f (c := 0) (by rwa [pow_zero, mul_one])).mono (by decide)
  have H (p : Coloring.B w → Guess P B)
      (hu : packed (U := raw _) F C.input (fun (s : X) j => (used s (p j)).toNat) 512)
      (hs : packed (U := raw _) F C.input (fun (s : X) j => (sent s (p j)).toNat) 512)
      (he : packed (U := raw _) F C.input (fun (s : X) j => (C.expected s w (p j)).toNat) 512) :
      packed (U := raw _) F C.tapeIn (fun (z : Y) j => (C.checkCell w z (.inl (p j))).toNat) 578 :=
    packed_accept hw' (C.lift hx hu) (C.lift hx hs) (C.lift hx he) (read (Sum.inr ∘ p))
  apply packed.casesOn (c := 592) hw1 (fun z (_ : Unit) j => (C.checkCell w z j).toNat)
    (fun _ => ()) p
  · intro f
    apply packed.casesOn (c := 578) hw1 (fun z (_ : Unit) j => (C.checkCell w z (.inl j)).toNat)
      (fun _ => ()) f
    · intro a
      -- 推导：从 `PinIndex.packed_pins (i := i) C hw hi hb idx a` 中取出 `hu, hs, he`。
      obtain ⟨hu, hs, he⟩ := PinIndex.packed_pins (i := i) C hw hi hb idx a
      exact H (Sum.inl ∘ a) hu hs he
    · intro a
      obtain ⟨hu, hs, he⟩ := SlotKey.packed_slots (i := i) C hw hi hc idx a
      exact H (Sum.inr ∘ a) (hu.mono (by decide)) (hs.mono (by decide)) (he.mono (by decide))
  · intro a
    have h₁ := read (fun j => .inr (.inl (.inl (a j))))
    have h₂ := read (fun j => .inl (.inl (a j)))
    have hsame := packed.binary (fun x y => (x == y).toNat) (m := 2) (n := 2) (by omega)
      h₁ h₂ (fun _ _ => bit_lt _) (fun _ _ => bit_lt _)
    convert hsame.mono (n := 592) (by decide) using 1
    funext z j
    change (_ == _).toNat = ((z.2 (.inl (.inl (a j)))).toNat ==
      (C.code (some (z.1.site, z.1.script)) (a j)).toNat).toNat
    cases z.2 (.inl (.inl (a j))) <;> cases C.code (some (z.1.site, z.1.script)) (a j) <;> rfl

include hw hi hb hx hc idx in
-- 读法：这里调用 `le_trans`。
theorem private_net :
    ∃ f, Weight F f (2 ^ w * (100 + w) ^ 650) ∧ ∀ z : Y, f (C.tapeIn z) =
      if C.pass z.1 w z.2 then Pin.mask F (workerAt z.1) (C.code (some (z.1.site, z.1.script)))
        (localPins z.1 (z.2 ∘ gather hf z.1)) else 0 := by
  have hl : 0 < l := by have := C.literal; omega
  let _ : Nonempty (Test P B) := ⟨.inr ⟨0, hl⟩⟩
  obtain ⟨e⟩ : Nonempty (Test P B ↪ Coloring.B w) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin]
    apply le_trans _ hx
    simp only [Test, XIn, Machine.Ports, Fintype.card_sum, Fintype.card_fin]
    omega)
  let p := Function.invFun e
  have hp : Function.Surjective p := (Function.leftInverse_invFun e.injective).surjective
  -- 推导：记下中间结论 `hw'`：`16 ≤ 2 ^ w`。
  have hw' : 16 ≤ 2 ^ w := by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega
  have h := C.packed_cells (i := i) hw hi hb hx hc idx p
  obtain ⟨b, hb, he⟩ := packed.conjunction (by have := hw.large; omega) h
    (fun _ _ => (bit_lt _).trans_le (by omega))
  have hout := hb.weight (Weight.dense F Unit (fun x => if x () then 1 else 0))
  refine ⟨_, hout.mono ?_, fun z => ?_⟩
  · rw [Fintype.card_unit]
    let T := 2 ^ w * (100 + w) ^ 608
    have ht : 16 ≤ T := hw'.trans (Nat.le_mul_of_pos_right _ (by positivity))
    calc
      _ ≤ T * 2 := by
        rw [show 606 + 2 = 608 by decide, show (8 : ℕ) * 2 ^ 1 = 16 by decide]
        exact (Nat.add_le_add_left ht T).trans_eq (mul_two T).symm
      _ ≤ T * (100 + w) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ w * (100 + w) ^ 609 := by unfold T; rw [mul_assoc, ← pow_succ]
      _ ≤ _ := by gcongr; omega
  · have ht : (∀ j, (C.checkCell w z (p j)).toNat = 1) ↔
        C.pass z.1 w z.2 ∧ (fun j => z.2 (.inl (.inl j))) = C.code (some (z.1.site, z.1.script)) := by
      have hu : (∀ j, (C.checkCell w z (p j)).toNat = 1) ↔
          ∀ t, C.checkCell w z t = true := by
        simp only [Bool.toNat_eq_one]
        constructor
        · intro h t; obtain ⟨j, rfl⟩ := hp t; exact h j
        · exact fun h _ => h _
      rw [hu, Sum.forall]
      simp only [checkCell, beq_iff_eq, pass, funext_iff]
    simp only [Function.comp_apply, he, decide_eq_true_eq, ht, Pin.mask, workerAt,
      Equiv.apply_symm_apply, literal_eq, ite_and]

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 从紧凑数组读取带颜色的处理器输入

**英文原文**

Reading a colored processor input from the compact array
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Controller Diagonal Classical
variable {F : Type} [Field F] {N l d B n r h : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)} {i : Fin n}
  (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

-- 读法：`read` 的结果类型为 `Bool`。
def read (z : Y) (j u : ℕ) : Bool :=
  if hj : j < Fintype.card (Selected P.colors (axis z.1) (symbol z.1)) then
    if hu : u < 3 * r then
      let p := ((Fintype.equivFin (Selected P.colors (axis z.1) (symbol z.1))).symm ⟨j, hj⟩).val
      if A.owner hn N z.1.report.val (P.colors p) = workerAt z.1 then
        value (localPins z.1 (z.2 ∘ gather hf z.1)) ⟨u, hu⟩ p else false
    else false
  else false

-- 读法：`localPins z.1 (z.2 ∘ gather hf z.1) q` 等于 `z.2 (.inl e)`。
private theorem pin_read (z : Y) (e : Domain N l r) {q : Pin N l l r}
    (he : decode z.1 e = some q) :
    localPins z.1 (z.2 ∘ gather hf z.1) q = z.2 (.inl e) := by
  obtain ⟨hq, rfl⟩ := (decode_eq hf z.1 e q).mp he
  change fullBit z.1 _ (.inl q) = _
  rw [fullBit_at _ _ _ hq]
  rfl

-- 读法：`direct` 的取值由 `| some (.inl k) => some (.inl k) | _ => none` 给出。
def direct : Option (Machine.Ports N l l) → Option (Domain N l r)
  | some (.inl k) => some (.inl k)
  | _ => none

variable [NeZero r]

-- 读法：`access` 的结果类型为 `Option (Domain N l r)`。
def access (s : X) (k : Fin (4 * N / r)) (u : Fin (3 * r)) : Option (Domain N l r) :=
  let e := .inr (k, u)
  let p := cellPort s e
  let st := status s e
  if st = 0 then none else
  if st = 1 ∧ (direct (r := r) p).isSome then direct p else
    (number (kind p) u).map (fun j => .inr (k, j))

-- 读法：`status s (.inr (k, u))` 等于 `state s.site u (Worker.index r (A.owner hn N s.report.val (P.colors p)))`。
private theorem status_port (s : X) (k : Fin (4 * N / r)) (u : Fin (3 * r)) (p : Machine.Ports N l l)
    (hp : cellPort s (.inr (k, u)) = some p) :
    status s (.inr (k, u)) = state s.site u (Worker.index r (A.owner hn N s.report.val (P.colors p))) := by
  unfold status query
  rw [hp]
  change state _ ((Worker.index r) ((Worker.index r).symm _)) _ = _
  rw [Equiv.apply_symm_apply]
  rfl

-- 读法：`read hf z k.val u.val` 等于 `(access z.1 k u).any (fun e => z.2 (.inl e))`。按 `k.val < Fintype.card t` 成立与否分情况。
theorem read_access (z : Y) (k : Fin (4 * N / r)) (u : Fin (3 * r)) :
    read hf z k.val u.val = (access z.1 k u).any (fun e => z.2 (.inl e)) := by
  let s := z.1
  let t := Selected P.colors (axis s) (symbol s)
  let y := localPins s (z.2 ∘ gather hf s)
  unfold read
  by_cases hk : k.val < Fintype.card t
  swap
  · have he : cellPort s (.inr (k, u)) = none := dite_eq_right hk
    rw [dite_eq_right hk]
    simp [access, show cellPort z.1 (.inr (k, u)) = none from he, direct, kind, number]
  rw [dite_eq_left hk, dite_eq_left u.isLt]
  let p := ((Fintype.equivFin t).symm ⟨k.val, hk⟩).val
  let dest := A.owner hn N s.report.val (P.colors p)
  change (if dest = workerAt s then value y u p else false) =
    (access s k u).any _
  -- 推导：记下中间结论 `hp`：`cellPort s (.inr (k, u)) = some p`。
  have hp : cellPort s (.inr (k, u)) = some p := dite_eq_left hk
  have hs : status s (.inr (k, u)) = state s.site u (Worker.index r dest) :=
    status_port s k u p hp
  unfold access
  dsimp only
  rw [hs, hp]
  by_cases hd : dest = workerAt s
  swap
  · have he : s.site ≠ Worker.index r dest :=
      fun h => hd ((Worker.index r).eq_symm_apply.mpr h.symm)
    simp [hd, state, he]
  -- 推导：记下中间结论 `he`：`s.site = Worker.index r dest`。
  have he : s.site = Worker.index r dest := ((Worker.index r).eq_symm_apply.mp hd).symm
  rw [ite_eq_left hd, state, ite_eq_left he]
  have dir : (direct (r := r) (some p)).isSome = true ↔ ∃ j, p = .inl j := by
    rcases p with j|j <;> simp [direct]
  by_cases own : s.site = u ∧ (direct (r := r) (some p)).isSome
  · obtain ⟨u', hj⟩ := dir.mp own.2
    rw [ite_eq_left own.1, hj]
    simp only [direct, Option.isSome_some, and_self, ite_true, one_ne_zero, ite_false, Option.any_some]
    rw [← own.1]
    exact pin_read hf z _ (decode_left s _)
  -- 推导：记下中间结论 `hn'`：`(if s.site = u then 1 else 2) ≠ 0`。
  have hn' : (if s.site = u then 1 else 2) ≠ 0 := by split <;> decide
  have hd' : ¬ ((if s.site = u then 1 else 2) = 1 ∧ (direct (r := r) (some p)).isSome) := by
    split <;> grind
  rw [ite_eq_right hn', ite_eq_right hd']
  have ht := number_spec y u p
  cases hnum : number (kind (some p)) u with
  | none => rwa [hnum] at ht
  | some j =>
    rw [hnum] at ht
    obtain ⟨q, hq, hv⟩ := ht
    -- 推导：从 `prior_spec hq` 中取出 `hq', hj`。
    obtain ⟨hq', hj⟩ := prior_spec hq
    have hi : target s (.inl q) = s.site := by
      change Worker.index r (A.owner hn N s.report.val (P.colors q.position)) = _
      rw [hq']; exact he.symm
    have ho : ¬ PinIndex.own s q := by
      rintro ⟨x, rfl⟩
      have hx : p = .inl x := hq'.symm
      rw [hx] at hnum
      have hu : u = j := Option.some.inj hnum
      exact own ⟨(Fin.ext hj).trans hu.symm, dir.mpr ⟨x, hx⟩⟩
    have hi' := (decode_right s k j q).mpr ⟨hq' ▸ hp, hj, hi, ho⟩
    exact hv.trans (pin_read hf z _ hi')

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 通过并行读取收集原有带上的比特

**英文原文**

Collecting original tape bits by parallel reads
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Controller Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n} (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (hb : 100 * N ≤ 2 ^ w)
  (hx : Fintype.card (XIn P B) ≤ 2 ^ w) [NeZero r] [LinearOrder (Name n r)]
  (idx : Name n r ↪ Coloring.B w) (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

include hw hi hb idx in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => fn (access s (k j) (u j))) 300`。
private theorem packed_access (k : Coloring.B w → Fin (4 * N / r)) (u : Coloring.B w → Fin (3 * r))
    (fn : Option (Domain N l r) → ℕ) :
    packed (U := raw _) F C.input (fun (s : X) j => fn (access s (k j) (u j))) 300 := by
  let cell (j : Coloring.B w) : Domain N l r := .inr (k j, u j)
  let f (s : X) j := number (kind (cellPort s (cell j))) (u j)
  let e := Fintype.equivFin (Option (Fin (3 * r)))
  have hf : packed (U := raw _) F C.input (fun s j => (e (f s j)).val) 96 :=
    packed_kind C hw hi hb cell (fun a b => (e (number a b)).val)
  have hcap : Fintype.card (Option (Fin (3 * r))) * Fintype.card (Fin (4 * N / r)) ≤ 2 ^ w := by
    rw [Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
    have := Nat.mul_div_le (4 * N) r
    have := Nat.div_le_self (4 * N) r
    nlinarith
  have H (v : Coloring.B w → ℕ) : packed (U := raw _) F (C.input (i := i)) (fun _ => v) 2 :=
    packed.const (U := raw _) F _ _ (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  let _ : Nonempty (Fin (4 * N / r)) := ⟨k 0⟩
  let e' := Fintype.equivFin (Fin (4 * N / r))
  let g (v : Option (Fin (3 * r))) (j : Fin (4 * N / r)) := fn (v.map (fun x => .inr (j, x)))
  have right := packed.named_table g hcap f (fun _ j => k j) e e' hf (H (fun j => (e' (k j)).val))
  -- 推导：记下中间结论 `left`：`= packed_port (i`。
  have left := packed_port (i := i) C hw hi hb cell (fun p => fn (direct p))
  have lit := packed_port (i := i) C hw hi hb cell (fun p => (direct (r := r) p).isSome.toNat)
  have hstat : packed (U := raw _) F C.input (fun (s : X) j => status s (cell j)) 188 :=
    C.packed_pair hw hi _ idx (packed_query C hw hi hb cell idx) state
  have h2 : 2 < 2 ^ w := by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega
  have ht : fits (fun (s : X) j => status s (cell j)) := by
    intro s j
    simp only [status, state]
    split_ifs <;> omega
  have hl : fits (fun (s : X) j => (direct (r := r) (cellPort s (cell j))).isSome.toNat) := by
    intro s j
    dsimp only
    cases (direct (r := r) (cellPort s (cell j))).isSome <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  -- 推导：记下中间结论 `hone`：`fits (fun (_ : X) (_ : Coloring.B w) => 1)`。
  have hone : fits (fun (_ : X) (_ : Coloring.B w) => 1) := fun _ _ => (by omega : 1 < 2 ^ w)
  have a := lit.choose_eq (H (fun _ => 1)) left right hl hone
  have b := hstat.choose_eq (H (fun _ => 1)) a right ht hone
  have c := hstat.choose_eq (H (fun _ => 0)) (H (fun _ => fn none)) b ht
    (fun _ _ => Nat.two_pow_pos w)
  convert c.mono (n := 300) (by decide) using 1
  funext s j
  unfold access f g
  change fn (if status s (cell j) = 0 then none else
    if status s (cell j) = 1 ∧ (direct (r := r) (cellPort s (cell j))).isSome
      then _ else _) = _
  cases (direct (r := r) (cellPort s (cell j))).isSome <;>
    simp only [Bool.false_eq_true, and_false, and_true, ite_false, Bool.toNat_true, Bool.toNat_false] <;>
    split_ifs <;> first | rfl | contradiction

include hw hi hb hx idx in
-- 读法：要证明的命题是 `packed (U := raw _) F C.tapeIn (fun (z : Y) j => (read hf z (k j).val (u j).val).toNat) 400`。这里调用 `le_trans`。
private theorem bounded_read (k : Coloring.B w → Fin (4 * N / r)) (u : Coloring.B w → Fin (3 * r)) :
    packed (U := raw _) F C.tapeIn (fun (z : Y) j => (read hf z (k j).val (u j).val).toNat) 400 := by
  let D := Domain N l r
  let o : D := .inr (k 0, u 0)
  let _ : Nonempty D := ⟨o⟩
  have hcard : Fintype.card D ≤ Fintype.card (Coloring.B w) := by
    rw [Fintype.card_fin]
    apply le_trans _ hx
    exact Fintype.card_le_of_injective (fun j : D => (Sum.inr (.inl j) : XIn P B))
      (fun _ _ he => Sum.inl.inj (Sum.inr.inj he))
  -- 推导：从 `Function.Embedding.nonempty_of_card_le hcard` 中取出 `e`。
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let choice (z : Y) j := access z.1 (k j) (u j)
  have H (f : Option D → ℕ) : packed (U := raw _) F C.tapeIn (fun z j => f (choice z j)) 302 :=
    C.lift hx (packed_access C hw hi hb idx k u f)
  have named (p : Coloring.B w → D) :
      packed (U := raw _) F C.tapeIn (fun (z : Y) j => (z.2 (.inl (p j))).toNat) 2 :=
    packed.named F (C.tapeIn (i := i)) (fun j => .inr (.inl (p j))) (c := 0)
      (by rw [pow_zero, mul_one]; exact hx)
  have hget := packed.fetch (fun z j => (choice z j).getD o) e
    (fun z t => (z.2 (.inl t)).toNat) (H (fun p => (e (p.getD o)).val)) named
  have hk := H (fun p => p.isSome.toNat)
  have hbool (b : Bool) : b.toNat < 2 := by cases b <;> decide
  -- 推导：记下中间结论 `ht`：`= packed.binary (fun k x => if k = 1 then x else 0) (m`。
  have ht := packed.binary (fun k x => if k = 1 then x else 0) (m := 2) (n := 2)
    (by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega) hk hget
    (fun _ _ => hbool _) (fun _ _ => hbool _)
  convert ht.mono (n := 400) (by decide) using 1
  funext z j
  rw [read_access]
  unfold choice
  cases access z.1 (k j) (u j) <;> rfl

include hw hi hb hx idx in
-- 读法：要证明的命题是 `packed (U := raw _) F C.tapeIn (fun (z : Y) t => (read hf z (j t) (u t)).toNat) 512`。
theorem packed_read (j u : Coloring.B w → ℕ) :
    packed (U := raw _) F C.tapeIn (fun (z : Y) t => (read hf z (j t) (u t)).toNat) 512 := by
  have hR := hw.pos
  have hN := C.links
  let _ : NeZero (3 * r) := ⟨by omega⟩
  let _ : NeZero (4 * N / r) := ⟨(Nat.div_pos (by nlinarith) hR).ne'⟩
  have h := bounded_read (i := i) C hw hi hb hx idx hf (fun t => Fin.ofNat _ (j t))
    (fun t => Fin.ofNat _ (u t))
  let ok (t : Coloring.B w) := j t < 4 * N / r ∧ u t < 3 * r
  have hv := packed.const (U := raw _) F (C.tapeIn (i := i)) (fun t => if ok t then 1 else 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact hx)
  -- 推导：记下中间结论 `ht`：`= packed.binary (fun k x => if k = 1 then x else 0) (m`。
  have ht := packed.binary (fun k x => if k = 1 then x else 0) (m := 2) (n := 2)
    (by have := hw.large; have := Nat.lt_two_pow_self (n := w); omega) hv h
    (by intro z t; split <;> decide)
    (fun _ _ => (show ∀ b : Bool, b.toNat < 2 from fun b => by cases b <;> decide) _)
  convert ht.mono (n := 512) (by decide) using 1
  funext z t
  by_cases H : ok t
  · simp only [ite_eq_left H, ite_true, Fin.val_ofNat, Nat.mod_eq_of_lt H.1, Nat.mod_eq_of_lt H.2]
  · rw [ite_eq_right H, ite_eq_right (by decide : 0 ≠ 1)]
    have hp : Fintype.card (Selected P.colors (axis z.1) (symbol z.1)) ≤ 4 * N / r :=
      (Nat.le_div_iff_mul_le hR).mpr (project_bound _ hf _ _)
    unfold read
    split
    · rename_i hj
      rw [dite_eq_right (fun ht => H ⟨hj.trans_le hp, ht⟩)]
      rfl
    · rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 按可变模板名称从私有带取出槽位比特

**英文原文**

Fetching slot bits from the private tape at variable template names
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w c : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Slot" => Position n r (B * P.count) h × Bool
local notation "Dom" => SlotKey.Domain n r (B * P.count) h

-- 读法：`colNumber` 的结果类型为 `Name n r → ℕ`。
private def colNumber (hn : 2 ≤ n) (i : Fin n) (u : Worker r) : Name n r → ℕ
  | .inr (.inl k) =>
    if he : SlotKey.focus hn i u k = Layout.symbol u then
      ((SlotKey.enumerate hn i u).symm ⟨k, he⟩).val
    else 0
  | _ => 0

omit [Fintype F] in
-- 读法：`(SlotKey.encode s e).1.val` 等于 `colNumber hn i (workerAt s) (key P B (.inr (.inl e.val)))`。
private theorem encode_col (s : X) (e : SlotKey.Here s) :
    (SlotKey.encode s e).1.val = colNumber hn i (workerAt s) (key P B (.inr (.inl e.val))) := by
  rw [← SlotKey.expand_encode s e]
  let k := SlotKey.enumerate hn i (workerAt s) (SlotKey.encode s e).1
  change _ = colNumber hn i (workerAt s) (.inr (.inl k.val))
  rw [colNumber, dite_eq_left k.property]
  exact congrArg Fin.val ((SlotKey.enumerate hn i (workerAt s)).symm_apply_apply _).symm

-- 读法：`slotCode` 的结果类型为 `Dom ↪ Coloring.B w`。
private def slotCode (hc : Fintype.card Dom ≤ 2 ^ w) : Dom ↪ Coloring.B w :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).toEmbedding.trans
    (Fin.castLEEmb (by simpa [SlotKey.Domain] using hc))

omit [Fintype F] in
-- 读法：结论为 `(slotCode hc (SlotKey.encode s e)).val = e.val.1.2.2.val + h * e.val.1.1.2.val + (B * P.count * h) * colNumber hn i (workerAt s) (key P B (.inr (.inl e.val)))`。
private theorem encode_offset (hc : Fintype.card Dom ≤ 2 ^ w) (s : X) (e : SlotKey.Here s) :
    (slotCode hc (SlotKey.encode s e)).val =
      e.val.1.2.2.val + h * e.val.1.1.2.val +
        (B * P.count * h) * colNumber hn i (workerAt s) (key P B (.inr (.inl e.val))) := by
  rw [← encode_col]
  rfl

variable [LinearOrder (Name n r)]

-- 读法：要证明的命题是 `packed (U := raw _) F C.tapeIn (fun z j => (fullBit z.1 (z.2 ∘ gather hf z.1) (.inr (slot z.1 j))).toNat) (c + 128)`。
theorem packed_slot (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (XIn P B) ≤ 2 ^ w) (hc : 3 * r * Fintype.card (Name n r) ≤ 2 ^ w)
    (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)
    (slot : X → Coloring.B w → Slot) (idx : Name n r ↪ Coloring.B w)
    (hk : packed (U := raw _) F C.input (fun s j => (idx (key P B (.inr (.inl (slot s j))))).val) c)
    (low : Coloring.B w → ℕ)
    (hlow : ∀ s j, (slot s j).1.2.2.val + h * (slot s j).1.1.2.val = low j) :
    packed (U := raw _) F C.tapeIn
      (fun z j => (fullBit z.1 (z.2 ∘ gather hf z.1) (.inr (slot z.1 j))).toNat) (c + 128) := by
  have : Nonempty (Name n r) := ⟨.inl (.inr (fun _ => ⟨0, hw.pos⟩))⟩
  -- 推导：记下中间结论 `hI`：`Fintype.card (Machine.Ports N l l) ≤ 2 ^ w`。
  have hI : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w := by
    rw [Fintype.card_sum] at hi
    omega
  have hD : Fintype.card Dom ≤ 2 ^ w := by
    rw [Fintype.card_sum, Fintype.card_sum (α := PinIndex.Domain N l r)] at hi
    omega
  let keys (s : X) j := key P B (.inr (.inl (slot s j)))
  let K (s : X) j := low j + (B * P.count * h) * colNumber hn i (workerAt s) (keys s j)
  have hb := C.packed_workerLookup hw hI hc keys idx hk (fun u k => (B * P.count * h) * colNumber hn i u k)
  have ha := packed.const (U := raw _) F (C.input (i := i)) low (m := 0) (by rw [pow_zero, mul_one]; exact hI)
  have hK : packed (U := raw _) F C.input K (c + 51) := (ha.add hb).mono (by omega)
  -- 推导：记下中间结论 `p`：`Coloring.B w → XIn P B`。
  let p : Coloring.B w → XIn P B := Function.extend (slotCode hD)
    (fun j => .inr (.inr j)) (fun _ => .inl (.inl ⟨0, by have := C.literal; omega⟩))
  have hv := packed.named F (C.tapeIn (i := i)) p (c := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hget := hv.lookup (C.lift hi hK)
  let f (s : X) (j : Coloring.B w) := if incident s (.inr (.inl (slot s j))) then 1 else 0
  have hflag : packed (U := raw _) F C.input f (c + 92) := by
    have h := C.packed_pair hw hI keys idx hk (fun u a b => if a = u ∨ b = u then 1 else 0)
    simpa only [keys, ends_eq] using h
  have z0 := packed.const (U := raw _) F (C.tapeIn (i := i)) (fun _ : Coloring.B w => 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  -- 推导：记下中间结论 `hsize`：`1 < 2 ^ w`。
  have hsize : 1 < 2 ^ w := Nat.one_lt_pow (by have := hw.large; omega) (by decide)
  have H := z0.select (C.lift hi hflag) hget z0
    (fun _ _ => pow_pos (by decide) _) (fun _ _ => by unfold f; split <;> omega)
  convert H.mono (n := c + 128) (by omega) using 1
  funext z j
  by_cases he : incident z.1 (.inr (.inl (slot z.1 j)))
  · let e : SlotKey.Here z.1 := ⟨slot z.1 j, he⟩
    have eq : Fin.ofNat (2 ^ w) (K z.1 j) = slotCode hD (SlotKey.encode z.1 e) := by
      have ho := encode_offset hD z.1 e
      have ho' : (slotCode hD (SlotKey.encode z.1 e)).val = K z.1 j := by
        simpa only [e, hlow, K, keys] using ho
      rw [← ho']
      exact Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
    have ht : incident z.1 (wrap (.inr (slot z.1 j))) := he
    unfold fullBit
    rw [dite_eq_left ht]
    simp only [f, he, ite_true, zero_lt_one, eq, p, (slotCode hD).injective.extend_apply]
    rfl
  · simp [f, he, fullBit, wrap]

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
