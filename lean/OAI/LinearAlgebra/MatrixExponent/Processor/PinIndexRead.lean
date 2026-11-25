-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Processor.LocalReceive
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize
import OAI.LinearAlgebra.MatrixExponent.Processor.LocalBank
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases

/-!
# 原有处理器输入的紧凑索引

原有物理比特由其在带上的位置和所在链路的较小端点确定。地址除以链路宽度所得的商，给出两端点之和对处理器数取模的结果。

**英文原文**

A compact index for the old processor inputs

An old physical bit is determined by its tape position and the lower
endpoint of its link. The quotient of the address by the link width
gives the sum of the endpoints modulo the number of processors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Diagonal
variable {R N l r n : ℕ}

-- 读法：在后续公式中，`Domain` 是 `Fin l ⊕ (Fin (4 * N / r) × Fin (3 * r))` 的缩写。
abbrev Domain (N l r : ℕ) := Fin l ⊕ (Fin (4 * N / r) × Fin (3 * r))

-- 读法：逐一匹配以下输入模式：`.inl t`、`.inr (.inl _)`、`.inr (.inr t)`。
def old : Pin N l l r → ℕ
  | .inl t => t.1.val
  | .inr (.inl _) => 0
  | .inr (.inr t) => t.1.val.1.val

-- 读法：`old q` 严格小于 `3 * r`。这里调用 `q.1.isLt`。
theorem old_lt (q : Pin N l l r) (hr : 0 < 3 * r) : old q < 3 * r := by
  rcases q with q | q | q
  · exact q.1.isLt
  · exact hr
  · exact q.1.val.1.isLt

-- 读法：`physical` 的结果类型为 `Option (Links.Slot R N)`。
def physical (p : Fin (N / 4)) (u : Fin R) : Option (Links.Slot R N) :=
  if h : p.val < R * (N / (4 * R)) then
    let z := finProdFinEquiv.symm ⟨p.val, h⟩
    let v := z.1 - u
    if k : u < v then some (⟨(u, v), k⟩, z.2) else none
  else none

-- 读法：`physical (Links.address e) e.1.val.1` 等于 `some e`。
theorem physical_address (e : Links.Slot R N) :
    physical (Links.address e) e.1.val.1 = some e := by
  let z := (e.1.val.1 + e.1.val.2, e.2)
  have h : (Links.address e).val < R * (N / (4 * R)) := (finProdFinEquiv z).isLt
  have he : (⟨(Links.address e).val, h⟩ : Fin (R * (N / (4 * R)))) = finProdFinEquiv z := rfl
  let _ : NeZero R := ⟨e.1.val.1.pos.ne'⟩
  simp [physical, h, he, z, e.1.property]

-- 读法：`Links.address e = p` 与 `e.1.val.1 = u` 同时成立。
theorem physical_spec {p : Fin (N / 4)} {u : Fin R} {e : Links.Slot R N}
    (h : physical p u = some e) : Links.address e = p ∧ e.1.val.1 = u := by
  let _ : NeZero R := ⟨u.pos.ne'⟩
  unfold physical at h
  split at h <;> try contradiction
  rename_i hp
  let z := finProdFinEquiv.symm (⟨p.val, hp⟩ : Fin (R * (N / (4 * R))))
  dsimp only at h
  split at h <;> try contradiction
  cases Option.some.inj h
  refine ⟨Fin.ext ?_, rfl⟩
  change (finProdFinEquiv (u + (z.1 - u), z.2)).val = p.val
  rw [add_sub_cancel]
  exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨p.val, hp⟩)

-- 读法：`prior` 的结果类型为 `Option (Pin N l l r)`。
def prior (p : Machine.Ports N l l) (j : Fin (3 * r)) : Option (Pin N l l r) :=
  match p with
  | .inl x => some (.inl (j, x))
  | .inr (.inl x) => if j.val = 0 then some (.inr (.inl x)) else none
  | .inr (.inr x) => (physical x j).map (fun t => .inr (.inr t))

-- 读法：`prior q.position j` 等于 `some q`。
theorem prior_old (q : Pin N l l r) (j : Fin (3 * r)) (h : old q = j.val) :
    prior q.position j = some q := by
  rcases q with ⟨u, v⟩ | q | q
  · rw [← (show u = j from Fin.ext h)]; rfl
  · change 0 = j.val at h
    simp [Pin.position, prior, h.symm]
  · rw [← (show q.1.val.1 = j from Fin.ext h)]
    simp [Pin.position, prior, physical_address]

-- 读法：`q.position = p` 与 `old q = j.val` 同时成立。
theorem prior_spec {p : Machine.Ports N l l} {j : Fin (3 * r)} {q : Pin N l l r}
    (h : prior p j = some q) : q.position = p ∧ old q = j.val := by
  rcases p with p | p | p
  · cases Option.some.inj h; exact ⟨rfl, rfl⟩
  · simp only [prior] at h
    split at h <;> try contradiction
    cases Option.some.inj h
    exact ⟨rfl, by symm; assumption⟩
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hp, hj⟩ := physical_spec he
    simp [Pin.position, old, hp, hj]

variable (fa : Machine.Ports N l l → Label n r) (hfa : ∀ z, multiplicity fa z * r ^ n ≤ 4 * N)
  (i : Fin n) (g : Fin r)

-- 读法：在后续公式中，`Selected` 是 `{p // fa p i = g}` 的缩写。
abbrev Selected := {p // fa p i = g}

-- 读法：`portIndex` 的取值由 `(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb ((Nat.le_div_iff_mul_le g.pos).mpr (project_bound fa hfa i g)))` 给出。
/-- 编号只取决于坐标与符号，与工作单元的角色或当前报告无关。

英文原文：The numbering depends only on the coordinate and symbol, not on
the worker role or current report.
-/
def portIndex : Selected fa i g ↪ Fin (4 * N / r) :=
  (Fintype.equivFin _).toEmbedding.trans
    (Fin.castLEEmb ((Nat.le_div_iff_mul_le g.pos).mpr (project_bound fa hfa i g)))

-- 读法：`readPort` 的结果类型为 `Option (Machine.Ports N l l)`。
def readPort (j : Fin (4 * N / r)) : Option (Machine.Ports N l l) :=
  if h : j.val < Fintype.card (Selected fa i g) then
    some ((Fintype.equivFin (Selected fa i g)).symm ⟨j.val, h⟩).val else none

-- 读法：`readPort fa i g (portIndex fa hfa i g p)` 等于 `some p.val`。
theorem readPort_index (p : Selected fa i g) :
    readPort fa i g (portIndex fa hfa i g p) = some p.val := by
  have he : (portIndex fa hfa i g p).val = (Fintype.equivFin _ p).val := rfl
  simp [readPort, he]

-- 读法：`portIndex fa hfa i g p` 等于 `j`。按 `Fin.ext` 的外延性准则比较各分量。
theorem index_readPort (p : Selected fa i g) (j : Fin (4 * N / r))
    (he : readPort fa i g j = some p.val) : portIndex fa hfa i g p = j := by
  unfold readPort at he
  split at he <;> try contradiction
  rename_i hj
  have h : (Fintype.equivFin (Selected fa i g)).symm ⟨j.val, hj⟩ = p :=
    Subtype.ext (Option.some.inj he)
  apply Fin.ext
  change (Fintype.equivFin _ p).val = j.val
  rw [← h, Equiv.apply_symm_apply]

open Controller Classical
variable {F : Type} [Field F] {d h B : ℕ} {i}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h} {hn : 2 ≤ n}
  (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)

variable (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

-- 读法：在后续公式中，`Here` 是 `{q : Pin N l l r // incident s (.inl q)}` 的缩写。
abbrev Here := {q : Pin N l l r // incident s (.inl q)}

-- 读法：`own` 的取值由 `∃ j, q = .inl (s.site, j)` 给出。
def own (q : Pin N l l r) := ∃ j, q = .inl (s.site, j)

-- 读法：`incident s (.inl q)` 与 `own s q ∨ target s (.inl q) = s.site` 等价。
private theorem here_iff (q : Pin N l l r) :
    incident s (.inl q) ↔ own s q ∨ target s (.inl q) = s.site := by
  rcases q with ⟨u, j⟩ | q
  · simp [incident, own, source, Expansion.extraSrc, Pin.src]
  · simp [incident, own, source, target, Expansion.extraSrc, Expansion.extraDst, Pin.src]

-- 读法：`axis` 的取值由 `Layout.axis hn i (workerAt s)` 给出。
def axis := Layout.axis hn i (workerAt s)
-- 读法：`symbol` 的取值由 `Layout.symbol (workerAt s)` 给出。
def symbol := Layout.symbol (workerAt s)

-- 读法：`P.colors q.position (axis s)` 等于 `symbol s`。
theorem selected (q : Pin N l l r) (ht : target s (.inl q) = s.site) :
    P.colors q.position (axis s) = symbol s := by
  have h : A.owner hn N s.report.val (P.colors q.position) = workerAt s :=
    (Worker.index r).eq_symm_apply.mpr ht
  unfold axis symbol
  rw [← h, ← congrArg (Layout.axis (r := r) hn) s.cut]
  unfold Expansion.owner
  split <;> rfl

-- 读法：逐一匹配以下输入模式：`.inl j`、`.inr p`。
def cellPort : Domain N l r → Option (Machine.Ports N l l)
  | .inl j => some (.inl j)
  | .inr p => readPort P.colors (axis s) (symbol s) p.1

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr p`。
def cellWorker : Domain N l r → Fin (3 * r)
  | .inl _ => s.site
  | .inr p => p.2

-- 读法：`candidate` 的取值由 `(cellPort s e).bind fun p => prior p (cellWorker s e)` 给出。
def candidate (e : Domain N l r) : Option (Pin N l l r) :=
  (cellPort s e).bind fun p => prior p (cellWorker s e)

-- 读法：`decode` 的取值由 `(candidate s e).bind (fun q => if e.isLeft ∨ target s (.inl q) = s.site ∧ ¬ own s q then some q else none)` 给出。
/-- 在本站点产生的字面值总是使用自己的直连单元。即使是本地字面值，也会抑制第二份副本。

英文原文：A literal emitted at this site always uses its own direct cell.
The second copy is suppressed even for a local literal.
-/
def decode (e : Domain N l r) : Option (Pin N l l r) :=
  (candidate s e).bind (fun q =>
    if e.isLeft ∨ target s (.inl q) = s.site ∧ ¬ own s q then some q else none)

-- 读法：`decode s (.inl j)` 等于 `some (.inl (s.site, j))`。
theorem decode_left (j : Fin l) : decode s (.inl j) = some (.inl (s.site, j)) := by
  simp [decode, candidate, cellPort, cellWorker, prior]

-- 读法：`decode s (.inr (k, u)) = some q` 与 `readPort P.colors (axis s) (symbol s) k = some q.position ∧ old q = u.val ∧ target s (.inl q) = s.site ∧ ¬own s q` 等价。
theorem decode_right (k : Fin (4 * N / r)) (u : Fin (3 * r)) (q : Pin N l l r) :
    decode s (.inr (k, u)) = some q ↔
      readPort P.colors (axis s) (symbol s) k = some q.position ∧
        old q = u.val ∧ target s (.inl q) = s.site ∧ ¬own s q := by
  unfold decode candidate cellPort cellWorker
  simp only [Sum.isLeft_inr, Bool.false_eq_true, false_or, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨q', ⟨p, hp, hp'⟩, h⟩
    split at h <;> try contradiction
    cases Option.some.inj h
    obtain ⟨rfl, he⟩ := prior_spec hp'
    exact ⟨hp, he, by assumption⟩
  · rintro ⟨hp, he, h⟩
    exact ⟨q, ⟨q.position, hp, prior_old q u he⟩, ite_eq_left h⟩

-- 读法：`place` 的结果类型为 `Domain N l r`。
private def place (q : Here s) : Domain N l r :=
  if h : own s q.val then .inl h.choose else
    .inr (portIndex _ hf _ _ ⟨q.val.position, selected s q.val ((here_iff s _).mp q.2 |>.resolve_left h)⟩,
      ⟨old q.val, old_lt _ s.site.pos⟩)

-- 读法：`decode s (place hf s q)` 等于 `some q.val`。这里调用 `decode_left`。
private theorem decode_place (q : Here s) : decode s (place hf s q) = some q.val := by
  unfold place
  split
  · rename_i h
    exact (decode_left s _).trans (congrArg some h.choose_spec.symm)
  · rename_i h
    exact (decode_right ..).mpr ⟨readPort_index .., rfl, ((here_iff s _).mp q.2).resolve_left h, h⟩

-- 读法：`encode` 的结果类型为 `Here s ↪ Domain N l r`。
def encode : Here s ↪ Domain N l r :=
  ⟨place hf s, fun x y h => Subtype.ext (Option.some.inj
    ((decode_place hf s x).symm.trans ((congrArg (decode s) h).trans (decode_place hf s y))))⟩

-- 读法：`decode s (encode hf s q)` 等于 `some q.val`。使用 `decode_place` 给出的结论。
theorem decode_encode (q : Here s) : decode s (encode hf s q) = some q.val := decode_place hf s q

-- 读法：`decode s e = some q` 与 `∃ hq, encode hf s ⟨q, hq⟩ = e` 等价。
theorem decode_eq (e : Domain N l r) (q : Pin N l l r) :
    decode s e = some q ↔ ∃ hq, encode hf s ⟨q, hq⟩ = e := by
  constructor
  · intro he
    rcases e with j | ⟨k, u⟩
    · rw [decode_left, Option.some.injEq] at he
      have h : own s q := ⟨j, he.symm⟩
      refine ⟨(here_iff s q).mpr (.inl h), ?_⟩
      change place hf s _ = _
      simp only [place, dite_eq_left h, Sum.inl.injEq]
      exact congrArg Prod.snd (Sum.inl.inj (h.choose_spec.symm.trans he.symm))
    · obtain ⟨hp, hu, ht, h⟩ := (decode_right ..).mp he
      refine ⟨.inr ht, ?_⟩
      change place hf s _ = _
      simp only [place, dite_eq_right h, Sum.inr.injEq]
      exact Prod.ext (index_readPort _ hf _ _ _ _ hp) (Fin.ext hu)
  · rintro ⟨hq, rfl⟩
    exact decode_encode hf s ⟨q, hq⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

section
/-!
# 批量读取与消息解码器的一致性

**英文原文**

Agreement of batched reads with the message decoder
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)]
  {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：`key` 的取值由 `(records P.colors h (B * P.count)).key e` 给出。
noncomputable def key (P : Format N l d n r h) (B : ℕ) (e : Edge P B) : Name n r :=
  (records P.colors h (B * P.count)).key e

-- 读法：`offset` 的取值由 `(records P.colors h (B * P.count)).index e` 给出。
noncomputable def offset (P : Format N l d n r h) (B : ℕ) (e : Edge P B) : ℕ :=
  (records P.colors h (B * P.count)).index e

omit [LinearOrder (Name n r)] [Fintype F] in
-- 读法：`request A hn N s.report.val (key P B e)` 等于 `(source s e, target s e, some (key P B e))`。这里调用 `Prod.ext`。
theorem ends_eq (s : X) (e : Edge P B) :
    request A hn N s.report.val (key P B e) = (source s e, target s e, some (key P B e)) := by
  let t := grouping P.colors A hn s.report.1
  exact Prod.ext (t.atSrc e) (Prod.ext (t.atDst e) rfl)

variable [NeZero (N / 4)]

-- 读法：`C.numberInOrder.receive s z he` 等于 `get w s (key P B z.1.val) (offset P B z.1.val * width s z.1.val + z.2.val)`。
theorem get_eq (hw : N ≤ 2 ^ w) (s : X) (z : Encoded.Bits (source s) (target s) (width s))
    (he : incident s z.1.val) :
    C.numberInOrder.receive s z he =
      get w s (key P B z.1.val) (offset P B z.1.val * width s z.1.val + z.2.val) := by
  let c := channels s.report
  have hq := C.pairSum s.report
  let v := Links.token _ _ c.serial z z.1.2
  have hv : v.2.val < N :=
    v.2.isLt.trans_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)).trans
      ((hq _).trans (Nat.div_le_self ..)))
  -- 推导：记下中间结论 `haddr`：`c.address z < 2 ^ w`。
  have haddr : c.address z < 2 ^ w := by rw [← c.token_address z z.1.2]; exact hv.trans_le hw
  let loc := Links.location _ _ c.serial hq C.links s.site z z.1.2 he
  have hx : loc.val = routeAddress N (pairCount s.report) s.site (source s z.1.val)
      (target s z.1.val) (c.address z) := c.location_eq _ _ _ _ _ _
  unfold get
  rw [ends_eq]
  change s.physical loc = s.physical (Fin.ofNat (N / 4) (routeAddress N (pairCount s.report) s.site
    (source s z.1.val) (target s z.1.val)
    ((baseAddress A hn P.colors s.report.val (key P B z.1.val) +
      (offset P B z.1.val * width s z.1.val + z.2.val)) % 2 ^ w) % 2 ^ w))
  have ha := grouping_address A hn P.colors s.report.val z
  change c.address z = baseAddress A hn P.colors s.report.val (key P B z.1.val) +
    (offset P B z.1.val * width s z.1.val + z.2.val) at ha
  rw [← ha, Nat.mod_eq_of_lt haddr, ← hx, Nat.mod_eq_of_lt (loc.isLt.trans_le ((Nat.div_le_self ..).trans hw))]
  exact congrArg s.physical (Fin.ext (Nat.mod_eq_of_lt loc.isLt).symm)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 候选引脚的元数据

带上的位置确定标签与字面值偏移量。判断某个原有物理比特是否存在，只需要其匹配编号和拟定的较小处理器索引。

**英文原文**

Metadata for a candidate pin

The tape position determines the label and literal offset. To decide
whether an old physical bit exists, only its matching number and
the proposed lower processor index are needed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Controller Diagonal Classical
variable {N l r n : ℕ}

-- 读法：归纳构造子包括 `empty`、`literal`、`broadcast`、`link`。
inductive Kind (r : ℕ) where
  | empty
  | literal
  | broadcast
  | link (j : Fin (3 * r))
  deriving DecidableEq, Fintype

-- 读法：`Fintype.card (Kind r)` 等于 `3 * r + 3`。
theorem card_kind (r : ℕ) : Fintype.card (Kind r) = 3 * r + 3 := by
  let e : Kind r ≃ Option (Option (Option (Fin (3 * r)))) := {
    toFun
      | .empty => none
      | .literal => some none
      | .broadcast => some (some none)
      | .link j => some (some (some j))
    invFun
      | none => .empty
      | some none => .literal
      | some (some none) => .broadcast
      | some (some (some j)) => .link j
    left_inv x := by cases x <;> rfl
    right_inv x := by rcases x with _ | (_ | (_ | _)) <;> rfl
  }
  rw [Fintype.card_congr e]
  simp

-- 读法：逐一匹配以下输入模式：`none`、`some (.inl _)`、`some (.inr (.inl _))`、`some (.inr (.inr p))`。
def kind : Option (Machine.Ports N l l) → Kind r
  | none => .empty
  | some (.inl _) => .literal
  | some (.inr (.inl _)) => .broadcast
  | some (.inr (.inr p)) =>
    if hp : p.val < 3 * r * (N / (4 * (3 * r))) then .link (finProdFinEquiv.symm ⟨p.val, hp⟩).1
    else .empty

-- 读法：`mode` 的结果类型为 `ℕ`。
/-- 零表示缺失，一表示字面值，二表示私有引脚。

英文原文：Zero means absent, one means literal, and two means a private pin.
-/
def mode (k : Kind r) (j : Fin (3 * r)) : ℕ :=
  match k with
  | .empty => 0
  | .literal => 1
  | .broadcast => if j.val = 0 then 2 else 0
  | .link a => if j < a - j then 2 else 0

-- 读法：逐一匹配以下输入模式：`none`、`some (.inl _)`、`some (.inr _)`。
def tag : Option (Pin N l l r) → ℕ
  | none => 0
  | some (.inl _) => 1
  | some (.inr _) => 2

-- 读法：`mode (kind p) j` 等于 `tag (p.bind fun t => prior t j)`。
theorem mode_spec (p : Option (Machine.Ports N l l)) (j : Fin (3 * r)) :
    mode (kind p) j = tag (p.bind fun t => prior t j) := by
  rcases p with _ | (x|x|x)
  · rfl
  · rfl
  · simp only [kind, mode, Option.bind_some, prior]
    split <;> rfl
  · simp only [kind, Option.bind_some, prior, physical]
    split
    · unfold mode
      dsimp only
      split <;> rfl
    · rfl

variable {F : Type} [Field F] {d h B w : ℕ} {i : Fin n}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h} {hn : 2 ≤ n}
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

-- 读法：`shared` 的取值由 `(decode s e).any (fun q => decide (source s (.inl q) ≠ target s (.inl q)))` 给出。
def shared (e : Domain N l r) := (decode s e).any (fun q => decide (source s (.inl q) ≠ target s (.inl q)))

-- 读法：`label` 的取值由 `(p.map fa).getD (fun _ => 0)` 给出。
def label [NeZero r] (fa : Machine.Ports N l l → Label n r) (p : Option (Machine.Ports N l l)) :=
  (p.map fa).getD (fun _ => 0)

-- 读法：`query` 的取值由 `.inl (.inl (cellWorker s e, label P.colors (cellPort s e)))` 给出。
/-- 即使是私有引脚，使用字面值的键也会得到正确的目的地，而这种情形只需要该端点。

英文原文：Using a literal key even for a private pin gives the correct
destination, the only endpoint needed for that case.
-/
def query [NeZero r] (e : Domain N l r) : Name n r :=
  .inl (.inl (cellWorker s e, label P.colors (cellPort s e)))

-- 读法：`placeInClass` 的取值由 `| some (.inl j) => (Records.partition (fun t => fa (.inl t))).index j | _ => 0` 给出。
def placeInClass (fa : Machine.Ports N l l → Label n r) : Option (Machine.Ports N l l) → ℕ
  | some (.inl j) => (Records.partition (fun t => fa (.inl t))).index j
  | _ => 0

-- 读法：`state` 的取值由 `if u = b then (if u = a then 1 else 2) else 0` 给出。
def state (u a b : Fin (3 * r)) : ℕ := if u = b then (if u = a then 1 else 2) else 0

-- 读法：`status` 的取值由 `let k := request A hn N s.report.val (query s e) state s.site k.1 k.2.1` 给出。
def status [NeZero r] (e : Domain N l r) :=
  let k := request A hn N s.report.val (query s e)
  state s.site k.1 k.2.1

-- 读法：`cellPort s e = some q.position` 与 `(cellWorker s e).val = old q` 同时成立。
private theorem occupied {e : Domain N l r} {q : Pin N l l r} (he : candidate s e = some q) :
    cellPort s e = some q.position ∧ (cellWorker s e).val = old q := by
  obtain ⟨p, hp, hp'⟩ := Option.bind_eq_some_iff.mp he
  obtain ⟨rfl, ho⟩ := prior_spec hp'
  exact ⟨hp, ho.symm⟩

variable [NeZero r]

-- 读法：`query s e = key P B (.inl (.inl (u, j)))` 与 `placeInClass P.colors (cellPort s e) = offset P B (.inl (.inl (u, j)))` 同时成立。
private theorem literal_key {e : Domain N l r} {u : Fin (3 * r)} {j : Fin l}
    (he : candidate s e = some (.inl (u, j))) :
    query s e = key P B (.inl (.inl (u, j))) ∧
      placeInClass P.colors (cellPort s e) = offset P B (.inl (.inl (u, j))) := by
  obtain ⟨hp, ho⟩ := occupied s he
  rw [query, hp, show cellWorker s e = u from Fin.ext ho]
  exact ⟨rfl, rfl⟩

-- 读法：`status s e` 等于 `state s.site (cellWorker s e) (target s (.inl q))`。
private theorem status_eq {e : Domain N l r} {q : Pin N l l r} (he : candidate s e = some q) :
    status s e = state s.site (cellWorker s e) (target s (.inl q)) := by
  unfold status query
  rw [(occupied s he).1]
  change state _ ((Worker.index r) ((Worker.index r).symm _)) _ = _
  rw [Equiv.apply_symm_apply]
  rfl

-- 读法：当 `e.isLeft` 成立时取 `3`，否则取 `mode (kind (cellPort s e)) (cellWorker s e)`。
def mark (e : Domain N l r) :=
  if e.isLeft then 3 else mode (kind (cellPort s e)) (cellWorker s e)

-- 读法：`activity` 的结果类型为 `ℕ`。
/-- 零表示缺失单元，一表示私有单元，二表示共享单元。

英文原文：Zero for absent cells, one for private cells and two for shared cells.
-/
def activity (mark status : ℕ) : ℕ :=
  if mark = 3 then (if status = 0 then 2 else 1) else
  if mark = 2 then (if status = 0 then 0 else 1) else
  if mark = 1 ∧ status = 2 then 2 else 0

omit [NeZero r] in
-- 读法：`source s (.inl (.inl (u, j)))` 等于 `u`。使用 `Worker.index` 给出的结论。
private theorem literal_src (u : Fin (3 * r)) (j : Fin l) :
    source s (.inl (.inl (u, j))) = u := (Worker.index r).apply_symm_apply u

-- 读法：`activity (mark s e) (status s e)` 等于 `if (decode s e).isSome then if shared s e then 2 else 1 else 0`。对 `e` 分类讨论。
theorem activity_eq (e : Domain N l r) :
    activity (mark s e) (status s e) =
      if (decode s e).isSome then if shared s e then 2 else 1 else 0 := by
  unfold mark
  rw [mode_spec]
  change activity (if e.isLeft then 3 else tag (candidate s e)) _ = _
  unfold shared
  cases e with
  | inl j =>
    have h : candidate s (.inl j) = some (.inl (s.site, j)) := rfl
    rw [decode_left, status_eq s h]
    simp [cellWorker, activity, literal_src, state]
  | inr t =>
    cases h : candidate s (.inr t) with
    | none => simp [decode, h, activity, tag]
    | some q =>
      rw [status_eq s h]
      rcases q with ⟨u, j⟩ | q
      -- 推导：记下中间结论 `he`：`cellWorker s (.inr t) = u`。
      · have he : cellWorker s (.inr t) = u := Fin.ext (occupied s h).2
        rw [he]
        by_cases hh : target s (.inl (.inl (u, j))) = s.site ∧ ¬own s (.inl (u, j))
        · simp only [decode, h, Option.bind_some, Sum.isLeft_inr, Bool.false_eq_true, false_or,
            ite_eq_left hh, Option.any_some, literal_src]
          simp [own] at hh
          simp [tag, activity, state, hh.1, hh.2, Ne.symm hh.2]
        · simp only [decode, h, Option.bind_some, Sum.isLeft_inr, Bool.false_eq_true, false_or,
            ite_eq_right hh]
          simp [own] at hh
          simp [tag, activity, state]
          grind
      -- 推导：记下中间结论 `he`：`source s (.inl (.inr q)) = target s (.inl (.inr q))`。
      · have he : source s (.inl (.inr q)) = target s (.inl (.inr q)) := rfl
        simp [decode, h, tag, activity, own, state]
        grind

variable [Fintype F] [LinearOrder (Name n r)] (C : Controller P A hn M B)

-- 读法：`expected` 的取值由 `(decode s e).any fun q => C.numberInOrder.physicalBit s (.inl q) 0` 给出。
def expected (C : Controller P A hn M B)
    (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i) (e : Domain N l r) := (decode s e).any fun q => C.numberInOrder.physicalBit s (.inl q) 0

-- 读法：`expected C s e` 等于 `if shared s e then get w s (query s e) (placeInClass P.colors (cellPort s e)) else false`。
theorem expected_eq [NeZero (N / 4)] (hw : N ≤ 2 ^ w) (e : Domain N l r) :
    expected C s e =
      if shared s e then get w s (query s e) (placeInClass P.colors (cellPort s e)) else false := by
  unfold expected shared
  cases he : decode s e with
  | none => rfl
  | some q =>
    obtain ⟨q', hc, hc'⟩ := Option.bind_eq_some_iff.mp he
    split at hc' <;> try contradiction
    cases Option.some.inj hc'
    have hi : incident s (.inl q) := by
      rcases e with j | ⟨k, u⟩
      · rw [decode_left, Option.some.injEq] at he
        rw [← he]
        exact .inl (literal_src ..)
      · exact .inr ((decode_right ..).mp he).2.2.1
    by_cases hne : source s (.inl q) ≠ target s (.inl q)
    · rcases q with ⟨u, j⟩ | q
      -- 推导：从 `literal_key s hc` 中取出 `hk, ho`。
      · obtain ⟨hk, ho⟩ := literal_key s hc
        simp only [Option.any_some, decide_eq_true_eq, ite_eq_left hne, hk, ho]
        have h : width s (.inl (.inl (u, j))) = 1 := rfl
        unfold physicalBit
        rw [dite_eq_left ⟨hne, hi, by omega⟩, C.get_eq hw]
        simp only [h, mul_one, add_zero]
      · exact (hne rfl).elim
    · simp [physicalBit, hne]

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 根据工作单元标识符批量读取静态元数据

**英文原文**

Batched reads of static metadata depending on the worker identifier
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n} (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)

include hi hw in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s j => f s.site (col j)) 37`。这里调用 `packed.named_table`。
theorem workerTable {J : Type} [Fintype J] (col : Coloring.B w → J)
    (hc : 3 * r * Fintype.card J ≤ 2 ^ w) (f : Fin (3 * r) → J → ℕ) :
    packed (U := raw _) F (C.input (i := i)) (fun s j => f s.site (col j)) 37 := by
  have : Nonempty J := ⟨col 0⟩
  have : Nonempty (Fin (3 * r)) := ⟨⟨0, Nat.mul_pos (by decide) hw.pos⟩⟩
  let a : Fin (3 * r) ≃ Fin (Fintype.card (Fin (3 * r))) := finCongr (Fintype.card_fin _).symm
  let b := Fintype.equivFin J
  have ht := packed.const (U := raw _) F (C.input (i := i)) (fun j => (b (col j)).val)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hu := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  exact packed.named_table (U := raw _) (inp := C.input (i := i)) (c := 5) (d := 0 + 2) f (by rwa [Fintype.card_fin]) (fun s (_ : Coloring.B w) => s.site) (fun _ j => col j)
    a b hu ht

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun s j => let e := request A hn N s.report.val (key s j) f s.site e.1 e.2.1) (c + 92)`。
/-- 对源点、目的地与当前站点进行的可达性检验构成任意一张静态表，其条目数至多为 `(3*r)^3`。

英文原文：The reachability tests on source, destination and current site
form an arbitrary static table of at most `(3*r)^3` entries.
-/
theorem packed_pair [LinearOrder (Name n r)] {c : ℕ} (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
    (key : X → Coloring.B w → Name n r) (idx : Name n r ↪ Coloring.B w)
    (hk : packed (U := raw _) F C.input (fun s j => (idx (key s j)).val) c)
    (f : Fin (3 * r) → Fin (3 * r) → Fin (3 * r) → ℕ) :
    packed (U := raw _) F C.input (fun s j =>
      let e := request A hn N s.report.val (key s j)
      f s.site e.1 e.2.1) (c + 92) := by
  have hr : 0 < 3 * r := Nat.mul_pos (by decide) hw.pos
  let _ : NeZero (3 * r) := ⟨Nat.ne_of_gt hr⟩
  -- 推导：记下中间结论 `fwd`：`Query n r → Fin ((3 * r) * (3 * r))`。
  let fwd : Query n r → Fin ((3 * r) * (3 * r)) := fun e => finProdFinEquiv (e.1, e.2.1)
  have hp := packed_request A hn P.colors hw hi C.input C.countPort (fun s : X => s.report.val) i
    Invocation.cut C.counts_eq key idx hk (fun j => (fwd j).val)
  have hu := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  have hcap : 3 * r * ((3 * r) * (3 * r)) ≤ 2 ^ w := by
    rw [show 3 * r * ((3 * r) * (3 * r)) = (3 * r) ^ 3 by ring]
    exact (Nat.pow_le_pow_right hr (by decide : 3 ≤ 5)).trans hw.pairs
  let k (u v : ℕ) :=
    let p := finProdFinEquiv.symm (Fin.ofNat ((3 * r) * (3 * r)) v)
    f (Fin.ofNat (3 * r) u) p.1 p.2
  have H := packed.binary k hcap hu hp (fun _ _ => Fin.isLt _) (fun _ _ => Fin.isLt _)
  convert H.mono (n := c + 92) (by omega) using 1
  funext s j
  have e {a : ℕ} [NeZero a] (v : Fin a) : Fin.ofNat a v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  simp only [k, e, fwd, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 从小型固定表读取各工作单元专用的引脚元数据

**英文原文**

Reading worker-specific pin metadata from small fixed tables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex

open Controller Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n} (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (hb : 100 * N ≤ 2 ^ w)
  (cell : Coloring.B w → Domain N l r)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

include hw hi in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun s j => if (cell j).isLeft then f s j else g s j) (max a b + 26)`。用函数外延性比较等号两侧在 `s j` 处的取值。
private theorem left {f g : Vector.Array X w} {a b : ℕ}
    (hf : packed (U := raw _) F C.input f a) (hg : packed (U := raw _) F C.input g b) :
    packed (U := raw _) F C.input (fun s j => if (cell j).isLeft then f s j else g s j)
      (max a b + 26) := by
  have ht := packed.const (U := raw _) F (C.input (i := i))
    (fun j => if (cell j).isLeft then 0 else 1) (m := 0) (w := w) (by rw [pow_zero, mul_one]; exact hi)
  have hz := packed.const (U := raw _) F (C.input (i := i)) (fun _ => 0) (m := 0) (w := w) (by rw [pow_zero, mul_one]; exact hi)
  have h2 : 1 < 2 ^ w := Nat.one_lt_pow (by have := hw.large; omega) (by decide)
  have h := ht.choose_eq hz hf hg (by intro s j; dsimp; split <;> omega) (fun _ _ => Nat.two_pow_pos w)
  convert h.mono (n := max a b + 26) (by omega) using 1
  funext s j
  cases (cell j).isLeft <;> rfl

include hw hi hb in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => f (cellPort s (cell j))) 64`。
/-- 对以工作单元所选端口为自变量的任意函数，都可以在给每份副本附上原处理器索引前先列出函数值表。

英文原文：Any function of the worker's selected port can be tabulated before
the old processor index is attached to each copy.
-/
theorem packed_port (f : Option (Machine.Ports N l l) → ℕ) :
    packed (U := raw _) F C.input (fun (s : X) j => f (cellPort s (cell j))) 64 := by
  let col : Coloring.B w → Option (Fin (4 * N / r)) := fun j =>
    Sum.elim (fun _ => none) (fun p => some p.1) (cell j)
  have hsize : 3 * r * Fintype.card (Option (Fin (4 * N / r))) ≤ 2 ^ w := by
    rw [Fintype.card_option, Fintype.card_fin]
    have hg := Nat.mul_div_le (4 * N) r
    have hr : 3 * r ≤ (3 * r) ^ 2 := Nat.le_pow (by decide)
    have := C.links
    nlinarith
  let v (u : Fin (3 * r)) (k : Option (Fin (4 * N / r))) :=
    let a := (Worker.index r).symm u
    f (k.bind (readPort P.colors (Layout.axis hn i a) (Layout.symbol a)))
  -- 推导：记下中间结论 `hp`：`= C.workerTable (i`。
  have hp := C.workerTable (i := i) hw hi col hsize v
  have hl := packed.const (U := raw _) F (C.input (i := i))
    (fun j => Sum.elim (fun x => f (some (.inl x))) (fun _ => 0) (cell j))
    (m := 0) (w := w) (by rw [pow_zero, mul_one]; exact hi)
  convert (left C hw hi cell hl hp).mono (n := 64) (by decide) using 1
  funext s j
  unfold col
  cases cell j <;> rfl

include hw hi in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => (cellWorker s (cell j)).val) 31`。用函数外延性比较等号两侧在 `s j` 处的取值。
theorem packed_worker :
    packed (U := raw _) F C.input (fun (s : X) j => (cellWorker s (cell j)).val) 31 := by
  have hp := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  have h := packed.const (U := raw _) F (C.input (i := i))
    (fun j => Sum.elim (fun _ => 0) (fun p => p.2.val) (cell j)) (m := 0) (w := w) (by rw [pow_zero, mul_one]; exact hi)
  convert (left C hw hi cell hp h).mono (n := 31) (by decide) using 1
  funext s j
  cases cell j <;> rfl

include hw hi hb in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => g (f (cellPort s (cell j))) (cellWorker s (cell j))) 96`。这里调用 `ht.mono`。
private theorem packed_table {T : Type} [Fintype T] [Nonempty T]
    (hsize : Fintype.card T * (3 * r) ≤ 2 ^ w)
    (f : Option (Machine.Ports N l l) → T) (g : T → Fin (3 * r) → ℕ) :
    packed (U := raw _) F C.input
      (fun (s : X) j => g (f (cellPort s (cell j))) (cellWorker s (cell j))) 96 := by
  let _ : Nonempty (Fin (3 * r)) := ⟨⟨0, by have := hw.pos; omega⟩⟩
  let e := Fintype.equivFin T
  let v : Fin (3 * r) ≃ Fin (Fintype.card (Fin (3 * r))) := finCongr (Fintype.card_fin _).symm
  have hv := packed_worker (i := i) C hw hi cell
  have hp := packed_port (i := i) C hw hi hb cell (fun k => (e (f k)).val)
  have ht := packed.named_table g (by rwa [Fintype.card_fin])
    (fun (s : X) j => f (cellPort s (cell j))) (fun s j => cellWorker s (cell j)) e v hp hv
  exact ht.mono (by decide)

include hw hi hb in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => (idx (query s (cell j))).val) 96`。这里调用 `packed_table`。
theorem packed_query [NeZero r] (idx : Name n r ↪ Coloring.B w) :
    packed (U := raw _) F C.input (fun (s : X) j => (idx (query s (cell j))).val) 96 := by
  have hcap : Fintype.card (Label n r) * (3 * r) ≤ 2 ^ w := by
    have := Fintype.card_le_of_injective idx idx.injective
    rw [name_card, Fintype.card_fin] at this
    rw [show Fintype.card (Label n r) = r ^ n by simp [Label], mul_comm]
    omega
  exact packed_table C hw hi hb cell hcap (label P.colors) (fun z u => (idx (.inl (.inl (u, z)))).val)

include hw hi hb in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => f (kind (cellPort s (cell j))) (cellWorker s (cell j))) 96`。这里调用 `packed_table`。
theorem packed_kind (f : Kind r → Fin (3 * r) → ℕ) :
    packed (U := raw _) F C.input
      (fun (s : X) j => f (kind (cellPort s (cell j))) (cellWorker s (cell j))) 96 := by
  let _ : Nonempty (Kind r) := ⟨.empty⟩
  have hcap : Fintype.card (Kind r) * (3 * r) ≤ 2 ^ w := by
    rw [card_kind]
    have := C.links
    have := hw.pos
    nlinarith
  exact packed_table C hw hi hb cell hcap kind f

include hw hi hb in
-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun (s : X) j => mark s (cell j)) 122`。
theorem packed_mark :
    packed (U := raw _) F C.input (fun (s : X) j => mark s (cell j)) 122 := by
  have hm := packed_kind (i := i) C hw hi hb cell mode
  have h := packed.const (U := raw _) F (C.input (i := i)) (fun _ => 3) (m := 0) (w := w) (by rw [pow_zero, mul_one]; exact hi)
  exact (left C hw hi cell h hm).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Processor.PinIndex
end

/-!
# 由工作单元标识符与报告读取类别控制信息

**英文原文**

Reading class controls from the worker identifier and report
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：`chosen` 的取值由 `PacketKernel.candidate (workerAt s) c` 给出。
def chosen (s : X) (c : PacketKernel.Spot r) := PacketKernel.candidate (workerAt s) c

omit [Fintype F] in
-- 读法：`3 * r * Fintype.card (PacketKernel.Spot r)` 不超过 `2 ^ w`。
theorem spot_fit (hw : Limits A N r (B * P.count) w) :
    3 * r * Fintype.card (PacketKernel.Spot r) ≤ 2 ^ w := by
  have : 0 < 3 * r := Nat.mul_pos (by decide) hw.pos
  rw [PacketKernel.card_spot]
  calc
    _ ≤ (3 * r) ^ 3 := by ring_nf; omega
    _ ≤ _ := (Nat.pow_le_pow_right this (by decide)).trans hw.pairs

variable [LinearOrder (Name n r)] (hw : Limits A N r (B * P.count) w)
  (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
  (idx : Name n r ↪ Coloring.B w) (a : Coloring.B w → PacketKernel.Spot r)

omit [LinearOrder (Name n r)] in
include hi hw in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s j => (idx (.inr (.inr (chosen s (a j))))).val) 37`。
theorem packed_chosen :
    packed (U := raw _) F (C.input (i := i))
      (fun s j => (idx (.inr (.inr (chosen s (a j))))).val) 37 :=
  C.workerTable hw hi a (spot_fit hw) (fun u c =>
    (idx (.inr (.inr (PacketKernel.candidate ((Worker.index r).symm u) c)))).val)

include hw hi idx in
-- 读法：结论为 `packed (U := raw _) F (C.input (i := i)) (fun s j => k (workerAt s) (A.src hn N s.report.1 (.inr (chosen s (a j)))) (A.dst hn N s.report.1 (.inr (chosen s (a j))))) 129`。
theorem packed_class_pair (k : Worker r → Worker r → Worker r → ℕ) :
    packed (U := raw _) F (C.input (i := i)) (fun s j =>
      k (workerAt s) (A.src hn N s.report.1 (.inr (chosen s (a j))))
        (A.dst hn N s.report.1 (.inr (chosen s (a j))))) 129 := by
  let f (s : X) (j : Coloring.B w) : Name n r := .inr (.inr (chosen s (a j)))
  have H := C.packed_pair hw hi f idx (C.packed_chosen hw hi idx a)
    (fun u x y => k ((Worker.index r).symm u) ((Worker.index r).symm x) ((Worker.index r).symm y))
  simpa only [f, request, descriptor, Equiv.symm_apply_apply] using H

include hw hi idx in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s j => (decide (PacketKernel.active A hn N s.report.1 (workerAt s) (a j))).toNat) 150`。
theorem packed_enabled :
    packed (U := raw _) F (C.input (i := i)) (fun s j =>
      (decide (PacketKernel.active A hn N s.report.1 (workerAt s) (a j))).toNat) 150 := by
  have h₁ := C.packed_class_pair (i := i) hw hi idx a (fun u x y => if x = u ∨ y = u then 1 else 0)
  have h₂ := C.workerTable (i := i) hw hi a (spot_fit hw) (fun u j =>
    let v := (Worker.index r).symm u
    if PacketKernel.locate v (PacketKernel.candidate v j) = j then 1 else 0)
  have hz := packed.const (U := raw _) F (C.input (i := i)) (fun _ : Coloring.B w => 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hpow : 1 < 2 ^ w := Nat.one_lt_pow (by have := hw.large; omega) (by decide)
  have hk := hz.select h₁ h₂ hz (fun _ _ => by positivity) (fun _ _ => by split <;> omega)
  convert hk.mono (n := 150) (by decide) using 1
  funext s j
  simp only [PacketKernel.active, chosen, workerAt]
  split_ifs <;> simp_all [Bool.toNat]

-- 读法：`fromEnds` 的取值由 `match x with | .home _ => if x = y then .both else .side (decide (y = u)) | _ => .joint` 给出。
private def fromEnds (u x y : Worker r) : PacketKernel.Mode :=
  match x with
  | .home _ => if x = y then .both else .side (decide (y = u))
  | _ => .joint

omit [Fintype F] [LinearOrder (Name n r)] in
-- 读法：`PacketKernel.modeAt A hn N s.report.1 (workerAt s) c` 等于 `fromEnds (workerAt s) (A.src hn N s.report.1 (.inr c)) (A.dst hn N s.report.1 (.inr c))`。
private theorem mode_ends (s : X) (c : Class r) :
    PacketKernel.modeAt A hn N s.report.1 (workerAt s) c =
      fromEnds (workerAt s) (A.src hn N s.report.1 (.inr c)) (A.dst hn N s.report.1 (.inr c)) := by
  let u := workerAt s
  let x := A.src hn N s.report.1 (.inr c)
  let y := A.dst hn N s.report.1 (.inr c)
  change (if A.shared N s.report.1 c then if x = y then PacketKernel.Mode.both
    else .side (decide (y = u)) else .joint) = fromEnds u x y
  unfold x
  cases hh : A.shared N s.report.1 c <;> simp [fromEnds, Expansion.src, hh]

include hw hi idx in
-- 读法：结论为 `packed (U := raw _) F (C.input (i := i)) (fun s j => ((PacketKernel.modeAt A hn N s.report.1 (workerAt s) (chosen s (a j))).bits (b j)).toNat) 150`。
theorem packed_mode (b : Coloring.B w → Fin 2) :
    packed (U := raw _) F (C.input (i := i)) (fun s j =>
      ((PacketKernel.modeAt A hn N s.report.1 (workerAt s) (chosen s (a j))).bits (b j)).toNat) 150 := by
  have H (v : Fin 2) := C.packed_class_pair (i := i) hw hi idx a
    (fun u x y => ((fromEnds u x y).bits v).toNat)
  have h := packed.const (U := raw _) F (C.input (i := i)) (fun j => (b j).val)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have ho := packed.const (U := raw _) F (C.input (i := i)) (fun _ : Coloring.B w => 1)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hpow : 1 < 2 ^ w := Nat.one_lt_pow (by have := hw.large; omega) (by decide)
  have hk := h.select ho (H 0) (H 1) (fun _ j => (b j).isLt.trans_le hpow) (fun _ _ => hpow)
  convert hk.mono (n := 150) (by decide) using 1
  funext s j
  rw [mode_ends]
  generalize b j = k
  fin_cases k <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 批量访问各类别的计数与总宽度

**英文原文**

Batched access to the counts and total widths of classes
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：`Fintype.card (Class r)` 等于 `r ^ 3`。
private theorem class_card : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring

variable (hw : Limits A N r (B * P.count) w) (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
  (a : Coloring.B w → PacketKernel.Spot r)

include hw hi in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s j => (A.countBits s.report.val ((chosen s (a j), (b j).1), (b j).2)).toNat) 47`。
theorem packed_counts_frame (hc : 9 * Fintype.card (A.CountBit r (B * P.count)) ≤ 2 ^ w)
    (b : Coloring.B w → A.I × Fin (countWidth P B)) :
    packed (U := raw _) F (C.input (i := i)) (fun s j =>
      (A.countBits s.report.val ((chosen s (a j), (b j).1), (b j).2)).toNat) 47 := by
  let D := A.CountBit r (B * P.count)
  let J := PacketKernel.Spot r × A.I × Fin (countWidth P B)
  let f (u : Fin (3 * r)) (z : J) : D :=
    ((PacketKernel.candidate ((Worker.index r).symm u) z.1, z.2.1), z.2.2)
  have cap : 3 * r * Fintype.card J ≤ 2 ^ w := by
    calc
      _ = 9 * Fintype.card D := by
        simp only [J, D, Expansion.CountBit, PacketKernel.Spot, Class, Fintype.card_prod, Fintype.card_fin, countWidth]
        ring
      _ ≤ _ := hc
  have : Nonempty D := ⟨f ⟨0, by have := hw.pos; omega⟩ (a 0, b 0)⟩
  obtain ⟨e⟩ : Nonempty (D ↪ Coloring.B w) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; exact hw.counts)
  -- 推导：记下中间结论 `hk`：`= C.workerTable (i`。
  have hk := C.workerTable (i := i) hw hi (fun j => (a j, b j)) cap (fun u j => (e (f u j)).val)
  have ht (j : Coloring.B w → D) : packed (U := raw _) F (C.input (i := i))
      (fun s k => (A.countBits s.report.val (j k)).toNat) 2 := by
    have h := packed.named F (C.input (i := i)) (C.countPort ∘ j) (c := 0) (by simpa using hi)
    convert h using 1
    funext s k
    exact congrArg Bool.toNat (congrFun (C.counts_eq s) (j k)).symm
  have H := packed.fetch (fun (s : X) j => f s.site (a j, b j)) e
    (fun s k => (A.countBits s.report.val k).toNat) hk ht
  exact H.mono (by decide)

include hw hi in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s k => A.classWidth s.report.val (j k)) 7`。这里调用 `packed.reshape`。
private theorem packed_all_widths (j : Coloring.B w → Class r) :
    packed (U := raw _) F (C.input (i := i)) (fun s k => A.classWidth s.report.val (j k)) 7 := by
  let v := countWidth P B
  let f := A.chargeBits i
  have hb := Install.BNet.copies (linear_register F f w v) (Class r)
  let addr : Class r × (A.I × Fin v) → Machine.Ports N l l :=
    fun p => C.countPort ((p.1, p.2.1), p.2.2)
  have h := hb.pull addr
  apply packed.reshape _ j h
  · have h₁ : Fintype.card (Class r) ≤ 2 ^ w := by
      rw [class_card]
      exact (Nat.pow_le_pow_right hw.pos (by omega)).trans hw.power
    -- 推导：记下中间结论 `h₂`：`Fintype.card (Class r) * (Fintype.card A.I * v) ≤ 2 ^ w`。
    have h₂ : Fintype.card (Class r) * (Fintype.card A.I * v) ≤ 2 ^ w := by
      simpa only [v, countWidth, Expansion.CountBit, Fintype.card_prod, Fintype.card_fin, mul_assoc] using hw.counts
    rw [Fintype.card_prod (Class r) (A.I × Fin v), Fintype.card_prod A.I (Fin v), Fintype.card_fin]
    have h₃ : Fintype.card (Class r) * (20000 * (1 + Fintype.card A.I * v) * (1 + w)) ≤
        40000 * 2 ^ w * (1 + w) := by
      have hh := Nat.mul_le_mul_right (20000 * (1 + w)) (Nat.add_le_add h₁ h₂)
      nlinarith only [hh]
    have h₄ : 50000 * (1 + w) ≤ (100 + w) ^ 7 := by ring_nf; omega
    nlinarith only [h₂, h₃, hi, Nat.mul_le_mul_right w h₁, Nat.mul_le_mul_left (2 ^ w) h₄]
  · intro s k t
    change digits w (linear f (fun y => C.input s (addr (j k, y)))) t = _
    have hh (z : A.I) : Processor.number (fun y => C.input s (addr (j k, (z, y)))) =
        (s.report.val.2 (j k, z)).val := by
      change Processor.number (fun y => (C.input s ∘ C.countPort) ((j k, z), y)) = _
      rw [C.counts_eq s]
      exact A.cnt_countBits _ _
    simp only [linear, hh, Expansion.classWidth, f, Expansion.chargeBits, s.cut]

include hw hi in
-- 读法：要证明的命题是 `packed (U := raw _) F (C.input (i := i)) (fun s j => A.classWidth s.report.val (chosen s (a j))) 47`。这里调用 `H.mono`。
theorem packed_frame_width :
    packed (U := raw _) F (C.input (i := i))
      (fun s j => A.classWidth s.report.val (chosen s (a j))) 47 := by
  have : Nonempty (Fin r) := ⟨⟨0, hw.pos⟩⟩
  obtain ⟨idx⟩ : Nonempty (Class r ↪ Coloring.B w) := Function.Embedding.nonempty_of_card_le
    (by rw [class_card, Fintype.card_fin]; exact (Nat.pow_le_pow_right hw.pos (by omega)).trans hw.power)
  have hk := C.workerTable (i := i) hw hi a (spot_fit hw)
    (fun u c => (idx (PacketKernel.candidate ((Worker.index r).symm u) c)).val)
  have H := packed.fetch (fun (s : X) j => chosen s (a j)) idx
    (fun s c => A.classWidth s.report.1 c) hk (C.packed_all_widths hw hi)
  exact H.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 用工作单元编号与可变键查询静态表

**英文原文**

Static lookups on worker numbers and variable keys
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w c : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

-- 读法：要证明的命题是 `packed (U := raw _) F C.input (fun s j => f (workerAt s) (col s j)) (c + 44)`。
theorem packed_workerLookup (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
    {J : Type} [Fintype J] [Nonempty J] (hc : 3 * r * Fintype.card J ≤ 2 ^ w)
    (col : X → Coloring.B w → J) (idx : J ↪ Coloring.B w)
    (hk : packed (U := raw _) F C.input (fun s j => (idx (col s j)).val) c)
    (f : Worker r → J → ℕ) :
    packed (U := raw _) F C.input (fun s j => f (workerAt s) (col s j)) (c + 44) := by
  have : Nonempty (Fin (3 * r)) := ⟨⟨0, Nat.mul_pos (by decide) hw.pos⟩⟩
  let a : Fin (3 * r) ≃ Fin (Fintype.card (Fin (3 * r))) := finCongr (Fintype.card_fin _).symm
  let b := Fintype.equivFin J
  have hu := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  have hslot := packed.remap col idx hk (fun j => (b j).val)
  have hv := packed.named_table (U := raw _) (inp := C.input (i := i))
    (c := 5) (d := c + 12) (fun u j => f ((Worker.index r).symm u) j)
    (by rwa [Fintype.card_fin]) (fun s (_ : Coloring.B w) => s.site) col a b hu hslot
  exact hv.mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
