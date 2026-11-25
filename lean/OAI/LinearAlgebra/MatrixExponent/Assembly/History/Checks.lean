-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Entry
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.Model

/-!
# 节省连线的步骤中采用的标准化因子

用模式与站点索引命名原站点，用一个选择器和一个位点编号命名六方构件中的角色。未改动连线的各项检查之积只需知道其关联数。

**英文原文**

Standardized factors of a wire-saving step

An old station is named by its pattern and its station index. A
six-party role is named by one selector and a site number. A product
of untouched wire checks only needs its number of incidences.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring Packing Classical Spectral.Tensor

variable {F : Type} [Field F] (S : Scheme F) (P : Gadget F) (z : ℕ) (hz : 0 < z)

-- 读法：在后续公式中，`Role` 是 `(Fin P.copies × ↥P.shapes) × Fin 6` 的缩写。
abbrev Role := (Fin P.copies × ↥P.shapes) × Fin 6
-- 读法：在后续公式中，`Kind` 是 `(B S.ℓ × B S.k) ⊕ Role P ⊕ B c` 的缩写。
abbrev Kind (c : ℕ) := (B S.ℓ × B S.k) ⊕ Role P ⊕ B c

-- 读法：用字段 `Span`、`width`、`weight` 构造 `Atom F`。
def original (p : B S.ℓ × B S.k) : Atom F where
  Span := B S.e
  width := (S.decode p.1).width p.2
  weight := (S.decode p.1).value p.2

namespace Role
variable {P} (r : Role P)

-- 读法：在后续公式中，`Demand` 是 `{q : Fin 2 × Bool // (if q.2 then (sixDemandPair q.1).2 else (sixDemandPair q.1).1) = r.2}` 的缩写。
abbrev Demand := {q : Fin 2 × Bool //
  (if q.2 then (sixDemandPair q.1).2 else (sixDemandPair q.1).1) = r.2}

-- 读法：在后续公式中，`Supply` 是 `{q : Σ j : Fin 8, Fin (r.1.2.val j) // (sixPair q.1).1 = r.2 ∨ (sixPair q.1).2 = r.2}` 的缩写。
abbrev Supply := {q : Σ j : Fin 8, Fin (r.1.2.val j) //
  (sixPair q.1).1 = r.2 ∨ (sixPair q.1).2 = r.2}

-- 读法：在后续公式中，`Port` 是 `r.Demand ⊕ r.Supply` 的缩写。
abbrev Port := r.Demand ⊕ r.Supply
-- 读法：`width` 的取值由 `Sum.elim (fun _ => P.b * z) (fun _ => z)` 给出。
def width : r.Port → ℕ := Sum.elim (fun _ => P.b * z) (fun _ => z)

variable {z}

-- 读法：`demands` 的取值由 `if h : (if s then (sixDemandPair q.1).2 else (sixDemandPair q.1).1) = r.2 then x (.inl ⟨(q.1, s), h⟩) q.2 else false` 给出。
private def demands (x : ∀ j : r.Port, Fin (width z r j) → Bool) (s : Bool)
    (q : Fin 2 × Fin (P.b * z)) : Bool :=
  if h : (if s then (sixDemandPair q.1).2 else (sixDemandPair q.1).1) = r.2
    then x (.inl ⟨(q.1, s), h⟩) q.2 else false

-- 读法：`supplies` 的结果类型为 `Bool`。
private def supplies (x : ∀ j : r.Port, Fin (width z r j) → Bool)
    (q : Σ j : Fin 8, Fin (r.1.2.val j * z)) : Bool :=
  if h : (sixPair q.1).1 = r.2 ∨ (sixPair q.1).2 = r.2
    then x (.inr ⟨⟨q.1, (finProdFinEquiv.symm q.2).1⟩, h⟩) (finProdFinEquiv.symm q.2).2
    else false

-- 读法：用字段 `Span`、`width`、`weight` 构造 `Atom F`。
def atom (hz : 0 < z) : Atom F where
  Span := r.Port
  width := width z r
  weight x := (P.packet z hz).rule.entry r.1 r.2 (r.demands x false) (r.demands x true) (r.supplies x)

-- 读法：`(r.atom hz).weight x` 等于 `(P.packet z hz).rule.entry r.1 r.2 L R U`。这里调用 `P.packet`。
theorem eval (hz : 0 < z) (x : ∀ j : r.Port, Fin (width z r j) → Bool)
    (L R : Fin 2 × Fin (P.b * z) → Bool) (U : (Σ j : Fin 8, Fin (r.1.2.val j * z)) → Bool)
    (hd : ∀ (p : r.Demand) t, x (.inl p) t = (if p.1.2 then R else L) (p.1.1, t))
    (hs : ∀ (p : r.Supply) t, x (.inr p) t = U ⟨p.1.1, finProdFinEquiv (p.1.2, t)⟩) :
    (r.atom hz).weight x = (P.packet z hz).rule.entry r.1 r.2 L R U := by
  apply (P.packet z hz).rule.local'
  · rintro ⟨j, t⟩ h
    simp only [demands, Bool.false_eq_true, ite_false, dite_eq_left h]
    exact hd ⟨(j, false), h⟩ t
  · rintro ⟨j, t⟩ h
    simp only [demands, ite_true, dite_eq_left h]
    exact hd ⟨(j, true), h⟩ t
  · rintro ⟨j, t⟩ h
    simp only [supplies, dite_eq_left h]
    refine (hs ⟨⟨j, (finProdFinEquiv.symm t).1⟩, h⟩ (finProdFinEquiv.symm t).2).trans ?_
    exact congrArg (fun t => U ⟨j, t⟩) (finProdFinEquiv.apply_symm_apply t)

end Role

-- 读法：用字段 `Span`、`width`、`weight` 构造 `Atom F`。
def checks (n : ℕ) : Atom F where
  Span := Fin n × Option (Fin P.b)
  width j := j.2.elim (P.b * z) (fun _ => z)
  weight x := if ∀ (j : Fin n) (b : Fin P.b) (t : Fin z),
    x (j, none) (finProdFinEquiv (b, t)) = x (j, some b) t then 1 else 0

-- 读法：逐一匹配以下输入模式：`.inl p`、`.inr (.inl r)`、`.inr (.inr q)`。
def kind {c : ℕ} : Kind S P c → Atom F
  | .inl p => original S p
  | .inr (.inl r) => r.atom hz
  | .inr (.inr q) => checks P z q.val

end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 每条活跃的系接线至少承载一个完整外部区段

**英文原文**

A live tether carries at least one complete exterior span
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Packing
open scoped Classical
variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T}
  {h u : ℕ} {H : HostNet F L h u} {S : Scheme F} {r : S.format.obj}
  (p : S.Presentation r H.diagram)

-- 读法：`n` 不超过 `H.tetherLoad (H.far i)`。
theorem contacts {n : ℕ} (h : ∀ j, n ≤ p.borderWidth j) (i : slots x ⊕ slots y) :
    n ≤ H.tetherLoad (H.far i) := by
  obtain ⟨⟨j, t⟩, rfl⟩ := p.exteriorBits.surjective i
  have eqn (t) : H.far (p.exteriorBits ⟨j, t⟩) = H.units.place j.val.1 :=
    congrArg H.units.place (p.border_station _)
  rw [eqn]
  let w := H.units.place j.val.1
  let e (t : Fin (p.borderWidth j)) : {q // H.far q = w} := ⟨p.exteriorBits ⟨j, t⟩, eqn t⟩
  have he : Function.Injective e := by
    intro l k hh
    exact eq_of_heq (Sigma.mk.inj (p.exteriorBits.injective (congrArg Subtype.val hh))).2
  have hc := Fintype.card_le_of_injective e he
  rw [Fintype.card_fin] at hc
  refine ((h j).trans hc).trans_eq ?_
  apply Nat.cast_injective (R := ℝ)
  rw [HostNet.tetherLoad, port_load]
  change _ = push H.far (fun _ => 1) w
  simp only [push, Finset.sum_boole, Fintype.card_subtype]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# 为新记录分配外露区段与参数

**英文原文**

Assigning the exposed spans and arguments to a new record
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  (P : Gadget F) (G : HostNet F L h (P.b * z))
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G.diagram)
  (q : G.Projection Δ D a) (U : Scheme F)

-- 读法：结构的字段包括 `host`、`block`、`index`、`seat`。
/-- 传出区段与传入区段共用一份局部地址列表。

英文原文：Outgoing and incoming spans share one local address list.
-/
structure Allocation where
  host : q.W ↪ B U.m
  block : Cell a ↪ B U.h
  index : q.W → q.W → B U.d
  seat : ∀ v, Visible g m P G.units i p v ↪ B U.e

namespace Allocation
variable {P G g m i p q U} (A : Allocation P G g m i p q U)

-- 读法：用字段 `toFun`、`inj'` 构造 `Site G.V h ↪ U.Vtx`。
def vertex : Site G.V h ↪ U.Vtx where
  toFun v := (A.host (q.place v).1, A.block (q.place v).2, 0)
  inj' _ _ he := q.place.injective (Prod.ext (A.host.injective (Prod.mk.inj he).1)
    (A.block.injective (Prod.mk.inj (Prod.mk.inj he).2).1))

local notation "atSite" => whereAt g m P G.units i p

-- 读法：`slot` 的取值由 `A.seat (atSite j) ⟨j, rfl⟩` 给出。
def slot (j : Face g m P i p) := A.seat (atSite j) ⟨j, rfl⟩

-- 读法：`A.slot j.val` 等于 `A.seat v j`。
theorem slot_eq (v : Site G.V h) (j : Visible g m P G.units i p v) :
    A.slot j.val = A.seat v j := by
  obtain ⟨j, rfl⟩ := j
  rfl

-- 读法：`span` 的取值由 `(A.vertex (atSite j), A.slot j)` 给出。
def span (j : Face g m P i p) : U.Span := (A.vertex (atSite j), A.slot j)

-- 读法：`A.span` 是单射。
theorem span_injective : Function.Injective A.span := by
  intro j k he
  have hk := A.vertex.injective (Prod.mk.inj he).1
  let t : Visible g m P G.units i p (atSite k) := ⟨j, hk⟩
  have h : A.seat _ t = A.seat _ ⟨k, rfl⟩ := (A.slot_eq _ t).symm.trans (Prod.mk.inj he).2
  exact congrArg Subtype.val ((A.seat _).injective h)

-- 读法：结构的字段包括 `used`、`idle`。
structure Lengths (out : U.format.obj) : Prop where
  used : ∀ j, U.width out (A.span j) = visibleWidth g m P i p z j
  idle : ∀ t ∉ Set.range A.span, U.width out t = 0

variable {out : U.format.obj} (l : A.Lengths out)

include l in
-- 读法：`U.width out (A.vertex v, A.seat v j)` 等于 `visibleWidth g m P i p z j.val`。这里调用 `l.used`。
theorem length_at (v : Site G.V h) (j : Visible g m P G.units i p v) :
    U.width out (A.vertex v, A.seat v j) = visibleWidth g m P i p z j.val := by
  obtain ⟨j, rfl⟩ := j
  exact l.used j

-- 读法：`orderPins` 的结果类型为 `(Σ j : Visible g m P G.units i p v, Fin (visibleWidth g m P i p z j.val)) ≃ U.LocalPin out (A.vertex v)`。
def orderPins (v : Site G.V h) :
    (Σ j : Visible g m P G.units i p v, Fin (visibleWidth g m P i p z j.val)) ≃
      U.LocalPin out (A.vertex v) :=
  Equiv.ofBijective (fun t => ⟨A.seat v t.1, t.2.cast (A.length_at l v t.1).symm⟩) ⟨by
    rintro ⟨j, b⟩ ⟨k, c⟩ he
    have hj : j = k := (A.seat v).injective (congrArg Sigma.fst he)
    subst k
    have hi : b.val = c.val := congrArg (fun p => p.2.val) he
    rw [Fin.ext hi], by
    rintro ⟨j, b⟩
    have hs : (A.vertex v, j) ∈ Set.range A.span := by
      by_contra h
      have := l.idle _ h
      have := b.isLt
      omega
    obtain ⟨k, hk⟩ := hs
    let t : Visible g m P G.units i p v := ⟨k, A.vertex.injective (Prod.mk.inj hk).1⟩
    have he : A.seat v t = j := (A.slot_eq v t).symm.trans (Prod.mk.inj hk).2
    have hl : b.val < visibleWidth g m P i p z t.val := by rw [← A.length_at l, he]; exact b.isLt
    refine ⟨⟨t, ⟨b.val, hl⟩⟩, Sigma.ext he ?_⟩
    exact (Fin.heq_ext_iff (congrArg (fun j => U.width out (A.vertex v, j)) he)).mpr rfl⟩

-- 读法：`pin` 的取值由 `(visibleBits g m P G.units hz i p v).symm.trans (A.orderPins l v)` 给出。
def pin (hz : 0 < z) (v : Site G.V h) :
    (g.contract m P G.units hz i).Port v ≃ U.LocalPin out (A.vertex v) :=
  (visibleBits g m P G.units hz i p v).symm.trans (A.orderPins l v)

-- 读法：`A.pin l hz v (visibleBits g m P G.units hz i p v ⟨j, k⟩)` 等于 `⟨A.seat v j, k.cast (A.length_at l v j).symm⟩`。
theorem pin_at (hz : 0 < z) (v : Site G.V h) (j : Visible g m P G.units i p v)
    (k : Fin (visibleWidth g m P i p z j.val)) :
    A.pin l hz v (visibleBits g m P G.units hz i p v ⟨j, k⟩) =
      ⟨A.seat v j, k.cast (A.length_at l v j).symm⟩ := by
  rw [pin, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end Allocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# 匹配子轮次中的区段地址

需求项与合并后的供给项在两端具有相同的隐藏地址。保留的供给项与外部区段沿用其可见偏移量。这些结论也覆盖两端重合的连线。

**英文原文**

Span addresses in a matched subround

Demands and merged supplies have the same hidden address at both
ends. A surviving supply and an exterior span keep their visible
offsets. These statements also cover wires whose ends coincide.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.PortMap

open Packing
open scoped Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G) (v : Site V h)

-- 读法：在后续公式中，`Port` 是 `Visible g m P s i p v ⊕ Hidden g m P i v` 的缩写。
abbrev Port := Visible g m P s i p v ⊕ Hidden g m P i v

-- 读法：`width` 的取值由 `Sum.elim (fun j => visibleWidth g m P i p z j.val) (fun j => segmentWidth g m P i z j.val)` 给出。
def width : Port g m P s i p v → ℕ :=
  Sum.elim (fun j => visibleWidth g m P i p z j.val) (fun j => segmentWidth g m P i z j.val)

-- 读法：逐一匹配以下输入模式：`.inl q, b`、`.inr q, b`。
def bit (hz : 0 < z) : (j : Port g m P s i p v) → Fin (width g m P s i p v j) →
    Bit (cluster g m P s hz i)
  | .inl q, b => .inl (faceBits g m P s hz i p ⟨q.val, b⟩)
  | .inr q, b => .inr ⟨v, hiddenBits g m P s hz i v ⟨q, b⟩⟩

-- 读法：`exterior` 的取值由 `.inl ⟨.inl x, he⟩` 给出。
def exterior (x : p.BorderSpan) (he : g.assign m P s i x.val.1 = v) : Port g m P s i p v :=
  .inl ⟨.inl x, he⟩

-- 读法：`width g m P s i p v (exterior g m P s i p v x he)` 等于 `p.borderWidth x`。两端由定义化简为同一项。
theorem width_exterior (x : p.BorderSpan) (he : g.assign m P s i x.val.1 = v) :
    width g m P s i p v (exterior g m P s i p v x he) = p.borderWidth x := rfl

-- 读法：`demand` 的结果类型为 `Port g m P s i p v`。
def demand (e : E) (t : Bool)
    (he : g.route m (g.layout m P i) (cond t (dst e) (src e)) (ix e) = v) : Port g m P s i p v :=
  .inr ⟨cond t (.inr (.inl e)) (.inl e), by cases t <;> exact Prod.ext he he⟩

-- 读法：`width g m P s i p v (demand g m P s i p v e t he)` 等于 `P.b * z`。
theorem width_demand (e : E) (t : Bool)
    (he : g.route m (g.layout m P i) (cond t (dst e) (src e)) (ix e) = v) :
    width g m P s i p v (demand g m P s i p v e t he) = P.b * z := by cases t <;> rfl

-- 读法：在后续公式中，`supplySite` 是 `cond t (g.contact m (g.layout m P i) e).2 (g.contact m (g.layout m P i) e).1` 的缩写。
abbrev supplySite (e : g.Supply m P i) (t : Bool) :=
  cond t (g.contact m (g.layout m P i) e).2 (g.contact m (g.layout m P i) e).1

-- 读法：`supply` 的结果类型为 `Port g m P s i p v`。
def supply (e : g.Supply m P i) (t : Bool) (he : supplySite g m P i e t = v) :
    Port g m P s i p v :=
  if h : (g.contact m (g.layout m P i) e).1 = (g.contact m (g.layout m P i) e).2
  then .inr ⟨.inr (.inr e), by
    cases t
    · exact Prod.ext he (h.symm.trans he)
    · exact Prod.ext (h.trans he) he⟩
  else .inl ⟨.inr (⟨e, h⟩, t), he⟩

-- 读法：`width g m P s i p v (supply g m P s i p v e t he)` 等于 `z`。
theorem width_supply (e : g.Supply m P i) (t : Bool) (he : supplySite g m P i e t = v) :
    width g m P s i p v (supply g m P s i p v e t he) = z := by
  unfold supply
  split <;> rfl

variable (hz : 0 < z)
local notation "H" => cluster g m P s hz i

-- 读法：`address H (old g m P s hz i (boundaryEnd G (p.exteriorBits ⟨x, j⟩)))` 等于 `bit g m P s i p v hz (exterior g m P s i p v x he) (j.cast (width_exterior g m P s i p v x he).symm)`。
theorem address_exterior (x : p.BorderSpan) (he : g.assign m P s i x.val.1 = v)
    (j : Fin (p.borderWidth x)) :
    address H (old g m P s hz i (boundaryEnd G (p.exteriorBits ⟨x, j⟩))) =
      bit g m P s i p v hz (exterior g m P s i p v x he) (j.cast (width_exterior g m P s i p v x he).symm) := by
  change _ = (Sum.inl (boundaryEnd (g.contract m P s hz i) (p.exteriorBits ⟨x, j⟩)) : Bit H)
  cases p.exteriorBits ⟨x, j⟩ <;> rfl

-- 读法：结论为 `let b := segmentBits g m P s hz i ⟨q.val, j⟩ address H (cond t (.inr (.inr b)) (.inl (.inr b))) = .inr ⟨v, hiddenBits g m P s hz i v ⟨q, j⟩⟩`。
private theorem address_internal (q : Hidden g m P i v) (j : Fin (segmentWidth g m P i z q.val))
    (t : Bool) :
    let b := segmentBits g m P s hz i ⟨q.val, j⟩
    address H (cond t (.inr (.inr b)) (.inl (.inr b))) =
      .inr ⟨v, hiddenBits g m P s hz i v ⟨q, j⟩⟩ := by
  have e : (H).edges.symm (segmentBits g m P s hz i ⟨q.val, j⟩) =
      .inr ⟨v, hiddenBits g m P s hz i v ⟨q, j⟩⟩ :=
    (H).edges.symm_apply_eq.mpr rfl
  cases t <;> simp only [cond, address, e, Sum.map_inr, id_eq]

-- 读法：对 `t` 分类讨论。
theorem address_demand_old (e : E) (t : Bool)
    (he : g.route m (g.layout m P i) (cond t (dst e) (src e)) (ix e) = v) (j : Fin (P.b * z)) :
    let b := s.bits.symm (e, j)
    address H (old g m P s hz i (cond t (.inr (.inr b)) (.inl (.inr b)))) =
      bit g m P s i p v hz (demand g m P s i p v e t he) (j.cast (width_demand g m P s i p v e t he).symm) := by
  cases t
  · exact address_internal g m P s i v hz ⟨.inl e, Prod.ext he he⟩ j false
  · exact address_internal g m P s i v hz ⟨.inr (.inl e), Prod.ext he he⟩ j true

-- 读法：对 `t` 分类讨论。
theorem address_demand_new (e : E) (t : Bool)
    (he : g.route m (g.layout m P i) (cond t (dst e) (src e)) (ix e) = v) (j : Fin (P.b * z)) :
    let b := s.bits.symm (e, j)
    address H (cond t (right g m P s hz i b) (left g m P s hz i b)) =
      bit g m P s i p v hz (demand g m P s i p v e t he) (j.cast (width_demand g m P s i p v e t he).symm) := by
  cases t
  · exact address_internal g m P s i v hz ⟨.inl e, Prod.ext he he⟩ j true
  · exact address_internal g m P s i v hz ⟨.inr (.inl e), Prod.ext he he⟩ j false

-- 读法：`bit g m P s i p v hz x u` 等于 `bit g m P s i p v hz y w`。
theorem bit_congr {x y : Port g m P s i p v} (h : x = y)
    {u : Fin (width g m P s i p v x)} {w : Fin (width g m P s i p v y)} (e : u.val = w.val) :
    bit g m P s i p v hz x u = bit g m P s i p v hz y w := by
  subst y
  rw [Fin.ext e]

-- 读法：按 `(g.contact m c e).1 = (g.contact m c e).2` 成立与否分情况。
theorem address_supply (e : g.Supply m P i) (t : Bool) (he : supplySite g m P i e t = v) (j : Fin z) :
    address H (Subround.supply g m P s hz i (cond t (g.supplies m e).2 (g.supplies m e).1) (e, j)) =
      bit g m P s i p v hz (supply g m P s i p v e t he) (j.cast (width_supply g m P s i p v e t he).symm) := by
  let c := g.layout m P i
  by_cases h : (g.contact m c e).1 = (g.contact m c e).2
  · have hh : g.contact m c e = (v, v) := by
      cases t
      · exact Prod.ext he (h.symm.trans he)
      · exact Prod.ext (h.trans he) he
    let q : Hidden g m P i v := ⟨.inr (.inr e), hh⟩
    -- 推导：记下中间结论 `eq`：`supply g m P s i p v e t he = .inr q`。
    have eq : supply g m P s i p v e t he = .inr q := dite_eq_left h
    refine Eq.trans ?_ (bit_congr g m P s i p v hz eq.symm (u := j) rfl)
    unfold Subround.supply
    split
    · exact address_internal g m P s i v hz q j false
    · exact address_internal g m P s i v hz q j true
  · let r : g.Survivors m P i := ⟨e, h⟩
    let q : Visible g m P s i p v := ⟨.inr (r, t), he⟩
    have eq : supply g m P s i p v e t he = .inl q := dite_eq_right h
    refine Eq.trans ?_ (bit_congr g m P s i p v hz eq.symm (u := j) rfl)
    have hn : (g.supplies m e).1 ≠ (g.supplies m e).2 := by
      rw [← g.locate_supply m c e] at h
      exact fun hh => h (congrArg (g.locate m c) hh)
    -- 推导：记下中间结论 `hx`：`(H).edges.symm (.inr (.inr (e, j))) = .inl (g.remaining m P s hz i (r, j))`。
    have hx : (H).edges.symm (.inr (.inr (e, j))) = .inl (g.remaining m P s hz i (r, j)) :=
      (H).edges.symm_apply_eq.mpr rfl
    cases t <;> simp only [cond, Subround.supply, hn, ↓reduceIte, address, hx] <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.PortMap
end

/-!
# 收缩编码的局部参数映射

**英文原文**

Local argument maps for a contraction code
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
open Packing
open scoped Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {x y : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F x y} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G) (v : Site V h)

-- 读法：结构的字段包括 `slot`、`size`、`value`。
/-- 原子的每个非空区段均读取新站点中的一个完整区段；该区段或可见，或在内部被求和消去。

英文原文：Every nonempty span of the atom reads one full span in the new
station, either visible or summed over internally.
-/
structure AtomMap (a : History.Atom F) (u : (before g m P s hz i).V) where
  slot (j : a.Span) (h : 0 < a.width j) : PortMap.Port g m P s i p v
  size (j) (h) : PortMap.width g m P s i p v (slot j h) = a.width j
  value (w : Bit (cluster g m P s hz i) → Bool) :
    a.weight (fun j t => w (PortMap.bit g m P s i p v hz
      (slot j (Nat.zero_lt_of_lt t.isLt)) (t.cast (size _ _).symm))) =
      factor (cluster g m P s hz i) u w

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# 实际六方构件中的区段连接

**英文原文**

Span links for an actual six-party gadget
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Packing Spectral.Tensor Classical

variable {F : Type} [Field F] {P : Gadget F}

-- 读法：`Role.side` 的取值由 `decide ((sixPair p.val.1).2 = r.2)` 给出。
def Role.side (r : Role P) (p : r.Supply) : Bool :=
  decide ((sixPair p.val.1).2 = r.2)

-- 读法：`cond (r.side p) (sixPair p.val.1).2 (sixPair p.val.1).1` 等于 `r.2`。按 `(sixPair p.val.1).2 = r.2` 成立与否分情况。
theorem Role.end_eq (r : Role P) (p : r.Supply) :
    cond (r.side p) (sixPair p.val.1).2 (sixPair p.val.1).1 = r.2 := by
  by_cases h : (sixPair p.val.1).2 = r.2
  · simp [side, h]
  · simpa [side, h] using p.property.resolve_right h

namespace Subround

variable {V E : Type} [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G) (v : Site V h)

local notation "col" => g.layout m P i

-- 读法：`PortMap.supplySite g m P i e t` 等于 `g.locate m col (cond t (g.supplies m e).2 (g.supplies m e).1)`。对 `t` 分类讨论。
theorem supply_at (e : g.Supply m P i) (t : Bool) :
    PortMap.supplySite g m P i e t =
      g.locate m col (cond t (g.supplies m e).2 (g.supplies m e).1) := by
  have he := g.locate_supply m col e
  cases t
  · exact congrArg Prod.fst he.symm
  · exact congrArg Prod.snd he.symm

variable (e : m.items) (j : Fin 6) (hv : g.party m (g.layout m P i) e j = v)

-- 读法：在后续公式中，`role` 是 `(i e, j)` 的缩写。
abbrev role : Role P := (i e, j)
local notation "R" => role g m P i e j

-- 读法：`roleEdge` 的取值由 `.inl ⟨e, u.val⟩` 给出。
def roleEdge (u : (R).Supply) : g.Supply m P i := .inl ⟨e, u.val⟩

-- 读法：结论为 `let f := m.pairEdge (e, q.val.1) g.route m col (cond q.val.2 (dst f) (src f)) (ix f) = g.party m col e j`。对 `d` 分类讨论。
theorem match_demand (q : (R).Demand) :
    let f := m.pairEdge (e, q.val.1)
    g.route m col (cond q.val.2 (dst f) (src f)) (ix f) = g.party m col e j := by
  rcases q with ⟨⟨q, d⟩, hq⟩
  have he := g.rep_demand m col e q
  cases d
  · change (sixDemandPair q).1 = j at hq
    subst j
    exact congrArg (fun p => g.route m col p.1 p.2) (congrArg Prod.fst he.symm)
  · change (sixDemandPair q).2 = j at hq
    subst j
    exact congrArg (fun p => g.route m col p.1 p.2) (congrArg Prod.snd he.symm)

omit [Fintype E] in
-- 读法：结论为 `let f := g.supplies m (roleEdge g m P i e j u) cond ((R).side u) f.2 f.1 = .inl ⟨e, j⟩`。
theorem match_supply (u : (R).Supply) :
    let f := g.supplies m (roleEdge g m P i e j u)
    cond ((R).side u) f.2 f.1 = .inl ⟨e, j⟩ := by
  have he := (R).end_eq u
  cases h : (R).side u <;> rw [h] at he <;>
    exact congrArg (fun j : Fin 6 => (.inl ⟨e, j⟩ : g.Parties m)) he

include hv in
-- 读法：`PortMap.supplySite g m P i (roleEdge g m P i e j u) ((R).side u)` 等于 `v`。
theorem match_site (u : (R).Supply) :
    PortMap.supplySite g m P i (roleEdge g m P i e j u) ((R).side u) = v := by
  rw [supply_at, match_supply]
  exact hv

-- 读法：逐一匹配以下输入模式：`.inl q`、`.inr u`。
def matchLinks : (R).Port → PortMap.Port g m P s i p v
  | .inl q => PortMap.demand g m P s i p v (m.pairEdge (e, q.val.1)) q.val.2
      ((match_demand g m P i e j q).trans hv)
  | .inr u => PortMap.supply g m P s i p v (roleEdge g m P i e j u) ((R).side u)
      (match_site g m P i v e j hv u)

-- 读法：`PortMap.width g m P s i p v (matchLinks g m P s i p v e j hv q)` 等于 `Role.width z (R) q`。这里调用 `PortMap.width_demand`。
theorem match_width (q : (R).Port) :
    PortMap.width g m P s i p v (matchLinks g m P s i p v e j hv q) = Role.width z (R) q := by
  rcases q with q | u
  · exact PortMap.width_demand g m P s i p v _ _ ((match_demand g m P i e j q).trans hv)
  · exact PortMap.width_supply g m P s i p v _ _ (match_site g m P i v e j hv u)

-- 读法：结论为 `((R).atom hz).weight (fun q t => w (PortMap.bit g m P s i p v hz (matchLinks g m P s i p v e j hv q) (t.cast (match_width g m P s i p v e j hv q).symm))) = factor (cluster g m P s hz i) (.inr (.inl ⟨e, j⟩)) w`。
theorem match_weight (hz : 0 < z) (w : Bit (cluster g m P s hz i) → Bool) :
    ((R).atom hz).weight (fun q t => w (PortMap.bit g m P s i p v hz
      (matchLinks g m P s i p v e j hv q) (t.cast (match_width g m P s i p v e j hv q).symm))) =
      factor (cluster g m P s hz i) (.inr (.inl ⟨e, j⟩)) w := by
  rw [paired_factor]
  refine Role.eval (R) hz _ _ _ _ ?_ ?_
  · intro q t
    have he := PortMap.address_demand_new g m P s i p v hz (m.pairEdge (e, q.val.1)) q.val.2
      ((match_demand g m P i e j q).trans hv) t
    rcases q with ⟨⟨q, d⟩, hq⟩
    cases d <;> exact congrArg w he.symm
  · intro u t
    let f := roleEdge g m P i e j u
    have he := PortMap.address_supply g m P s i p v hz f ((R).side u) (match_site g m P i v e j hv u) t
    rw [match_supply] at he
    -- 推导：记下中间结论 `eb`：`inserted g m P i e ⟨u.val.1, finProdFinEquiv (u.val.2, t)⟩ = (f, t)`。
    have eb : inserted g m P i e ⟨u.val.1, finProdFinEquiv (u.val.2, t)⟩ = (f, t) := by
      simp only [inserted, Equiv.symm_apply_apply]
      rfl
    exact (congrArg w he.symm).trans
      (congrArg (read g m P s hz i w ∘ supply g m P s hz i (.inl ⟨e, j⟩)) eb.symm)

-- 读法：用字段 `slot`、`size`、`value` 构造 `AtomMap g m P s hz i p v ((R).atom hz) (.inr (.inl ⟨e, j⟩))`。
def matchMap (hz : 0 < z) :
    AtomMap g m P s hz i p v ((R).atom hz) (.inr (.inl ⟨e, j⟩)) where
  slot q _ := matchLinks g m P s i p v e j hv q
  size q _ := match_width g m P s i p v e j hv q
  value := match_weight g m P s i p v e j hv hz

end Subround
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 为未改动连线的每个关联位置配置一个检查行

**英文原文**

One checker row per incidence of an untouched wire
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
open Packing Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (i : g.Choice m P)

-- 读法：在后续公式中，`CheckRow` 是 `{q : m.unpaired × Bool // (cond q.2 (dst q.1.val) (src q.1.val), ix q.1.val) = v}` 的缩写。
abbrev CheckRow (v : V × Cell h) :=
  {q : m.unpaired × Bool // (cond q.2 (dst q.1.val) (src q.1.val), ix q.1.val) = v}

-- 读法：结论为 `(checks P z n).weight x = Spectral.Packet.checkAt F (fun r => (src r.1, ix r.1)) v L U * Spectral.Packet.checkAt F (fun r => (dst r.1, ix r.1)) v R U`。
theorem checks_eval {v : V × Cell h} {n : ℕ} (e : Fin n ≃ CheckRow g m v)
    (x : ∀ j : Fin n × Option (Fin P.b), Fin ((checks P z n).width j) → Bool)
    (L R U : m.unpaired × Fin (P.b * z) → Bool)
    (hd : ∀ j (t : Fin (P.b * z)), x (j, none) t = cond (e j).val.2 (R ((e j).val.1, t)) (L ((e j).val.1, t)))
    (hs : ∀ j b (t : Fin z), x (j, some b) t = U ((e j).val.1, finProdFinEquiv (b, t))) :
    (checks P z n).weight x =
      Spectral.Packet.checkAt F (fun r => (src r.1, ix r.1)) v L U *
      Spectral.Packet.checkAt F (fun r => (dst r.1, ix r.1)) v R U := by
  have he : (∀ (j : Fin n) (b : Fin P.b) (t : Fin z),
      x (j, none) (finProdFinEquiv (b, t)) = x (j, some b) t) ↔
      (∀ q : m.unpaired × Fin (P.b * z), (src q.1, ix q.1) = v → L q = U q) ∧
      (∀ q : m.unpaired × Fin (P.b * z), (dst q.1, ix q.1) = v → R q = U q) := by
    simp only [hd, hs]
    constructor
    · intro H
      have hall (j : CheckRow g m v) (t : Fin (P.b * z)) :
          cond j.val.2 (R (j.val.1, t)) (L (j.val.1, t)) = U (j.val.1, t) := by
        obtain ⟨j, rfl⟩ := e.surjective j
        obtain ⟨⟨b, t⟩, rfl⟩ := finProdFinEquiv.surjective t
        exact H j b t
      exact ⟨fun q h => hall ⟨(q.1, false), h⟩ q.2, fun q h => hall ⟨(q.1, true), h⟩ q.2⟩
    · rintro ⟨hl, hr⟩ j b t
      -- 推导：从 `e j` 中取出 `⟨q, s⟩, hq`。
      obtain ⟨⟨q, s⟩, hq⟩ := e j
      cases s
      · exact hl _ hq
      · exact hr _ hq
  simp only [checks, Spectral.Packet.checkAt, he, ite_and, ite_mul, one_mul, zero_mul]
  split_ifs <;> rfl

variable {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G) (v : Site V h)
  (o : V × Cell h) (hv : g.route m (g.layout m P i) o.1 o.2 = v)
  {n : ℕ} (e : Fin n ≃ CheckRow g m o)

-- 读法：`checkEdge` 的取值由 `.inr (q.val.1, b)` 给出。
def checkEdge (q : CheckRow g m o) (b : Fin P.b) : g.Supply m P i := .inr (q.val.1, b)

omit [Fintype E] in
-- 读法：结论为 `let f := g.supplies m (checkEdge g m P i o q b) cond q.val.2 f.2 f.1 = .inr o`。
theorem check_supply (q : CheckRow g m o) (b : Fin P.b) :
    let f := g.supplies m (checkEdge g m P i o q b)
    cond q.val.2 f.2 f.1 = .inr o := by
  rcases q with ⟨⟨q, _|_⟩, h⟩ <;> exact congrArg Sum.inr h

include hv in
-- 读法：`PortMap.supplySite g m P i (checkEdge g m P i o q b) q.val.2` 等于 `v`。
theorem check_site (q : CheckRow g m o) (b : Fin P.b) :
    PortMap.supplySite g m P i (checkEdge g m P i o q b) q.val.2 = v := by
  rw [supply_at, check_supply]
  exact hv

include hv in
-- 读法：`g.route m (g.layout m P i) (cond q.val.2 (dst q.val.1) (src q.val.1)) (ix q.val.1)` 等于 `v`。通过传递性衔接 `congrArg` 与 `hv`。
theorem check_demand (q : CheckRow g m o) :
    g.route m (g.layout m P i) (cond q.val.2 (dst q.val.1) (src q.val.1)) (ix q.val.1) = v :=
  (congrArg (fun t => g.route m (g.layout m P i) t.1 t.2) q.property).trans hv

-- 读法：逐一匹配以下输入模式：`(j, none)`、`(j, some b)`。
def checkLinks : Fin n × Option (Fin P.b) → PortMap.Port g m P s i p v
  | (j, none) => PortMap.demand g m P s i p v (e j).val.1 (e j).val.2
      (check_demand g m P i v o hv (e j))
  | (j, some b) => PortMap.supply g m P s i p v (checkEdge g m P i o (e j) b) (e j).val.2
      (check_site g m P i v o hv (e j) b)

-- 读法：`PortMap.width g m P s i p v (checkLinks g m P s i p v o hv e q)` 等于 `(checks P z n).width q`。这里调用 `PortMap.width_demand`。
theorem check_width (q : Fin n × Option (Fin P.b)) :
    PortMap.width g m P s i p v (checkLinks g m P s i p v o hv e q) = (checks P z n).width q := by
  rcases q with ⟨j, _|b⟩
  · exact PortMap.width_demand g m P s i p v _ _ (check_demand g m P i v o hv (e j))
  · exact PortMap.width_supply g m P s i p v _ _ (check_site g m P i v o hv (e j) b)

-- 读法：结论为 `(checks P z n).weight (fun q t => w (PortMap.bit g m P s i p v hz (checkLinks g m P s i p v o hv e q) (t.cast (check_width g m P s i p v o hv e q).symm))) = factor (cluster g m P s hz i) (.inr (.inr o)) w`。
theorem check_weight (hz : 0 < z) (w : Bit (cluster g m P s hz i) → Bool) :
    (checks P z n).weight (fun q t => w (PortMap.bit g m P s i p v hz
      (checkLinks g m P s i p v o hv e q) (t.cast (check_width g m P s i p v o hv e q).symm))) =
      factor (cluster g m P s hz i) (.inr (.inr o)) w := by
  rw [unpaired_factor]
  refine checks_eval g m P e _ _ _ _ ?_ ?_
  · intro j t
    have he := PortMap.address_demand_new g m P s i p v hz (e j).val.1 (e j).val.2
      (check_demand g m P i v o hv (e j)) t
    refine (congrArg w he.symm).trans ?_
    cases (e j).val.2 <;> rfl
  · intro j b t
    let f := checkEdge g m P i o (e j) b
    have he := PortMap.address_supply g m P s i p v hz f (e j).val.2
      (check_site g m P i v o hv (e j) b) t
    rw [check_supply] at he
    -- 推导：记下中间结论 `eb`：`carry g m P i ((e j).val.1, finProdFinEquiv (b, t)) = (f, t)`。
    have eb : carry g m P i ((e j).val.1, finProdFinEquiv (b, t)) = (f, t) := by
      simp only [carry, Equiv.symm_apply_apply]
      rfl
    exact (congrArg w he.symm).trans
      (congrArg (read g m P s hz i w ∘ supply g m P s hz i (.inr o)) eb.symm)

-- 读法：用字段 `slot`、`size`、`value` 构造 `AtomMap g m P s hz i p v (checks P z n) (.inr (.inr o))`。
def checkMap (hz : 0 < z) :
    AtomMap g m P s hz i p v (checks P z n) (.inr (.inr o)) where
  slot q _ := checkLinks g m P s i p v o hv e q
  size q _ := check_width g m P s i p v o hv e q
  value := check_weight g m P s i p v o hv e hz

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# 依据局部记录与可见区段名称验证发布结果

**英文原文**

Certifying a posting from its local records and visible span names
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram}
  {q : G.Projection Δ D a} {U : Scheme F}
  (A : Allocation P G g m i p q U) {out : U.format.obj} (l : A.Lengths out) (hz : 0 < z)

-- 读法：在后续公式中，`unitSeat` 是 `A.slot (.inr (e, t))` 的缩写。
abbrev unitSeat (e : g.Survivors m P i) (t : Bool) := A.slot (.inr (e, t))

-- 读法：在后续公式中，`endHost` 是 `(q.place (whereAt g m P G.units i p (.inr (e, t)))).1` 的缩写。
abbrev endHost (e : g.Survivors m P i) (t : Bool) :=
  (q.place (whereAt g m P G.units i p (.inr (e, t)))).1

-- 读法：`(A.span (.inr (e, t))).1` 等于 `(A.host (endHost (p := p) (q := q) e t), A.block (q.place (g.ends' m P i e).1).2, 0)`。对 `t` 分类讨论。
private theorem site_end (e : g.Survivors m P i) (t : Bool) :
    (A.span (.inr (e, t))).1 =
      (A.host (endHost (p := p) (q := q) e t), A.block (q.place (g.ends' m P i e).1).2, 0) := by
  cases t
  · rfl
  · have eq := (q.core _ _ (g.contact_mem m G.cs G.sub G.edge (g.layout m P i) e.val)).1
    change (q.place (g.ends' m P i e).1).2 = (q.place (g.ends' m P i e).2).2 at eq
    rw [eq]
    rfl

-- 读法：结构的字段包括 `sample`、`vacant`、`outside`、`idle`、`dir`。
/-- 这些条件施加在解码后的局部模式上。站点的张量表无须知道远端宿主的名称。

英文原文：Conditions on decoded local patterns. No names of remote hosts
are needed by a station's tensor table.
-/
structure Agrees : Prop where
  sample : ∀ v t, U.table out (A.vertex v) t =
    Transcript.sample ((g.contract m P G.units hz i).table v) (t ∘ A.pin l hz v)
  vacant : ∀ v ∉ Set.range A.vertex, ∀ t, U.table out v t = 1
  outside : ∀ j, U.peer out (A.span (.inl j)) = none
  idle : ∀ t ∉ Set.range A.span, U.peer out t = none
  dir : ∀ e t, U.direction out (A.span (.inr (e, t))) = t
  link : ∀ e t, let v := A.span (.inr (e, t))
    (U.pattern out v.1).peer v.1.2.2 v.2 =
      some (A.index (endHost (p := p) (q := q) e t) (endHost (p := p) (q := q) e (!t)),
        0, A.unitSeat e (!t))
  nav : ∀ (e : g.Survivors m P i) t, let v := endHost (p := p) (q := q) e t
    let w := endHost (p := p) (q := q) e (!t)
    (out (A.host v)).1 (A.index v w) = A.host w

variable (H : A.Agrees l hz)

-- 读法：用字段 `vertex`、`pin`、`cover`、`have` 构造 `U.Seating out (g.contract m P G.units hz i)`。
def seating : U.Seating out (g.contract m P G.units hz i) where
  vertex := A.vertex
  pin := A.pin l hz
  cover v := by
    obtain ⟨j, he⟩ : v.1 ∈ Set.range A.span := by
      by_contra h
      have := l.idle _ h
      have := v.2.isLt
      omega
    exact ⟨_, congrArg Prod.fst he⟩
  sample := H.sample
  vacant := H.vacant

-- 读法：结论为 `let y := faceBits g m P G.units hz i p ⟨j, b⟩ (A.seating l hz H).ends y = ⟨A.span j, b.cast (l.used j).symm⟩`。
theorem end_pin (j : Face g m P i p) (b : Fin (visibleWidth g m P i p z j)) :
    let y := faceBits g m P G.units hz i p ⟨j, b⟩
    (A.seating l hz H).ends y = ⟨A.span j, b.cast (l.used j).symm⟩ := by
  let v := whereAt g m P G.units i p j
  let r : Visible g m P G.units i p v := ⟨j, rfl⟩
  let o := visibleBits g m P G.units hz i p v ⟨r, b⟩
  have he := visible_pin g m P G.units hz i p v ⟨r, b⟩
  change (g.contract m P G.units hz i).portEquiv ⟨v, o⟩ = faceBits g m P G.units hz i p ⟨j, b⟩ at he
  dsimp only
  rw [← he, Scheme.Seating.ends_at]
  change U.port out (A.vertex v) (A.pin l hz v o) = _
  rw [show A.pin l hz v o = _ from A.pin_at l hz v r b]
  rfl

include H in
-- 读法：`U.peer out (A.span (.inr (e, t)))` 等于 `some (A.span (.inr (e, !t)))`。这里调用 `Prod.ext`。
theorem peer_end (e : g.Survivors m P i) (t : Bool) :
    U.peer out (A.span (.inr (e, t))) = some (A.span (.inr (e, !t))) := by
  rw [Scheme.peer, H.link, Option.map_some, A.site_end]
  dsimp only
  rw [H.nav]
  apply congrArg some
  exact Prod.ext (A.site_end e (!t)).symm rfl

include H in
-- 读法：要证明的命题是 `U.Proper out`。按 `a ∈ Set.range A.span` 成立与否分情况。
theorem proper : U.Proper out := by
  intro a b h
  by_cases he : a ∈ Set.range A.span
  swap
  · rw [H.idle _ he] at h
    cases h
  obtain ⟨j|⟨e, t⟩, rfl⟩ := he
  · rw [H.outside] at h
    cases h
  rw [A.peer_end l hz H, Option.some.injEq] at h
  subst b
  rw [A.peer_end l hz H, Bool.not_not, l.used, l.used, H.dir, H.dir]
  exact ⟨rfl, rfl, by cases t <;> decide⟩

-- 读法：结论为 `let G' := g.contract m P G.units hz i (A.seating l hz H).ends (boundaryEnd G' (p.exteriorBits j)) = ⟨A.span (.inl j.1), j.2.cast (l.used (.inl j.1)).symm⟩`。使用 `A.end_pin` 给出的结论。
theorem exposed_pin (j : p.BorderBit) :
    let G' := g.contract m P G.units hz i
    (A.seating l hz H).ends (boundaryEnd G' (p.exteriorBits j)) =
      ⟨A.span (.inl j.1), j.2.cast (l.used (.inl j.1)).symm⟩ :=
  A.end_pin l hz H (.inl j.1) j.2

-- 读法：结论为 `let e' := g.remaining m P G.units hz i (e, j) (A.seating l hz H).ends (cond b (.inr (.inr e')) (.inl (.inr e'))) = ⟨A.span (.inr (e, b)), j.cast (l.used (.inr (e, b))).symm⟩`。使用 `A.end_pin` 给出的结论。
theorem unit_pin (e : g.Survivors m P i) (b : Bool) (j : Fin z) :
    let e' := g.remaining m P G.units hz i (e, j)
    (A.seating l hz H).ends (cond b (.inr (.inr e')) (.inl (.inr e'))) =
      ⟨A.span (.inr (e, b)), j.cast (l.used (.inr (e, b))).symm⟩ :=
  A.end_pin l hz H (.inr (e, b)) j

-- 读法：`U.peer out ((A.seating l hz H).ends (boundaryEnd _ j)).1` 等于 `none`。这里调用 `H.outside`。
private theorem exposed_none (j : slots x ⊕ slots y) :
    U.peer out ((A.seating l hz H).ends (boundaryEnd _ j)).1 = none := by
  obtain ⟨t, rfl⟩ := p.exteriorBits.surjective j
  rw [A.exposed_pin]
  exact H.outside t.1

-- 读法：用字段 `toSeating`、`proper`、`input`、`output` 构造 `U.Presentation out (g.contract m P G.units hz i)`。
def presentation : U.Presentation out (g.contract m P G.units hz i) where
  toSeating := A.seating l hz H
  proper := A.proper l hz H
  input t := A.exposed_none l hz H (.inl t)
  output t := A.exposed_none l hz H (.inr t)
  internal e := by
    obtain ⟨⟨a, j⟩, rfl⟩ := (g.remaining m P G.units hz i).surjective e
    have hs := A.unit_pin l hz H a false j
    have ht := A.unit_pin l hz H a true j
    dsimp only [cond] at hs ht
    rw [hs, ht]
    exact ⟨A.peer_end l hz H a false, rfl⟩

variable (hle : Δ ≤ D)

-- 读法：`U.spanAt (HostNet.contracted q g m hz hle i) A.host A.block A.unitSeat e b` 等于 `A.span (.inr (e, b))`。按 `Prod.ext` 的外延性准则比较各分量。
private theorem unit_span (e : g.Survivors m P i) (b : Bool) :
    U.spanAt (HostNet.contracted q g m hz hle i) A.host A.block A.unitSeat e b = A.span (.inr (e, b)) := by
  refine Prod.ext ?_ rfl
  cases b
  · exact (A.site_end e false).symm
  · exact (A.site_end e true).symm

-- 读法：用字段 `toPresentation`、`host`、`block`、`stub` 构造 `U.Posting out (HostNet.contracted q g m hz hle i)`。
def posting : U.Posting out (HostNet.contracted q g m hz hle i) where
  toPresentation := A.presentation l hz H
  host := A.host
  block := A.block
  stub := A.unitSeat
  index := A.index
  vertex_eq _ := rfl
  ordered e b j := by
    change g.Survivors m P i at e
    let s := (A.seating l hz H).ends (Scheme.endBit (HostNet.contracted q g m hz hle i) e b j)
    have he : s = ⟨A.span (.inr (e, b)), j.cast (l.used (.inr (e, b))).symm⟩ := A.unit_pin l hz H e b j
    change s.1 = _ ∧ s.2.val = j.val
    rw [he]
    exact ⟨(A.unit_span hz hle e b).symm, rfl⟩
  length e t := (congrArg (U.width out) (A.unit_span hz hle e t)).trans (l.used _)
  dir e t := (congrArg (U.direction out) (A.unit_span hz hle e t)).trans (H.dir e t)
  link e t := by
    change g.Survivors m P i at e
    rw [unit_span]
    cases t
    · exact H.link e false
    · exact H.link e true

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end

/-!
# 共同的宿主列表覆盖所有投影端点

**英文原文**

Projected endpoints are covered by the common host lists
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)} {Δ D k : ℕ} {B' : ℝ}
  {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram} {q : G.Projection Δ D a}

-- 读法：`endHost (p := p) (q := q) e (!t)` 属于 `q.C (endHost (p := p) (q := q) e t)`。对 `t` 分类讨论。
theorem end_contact (e : g.Survivors m P i) (t : Bool) :
    endHost (p := p) (q := q) e (!t) ∈ q.C (endHost (p := p) (q := q) e t) := by
  have h := (q.core _ _ (g.contact_mem m G.cs G.sub G.edge (g.layout m P i) e.val)).2
  cases t
  · exact h
  · exact q.cs _ _ h

-- 读法：结论为 `let v := endHost (p := p) (q := q) e t let w := endHost (p := p) (q := q) e (!t) nav (A.host v) (A.index v w) = A.host w`。
theorem end_nav {U : Scheme F} (A : Allocation P G g m i p q U) (nav : B U.m → B U.d → B U.m)
    (cover : ∀ v w, w ∈ q.C v → nav (A.host v) (A.index v w) = A.host w)
    (e : g.Survivors m P i) (t : Bool) :
    let v := endHost (p := p) (q := q) e t
    let w := endHost (p := p) (q := q) e (!t)
    nav (A.host v) (A.index v w) = A.host w :=
  cover _ _ (end_contact e t)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end
