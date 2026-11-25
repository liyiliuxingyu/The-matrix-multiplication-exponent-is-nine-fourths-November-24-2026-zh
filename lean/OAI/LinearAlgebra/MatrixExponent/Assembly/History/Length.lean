-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.State
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Guard
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Prefix
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Radius
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep

/-!
# 输出连线的另一端

可见供给项的发出位置相距不超过两跳，且两端点到该发出位置也各不超过两跳。再走四跳即可还原另一端的紧凑字典。

**英文原文**

The opposite end of an emitted wire

A visible supply was issued within two hops, and both endpoints are
within two hops of that issuer. Four more hops recover the compact
dictionary at the opposite end.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Packing
open scoped Classical

namespace Window

-- 读法：`α.node (q ++ p)` 等于 `({ α with root := α.node p } : Env V X d h e ℓ).node q`。
private theorem node_append {V X : Type} {d h e ℓ : ℕ} (α : Env V X d h e ℓ) (p q : List (B d)) :
    α.node (q ++ p) = ({ α with root := α.node p } : Env V X d h e ℓ).node q := by
  simp only [Env.node, visit, List.foldr_append]

-- 读法：要证明的命题是 `Agree { α with root := v } { β with root := w } m`。这里调用 `h.same`。
theorem Agree.reroot {V W X : Type} {d h e ℓ n m : ℕ} {α : Env V X d h e ℓ} {β : Env W X d h e ℓ}
    {v : V} {w : W} (h : Agree α β (m + n)) (hr : Related α β n v w) :
    Agree { α with root := v } { β with root := w } m := by
  obtain ⟨p, hp, rfl, rfl⟩ := hr
  have bound (q : List (B d)) (hq : q.length ≤ m) : (q ++ p).length ≤ m + n := by
    rw [List.length_append]; exact Nat.add_le_add hq hp
  constructor
  · intro q r hq hr
    simpa only [node_append] using h.same _ _ (bound q hq) (bound r hr)
  · intro q hq
    simpa only [node_append] using h.data _ (bound q hq)
  · intro q hq
    simpa only [node_append] using h.recv _ (bound q hq)
  · intro q hq
    simpa only [node_append] using h.extra _ (bound q hq)

end Window

namespace State
open Window Navigation.Emission

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B')

-- 读法：在后续公式中，`endAt` 是 `cond s (u.g.contact u.m u.col t).2 (u.g.contact u.m u.col t).1` 的缩写。
abbrev endAt (t : u.g.Supply u.m P u.i) (s : Bool) :=
  cond s (u.g.contact u.m u.col t).2 (u.g.contact u.m u.col t).1

-- 读法：在后续公式中，`nameAt` 是 `u.q.supplyKey u.g u.m u.col P u.i t s` 的缩写。
abbrev nameAt (t : u.g.Supply u.m P u.i) (s : Bool) := u.q.supplyKey u.g u.m u.col P u.i t s

-- 读法：`(u.c.event P u.i t).1.1` 属于 `u.env.issuers`。
private theorem in_window (t : u.g.Supply u.m P u.i) (s : Bool) (he : u.endAt t s = u.v) :
    (u.c.event P u.i t).1.1 ∈ u.env.issuers := by
  have hw := u.q.window_supply u.g u.m u.col P u.i t s
  change _ ∈ u.q.neighborhood (u.endAt t s).1 at hw
  rw [he] at hw
  rcases t with ⟨t, j, i⟩ | ⟨t, i⟩ <;> exact hw

variable {u} {v : State S P a h z Δ D k B'} {n : ℕ}

-- 读法：存在 `t : v.g.Supply v.m P v.i`，`v.endAt t b = v.v` 与 `∀ c, u.nameAt s c = v.nameAt t c ∧ Names u.env v.env (u.c.site (u.endAt s c)) (v.c.site (v.endAt t c))` 同时成立。
private theorem Same.matched (e : u.Same v n) (hn : 4 ≤ n)
    (s : u.g.Supply u.m P u.i) (b : Bool) (hs : u.endAt s b = u.v) :
    ∃ t : v.g.Supply v.m P v.i, v.endAt t b = v.v ∧ ∀ c,
      u.nameAt s c = v.nameAt t c ∧ Names u.env v.env (u.c.site (u.endAt s c)) (v.c.site (v.endAt t c)) := by
  let A := e.agree.restrict hn
  let j := u.c.event P u.i s
  obtain ⟨w, _, hw⟩ := Related.issuers (β := v.env) (u.in_window s b hs)
  let j' := ((w, j.1.2), j.2)
  have enable := A.enabled hw (fun x i => profileOf P (x.2 i)) j.1.2 j.2
  have ok := (u.c.enabled_iff P u.i (profileOf P ∘ u.selector) u.code j).mpr ⟨s, rfl⟩
  -- 推导：从 `(v.c.enabled_iff P v.i (profileOf P ∘ v.selector) v.code j').mp (enable.symm.trans ok)` 中取出 `t, ht`。
  obtain ⟨t, ht⟩ := (v.c.enabled_iff P v.i (profileOf P ∘ v.selector) v.code j').mp (enable.symm.trans ok)
  have keys (c) : u.nameAt s c = v.nameAt t c := by
    have H := A.supplies hw (by decide) u.col j.1.2 j.2
    change u.env.supplies u.col j = v.env.supplies u.col j' at H
    refine (u.p.supply_key u.hu a u.ha u.g u.m u.ctl u.i s c).trans ?_
    refine Eq.trans ?_ (v.p.supply_key v.hu a v.ha v.g v.m v.ctl v.i t c).symm
    change supply u.col (u.env.supplies u.col j) j.2 c =
      supply v.col (v.env.supplies v.col (v.c.event P v.i t)) (v.c.event P v.i t).2 c
    rw [ht, H, e.layout]
  have sites (c) : Names u.env v.env (u.c.site (u.endAt s c)) (v.c.site (v.endAt t c)) := by
    have hu := u.p.newAt_eq u.hu a u.ha u.g u.m u.ctl u.i s c
    have hv := v.p.newAt_eq v.hu a v.ha v.g v.m v.ctl v.i t c
    change newAt u.env.nav u.env.data u.col j c = u.c.site (u.endAt s c) at hu
    change newAt v.env.nav v.env.data v.col (v.c.event P v.i t) c = v.c.site (v.endAt t c) at hv
    rw [← hu, ← hv, ht, ← e.layout]
    exact A.newAt hw u.col j.1.2 j.2 c
  have root : Names u.env v.env (u.c.site u.v) (v.c.site v.v) :=
    ⟨related_root.widen (by decide), e.key⟩
  exact ⟨t, v.c.site.injective ((A.identical (sites b) root).mp (congrArg u.c.site hs)),
    fun c => ⟨keys c, sites c⟩⟩

-- 读法：在后续公式中，`recenter` 是 `{ u with v := x }` 的缩写。
/-- 固定图式及其中各项选择，仅更换所查询的位点。

英文原文：Keep the diagram and its choices fixed, changing only the queried site.
-/
abbrev recenter (u : State S P a h z Δ D k B') (x : Site (u.G.V × Cell a) (h - a)) :=
  { u with v := x }

-- 读法：结论为 `u.nameAt s (!b) = v.nameAt t (!b) ∧ Related u.env v.env 4 (u.endAt s (!b)).1 (v.endAt t (!b)).1 ∧ (u.recenter (u.endAt s (!b))).Same (v.recenter (v.endAt t (!b))) 4`。
theorem Same.supply_remote (e : u.Same v n) (hn : 8 ≤ n)
    {s : u.g.Supply u.m P u.i} {t : v.g.Supply v.m P v.i} {b : Bool}
    (hs : u.endAt s b = u.v) (ht : v.endAt t b = v.v) (he : u.nameAt s b = v.nameAt t b) :
    u.nameAt s (!b) = v.nameAt t (!b) ∧
      Related u.env v.env 4 (u.endAt s (!b)).1 (v.endAt t (!b)).1 ∧
      (u.recenter (u.endAt s (!b))).Same (v.recenter (v.endAt t (!b))) 4 := by
  obtain ⟨q, hq, h⟩ := e.matched (by omega) s b hs
  have ha : v.H.anchor v.g v.m v.col (Navigation.supplyAtom (G := v.H) v.g v.m P v.i q b) =
      v.H.anchor v.g v.m v.col (Navigation.supplyAtom (G := v.H) v.g v.m P v.i t b) := by
    have eq := Navigation.supply_anchor (G := v.H) v.g v.m v.col P v.i
    exact (eq q b).trans ((hq.trans ht.symm).trans (eq t b).symm)
  have hqt := v.q.supply_unique v.g v.m v.col P v.i ha ((h b).1.symm.trans he)
  have : q = t := congrArg Prod.fst hqt
  subst q
  obtain ⟨hk, hr, hi⟩ := h (!b)
  exact ⟨hk, hr, (e.agree.restrict hn).reroot (m := 4) hr, e.layout, hi⟩

end State
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 由局部信息确定输出的首部及对端位置

**英文原文**

Local determination of emitted headers and peer seats
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State

open Coloring Packing History History.Subround
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B')

-- 读法：在后续公式中，`Faces` 是 `Face u.g u.m P u.i u.p.toPresentation` 的缩写。
abbrev Faces := Face u.g u.m P u.i u.p.toPresentation
-- 读法：在后续公式中，`faceName` 是 `Navigation.faceKey P u.H u.g u.m u.i u.p.toPresentation u.q` 的缩写。
abbrev faceName := Navigation.faceKey P u.H u.g u.m u.i u.p.toPresentation u.q
-- 读法：在后续公式中，`faceWidth` 是 `visibleWidth u.g u.m P u.i u.p.toPresentation z` 的缩写。
abbrev faceWidth := visibleWidth u.g u.m P u.i u.p.toPresentation z
-- 读法：在后续公式中，`localFaces` 是 `Visible u.g u.m P u.H.units u.i u.p.toPresentation u.v` 的缩写。
abbrev localFaces := Visible u.g u.m P u.H.units u.i u.p.toPresentation u.v

variable {m' d' a' e' ℓ n' l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
    {unpack : Y.obj → (History.code n' e' l s ℓ).obj}

-- 读法：在后续公式中，`Assignment` 是 `Allocation P u.H u.g u.m u.i u.p.toPresentation (u.G.project a u.ha Δ D hle) Z` 的缩写。
abbrev Assignment (hle : Δ ≤ D) (Z : Scheme F) :=
  Allocation P u.H u.g u.m u.i u.p.toPresentation (u.G.project a u.ha Δ D hle) Z

variable {hle : Δ ≤ D}

-- 读法：`Ranked` 表示以下条件：对每个 `w t`，`(A.seat w t).val` 等于 `Navigation.index (u.recenter w).lists.2.2 (u.faceName t.val)`。
/-- 面键在局部列表中的序号即为其紧凑位置编号。

英文原文：A compact seat is the rank of the face key in the local list.
-/
def Ranked {Z : Scheme F} (A : u.Assignment hle Z) : Prop :=
  ∀ w t, (A.seat w t).val = Navigation.index (u.recenter w).lists.2.2 (u.faceName t.val)

variable {u} {v : State S P a h z Δ D k B'} {n : ℕ}
  (e : u.Same v n) (hn : 8 ≤ n) (α : u.Assignment hle (Post.scheme m' d' a' e' Y M unpack))
  (β : v.Assignment hle (Post.scheme m' d' a' e' Y M unpack))
  (sizeA : u.Faces → B ℓ) (sizeB : v.Faces → B ℓ)
  (hsize : ∀ i j, u.faceWidth i = v.faceWidth j → sizeA i = sizeB j)
  (hindex : ∀ (x : Site (u.G.V × Cell a) (h - a)) (y : Site (v.G.V × Cell a) (h - a)),
    Window.Related u.env v.env 4 x.1 y.1 → intervalCode _ x.2 = intervalCode _ y.2 →
    α.index (u.v.1.1, u.v.2) (x.1.1, x.2) = β.index (v.v.1.1, v.v.2) (y.1.1, y.2))
  (ha : u.Ranked α) (hb : v.Ranked β)

include ha hb in
-- 读法：`α.seat x i` 等于 `β.seat y j`。按 `Fin.ext` 的外延性准则比较各分量。
private theorem seats {x : Site (u.G.V × Cell a) (h - a)} {y : Site (v.G.V × Cell a) (h - a)}
    (hlist : (u.recenter x).lists = (v.recenter y).lists)
    (i : (u.recenter x).localFaces) (j : (v.recenter y).localFaces)
    (hij : u.faceName i.val = v.faceName j.val) : α.seat x i = β.seat y j := by
  apply Fin.ext
  have hl := congrArg (fun t : Window.Lists S.d S.e (h - a) P.b => t.2.2) hlist
  have hi := ha x i
  have hj := hb y j
  exact hi.trans ((congrArg₂ Navigation.index hl hij).trans hj.symm)

-- 读法：`t ∈ u.lists.2.2` 与 `∃ i : u.localFaces, u.faceName i.val = t` 等价。
private theorem face_mem (u : State S P a h z Δ D k B') (t : Navigation.SpanKey S.d S.e (h - a) P.b) :
    t ∈ u.lists.2.2 ↔ ∃ i : u.localFaces, u.faceName i.val = t := by
  change t ∈ Finset.univ.map (Navigation.visibleNames P u.H u.g u.m u.i u.p.toPresentation u.v u.q) ↔ _
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  rfl

include e hn ha hb in
-- 读法：存在 `j : v.localFaces`，`u.faceName i.val = v.faceName j.val` 与 `α.seat u.v i = β.seat v.v j` 同时成立。
theorem match_seat (i : u.localFaces) :
    ∃ j : v.localFaces, u.faceName i.val = v.faceName j.val ∧ α.seat u.v i = β.seat v.v j := by
  have hl := e.lists (by omega)
  have hm := (face_mem u _).mpr ⟨i, rfl⟩
  rw [hl] at hm
  obtain ⟨j, hj⟩ := (face_mem v _).mp hm
  exact ⟨j, hj.symm, seats α β ha hb (x := u.v) (y := v.v) hl i j hj.symm⟩

include e hn hsize hindex ha hb

-- 读法：`α.header sizeA i.val` 等于 `β.header sizeB j.val`。这里调用 `Prod.ext`。
theorem Same.header {i : u.localFaces} {j : v.localFaces}
    (he : u.faceName i.val = v.faceName j.val) : α.header sizeA i.val = β.header sizeB j.val := by
  rcases i with ⟨i | ⟨i, b⟩, hi⟩ <;> rcases j with ⟨j | ⟨j, c⟩, hj⟩
  · obtain ⟨hw, hd⟩ := e.exterior (by omega) hi hj he
    exact Prod.ext (hsize (.inl i) (.inl j) hw) (Prod.ext hd rfl)
  · cases he
  · cases he
  · have key : u.nameAt i.val b = v.nameAt j.val c := Sum.inr.inj he
    have dir := congrArg Prod.fst key
    change b = c at dir
    subst c
    -- 推导：从 `e.supply_remote hn hi hj key` 中取出 `hk, hr, h`。
    obtain ⟨hk, hr, h⟩ := e.supply_remote hn hi hj key
    have hs := h.lists le_rfl
    let x := u.endAt i.val (!b)
    let y := v.endAt j.val (!b)
    have seat : α.unitSeat i (!b) = β.unitSeat j (!b) := by
      have he : u.faceName (.inr (i, !b)) = v.faceName (.inr (j, !b)) := congrArg Sum.inr hk
      exact seats α β ha hb (x := x) (y := y) hs ⟨.inr (i, !b), rfl⟩ ⟨.inr (j, !b), rfl⟩ he
    have idx := hindex x y hr h.key
    change u.endAt i.val b = u.v at hi
    change v.endAt j.val b = v.v at hj
    have heq : α.index ((u.endAt i.val b).1.1, (u.endAt i.val b).2) (x.1.1, x.2) =
        β.index ((v.endAt j.val b).1.1, (v.endAt j.val b).2) (y.1.1, y.2) := by
      rw [hi, hj]
      exact idx
    exact Prod.ext (hsize (.inr (i, b)) (.inr (j, b)) rfl) (Prod.ext rfl (Prod.ext rfl (Prod.ext heq seat)))

-- 读法：`α.fields sizeA u.v` 等于 `β.fields sizeB v.v`。用函数外延性比较等号两侧在 `r` 处的取值。
/-- 相同的键占用相同的位置，且未使用位置的默认值也相同。

英文原文：Equal keys occupy equal seats, with the same unused-seat default.
-/
theorem Same.fields : α.fields sizeA u.v = β.fields sizeB v.v := by
  funext r
  unfold Allocation.fields
  by_cases hr : r ∈ Set.range (α.seat u.v)
  · obtain ⟨i, rfl⟩ := hr
    obtain ⟨j, hj, he⟩ := match_seat e hn α β ha hb i
    rw [(α.seat u.v).injective.extend_apply, he]
    refine (e.header hn α β sizeA sizeB hsize hindex ha hb hj).trans ?_
    exact ((β.seat v.v).injective.extend_apply (fun t => β.header sizeB t.val) (fun _ => Post.unused) j).symm
  · have hr' : r ∉ Set.range (β.seat v.v) := by
      rintro ⟨j, hj⟩
      obtain ⟨i, _, he⟩ := match_seat e.symm hn β α hb ha j
      exact hr ⟨i, he.symm.trans hj⟩
    rw [Function.extend_apply' _ _ _ hr, Function.extend_apply' _ _ _ hr']

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 节省连线的步骤中实际使用的原子因子

**英文原文**

The actual atomic factors in a wire-saving step
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History.Subround
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B')

-- 读法：`atomMap` 的结果类型为 `AtomMap u.g u.m P u.H.units u.hz u.i u.p.toPresentation u.v (History.kind S P z u.hz (u.kind j)) j`。
def atomMap (j : u.H.Atom u.g u.m) (hj : u.H.anchor u.g u.m u.col j = u.v) :
    AtomMap u.g u.m P u.H.units u.hz u.i u.p.toPresentation u.v (History.kind S P z u.hz (u.kind j)) j :=
  match j, hj with
  | .inl w, hw => u.p.oldMap a u.ha u.g u.m u.i u.v w hw u.hz
  | .inr (.inl ⟨t, i⟩), ht => matchMap u.g u.m P u.H.units u.i u.p.toPresentation u.v t i ht u.hz
  | .inr (.inr w), hw => checkMap u.g u.m P u.H.units u.i u.p.toPresentation u.v w hw (u.checkOrder w) u.hz

-- 读法：用字段 `label`、`arg` 构造 `Bundle P u.H u.g u.m u.i u.p.toPresentation u.hz u.v (S.e + 2)`。
def bundle : Bundle P u.H u.g u.m u.i u.p.toPresentation u.hz u.v (S.e + 2) where
  label t := u.kind t.val
  arg t := u.atomMap t.val ((anchor_eq _).trans (includeAtom u.hz t).property)

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 收缩后出现位置的打包编码

**英文原文**

The packed code of a contracted occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History.Subround
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k e l s d : ℕ} {B' : ℝ} (u : State S P a h z Δ D k B')

-- 读法：结构的字段包括 `budget`、`contacts`、`floor`。
structure Room (e : ℕ) : Prop where
  budget : Navigation.Budget P u.H Δ k B' e
  contacts : ∀ t, P.b * z ≤ u.H.tetherLoad (u.H.far t)
  floor : ∀ t, z ≤ u.p.toPresentation.borderWidth t

-- 读法：当 `(u.q.hiddenKey u.g u.m P u.i q.val).isRight` 成立时取 `new`，否则取 `old`。
def hiddenSize (old new : B d) (q : Hidden u.g u.m P u.i u.v) : B d :=
  if (u.q.hiddenKey u.g u.m P u.i q.val).isRight then new else old

-- 读法：`len (u.hiddenSize old new q)` 等于 `segmentWidth u.g u.m P u.i z q.val`。
theorem hiddenSize_spec (old new : B d) (len : B d → ℕ)
    (ho : len old = P.b * z) (hn : len new = z) (q : Hidden u.g u.m P u.i u.v) :
    len (u.hiddenSize old new q) = segmentWidth u.g u.m P u.i z q.val := by
  rcases q with ⟨q|q|q, _⟩
  · exact ho
  · exact ho
  · exact hn

namespace Room
variable {u} (R : u.Room e)

include R in
-- 读法：要证明的命题是 `(u.recenter x).Room e`。
theorem recenter (x : Site (u.G.V × Cell a) (h - a)) : (u.recenter x).Room e :=
  ⟨R.budget, R.contacts, R.floor⟩

-- 读法：在后续公式中，`atoms` 是 `u.q.atoms u.g u.m u.i R.budget R.contacts u.v` 的缩写。
abbrev atoms := u.q.atoms u.g u.m u.i R.budget R.contacts u.v
-- 读法：在后续公式中，`hidden` 是 `u.q.hidden u.g u.m u.i R.budget u.v` 的缩写。
abbrev hidden := u.q.hidden u.g u.m u.i R.budget u.v
-- 读法：在后续公式中，`visible` 是 `u.q.visible u.g u.m u.i u.p.toPresentation R.budget R.floor u.v` 的缩写。
abbrev visible := u.q.visible u.g u.m u.i u.p.toPresentation R.budget R.floor u.v
end Room

-- 读法：`packedCode` 的取值由 `(u.bundle.packed names index R.visible (u.hiddenSize old new)).encode R.atoms R.hidden` 给出。
def packedCode (R : u.Room e) (names : History.Kind S P (S.e + 2) ↪ B l)
    (index : ∀ j : History.Kind S P (S.e + 2), (History.kind S P z u.hz j).Span ↪ B s)
    (old new : B d) : (History.code e e l s d).obj :=
  (u.bundle.packed names index R.visible (u.hiddenSize old new)).encode R.atoms R.hidden

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 收缩后出现位置的公共字典与记录

索引和长度编码均一次选定，与宿主数、出现位置以及局部数据包的选取无关。

**英文原文**

The common dictionary and record of a contracted occurrence

Indices and length codes are chosen once, independently of the
number of hosts, the occurrence, and the local packet choices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing History History.Subround
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {z : ℕ} {hz : 0 < z}

namespace History

-- 读法：结构的字段包括 `ord`、`s`、`index`、`d`、`len`。
structure Book (S : Scheme F) (P : Gadget F) (z : ℕ) (hz : 0 < z) where
  ord : B S.ℓ ≃ B S.ℓ
  s : ℕ
  index : ∀ j : Kind S P (S.e + 2), (kind S P z hz j).Span ↪ B s
  d : ℕ
  len : B d → ℕ
  put : ℕ → B d
  zero : len 0 = 0
  old : len (put (P.b * z)) = P.b * z
  unit : len (put z) = z

namespace Book
variable (b : Book S P z hz)

-- 读法：在后续公式中，`names` 是 `Kind.names S P (S.e + 2) b.ord` 的缩写。
abbrev names := Kind.names S P (S.e + 2) b.ord
-- 读法：在后续公式中，`menu` 是 `History.menu (kind S P z hz) b.names b.index b.len` 的缩写。
abbrev menu := History.menu (kind S P z hz) b.names b.index b.len
-- 读法：在后续公式中，`scheme` 是 `Post.scheme m d h e (.addr cap) b.menu (Dense.unpack (m := e) cap)` 的缩写。
abbrev scheme (m d h e cap : ℕ) := Post.scheme m d h e (.addr cap) b.menu (Dense.unpack (m := e) cap)
-- 读法：在后续公式中，`overhead` 是 `Post.bookkeeping e e b.s b.d S.ℓ (Kind.width S P (S.e + 2))` 的缩写。
abbrev overhead (e : ℕ) := Post.bookkeeping e e b.s b.d S.ℓ (Kind.width S P (S.e + 2))

end Book
end History

namespace State
variable {a h Δ D k e m' d' h' : ℕ} {B' : ℝ} {hle : Δ ≤ D}
    (u : State S P a h z Δ D k B') (b : Book S P z hz) (r : u.Room e)

-- 读法：在后续公式中，`codeAt` 是 `u.packedCode r b.names b.index (b.put (P.b * z)) (b.put z)` 的缩写。
abbrev codeAt := u.packedCode r b.names b.index (b.put (P.b * z)) (b.put z)

-- 读法：`data` 的取值由 `Dense.encode cap (u.codeAt b r)` 给出。
def data (cap : ℕ) : B cap := Dense.encode cap (u.codeAt b r)

-- 读法：`Dense.unpack cap (u.data b r cap)` 等于 `u.codeAt b r`。这里调用 `Dense.unpack_encode`。
theorem unpack_data (cap : ℕ) (h : b.overhead e + u.inherited b.ord ≤ cap) :
    Dense.unpack cap (u.data b r cap) = u.codeAt b r := by
  apply Dense.unpack_encode
  exact (Post.packed_length S P b.ord _ _ _ _ rfl).trans h

-- 读法：在后续公式中，`sizes` 是 `b.put (visibleWidth u.g u.m P u.i u.p.toPresentation z j)` 的缩写。
abbrev sizes (j : Face u.g u.m P u.i u.p.toPresentation) :=
  b.put (visibleWidth u.g u.m P u.i u.p.toPresentation z j)

-- 读法：`payload` 的取值由 `(u.recenter v).data b (r.recenter v) cap` 给出。
def payload (cap : ℕ) (v : Site u.H.V (h - a)) : B cap :=
  (u.recenter v).data b (r.recenter v) cap

variable (cap : ℕ)
    (A : Allocation P u.H u.g u.m u.i u.p.toPresentation (u.G.project a u.ha Δ D hle)
      (b.scheme m' d' h' e cap))

-- 读法：`localRecord` 的取值由 `(true, A.fields (u.sizes b) u.v, u.data b r cap)` 给出。
def localRecord : (Post.record d' e b.d (.addr cap)).obj :=
  (true, A.fields (u.sizes b) u.v, u.data b r cap)

-- 读法：在后续公式中，`records` 是 `A.records (u.sizes b) (u.payload b r cap)` 的缩写。
abbrev records := A.records (u.sizes b) (u.payload b r cap)

-- 读法：`u.records b r cap A (A.vertex v).1 (A.vertex v).2.1` 等于 `(u.recenter v).localRecord b (r.recenter v) cap A`。使用 `A.record_at` 给出的结论。
theorem record_at (v : Site u.H.V (h - a)) :
    u.records b r cap A (A.vertex v).1 (A.vertex v).2.1 =
      (u.recenter v).localRecord b (r.recenter v) cap A := A.record_at _ _ _

end State
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 因子区段与长度的公共字典

外部宽度从固定的备选集合中选取。两个内部长度与空闲长度至多再需三个条目。

**英文原文**

Common dictionaries of factor spans and lengths

Exterior widths use a fixed palette. The two interior lengths and the
idle length cost at most three further entries.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Book
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (S : Scheme F) (P : Gadget F) (z : ℕ) (hz : 0 < z)

-- 读法：在后续公式中，`spanBits` 是 `S.e + 2 + Nat.clog 2 (P.b + 1)` 的缩写。
abbrev spanBits := S.e + 2 + Nat.clog 2 (P.b + 1)

-- 读法：`Fintype.card t.Port` 不超过 `4 * (P.b + 1)`。
private theorem role_card (t : Role P) : Fintype.card t.Port ≤ 4 * (P.b + 1) := by
  have hd : Fintype.card t.Demand ≤ 4 :=
    (Fintype.card_subtype_le _).trans_eq (by simp)
  have hs : Fintype.card t.Supply ≤ ∑ j, t.1.2.val j :=
    (Fintype.card_subtype_le _).trans_eq (by simp)
  have hb := P.cost t.1.2.val t.1.2.property
  change Fintype.card (t.Demand ⊕ t.Supply) ≤ _
  rw [Fintype.card_sum]
  omega

-- 读法：`((kind S P z hz j).Span ↪ B (spanBits S P))` 有元素。这里调用 `Nat.mul_le_mul_left`。
private theorem exists_index (j : Kind S P (S.e + 2)) :
    Nonempty ((kind S P z hz j).Span ↪ B (spanBits S P)) := by
  have h : 2 ^ (S.e + 2) * (P.b + 1) ≤ 2 ^ spanBits S P := by
    rw [spanBits, pow_add 2 (S.e + 2)]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
  have hf : 4 ≤ 2 ^ (S.e + 2) := by
    rw [pow_add]
    have hpos : 0 < 2 ^ S.e := by positivity
    omega
  rcases j with t|t|q
  · exact ⟨Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (by unfold spanBits; omega))⟩
  · change Nonempty (t.Port ↪ B (spanBits S P))
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    exact (role_card P t).trans ((Nat.mul_le_mul_right _ hf).trans h)
  · change Nonempty (Fin q.val × Option (Fin P.b) ↪ B (spanBits S P))
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact (Nat.mul_le_mul_right _ q.isLt.le).trans h

-- 读法：在后续公式中，`lenBits` 是 `Nat.clog 2 (W.card + 3)` 的缩写。
abbrev lenBits (W : Finset ℕ) := Nat.clog 2 (W.card + 3)

-- 读法：存在 `f : (ℕ → B (lenBits W)) × (B (lenBits W) → ℕ)`，`f.2 0 = 0` 与 `f.2 (f.1 (P.b * z)) = P.b * z ∧ f.2 (f.1 z) = z ∧ ∀ j ∈ W, f.2 (f.1 j) = j` 同时成立。这里调用 `hc.trans`。
private theorem exists_lengths (W : Finset ℕ) :
    ∃ f : (ℕ → B (lenBits W)) × (B (lenBits W) → ℕ), f.2 0 = 0 ∧
      f.2 (f.1 (P.b * z)) = P.b * z ∧ f.2 (f.1 z) = z ∧ ∀ j ∈ W, f.2 (f.1 j) = j := by
  let U := insert 0 (insert z (insert (P.b * z) W))
  have hc : U.card ≤ W.card + 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))))
  obtain ⟨i⟩ : Nonempty (↥U ↪ B (lenBits W)) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_coe, Fintype.card_fin]
      exact hc.trans (Nat.le_pow_clog (by decide) _))
  let a : ↥U := ⟨0, by simp [U]⟩
  let e := i.trans (Equiv.swap (i a) 0).toEmbedding
  -- 推导：记下中间结论 `he`：`e a = 0`。
  have he : e a = 0 := Equiv.swap_apply_left _ _
  let len := Function.extend e Subtype.val (fun _ => 0)
  let put (j : ℕ) := if h : j ∈ U then e ⟨j, h⟩ else 0
  have hu (j : ℕ) (h : j ∈ U) : len (put j) = j := by
    simp only [put, dite_eq_left h, len, e.injective.extend_apply]
  have h0 : len 0 = 0 := by
    rw [← he]
    exact e.injective.extend_apply _ _ a
  exact ⟨(put, len), h0, hu _ (by simp [U]), hu _ (by simp [U]), fun j hj => hu j (by simp [U, hj])⟩

variable (ord : B S.ℓ ≃ B S.ℓ) (W : Finset ℕ)

-- 读法：用字段 `ord`、`s`、`index`、`d` 构造 `Book S P z hz`。
def make : Book S P z hz where
  ord := ord
  s := spanBits S P
  index j := Classical.choice (exists_index S P z hz j)
  d := lenBits W
  len := (exists_lengths P z W).choose.2
  put := (exists_lengths P z W).choose.1
  zero := (exists_lengths P z W).choose_spec.1
  old := (exists_lengths P z W).choose_spec.2.1
  unit := (exists_lengths P z W).choose_spec.2.2.1

-- 读法：结论为 `let b := make S P z hz ord W b.len (b.put j) = j`。使用 `exists_lengths` 给出的结论。
theorem represent {j : ℕ} (hj : j ∈ W) :
    let b := make S P z hz ord W
    b.len (b.put j) = j :=
  (exists_lengths P z W).choose_spec.2.2.2 _ hj

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Book
end

/-!
# 打包历史中每个非空原子参数的局部性

**英文原文**

Locality of every nonempty atom argument in the packed history
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing
open scoped Classical

-- 读法：`i.1.val = j.1.val` 与 `i.2 = j.2` 同时成立。
private theorem pair_eq {m n : ℕ} {A : Type} (h : m = n)
    (i : Fin m × A) (j : Fin n × A) (e : HEq i j) : i.1.val = j.1.val ∧ i.2 = j.2 := by
  subst n
  rw [eq_of_heq e]
  exact ⟨rfl, rfl⟩

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k n : ℕ} {B' : ℝ}
    {u v : State S P a h z Δ D k B'}

-- 读法：`u.q.portKey P u.g u.m u.i u.p.toPresentation u.v ((u.atomMap i hu).slot x hx)` 等于 `v.q.portKey P v.g v.m v.i v.p.toPresentation v.v ((v.atomMap j hv).slot y hy)`。这里调用 `e.oldMap_key`。
theorem Same.atom_slot (e : u.Same v n) (hn : 4 ≤ n)
    {i : u.H.Atom u.g u.m} {j : v.H.Atom v.g v.m}
    (hu : u.H.anchor u.g u.m u.col i = u.v) (hv : v.H.anchor v.g v.m v.col j = v.v)
    (hk : u.q.atomKey u.g u.m u.col i = v.q.atomKey v.g v.m v.col j)
    (x : (History.kind S P z u.hz (u.kind i)).Span)
    (y : (History.kind S P z v.hz (v.kind j)).Span)
    (he : HEq x y) (hx : 0 < (History.kind S P z u.hz (u.kind i)).width x)
    (hy : 0 < (History.kind S P z v.hz (v.kind j)).width y) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v ((u.atomMap i hu).slot x hx) =
      v.q.portKey P v.g v.m v.i v.p.toPresentation v.v ((v.atomMap j hv).slot y hy) := by
  have hr := (Prod.mk.inj hk).2
  rcases i with i|⟨i, r⟩|i <;> rcases j with j|⟨j, t⟩|j <;>
    simp only [Navigation.role, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at hr
  · change B S.e at x y
    -- 推导：记下中间结论 `eq`：`x = y`。
    have eq : x = y := eq_of_heq he
    subst y
    exact e.oldMap_key hn hu hv hk x hx hy
  · exact e.match_key hn hu hv hk x y he
  · have hs := congrArg Prod.fst hk
    have hc := e.checkCount hn hu hv hs
    change Fin (Fintype.card (u.CheckRow i)) × Option (Fin P.b) at x
    change Fin (Fintype.card (v.CheckRow j)) × Option (Fin P.b) at y
    obtain ⟨b, l⟩ := x
    obtain ⟨c, r⟩ := y
    -- 推导：从 `pair_eq hc (b, l) (c, r) he` 中取出 `h₁, h₂`。
    obtain ⟨h₁, h₂⟩ := pair_eq hc (b, l) (c, r) he
    change l = r at h₂
    subst r
    exact e.check_key hn hu hv hs b c h₁ l

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 相同的局部窗口输出相同的打包历史

按各自固定的次序压缩三份名称字典。此时原始键相同即可推出数值标签和连接均相同。两边对未使用键与空区段采用的填充约定也一致。

**英文原文**

Equal local windows emit identical packed histories

Compact each of the three name dictionaries in its fixed order.
Raw key equality then gives equality of numerical labels and links.
The padding conventions agree also on unused keys and empty spans.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History.Subround Navigation Finset
open scoped Classical

-- 读法：`Function.extend (compact f hf) a base` 等于 `Function.extend (compact g hg) t base`。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem compact_extend {A T K Z : Type} [Fintype A] [Fintype T] [Encodable K] {e : ℕ}
    {f : A ↪ K} {g : T ↪ K} {hf : Fintype.card A ≤ 2 ^ e} {hg : Fintype.card T ≤ 2 ^ e}
    (h : univ.map f = univ.map g) (a : A → Z) (t : T → Z) (base : B e → Z)
    (he : ∀ i j, f i = g j → a i = t j) :
    Function.extend (compact f hf) a base = Function.extend (compact g hg) t base := by
  funext x
  by_cases hx : x ∈ Set.range (compact f hf)
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, _, hj⟩ := mem_map.mp (h ▸ mem_map_of_mem f (mem_univ i))
    rw [(compact f hf).injective.extend_apply, compact_eq (hg := hg) h hj.symm,
      (compact g hg).injective.extend_apply]
    exact he i j hj.symm
  have hy : x ∉ Set.range (compact g hg) := by
    rintro ⟨j, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_map.mp (h.symm ▸ mem_map_of_mem g (mem_univ j))
    exact hx ⟨i, compact_eq h hi⟩
  rw [Function.extend_apply' _ _ _ hx, Function.extend_apply' _ _ _ hy]

-- 读法：按 `t ∈ Set.range (index i)` 成立与否分情况。
private theorem extend_slot {F L X Y Z : Type} {s : ℕ} (a : L → History.Atom F)
    (index : ∀ i, (a i).Span ↪ B s) {i j : L} (e : i = j)
    (f : ∀ x, 0 < (a i).width x → X) (g : ∀ y, 0 < (a j).width y → Y)
    (p : X → Z) (q : Y → Z) (x : X) (y : Y) (he : p x = q y)
    (hs : ∀ b c, HEq b c → ∀ h h', p (f b h) = q (g c h')) (t : B s) :
    p (Function.extend (index i) (fun b => if h : 0 < (a i).width b then f b h else x) (fun _ => x) t) =
    q (Function.extend (index j) (fun c => if h : 0 < (a j).width c then g c h else y) (fun _ => y) t) := by
  subst j
  by_cases h : t ∈ Set.range (index i)
  · obtain ⟨b, rfl⟩ := h
    simp only [(index i).injective.extend_apply]
    by_cases hb : 0 < (a i).width b
    · rw [dite_eq_left hb, dite_eq_left hb]
      exact hs _ _ HEq.rfl _ _
    · simpa only [dite_eq_right hb] using he
  simpa only [Function.extend_apply' _ _ _ h] using he

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k n e l s d : ℕ} {B' : ℝ} {u v : State S P a h z Δ D k B'}

-- 读法：`(compact f h x).val` 等于 `Navigation.index (univ.map f) (f x)`。两端由定义化简为同一项。
private theorem compact_val {A K : Type} [Fintype A] [Encodable K]
    (f : A ↪ K) (h : Fintype.card A ≤ 2 ^ e) (x : A) :
    (compact f h x).val = Navigation.index (univ.map f) (f x) := rfl

-- 读法：`(R.visible x).val` 等于 `Navigation.index u.lists.2.2 (u.q.faceKey P u.H u.g u.m u.i u.p.toPresentation x.val)`。这里调用 `Subsingleton.elim`。
theorem visible_index (R : u.Room e) (x : Visible u.g u.m P u.H.units u.i u.p.toPresentation u.v) :
    (R.visible x).val = Navigation.index u.lists.2.2 (u.q.faceKey P u.H u.g u.m u.i u.p.toPresentation x.val) := by
  unfold Room.visible Navigation.visible lists Scheme.Posting.dictionaries
  erw [@compact_val]
  congr 3
  exact Subsingleton.elim _ _

-- 读法：`History.Packed.link R.hidden (x.map R.visible id, (0 : B d))` 等于 `History.Packed.link T.hidden (y.map T.visible id, (0 : B d))`。按 `Fin.ext` 的外延性准则比较各分量。
private theorem Same.link (same : u.Same v n) (hn : 4 ≤ n) (R : u.Room e) (T : v.Room e)
    {x : PortMap.Port u.g u.m P u.H.units u.i u.p.toPresentation u.v}
    {y : PortMap.Port v.g v.m P v.H.units v.i v.p.toPresentation v.v}
    (he : u.q.portKey P u.g u.m u.i u.p.toPresentation u.v x =
      v.q.portKey P v.g v.m v.i v.p.toPresentation v.v y) :
    History.Packed.link R.hidden (x.map R.visible id, (0 : B d)) =
      History.Packed.link T.hidden (y.map T.visible id, (0 : B d)) := by
  have hs := same.lists hn
  rcases x with x|x <;> rcases y with y|y
  · have hv : R.visible x = T.visible y := by
      apply Fin.ext
      rw [visible_index, visible_index]
      exact congrArg₂ Navigation.index (congrArg (fun p => p.2.2) hs) (congrArg Prod.snd he)
    exact congrArg (fun i => (false, i, (0 : B d))) hv
  · exact (Bool.false_ne_true (congrArg Prod.fst he)).elim
  · exact (Bool.false_ne_true (congrArg Prod.fst he.symm)).elim
  -- 推导：记下中间结论 `hv`：`R.hidden x = T.hidden y`。
  · have hv : R.hidden x = T.hidden y :=
      compact_eq (congrArg (fun p => p.2.1) hs) (congrArg Prod.snd he)
    exact congrArg (fun i => (true, i, (0 : B d))) hv

-- 读法：`u.packedCode R names index old new` 等于 `v.packedCode T names index old new`。按 `Prod.ext` 的外延性准则比较各分量。
theorem Same.packedCode (same : u.Same v n) (hn : 4 ≤ n) (R : u.Room e) (T : v.Room e)
    (names : History.Kind S P (S.e + 2) ↪ B l)
    (index : ∀ j : History.Kind S P (S.e + 2), (History.kind S P z u.hz j).Span ↪ B s)
    (old new : B d) :
    u.packedCode R names index old new = v.packedCode T names index old new := by
  have keys := same.lists hn
  apply Prod.ext
  · apply compact_extend (congrArg (fun p => p.2.1) keys)
    intro i j hij
    exact congrArg (fun x => if x.isRight then new else old) hij
  · unfold State.packedCode History.Packed.encode Room.atoms Navigation.atoms
    dsimp only
    refine compact_extend (congrArg Prod.fst keys) _ _ _ ?_
    intro i j hij
    -- 推导：记下中间结论 `hu`：`u.H.anchor u.g u.m u.col i.val = u.v`。
    have hu : u.H.anchor u.g u.m u.col i.val = u.v :=
      (anchor_eq _).trans (includeAtom u.hz i).property
    have hv : v.H.anchor v.g v.m v.col j.val = v.v :=
      (anchor_eq _).trans (includeAtom v.hz j).property
    have he := same.kind hn hu hv hij
    refine Prod.ext rfl (Prod.ext (congrArg names he) (funext fun q => ?_))
    refine extend_slot (History.kind S P z u.hz) index he
      (fun x h => ((u.atomMap i.val hu).slot x h).map R.visible id)
      (fun x h => ((v.atomMap j.val hv).slot x h).map T.visible id)
      (fun x => History.Packed.link R.hidden (x, (0 : B d)))
      (fun x => History.Packed.link T.hidden (x, (0 : B d)))
      (.inl 0) (.inl 0) rfl ?_ q
    intro x y hxy hx hy
    exact same.link hn R T (same.atom_slot hn hu hv hij x y hxy hx hy)

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 由局部信息确定完整的收缩记录

**英文原文**

Local determination of a complete contraction record
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    {u v : State S P a h z Δ D k B'} {m' d' h' e n : ℕ} {hz : 0 < z} {hle : Δ ≤ D}

-- 读法：`u.localRecord b ru cap α` 等于 `v.localRecord b rv cap β`。这里调用 `Prod.ext`。
theorem Same.localRecord (same : u.Same v n) (hn : 8 ≤ n) (b : Book S P z hz)
    (ru : u.Room e) (rv : v.Room e) (cap : ℕ)
    (α : u.Assignment hle (b.scheme m' d' h' e cap)) (β : v.Assignment hle (b.scheme m' d' h' e cap))
    (hindex : ∀ (x : Site (u.G.V × Cell a) (h - a)) (y : Site (v.G.V × Cell a) (h - a)),
      Window.Related u.env v.env 4 x.1 y.1 → intervalCode _ x.2 = intervalCode _ y.2 →
      α.index (u.v.1.1, u.v.2) (x.1.1, x.2) = β.index (v.v.1.1, v.v.2) (y.1.1, y.2))
    (ha : u.Ranked α) (hb : v.Ranked β) :
    u.localRecord b ru cap α = v.localRecord b rv cap β := by
  have hp := same.packedCode (by omega) ru rv b.names b.index (b.put (P.b * z)) (b.put z)
  have hf := same.fields hn α β (u.sizes b) (v.sizes b) (fun _ _ he => congrArg b.put he) hindex ha hb
  exact Prod.ext rfl (Prod.ext hf (congrArg (Dense.encode cap) hp))

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 依据局部历史发布收缩后的宿主记录

**英文原文**

Posting a contracted host from its local histories
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History History.Subround
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  {hz : 0 < z} {e m' d' h' : ℕ}
  (u : State S P a h z Δ D k B') (b : Book S P z hz) (r : u.Room e) (cap : ℕ)
  (hle : Δ ≤ D)

-- 读法：在后续公式中，`allocate` 是 `⟨host, block, slot, fun v => (r.recenter v).visible⟩` 的缩写。
abbrev allocate (host : Site u.G.V (h - a) ↪ B m') (block : Cell a ↪ B h')
    (slot : Site u.G.V (h - a) → Site u.G.V (h - a) → B d') :
    u.Assignment hle (b.scheme m' d' h' e cap) :=
  ⟨host, block, slot, fun v => (r.recenter v).visible⟩

variable {hle} (A : u.Assignment hle (b.scheme m' d' h' e cap)) (nav : B m' → B d' → B m')

-- 读法：在后续公式中，`output` 是 `Post.write b.menu (Dense.unpack (m := e) cap) nav (u.records b r cap A)` 的缩写。
abbrev output := Post.write b.menu (Dense.unpack (m := e) cap) nav (u.records b r cap A)

-- 读法：结构的字段包括 `seat`、`sizes`、`hop`、`neutral`、`budget`。
/-- 存储这一族局部历史所需的各项上界。

英文原文：The bounds necessary to store this family of local histories.
-/
structure Ready : Prop where
  seat : ∀ v, A.seat v = (r.recenter v).visible
  sizes : ∀ j, b.len (b.put (u.p.toPresentation.borderWidth j)) = u.p.toPresentation.borderWidth j
  hop : ∀ v w, w ∈ (u.G.project a u.ha Δ D hle).C v → nav (A.host v) (A.index v w) = A.host w
  neutral : ∀ v, u.G.diagram.arity v = 0 → ∀ x, Transcript.sample (u.G.diagram.table v) x = 1
  budget : ∀ v, b.overhead e + (u.recenter v).inherited b.ord ≤ cap

-- 读法：`(⟨x, i.cast hx⟩ : Σ j, Fin (w j))` 等于 `⟨y, i.cast hy⟩`。
private theorem offsets {e : ℕ} (w : B e → ℕ) {x y : B e} (he : x = y)
    {n : ℕ} (i : Fin n) (hx : n = w x) (hy : n = w y) :
    (⟨x, i.cast hx⟩ : Σ j, Fin (w j)) = ⟨y, i.cast hy⟩ := by subst y; rfl

namespace Ready

variable {u b r cap A nav} (H : Ready u b r cap A nav)

include H in
-- 读法：要证明的命题是 `A.Emitted (u.sizes b) nav (u.records b r cap A)`。这里调用 `H.sizes`。
theorem emitted : A.Emitted (u.sizes b) nav (u.records b r cap A) := by
  refine A.emitted _ _ _ b.zero ?_ (A.end_nav nav H.hop)
  rintro (j|j)
  · exact H.sizes j
  · exact b.unit

include H in
-- 读法：要证明的命题是 `u.Ranked A`。这里调用 `visible_index`。
theorem ranked : u.Ranked A := by
  intro v j
  rw [H.seat v]
  exact visible_index (r.recenter v) j

local notation "Z" => b.scheme m' d' h' e cap
local notation "out" => u.output b r cap A nav
local notation "len" => H.emitted.lengths

include H in
-- 读法：要证明的命题是 `A.Agrees len u.hz`。这里调用 `H.emitted.agrees`。
set_option maxHeartbeats 800000 in
theorem agrees : A.Agrees len u.hz := by
  apply H.emitted.agrees
  intro v t
  rw [u.record_at b r cap A v]
  let u' := u.recenter v
  let r' := r.recenter v
  let w := fun j => (Z).width out (A.vertex v, j)
  change b.menu.decode w (Dense.unpack (m := e) cap (u'.data b r' cap)) t = _
  rw [u'.unpack_data b r' cap (H.budget v)]
  have ho (j : Visible u.g u.m P u.H.units u.i u.p.toPresentation v) :
      w (r'.visible j) = visibleWidth u.g u.m P u.i u.p.toPresentation z j.val := by
    rw [show r'.visible = A.seat v from (H.seat v).symm]
    exact A.length_at len v j
  let pin := A.pin len u.hz v
  have hp (j : Visible u.g u.m P u.H.units u.i u.p.toPresentation v)
      (k : Fin (visibleWidth u.g u.m P u.i u.p.toPresentation z j.val)) :
      pin (visibleBits u.g u.m P u.H.units u.hz u.i u.p.toPresentation v ⟨j, k⟩) =
        ⟨r'.visible j, k.cast (ho j).symm⟩ := by
    refine (A.pin_at len u.hz v j k).trans ?_
    exact offsets w (congrArg (· j) (H.seat v)) k _ _
  exact u'.bundle.decode b.names b.index r'.visible (u'.hiddenSize (b.put (P.b * z)) (b.put z))
    b.len w b.zero (u'.hiddenSize_spec _ _ b.len b.old b.unit) ho pin hp H.neutral r'.atoms r'.hidden t

include H in
-- 读法：`posting` 的取值由 `A.posting len u.hz H.agrees hle` 给出。
def posting : (Z).Posting out (HostNet.contracted (u.G.project a u.ha Δ D hle) u.g u.m u.hz hle u.i) :=
  A.posting len u.hz H.agrees hle

-- 读法：对每个 `j`，`w` 不超过 `H.posting.toPresentation.borderWidth j`。使用 `H.emitted.floor` 给出的结论。
theorem floor {w : ℕ} (hw : ∀ j, w ≤ u.p.toPresentation.borderWidth j) :
    ∀ j, w ≤ H.posting.toPresentation.borderWidth j :=
  H.emitted.floor u.hz H.agrees hw

-- 读法：对每个 `j`，`H.posting.toPresentation.borderWidth j` 属于 `W`。这里调用 `Eq.mp`。
theorem palette (W : Finset ℕ) (hw : ∀ j, u.p.toPresentation.borderWidth j ∈ W) :
    ∀ j, H.posting.toPresentation.borderWidth j ∈ W := by
  let p' := A.presentation len u.hz H.agrees
  intro j
  let x : p'.BorderBit := ⟨j, ⟨0, j.property.1⟩⟩
  obtain ⟨t, ht⟩ := u.p.toPresentation.exteriorBits.surjective (p'.exteriorBits x)
  have h := (H.emitted.boundary u.hz H.agrees (p'.exteriorBits x)).1
  rw [p'.border_pin, ← ht] at h
  have h := h.trans (congrArg (fun q : S.Pin u.r => S.width u.r q.1) (u.p.toPresentation.border_pin t))
  exact Eq.mp (congrArg (· ∈ W) h.symm) (hw t.1)

include H in
-- 读法：`Dense.used (Post.order d' e b.d cap ((out (A.vertex v).1).2 (A.vertex v).2.1)).val` 不超过 `(Post.headerFmt d' e b.d).width + b.overhead e + (u.recenter v).inherited b.ord`。
theorem stored (v : Site u.H.V (h - a)) :
    Dense.used (Post.order d' e b.d cap ((out (A.vertex v).1).2 (A.vertex v).2.1)).val ≤
      (Post.headerFmt d' e b.d).width + b.overhead e + (u.recenter v).inherited b.ord := by
  let u' := u.recenter v
  let r' := r.recenter v
  let p := u'.bundle.packed b.names b.index r'.visible (u'.hiddenSize (b.put (P.b * z)) (b.put z))
  let q := u'.localRecord b r' cap A
  have h := u'.stored b.ord p (fun _ => rfl) r'.atoms r'.hidden (H.budget v) q rfl
  change Dense.used (Post.order d' e b.d cap ((Post.record _ _ _ _).serial
    (u.records b r cap A (A.vertex v).1 (A.vertex v).2.1))).val ≤ _
  rw [u.record_at]
  exact h.2

end Ready
end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# 收缩历史长度的摊还分析

每个原表名称只计费一次，费用归入其出现位置上现有与已退役的端口。特别地，无须将先前名称的最大长度乘以提供贡献的站点数。

**英文原文**

Amortizing the length of a contraction history

Charge an old table name just once against its occurrence's current
and retired ports. In particular, the previous maximum name length
is not multiplied by the number of contributing stations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Packing
open scoped Classical

namespace Packing.HostNet

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {h u : ℕ} (G : HostNet F L h u)

-- 读法：`u` 不超过 `G.footprint w`。按 `G.tetherLoad w = 0` 成立与否分情况。
theorem active_floor (he : ∀ t, u ≤ G.tetherLoad (G.far t)) (w : G.V × Cell h)
    (hp : 0 < G.tetherLoad w + degree G.pair w * u) : u ≤ G.footprint w := by
  by_cases hx : G.tetherLoad w = 0
  · have hh : 0 < degree G.pair w := by
      by_contra! hz
      simp [hx, Nat.eq_zero_of_le_zero hz] at hp
    have := Nat.le_mul_of_pos_left u hh
    unfold footprint
    omega
  · have hf : ∃ t, G.far t = w := by
      by_contra! hn
      -- 推导：记下中间结论 `hv`：`(G.tetherLoad w : ℝ) = 0`。
      have hv : (G.tetherLoad w : ℝ) = 0 := by
        rw [tetherLoad, port_load]
        change push G.far (fun _ => 1) w = 0
        simp [push, hn]
      exact hx (Nat.cast_eq_zero.mp hv)
    obtain ⟨t, rfl⟩ := hf
    have := he t
    unfold footprint
    omega

-- 读法：`0` 严格小于 `G.tetherLoad (G.units.place v) + degree G.pair (G.units.place v) * u`。
theorem arity_active [Fintype T] (v : G.diagram.V) (hv : 0 < G.diagram.arity v) :
    0 < G.tetherLoad (G.units.place v) + degree G.pair (G.units.place v) * u := by
  let w := G.units.place v
  have ht : (G.diagram.arity v : ℝ) ≤ push G.units.place (fun i => (G.diagram.arity i : ℝ)) w := by
    unfold push
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => by split_ifs <;> positivity) (Finset.mem_univ v))
    simp [w]
  have he := G.load_eq w
  simp only [load, Prod.mk.eta] at he
  have hp : (0 : ℝ) < (G.diagram.arity v : ℝ) := Nat.cast_pos.mpr hv
  have h : 0 < (G.tetherLoad w : ℝ) + degree G.pair w * (u : ℝ) := by linarith only [ht, he, hp]
  exact_mod_cast h

end Packing.HostNet

namespace Assembly.State
open Coloring History

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B') (o : B S.ℓ ≃ B S.ℓ) (unit cost : ℕ)

-- 读法：`Charged` 的构造用到 `u.G.V`、`u.G.tetherLoad`、`u.G.pair`。
def Charged := ∀ w : u.G.V × Cell h, 0 < u.G.tetherLoad w + degree u.G.pair w * (P.b * z) →
  Dense.used (o ((u.r (u.p.host w.1)).2 (u.p.block w.2))).val * unit ≤ cost * u.G.footprint w

variable {o unit cost} (hc : Δ ≤ D)

local notation "pr" => u.G.project a u.ha Δ D hc
local notation "Q" => HostNet.contracted pr u.g u.m u.hz hc u.i

-- 读法：`u.inherited o * unit` 不超过 `cost * (Q).footprint ((pr).place u.v)`。
theorem inherited_charge (tag : u.Charged o unit cost) (hu : 0 < unit) :
    u.inherited o * unit ≤ cost * (Q).footprint ((pr).place u.v) := by
  let c : ℝ := (cost : ℝ) / unit
  have hc' : 0 ≤ c := by unfold c; positivity
  have hu' : (0 : ℝ) < unit := Nat.cast_pos.mpr hu
  let mass (p : u.H.V × Cell (h - a)) := c * (u.H.footprint p : ℝ)
  have hh := u.inherited_le o mass (fun t => mul_nonneg hc' (Nat.cast_nonneg _)) (by
    intro v hv
    let w := u.G.units.place v
    have ht := tag w (u.G.arity_active v hv)
    rw [oldTag, u.p.vertex_eq]
    change (Dense.used (o ((u.r (u.p.host w.1)).2 (u.p.block w.2))).val : ℝ) ≤
      (cost : ℝ) / unit * (u.G.regroup a u.ha).footprint (splitAddr u.G.V a u.ha w)
    rw [u.G.regroup_footprint, div_mul_eq_mul_div, le_div_iff₀ hu']
    exact_mod_cast ht)
  have hf := HostNet.footprint_route pr u.g u.m u.hz hc u.i u.v
  -- 推导：记下中间结论 `hm`：`push (fun t => u.g.route u.m u.col t.1 t.2) mass u.v ≤ c * (Q).footprint ((pr).place u.v)`。
  have hm : push (fun t => u.g.route u.m u.col t.1 t.2) mass u.v ≤ c * (Q).footprint ((pr).place u.v) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hf hc')
    have ee := push_div (Function.uncurry (u.g.route u.m u.col))
      (fun t => (u.H.footprint t : ℝ)) c⁻¹ u.v
    simp only [div_inv_eq_mul, mul_comm _ c] at ee
    exact ee.le
  have hh := hh.trans hm
  rw [show c = (cost : ℝ) / unit from rfl, div_mul_eq_mul_div, le_div_iff₀ hu'] at hh
  exact_mod_cast hh

-- 读法：`u.inherited o` 不超过 `cost * (2 ^ u.L.discount * B)`。这里调用 `Nat.le_of_mul_le_mul_right`。
theorem inherited_bound (tag : u.Charged o unit cost) (hu : 0 < unit) (B : ℕ)
    (hm : (Q).mass ≤ u.L.cap) (hl : ∀ v i, (Q).load v i ≤ (B : ℝ) * unit) :
    u.inherited o ≤ cost * (2 ^ u.L.discount * B) := by
  let w := (pr).place u.v
  have hp : (Q).footprint w ≤ 2 ^ u.L.discount * B * unit := by
    have he := ((Q).footprint_le hm w).trans (mul_le_mul_of_nonneg_left (hl w.1 w.2) (by positivity))
    rw [← mul_assoc] at he
    exact_mod_cast he
  apply Nat.le_of_mul_le_mul_right _ hu
  rw [mul_assoc]
  exact (u.inherited_charge hc tag hu).trans (Nat.mul_le_mul_left _ hp)

end Assembly.State
end OAI.LinearAlgebra.MatrixExponent
end
