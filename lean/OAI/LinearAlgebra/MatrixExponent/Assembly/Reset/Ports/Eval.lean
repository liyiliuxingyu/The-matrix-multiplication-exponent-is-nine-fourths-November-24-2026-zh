-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Correspondence
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Repost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Move
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Width
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Raw.Local
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers

/-!
# 驻留在重置站点的原顶点与外部区段

**英文原文**

Old vertices and exterior spans resident at a reset station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  (U V : Setup S h u a Δ D Y w B') {R : Rotor F Y w}
  {σ : Cell a} {v : U.G.V} {z : V.G.V} {loc : Coord R h a Δ}

-- 读法：`Tags` 的取值由 `∀ j, U.Z.group j = σ → U.tag v j = V.tag z j` 给出。
def Tags (σ : Cell a) (v : U.G.V) (z : V.G.V) :=
  ∀ j, U.Z.group j = σ → U.tag v j = V.tag z j

-- 读法：`0 < U.G.diagram.arity t` 与 `∃ j, 0 < S.width U.r (U.post.vertex t, j)` 等价。
private theorem positive_arity (t : U.G.diagram.V) :
    0 < U.G.diagram.arity t ↔ ∃ j, 0 < S.width U.r (U.post.vertex t, j) := by
  have he : 0 < U.G.diagram.arity t ↔ Nonempty (S.LocalPin U.r (U.post.vertex t)) := by
    rw [← Fintype.card_pos_iff, ← Fintype.card_congr (U.post.pin t)]
    simp only [Diagram.Port, Fintype.card_sum, card_slots, Diagram.arity]
  rw [he]
  exact ⟨fun ⟨⟨j, i⟩⟩ => ⟨j, i.pos⟩, fun ⟨j, hj⟩ => ⟨⟨j, ⟨0, hj⟩⟩⟩⟩

-- 读法：存在 `x`，`0 < U.G.diagram.arity x` 与 `U.G.units.place x = (v, j)` 同时成立。这里调用 `Prod.ext`。
private theorem exists_vertex (v : U.G.V) (j : Cell h) (t : B S.e) (ht : 0 < (U.pat v j).width 0 t) :
    ∃ x, 0 < U.G.diagram.arity x ∧ U.G.units.place x = (v, j) := by
  let b : S.Vtx := (U.post.host v, U.post.block j, 0)
  obtain ⟨x, hx⟩ := U.post.cover ⟨(b, t), ⟨0, ht⟩⟩
  change U.post.vertex x = b at hx
  refine ⟨x, (U.positive_arity x).mpr ⟨t, by rw [hx]; exact ht⟩, ?_⟩
  rw [U.post.vertex_eq] at hx
  exact Prod.ext (U.post.host.injective (Prod.mk.inj hx).1)
    (U.post.block.injective (Prod.mk.inj (Prod.mk.inj hx).2).1)

variable {U V} [NeZero Y] [NeZero w] {fit : U.Fits R c} {fit' : V.Fits R c}
  (p : Agree U V σ v z) (ht : U.Tags V σ v z)

include p ht in
omit [NeZero Y] [NeZero w] in
-- 读法：要证明的命题是 `V.Tags U σ z v`。通过传递性衔接 `fun` 与 `hj`。
theorem Tags.symm : V.Tags U σ z v := fun j hj => (ht j ((p.group j).trans hj)).symm

-- 读法：`U.Z.group s.2 = σ` 与 `s.1 = v` 同时成立。
theorem owner_here {s : U.G.V × Cell h} (he : (U.result R fit).owner s = U.station R fit σ v loc) :
    U.Z.group s.2 = σ ∧ s.1 = v := by
  have := (U.place R fit).eq_symm_apply.mp he
  simp only [owner_place, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

include p in
-- 读法：`(V.result R fit').owner (z, s.2)` 等于 `V.station R fit' σ z loc`。
theorem Agree.owner_here {s : U.G.V × Cell h}
    (he : (U.result R fit).owner s = U.station R fit σ v loc) :
    (V.result R fit').owner (z, s.2) = V.station R fit' σ z loc := by
  obtain ⟨v', j⟩ := s
  obtain ⟨hg, hv⟩ := Setup.owner_here he
  change v' = v at hv
  subst v'
  have hdrop := congrArg (fun b => (Site.drop a ((), b)).2) (p.leaf j hg)
  change ((U.Z.leaf (v, j)).drop a).2 = ((V.Z.leaf (z, j)).drop a).2 at hdrop
  simp only [station, Equiv.eq_symm_apply, owner_place, Prod.mk.injEq, true_and] at he ⊢
  rwa [← p.group, ← hdrop, ← p.terminal j hg]

-- 读法：在后续公式中，`Actors` 是 `Live (U.result R fit) (U.station R fit σ v loc)` 的缩写。
abbrev Actors (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fit : U.Fits R c)
    (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ) :=
  Live (U.result R fit) (U.station R fit σ v loc)

-- 读法：`blockOf` 的取值由 `(U.G.units.place t.val).2` 给出。
def blockOf (t : U.Actors R fit σ v loc) : Cell h := (U.G.units.place t.val).2

-- 读法：`oldLabel U.post t.val` 等于 `(U.tag v (blockOf t), 0)`。
theorem actor_label (t : U.Actors R fit σ v loc) :
    oldLabel U.post t.val = (U.tag v (blockOf t), 0) := by
  unfold oldLabel
  rw [U.post.vertex_eq, (Setup.owner_here t.2.2).2]
  rfl

-- 读法：`(blockOf (U := U) (fit := fit) (σ := σ) (v := v) (loc := loc))` 是单射。按 `Subtype.ext` 的外延性准则比较各分量。
private theorem block_inj : Function.Injective (blockOf (U := U) (fit := fit) (σ := σ) (v := v) (loc := loc)) := by
  intro i j he
  apply Subtype.ext
  apply U.post.vertex.injective
  rw [U.post.vertex_eq, U.post.vertex_eq, (owner_here i.2.2).2, (owner_here j.2.2).2]
  unfold blockOf at he
  rw [he]

include p ht in
-- 读法：存在 `t' : V.Actors R fit' σ z loc`，`blockOf t` 等于 `blockOf t'`。
private theorem Agree.actor_map (t : U.Actors R fit σ v loc) :
    ∃ t' : V.Actors R fit' σ z loc, blockOf t = blockOf t' := by
  obtain ⟨j, hj⟩ := (U.positive_arity t.val).mp t.2.1
  have htag := ht (blockOf t) (Setup.owner_here t.2.2).1
  rw [U.post.vertex_eq, (Setup.owner_here t.2.2).2] at hj
  change 0 < (S.decode (U.tag v (blockOf t))).width 0 j at hj
  rw [htag] at hj
  obtain ⟨x, hx, he⟩ := V.exists_vertex _ _ j hj
  refine ⟨⟨x, hx, by rw [he]; exact p.owner_here t.2.2⟩, (congrArg Prod.snd he).symm⟩

include p ht in
-- 读法：存在 `e : U.Actors R fit σ v loc ≃ V.Actors R fit' σ z loc`，对每个 `t`，`blockOf (e t)` 等于 `blockOf t`。使用 `Dispatch.equivalent` 给出的结论。
theorem Agree.actors :
    ∃ e : U.Actors R fit σ v loc ≃ V.Actors R fit' σ z loc, ∀ t, blockOf (e t) = blockOf t :=
  Dispatch.equivalent _ _ block_inj block_inj (p.actor_map ht) (p.symm.actor_map (ht.symm p))

include p ht in
-- 读法：证明中先建立 `hl`，即 `U.pat v i = V.pat z i`。
theorem Agree.border_map (t : U.post.toPresentation.BorderSpan)
    (he : (U.result R fit).owner (U.G.units.place t.val.1) = U.station R fit σ v loc) :
    ∃ j : V.post.toPresentation.BorderSpan,
      (V.result R fit').owner (V.G.units.place j.val.1) = V.station R fit' σ z loc ∧
      (V.G.units.place j.val.1).2 = (U.G.units.place t.val.1).2 ∧ j.val.2 = t.val.2 ∧
      V.post.toPresentation.borderWidth j = U.post.toPresentation.borderWidth t := by
  let i := (U.G.units.place t.val.1).2
  have hl : U.pat v i = V.pat z i := congrArg S.decode (ht i (Setup.owner_here he).1)
  have hv : U.post.vertex t.val.1 = (U.post.host v, U.post.block i, 0) := by
    rw [U.post.vertex_eq, (Setup.owner_here he).2]
  have h := t.property
  rw [hv] at h
  -- 推导：记下中间结论 `hm`：`0 < (V.pat z i).width 0 t.val.2`。
  have hm : 0 < (V.pat z i).width 0 t.val.2 := by rw [← hl]; exact h.1
  obtain ⟨x, _, hx⟩ := V.exists_vertex _ _ _ hm
  have hz : V.post.vertex x = (V.post.host z, V.post.block i, 0) := by rw [V.post.vertex_eq, hx]
  have hh : S.peer V.r (V.post.vertex x, t.val.2) = none := by
    rw [hz]
    have hs : (U.pat v i).peer 0 t.val.2 = none := by simpa [pat, tag, Scheme.peer, Scheme.pattern] using h.2
    rw [hl] at hs
    simpa [pat, tag, Scheme.peer, Scheme.pattern] using hs
  let j : V.post.toPresentation.BorderSpan := ⟨(x, t.val.2), by rw [hz]; exact hm, hh⟩
  refine ⟨j, ?_, congrArg Prod.snd hx, rfl, ?_⟩
  · change (V.result R fit').owner (V.G.units.place x) = _
    rw [hx]; exact p.owner_here he
  · change S.width V.r (V.post.vertex x, _) = S.width U.r (U.post.vertex t.val.1, _)
    rw [hz, hv]
    exact congrArg (fun p : Pattern F S.d S.k S.e => p.width 0 t.val.2) hl.symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 相匹配的重置站点上的可见与隐藏载体

**英文原文**

The visible and hidden carriers at matching reset stations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c) (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ)

-- 读法：在后续公式中，`Seen` 是 `Visible U.post (U.result R fit) (U.station R fit σ v loc)` 的缩写。
abbrev Seen := Visible U.post (U.result R fit) (U.station R fit σ v loc)
-- 读法：在后续公式中，`Unseen` 是 `Hidden (U.result R fit) (U.station R fit σ v loc)` 的缩写。
abbrev Unseen := Hidden (U.result R fit) (U.station R fit σ v loc)

-- 读法：`visibleKey` 的取值由 `U.portKey R fit _ (.inl t)` 给出。
def visibleKey (t : U.Seen R fit σ v loc) := U.portKey R fit _ (.inl t)
-- 读法：`hiddenKey` 的取值由 `U.portKey R fit _ (.inr t)` 给出。
def hiddenKey (t : U.Unseen R fit σ v loc) := U.portKey R fit _ (.inr t)

-- 读法：`(U.visibleKey R fit σ v loc)` 是单射。
theorem visible_inj : Function.Injective (U.visibleKey R fit σ v loc) :=
  fun _ _ he => Sum.inl.inj (U.portKey_injective R fit _ he)

-- 读法：`(U.hiddenKey R fit σ v loc)` 是单射。
theorem hidden_inj : Function.Injective (U.hiddenKey R fit σ v loc) :=
  fun _ _ he => Sum.inr.inj (U.portKey_injective R fit _ he)

variable {U R fit σ v loc} {V : Setup S h u a Δ D Y w B'} {fit' : V.Fits R c}
  {z : V.G.V} {Q : Relation U V} {k n : ℕ}

-- 读法：`U.visibleKey R fit σ v loc j` 不等于 `V.hiddenKey R fit' σ z loc t`。
theorem distinct_keys (j : U.Seen R fit σ v loc) (t : V.Unseen R fit' σ z loc) :
    U.visibleKey R fit σ v loc j ≠ V.hiddenKey R fit' σ z loc t := by
  rcases j with ⟨j | ⟨q, b⟩, hj⟩ <;> rcases t with ⟨e|e|e, he⟩ <;>
    simp [visibleKey, hiddenKey, portKey]

variable (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
  (ht : U.Tags V σ v z)

include p hk hr ht in
-- 读法：结论为 `∃ j : V.Seen R fit' σ z loc, U.visibleKey R fit σ v loc t = V.visibleKey R fit' σ z loc j ∧ visibleWidth U.post (U.result R fit) t.val = visibleWidth V.post (V.result R fit') j.val`。
theorem Region.visible_map (t : U.Seen R fit σ v loc) :
    ∃ j : V.Seen R fit' σ z loc, U.visibleKey R fit σ v loc t = V.visibleKey R fit' σ z loc j ∧
      visibleWidth U.post (U.result R fit) t.val = visibleWidth V.post (V.result R fit') j.val := by
  rcases t with ⟨q | ⟨e, b⟩, he⟩
  · obtain ⟨j, hj, hb, hs, hw⟩ := (p.toSurvey.agree (by omega) hr).border_map (fit' := fit') ht q he
    refine ⟨⟨.inl j, hj⟩, ?_, hw.symm⟩
    exact congrArg₂ PortId.border hb.symm (congrArg Fin.val hs.symm)
  · obtain ⟨f, hf, r⟩ := p.raw_here (fit' := fit') hk hr (raw_at.mp he)
    let g : (V.result R fit').Survivors := ⟨f, mt (r.loop p (by omega)).mpr e.property⟩
    exact ⟨⟨.inr (g, b), raw_at.mpr hf⟩, congrArg (PortId.line true b) (r.key b), rfl⟩

include p hk hr ht in
-- 读法：结论为 `∃ e : U.Seen R fit σ v loc ≃ V.Seen R fit' σ z loc, ∀ t, V.visibleKey R fit' σ z loc (e t) = U.visibleKey R fit σ v loc t ∧ visibleWidth V.post (V.result R fit') (e t).val = visibleWidth U.post (U.result R fit) t.val`。
theorem Region.visible :
    ∃ e : U.Seen R fit σ v loc ≃ V.Seen R fit' σ z loc, ∀ t,
      V.visibleKey R fit' σ z loc (e t) = U.visibleKey R fit σ v loc t ∧
      visibleWidth V.post (V.result R fit') (e t).val = visibleWidth U.post (U.result R fit) t.val := by
  have a := p.visible_map (fit := fit) (fit' := fit') (loc := loc) hk hr ht
  have b := p.symm.visible_map (fit := fit') (fit' := fit) (loc := loc) hk hr
    (ht.symm (p.toSurvey.agree (by omega) hr))
  obtain ⟨e, he⟩ := Dispatch.equivalent _ _ (U.visible_inj R fit σ v loc) (V.visible_inj R fit' σ z loc)
    (fun x => (a x).imp (fun _ h => h.1)) (fun x => (b x).imp (fun _ h => h.1))
  refine ⟨e, fun t => ⟨he t, ?_⟩⟩
  obtain ⟨q, hq, hw⟩ := b (e t)
  rw [U.visible_inj R fit σ v loc (hq.symm.trans (he t))] at hw
  exact hw

include p hk hr in
-- 读法：存在 `j : V.Unseen R fit' σ z loc`，`U.hiddenKey R fit σ v loc t` 等于 `V.hiddenKey R fit' σ z loc j`。
private theorem Region.hidden_map (t : U.Unseen R fit σ v loc) :
    ∃ j : V.Unseen R fit' σ z loc, U.hiddenKey R fit σ v loc t = V.hiddenKey R fit' σ z loc j := by
  rcases t with ⟨e|e|e, he⟩
  · have h : demandSite (U.result R fit) e false = U.station R fit σ v loc := congrArg Prod.fst he
    obtain ⟨f, hf, r⟩ := p.old_here (fit' := fit') hk hr (old_at.mp h)
    exact ⟨⟨.inl f, Prod.ext (old_at.mpr hf) (old_at.mpr hf)⟩, congrArg (PortId.demand false) (r.name false)⟩
  · have h : demandSite (U.result R fit) e true = U.station R fit σ v loc := congrArg Prod.fst he
    obtain ⟨f, hf, r⟩ := p.old_here (fit' := fit') hk hr (old_at.mp h)
    exact ⟨⟨.inr (.inl f), Prod.ext (old_at.mpr hf) (old_at.mpr hf)⟩,
      congrArg (PortId.demand true) (r.name true)⟩
  · have h : supplySite (U.result R fit) e false = U.station R fit σ v loc := congrArg Prod.fst he
    obtain ⟨f, hf, r⟩ := p.raw_here (fit' := fit') hk hr (raw_at.mp h)
    have hh := (r.loop p (by omega)).mp ((congrArg Prod.fst he).trans (congrArg Prod.snd he).symm)
    exact ⟨⟨.inr (.inr f), Prod.ext (raw_at.mpr hf) (hh.symm.trans (raw_at.mpr hf))⟩,
      congrArg (PortId.line false false) (r.key false)⟩

include p hk hr in
-- 读法：存在 `e : U.Unseen R fit σ v loc ≃ V.Unseen R fit' σ z loc`，对每个 `t`，`V.hiddenKey R fit' σ z loc (e t)` 等于 `U.hiddenKey R fit σ v loc t`。
theorem Region.hidden :
    ∃ e : U.Unseen R fit σ v loc ≃ V.Unseen R fit' σ z loc, ∀ t,
      V.hiddenKey R fit' σ z loc (e t) = U.hiddenKey R fit σ v loc t :=
  Dispatch.equivalent _ _ (U.hidden_inj ..) (V.hidden_inj ..)
    (p.hidden_map hk hr) (p.symm.hidden_map hk hr)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 在相匹配的端口数据带上读取同一重置规则

**英文原文**

Reading the same reset rule on matching port tapes
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c) (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ)

-- 读法：在后续公式中，`Pins` 是 `Port U.post (U.result R fit) (U.station R fit σ v loc)` 的缩写。
abbrev Pins := Port U.post (U.result R fit) (U.station R fit σ v loc)
-- 读法：在后续公式中，`Readings` 是 `Tape U.post (U.result R fit) (U.station R fit σ v loc)` 的缩写。
abbrev Readings := Tape U.post (U.result R fit) (U.station R fit σ v loc)

-- 读法：`values` 的取值由 `Sum.elim (fun i => inBits U.post _ _ x i.2 j i.1) (outBits U.post _ _ x j)` 给出。
def values (x : U.Readings R fit σ v loc) (j : Fin u) : U.Value R :=
  Sum.elim (fun i => inBits U.post _ _ x i.2 j i.1) (outBits U.post _ _ x j)

-- 读法：`supply U.post (U.result R fit) (U.station R fit σ v loc) e false h₁` 等于 `supply U.post (U.result R fit) (U.station R fit σ v loc) e true h₂`。
private theorem loop_port (e : U.Raw R) (h₁ : supplySite (U.result R fit) e false = U.station R fit σ v loc)
    (h₂ : supplySite (U.result R fit) e true = U.station R fit σ v loc) :
    supply U.post (U.result R fit) (U.station R fit σ v loc) e false h₁ = supply U.post (U.result R fit) (U.station R fit σ v loc) e true h₂ := by
  have he : ((U.result R fit).supply e).1 = ((U.result R fit).supply e).2 := h₁.trans h₂.symm
  simp only [supply, dite_eq_left he]

-- 读法：对 `t` 分类讨论。
private theorem read_line (x : U.Readings R fit σ v loc) (j : Fin u) (e : U.Raw R) (t : Bool)
    (he : supplySite (U.result R fit) e t = U.station R fit σ v loc) :
    U.values R fit σ v loc x j (.inr e) = x (supply U.post (U.result R fit) (U.station R fit σ v loc) e t he)
      (j.cast (width_supply U.post (U.result R fit) (U.station R fit σ v loc) e t he).symm) := by
  change outBits U.post (U.result R fit) (U.station R fit σ v loc) x j e = _
  unfold outBits
  cases t
  · rw [dite_eq_left he]
  · by_cases hf : supplySite (U.result R fit) e false = U.station R fit σ v loc
    · rw [dite_eq_left hf]
      congr 1
      · exact U.loop_port R fit σ v loc e hf he
      · apply (Fin.heq_ext_iff ((width_supply ..).trans (width_supply ..).symm)).mpr
        rfl
    · rw [dite_eq_right hf, dite_eq_left he]

variable {U R fit σ v loc} {V : Setup S h u a Δ D Y w B'} {fit' : V.Fits R c}
  {z : V.G.V} {Q : Relation U V} {k n : ℕ}

-- 读法：`Reads` 表示以下条件：对每个 `i j`，由 `U.portKey R fit _ i = V.portKey R fit' _ j` 推出 `∀ t t', t.val = t'.val → x i t = y j t'`。
def Reads (x : U.Readings R fit σ v loc) (y : V.Readings R fit' σ z loc) : Prop :=
  ∀ i j, U.portKey R fit _ i = V.portKey R fit' _ j →
    ∀ t t', t.val = t'.val → x i t = y j t'

variable (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
  {x : U.Readings R fit σ v loc} {y : V.Readings R fit' σ z loc} (hread : Reads x y)

include p hk hr hread in
-- 读法：要证明的命题是 `Alignment R fit fit' σ v z loc (U.values R fit σ v loc x j) (V.values R fit' σ z loc y j)`。
theorem Region.alignment (j : Fin u) : Alignment R fit fit' σ v z loc
    (U.values R fit σ v loc x j) (V.values R fit' σ z loc y j) := by
  constructor
  · intro e f t he hf hn
    have he' := old_at.mpr he
    have hf' := old_at.mpr hf
    change inBits U.post _ _ x t j e = inBits V.post _ _ y t j f
    simp only [inBits, dite_eq_left he', dite_eq_left hf']
    refine hread _ _ ?_ _ _ rfl
    rw [demand_key, demand_key, hn]
  · intro e f t he hf hn
    have he' := raw_at.mpr he
    have hf' := raw_at.mpr hf
    have r := p.raw_pair hk hr he hf hn
    rw [U.read_line R fit σ v loc x j e t he', V.read_line R fit' σ z loc y j f t hf']
    refine hread _ _ ?_ _ _ rfl
    simp only [supply_key, r.loop p (by omega), r.key]

include p hk hr hread in
-- 读法：`created U.post _ _ x` 等于 `created V.post _ _ y`。这里调用 `Finset.prod_congr`。
theorem Region.created : created U.post _ _ x = created V.post _ _ y := by
  apply Finset.prod_congr rfl
  intro j _
  exact (p.alignment hk hr hread j).value p hk hr

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 从已发布的局部表中还原原参数名称

**英文原文**

Recovering old argument names from a posted local table
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c) (σ : Cell a) (v : U.G.V) (loc : Coord R h a Δ)

-- 读法：`oldKey` 的结果类型为 `PortId R h`。
def oldKey (S : Scheme F) (b : Cell h) (k : B S.ℓ × B S.k) (j : B S.e) : PortId R h :=
  let pat := S.decode k.1
  if pat.peer k.2 j = none then .border b j.val
  else .demand (pat.direction k.2 j) (Encodable.encode (cellIndex h b, j, pat.direction k.2 j))

-- 读法：`U.portKey R fit _ p` 等于 `oldKey R S (blockOf x) (oldLabel U.post x.val) j`。对 `hp` 分类讨论。
theorem origin_key (x : U.Actors R fit σ v loc) (j : B S.e)
    {p : Port U.post (U.result R fit) (U.station R fit σ v loc)}
    (hp : Origin U.post (U.result R fit) (U.station R fit σ v loc) x.val j p) :
    U.portKey R fit _ p = oldKey R S (blockOf x) (oldLabel U.post x.val) j := by
  unfold oldKey
  dsimp only
  let t := U.post.vertex x.val
  change _ = if (S.pattern U.r t).peer t.2.2 j = none then PortId.border _ _ else _
  cases hp with
  | outside q hq he =>
    -- 推导：记下中间结论 `h`：`(S.pattern U.r t).peer t.2.2 j = none`。
    have h : (S.pattern U.r t).peer t.2.2 j = none := by
      have h := q.property.2
      rw [hq] at h
      simpa [t, Scheme.peer] using h
    rw [ite_eq_left h, exterior_key, hq]
    rfl
  | inside e b he hs =>
    have ht : (U.post.span e b).1 = t := congrArg Prod.fst he
    have hj : U.post.stub e b = j := congrArg Prod.snd he
    have hb : U.G.ix e = blockOf x := by
      unfold blockOf
      apply U.post.block.injective
      rw [U.post.vertex_eq] at he
      exact congrArg (fun p : S.Span => p.1.2.1) he
    have hi : (S.pattern U.r t).peer t.2.2 j ≠ none := by
      rw [← ht, ← hj]
      exact (U.post.link e b).trans_ne (by simp)
    rw [ite_eq_right hi, demand_key]
    change PortId.demand b (endName U.post e b) =
      .demand (S.direction U.r (t, j)) (Encodable.encode (cellIndex h (blockOf x), j, S.direction U.r (t, j)))
    -- 推导：记下中间结论 `hd`：`S.direction U.r (t, j) = b`。
    have hd : S.direction U.r (t, j) = b := (congrArg (S.direction U.r) he).symm.trans (U.post.dir e b)
    rw [hd, endName, hb, hj]

variable {U R fit σ v loc} {V : Setup S h u a Δ D Y w B'} {fit' : V.Fits R c}
  {z : V.G.V}

omit [Field F] in
-- 读法：`(History.original S m).weight x` 等于 `(History.original S n).weight y`。
private theorem original_congr {m n : B S.ℓ × B S.k} (h : m = n)
    (x : ∀ j : B S.e, Fin ((History.original S m).width j) → Bool)
    (y : ∀ j : B S.e, Fin ((History.original S n).width j) → Bool)
    (he : ∀ j t t', t.val = t'.val → x j t = y j t') :
    (History.original S m).weight x = (History.original S n).weight y := by
  subst n
  exact congrArg _ (funext fun j => funext fun t => he j t t rfl)

-- 读法：`previous U.post _ _ x i` 等于 `previous V.post _ _ y j`。这里调用 `original_congr`。
theorem Reads.previous {x : U.Readings R fit σ v loc} {y : V.Readings R fit' σ z loc}
    (r : Reads x y) (ht : U.Tags V σ v z)
    (i : U.Actors R fit σ v loc) (j : V.Actors R fit' σ z loc) (hb : blockOf i = blockOf j) :
    previous U.post _ _ x i = previous V.post _ _ y j := by
  have hl : oldLabel U.post i.val = oldLabel V.post j.val := by
    rw [actor_label, actor_label, ← hb, ht (blockOf i) (owner_here i.2.2).1]
  unfold Reset.previous
  apply original_congr hl
  intro t a b he
  apply r _ _ _ _ _ he
  have h₁ := U.origin_key R fit σ v loc i t (station_origin U.post _ _ i.val i.property.2 t a.pos)
  have h₂ := V.origin_key R fit' σ z loc j t (station_origin V.post _ _ j.val j.property.2 t b.pos)
  exact h₁.trans ((congrArg₂ (fun q l => oldKey R S q l t) hb hl).trans h₂.symm)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 收缩后重置表的局部相等性

**英文原文**

Local equality of contracted reset tables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {σ : Cell a} {v : U.G.V} {z : V.G.V}
  {loc : Coord R h a Δ} {Q : Relation U V} {k n e e' : ℕ}

local notation "d" => U.result R fit
local notation "d'" => V.result R fit'
local notation "b" => U.station R fit σ v loc
local notation "b'" => V.station R fit' σ z loc

-- 读法：`renameBits` 的取值由 `(f.prodCongr (.refl _)).arrowCongr (.refl _)` 给出。
private def renameBits (f : U.Unseen R fit σ v loc ≃ V.Unseen R fit' σ z loc) :
    (Inner d b → Bool) ≃ (Inner d' b' → Bool) :=
  (f.prodCongr (.refl _)).arrowCongr (.refl _)

-- 读法：要证明的命题是 `Reads (tape U.post d b s x t) (tape V.post d' b' s' y (renameBits f t))`。这里调用 `distinct_keys`。
private theorem tape_eq (f : U.Unseen R fit σ v loc ≃ V.Unseen R fit' σ z loc)
    (hf : ∀ t, V.hiddenKey R fit' σ z loc (f t) = U.hiddenKey R fit σ v loc t)
    (s : U.Seen R fit σ v loc ↪ B e) (s' : V.Seen R fit' σ z loc ↪ B e')
    (x : B e → ℕ → Bool) (y : B e' → ℕ → Bool)
    (he : ∀ i j, U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j → ∀ l, x (s i) l = y (s' j) l)
    (t : Inner d b → Bool) :
    Reads (tape U.post d b s x t) (tape V.post d' b' s' y (renameBits f t)) := by
  rintro (i|i) (j|j) h a a' ha
  · exact (he i j h a.val).trans (congrArg (y (s' j)) ha)
  · exact (distinct_keys i j h).elim
  · exact (distinct_keys j i h.symm).elim
  · have hj := V.hidden_inj R fit' σ z loc ((hf i).trans h)
    change t (i, a) = t (f.symm j, a')
    rw [← hj, Equiv.symm_apply_apply, Fin.ext ha]

-- 读法：`localEval U.post d b s x` 等于 `localEval V.post d' b' s' y`。这里调用 `Fintype.sum_equiv`。
/-- 对于在具名外部端口上取值相同的一切赋值，相匹配的输入补丁给出的表完全相同。

英文原文：Matched input patches yield exactly the same table for all
assignments agreeing at their named exterior ports.
-/
theorem Region.eval (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
    (ht : U.Tags V σ v z)
    (hu : ∀ t, U.G.diagram.arity t = 0 → ∀ x, Transcript.sample (U.G.diagram.table t) x = 1)
    (hv : ∀ t, V.G.diagram.arity t = 0 → ∀ x, Transcript.sample (V.G.diagram.table t) x = 1)
    (s : U.Seen R fit σ v loc ↪ B e) (s' : V.Seen R fit' σ z loc ↪ B e')
    (x : B e → ℕ → Bool) (y : B e' → ℕ → Bool)
    (he : ∀ i j, U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j → ∀ l, x (s i) l = y (s' j) l) :
    localEval U.post d b s x = localEval V.post d' b' s' y := by
  obtain ⟨f, hf⟩ := p.hidden (fit := fit) (fit' := fit') (loc := loc) hk hr
  obtain ⟨g, hg⟩ := (p.toSurvey.agree (by omega) hr).actors (fit := fit) (fit' := fit') (loc := loc) ht
  rw [eval_formula _ _ _ hu, eval_formula _ _ _ hv]
  apply Fintype.sum_equiv (renameBits f)
  intro t
  have H := tape_eq f hf s s' x y he t
  apply congrArg₂ (· * ·) _ (p.created hk hr H)
  exact Fintype.prod_equiv g _ _ (fun i => H.previous ht i (g i) (hg i).symm)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 对重置站点上所有可见区段统一编号

**英文原文**

A common numbering of all visible spans at a reset station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U V : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fit : U.Fits R c)
  (Z : Scheme F)

-- 读法：`visibleName` 的取值由 `⟨fun j => U.portKey R fit v (.inl j), (U.portKey_injective R fit v).comp Sum.inl_injective⟩` 给出。
def visibleName (v : U.At R fit) : Visible U.post (U.result R fit) v ↪ PortId R h :=
  ⟨fun j => U.portKey R fit v (.inl j), (U.portKey_injective R fit v).comp Sum.inl_injective⟩

-- 读法：`Room` 的取值由 `∀ v, Fintype.card (Visible U.post (U.result R fit) v) ≤ 2 ^ Z.e` 给出。
def Room := ∀ v, Fintype.card (Visible U.post (U.result R fit) v) ≤ 2 ^ Z.e

-- 读法：用字段 `host`、`block`、`index`、`seat` 构造 `Allocation U.post (U.result R fit) Z`。
def allocate (host : (U.result R fit).vertex ↪ B Z.m) (block : Cell a ↪ B Z.h)
    (index : (U.result R fit).vertex → (U.result R fit).vertex → B Z.d)
    (room : U.Room R fit Z) : Allocation U.post (U.result R fit) Z where
  host := host
  block := block
  index := index
  seat v := rank (U.visibleName R fit v) (room v)

variable {U V R fit Z}

-- 读法：`Ranked` 的取值由 `∀ v, A.seat v = rank (U.visibleName R fit v) (by simpa using Fintype.card_le_of_embedding (A.seat v))` 给出。
def Ranked (A : Allocation U.post (U.result R fit) Z) :=
  ∀ v, A.seat v = rank (U.visibleName R fit v) (by simpa using Fintype.card_le_of_embedding (A.seat v))

variable {fit' : V.Fits R c} {Q : Relation U V} {σ : Cell a} {k n : ℕ}
  {v : U.G.V} {z : V.G.V} {loc : Coord R h a Δ}
  {A : Allocation U.post (U.result R fit) Z} {A' : Allocation V.post (V.result R fit') Z}
  (p : Region U V σ Q n) (hk : k + (h - a) + 3 ≤ n) (hr : Q k v z)
  (ht : U.Tags V σ v z) (ha : Ranked A) (hb : Ranked A')

include p hk hr ht ha hb in
-- 读法：`A.seat _ i` 等于 `A'.seat _ j`。这里调用 `rank_eq`。
theorem Region.seat {i : U.Seen R fit σ v loc} {j : V.Seen R fit' σ z loc}
    (he : U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j) :
    A.seat _ i = A'.seat _ j := by
  obtain ⟨e, he'⟩ := p.visible (fit := fit) (fit' := fit') (loc := loc) hk hr ht
  rw [ha, hb]
  apply rank_eq _ _ he
  · exact fun i => ⟨e i, (he' i).1.symm⟩
  · intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact ⟨i, (he' i).1⟩

variable {s : (U.result R fit).Survivors} {r : (V.result R fit').Survivors} {b : Bool}

-- 读法：`(U.place R fit).symm (U.rawPlace R fit s.val b)` 等于 `whereAt U.post (U.result R fit) (.inr (s, b))`。使用 `U.place` 给出的结论。
theorem end_site (s : (U.result R fit).Survivors) (b : Bool) :
    (U.place R fit).symm (U.rawPlace R fit s.val b) = whereAt U.post (U.result R fit) (.inr (s, b)) :=
  (U.place R fit).symm_apply_apply _

include p hk hr ht ha hb in
-- 读法：`A.unitSeat s b` 等于 `A'.unitSeat r b`。这里调用 `A.slot_eq`。
theorem Region.unit_seat
    (hs : U.rawPlace R fit s.val b = (σ, v, loc)) (hr' : V.rawPlace R fit' r.val b = (σ, z, loc))
    (he : U.rawKey R s.val b = V.rawKey R r.val b) : A.unitSeat s b = A'.unitSeat r b := by
  let i : U.Seen R fit σ v loc := ⟨.inr (s, b), raw_at.mpr hs⟩
  let j : V.Seen R fit' σ z loc := ⟨.inr (r, b), raw_at.mpr hr'⟩
  have eq : U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j :=
    congrArg (PortId.line true b) he
  exact (A.slot_eq _ i).trans ((p.seat hk hr ht ha hb eq).trans (A'.slot_eq _ j).symm)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 重置后保留区段的对端地址

**英文原文**

The peer address of a surviving span after a reset
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S Z : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} (A : Allocation U.post (U.result R fit) Z)
  (A' : Allocation V.post (V.result R fit') Z)
  (Q : Relation U V) (σ : Cell a) (v : U.G.V) (z : V.G.V)

-- 读法：`IndexAgrees` 的结果类型为 `Prop`。
def IndexAgrees : Prop :=
  ∀ v' z', Q 1 v' z' → ∀ loc loc',
    A.index (U.station R fit σ v loc).2 (U.station R fit σ v' loc').2 =
    A'.index (V.station R fit' σ z loc).2 (V.station R fit' σ z' loc').2

variable {A A' Q σ v z} {loc : Coord R h a Δ} {n : ℕ}
  (p : Region U V σ Q n) (hk : (h - a) + 4 ≤ n) (hr : Q 0 v z)
  (ht : ∀ i j, Q 1 i j → U.Tags V σ i j) (ha : Ranked A) (hb : Ranked A')
  (hi : IndexAgrees A A' Q σ v z)
  {s : (U.result R fit).Survivors} {r : (V.result R fit').Survivors} {b : Bool}

-- 读法：`(U.station R fit σ v loc).2` 等于 `Allocation.endHost (q := U.result R fit) s b`。
theorem station_end (hs : U.rawPlace R fit s.val b = (σ, v, loc)) :
    (U.station R fit σ v loc).2 = Allocation.endHost (q := U.result R fit) s b := by
  rw [station, ← hs, end_site]
  rfl

include p hk hr ht ha hb hi in
-- 读法：证明中先建立 `hh`，即 `= p.raw_pair (k`。
theorem Region.link
    (hs : U.rawPlace R fit s.val b = (σ, v, loc)) (hr' : V.rawPlace R fit' r.val b = (σ, z, loc))
    (he : U.rawKey R s.val b = V.rawKey R r.val b) :
    A.unitSeat s (!b) = A'.unitSeat r (!b) ∧
    A.index (Allocation.endHost (q := U.result R fit) s b) (Allocation.endHost (q := U.result R fit) s (!b)) =
    A'.index (Allocation.endHost (q := V.result R fit') r b) (Allocation.endHost (q := V.result R fit') r (!b)) := by
  have hh := p.raw_pair (k := 0) (by omega) hr hs hr' he
  let x := U.rawPlace R fit s.val (!b)
  let y := V.rawPlace R fit' r.val (!b)
  have hx : U.rawPlace R fit s.val (!b) = (σ, x.2.1, x.2.2) := Prod.ext (hh.group _) rfl
  have hy : V.rawPlace R fit' r.val (!b) = (σ, y.2.1, x.2.2) :=
    Prod.ext (hh.group' _) (Prod.ext rfl (hh.coord _).symm)
  have heq : Q 1 x.2.1 y.2.1 := hh.host (!b)
  refine ⟨p.unit_seat (by omega) heq (ht _ _ heq) ha hb hx hy (hh.key _), ?_⟩
  rw [← station_end hs, ← station_end hx, ← station_end hr', ← station_end hy]
  exact hi _ _ heq loc x.2.2

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 首部与外部返回指针均由局部信息决定

**英文原文**

Both the header and the exterior return pointer are local
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring BatchDescent.Trail
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {e cap m d : ℕ}
  {b : Book S u e cap}
  (A : Allocation U.post (U.result R fit) (b.scheme m d a))
  (A' : Allocation V.post (V.result R fit') (b.scheme m d a))
  (Q : Relation U V) (σ : Cell a) (v : U.G.V) (z : V.G.V) (n : ℕ)

-- 读法：结构的字段包括 `region`、`depth`、`root`、`tags`、`block`。
structure Corresponds : Prop where
  region : Region U V σ Q n
  depth : h - a + 4 ≤ n
  root : Q 0 v z
  tags : ∀ i j, Q 1 i j → U.Tags V σ i j
  block : U.post.block = V.post.block
  left : Ranked A
  right : Ranked A'
  index : IndexAgrees A A' Q σ v z

namespace Corresponds
variable {A A' Q σ v z n} (p : Corresponds A A' Q σ v z n) {loc : Coord R h a Δ}
  {i : U.Seen R fit σ v loc} {j : V.Seen R fit' σ z loc}
include p

-- 读法：要证明的命题是 `U.Tags V σ v z`。使用 `p.tags` 给出的结论。
theorem at_root : U.Tags V σ v z := p.tags _ _ (p.region.widen (by omega) p.root)

-- 读法：`A.seat _ i` 等于 `A'.seat _ j`。使用 `p.region.seat` 给出的结论。
theorem seat (he : U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j) :
    A.seat _ i = A'.seat _ j :=
  p.region.seat (k := 0) (by have := p.depth; omega) p.root p.at_root p.left p.right he

-- 读法：结论为 `A.header (b.size U.post (U.result R fit)) i.val = A'.header (b.size V.post (V.result R fit')) j.val ∧ facePointer U.post (U.result R fit) i.val = facePointer V.post (V.result R fit') j.val`。
theorem header (he : U.visibleKey R fit σ v loc i = V.visibleKey R fit' σ z loc j)
    (hw : visibleWidth U.post (U.result R fit) i.val = visibleWidth V.post (V.result R fit') j.val) :
    A.header (b.size U.post (U.result R fit)) i.val = A'.header (b.size V.post (V.result R fit')) j.val ∧
    facePointer U.post (U.result R fit) i.val = facePointer V.post (V.result R fit') j.val := by
  have hb := congrArg b.put hw
  change b.size _ _ i.val = b.size _ _ j.val at hb
  rcases i with ⟨s|⟨s, t⟩, hs⟩ <;> rcases j with ⟨r|⟨r, t'⟩, hr⟩
  · obtain ⟨hx, hy⟩ := PortId.border.inj he
    have hy := Fin.ext hy
    obtain ⟨hg, hv⟩ := owner_here hs
    -- 推导：从 `owner_here hr` 中取出 `_, hz`。
    obtain ⟨_, hz⟩ := owner_here hr
    have hdr : S.direction U.r (U.post.vertex s.val.1, s.val.2) =
        S.direction V.r (V.post.vertex r.val.1, r.val.2) := by
      rw [U.post.vertex_eq, V.post.vertex_eq]
      change (U.pat _ _).direction 0 _ = (V.pat _ _).direction 0 _
      rw [hv, hz, ← hx, hy]
      unfold pat
      rw [p.at_root _ hg]
    constructor
    · simp only [Allocation.header, hdr, hb]
    · simp only [facePointer, stub, U.post.vertex_eq, V.post.vertex_eq, p.block, hx, hy]
  · cases he
  · cases he
  -- 推导：从 `PortId.line.inj he` 中取出 `_, rfl, hn`。
  · obtain ⟨_, rfl, hn⟩ := PortId.line.inj he
    obtain ⟨hseat, hindex⟩ := p.region.link p.depth p.root p.tags p.left p.right p.index
      (raw_at.mp hs) (raw_at.mp hr) hn
    exact ⟨by simp only [Allocation.header, hb, hseat, hindex], rfl⟩

end Corresponds
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 将相匹配的局部字段与指针序列化

**英文原文**

Serializing matched local fields and pointers
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring BatchDescent.Trail
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {e cap m d : ℕ}
  {b : Book S u e cap}
  (A : Allocation U.post (U.result R fit) (b.scheme m d a))
  (A' : Allocation V.post (V.result R fit') (b.scheme m d a))

-- 读法：`A.span j.val` 等于 `(A.vertex x, A.seat x j)`。使用 `Prod.ext` 给出的结论。
private theorem span_at (x : U.At R fit) (j : Visible U.post (U.result R fit) x) :
    A.span j.val = (A.vertex x, A.seat x j) :=
  Prod.ext (congrArg A.vertex j.property) (A.slot_eq _ j)

-- 读法：`(A.vertex x, s)` 不属于 `Set.range A.span`。
private theorem unused_at (x : U.At R fit) {s : B e} (hs : s ∉ Set.range (A.seat x)) :
    (A.vertex x, s) ∉ Set.range A.span := by
  rintro ⟨j, he⟩
  have hv : whereAt U.post (U.result R fit) j = x := A.vertex.injective (Prod.mk.inj he).1
  exact hs ⟨⟨j, hv⟩, (A.slot_eq x ⟨j, hv⟩).symm.trans (Prod.mk.inj he).2⟩

variable (parent : B m → B S.m)

-- 读法：`localPointers` 的取值由 `(A.move parent).commands (A.host x.2) (A.block x.1)` 给出。
def localPointers (x : U.At R fit) := (A.move parent).commands (A.host x.2) (A.block x.1)

variable {A A'} {Q : Relation U V} {σ : Cell a} {v : U.G.V} {z : V.G.V} {n : ℕ}
  (p : Corresponds A A' Q σ v z n) (loc : Coord R h a Δ)
local notation "src" => U.station R fit σ v loc
local notation "dst" => V.station R fit' σ z loc

include p in
-- 读法：`A.fields (b.size _ _) src s = A'.fields (b.size _ _) dst s` 与 `(A.move parent).read (A.vertex src, s) = (A'.move parent).read (A'.vertex dst, s)` 同时成立。按 `s ∈ Set.range (A.seat src)` 成立与否分情况。
private theorem slot_value (s : B e) :
    A.fields (b.size _ _) src s = A'.fields (b.size _ _) dst s ∧
    (A.move parent).read (A.vertex src, s) = (A'.move parent).read (A'.vertex dst, s) := by
  obtain ⟨f, hf⟩ := p.region.visible (k := 0) (fit := fit) (fit' := fit') (loc := loc)
    (by have := p.depth; omega) p.root p.at_root
  have hs (i) : A.seat src i = A'.seat dst (f i) := p.seat (hf i).1.symm
  by_cases h : s ∈ Set.range (A.seat src)
  · obtain ⟨i, rfl⟩ := h
    obtain ⟨hh, hp⟩ := p.header (hf i).1.symm (hf i).2.symm
    constructor
    · rw [Allocation.fields, Allocation.fields, (A.seat _).injective.extend_apply, hs,
        (A'.seat _).injective.extend_apply]
      exact hh
    · rw [← span_at, Allocation.read_span, hs, ← span_at, Allocation.read_span]
      exact hp
  have h' : s ∉ Set.range (A'.seat dst) := by
    rintro ⟨j, rfl⟩
    exact h ⟨f.symm j, by rw [hs, f.apply_symm_apply]⟩
  constructor
  · rw [Allocation.fields, Allocation.fields, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h']
  · rw [A.read_idle _ _ (unused_at A _ h), A'.read_idle _ _ (unused_at A' _ h')]

include p in
-- 读法：`localPointers A parent src` 等于 `localPointers A' parent dst`。用函数外延性比较等号两侧在 `j s` 处的取值。
theorem Corresponds.pointers : localPointers A parent src = localPointers A' parent dst := by
  funext j s
  have : j = 0 := Fin.eq_zero _
  subst j
  exact congrArg (point S) (slot_value parent p loc s).2

include p in
-- 读法：`(b.output A nav (A.host (src).2)).2 (A.block (src).1)` 等于 `(b.output A' nav' (A'.host (dst).2)).2 (A'.block (dst).1)`。
theorem Corresponds.tag (nav nav' : B m → B d → B m)
    (payload : b.data A src = b.data A' dst) :
    (b.output A nav (A.host (src).2)).2 (A.block (src).1) =
      (b.output A' nav' (A'.host (dst).2)).2 (A'.block (dst).1) := by
  change (Post.record d e b.d (.addr cap)).serial
    (A.records _ _ (A.vertex src).1 (A.vertex src).2.1) =
    (Post.record d e b.d (.addr cap)).serial (A'.records _ _ (A'.vertex dst).1 (A'.vertex dst).2.1)
  rw [Allocation.record_at, Allocation.record_at]
  have hh := funext fun s => (slot_value (fun _ => 0) p loc s).1
  simp only [Allocation.localRecord, hh, payload]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 重置的所有分支共用的输出模板

**英文原文**

The output template shared by all branches of a reset
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Packing History

variable {F : Type} [Field F] [Fintype F] {Y l u e cap : ℕ}

-- 读法：用字段 `scheme`、`count`、`load`、`park` 构造 `Template F`。
abbrev resetTarget (T : Template F) (b : Reset.Book T.scheme u e cap) (M : Meter)
    (m d a : ℕ) : Template F where
  scheme := b.scheme m d a
  count := M.count
  load := M.load
  park := M.park
  past := M.past
  order := Post.order d e b.d cap
  full := T.full

-- 读法：在后续公式中，`reset` 是 `T.resetTarget b M (T.scheme.m + Reset.Child.extra P Δ (T.scheme.h - a)) (Reset.Child.width D Y T.full) a` 的缩写。
abbrev reset (T : Template F) (P : Rotor F Y l) (Δ D a : ℕ)
    (b : Reset.Book T.scheme u e cap) (M : Meter) : Template F :=
  T.resetTarget b M (T.scheme.m + Reset.Child.extra P Δ (T.scheme.h - a))
    (Reset.Child.width D Y T.full) a

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 合并局部重置历史与公共图首部

**英文原文**

Combining local reset histories and the common graph header
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup A.scheme A.scheme.h u a Δ D Y w B') (R : Rotor F Y w)
  (fit : U.Fits R c) {e cap : ℕ} (b : Book A.scheme u e cap) (M : Template.Meter)

variable {mx dx : ℕ}
local notation "E" => (A.resetTarget b M mx dx a)

-- 读法：在后续公式中，`Layout` 是 `Allocation U.post (U.result R fit) (b.scheme mx dx a)` 的缩写。
abbrev Layout (mx dx : ℕ) := Allocation U.post (U.result R fit) (b.scheme mx dx a)

variable {U R fit b} (L : U.Layout R fit b mx dx) (g : (Child.Graph mx dx).obj)

-- 读法：结论为 `let src := Allocation.endHost (q := U.result R fit) i t let dst := Allocation.endHost (q := U.result R fit) i (!t) g.1 (L.host src) (L.index src dst) = L.host dst`。这里调用 `h.hop`。
theorem hop (h : Child.Describes (m := mx) (d := dx) A.full (U.graph R fit) L.host L.index g)
    (i : (U.result R fit).Survivors) (t : Bool) :
    let src := Allocation.endHost (q := U.result R fit) i t
    let dst := Allocation.endHost (q := U.result R fit) i (!t)
    g.1 (L.host src) (L.index src dst) = L.host dst := by
  apply h.hop
  cases t
  · exact (U.graph R fit).edge i
  · exact (U.graph R fit).cs _ _ ((U.graph R fit).edge i)

-- 读法：`counters` 的取值由 `Function.extend L.host (fun v => M.read (U.graph R fit) (v, (cellIndex a).symm j)) (fun _ => 0) i` 给出。
def counters (i : B mx) (j : B a) : B M.count :=
  Function.extend L.host (fun v => M.read (U.graph R fit) (v, (cellIndex a).symm j)) (fun _ => 0) i

-- 读法：`printed` 的取值由 `(b.output (m := mx) (d := dx) (h' := a) L g.1, fun i => ((g.2 i).1, (g.2 i).2, counters M L i))` 给出。
def printed : (E).format.obj :=
  (b.output (m := mx) (d := dx) (h' := a) L g.1, fun i => ((g.2 i).1, (g.2 i).2, counters M L i))

-- 读法：`Tile.header E (printed M L g)` 等于 `g`。两端由定义化简为同一项。
theorem printed_header : Tile.header E (printed M L g) = g := rfl

-- 读法：`(E).counter (printed M L g) (L.host v) (cellIndex a i)` 等于 `M.read (U.graph R fit) (v, i)`。
theorem counter_at (v : (U.graph R fit).V) (i : Cell a) :
    (E).counter (printed M L g) (L.host v) (cellIndex a i) = M.read (U.graph R fit) (v, i) := by
  change counters M L _ _ = _
  refine (L.host.injective.extend_apply _ _ _).trans ?_
  exact congrArg (fun j => M.read (U.graph R fit) (v, j)) ((cellIndex a).symm_apply_apply i)

-- 读法：用字段 `post`、`block`、`live`、`frozen` 构造 `(E).Encodes (printed M L g) (U.graph R fit)`。
def outputEncodes (H : b.Ready (m := mx) (d := dx) (h' := a) L g.1) (blk : L.block = (cellIndex a).toEmbedding)
    (head : Child.Describes (m := mx) (d := dx) A.full (U.graph R fit) L.host L.index g)
    (meter : M.Valid (U.graph R fit)) :
    (E).Encodes (printed M L g) (U.graph R fit) where
  post := H.posting
  block i := congrArg (fun f => f i) blk
  live := head.live
  frozen := head.frozen
  closed := head.closed
  reciprocal := head.reciprocal
  edge := head.edge
  core := head.core
  load v i := by
    change M.load ((E).counter _ (L.host v) (L.block i)) = _
    rw [blk, Equiv.toEmbedding_apply, counter_at]
    exact (meter (v, i)).1
  park v i := by
    change M.park ((E).counter _ (L.host v) (L.block i)) = _
    rw [blk, Equiv.toEmbedding_apply, counter_at]
    exact (meter (v, i)).2.1
  past v i := by
    change M.past ((E).counter _ (L.host v) (L.block i)) = _
    rw [blk, Equiv.toEmbedding_apply, counter_at]
    exact (meter (v, i)).2.2

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 每个重置站点的静态父位置

**英文原文**

The static parent of each reset station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] [Fintype F] (A : Template F) {u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U : Setup A.scheme A.scheme.h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {e cap t d : ℕ} {b : Book A.scheme u e cap}
  (L : U.Layout R fit b (A.scheme.m + t) d) (locate : Coord R A.scheme.h a Δ ↪ B t)

-- 读法：结构的字段包括 `block`、`host`。
structure Placed : Prop where
  block : L.block = (cellIndex a).toEmbedding
  host : ∀ σ v loc, L.host (U.station R fit σ v loc).2 =
    (Match.rowIndex A.scheme.m t).symm (U.post.host v, locate loc)

-- 读法：在后续公式中，`parent` 是 `(Match.rowIndex A.scheme.m t j).1` 的缩写。
abbrev parent (t : ℕ) (j : B (A.scheme.m + t)) := (Match.rowIndex A.scheme.m t j).1

variable {A L locate} (p : Placed A L locate)

omit [Fintype F] in
-- 读法：`(U.result R fit).origin (U.station R fit σ v loc).2` 等于 `v`。
theorem station_owner (U : Setup A.scheme A.scheme.h u a Δ D Y w B') (R : Rotor F Y w)
    (fit : U.Fits R c) (σ : Cell a) (v : U.G.V) (loc : Coord R A.scheme.h a Δ) :
    (U.result R fit).origin (U.station R fit σ v loc).2 = v := by
  cases loc <;> rfl

include p in
-- 读法：`parent A t (L.host w)` 等于 `U.post.host ((U.result R fit).origin w)`。
theorem Placed.parent (w : (U.result R fit).vertex) :
    parent A t (L.host w) = U.post.host ((U.result R fit).origin w) := by
  obtain ⟨⟨σ, v, loc⟩, he⟩ := (U.place R fit).symm.surjective (0, w)
  have hw : (U.station R fit σ v loc).2 = w := congrArg Prod.snd he
  rw [← hw, p.host, station_owner]
  exact congrArg Prod.fst ((Match.rowIndex _ _).apply_symm_apply _)

include p in
-- 读法：`(Match.rowIndex _ _).symm (v, s) ∈ Set.range L.host` 与 `v ∈ Set.range U.post.host ∧ s ∈ Set.range locate` 等价。
theorem Placed.live (v : B A.scheme.m) (s : B t) :
    (Match.rowIndex _ _).symm (v, s) ∈ Set.range L.host ↔
      v ∈ Set.range U.post.host ∧ s ∈ Set.range locate := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨⟨σ, z, loc⟩, he⟩ := (U.place R fit).symm.surjective (0, w)
    have hz : (U.station R fit σ z loc).2 = w := congrArg Prod.snd he
    rw [← hz, p.host] at hw
    obtain ⟨hv, hs⟩ := Prod.mk.inj ((Match.rowIndex _ _).symm.injective hw)
    exact ⟨⟨z, hv⟩, ⟨loc, hs⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact ⟨(U.station R fit 0 i j).2, p.host ..⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 布置重置硬件并依次为其区段编号

**英文原文**

Placing the reset hardware and successively numbering its spans
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] (U : Setup A.scheme A.scheme.h u a Δ D Y w W)
  (R : Rotor F Y w) (fit : U.Fits R cost)
  {e cap d : ℕ} (b : Book A.scheme u e cap)
local notation "t" => (Child.extra R Δ (A.scheme.h - a))
local notation "mx" => (A.scheme.m + t)
variable (index : (U.graph R fit).V → (U.graph R fit).V → B d)
    (room : U.Room R fit (b.scheme (A.scheme.m + Child.extra R Δ (A.scheme.h - a)) d a))

-- 读法：`arrange` 的取值由 `U.allocate R fit (b.scheme mx d a) (U.host R fit) (cellIndex a).toEmbedding index room` 给出。
def arrange : U.Layout R fit b mx d :=
  U.allocate R fit (b.scheme mx d a) (U.host R fit) (cellIndex a).toEmbedding index room

omit [Fintype F] in
-- 读法：`U.parts R fit (U.station R fit σ v loc).2` 等于 `(v, loc)`。使用 `U.parts` 给出的结论。
theorem station_parts (σ : Cell a) (v : U.G.V) (loc : Coord R A.scheme.h a Δ) :
    U.parts R fit (U.station R fit σ v loc).2 = (v, loc) :=
  (U.parts R fit).apply_symm_apply _

-- 读法：要证明的命题是 `Placed A (U.arrange R fit b index room) (Child.code R Δ (A.scheme.h - a))`。
theorem arrange_placed : Placed A (U.arrange R fit b index room) (Child.code R Δ (A.scheme.h - a)) := by
  refine ⟨rfl, fun σ v loc => ?_⟩
  change U.host R fit _ = _
  exact congrArg (fun x => (Match.rowIndex _ _).symm
    (U.post.host x.1, Child.code R Δ (A.scheme.h - a) x.2)) (station_parts U R fit σ v loc)

-- 读法：要证明的命题是 `Ranked (U.arrange R fit b index room)`。
theorem arrange_ranked : Ranked (U.arrange R fit b index room) := fun _ => rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end
