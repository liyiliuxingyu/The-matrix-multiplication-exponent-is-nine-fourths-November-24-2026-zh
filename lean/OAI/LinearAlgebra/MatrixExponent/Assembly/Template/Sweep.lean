-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.Mixer.Choice
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow

/-!
# 将解码出的历史记录计入当前端口与已撤除端口

已退役的内部端口沿用系接线端点的分配方式。新的核心接触项增加可用预算。

**英文原文**

Charging decoded histories to current and retired ports

Retired internal ports follow the same assignment as tether
endpoints. New core contacts increase the available budget.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {h a u z Δ D k : ℕ}
  (G : HostNet F L h u)

-- 读法：`footprint` 的取值由 `G.past v + G.tetherLoad v + degree G.pair v * u` 给出。
def footprint (v : G.V × Cell h) := G.past v + G.tetherLoad v + degree G.pair v * u

-- 读法：`degree (G.regroup a ha).pair (splitAddr G.V a ha v)` 等于 `degree G.pair v`。
theorem regroup_degree (ha : a ≤ h) (v : G.V × Cell h) :
    degree (G.regroup a ha).pair (splitAddr G.V a ha v) = degree G.pair v := by
  let e := splitAddr G.V a ha
  change degree (fun i => Prod.map e e (G.pair i)) (e v) = _
  rw [degree_map]
  simp

-- 读法：`(G.regroup a ha).footprint (splitAddr G.V a ha v)` 等于 `G.footprint v`。
theorem regroup_footprint (ha : a ≤ h) (v : G.V × Cell h) :
    (G.regroup a ha).footprint (splitAddr G.V a ha v) = G.footprint v := by
  let e := splitAddr G.V a ha
  have ext : (exterior G.diagram (e ∘ G.units.place) (e v) : ℝ) = G.tetherLoad v := by
    rw [exterior_comp]
    simp [push, tetherLoad]
  unfold footprint
  rw [G.regroup_degree]
  change G.past (e.symm (e v)) + _ + _ = _
  rw [Equiv.symm_apply_apply, show (G.regroup a ha).tetherLoad _ = _ from Nat.cast_injective ext]

variable [Fintype T]

-- 读法：`G.footprint v` 不超过 `(2 : ℝ) ^ L.discount * G.load v.1 v.2`。
theorem footprint_le (hm : G.mass ≤ L.cap) (v : G.V × Cell h) :
    G.footprint v ≤ (2 : ℝ) ^ L.discount * G.load v.1 v.2 := by
  have hr := G.rate_le
  have hs := mul_nonneg L.pos.le (push_nonneg G.park L.charge L.nonneg v)
  have hi := mul_le_of_le_one_left
    (show 0 ≤ (G.tetherLoad v : ℝ) + degree G.pair v * (u : ℝ) by positivity) hr
  have hv : G.rate * (G.footprint v : ℝ) ≤ G.load v.1 v.2 := by
    simp only [load, footprint, Nat.cast_add, Nat.cast_mul]
    linarith only [hi, hs]
  rw [rate, ite_eq_left hm, one_div_mul_eq_div] at hv
  exact ((div_le_iff₀ (by positivity)).mp hv).trans_eq (mul_comm _ _)

-- 读法：`push (G.regroup a ha).park L.charge (splitAddr G.V a ha v)` 等于 `push G.park L.charge v`。
theorem regroup_park (ha : a ≤ h) (v : G.V × Cell h) :
    push (G.regroup a ha).park L.charge (splitAddr G.V a ha v) = push G.park L.charge v := by
  let e := splitAddr G.V a ha
  change push (e ∘ G.park) L.charge (e v) = _
  simp [push]
  congr! 2

variable [Field F] {B : ℝ} {P : Gadget F} {H : HostNet F L h (P.b * z)}
  (s : H.Projection Δ D a) (g : Grouping H.N H.C Δ D k B H.load)
  (m : Matching (g.ends H.src H.ix) (g.ends H.dst H.ix) H.ix)
  (hz : 0 < z) (hle : Δ ≤ D) (i : g.Choice m P) (v : Site H.V h)

local notation "Q" => contracted s g m hz hle i
local notation "f" => Function.uncurry (g.route m (g.layout m P i))

-- 读法：`push f l v` 等于 `push (assignment s g m i) l (s.place v)`。这里调用 `ite_eq_left`。
theorem push_route (l : H.V × Cell h → ℝ) :
    push f l v = push (assignment s g m i) l (s.place v) := by
  simp only [push, assignment, s.place.injective.eq_iff, Function.uncurry_def]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

-- 读法：`push f (push H.park L.charge) v` 等于 `push (Q).park L.charge (s.place v)`。
theorem park_route : push f (push H.park L.charge) v = push (Q).park L.charge (s.place v) := by
  rw [push_route s g m i, push_comp]
  rfl

-- 读法：`push f (fun t => (H.past t + degree H.pair t * (P.b * z) : ℕ)) v` 等于 `(Q).past (s.place v)`。
theorem past_route :
    push f (fun t => (H.past t + degree H.pair t * (P.b * z) : ℕ)) v = (Q).past (s.place v) := by
  rw [push_route s g m i]
  change _ = (H.carried (assignment s g m i) (s.place v) : ℝ)
  simp only [carried, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, push]

-- 读法：`push f (fun t => (H.footprint t : ℝ)) v` 不超过 `(Q).footprint (s.place v)`。
theorem footprint_route : push f (fun t => (H.footprint t : ℝ)) v ≤ (Q).footprint (s.place v) := by
  have ext : push f (fun t => (H.tetherLoad t : ℝ)) v = (Q).tetherLoad (s.place v) := by
    rw [push_route s g m i]
    unfold tetherLoad
    erw [← exterior_comp, port_load]
  have add : push f (fun t => (H.footprint t : ℝ)) v =
      push f (fun t => (H.past t + degree H.pair t * (P.b * z) : ℕ)) v +
        push f (fun t => (H.tetherLoad t : ℝ)) v := by
    unfold push
    rw [← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · simp only [footprint, Nat.cast_add]; exact add_right_comm _ _ _
    · exact (add_zero _).symm
  erw [add, ext, past_route s g m hz hle i]
  simp only [footprint, Nat.cast_add]
  exact le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) _)

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# 把记录的计费量分成核心元数和冻结权重

**英文原文**

Splitting the recorded charge into core arity and frozen weight
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
open Coloring Packing Rounds
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {u : ℕ}
    {D : Template F} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u} (s : D.Shows r Q)

-- 读法：`weight` 的取值由 `D.load (D.counter r (s.host a.1) (cellIndex _ a.2))` 给出。
def weight (a : Q.V × Cell D.scheme.h) :=
  D.load (D.counter r (s.host a.1) (cellIndex _ a.2))

-- 读法：`s.weight a` 等于 `push Q.frame.place Q.charge a`。
theorem weight_eq (a : Q.V × Cell D.scheme.h) : s.weight a = push Q.frame.place Q.charge a := by
  rw [weight, s.amount]
  unfold push
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [s.vertex]
  simp only [s.host.injective.eq_iff, (cellIndex _).injective.eq_iff, ← Prod.ext_iff]
  congr

-- 读法：`s.weight (Q.frame.place v)` 等于 `Q.charge v`。
theorem weight_at (v : Q.diagram.V) : s.weight (Q.frame.place v) = Q.charge v := by
  rw [weight_eq]
  simp [push, Q.one.eq_iff]

-- 读法：`D.load (D.counter r (s.pres.vertex v).1 (s.pres.vertex v).2.1)` 等于 `Q.charge v`。这里调用 `s.weight_at`。
theorem amount_at (v : Q.diagram.V) :
    D.load (D.counter r (s.pres.vertex v).1 (s.pres.vertex v).2.1) = Q.charge v := by
  rw [s.vertex]
  exact s.weight_at v

-- 读法：`0 < D.load (D.counter r i j)` 与 `(i, j, 0) ∈ Set.range s.pres.vertex` 等价。
theorem occupied (hu : 0 < u) (i : B D.scheme.m) (j : B D.scheme.h) :
    0 < D.load (D.counter r i j) ↔ (i, j, 0) ∈ Set.range s.pres.vertex := by
  constructor
  · intro h
    by_contra! hc
    have hz : D.load (D.counter r i j) = 0 := by
      rw [s.amount]
      refine Finset.sum_eq_zero fun v _ => ite_eq_right ?_
      rintro ⟨hi, hj⟩
      exact hc ⟨v, Prod.ext hi (Prod.ext hj (by rw [s.vertex]))⟩
    linarith
  · rintro ⟨v, hv⟩
    have := s.amount_at v
    rw [hv] at this
    rw [this]
    exact (Nat.cast_pos.mpr hu).trans_le (Q.floor v)

-- 读法：`push f l a` 等于 `0`。
private theorem missing {J I : Type} [Fintype J] {f : J → I} {a : I} (l : J → ℝ)
    (h : ∀ j, f j ≠ a) : push f l a = 0 := by simp [push, h]

-- 读法：`push (fun t : Q.freeze.Fixed => Q.frame.place t.val) (fun t => Q.charge t.val) a` 等于 `if D.frozen r (s.host a.1) then s.weight a else 0`。按 `∃ v, Q.frame.place v = a` 成立与否分情况。
theorem frozen_weight (a : Q.V × Cell D.scheme.h) :
    push (fun t : Q.freeze.Fixed => Q.frame.place t.val) (fun t => Q.charge t.val) a =
      if D.frozen r (s.host a.1) then s.weight a else 0 := by
  by_cases h : ∃ v, Q.frame.place v = a
  · obtain ⟨v, rfl⟩ := h
    rw [s.weight_at]
    have hv := (s.frozen (Q.frame.place v).1).trans (Q.frame.keep v)
    by_cases f : Q.freeze.frozen v
    · rw [ite_eq_left (hv.mpr f)]
      let w : Q.freeze.Fixed := ⟨v, f⟩
      change push _ _ (Q.frame.place w.val) = Q.charge w.val
      simp [push, Q.one.eq_iff, Subtype.val_inj]
    · rw [ite_eq_right (mt hv.mp f)]
      exact missing _ fun j he => f (Q.one he ▸ j.property)
  · have ha v : Q.frame.place v ≠ a := fun he => h ⟨v, he⟩
    rw [s.weight_eq, missing Q.charge ha, ite_self]
    exact missing _ fun j => ha j.val

-- 读法：按 `∃ v, Q.frame.place v = a` 成立与否分情况。
theorem mobile_weight (a : Q.V × Cell D.scheme.h) :
    push (fun t : Q.freeze.Core => Q.frame.place t.val) (fun t => (Q.diagram.arity t.val : ℝ)) a =
      if D.frozen r (s.host a.1) then 0 else max 0 (s.weight a - u) := by
  by_cases h : ∃ v, Q.frame.place v = a
  · obtain ⟨v, rfl⟩ := h
    rw [s.weight_at, s.charge, add_sub_cancel_right, max_eq_right (Nat.cast_nonneg _)]
    have hv := (s.frozen (Q.frame.place v).1).trans (Q.frame.keep v)
    by_cases f : Q.freeze.frozen v
    · rw [ite_eq_left (hv.mpr f)]
      exact missing _ fun j he => j.property ((Q.one he).symm ▸ f)
    · rw [ite_eq_right (mt hv.mp f)]
      let w : Q.freeze.Core := ⟨v, f⟩
      change push _ _ (Q.frame.place w.val) = (Q.diagram.arity w.val : ℝ)
      simp [push, Q.one.eq_iff, Subtype.val_inj]
  · have ha v : Q.frame.place v ≠ a := fun he => h ⟨v, he⟩
    rw [s.weight_eq, missing Q.charge ha, max_eq_left (sub_nonpos.mpr (Nat.cast_nonneg _)), ite_self]
    exact missing _ fun j => ha j.val

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
end

/-!
# 由切割后表示所编码的核心

**英文原文**

The core encoded by a cut presentation
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
open Coloring Packing Rounds
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {u : ℕ}
    {D : Template F} {r : D.format.obj} {Q : LocalTerm F x y D.scheme.h u}
    (s : D.Shows r Q) (hu : 0 < u) (L : Fringe Q.freeze.x Q.freeze.y Q.freeze.Fixed)
    (hL : L.tensor = Q.freeze.border.tensor) (hc : L.charge = fun i => Q.charge i.val)

local notation "G" => Q.frame.hostOf hu L hL s.packets
local notation "Y" => D.cut u L.scale
local notation "t" => D.remove u L.scale r

include hc in
-- 读法：`(Y).park ((Y).counter t (s.host v) (cellIndex _ i))` 等于 `push (G).park L.charge (v, i)`。
private theorem park_at (v : Q.V) (i : Cell D.scheme.h) :
    (Y).park ((Y).counter t (s.host v) (cellIndex _ i)) = push (G).park L.charge (v, i) := by
  have hf := s.frozen_weight (v, i)
  rw [← hc] at hf
  refine Eq.trans ?_ hf.symm
  simp only [weight, Template.counter, Template.cut, Template.remove, Equiv.symm_apply_apply]

include hc in
-- 读法：`(Y).load ((Y).counter t (s.host v) (cellIndex _ i))` 等于 `(G).load v i`。
private theorem load_at (v : Q.V) (i : Cell D.scheme.h) :
    (Y).load ((Y).counter t (s.host v) (cellIndex _ i)) = (G).load v i := by
  have h := HostNet.load_eq (G) (v, i)
  rw [show (G).past (v, i) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero] at h
  have hf := s.frozen_weight (v, i)
  rw [← hc] at hf
  refine Eq.trans ?_ h.symm
  change _ = push (fun j : Q.freeze.Core => Q.frame.place j.val) (fun j => (Q.diagram.arity j.val : ℝ)) (v, i)
    + L.scale * push (fun j : Q.freeze.Fixed => Q.frame.place j.val) L.charge (v, i)
  rw [s.mobile_weight, hf]
  simp only [weight, Template.counter, Template.cut, Template.remove, Equiv.symm_apply_apply]
  split <;> simp only [zero_add, mul_zero, add_zero]

-- 读法：用字段 `post`、`block`、`live`、`frozen` 构造 `(Y).Encodes t (G)`。
def encode : (Y).Encodes t (G) where
  post := s.posting hu L hL
  block _ := rfl
  live := s.live
  frozen := s.frozen
  closed := s.closed
  reciprocal := s.reciprocal
  edge := s.edge
  core := s.core
  load := s.load_at hu L hL hc
  park := s.park_at hu L hL hc
  past _ _ := rfl

-- 读法：`(s.encode hu L hL hc).post.toPresentation.borderWidth j` 等于 `u`。使用 `s.pres.freeze_borderWidth` 给出的结论。
theorem span (j : (s.encode hu L hL hc).post.toPresentation.BorderSpan) :
    (s.encode hu L hL hc).post.toPresentation.borderWidth j = u :=
  s.pres.freeze_borderWidth Q.freeze (D.mobile r) s.kept s.uniform j

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Shows
end

/-!
# 给定网络板表示的外部数据高度

**英文原文**

Exterior payload height of a presented board
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
open Coloring
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F a b D.scheme.h} (p : D.Presents r P)

include p in
-- 读法：要证明的命题是 `D.scheme.Fits r.1 (2 ^ D.scheme.m + wd a + wd b) (D.scheme.h + t)`。
/-- 每个宿主在每块中至多有一个站点。用外部比特所属的块及其在该站点所有端口中的序号编制索引。

英文原文：A host has at most one station in each block. Index an exterior bit
by its block and its ordinal among all ports of that station.
-/
theorem fits {t : ℕ} (bound : ∀ v, P.diagram.arity v ≤ 2 ^ t) :
    D.scheme.Fits r.1 (2 ^ D.scheme.m + wd a + wd b) (D.scheme.h + t) := by
  refine p.pres.fits le_rfl fun i => ?_
  let e := Equiv.ofBijective p.pres.toSeating.atPin p.pres.toSeating.atPin_bijective
  let locate (q : D.scheme.fiber r.1 i) := e.symm q.val.val
  have loc (q : D.scheme.fiber r.1 i) : (p.pres.vertex (locate q).1).1 = i :=
    (congrArg (fun z => z.1.1.1) (e.apply_symm_apply q.val.val)).trans q.property
  let rank (v : P.diagram.V) : P.diagram.Port v ↪ B t :=
    Classical.choice (Function.Embedding.nonempty_of_card_le
      (by simpa [Diagram.Port, Diagram.arity] using bound v))
  let encode (q : Σ v, P.diagram.Port v) := ((p.pres.vertex q.1).2.1, rank q.1 q.2)
  have eq_of_code (q s : Σ v, P.diagram.Port v)
      (he : (p.pres.vertex q.1).1 = (p.pres.vertex s.1).1) (hh : encode q = encode s) : q = s := by
    -- 推导：从 `q` 中取出 `v, k`。
    obtain ⟨v, k⟩ := q
    obtain ⟨w, l⟩ := s
    have hv : v = w := p.pres.vertex.injective (Prod.ext he
      (Prod.ext (congrArg (fun z : B D.scheme.h × B t => z.1) hh) (by rw [p.vertex, p.vertex])))
    subst w
    exact congrArg (Sigma.mk v) ((rank v).injective (congrArg Prod.snd hh))
  have hinj : Function.Injective (encode ∘ locate) := fun q s h =>
    Subtype.ext (Subtype.ext (e.symm.injective (eq_of_code _ _ ((loc q).trans (loc s).symm) h)))
  simpa [Scheme.load, pow_add] using Fintype.card_le_of_injective _ hinj

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
end

/-!
# 将元数、暂存的计费量与累积历史编码为一个字

**英文原文**

Encoding arity, parked charge, and accumulated history in one word
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

-- 读法：结构的字段包括 `count`、`load`、`park`、`past`、`encode`。
structure Meter where
  count : ℕ
  load : B count → ℝ
  park : B count → ℝ
  past : B count → ℕ
  encode : ℕ → ℝ → ℕ → B count

namespace Meter
variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (M : Meter) (H : HostNet F L h u)

-- 读法：`read` 的取值由 `M.encode (H.tetherLoad w + Packing.degree H.pair w * u) (push H.park L.charge w) (H.past w)` 给出。
def read (w : H.V × Cell h) :=
  M.encode (H.tetherLoad w + Packing.degree H.pair w * u) (push H.park L.charge w) (H.past w)

-- 读法：`Valid` 表示以下条件：对每个 `w`，`M.load (M.read H w) = H.load w.1 w.2` 与 `M.park (M.read H w) = push H.park L.charge w ∧ M.past (M.read H w) = H.past w` 同时成立。
def Valid : Prop :=
  ∀ w, M.load (M.read H w) = H.load w.1 w.2 ∧
    M.park (M.read H w) = push H.park L.charge w ∧ M.past (M.read H w) = H.past w

end Meter
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# 记录元数、暂存计费量和历史的有界整数计数器

**英文原文**

Bounded integer counters for arity, parked charge, and history
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Meter
open Coloring Packing
open scoped Classical

-- 读法：在后续公式中，`words` 是 `B n × B n × B n` 的缩写。
private abbrev words (n : ℕ) := B n × B n × B n

-- 读法：`pack` 的取值由 `Fintype.equivOfCardEq (by simp only [words, Fintype.card_prod, Fintype.card_fin, ← pow_add] congr 1; omega)` 给出。
private def pack (n : ℕ) : words n ≃ B (3 * n) := Fintype.equivOfCardEq (by
  simp only [words, Fintype.card_prod, Fintype.card_fin, ← pow_add]
  congr 1; omega)

-- 读法：当 `h : x < 2 ^ n` 成立时取 `⟨x, h⟩`，否则取 `0`。
private def word (n x : ℕ) : B n := if h : x < 2 ^ n then ⟨x, h⟩ else 0

-- 读法：`(word n x).val` 等于 `x`。
private theorem exact_word {n x : ℕ} (h : x < 2 ^ n) : (word n x).val = x := by simp [word, h]

-- 读法：用字段 `count`、`load`、`park`、`past` 构造 `Meter`。
def bounded (n : ℕ) (scale rate : ℝ) : Meter where
  count := 3 * n
  load i := let w := (pack n).symm i
            w.1.val + scale * w.2.1.val + rate * w.2.2.val
  park i := ((pack n).symm i).2.1.val
  past i := ((pack n).symm i).2.2.val
  encode a p c := pack n (word n a, word n ⌊p⌋₊, word n c)

variable {F T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (G : HostNet F L h u)

-- 读法：要证明的命题是 `(bounded n L.scale rate).Valid G`。
theorem bounded_valid (n : ℕ) (rate : ℝ) (hr : G.rate = rate)
    (hi : ∀ v, G.footprint v < 2 ^ n)
    (hp : ∀ v, ∃ j : ℕ, j < 2 ^ n ∧ push G.park L.charge v = j) :
    (bounded n L.scale rate).Valid G := by
  intro v
  obtain ⟨j, hj, hp⟩ := hp v
  have ha : G.tetherLoad v + Packing.degree G.pair v * u < 2 ^ n := by
    have := hi v; unfold HostNet.footprint at this; omega
  have hc : G.past v < 2 ^ n := by
    have := hi v; unfold HostNet.footprint at this; omega
  simp only [read, bounded, hp, Nat.floor_natCast, Equiv.symm_apply_apply, exact_word ha,
    exact_word hj, exact_word hc, HostNet.load, hr, Prod.mk.eta, Nat.cast_add, Nat.cast_mul, and_self]

-- 读法：存在 `j : ℕ`，`j < 2 ^ n` 与 `push G.park L.charge v = j` 同时成立。
theorem parked (n : ℕ) (hl : ∀ v i, G.load v i < L.scale * (2 : ℝ) ^ n)
    (charge : ∀ t, ∃ x : ℕ, L.charge t = x) (v : G.V × Cell h) :
    ∃ j : ℕ, j < 2 ^ n ∧ push G.park L.charge v = j := by
  choose f hf using charge
  let j := ∑ t, if G.park t = v then f t else 0
  have hj : push G.park L.charge v = (j : ℝ) := by
    simp only [push, j, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, hf]
  refine ⟨j, ?_, hj⟩
  have he : L.scale * j ≤ G.load v.1 v.2 := by
    unfold HostNet.load
    rw [hj]
    exact (le_add_of_nonneg_left (by positivity)).trans
      (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _)))
  have hh := lt_of_mul_lt_mul_left (he.trans_lt (hl _ _)) L.pos.le
  exact_mod_cast hh

-- 读法：要证明的命题是 `(bounded n L.scale (1 / (2 : ℝ) ^ L.discount)).Valid G`。
theorem valid_of_charge (n : ℕ) (B : ℝ)
    (mass : G.mass ≤ L.cap) (load : ∀ v i, G.load v i ≤ B)
    (scale : B < L.scale * (2 : ℝ) ^ n) (size : (2 : ℝ) ^ L.discount * B < (2 : ℝ) ^ n)
    (charge : ∀ t, ∃ x : ℕ, L.charge t = x) :
    (bounded n L.scale (1 / (2 : ℝ) ^ L.discount)).Valid G := by
  refine bounded_valid G n _ (ite_eq_left mass) ?_ ?_
  · intro v
    have hv := (G.footprint_le mass v).trans (mul_le_mul_of_nonneg_left (load v.1 v.2) (by positivity))
    exact_mod_cast hv.trans_lt size
  · exact parked G n (fun v i => (load v i).trans_lt scale) charge

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Meter
end

/-!
# 取出孤立标量时保留宿主元数据

**英文原文**

Keeping host metadata while withdrawing isolated scalars
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

namespace Assembly.Template
variable (T : Template F)

-- 读法：在后续公式中，`sweep` 是 `{ T with scheme := T.scheme.sweep }` 的缩写。
abbrev sweep : Template F := { T with scheme := T.scheme.sweep }

variable {T} {Z : Type} [Fintype Z] {L : Packing.Fringe x y Z} {u : ℕ}
  {r : T.format.obj} {G : Packing.HostNet F L T.scheme.h u}

-- 读法：`Encodes.sweep` 的取值由 `{ e with post := e.post.sweep }` 给出。
def Encodes.sweep (e : T.Encodes r G) : T.sweep.Encodes r G.sweep :=
  { e with post := e.post.sweep }

end Assembly.Template

end OAI.LinearAlgebra.MatrixExponent
end

/-!
# 合并控制器短记录并读取相邻的记录头

**英文原文**

Combining short controller records and reading neighboring headers
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

variable {F : Type} [Field F] {u m n k : ℕ} {L : Set (Table F)} {A D E : Format}

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `(.pair D E)` 实现映射 `(fun x => (f x, g x))` 的开销至多为 `(20 * A.width + m + n)`。
theorem Map.pair {f : A.obj → D.obj} {g : A.obj → E.obj} (hu : 3 ≤ u)
    (hf : Map F u L A D f m) (hg : Map F u L A E g n) :
    Map F u L A (.pair D E) (fun x => (f x, g x)) (20 * A.width + m + n) := by
  have h : Circuit F A (.pair A A) (fun x => (x, x)) (5 * A.width) := by
    refine (Circuit.project (D := .pair A A) (Sum.elim id id) ?_).mono ?_
    · rintro x (i|i) <;> rfl
    · simp only [Format.width_pair]; omega
  exact ((Map.circuit hu h).comp (hf.par hg)).mono (by omega)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `D` 实现映射 `f` 的开销至多为 `(4 * (A.width + 2 * D.width))`。使用 `Map.circuit` 给出的结论。
theorem Map.project {f : A.obj → D.obj} (hu : 3 ≤ u) (e : D.pins → A.pins)
    (he : ∀ x i, D.code (f x) i = A.code x (e i)) :
    Map F u L A D f (4 * (A.width + 2 * D.width)) := Map.circuit hu (Circuit.project e he)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `D` 实现映射 `f` 的开销至多为 `(4 * (2 ^ h * (100 + b) ^ d))`。这里调用 `Map.circuit`。
theorem Map.cheap {h b d : ℕ} {f : A.obj → D.obj} (hu : 3 ≤ u) (hf : Cheap F h b A D f d) :
    Map F u L A D f (4 * (2 ^ h * (100 + b) ^ d)) := by
  obtain ⟨_, ht, hc⟩ := hf
  exact Map.circuit hu (ht.mono (by omega))

namespace Template

variable (D : Template F) (k : ℕ)
-- 读法：在后续公式中，`Depths` 是 `Mixing.Num D.scheme.m k` 的缩写。
abbrev Depths := Mixing.Num D.scheme.m k
-- 读法：在后续公式中，`Next` 是 `Mixing.Matrix D.scheme.m D.scheme.d k` 的缩写。
abbrev Next := Mixing.Matrix D.scheme.m D.scheme.d k
-- 读法：在后续公式中，`NetworkDepths` 是 `D.format.pair (D.Depths k)` 的缩写。
abbrev NetworkDepths := D.format.pair (D.Depths k)
-- 读法：在后续公式中，`Queries` 是 `(D.Depths k).pair (.vec D.scheme.d (Perm D.scheme.m))` 的缩写。
private abbrev Queries := (D.Depths k).pair (.vec D.scheme.d (Perm D.scheme.m))

-- 读法：输入 `i j` 时返回 `x.2 (D.nav x.1 i j)`。
def nearDepth (x : (D.NetworkDepths k).obj) : (D.Next k).obj :=
  fun i j => x.2 (D.nav x.1 i j)

-- 读法：`nearCost` 的构造用到 `D.NetworkDepths`、`D.Queries`、`D.scheme.m`。
def nearCost := 4 * ((D.NetworkDepths k).width + 2 * (D.Queries k).width) +
  4 * (2 ^ D.scheme.m * (100 + (D.scheme.m + k + 2 ^ D.scheme.d)) ^ 12)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(D.NetworkDepths k)` 到 `(D.Next k)` 实现映射 `(D.nearDepth k)` 的开销至多为 `(D.nearCost k)`。这里调用 `Map.project`。
theorem near_net (hu : 3 ≤ u) :
    Map F u L (D.NetworkDepths k) (D.Next k) (D.nearDepth k) (D.nearCost k) := by
  let X := D.NetworkDepths k
  let Y := D.Queries k
  let b := D.scheme.m + k + 2 ^ D.scheme.d
  have prep : Map F u L X Y (fun x => (x.2, fun i j => D.nav x.1 j i)) (4 * (X.width + 2 * Y.width)) := by
    apply Map.project hu (Sum.elim Sum.inr (fun t => .inl (.inl (t.2.1, .inl (t.1, t.2.2)))))
    rintro x (i|i) <;> rfl
  have he : 0 < 2 ^ D.scheme.d := by positivity
  have hn := Cheap.neighbors F (.addr k) D.scheme.m b D.scheme.d
    (by unfold b; omega) (by rw [Format.width_addr]; unfold b; omega) (by unfold b; omega)
  exact prep.comp (Map.cheap hu hn)

end Template
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 计算混排器与深度记录的格式和成本

**英文原文**

Formats and costs for computing the mixer and depth records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d

-- 读法：在后续公式中，`Sources` 是 `Format.vec m (.vec h T.MixSource)` 的缩写。
abbrev Sources := Format.vec m (.vec h T.MixSource)
-- 读法：在后续公式中，`Digits` 是 `Format.vec h (T.Summand d)` 的缩写。
abbrev Digits := Format.vec h (T.Summand d)
-- 读法：在后续公式中，`Split` 是 `Format.pair (Mixing.Num h d) (Mixing.Matrix h b T.CounterBits)` 的缩写。
abbrev Split := Format.pair (Mixing.Num h d) (Mixing.Matrix h b T.CounterBits)
-- 读法：在后续公式中，`Stats` 是 `Format.vec m (T.Statistics k)` 的缩写。
abbrev Stats := Format.vec m (T.Statistics k)
-- 读法：在后续公式中，`Window` 是 `Format.pair .bit ((Group.Flags b).pair (.pair (.addr k) (Mixing.Num b k)))` 的缩写。
abbrev Window := Format.pair .bit ((Group.Flags b).pair (.pair (.addr k) (Mixing.Num b k)))
-- 读法：在后续公式中，`Windows` 是 `Format.vec m (Window T k)` 的缩写。
abbrev Windows := Format.vec m (Window T k)
-- 读法：在后续公式中，`Travel` 是 `(T.NetworkDepths k).pair (T.Depths k)` 的缩写。
abbrev Travel := (T.NetworkDepths k).pair (T.Depths k)
-- 读法：在后续公式中，`Heads` 是 `Format.vec T.widthCols (Mixing.Header k)` 的缩写。
abbrev Heads := Format.vec T.widthCols (Mixing.Header k)
-- 读法：在后续公式中，`Sides` 是 `Format.pair (.vec m (Heads T k)) (Mixing.Matrix m h T.profileBits)` 的缩写。
abbrev Sides := Format.pair (.vec m (Heads T k)) (Mixing.Matrix m h T.profileBits)
-- 读法：在后续公式中，`First` 是 `T.format.pair (Stats T k)` 的缩写。
abbrev First := T.format.pair (Stats T k)
-- 读法：在后续公式中，`Both` 是 `(First T k).pair (T.Depths k)` 的缩写。
abbrev Both := (First T k).pair (T.Depths k)

-- 读法：`project` 的取值由 `4 * (A.width + 2 * B.width)` 给出。
def project (A B : Format) := 4 * (A.width + 2 * B.width)

-- 读法：`arity` 的构造用到 `T.MixSource.width`、`T.Summand`、`T.profileBits`。
def arity := 3 + T.MixSource.width + (T.Summand d).width + (d + h) + k +
  (Window T k).width + (Heads T k).width + T.profileBits + Mixing.arity T.widthCols h k T.profileBits d

-- 读法：`localCost` 的构造用到 `Mixing.collectCost`、`T.CounterBits`。
def localCost := 2 ^ h * (1 + arity T k d) + project (Digits T d) (Split T d) +
  (4 * (2 ^ h * (100 + d) ^ 5) + (1 + arity T k d) + 4 * Mixing.collectCost h b T.CounterBits)

-- 读法：`tallyCost` 的取值由 `project T.format (Sources T) + 2 ^ m * localCost T k d` 给出。
def tallyCost := project T.format (Sources T) + 2 ^ m * localCost T k d

-- 读法：`gatherCost` 的构造用到 `T.NetworkDepths`、`T.nearCost`、`T.Next`。
def gatherCost := 24 * (Travel T k).width + project (Travel T k) (T.NetworkDepths k) +
  T.nearCost k + project ((Travel T k).pair (T.Next k)) (Windows T k)

-- 读法：`waveCost` 的构造用到 `T.NetworkDepths`、`T.Depths`。
def waveCost (n : ℕ) := project (T.NetworkDepths k) (T.Depths k) +
  n * (24 * (T.NetworkDepths k).width + gatherCost T k + 2 ^ m * (1 + arity T k d))

-- 读法：`profileCost` 的构造用到 `T.NetworkDepths`、`T.profileShape`。
def profileCost := 20 * (T.NetworkDepths k).width +
  (project (T.NetworkDepths k) (Travel T k) + gatherCost T k + 2 ^ m * (1 + arity T k d)) +
  (project (T.NetworkDepths k) (Sources T) + 2 ^ m * (2 ^ h * (1 + arity T k d))) +
  project (Sides T k) (T.profileShape k)

-- 读法：`cost` 的构造用到 `T.format.width`、`T.NetworkDepths`、`Mixing.extractionCost`。
def cost (n : ℕ) := 48 * T.format.width + tallyCost T k d +
  24 * (First T k).width + project (First T k) (T.NetworkDepths k) + waveCost T k d n +
  20 * (Both T k).width + project (Both T k) (T.NetworkDepths k) + profileCost T k d +
  Mixing.extractionCost m T.widthCols h k T.profileBits d + Mixing.cost (m + T.widthCols) h k d +
  project (Both T k) (Stats T k)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end

/-!
# 选择混排器所用的短表

**英文原文**

The short tables used to select a mixer
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d

-- 读法：结构的字段包括 `a`、`u`、`Δ`、`D`、`Z`。
structure Params where
  a : ℕ
  u : ℕ
  Δ : ℕ
  D : ℕ
  Z : ℕ
  g : ℕ
  W : ℝ

variable (C : Params)

-- 读法：`step` 的取值由 `Fin.ofNat _ (Mixing.update C.Δ C.D z.2.1 z.2.2.1.val (fun j => (z.2.2.2 j).val))` 给出。
def step (z : (Window T k).obj) : B k :=
  Fin.ofNat _ (Mixing.update C.Δ C.D z.2.1 z.2.2.1.val (fun j => (z.2.2.2 j).val))

-- 读法：`heads` 的取值由 `T.heads z.1 z.2.2.1 z.2.2.2` 给出。
def heads (z : (Window T k).obj) : (Heads T k).obj := T.heads z.1 z.2.2.1 z.2.2.2

-- 读法：`pack` 的取值由 `(Match.rowIndex _ _).symm z` 给出。
def pack (z : T.MixSource.obj) : B T.profileBits := (Match.rowIndex _ _).symm z

variable [Field F]
open scoped Classical

-- 读法：在后续公式中，`election` 是 `Mixing.rowKeys C.g (T.getLoad C.u C.Z d) F h k` 的缩写。
abbrev election := Mixing.rowKeys C.g (T.getLoad C.u C.Z d) F h k

-- 读法：`keys` 的构造用到 `Mixing.graph`、`T.MixSource`、`T.Summand`。
def keys :=
  insert (Mixing.graph F T.MixSource (T.Summand d) (T.summand C.Z d))
  (insert (Mixing.graph F (.addr (d + h)) (.addr k) (request C.a C.Z k C.W))
  (insert (Mixing.graph F (Window T k) (.addr k) (step T k C))
  (insert (Mixing.graph F (Window T k) (Heads T k) (heads T k))
  (insert (Mixing.graph F T.MixSource (.addr T.profileBits) (pack T))
    (election T k d C)))))

-- 读法：`(keys T k d C).card` 不超过 `12`。这里调用 `Finset.card_insert_le`。
theorem few : (keys T k d C).card ≤ 12 := by
  unfold keys
  iterate 5
    apply (Finset.card_insert_le _ _).trans
    apply Nat.add_le_add_right
  exact Mixing.rowKeys_size ..

-- 读法：`wd v.1 + wd v.2.1` 不超过 `arity T k d`。
theorem narrow {v : Table F} (hv : v ∈ keys T k d C) :
    wd v.1 + wd v.2.1 ≤ arity T k d := by
  unfold arity
  simp only [keys, Finset.mem_insert] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | hv
  · simp only [Mixing.graph, lookup, wd_word]; omega
  · simp only [Mixing.graph, lookup, wd_word, Format.width_addr]; omega
  · simp only [Mixing.graph, lookup, wd_word, Format.width_addr]; omega
  · simp only [Mixing.graph, lookup, wd_word]; omega
  · simp only [Mixing.graph, lookup, wd_word, Format.width_addr]; omega
  · exact (Mixing.rowKeys_arity _ _ hv).trans (Nat.le_add_left ..)

variable {u : ℕ} {L : Set (Table F)} (ha : arity T k d ≤ u) (hl : (keys T k d C : Set _) ⊆ L)

omit [Field F] in
include ha in
-- 读法：`3` 不超过 `u`。
theorem three : 3 ≤ u := by unfold arity at ha; omega

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `D` 实现映射 `f` 的开销至多为 `(1 + arity T k d)`。这里调用 `Mixing.gate`。
theorem gate (A D : Format) (f : A.obj → D.obj) (hf : Mixing.graph F A D f ∈ keys T k d C) :
    Map F u L A D f (1 + arity T k d) := by
  have hb : A.width + D.width ≤ arity T k d := by
    simpa only [Mixing.graph, lookup, wd_word] using narrow T k d C hf
  exact (Mixing.gate (hb.trans ha) (hl hf)).mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end

/-!
# 对每个宿主的缩放负载与接触数分别求和

**英文原文**

Summing the scaled load and contact counts at each host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d
variable [Field F] (C : Params) {u : ℕ} {L : Set (Table F)}
  (ha : arity T k d ≤ u) (hl : (keys T k d C : Set _) ⊆ L)
open scoped Classical

-- 读法：逐一匹配以下输入模式：`(i, j, .inl x)`、`(i, j, .inr x)`。
def readSource : (Sources T).pins → T.format.pins
  | (i, j, .inl x) => .inl (i, .inr (j, x))
  | (i, j, .inr x) => .inr (i, .inr (.inr (j, x)))

omit [Field F] in
-- 读法：`(Sources T).code (T.source r) i` 等于 `T.format.code r (readSource T i)`。
theorem source_read (r : T.format.obj) (i : (Sources T).pins) :
    (Sources T).code (T.source r) i = T.format.code r (readSource T i) := by
  rcases i with ⟨i, j, x|x⟩ <;> rfl

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(.vec h T.MixSource)` 到 `(T.Statistics k)` 实现映射 `(T.summary C.a C.Z k d C.W)` 的开销至多为 `(localCost T k d)`。
private theorem summary_net :
    Map F u L (.vec h T.MixSource) (T.Statistics k) (T.summary C.a C.Z k d C.W)
      (localCost T k d) := by
  have hu := three T k d ha
  have h₁ := gate T k d C ha hl T.MixSource (T.Summand d) (T.summand C.Z d)
    (Finset.mem_insert_self ..)
  have h₂ := gate T k d C ha hl (.addr (d + h)) (.addr k) (request C.a C.Z k C.W)
    (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have split : Map F u L (Digits T d) (Split T d) (fun q => (fun j => (q j).1, fun j => (q j).2))
      (project (Digits T d) (Split T d)) := by
    refine Map.project hu (Sum.elim (fun p => (p.1, .inl p.2)) (fun p => (p.1, .inr p.2))) ?_
    rintro q (i|i) <;> rfl
  have h₃ := (Map.cheap (L:=L) hu (cheap_total F h d)).comp h₂
  have h₄ := Map.circuit (L:=L) hu (Mixing.collect_net F h b T.CounterBits)
  exact ((Map.vec (t:=h) _ (fun _ => h₁)).comp split).comp (h₃.par h₄)

-- 读法：输入 `v` 时返回 `(T.startDepth C.a C.Z k d C.W r v, T.unitCount r v)`。
def tally (r : T.format.obj) : (Stats T k).obj := fun v =>
  (T.startDepth C.a C.Z k d C.W r v, T.unitCount r v)

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `T.format` 到 `(Stats T k)` 实现映射 `(tally T k d C)` 的开销至多为 `(tallyCost T k d)`。这里调用 `prep.comp`。
theorem tally_net : Map F u L T.format (Stats T k) (tally T k d C) (tallyCost T k d) := by
  have prep := Map.project (L:=L) (three T k d ha) (readSource T) (source_read T)
  exact prep.comp (Map.vec _ (fun _ => summary_net T k d C ha hl))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end

/-!
# 沿宿主图传播基区深度

**英文原文**

Propagating the base depths through the host graph
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d
variable [Field F] (C : Params) {u : ℕ} {L : Set (Table F)}
  (ha : arity T k d ≤ u) (hl : (keys T k d C : Set _) ⊆ L)
open scoped Classical

-- 读法：输入 `v` 时返回 `(T.live x.1.1 v, T.flags x.1.1 v, x.1.2 v, x.2 ∘ T.nav x.1.1 v)`。
def gather (x : (Travel T k).obj) : (Windows T k).obj :=
  fun v => (T.live x.1.1 v, T.flags x.1.1 v, x.1.2 v, x.2 ∘ T.nav x.1.1 v)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(Travel T k)` 到 `(Windows T k)` 实现映射 `(gather T k)` 的开销至多为 `(gatherCost T k)`。这里调用 `Map.project`。
theorem gather_net (hu : 3 ≤ u) : Map F u L (Travel T k) (Windows T k) (gather T k)
    (gatherCost T k) := by
  let A := Travel T k
  let B := T.NetworkDepths k
  let D := A.pair (T.Next k)
  have pick : Map F u L A B (fun x => (x.1.1, x.2)) (project A B) := by
    apply Map.project hu (Sum.elim (fun i => .inl (.inl i)) Sum.inr)
    rintro x (i|i) <;> rfl
  let f (x : D.obj) (v : Coloring.B m) := (T.live x.1.1.1 v, T.flags x.1.1.1 v, x.1.1.2 v, x.2 v)
  have last : Map F u L D (Windows T k) f (project D (Windows T k)) := by
    let j : (Windows T k).pins → D.pins
      | (v, .inl i) => .inl (.inl (.inl (.inr (v, .inl (.inl i)))))
      | (v, .inr (.inl i)) => .inl (.inl (.inl (.inr (v, .inr (.inl i)))))
      | (v, .inr (.inr (.inl i))) => .inl (.inl (.inr (v, i)))
      | (v, .inr (.inr (.inr i))) => .inr (v, i)
    apply Map.project hu j
    rintro x ⟨v, i|i|i|i⟩ <;> rfl
  have mid := (Map.circuit hu (Circuit.id F A)).pair hu (pick.comp (T.near_net k hu))
  exact (mid.comp last).mono (by unfold gatherCost; dsimp only [A, B, D]; omega)

-- 读法：`wave` 的取值由 `Mixing.wave C.Δ C.D (T.nav x.1) (T.flags x.1) x.2 n` 给出。
def wave (n : ℕ) (x : (T.NetworkDepths k).obj) :=
  Mixing.wave C.Δ C.D (T.nav x.1) (T.flags x.1) x.2 n

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(T.NetworkDepths k)` 到 `(T.Depths k)` 实现映射 `(wave T k C n)` 的开销至多为 `(waveCost T k d n)`。对 `n` 作归纳。
theorem wave_net (n : ℕ) : Map F u L (T.NetworkDepths k) (T.Depths k) (wave T k C n)
    (waveCost T k d n) := by
  have hu := three T k d ha
  induction n with
  | zero =>
    rw [waveCost, zero_mul, add_zero]
    exact Map.project hu Sum.inr (fun _ _ => rfl)
  | succ n ih =>
    have g := gate T k d C ha hl (Window T k) (.addr k) (step T k C) (by simp [keys])
    have upd := (gather_net T k hu).comp (Map.vec (t:=m) _ (fun _ => g))
    have data := (Map.circuit hu (Circuit.id F (T.NetworkDepths k))).pair hu ih
    exact (data.comp upd).mono (by unfold waveCost; rw [Nat.succ_mul n]; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end

/-!
# 准备表决选取混排器所用的行矩阵

**英文原文**

Preparing the matrix of rows used by the mixer election
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d
variable [Field F] (C : Params) {u : ℕ} {L : Set (Table F)}
  (ha : arity T k d ≤ u) (hl : (keys T k d C : Set _) ⊆ L)
open scoped Classical

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(T.NetworkDepths k)` 到 `(T.profileShape k)` 实现映射 `(fun x => T.profile x.1 x.2)` 的开销至多为 `(profileCost T k d)`。这里调用 `Map.project`。
theorem profile_net : Map F u L (T.NetworkDepths k) (T.profileShape k) (fun x => T.profile x.1 x.2)
    (profileCost T k d) := by
  have hu := three T k d ha
  let A := T.NetworkDepths k
  have dup : Map F u L A (Travel T k) (fun x => (x, x.2)) (project A (Travel T k)) := by
    apply Map.project hu (Sum.elim id Sum.inr)
    rintro x (j|j) <;> rfl
  have head := gate T k d C ha hl (Window T k) (Heads T k) (heads T k) (by simp [keys])
  have first := (dup.comp (gather_net T k hu)).comp (Map.vec (t:=m) _ (fun _ => head))
  have data : Map F u L A (Sources T) (fun x => T.source x.1) (project A (Sources T)) :=
    Map.project hu (Sum.inl ∘ readSource T) (fun x i => source_read T x.1 i)
  have encode := gate T k d C ha hl T.MixSource (.addr T.profileBits) (pack T) (by simp [keys])
  have second := data.comp (Map.vec (t:=m) _ (fun _ => Map.vec (t:=h) _ (fun _ => encode)))
  have zip : Map F u L (Sides T k) (T.profileShape k) (fun x v => (x.1 v, x.2 v))
      (project (Sides T k) (T.profileShape k)) := by
    apply Map.project (A:=Sides T k) hu (fun p : (T.profileShape k).pins => p.2.elim (fun i => .inl (p.1, i)) (fun i => .inr (p.1, i)))
    rintro x ⟨v, i|i⟩ <;> rfl
  exact (Map.pair hu first second).comp zip

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end

/-!
# 联合计算选定的混排器、最终深度和接触总数的电路

**英文原文**

Joint circuit for the elected mixer, final depths and contact totals
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
open Coloring
variable {F : Type} (T : Template F) (k d : ℕ)
local notation "m" => T.scheme.m
local notation "h" => T.scheme.h
local notation "b" => T.scheme.d
variable [Field F] (C : Params) {u : ℕ} {L : Set (Table F)}
  (ha : arity T k d ≤ u) (hl : (keys T k d C : Set _) ⊆ L)
open scoped Classical

-- 读法：`prepare` 的结果类型为 `(History.Reset.Tile.pair T k).obj`。
def prepare (t : ℕ) (hk : h < 2 ^ k) (r : T.format.obj) : (History.Reset.Tile.pair T k).obj :=
  (r, T.mixerChoice C.a t C.Δ C.D C.u C.g C.Z k d hk C.W r,
    fun v => (T.baseDepth C.a t C.Δ C.D C.Z k d C.W r v, T.unitCount r v))

include ha hl in
-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `T.format` 到 `(History.Reset.Tile.pair T k)` 实现映射 `(prepare T k d C t hk)` 的开销至多为 `(cost T k d (h - t - C.a))`。这里调用 `Map.project`。
theorem prepare_net (t : ℕ) (hk : h < 2 ^ k) :
    Map F u L T.format (History.Reset.Tile.pair T k) (prepare T k d C t hk) (cost T k d (h - t - C.a)) := by
  have hu := three T k d ha
  let A := First T k
  let D := Both T k
  let Y := T.NetworkDepths k
  have start : Map F u L A Y (fun x => (x.1, fun v => (x.2 v).1)) (project A Y) := by
    apply Map.project hu (Sum.map id (fun p => (p.1, .inl p.2)))
    rintro q (i|⟨i, j⟩) <;> rfl
  have select : Map F u L D Y (fun x => (x.1.1, x.2)) (project D Y) := by
    apply Map.project hu (Sum.map Sum.inl id)
    rintro q (i|i) <;> rfl
  -- 推导：记下中间结论 `stats`：`Map F u L D (Stats T k) (fun x v => (x.2 v, (x.1.2 v).2)) (project D (Stats T k))`。
  have stats : Map F u L D (Stats T k) (fun x v => (x.2 v, (x.1.2 v).2)) (project D (Stats T k)) := by
    apply Map.project (A:=D) hu (fun p : (Stats T k).pins => p.2.elim (fun i => .inr (p.1, i)) (fun i => .inl (.inr (p.1, .inr i))))
    rintro q ⟨i, j|j⟩ <;> rfl
  have input := Map.circuit (L:=L) hu (Circuit.id F T.format)
  have sums := Map.pair hu input (tally_net T k d C ha hl)
  have run := start.comp (wave_net T k d C ha hl (h - t - C.a))
  have mid := sums.comp (Map.pair hu (Map.circuit hu (Circuit.id F A)) run)
  have prof := select.comp (profile_net T k d C ha hl)
  have keys' : (election T k d C : Set (Table F)) ⊆ L := by
    intro i hi
    apply hl
    iterate 5 apply Finset.mem_insert_of_mem
    exact hi
  -- 推导：记下中间结论 `win`：`= Mixing.elect_records («m»`。
  have win := Mixing.elect_records («m»:=m) C.g (T.getLoad C.u C.Z d) hk
    ((Nat.le_add_left ..).trans ha) keys'
  have elect := mid.comp (Map.pair hu (prof.comp win) stats)
  exact (Map.pair hu input elect).mono (by unfold cost; dsimp only [A, D, Y, First, Both]; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Mix
end
