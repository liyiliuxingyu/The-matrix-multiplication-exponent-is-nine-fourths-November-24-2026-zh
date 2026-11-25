-- 本文件所属证明环节：在有限域上把具有短标签的调用编成批量下降过程；结合带标签置换的难度和对角抵抗性，导出多份独立列表同时判重的规模下界。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Observed
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Packing.Budget
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.TraceNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes

/-!
# 将块地址的前缀移入宿主坐标

表标签保持原值。每个邻点地址都加上与当前宿主相同的前缀，与标签数据无关。

**英文原文**

Moving a block prefix into the host coordinate

The table labels stay unchanged. Each neighbor address acquires the
same prefix as the current host, independently of the label data.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
open Assembly Coloring Packing

variable {F : Type}

-- 读法：在后续公式中，`target` 是 `{ S with m := S.m + k, h := S.h - k }` 的缩写。
abbrev target (S : Scheme F) (k : ℕ) : Scheme F := { S with m := S.m + k, h := S.h - k }

variable {S : Scheme F} (k : ℕ) (hk : k ≤ S.h)

-- 读法：`blocks` 的取值由 `(cellIndex _).symm.trans ((splitCell k hk).trans ((cellIndex _).prodCongr (cellIndex _)))` 给出。
def blocks : B S.h ≃ B k × B (S.h - k) :=
  (cellIndex _).symm.trans ((splitCell k hk).trans ((cellIndex _).prodCongr (cellIndex _)))

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `S.Vtx ≃ (target S k).Vtx`。
def room : S.Vtx ≃ (target S k).Vtx where
  toFun v := ((Match.rowIndex S.m k).symm (v.1, (blocks k hk v.2.1).1),
    (blocks k hk v.2.1).2, v.2.2)
  invFun v := ((Match.rowIndex S.m k v.1).1,
    (blocks k hk).symm ((Match.rowIndex S.m k v.1).2, v.2.1), v.2.2)
  left_inv v := by simp
  right_inv v := by simp

-- 读法：`span` 的取值由 `(room k hk).prodCongr (.refl _)` 给出。
def span : S.Span ≃ (target S k).Span := (room k hk).prodCongr (.refl _)

-- 读法：`rows` 的结果类型为 `(target S k).format.obj`。
def rows (r : S.format.obj) : (target S k).format.obj := fun i =>
  let a := Match.rowIndex S.m k i
  (fun j => (Match.rowIndex S.m k).symm ((r a.1).1 j, a.2),
   fun j => (r a.1).2 ((blocks k hk).symm (a.2, j)))

-- 读法：用字段 `short`、`long` 构造 `Trail.Record (target S k) h d e`。
def trail {h d e : ℕ} (data : Trail.Record S h d e) : Trail.Record (target S k) h d e where
  short := data.short ∘ (span k hk).symm
  long := fun i => data.long (Match.rowIndex S.m k i).1

variable (r : S.format.obj)

-- 读法：`(target S k).pattern (rows k hk r) (room k hk v)` 等于 `S.pattern r v`。
theorem pattern (v : S.Vtx) :
    (target S k).pattern (rows k hk r) (room k hk v) = S.pattern r v := by
  simp [Scheme.pattern, rows, room, target]

-- 读法：`(target S k).width (rows k hk r) (span k hk q)` 等于 `S.width r q`。
theorem width (q : S.Span) :
    (target S k).width (rows k hk r) (span k hk q) = S.width r q := by
  exact congrArg (fun t => t.width q.1.2.2 q.2) (pattern k hk r q.1)

-- 读法：`(target S k).direction (rows k hk r) (span k hk q)` 等于 `S.direction r q`。
theorem direction (q : S.Span) :
    (target S k).direction (rows k hk r) (span k hk q) = S.direction r q := by
  exact congrArg (fun t => t.direction q.1.2.2 q.2) (pattern k hk r q.1)

-- 读法：`(target S k).peer (rows k hk r) (span k hk q)` 等于 `(S.peer r q).map (span k hk)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem peer (q : S.Span) :
    (target S k).peer (rows k hk r) (span k hk q) = (S.peer r q).map (span k hk) := by
  unfold Scheme.peer
  change (((target S k).pattern (rows k hk r) (room k hk q.1)).peer q.1.2.2 q.2).map _ = _
  rw [pattern, Option.map_map]
  congr 1
  funext x
  simp [span, room, rows]

-- 读法：要证明的命题是 `(target S k).Proper (rows k hk r)`。
theorem proper (hp : S.Proper r) : (target S k).Proper (rows k hk r) := by
  intro a b h
  obtain ⟨q, rfl⟩ := (span k hk).surjective a
  obtain ⟨w, rfl⟩ := (span k hk).surjective b
  rw [peer, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, he⟩ := h
  have := (span k hk).injective he
  subst t
  obtain ⟨hw, hl, hd⟩ := hp _ _ ht
  rw [peer, hw, width, width, direction, direction]
  exact ⟨rfl, hl, hd⟩

-- 读法：在后续公式中，`Pins` 是 `Σ t, Fin (P.width j t)` 的缩写。
private abbrev Pins {d l e : ℕ} (P : Pattern F d l e) (j : B l) :=
  Σ t, Fin (P.width j t)

-- 读法：`pins` 的取值由 `Equiv.sigmaCongrRight fun t => finCongr (congrArg (fun a => a.width j t) he.symm)` 给出。
private def pins {d l e : ℕ} {P Q : Pattern F d l e} (he : Q = P) (j : B l) :
    Pins P j ≃ Pins Q j :=
  Equiv.sigmaCongrRight fun t => finCongr (congrArg (fun a => a.width j t) he.symm)

-- 读法：`Q.value j (fun s i => t ⟨s, i⟩)` 等于 `P.value j (fun s i => t (pins he j ⟨s, i⟩))`。对 `he` 分类讨论。
private theorem value {d l e : ℕ} {P Q : Pattern F d l e} (he : Q = P) (j : B l)
    (t : Pins Q j → Bool) :
    Q.value j (fun s i => t ⟨s, i⟩) = P.value j (fun s i => t (pins he j ⟨s, i⟩)) := by
  cases he
  rfl

-- 读法：`ports` 的取值由 `pins (pattern k hk r v) v.2.2` 给出。
private def ports (v : S.Vtx) :
    S.LocalPin r v ≃ (target S k).LocalPin (rows k hk r) (room k hk v) :=
  pins (pattern k hk r v) v.2.2

-- 读法：`(target S k).table (rows k hk r) (room k hk v) t` 等于 `S.table r v (t ∘ ports k hk r v)`。
private theorem table (v : S.Vtx)
    (t : (target S k).LocalPin (rows k hk r) (room k hk v) → Bool) :
    (target S k).table (rows k hk r) (room k hk v) t = S.table r v (t ∘ ports k hk r v) :=
  value (pattern k hk r v) v.2.2 t

variable {r} [Field F] {x y : Wire} {G : Diagram F x y}

-- 读法：用字段 `vertex`、`pin`、`cover`、`obtain` 构造 `(target S k).Seating (rows k hk r) G`。
def seat (p : S.Seating r G) : (target S k).Seating (rows k hk r) G where
  vertex := p.vertex.trans (room k hk).toEmbedding
  pin v := (p.pin v).trans (ports k hk r _)
  cover := by
    rintro ⟨q, i⟩
    obtain ⟨a, rfl⟩ := (span k hk).surjective q
    obtain ⟨v, hv⟩ := p.cover ⟨a, finCongr (width k hk r a) i⟩
    exact ⟨v, congrArg (room k hk) hv⟩
  sample v t := (table k hk r _ t).trans (p.sample v _)
  vacant := by
    intro v hv t
    obtain ⟨z, rfl⟩ := (room k hk).surjective v
    rw [table]
    apply p.vacant
    rintro ⟨i, rfl⟩
    exact hv ⟨i, rfl⟩

-- 读法：`((seat k hk p).ends z).1 = span k hk (p.ends z).1` 与 `((seat k hk p).ends z).2.val = (p.ends z).2.val` 同时成立。
theorem seat_ends (p : S.Seating r G) (z : G.End) :
    ((seat k hk p).ends z).1 = span k hk (p.ends z).1 ∧
      ((seat k hk p).ends z).2.val = (p.ends z).2.val := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective z
  rw [Scheme.Seating.ends_at, Scheme.Seating.ends_at]
  exact ⟨rfl, rfl⟩

-- 读法：用字段 `toSeating`、`proper`、`internal`、`obtain` 构造 `(target S k).Presentation (rows k hk r) G`。
def presentation (p : S.Presentation r G) : (target S k).Presentation (rows k hk r) G where
  toSeating := seat k hk p.toSeating
  proper := proper k hk r p.proper
  internal i := by
    obtain ⟨h, hi⟩ := p.internal i
    obtain ⟨hl, he⟩ := seat_ends k hk p.toSeating (.inl (.inr i))
    obtain ⟨hr, hf⟩ := seat_ends k hk p.toSeating (.inr (.inr i))
    exact ⟨by rw [hl, hr, peer, h]; rfl, he.trans (hi.trans hf.symm)⟩
  input i := by rw [(seat_ends k hk p.toSeating _).1, peer, p.input]; rfl
  output i := by rw [(seat_ends k hk p.toSeating _).1, peer, p.output]; rfl

-- 读法：`((presentation k hk p).boundary z).val.1 = span k hk (p.boundary z).val.1` 与 `((presentation k hk p).boundary z).val.2.val = (p.boundary z).val.2.val` 同时成立。对 `z` 分类讨论。
theorem outer (p : S.Presentation r G) (z : slots x ⊕ slots y) :
    ((presentation k hk p).boundary z).val.1 = span k hk (p.boundary z).val.1 ∧
      ((presentation k hk p).boundary z).val.2.val = (p.boundary z).val.2.val := by
  cases z with
  | inl i => exact seat_ends k hk p.toSeating (.inl (.inl i))
  | inr i => exact seat_ends k hk p.toSeating (.inr (.inl i))

section
variable {T : Type} {L : Fringe x y T} {u : ℕ} {Q : HostNet F L S.h u}
    (p : S.Posting r Q) (hb : p.block = (cellIndex S.h).toEmbedding)

-- 读法：`host` 的取值由 `(p.host.prodMap (cellIndex k).toEmbedding).trans (Match.rowIndex S.m k).symm.toEmbedding` 给出。
def host : (Q.regroup k hk).V ↪ B (S.m + k) :=
  (p.host.prodMap (cellIndex k).toEmbedding).trans (Match.rowIndex S.m k).symm.toEmbedding

include hb in
-- 读法：`room k hk (p.host v, p.block c, 0)` 等于 `(host k hk p (v, ancestor hk c), cellIndex _ (suffix k c), 0)`。
private theorem place (v : Q.V) (c : Cell S.h) :
    room k hk (p.host v, p.block c, 0) =
      (host k hk p (v, ancestor hk c), cellIndex _ (suffix k c), 0) := by
  rw [hb]
  simp [room, blocks, host, splitCell]
  rfl

include hb in
-- 读法：`(target S k).spanAt (Q.regroup k hk) (host k hk p) (cellIndex _).toEmbedding p.stub i t` 等于 `span k hk (p.span i t)`。
private theorem spanAt (i : Q.E) (t : Bool) :
    (target S k).spanAt (Q.regroup k hk) (host k hk p) (cellIndex _).toEmbedding p.stub i t =
      span k hk (p.span i t) := by
  cases t <;> exact Prod.ext (place k hk p hb _ _).symm rfl

-- 读法：用字段 `toPresentation`、`host`、`block`、`stub` 构造 `(target S k).Posting (rows k hk r) (Q.regroup k hk)`。
def post : (target S k).Posting (rows k hk r) (Q.regroup k hk) where
  toPresentation := presentation k hk p.toPresentation
  host := host k hk p
  block := (cellIndex _).toEmbedding
  stub := p.stub
  index i j := p.index i.1 j.1
  vertex_eq v := by
    change room k hk (p.vertex v) = _
    rw [p.vertex_eq v]
    exact place k hk p hb _ _
  ordered i t j := by
    obtain ⟨hs, he⟩ := seat_ends k hk p.toSeating (Scheme.endBit Q i t j)
    obtain ⟨hp, hj⟩ := p.ordered i t j
    exact ⟨hs.trans ((congrArg (span k hk) hp).trans (spanAt k hk p hb i t).symm), he.trans hj⟩
  length i t := by rw [spanAt k hk p hb i t, width]; exact p.length i t
  dir i t := by rw [spanAt k hk p hb i t, direction]; exact p.dir i t
  link i t := by
    rw [spanAt k hk p hb i t]
    change ((target S k).pattern (rows k hk r) (room k hk (p.span i t).1)).peer
      (p.span i t).1.2.2 (p.span i t).2 = _
    rw [pattern]
    cases t
    · exact p.link i false
    · exact p.link i true

end

variable {h u d e : ℕ} {T : Type} {L : Fringe (copies x (2 ^ h * u)) (copies y (2 ^ h * u)) T}
    {z : ℕ} {Q : HostNet F L S.h z} (p : S.Posting r Q)
    (hb : p.block = (cellIndex S.h).toEmbedding)
    {name : Stack.Outer x y ↪ (Fin e → Bool)} {data : Trail.Record S h d e}

-- 读法：要证明的命题是 `Trail.Marked (post k hk p hb).toPresentation name (trail k hk data) (fun j => lane (Match.rowIndex S.m k j).1)`。
theorem marked {lane : B S.m → Stack.Outer x y → Fin d}
    (hp : Trail.Marked p.toPresentation name data lane) :
    Trail.Marked (post k hk p hb).toPresentation name (trail k hk data)
      (fun j => lane (Match.rowIndex S.m k j).1) := by
  intro i c
  obtain ⟨a, hw, hs, hl, he⟩ := hp i c
  have host_eq : (Match.rowIndex S.m k (span k hk a).1.1).1 = a.1.1 := by simp [span, room]
  refine ⟨span k hk a, (width k hk r a).trans hw, ?_, ?_, fun t => ?_⟩
  · simpa only [trail, Function.comp_apply, Equiv.symm_apply_apply, host_eq] using hs
  · simpa only [trail, host_eq] using hl
  · obtain ⟨h₁, h₂⟩ := outer k hk p.toPresentation (Stack.bit h u x y ((c, t), i))
    exact ⟨h₁.trans (congrArg (span k hk) (he t).1), h₂.trans (he t).2⟩

-- 读法：要证明的命题是 `Trail.Tracks (post k hk p hb).toPresentation name (trail k hk data)`。
theorem tracks (hp : Trail.Tracks p.toPresentation name data) :
    Trail.Tracks (post k hk p hb).toPresentation name (trail k hk data) :=
  ⟨_, marked k hk p hb hp.choose_spec⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
end

/-!
# 重新分组各块时传送标签的成本

**英文原文**

The cost of transferring labels when blocks are regrouped
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
open Assembly Coloring Packing

variable {F : Type} {S : Scheme F} (k : ℕ) (hk : k ≤ S.h) (h d e : ℕ)

-- 读法：在后续公式中，`tape` 是 `S.format.pair (Trail.format S h d e)` 的缩写。
abbrev tape (S : Scheme F) (h d e : ℕ) := S.format.pair (Trail.format S h d e)

-- 读法：`repack` 的取值由 `(rows k hk x.1, trail k hk x.2)` 给出。
def repack (x : (tape S h d e).obj) : (tape (target S k) h d e).obj :=
  (rows k hk x.1, trail k hk x.2)

local notation "A" => tape S h d e
local notation "D" => tape (target S k) h d e

-- 读法：`(∃ p : (A).pins, ∀ x, (D).code (repack k hk h d e x) q = (A).code x p)`、`(∃ b, ∀ x, (D).code (repack k hk h d e x) q = b)` 至少有一项成立。
private theorem wiring (q : (D).pins) :
    (∃ p : (A).pins, ∀ x, (D).code (repack k hk h d e x) q = (A).code x p) ∨
    (∃ b, ∀ x, (D).code (repack k hk h d e x) q = b) := by
  rcases q with ⟨i, ⟨j, l⟩ | ⟨j, l⟩⟩ | (⟨v, t⟩ | ⟨i, j, t⟩)
  · obtain ⟨s | s, hs⟩ := Match.append_pin S.m k l
    · left
      exact ⟨.inl ((Match.rowIndex S.m k i).1, .inl (j, s)), fun x => hs _ _⟩
    · right
      exact ⟨(Format.addr k).code (Match.rowIndex S.m k i).2 s, fun x => hs _ _⟩
  · left
    let a := Match.rowIndex S.m k i
    exact ⟨.inl (a.1, .inr ((blocks k hk).symm (a.2, j), l)), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inl ((span k hk).symm v, t)), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr ((Match.rowIndex S.m k i).1, j, t)), fun _ => rfl⟩

-- 读法：在 `F` 上按格式 `A`、`D` 编码输入输出，映射 `(repack k hk h d e)` 的电路规模至多为 `((A).width + 34 * (D).width)`。这里调用 `hd.bnet`。
theorem circuit [Field F] : Circuit F A D (repack k hk h d e) ((A).width + 34 * (D).width) := by
  classical
  have hd : Install.Depends ((D).code ∘ repack k hk h d e ∘ (A).code.symm) 1 := by
    intro q
    rcases wiring k hk h d e q with ⟨p, hp⟩ | ⟨b, hb⟩
    · refine ⟨{p}, by simp, fun x y he => ?_⟩
      simpa only [Function.comp_apply, hp, Equiv.apply_symm_apply] using he p (by simp)
    · exact ⟨∅, by simp, fun _ _ _ => (hb _).trans (hb _).symm⟩
  exact hd.bnet F

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup

namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (G : HostNet F L h u) (k : ℕ) (hk : k ≤ h)

-- 读法：要证明的命题是 `G.Preserves (G.regroup k hk)`。
theorem regroup_preserves : G.Preserves (G.regroup k hk) := by
  let f : Cell h →ₗ[ZMod 2] Cell (h - k) :=
    { toFun := suffix k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have onto : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := (splitCell k hk).surjective (0, j)
    exact ⟨i, congrArg Prod.snd hi⟩
  exact ⟨splitAddr G.V k hk, rfl, fun _ => rfl, ⟨f, onto, fun _ => rfl⟩,
    Cell k, inferInstance, Equiv.refl _, fun _ => rfl⟩

-- 读法：要证明的命题是 `G.Tracks (G.regroup k hk) 1`。这里调用 `tracks_of_slots`。
theorem regroup_tracks : G.Tracks (G.regroup k hk) 1 := by
  classical
  apply tracks_of_slots (H := 1) (K := 1) (Q := G.regroup k hk) (A := Cell k)
    (Equiv.refl _) (fun v => {v})
  · simp [eq_comm]
  · simp
  · decide
  · change Fintype.card (G.V × Cell k) ≤ _
    rw [Fintype.card_prod, card_cell, one_mul, show h - (h - k) = k by omega, mul_comm]
  · exact fun _ => Finset.mem_singleton_self _

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# 存放两种行顺序所需的空间

各次出现的元数以最细线束的宽度为单位。关联预算将每个核心线束计两次，每个外部线束计一次。

**英文原文**

Space for the two row orders

Occurrence arities use the width of a finest bundle as their unit.
The incidence budget counts each core bundle twice and each exterior
bundle once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
open Coloring Assembly PackRows Classical

variable {F : Type} [Field F] {D : Dimensions} {S : Scheme F} {x y : Wire} {G : Diagram F x y}
    (t : Assignment D S G)

-- 读法：`(∑ i, total (t.inventory i)) * D.z` 等于 `2 * t.state.X + (wd x + wd y) * D.copies`。
theorem inventory_total :
    (∑ i, total (t.inventory i)) * D.z = 2 * t.state.X + (wd x + wd y) * D.copies := by
  have he := Fintype.card_congr (Exterior.point t.loc t.lane D.b)
  simp only [Fintype.card_prod, Fintype.card_fin, Packing.card_cell, Fintype.card_sum,
    card_slots] at he
  unfold Endpoints Slots Blocks at he
  simp_rw [Fintype.card_sigma, Fintype.card_fin] at he
  have hc := t.inner.total_eq
  change (wd x + wd y) * 2 ^ D.h * D.b = ∑ i, total (t.outerCount i) at he
  have sum (i) : total (t.inventory i) = total (t.inner.inventory i) + total (t.outerCount i) := by
    simp [inventory, PackRows.total, Finset.sum_add_distrib]
  simp_rw [sum]
  rw [Finset.sum_add_distrib, hc, ← he]
  unfold Packing.HostNet.X Dimensions.copies
  ring

-- 读法：要证明的命题是 `Pieces.Room (l := t.inventory) (u := D.u)`。按 `∃ a b, t.post.host a = i ∧ t.post.block b = j` 成立与否分情况。
theorem room (hl : ∀ i j, t.state.load i j ≤ (D.u * D.z : ℕ)) :
    Pieces.Room (l := t.inventory) (u := D.u) := by
  intro i j
  rw [inventory, arity_append]
  by_cases h : ∃ a b, t.post.host a = i ∧ t.post.block b = j
  · obtain ⟨a, b, rfl, rfl⟩ := h
    rw [t.post.channels_arity]
    have hc := t.state.core_le_load a b
    have he := t.holders.load_eq t.post.host t.post.block t.lane rfl a b
    have hb := hl a b
    apply Nat.le_of_mul_le_mul_right _ D.zpos
    exact_mod_cast (show ((Packing.degree t.state.pair (a, b) : ℝ) +
      arity (t.outerCount (t.post.host a)) (t.post.block b)) * D.z ≤ (D.u * D.z : ℕ) by
        rw [add_mul, he, add_comm]
        exact hc.trans hb)
  · have hc (e : t.state.E) (d : Bool) : ¬(t.inner.host d e = i ∧ t.inner.block e = j) :=
      fun he => h ⟨_, _, he⟩
    have he (a : Stack.Outer x y × Packing.Cell D.h) : t.loc a.1 a.2 ≠ (i, j) :=
      fun he => h ⟨_, _, Prod.mk.inj he⟩
    rw [Channels.arity_eq, Exterior.arity]
    simp [hc, he]

-- 读法：要证明的命题是 `t.Fits`。这里调用 `Finset.sum_le_sum`。
theorem fits (hl : ∀ i j, t.state.load i j ≤ (D.u * D.z : ℕ))
    (hv : D.PortCount S + 2 + 2 * 2 ^ S.h ≤ D.v)
    (hr : 2 ^ S.m * ((D.PortCount S + 2) * D.u) * D.z + 2 * (2 * t.state.X + (wd x + wd y) * D.copies)
          + D.v * D.u * D.z ≤ D.K * D.v * D.u * D.z) : t.Fits := by
  have hm := t.room hl
  refine ⟨hm, fun i => ?_, ?_⟩
  · have ht : total (t.inventory i) ≤ 2 ^ S.h * D.u := by
      unfold PackRows.total
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hm i j)
    apply Nat.le_of_mul_le_mul_right _ D.upos
    calc
      _ ≤ (D.PortCount S + 2) * D.u + 2 * total (t.inventory i) := size_cost _ _
      _ ≤ (D.PortCount S + 2 + 2 * 2 ^ S.h) * D.u := by grw [ht]; exact le_of_eq (by ring)
      _ ≤ _ := Nat.mul_le_mul_right _ hv
  · apply Nat.le_of_mul_le_mul_right _ (by positivity : 0 < D.v)
    apply Nat.le_of_mul_le_mul_right _ D.upos
    apply Nat.le_of_mul_le_mul_right _ D.zpos
    refine (Nat.mul_le_mul_right _ (bins_cost t.inventory D.u D.v)).trans ?_
    rw [add_mul, add_mul, mul_assoc 2, t.inventory_total]
    exact hr

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
end

/-!
# 批量下降的固定数据与可变控制信息

**英文原文**

Fixed data and varying controls of a batch descent
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Assembly Coloring Packing
open scoped Classical

-- 读法：结构的字段包括 `G`、`h`、`U`、`z`、`d`。
structure Setup (F : Type) (x y : Wire) where
  G : Diagram F x y
  h : ℕ
  U : ℕ
  z : ℕ
  d : ℕ
  e : ℕ
  name : Stack.Outer x y ↪ (Fin e → Bool)
  cap : ℕ
  discount : ℕ

namespace Setup
variable {F : Type} {x y : Wire} (S : Setup F x y)

-- 读法：在后续公式中，`count` 是 `2 ^ S.h * S.U` 的缩写。
abbrev count := 2 ^ S.h * S.U
-- 读法：在后续公式中，`input` 是 `copies x S.count` 的缩写。
abbrev input := copies x S.count
-- 读法：在后续公式中，`output` 是 `copies y S.count` 的缩写。
abbrev output := copies y S.count
-- 读法：在后续公式中，`fringe` 是 `{ Stack.fringe S.input S.output with cap := S.cap, discount := S.discount }` 的缩写。
abbrev fringe := { Stack.fringe S.input S.output with cap := S.cap, discount := S.discount }
-- 读法：在后续公式中，`first` 是 `(Stack.start S.G S.h S.U).reserve S.cap S.discount` 的缩写。
abbrev first [Field F] := (Stack.start S.G S.h S.U).reserve S.cap S.discount
-- 读法：在后续公式中，`format` 是 `T.format.pair (Trail.format T.scheme S.h S.d S.e)` 的缩写。
abbrev format (T : Template F) := T.format.pair (Trail.format T.scheme S.h S.d S.e)
end Setup

namespace Snapshot
variable {F : Type} [Field F] {x y : Wire} (S : Setup F x y) (T : Template F) (u : ℕ)

-- 读法：结构的字段包括 `G`、`rows`、`trail`、`encodes`、`tracks`。
structure Data where
  G : HostNet F S.fringe T.scheme.h u
  rows : T.format.obj
  trail : Trail.Record T.scheme S.h S.d S.e
  encodes : T.Encodes rows G
  tracks : Trail.Tracks encodes.post.toPresentation S.name trail
  preserved : S.first.Preserves G

variable {S T u}

-- 读法：`Data.code` 的取值由 `(x.rows, x.trail)` 给出。
def Data.code (x : Data S T u) : (S.format T).obj := (x.rows, x.trail)

-- 读法：`Data.Neutral` 表示以下条件：对每个 `v`，由 `x.G.diagram.arity v = 0` 推出 `∀ t, Transcript.sample (x.G.diagram.table v) t = 1`。
def Data.Neutral (x : Data S T u) : Prop :=
  ∀ v, x.G.diagram.arity v = 0 → ∀ t, Transcript.sample (x.G.diagram.table v) t = 1

-- 读法：`Data.Tagged` 的结果类型为 `Prop`。
def Data.Tagged (x : Data S T u) (cost : ℕ) : Prop :=
  ∀ v b, 0 < x.G.tetherLoad (v, b) + degree x.G.pair (v, b) * u →
    T.tagLength x.rows (x.encodes.post.host v) (x.encodes.post.block b) * S.z ≤
      cost * (x.G.past (v, b) + x.G.tetherLoad (v, b) + degree x.G.pair (v, b) * u)

-- 读法：用字段 `state`、`eval`、`port`、`encode` 构造 `Assembly.Snapshot.{1} F S.input S.output`。
def restrict (P : Data S T u → Prop) : Assembly.Snapshot.{1} F S.input S.output where
  state := {x // P x}
  eval q := q.val.G.diagram.eval
  port := S.format T
  encode q _ _ := q.val.code

end Snapshot
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# 在终端预算中分别核算短记录与长记录

在每个宿主的每个块上计入短记录。邻点地址和外部长名称在每个宿主只计一次。

**英文原文**

Separating short and long records in the terminal budget

Charge the short record at each block of each host. Charge the neighbor
addresses and long exterior names just once at each host.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
open Assembly Coloring

variable {F : Type} {x y : Wire} {S : Setup F x y} {T : Template F} {N : Scheme F}
    {A L w : ℕ}

-- 读法：`N.ℓ + c + 2 ^ N.e * (S.d + S.h)` 不超过 `100 * A ^ 3`。
private theorem short_bound {c : ℕ} (hA : 2 ≤ A) (hd : S.d ≤ A) (hh : S.h ≤ A)
    (ht : N.ℓ ≤ A) (he : 2 ^ N.e ≤ A) (hc : c ≤ A) :
    N.ℓ + c + 2 ^ N.e * (S.d + S.h) ≤ 100 * A ^ 3 := by
  calc
    _ ≤ A + A + A * (A + A) := by gcongr
    _ ≤ 100 * A ^ 3 := by nlinarith [Nat.mul_le_mul_right (A ^ 2) hA]

-- 读法：`2 ^ N.d * (N.m + 2) + 2 + S.d * S.e` 不超过 `100 * L * w`。
private theorem long_bound (hL : 2 ≤ L) (hw : 1 ≤ w) (hm : N.m ≤ 3 * w) (he : S.e ≤ 3 * w)
    (hf : 2 ^ N.d ≤ L) (hd : S.d ≤ L) :
    2 ^ N.d * (N.m + 2) + 2 + S.d * S.e ≤ 100 * L * w := by
  calc
    _ ≤ L * (3 * w + 2) + 2 + L * (3 * w) := by gcongr
    _ ≤ _ := by nlinarith

-- 读法：`(S.format T).width` 不超过 `100 * A ^ 3 * 2 ^ (T.scheme.m + T.scheme.h) + 100 * L * 2 ^ T.scheme.m * w`。
theorem format_bound (hL : 2 ≤ L) (ha : L ≤ A) (hw : 1 ≤ w)
    (hk : T.scheme.k = 0) (hm : T.scheme.m ≤ 3 * w) (he : S.e ≤ 3 * w)
    (hf : 2 ^ T.scheme.d ≤ L) (hd : S.d ≤ L) (hh : S.h ≤ A) (ht : T.scheme.ℓ ≤ A)
    (hp : 2 ^ T.scheme.e ≤ A) (hc : T.count ≤ A) :
    (S.format T).width ≤ 100 * A ^ 3 * 2 ^ (T.scheme.m + T.scheme.h) + 100 * L * 2 ^ T.scheme.m * w := by
  have small := short_bound (hL.trans ha) (hd.trans ha) hh ht hp hc
  have large := long_bound hL hw hm he hf hd
  calc
    _ = (T.scheme.ℓ + T.count + 2 ^ T.scheme.e * (S.d + S.h)) * 2 ^ (T.scheme.m + T.scheme.h) +
        (2 ^ T.scheme.d * (T.scheme.m + 2) + 2 + S.d * S.e) * 2 ^ T.scheme.m := by
      rw [Format.width_pair, Template.width, Trail.width_format, Trail.width_row, hk,
        add_zero, pow_add, pow_add]
      ring
    _ ≤ 100 * A ^ 3 * 2 ^ (T.scheme.m + T.scheme.h) + (100 * L * w) * 2 ^ T.scheme.m :=
      Nat.add_le_add (Nat.mul_le_mul_right _ small) (Nat.mul_le_mul_right _ large)
    _ = _ := by ring

-- 读法：`(tape N S.h S.d S.e).width` 不超过 `100 * A ^ 3 * 2 ^ (N.m + N.h) + 100 * L * 2 ^ N.m * w`。
theorem tape_bound (hL : 2 ≤ L) (ha : L ≤ A) (hw : 1 ≤ w) (hk : N.k = 0)
    (hm : N.m ≤ 3 * w) (he : S.e ≤ 3 * w) (hf : 2 ^ N.d ≤ L) (hd : S.d ≤ L)
    (hh : S.h ≤ A) (ht : N.ℓ ≤ A) (hp : 2 ^ N.e ≤ A) :
    (tape N S.h S.d S.e).width ≤ 100 * A ^ 3 * 2 ^ (N.m + N.h) + 100 * L * 2 ^ N.m * w := by
  have small := short_bound (hL.trans ha) (hd.trans ha) hh ht hp (Nat.zero_le A)
  have large : 2 ^ N.d * N.m + S.d * S.e ≤ 100 * L * w :=
    le_trans (by rw [mul_add]; omega) (long_bound hL hw hm he hf hd)
  calc
    _ = (N.ℓ + 2 ^ N.e * (S.d + S.h)) * 2 ^ (N.m + N.h) + (2 ^ N.d * N.m + S.d * S.e) * 2 ^ N.m := by
      rw [Format.width_pair, Fmt.width_rows, Format.width_addr, Trail.width_format,
        Trail.width_row, hk, add_zero, pow_add, pow_add]
      ring
    _ ≤ 100 * A ^ 3 * 2 ^ (N.m + N.h) + (100 * L * w) * 2 ^ N.m :=
      Nat.add_le_add (Nat.mul_le_mul_right _ small) (Nat.mul_le_mul_right _ large)
    _ = _ := by ring

-- 读法：`Fintype.card (Trail.Meta N S.h S.d)` 不超过 `100 * A ^ 3 * 2 ^ N.h`。这里调用 `Nat.mul_le_mul_right`。
theorem meta_bound (hA : 2 ≤ A) (hk : N.k = 0) (hd : S.d ≤ A) (hh : S.h ≤ A)
    (ht : N.ℓ ≤ A) (hp : 2 ^ N.e ≤ A) :
    Fintype.card (Trail.Meta N S.h S.d) ≤ 100 * A ^ 3 * 2 ^ N.h := by
  rw [Trail.card_meta, hk, zero_add, mul_comm]
  exact Nat.mul_le_mul_right _ (short_bound hA hd hh ht hp (Nat.zero_le A))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
end

/-!
# 取出孤立的标量项

记录带保留原有的标签和追踪标记。每个空站点的旧值成为这次转移的一个系数。

**英文原文**

Withdrawing isolated scalar entries

The same labels and trail markers remain on the tape. Every empty
station's old value becomes a coefficient of the transition.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

namespace BatchDescent.Snapshot
variable {S : Setup F x y} {T : Template F} {u : ℕ} (d : Data S T u)

-- 读法：`recode` 的取值由 `⟨t.short, t.long⟩` 给出。
def recode (t : Trail.Record T.scheme S.h S.d S.e) : Trail.Record T.sweep.scheme S.h S.d S.e :=
  ⟨t.short, t.long⟩

-- 读法：用字段 `G`、`rows`、`trail`、`encodes` 构造 `Data S T.sweep u`。
def Data.sweep : Data S T.sweep u where
  G := d.G.sweep
  rows := d.rows
  trail := recode d.trail
  encodes := d.encodes.sweep
  tracks := d.tracks
  preserved := d.preserved

-- 读法：要证明的命题是 `d.sweep.Neutral`。使用 `d.G.diagram.sweep_neutral` 给出的结论。
theorem Data.sweep_neutral : d.sweep.Neutral := d.G.diagram.sweep_neutral

-- 读法：`d.sweep.Tagged n` 与 `d.Tagged n` 等价。使用 `Iff.rfl` 给出的结论。
theorem Data.sweep_tagged (n : ℕ) : d.sweep.Tagged n ↔ d.Tagged n := Iff.rfl

-- 读法：`sweepTable` 的取值由 `weightTable (A := .addr T.scheme.ℓ) (D := .addr T.scheme.ℓ) id T.scheme.scalar` 给出。
def sweepTable (T : Template F) := weightTable (A := .addr T.scheme.ℓ) (D := .addr T.scheme.ℓ)
  id T.scheme.scalar

-- 读法：`sweepCost` 的构造用到 `T.scheme.m`、`T.scheme.d`、`T.scheme.h`。
def sweepCost (S : Setup F x y) (T : Template F) :=
  updateCost T.scheme.m T.scheme.d T.scheme.h (.addr T.scheme.ℓ) (.addr T.scheme.ℓ) +
  4 * (Format.vec T.scheme.m T.header).width + 4 * (Trail.format T.scheme S.h S.d S.e).width

-- 读法：要证明的命题是 `Transforms F cap L (restrict P) (restrict Q) (sweepCost S T)`。
theorem sweep {P : Data S T u → Prop} {Q : Data S T.sweep u → Prop}
    (h : ∀ d, P d → Q d.sweep) {cap : ℕ} {L : Set (Table F)} (hu : 3 ≤ cap)
    (ha : 2 * T.scheme.ℓ ≤ cap) (hl : sweepTable T ∈ L) :
    Transforms F cap L (restrict P) (restrict Q) (sweepCost S T) := by
  let A := Format.addr T.scheme.ℓ
  have update := Assembly.update (m := T.scheme.m) (d := T.scheme.d) (h := T.scheme.h)
    (A := A) (D := A) id T.scheme.scalar hu (by simpa [A, two_mul] using ha) hl
  have header := Map.circuit (L := L) hu (Circuit.id F (.vec T.scheme.m T.header))
  let left := Trail.format T.scheme S.h S.d S.e
  let right := Trail.format T.sweep.scheme S.h S.d S.e
  have trail : Circuit F left right (recode (S := S) (T := T)) left.width := by
    unfold Circuit
    convert Install.BNet.id F left.pins using 1
    funext k i
    rcases i with i | i <;> rfl
  -- 推导：记下中间结论 `k`：`= (update.par (Action.of_map header)).par (Action.of_map (Map.circuit (L`。
  have k := (update.par (Action.of_map header)).par (Action.of_map (Map.circuit (L := L) hu trail))
  simp only [mul_one] at k
  refine Transforms.of_action (X := restrict P) (Y := restrict Q)
    (fun i => ⟨i.val.sweep, h i.val i.property⟩)
    (fun i => Fmt.weight T.scheme.scalar i.val.rows.1) _ _ k ?_ ?_ ?_
  · exact fun i a b => i.val.encodes.post.toPresentation.sweep_eval a b
  · exact fun _ _ _ => rfl
  · exact fun _ _ _ => rfl

end BatchDescent.Snapshot
end OAI.LinearAlgebra.MatrixExponent
end

section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Snapshot.Data
open Assembly
variable {F : Type} [Field F] {x y : Wire} {S : Setup F x y} {T : Template F} {u : ℕ}
    (q : Data S T u)

-- 读法：`T.scheme.width q.rows.1 p` 等于 `S.U`。
/-- 每个正长度外部区段携带一个完整的原始栈。

英文原文：Every positive exterior span carries a whole original stack.
-/
theorem exterior_width (p : T.scheme.Span) (he : T.scheme.peer q.rows.1 p = none)
    (hw : 0 < T.scheme.width q.rows.1 p) : T.scheme.width q.rows.1 p = S.U := by
  let a : T.scheme.exposed q.rows.1 := ⟨⟨p, ⟨0, hw⟩⟩, he⟩
  obtain ⟨i, hi⟩ := q.encodes.post.toPresentation.boundary.surjective a
  obtain ⟨⟨⟨s, t⟩, b⟩, rfl⟩ := (Stack.bit S.h S.U x y).surjective i
  obtain ⟨_, hl⟩ := q.tracks
  obtain ⟨w, hz, _, _, hs⟩ := hl b s
  have h : w = p := (hs t).1.symm.trans (congrArg (fun j => j.val.1) hi)
  rwa [← h]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Snapshot.Data
end

section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

-- 读法：在后续公式中，`Dimensions.setup` 是 `⟨G, D.h, D.b * D.z, D.z, D.d, D.e, name, cap, discount⟩` 的缩写。
/-- 用终端打包中采用的宽度与复制参数初始化下降过程。

英文原文：Initialize the descent from the width and replication parameters
used in the terminal packing.
-/
abbrev Dimensions.setup {F : Type} {x y : Wire} (D : Dimensions) (G : Diagram F x y)
    (name : Stack.Outer x y ↪ (Fin D.e → Bool)) (cap discount : ℕ) : Setup F x y :=
  ⟨G, D.h, D.b * D.z, D.z, D.d, D.e, name, cap, discount⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# 计入历史余量时保持外部来源不变

**英文原文**

The history allowance leaves exterior origins unchanged
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Coloring Packing Classical

variable {F : Type} [Field F] {x y : Wire}

-- 读法：用字段 `toPresentation`、`host`、`block`、`stub` 构造 `S.Posting r (Q.reserve 0 0)`。
def Regroup.unreserve {A : Type} {f : Fringe x y A} {h z : ℕ} {Q : HostNet F f h z}
    {S : Scheme F} {r : S.format.obj} (p : S.Posting r Q) :
    S.Posting r (Q.reserve 0 0) where
  toPresentation := p.toPresentation
  host := p.host
  block := p.block
  stub := p.stub
  index := p.index
  vertex_eq := p.vertex_eq
  ordered := p.ordered
  length := p.length
  dir := p.dir
  link := p.link

-- 读法：`(Trail.origins p.toPresentation v).card` 不超过 `3 * k`。按 `Nonempty S.G.V` 成立与否分情况。
theorem Setup.origins (S : Setup F x y) {a u : ℕ} (H : HostNet F S.fringe a u)
    {T : Scheme F} {r : T.format.obj} (p : T.Posting r H) {k : ℕ}
    (hp : S.first.Preserves H) (hk : S.first.Tracks H k) (hu : 0 < S.U) (ht : S.G.Trivalent)
    (v : B T.m) : (Trail.origins p.toPresentation v).card ≤ 3 * k := by
  by_cases hn : Nonempty S.G.V
  · let Q : HostNet F (Stack.fringe S.input S.output) a u := H.reserve 0 0
    let G := Stack.start S.G S.h S.U
    have h : 0 < G.seats := by
      rw [Stack.start_seats]
      have := Fintype.card_pos_iff.mpr hn
      positivity
    obtain ⟨L⟩ := Stack.holders S.G Q hu hp (Nat.le_mul_of_pos_right Q.seats h)
    exact Trail.origins_bound (Regroup.unreserve p) L hu ht hk v
  · have he : Trail.origins p.toPresentation v = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun i _ => hn ⟨portEnd S.G i⟩
    rw [he, Finset.card_empty]
    omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# 最后一个节拍后的终端赋值

去掉关联历史预算，将备用块索引位移到宿主坐标。这一步向终端视图传递短记录和外部名称，保留图式的全部表项。

**英文原文**

The terminal assignment after the final beat

Drop the incidence-history budget and move spare block bits to the host
coordinate. This step sends the short records and exterior names to the
terminal view. It leaves all diagram entries unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

variable {D : Dimensions} {G : Diagram F x y} {name : Stack.Outer x y ↪ (Fin D.e → Bool)}
    {cap discount K k u : ℕ} {T : Template F}

local notation "s" => D.setup G name cap discount
local notation "U" => target T.scheme k

-- 读法：结论为 `∃ t : Assignment D U G, t.state.X = d.G.X ∧ (∀ B : ℝ, (∀ i j, d.G.load i j ≤ B) → ∀ i j, t.state.load i j ≤ B) ∧ d.G.diagram.eval = t.state.diagram.eval ∧ ∀ hw, (Trail.view D U name).Valid t hw (rows k hk d.rows.1, trail k hk d.trail)`。
private theorem assignment (hn : Nonempty G.V) (hk : k ≤ T.scheme.h) (ht : T.scheme.h ≤ D.h)
    (d : Snapshot.Data s T D.z) (hq : K * D.q ≤ 2 ^ (T.scheme.h - k))
    (hc : (s).first.Tracks d.G K) :
    ∃ t : Assignment D U G, t.state.X = d.G.X ∧
      (∀ B : ℝ, (∀ i j, d.G.load i j ≤ B) → ∀ i j, t.state.load i j ≤ B) ∧
      d.G.diagram.eval = t.state.diagram.eval ∧
      ∀ hw, (Trail.view D U name).Valid t hw (rows k hk d.rows.1, trail k hk d.trail) := by
  let R := d.G.regroup k hk
  let Q : HostNet F (Stack.fringe (copies x D.copies) (copies y D.copies)) (T.scheme.h - k) D.z :=
    R.reserve 0 0
  let H := Stack.start G D.h (D.b * D.z)
  have hpre : H.Preserves Q := d.preserved.trans (d.G.regroup_preserves k hk)
  have htracks : H.Tracks Q K := by
    have ht' := hc.trans (d.G.regroup_tracks k hk) ht (Nat.sub_le _ _)
    rw [one_mul] at ht'
    exact ht'
  -- 推导：记下中间结论 `hpos`：`0 < H.seats`。
  have hpos : 0 < H.seats := by
    rw [Stack.start_seats]
    have := Fintype.card_pos_iff.mpr hn
    positivity
  have hseats := Nat.le_mul_of_pos_right Q.seats hpos
  have hp := Nat.mul_pos D.bpos D.zpos
  obtain ⟨L⟩ := Stack.holders G Q hp hpre hseats
  have reach (i) : (Finset.univ.image (L.core i)).card * D.q ≤ 2 ^ D.h := calc
    _ ≤ (K * 2 ^ (D.h - (T.scheme.h - k))) * D.q := Nat.mul_le_mul_right _ (L.reach hp htracks i)
    _ = (K * D.q) * 2 ^ (D.h - (T.scheme.h - k)) := by ring
    _ ≤ 2 ^ (T.scheme.h - k) * 2 ^ (D.h - (T.scheme.h - k)) := Nat.mul_le_mul_right _ hq
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  -- 推导：记下中间结论 `hb`：`d.encodes.post.block = (cellIndex T.scheme.h).toEmbedding`。
  have hb : d.encodes.post.block = (cellIndex T.scheme.h).toEmbedding :=
    DFunLike.ext _ _ d.encodes.block
  let q : (U).Posting (rows k hk d.rows.1) Q := unreserve (post k hk d.encodes.post hb)
  have marked' : Trail.Tracks q.toPresentation name (trail k hk d.trail) :=
    tracks k hk d.encodes.post hb d.tracks
  obtain ⟨lane, hl⟩ := marked'
  let t := Trail.Marked.assign (D := D) (p := q) hl L reach
  refine ⟨t, rfl, ?_, rfl, fun hw => Trail.view_valid t hw name (trail k hk d.trail) hl⟩
  intro B hB i j
  change Q.V at i
  change Cell (T.scheme.h - k) at j
  -- 推导：记下中间结论 `hu`：`Q.load i j ≤ R.load i j`。
  have hu : Q.load i j ≤ R.load i j := by
    rw [HostNet.load, HostNet.unpaid _ rfl, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg R.rate_nonneg (Nat.cast_nonneg _))
  obtain ⟨p, he⟩ := (splitAddr d.G.V k hk).surjective (i, j)
  have hh := d.G.regroup_load k hk p
  rw [he] at hh
  exact hu.trans (hh.le.trans (hB ..))

local notation "src" => Setup.format s T
local notation "mid" => tape T.scheme D.h D.d D.e
local notation "dst" => tape U D.h D.d D.e

-- 读法：这里调用 `Nat.add_le_add_right`。
theorem terminal (hn : Nonempty G.V) (hk : k ≤ T.scheme.h) (ht : T.scheme.h ≤ D.h)
    (P : Snapshot.Data s T D.z → Prop) (hq : K * D.q ≤ 2 ^ (T.scheme.h - k))
    (bounds : ∀ d, P d → (s).first.Tracks d.G K)
    (hu : 3 ≤ u) (L : Set (Table F)) :
    ∃ (Y : Assembly.Snapshot.{1} F (s).input (s).output)
      (V : View D U x y Y.port (Trail.Meta U D.h D.d)),
      Y.port.width = (dst).width ∧
      Transforms F u L (Snapshot.restrict P) Y (1000 * ((src).width + Y.port.width)) ∧
      ∀ i a b, ∃ (d : Snapshot.Data s T D.z) (t : Assignment D U G),
        P d ∧ t.state.X = d.G.X ∧
        (∀ B : ℝ, (∀ i j, d.G.load i j ≤ B) → ∀ i j, t.state.load i j ≤ B) ∧
        Y.eval i a b = t.state.diagram.eval a b ∧ ∀ hw, V.Valid t hw (Y.encode i a b) := by
  -- 推导：记下中间结论 `drop`：`(src).obj → (mid).obj`。
  let drop : (src).obj → (mid).obj := fun x => (x.1.1, x.2)
  have drop_net : Circuit F src mid drop ((src).width + 2 * (mid).width) :=
    Circuit.project (A := src) (D := mid) (Sum.map Sum.inl id) (by rintro _ (i|i) <;> rfl)
  have small : (mid).width ≤ (src).width := by
    rw [Format.width_pair, Format.width_pair, Format.width_pair]
    exact Nat.add_le_add_right (Nat.le_add_right _ _) _
  let f := repack k hk D.h D.d D.e ∘ drop
  have cost := Map.circuit (L := L) hu (drop_net.comp (circuit k hk D.h D.d D.e))
  have ctrl : Map F u L src dst f (1000 * ((src).width + (dst).width)) := cost.mono (by omega)
  let X := Snapshot.restrict P
  let Y : Assembly.Snapshot.{1} F (s).input (s).output :=
    { X with port := dst, encode := fun i a b => f (X.encode i a b) }
  refine ⟨Y, Trail.view D U name, rfl, Transforms.of_map f id ctrl (fun _ => rfl)
    (fun _ _ _ => rfl), ?_⟩
  rintro ⟨d, hd⟩ a b
  -- 推导：从 `assignment hn hk ht d hq (bounds d hd)` 中取出 `t, hx, hl, he, hv`。
  obtain ⟨t, hx, hl, he, hv⟩ := assignment hn hk ht d hq (bounds d hd)
  exact ⟨d, t, hd, hx, hl, congrFun (congrFun he a) b, hv⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Regroup
end
