-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress

/-!
# 用短记录表示图式

局部端口双射可能改变表中参数的次序。解码选项表中的相应表按新次序读取参数。只要求规范化后的区段在两端对齐。

**英文原文**

Representing a diagram by short records

A local port bijection may change the order of the arguments of a
table. The table in the decoding menu reads the reordered arguments.
Only the normalized spans are required to align at both ends.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (S : Scheme F) (r : S.format.obj) (G : Diagram F x y)

-- 读法：结构的字段包括 `vertex`、`pin`、`cover`、`sample`、`vacant`。
structure Seating where
  vertex : G.V ↪ S.Vtx
  pin : ∀ v, G.Port v ≃ S.LocalPin r (vertex v)
  cover : ∀ p : S.Pin r, ∃ v, vertex v = p.1.1
  sample : ∀ v t, S.table r (vertex v) t = Transcript.sample (G.table v) (t ∘ pin v)
  vacant : ∀ v ∉ Set.range vertex, ∀ t, S.table r v t = 1

variable {S r G}

namespace Seating
variable (a : S.Seating r G)

-- 读法：`atPin` 的取值由 `S.port r (a.vertex i.1) (a.pin i.1 i.2)` 给出。
def atPin (i : Σ v, G.Port v) := S.port r (a.vertex i.1) (a.pin i.1 i.2)

-- 读法：`a.atPin` 是双射。
theorem atPin_bijective : Function.Bijective a.atPin := by
  constructor
  · rintro ⟨v, i⟩ ⟨w, j⟩ h
    have h' : v = w := a.vertex.injective (congrArg (fun p => p.1.1) h)
    subst w
    have hs : (a.pin v i).1 = (a.pin v j).1 := congrArg (fun p => p.1.2) h
    have hn : (a.pin v i).2.val = (a.pin v j).2.val := congrArg (fun p => p.2.val) h
    have ht : a.pin v i = a.pin v j :=
      Sigma.ext hs ((Fin.heq_ext_iff (congrArg (fun z => S.width r (a.vertex v, z)) hs)).mpr hn)
    rw [(a.pin v).injective ht]
  · rintro ⟨⟨v, j⟩, i⟩
    obtain ⟨u, hu⟩ := a.cover ⟨(v, j), i⟩
    change a.vertex u = v at hu
    subst v
    refine ⟨⟨u, (a.pin u).symm ⟨j, i⟩⟩, ?_⟩
    simp only [atPin, Equiv.apply_symm_apply]
    rfl

-- 读法：`ends` 的取值由 `G.portEquiv.symm.trans (Equiv.ofBijective a.atPin a.atPin_bijective)` 给出。
def ends : G.End ≃ S.Pin r := G.portEquiv.symm.trans (Equiv.ofBijective a.atPin a.atPin_bijective)

-- 读法：`a.ends (G.portEquiv ⟨v, p⟩)` 等于 `S.port r (a.vertex v) (a.pin v p)`。
theorem ends_at (v : G.V) (p : G.Port v) :
    a.ends (G.portEquiv ⟨v, p⟩) = S.port r (a.vertex v) (a.pin v p) := by
  simp [ends, atPin]

end Seating

variable (S r G)

-- 读法：结构的字段包括 `proper`、`internal`、`input`、`output`。
structure Presentation extends Seating S r G where
  proper : S.Proper r
  internal : ∀ e : G.E, S.Joins r (toSeating.ends (.inl (.inr e))) (toSeating.ends (.inr (.inr e)))
  input : ∀ i : slots x, S.peer r (toSeating.ends (.inl (.inl i))).1 = none
  output : ∀ i : slots y, S.peer r (toSeating.ends (.inr (.inl i))).1 = none

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# 求有序区段表示的值

每组内部赋值都唯一延拓为对全部引脚的赋值。证明也覆盖自环和空站点，且无须除以可能的编码数。

**英文原文**

Evaluating an ordered-span presentation

The extension of each internal assignment to all the pins is unique.
The proof includes loops and empty stations and does not divide by
the number of possible encodings.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {a b c : S.Pin r}

-- 读法：要证明的命题是 `S.Joins r b a`。
theorem Joins.symm (h : S.Joins r a b) (p : S.Proper r) : S.Joins r b a :=
  ⟨(p _ _ h.1).1, h.2.symm⟩

-- 读法：`b` 等于 `c`。这里调用 `Sigma.ext`。
theorem Joins.unique (h : S.Joins r a b) (k : S.Joins r a c) : b = c := by
  have he := Option.some.inj (h.1.symm.trans k.1)
  exact Sigma.ext he ((Fin.heq_ext_iff (congrArg (S.width r) he)).mpr (h.2.symm.trans k.2))

namespace Presentation
variable [Field F] {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)
  (u : Val x) (v : Val y)

-- 读法：`read` 的取值由 `Sum.elim (Sum.elim (bits x u) z) (Sum.elim (bits y v) z) ∘ p.toSeating.ends.symm` 给出。
def read (z : G.E → Bool) : S.Pin r → Bool :=
  Sum.elim (Sum.elim (bits x u) z) (Sum.elim (bits y v) z) ∘ p.toSeating.ends.symm

-- 读法：`p.read u v z (p.toSeating.ends t)` 等于 `Sum.elim (Sum.elim (bits x u) z) (Sum.elim (bits y v) z) t`。
theorem read_end (z : G.E → Bool) (t : G.End) :
    p.read u v z (p.toSeating.ends t) = Sum.elim (Sum.elim (bits x u) z) (Sum.elim (bits y v) z) t := by
  simp only [read, Function.comp_apply, Equiv.symm_apply_apply]

-- 读法：`exterior` 的取值由 `p.read u v (fun _ => false) q.val` 给出。
def exterior (q : S.exposed r) := p.read u v (fun _ => false) q.val

-- 读法：要证明的命题是 `S.Agrees r (p.exterior u v) (p.read u v z)`。
theorem read_agrees (z : G.E → Bool) : S.Agrees r (p.exterior u v) (p.read u v z) := by
  constructor
  · rintro ⟨q, h⟩
    obtain ⟨t, rfl⟩ := p.toSeating.ends.surjective q
    change p.read u v z (p.toSeating.ends t) = p.read u v _ (p.toSeating.ends t)
    rw [read_end, read_end]
    rcases t with (i|e)|(i|e)
    · rfl
    · rw [(p.internal e).1] at h
      contradiction
    · rfl
    · rw [((p.internal e).symm p.proper).1] at h
      contradiction
  · intro q t h
    -- 推导：从 `p.toSeating.ends.surjective q` 中取出 `i, rfl`。
    obtain ⟨i, rfl⟩ := p.toSeating.ends.surjective q
    rcases i with (i|e)|(i|e)
    · exact (by simpa [p.input i] using h.1 : False).elim
    · rw [h.unique (p.internal e), read_end, read_end]
      rfl
    · exact (by simpa [p.output i] using h.1 : False).elim
    · rw [h.unique ((p.internal e).symm p.proper), read_end, read_end]
      rfl

-- 读法：`(p.read u v)` 是单射。用函数外延性比较等号两侧在 `e` 处的取值。
theorem read_injective : Function.Injective (p.read u v) := by
  intro z w h
  funext e
  have he := congrFun h (p.toSeating.ends (.inl (.inr e)))
  simpa only [read_end, Sum.elim_inl, Sum.elim_inr] using he

-- 读法：存在 `z`，`p.read u v z` 等于 `w`。
theorem read_surjective (w : S.Pin r → Bool) (hw : S.Agrees r (p.exterior u v) w) :
    ∃ z, p.read u v z = w := by
  let z e := w (p.toSeating.ends (.inl (.inr e)))
  refine ⟨z, funext fun q => ?_⟩
  obtain ⟨t, rfl⟩ := p.toSeating.ends.surjective q
  rcases t with (i|e)|(i|e)
  · exact ((p.read_agrees u v z).1 ⟨_, p.input i⟩).trans (hw.1 ⟨_, p.input i⟩).symm
  · rw [read_end]; rfl
  · exact ((p.read_agrees u v z).1 ⟨_, p.output i⟩).trans (hw.1 ⟨_, p.output i⟩).symm
  · rw [read_end]
    exact hw.2 _ _ (p.internal e)

-- 读法：`S.table r (p.vertex w) (p.read u v z ∘ S.port r (p.vertex w))` 等于 `G.vertex u v z w`。用函数外延性比较等号两侧在 `i` 处的取值。
theorem table_eq (z : G.E → Bool) (w : G.V) :
    S.table r (p.vertex w) (p.read u v z ∘ S.port r (p.vertex w)) = G.vertex u v z w := by
  rw [p.sample, ← Transcript.sample_wires]
  apply congrArg (Transcript.sample _)
  funext i
  simp only [Function.comp_apply, ← p.toSeating.ends_at, read_end]
  rcases i with i | i
  · change Sum.elim _ _ (G.src ⟨w, i⟩) = _
    simp only [Transcript.wires]
    cases G.src ⟨w, i⟩ <;> rfl
  · change Sum.elim _ _ (G.dst ⟨w, i⟩) = _
    simp only [Transcript.wires]
    cases G.dst ⟨w, i⟩ <;> rfl

-- 读法：`S.eval r (p.exterior u v)` 等于 `G.eval u v`。这里调用 `ite_eq_right`。
theorem eval : S.eval r (p.exterior u v) = G.eval u v := by
  unfold Scheme.eval Diagram.eval
  symm
  refine Fintype.sum_of_injective (p.read u v) (p.read_injective u v) _ _ ?_ ?_
  · intro w hw
    exact ite_eq_right fun h => hw (p.read_surjective u v w h)
  · intro z
    rw [ite_eq_left (p.read_agrees u v z)]
    exact Fintype.prod_of_injective p.vertex p.vertex.injective _ _
      (fun i hi => p.vacant i hi _) (fun w => (p.table_eq u v z w).symm)

end Presentation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# 重排已给出表示的图式

保留原顶点名称、内部边名称和外部线端，只改变各顶点处的端口次序。

**英文原文**

Reordering a presented diagram

The original vertex names, internal edge names and exterior ends
are retained. Only the order of ports at each vertex changes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Transcript

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj}
  {G : Diagram F x y} (p : S.Presentation r G)

-- 读法：`Directed` 表示以下条件：对每个 `t : G.End`，`S.direction r (p.toSeating.ends t).1` 等于 `t.isRight`。
def Directed : Prop :=
  ∀ t : G.End, S.direction r (p.toSeating.ends t).1 = t.isRight

-- 读法：`S.direction r (p.vertex v, (p.pin v i).1)` 等于 `i.isRight`。
theorem side (h : p.Directed) (v : G.V) (i : G.Port v) :
    S.direction r (p.vertex v, (p.pin v i).1) = i.isRight := by
  have he := h (G.portEquiv ⟨v, i⟩)
  rw [p.toSeating.ends_at] at he
  cases i <;> exact he

-- 读法：存在 `f : A ≃ C`，存在 `g : B ≃ D`，`f.sumCongr g` 等于 `e`。
private theorem split {A B C D : Type} (e : A ⊕ B ≃ C ⊕ D)
    (h : ∀ i, (e i).isRight = i.isRight) :
    ∃ f : A ≃ C, ∃ g : B ≃ D, f.sumCongr g = e := by
  have l (a : A) : ∃ c, e (.inl a) = .inl c := by
    have hi := h (.inl a)
    cases he : e (.inl a) <;> simp_all
  have r (b : B) : ∃ d, e (.inr b) = .inr d := by
    have hi := h (.inr b)
    cases he : e (.inr b) <;> simp_all
  choose f hf using l
  choose g hg using r
  have he : Sum.map f g = e := by funext i; cases i <;> simp [hf, hg]
  have hk : Function.Bijective (Sum.map f g) := he.symm ▸ e.bijective
  obtain ⟨h₁, h₂⟩ := Sum.map_bijective.mp hk
  exact ⟨Equiv.ofBijective f h₁, Equiv.ofBijective g h₂, Equiv.ext (congrFun he)⟩

-- 读法：`stationTable` 的取值由 `(S.pattern r (p.vertex v)).orderedTable (p.vertex v).2.2` 给出。
def stationTable (v : G.V) := (S.pattern r (p.vertex v)).orderedTable (p.vertex v).2.2

-- 读法：`stationPin` 的取值由 `(S.pattern r (p.vertex v)).orderedPin (p.vertex v).2.2` 给出。
def stationPin (v : G.V) : Ports (p.stationTable v) ≃ S.LocalPin r (p.vertex v) :=
  (S.pattern r (p.vertex v)).orderedPin (p.vertex v).2.2

variable (h : p.Directed)

include h in
-- 读法：存在 `f : slots (p.stationTable v).1 ≃ slots (G.table v).1`，存在 `g : slots (p.stationTable v).2.1 ≃ slots (G.table v).2.1`，`f.sumCongr g` 等于 `(p.stationPin v).trans (p.pin v).symm`。这里调用 `S.pattern`。
private theorem split_pin (v : G.V) :
    ∃ f : slots (p.stationTable v).1 ≃ slots (G.table v).1,
      ∃ g : slots (p.stationTable v).2.1 ≃ slots (G.table v).2.1,
        f.sumCongr g = (p.stationPin v).trans (p.pin v).symm := by
  apply split
  intro i
  rw [← p.side h, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (S.pattern r (p.vertex v)).pin_side _ i

-- 读法：`left` 的取值由 `(p.split_pin h v).choose` 给出。
private def left (v : G.V) := (p.split_pin h v).choose
-- 读法：`right` 的取值由 `(p.split_pin h v).choose_spec.choose` 给出。
private def right (v : G.V) := (p.split_pin h v).choose_spec.choose

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F x y`。
def ordered : Diagram F x y where
  V := G.V
  E := G.E
  table := p.stationTable
  src := (Equiv.sigmaCongrRight (p.left h)).trans G.src
  dst := (Equiv.sigmaCongrRight (p.right h)).trans G.dst

-- 读法：用字段 `vertex`、`pin`、`cover`、`sample` 构造 `S.Seating r (p.ordered h)`。
private def seatOrdered : S.Seating r (p.ordered h) where
  vertex := p.vertex
  pin := p.stationPin
  cover := p.cover
  sample v t := ((S.pattern r (p.vertex v)).sample_ordered (p.vertex v).2.2 t).symm
  vacant := p.vacant

-- 读法：`(p.seatOrdered h).ends` 等于 `p.toSeating.ends`。按 `Equiv.ext` 的外延性准则比较各分量。
private theorem same_ends : (p.seatOrdered h).ends = p.toSeating.ends := by
  apply Equiv.ext
  intro t
  obtain ⟨⟨v, i⟩, rfl⟩ := (p.ordered h).portEquiv.surjective t
  rw [Seating.ends_at]
  let a := (p.left h v).sumCongr (p.right h v)
  have eq : (p.ordered h).portEquiv ⟨v, i⟩ = G.portEquiv ⟨v, a i⟩ := by cases i <;> rfl
  rw [eq]
  refine Eq.trans ?_ (p.toSeating.ends_at v (a i)).symm
  change S.port r (p.vertex v) (p.stationPin v i) = S.port r (p.vertex v) (p.pin v (a i))
  have ha : a = (p.stationPin v).trans (p.pin v).symm := (p.split_pin h v).choose_spec.choose_spec
  rw [ha]
  exact congrArg _ ((p.pin v).apply_symm_apply (p.stationPin v i)).symm

-- 读法：用字段 `toSeating`、`proper`、`internal`、`input` 构造 `S.Presentation r (p.ordered h)`。
def toOrdered : S.Presentation r (p.ordered h) where
  toSeating := p.seatOrdered h
  proper := p.proper
  internal := by rw [same_ends]; exact p.internal
  input := by rw [same_ends]; exact p.input
  output := by rw [same_ends]; exact p.output

-- 读法：`(p.toOrdered h).toSeating.ends` 等于 `p.toSeating.ends`。使用 `p.same_ends` 给出的结论。
theorem ordered_ends : (p.toOrdered h).toSeating.ends = p.toSeating.ends := p.same_ends h

-- 读法：`(p.ordered h).eval a b` 等于 `G.eval a b`。
theorem ordered_eval (a : Val x) (b : Val y) : (p.ordered h).eval a b = G.eval a b := by
  rw [← (p.toOrdered h).eval, ← p.eval]
  unfold exterior read
  rw [ordered_ends]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# 规范表示的端口次序

内部区段两端的偏移量相同。因此，局部偏移量每前进一步，对端的位置也随之前进一步。

**英文原文**

Port order of a canonical presentation

On internal spans the two ends have the same offset. Consecutive
local offsets therefore advance the position on the remote side.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Transcript

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj}

-- 读法：`startFromOrdered` 的取值由 `(S.pattern r s.1).start s.1.2.2 s.2` 给出。
private def startFromOrdered (S : Scheme F) (r : S.format.obj) (s : S.Span) :=
  (S.pattern r s.1).start s.1.2.2 s.2

-- 读法：`location` 的取值由 `(z.1.1, S.startFromOrdered r z.1 + z.2.val)` 给出。
private def location (z : S.Pin r) : S.Vtx × ℕ :=
  (z.1.1, S.startFromOrdered r z.1 + z.2.val)

-- 读法：`remote` 的取值由 `(S.peer r z.1).map fun t => (t.1, S.startFromOrdered r t + z.2.val)` 给出。
private def remote (z : S.Pin r) : Option (S.Vtx × ℕ) :=
  (S.peer r z.1).map fun t => (t.1, S.startFromOrdered r t + z.2.val)

omit [Field F] in
-- 读法：`remote z` 等于 `some (location w)`。
private theorem Joins.remote_eq {z w : S.Pin r} (h : S.Joins r z w) :
    remote z = some (location w) := by
  simp only [remote, location, h.1, h.2, Option.map_some]

namespace Presentation
variable {G : Diagram F x y} (p : S.Presentation r G)

-- 读法：`pinAt` 的取值由 `S.port r (p.vertex v) (p.pin v i)` 给出。
private def pinAt (v : G.V) (i : G.Port v) := S.port r (p.vertex v) (p.pin v i)

-- 读法：`offset` 的取值由 `Sum.elim (fun i => (positions (G.table v).1 i).val) (fun i => (positions (G.table v).2.1 i).val)` 给出。
private def offset (G : Diagram F x y) (v : G.V) : G.Port v → ℕ :=
  Sum.elim (fun i => (positions (G.table v).1 i).val)
    (fun i => (positions (G.table v).2.1 i).val)

-- 读法：`Aligned` 表示以下条件：对每个 `v i`，`offset G v i` 等于 `S.startFromOrdered r (p.pinAt v i).1 + (p.pinAt v i).2.val`。
private def Aligned : Prop :=
  ∀ v i, offset G v i = S.startFromOrdered r (p.pinAt v i).1 + (p.pinAt v i).2.val

-- 读法：`relabel` 的取值由 `(p.vertex t.1, t.2)` 给出。
private def relabel (t : G.V × ℕ) : S.Vtx × ℕ := (p.vertex t.1, t.2)

-- 读法：`p.relabel` 是单射。这里调用 `Prod.ext`。
private theorem relabel_inj : Function.Injective p.relabel := by
  intro i j h
  exact Prod.ext (p.vertex.injective (congrArg Prod.fst h)) (congrArg (Prod.snd (α := S.Vtx)) h)

-- 读法：`location (p.toSeating.ends (.inl e))` 等于 `p.relabel ((G.src.symm e).1, (positions (G.table (G.src.symm e).1).1 (G.src.symm e).2).val)`。
private theorem loc_src (ha : p.Aligned) (e : slots x ⊕ G.E) :
    location (p.toSeating.ends (.inl e)) =
      p.relabel ((G.src.symm e).1, (positions (G.table (G.src.symm e).1).1 (G.src.symm e).2).val) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.src.surjective e
  rw [Equiv.symm_apply_apply]
  have he : p.toSeating.ends (.inl (G.src ⟨v, i⟩)) = p.pinAt v (.inl i) :=
    p.toSeating.ends_at v (.inl i)
  rw [he, location, ← ha]
  rfl

-- 读法：`location (p.toSeating.ends (.inr e))` 等于 `p.relabel ((G.dst.symm e).1, (positions (G.table (G.dst.symm e).1).2.1 (G.dst.symm e).2).val)`。
private theorem loc_dst (ha : p.Aligned) (e : slots y ⊕ G.E) :
    location (p.toSeating.ends (.inr e)) =
      p.relabel ((G.dst.symm e).1, (positions (G.table (G.dst.symm e).1).2.1 (G.dst.symm e).2).val) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.dst.surjective e
  rw [Equiv.symm_apply_apply]
  have he : p.toSeating.ends (.inr (G.dst ⟨v, i⟩)) = p.pinAt v (.inr i) :=
    p.toSeating.ends_at v (.inr i)
  rw [he, location, ← ha]
  rfl

-- 读法：`(G.portPeer v i).2.map p.relabel` 等于 `remote (p.pinAt v i)`。
private theorem mapped_peer (ha : p.Aligned) (v : G.V) (i : G.Port v) :
    (G.portPeer v i).2.map p.relabel = remote (p.pinAt v i) := by
  rcases i with i | i
  · have he : p.pinAt v (.inl i) = p.toSeating.ends (.inl (G.src ⟨v, i⟩)) :=
      (p.toSeating.ends_at v (.inl i)).symm
    rw [he]
    unfold Diagram.portPeer
    dsimp only
    cases G.src ⟨v, i⟩ with
    | inl i => simp only [remote, p.input, Sum.elim_inl, Option.map_none]
    | inr e => rw [(p.internal e).remote_eq, p.loc_dst ha]; rfl
  -- 推导：记下中间结论 `he`：`p.pinAt v (.inr i) = p.toSeating.ends (.inr (G.dst ⟨v, i⟩))`。
  · have he : p.pinAt v (.inr i) = p.toSeating.ends (.inr (G.dst ⟨v, i⟩)) :=
      (p.toSeating.ends_at v (.inr i)).symm
    rw [he]
    unfold Diagram.portPeer
    dsimp only
    cases G.dst ⟨v, i⟩ with
    | inl i => simp only [remote, p.output, Sum.elim_inl, Option.map_none]
    | inr e => rw [((p.internal e).symm p.proper).remote_eq, p.loc_src ha]; rfl

-- 读法：`G.portPeer v j` 等于 `Diagram.advance (G.portPeer v i)`。按 `Prod.ext` 的外延性准则比较各分量。
private theorem adjacent (ha : p.Aligned) (v : G.V) (i j : G.Port v)
    (hb : i.isRight = j.isRight) (hs : (p.pinAt v i).1 = (p.pinAt v j).1)
    (hn : offset G v i + 1 = offset G v j) :
    G.portPeer v j = Diagram.advance (G.portPeer v i) := by
  have he : (p.pinAt v i).2.val + 1 = (p.pinAt v j).2.val := by
    rw [ha, ha] at hn
    have := congrArg (S.startFromOrdered r) hs
    omega
  apply Prod.ext
  · cases i <;> cases j <;> exact hb.symm
  · have inj : Function.Injective (Option.map p.relabel) := by
      rintro (_|a) (_|b) he <;> simp_all [p.relabel_inj.eq_iff]
    apply inj
    -- 推导：记下中间结论 `a`：`S.Vtx × ℕ → S.Vtx × ℕ`。
    let a : S.Vtx × ℕ → S.Vtx × ℕ := fun t => (t.1, t.2 + 1)
    have eq : (Diagram.advance (G.portPeer v i)).2.map p.relabel =
        ((G.portPeer v i).2.map p.relabel).map a := by
      unfold Diagram.advance
      cases (G.portPeer v i).2 <;> rfl
    rw [eq, p.mapped_peer ha, p.mapped_peer ha]
    unfold remote
    rw [← he, ← hs]
    cases S.peer r (p.pinAt v i).1 <;> rfl

-- 读法：`position` 的取值由 `positions (.pair (G.table v).1 (G.table v).2.1)` 给出。
private def position (G : Diagram F x y) (v : G.V) : G.Port v ≃ Fin (G.arity v) :=
  positions (.pair (G.table v).1 (G.table v).2.1)

omit [Field F] in
-- 读法：`(position G v i).val` 等于 `(if i.isRight then wd (G.table v).1 else 0) + offset G v i`。对 `i` 分类讨论。
private theorem position_val (v : G.V) (i : G.Port v) :
    (position G v i).val = (if i.isRight then wd (G.table v).1 else 0) + offset G v i := by
  cases i
  · exact (Nat.zero_add _).symm
  · rfl

-- 读法：`block` 的结果类型为 `Fin (2 ^ (S.e + 1))`。
private def block (v : G.V) (i : G.Port v) : Fin (2 ^ (S.e + 1)) :=
  ⟨(if i.isRight then 2 ^ S.e else 0) + (p.pin v i).1.val, by
    have := (p.pin v i).1.isLt
    rw [pow_succ]
    split <;> omega⟩

-- 读法：`p.block v i` 不超过 `p.block v j`。按 `i.isRight = j.isRight` 成立与否分情况。
private theorem block_mono (h : p.Directed) (ha : p.Aligned) (v : G.V) (i j : G.Port v)
    (hn : (position G v i).val ≤ (position G v j).val) : p.block v i ≤ p.block v j := by
  simp only [position_val] at hn
  by_cases hb : i.isRight = j.isRight
  · rw [hb, ha, ha] at hn
    suffices he : (p.pin v i).1 ≤ (p.pin v j).1 by
      simp only [block, Fin.mk_le_mk, hb]
      exact Nat.add_le_add_left he _
    by_contra! he
    have hd := (p.side h v j).trans (hb.symm.trans (p.side h v i).symm)
    have ht : S.startFromOrdered r (p.pinAt v j).1 + S.width r (p.pinAt v j).1 ≤ S.startFromOrdered r (p.pinAt v i).1 :=
      (S.pattern r (p.vertex v)).start_left (p.vertex v).2.2 hd he
    have := (p.pinAt v j).2.isLt
    omega
  · rcases i with i | i <;> rcases j with j | j
    · exact (hb rfl).elim
    · have := (p.pin v (.inl i)).1.isLt
      change 0 + _ ≤ 2 ^ S.e + _
      omega
    · have : offset G v (.inl j) < wd (G.table v).1 := Fin.isLt _
      change wd _ + _ ≤ 0 + _ at hn
      omega
    · exact (hb rfl).elim

-- 读法：`G.portPeer v j` 等于 `Diagram.advance (G.portPeer v i)`。
private theorem block_next (ha : p.Aligned) (v : G.V) (i j : G.Port v)
    (hn : (position G v i).val + 1 = (position G v j).val) (he : p.block v i = p.block v j) :
    G.portPeer v j = Diagram.advance (G.portPeer v i) := by
  have he' := congrArg Fin.val he
  simp only [block] at he'
  have hb : i.isRight = j.isRight := by
    have hi := (p.pin v i).1.isLt
    have hj := (p.pin v j).1.isLt
    cases hi' : i.isRight <;> cases hj' : j.isRight <;>
      simp [hi', hj'] at he' ⊢ <;> omega
  have hs : (p.pin v i).1 = (p.pin v j).1 := by
    rw [hb] at he'
    exact Fin.ext (Nat.add_left_cancel he')
  simp only [position_val, hb] at hn
  exact p.adjacent ha v i j hb (congrArg (Prod.mk (p.vertex v)) hs) (by omega)

-- 读法：要证明的命题是 `G.PortOrder (2 ^ (S.e + 1))`。这里调用 `p.block_mono`。
private theorem portOrder (h : p.Directed) (ha : p.Aligned) : G.PortOrder (2 ^ (S.e + 1)) := by
  intro v
  let e := position G v
  refine ⟨p.block v ∘ e.symm, ?_, ?_⟩
  · intro i j hn
    apply p.block_mono h ha
    simpa only [e, Equiv.apply_symm_apply] using (show i.val ≤ j.val from hn)
  · intro i j hn he
    apply p.block_next ha v (e.symm i) (e.symm j) _ he
    simpa only [e, Equiv.apply_symm_apply] using hn

-- 读法：要证明的命题是 `(p.toOrdered h).Aligned`。这里调用 `S.pattern`。
private theorem ordered_aligned (h : p.Directed) : (p.toOrdered h).Aligned := by
  rintro v (i|i)
  · exact (S.pattern r (p.vertex v)).position_left (p.vertex v).2.2 i
  · exact (S.pattern r (p.vertex v)).position_right (p.vertex v).2.2 i

-- 读法：要证明的命题是 `(p.ordered h).PortOrder (2 ^ (S.e + 1))`。这里调用 `p.toOrdered`。
theorem ordered_order (h : p.Directed) : (p.ordered h).PortOrder (2 ^ (S.e + 1)) := by
  apply (p.toOrdered h).portOrder
  · unfold Directed
    rw [p.ordered_ends h]
    exact h
  · exact p.ordered_aligned h

-- 读法：`route` 的结果类型为 `List (Bool × Option (ℕ × ℕ))`。
/-- 只利用当前模式、邻居的模式及其局部站点名称，读取对端及其偏移量。

英文原文：Read the peer and its offset using only this pattern, neighbor
patterns, and their local station names.
-/
def route {d k e : ℕ} (A : Pattern F d k e) (j : Coloring.B k) (near : Coloring.B d → Pattern F d k e)
    (name : Coloring.B d → Coloring.B k → ℕ) : List (Bool × Option (ℕ × ℕ)) :=
  List.ofFn fun i : Fin (wd (A.wire j false) + wd (A.wire j true)) =>
    let arg := (positions (.pair (A.wire j false) (A.wire j true))).symm i
    let pin := A.orderedPin j arg
    (arg.isRight, (A.peer j pin.1).map (fun t =>
      (name t.1 t.2.1, (near t.1).start t.2.1 t.2.2 + pin.2.val)))

-- 读法：`peerRows` 的取值由 `route (S.pattern r v) v.2.2 (fun j => S.pattern r ((r v.1).1 j, v.2.1, v.2.2)) (fun j k => f ((r v.1).1 j, v.2.1, k))` 给出。
def peerRows (v : S.Vtx) (f : S.Vtx → ℕ) (r : S.format.obj) :=
  route (S.pattern r v) v.2.2 (fun j => S.pattern r ((r v.1).1 j, v.2.1, v.2.2))
    (fun j k => f ((r v.1).1 j, v.2.1, k))

-- 读法：`Canonical` 的结果类型为 `Prop`。
/-- 每个站点所见的表及对端序列都恰好由其模式指定，无须使用外部比特的名称。

英文原文：Every station sees exactly the table and peer sequence specified
by its pattern. No external bit names are involved.
-/
def Canonical : Prop :=
  ∀ v, G.table v = p.stationTable v ∧ ∀ f : S.Vtx → ℕ,
    List.ofFn (fun i : Fin (G.arity v) =>
      ((G.peer v i).1, (G.peer v i).2.map (Prod.map (f ∘ p.vertex) id))) =
      peerRows (p.vertex v) f r

-- 读法：要证明的命题是 `(p.toOrdered h).Canonical`。
theorem canonical_ordered (h : p.Directed) : (p.toOrdered h).Canonical := by
  let q := p.toOrdered h
  have hq : q.Aligned := p.ordered_aligned h
  intro v
  refine ⟨rfl, fun f => ?_⟩
  let A := S.pattern r (p.vertex v)
  let j := (p.vertex v).2.2
  let G' := p.ordered h
  unfold peerRows route
  refine congrArg List.ofFn (funext fun i : Fin (G'.arity v) => ?_)
  let x := (position G' v).symm i
  have he := q.mapped_peer hq v x
  apply Prod.ext
  · change (G'.portPeer v x).1 = x.isRight
    cases x <;> rfl
  · have e : (G'.peer v i).2.map (Prod.map (f ∘ q.vertex) id) =
        (remote (q.pinAt v x)).map (Prod.map f id) := by
      rw [← he, Option.map_map]
      rfl
    change (G'.peer v i).2.map (Prod.map (f ∘ q.vertex) id) = _
    rw [e]
    let s := A.orderedPin j x
    change (((A.peer j s.1).map _).map _).map _ = (A.peer j s.1).map _
    cases A.peer j s.1 <;> rfl

end Presentation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# 用有序单位线束表示核心

每个活跃出现位置可容纳一个核心站点。相对的两个区段采用同一单位内比特次序。各块共用较长的宿主名称，而每个区段只需局部索引。

**英文原文**

Presenting a core with ordered unit bundles

One core station fits at a live occurrence. Opposite spans use the
same ordering of bits in the unit. The longer host names are shared
by all blocks, while each span uses only local indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T} {h u : ℕ}
    (S : Scheme F) (r : S.format.obj) (G : HostNet F L h u)

-- 读法：`side` 的取值由 `cond t (G.dst i) (G.src i)` 给出。
def side (i : G.E) (t : Bool) := cond t (G.dst i) (G.src i)

-- 读法：`endBit` 的取值由 `let q := G.units.bits.symm (i, j) cond t (.inr (.inr q)) (.inl (.inr q))` 给出。
def endBit (i : G.E) (t : Bool) (j : Fin u) : G.diagram.End :=
  let q := G.units.bits.symm (i, j)
  cond t (.inr (.inr q)) (.inl (.inr q))

-- 读法：`spanAt` 的取值由 `((host (side G i t), block (G.ix i), 0), stub i t)` 给出。
def spanAt (host : G.V ↪ B S.m) (block : Cell h ↪ B S.h) (stub : G.E → Bool → B S.e)
    (i : G.E) (t : Bool) : S.Span :=
  ((host (side G i t), block (G.ix i), 0), stub i t)

-- 读法：`outgoing` 表示以下条件：`0 < S.width r p` 与 `S.direction r p = false ∧ (S.peer r p).isSome` 同时成立。
def outgoing (p : S.Span) : Prop :=
  0 < S.width r p ∧ S.direction r p = false ∧ (S.peer r p).isSome

-- 读法：结构的字段包括 `host`、`block`、`stub`、`index`、`vertex_eq`。
structure Posting extends S.Presentation r G.diagram where
  host : G.V ↪ B S.m
  block : Cell h ↪ B S.h
  stub : G.E → Bool → B S.e
  index : G.V → G.V → B S.d
  vertex_eq : ∀ v, vertex v = (host (G.units.place v).1, block (G.units.place v).2, 0)
  ordered : ∀ i t j, let p := toSeating.ends (endBit G i t j)
    p.1 = S.spanAt G host block stub i t ∧ p.2.val = j.val
  length : ∀ i t, S.width r (S.spanAt G host block stub i t) = u
  dir : ∀ i t, S.direction r (S.spanAt G host block stub i t) = t
  link : ∀ i t, let p := S.spanAt G host block stub i t
    (S.pattern r p.1).peer p.1.2.2 p.2 =
      some (index (side G i t) (side G i (!t)), 0, stub i (!t))

namespace Posting

variable {S r G} (p : S.Posting r G) (hu : 0 < u)

-- 读法：在后续公式中，`span` 是 `S.spanAt G p.host p.block p.stub` 的缩写。
abbrev span := S.spanAt G p.host p.block p.stub

include hu in
-- 读法：`(r (p.host (G.src i))).1 (p.index (G.src i) (G.dst i))` 等于 `p.host (G.dst i)`。
theorem target (i : G.E) :
    (r (p.host (G.src i))).1 (p.index (G.src i) (G.dst i)) = p.host (G.dst i) := by
  let t : Fin u := ⟨0, hu⟩
  have he := (p.internal (G.units.bits.symm (i, t))).1
  change S.peer r (p.toSeating.ends (endBit G i false t)).1 =
    some (p.toSeating.ends (endBit G i true t)).1 at he
  rw [(p.ordered _ _ _).1, (p.ordered _ _ _).1, peer, p.link] at he
  exact congrArg (fun q : S.Span => q.1.1) (Option.some.inj he)

include hu in
-- 读法：`i` 等于 `j`。这里调用 `Sigma.ext`。
theorem distinct {i j : G.E} (h : p.span i false = p.span j false) : i = j := by
  let t : Fin u := ⟨0, hu⟩
  have hi := p.ordered i false t
  have hj := p.ordered j false t
  have ht : p.toSeating.ends (endBit G i false t) = p.toSeating.ends (endBit G j false t) := by
    have hf := hi.1.trans (h.trans hj.1.symm)
    exact Sigma.ext hf ((Fin.heq_ext_iff (congrArg (S.width r) hf)).mpr (hi.2.trans hj.2.symm))
  have he := Sum.inr.inj (Sum.inl.inj (p.toSeating.ends.injective ht))
  exact (Prod.mk.inj (G.units.bits.symm.injective he)).1

include hu in
-- 读法：`S.outgoing r w` 与 `∃ i, p.span i false = w` 等价。对 `hp` 分类讨论。
theorem enumerates (w : S.Span) : S.outgoing r w ↔ ∃ i, p.span i false = w := by
  constructor
  · rintro ⟨hl, hd, hp⟩
    obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨w, ⟨0, hl⟩⟩
    have he : (p.toSeating.ends q).1 = w := congrArg Sigma.fst hq
    rcases q with (i|e)|(i|e)
    · rw [← he, p.input] at hp
      cases hp
    · obtain ⟨⟨i, j⟩, rfl⟩ := G.units.bits.symm.surjective e
      exact ⟨i, (p.ordered i false j).1.symm.trans he⟩
    · rw [← he, p.output] at hp
      cases hp
    -- 推导：从 `G.units.bits.symm.surjective e` 中取出 `⟨i, j⟩, rfl`。
    · obtain ⟨⟨i, j⟩, rfl⟩ := G.units.bits.symm.surjective e
      have : p.span i true = w := (p.ordered i true j).1.symm.trans he
      rw [← this, p.dir] at hd
      cases hd
  · rintro ⟨i, rfl⟩
    unfold outgoing span
    rw [p.length, p.dir, peer, p.link]
    exact ⟨hu, rfl, rfl⟩

end Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# 在相邻两次收缩之间提取零元表

将每张这样的表替换为标量一，再把原标量乘入转移权重，即使其中某个标量为零也照此处理。所有连线、站点与宿主的索引均予保留。

**英文原文**

Withdrawing zero-arity tables between contractions

Replace every such table by the scalar one. The original scalars
are multiplied into the transition weight, including when one is
zero. All wire, station and host indices remain unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

-- 读法：在后续公式中，`Diagram.sweep` 是 `{G with table := fun v => ⟨(G.table v).1, (G.table v).2.1, fun a b => if G.arity v = 0 then 1 else (G.table v).2.2 a b⟩}` 的缩写。
abbrev Diagram.sweep (G : Diagram F x y) : Diagram F x y :=
  {G with table := fun v => ⟨(G.table v).1, (G.table v).2.1,
    fun a b => if G.arity v = 0 then 1 else (G.table v).2.2 a b⟩}

-- 读法：`Transcript.sample (G.sweep.table v) t` 等于 `1`。使用 `ite_eq_left` 给出的结论。
theorem Diagram.sweep_neutral (G : Diagram F x y) (v : G.V)
    (h : G.arity v = 0) (t : Transcript.Ports (G.table v) → Bool) :
    Transcript.sample (G.sweep.table v) t = 1 :=
  ite_eq_left h

namespace Packing

-- 读法：在后续公式中，`HostNet.sweep` 是 `{G with diagram := G.diagram.sweep, units := ⟨G.units.place, G.units.bits, G.units.left, G.units.right⟩}` 的缩写。
abbrev HostNet.sweep {T : Type} {L : Fringe x y T} {h u : ℕ}
    (G : HostNet F L h u) : HostNet F L h u :=
  {G with diagram := G.diagram.sweep, units :=
    ⟨G.units.place, G.units.bits, G.units.left, G.units.right⟩}

end Packing

namespace Assembly
open Coloring Packing

namespace Pattern
variable {d e k : ℕ} (P : Pattern F d k e)

-- 读法：`empty` 的取值由 `∀ s, P.width j s = 0` 给出。
def empty (j : B k) := ∀ s, P.width j s = 0

-- 读法：当 `P.empty j` 成立时取 `P.value j (fun _ _ => false)`，否则取 `1`。
def charge (j : B k) := if P.empty j then P.value j (fun _ _ => false) else 1

-- 读法：在后续公式中，`sweep` 是 `{P with value := fun j t => if P.empty j then 1 else P.value j t}` 的缩写。
abbrev sweep := {P with value := fun j t => if P.empty j then 1 else P.value j t}

-- 读法：`P.value j t` 等于 `P.charge j * P.sweep.value j t`。按 `P.empty j` 成立与否分情况。
theorem after_sweep (j : B k) (t : (s : B e) → Fin (P.width j s) → Bool) :
    P.value j t = P.charge j * P.sweep.value j t := by
  by_cases h : P.empty j
  · simp only [charge, ite_eq_left h, mul_one]
    apply congrArg (P.value j)
    funext s i
    exact (Nat.not_lt_zero _ (i.isLt.trans_eq (h s))).elim
  · simp only [charge, ite_eq_right h, one_mul]

end Pattern

namespace Scheme
variable (S : Scheme F) (r : S.format.obj)

-- 读法：在后续公式中，`sweep` 是 `{S with decode := fun i => (S.decode i).sweep}` 的缩写。
abbrev sweep := {S with decode := fun i => (S.decode i).sweep}

-- 读法：`scalar` 的取值由 `∏ j, (S.decode i).charge j` 给出。
def scalar (i : B S.ℓ) := ∏ j, (S.decode i).charge j

-- 读法：`S.eval r u` 等于 `Fmt.weight S.scalar r * S.sweep.eval r u`。按 `S.Agrees r u y` 成立与否分情况。
theorem sweep_eval (u : S.exposed r → Bool) :
    S.eval r u = Fmt.weight S.scalar r * S.sweep.eval r u := by
  have hc : Fmt.weight S.scalar r = ∏ v : S.Vtx, (S.pattern r v).charge v.2.2 := by
    simp only [Vtx, Fintype.prod_prod_type, pattern, Fmt.weight, scalar]
  unfold eval
  rw [hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : S.Agrees r u y
  · rw [ite_eq_left h, ite_eq_left (show S.sweep.Agrees r u y from h), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (S.pattern r j).after_sweep j.2.2 _
  · rw [ite_eq_right h, ite_eq_right (show ¬ S.sweep.Agrees r u y from h), mul_zero]

variable {S r} {G : Diagram F x y} (p : S.Presentation r G)

-- 读法：`(S.pattern r (p.vertex v)).empty (p.vertex v).2.2` 与 `G.arity v = 0` 等价。
theorem Presentation.empty_iff (v : G.V) :
    (S.pattern r (p.vertex v)).empty (p.vertex v).2.2 ↔ G.arity v = 0 := by
  have hc := Fintype.card_congr (p.pin v)
  simp only [Diagram.Port, LocalPin, Fintype.card_sigma, Fintype.card_sum, card_slots,
    Fintype.card_fin] at hc
  change G.arity v = ∑ s, S.width r (p.vertex v, s) at hc
  rw [hc, Finset.sum_eq_zero_iff]
  simp [Pattern.empty, width]

-- 读法：用字段 `vertex`、`pin`、`cover`、`sample` 构造 `S.sweep.Seating r G.sweep`。
def Presentation.sweepSeats : S.sweep.Seating r G.sweep where
  vertex := p.vertex
  pin := p.pin
  cover := p.cover
  sample v t := by
    change (if (S.pattern r (p.vertex v)).empty (p.vertex v).2.2 then 1 else S.table r _ t) =
      if G.arity v = 0 then 1 else Transcript.sample _ _
    simp only [p.empty_iff]
    exact congrArg (fun z => if G.arity v = 0 then 1 else z) (p.sample v t)
  vacant v hv t := by
    change (if (S.pattern r v).empty v.2.2 then 1 else S.table r v t) = 1
    exact ite_eq_left_iff.mpr (fun _ => p.vacant v hv t)

-- 读法：`p.sweepSeats.ends t` 等于 `p.toSeating.ends t`。
theorem Presentation.sweep_end (t : G.End) : p.sweepSeats.ends t = p.toSeating.ends t := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective t
  change p.sweepSeats.ends (G.sweep.portEquiv ⟨v, i⟩) = _
  rw [Seating.ends_at, Seating.ends_at]
  rfl

-- 读法：用字段 `toSeating`、`proper`、`internal`、`input` 构造 `S.sweep.Presentation r G.sweep`。
def Presentation.sweep : S.sweep.Presentation r G.sweep where
  toSeating := p.sweepSeats
  proper := p.proper
  internal e := by erw [p.sweep_end, p.sweep_end]; exact p.internal e
  input i := by erw [p.sweep_end]; exact p.input i
  output i := by erw [p.sweep_end]; exact p.output i

-- 读法：`Posting.sweep` 的取值由 `⟨p.toPresentation.sweep, p.host, p.block, p.stub, p.index, p.vertex_eq, p.ordered, p.length, p.dir, p.link⟩` 给出。
def Posting.sweep {T : Type} {L : Fringe x y T} {h u : ℕ} {G : HostNet F L h u}
    (p : S.Posting r G) : S.sweep.Posting r G.sweep :=
  ⟨p.toPresentation.sweep, p.host, p.block, p.stub, p.index, p.vertex_eq, p.ordered, p.length, p.dir, p.link⟩

include p in
-- 读法：`G.eval a b` 等于 `Fmt.weight S.scalar r * G.sweep.eval a b`。这里调用 `Scheme.sweep_eval`。
theorem Presentation.sweep_eval (a : Val x) (b : Val y) :
    G.eval a b = Fmt.weight S.scalar r * G.sweep.eval a b := by
  rw [← p.eval, ← p.sweep.eval]
  exact Scheme.sweep_eval S r _

end Scheme
end Assembly
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# 取表示中列出的区段作为核心线束

若任取双射将平行边分组，可能使同一数据包的两端次序错乱。故取源区段为新线束名称，取区段内比特的局部序号为新比特索引。

**英文原文**

Taking the displayed spans as the core bundles

An arbitrary bijection grouping parallel edges can scramble the two
ends of a packet. Instead use the source span and its local bit
ordinal as the new bundle name and bit index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {x y : Wire}
  {G : Diagram F x y} (p : S.Presentation r G)

-- 读法：`wirePin` 的取值由 `p.toSeating.ends (cond t (.inr (.inr e)) (.inl (.inr e)))` 给出。
def wirePin (e : G.E) (t : Bool) : S.Pin r :=
  p.toSeating.ends (cond t (.inr (.inr e)) (.inl (.inr e)))

-- 读法：`(p.wirePin e t).1.1` 等于 `p.vertex (cond t (G.target e) (G.source e))`。
theorem wirePin_at (e : G.E) (t : Bool) :
    (p.wirePin e t).1.1 = p.vertex (cond t (G.target e) (G.source e)) := by
  have h (a : G.End) : (p.toSeating.ends a).1.1 = p.vertex (G.station a) := by
    obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective a
    rw [Seating.ends_at, G.station_port]
    rfl
  cases t <;> exact h _

-- 读法：`S.peer r (p.wirePin e t).1` 等于 `some (p.wirePin e (!t)).1`。对 `t` 分类讨论。
theorem wirePin_peer (e : G.E) (t : Bool) :
    S.peer r (p.wirePin e t).1 = some (p.wirePin e (!t)).1 := by
  cases t
  · exact (p.internal e).1
  · exact (p.proper _ _ (p.internal e).1).1

-- 读法：`S.direction r (p.wirePin e t).1` 等于 `t`。
theorem wirePin_dir (h : p.Directed) (e : G.E) (t : Bool) :
    S.direction r (p.wirePin e t).1 = t := by cases t <;> exact h _

-- 读法：`Uniform` 表示以下条件：对每个 `e`，`S.width r (p.wirePin e false).1` 等于 `u`。
def Uniform (u : ℕ) : Prop := ∀ e, S.width r (p.wirePin e false).1 = u

-- 读法：`S.width r (p.wirePin e t).1` 等于 `u`。对 `t` 分类讨论。
theorem wirePin_width {u : ℕ} (h : p.Uniform u) (e : G.E) (t : Bool) :
    S.width r (p.wirePin e t).1 = u := by
  cases t
  · exact h e
  · exact (p.proper _ _ (p.internal e).1).2.1.symm.trans (h e)

-- 读法：在后续公式中，`Bundle` 是 `↥(Set.range (fun e => (p.wirePin e false).1))` 的缩写。
abbrev Bundle := ↥(Set.range (fun e => (p.wirePin e false).1))

-- 读法：`root` 的取值由 `i.property.choose` 给出。
def root (i : p.Bundle) : G.E := i.property.choose

-- 读法：`(p.wirePin (p.root i) false).1` 等于 `i.val`。使用 `i.property.choose_spec` 给出的结论。
theorem origin (i : p.Bundle) : (p.wirePin (p.root i) false).1 = i.val := i.property.choose_spec

variable {u : ℕ} (hd : p.Directed) (hu : p.Uniform u)

-- 读法：`locate` 的取值由 `(⟨(p.wirePin e false).1, ⟨e, rfl⟩⟩, (p.wirePin e false).2.cast (hu e))` 给出。
def locate (e : G.E) : p.Bundle × Fin u :=
  (⟨(p.wirePin e false).1, ⟨e, rfl⟩⟩, (p.wirePin e false).2.cast (hu e))

-- 读法：`(p.wirePin e t).1 = (p.wirePin (p.root (p.locate hu e).1) t).1` 与 `(p.wirePin e t).2.val = (p.locate hu e).2.val` 同时成立。对 `t` 分类讨论。
theorem located (e : G.E) (t : Bool) :
    (p.wirePin e t).1 = (p.wirePin (p.root (p.locate hu e).1) t).1 ∧
    (p.wirePin e t).2.val = (p.locate hu e).2.val := by
  have h := (p.origin (p.locate hu e).1).symm
  cases t
  · exact ⟨h, rfl⟩
  · refine ⟨Option.some.inj ?_, (p.internal e).2.symm⟩
    exact (p.wirePin_peer e false).symm.trans ((congrArg (S.peer r) h).trans (p.wirePin_peer _ false))

include hd in
-- 读法：`(p.locate hu)` 是双射。这里调用 `Sum.inr.inj`。
theorem locate_bijective : Function.Bijective (p.locate hu) := by
  constructor
  · intro i j h
    have he : (p.wirePin i false).1 = (p.wirePin j false).1 := congrArg (fun z => z.1.val) h
    have ht : (p.wirePin i false).2.val = (p.wirePin j false).2.val := congrArg (fun z => z.2.val) h
    have hp : p.wirePin i false = p.wirePin j false :=
      Sigma.ext he ((Fin.heq_ext_iff (congrArg (S.width r) he)).mpr ht)
    exact Sum.inr.inj (Sum.inl.inj (p.toSeating.ends.injective hp))
  · rintro ⟨⟨_, e, rfl⟩, j⟩
    let a : S.Pin r := ⟨(p.wirePin e false).1, j.cast (hu e).symm⟩
    -- 推导：从 `p.toSeating.ends.surjective a` 中取出 `t, ht`。
    obtain ⟨t, ht⟩ := p.toSeating.ends.surjective a
    have hdir : t.isRight = false := (hd t).symm.trans
      ((congrArg (fun x => S.direction r x.1) ht).trans (p.wirePin_dir hd e false))
    rcases t with (i|k)|i
    · have hh := p.input i
      rw [ht] at hh
      exact (Option.some_ne_none _ ((p.wirePin_peer e false).symm.trans hh)).elim
    · have hspan := congrArg Sigma.fst ht
      have hbit := congrArg (fun x => x.2.val) ht
      exact ⟨k, Prod.ext (Subtype.ext hspan) (Fin.ext hbit)⟩
    · contradiction

-- 读法：用字段 `E`、`src`、`dst`、`bits` 构造 `Packing.Packets G u`。
def packets : Packing.Packets G u where
  E := p.Bundle
  src i := G.source (p.root i)
  dst i := G.target (p.root i)
  bits := Equiv.ofBijective (p.locate hu) (p.locate_bijective hd hu)
  left e := p.vertex.injective ((p.wirePin_at _ false).symm.trans
    ((congrArg Prod.fst (p.located hu e false).1.symm).trans (p.wirePin_at e false)))
  right e := p.vertex.injective ((p.wirePin_at _ true).symm.trans
    ((congrArg Prod.fst (p.located hu e true).1.symm).trans (p.wirePin_at e true)))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# 图式表示中具名的外部边界

**英文原文**

The named exterior boundary of a presented diagram
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj}
  {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr i`。
def outer : slots x ⊕ slots y → S.exposed r
  | .inl i => ⟨_, p.input i⟩
  | .inr i => ⟨_, p.output i⟩

-- 读法：`p.outer` 是双射。
theorem outer_bijective : Function.Bijective p.outer := by
  constructor
  · intro i j h
    have e := congrArg (fun z => p.toSeating.ends.symm z.val) h
    cases i <;> cases j <;> simp [outer] at e <;> simp [e]
  · rintro ⟨a, ha⟩
    obtain ⟨t, rfl⟩ := p.toSeating.ends.surjective a
    rcases t with (i|e)|(i|e)
    · exact ⟨.inl i, rfl⟩
    · rw [(p.internal e).1] at ha
      contradiction
    · exact ⟨.inr i, rfl⟩
    · rw [((p.internal e).symm p.proper).1] at ha
      contradiction

-- 读法：`boundary` 的取值由 `Equiv.ofBijective p.outer p.outer_bijective` 给出。
def boundary := Equiv.ofBijective p.outer p.outer_bijective

-- 读法：`p.exterior a b (p.boundary i)` 等于 `Sum.elim (bits x a) (bits y b) i`。
@[simp] theorem exterior_boundary (a : Val x) (b : Val y) (i : slots x ⊕ slots y) :
    p.exterior a b (p.boundary i) = Sum.elim (bits x a) (bits y b) i := by
  cases i <;> simp [boundary, outer, exterior, read_end]

include p in
-- 读法：`Fintype.card (S.exposed r)` 等于 `wd x + wd y`。
theorem exposed_card : Fintype.card (S.exposed r) = wd x + wd y := by
  rw [← Fintype.card_congr p.boundary, Fintype.card_sum, card_slots, card_slots]

include p in
-- 读法：要证明的命题是 `S.Fits r V k`。这里调用 `Fintype.card_sigma.symm`。
theorem fits {V k : ℕ} (h : 2 ^ S.m + wd x + wd y ≤ V) (hl : ∀ i, S.load r i ≤ 2 ^ k) :
    S.Fits r V k := by
  refine ⟨le_trans ?_ h, hl⟩
  have he : ∑ i, S.load r i = wd x + wd y := by
    rw [← p.exposed_card, ← Fintype.card_congr (Equiv.sigmaFiberEquiv (S.owner r))]
    exact Fintype.card_sigma.symm
  calc
    _ ≤ ∑ i, (1 + S.load r i) := Finset.sum_le_sum fun i _ => by omega
    _ = _ := by simp [Finset.sum_add_distrib, he, add_assoc]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end
