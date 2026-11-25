-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Raw.Local

/-!
# 展开相对重置首部

每个地址比特或者直接复制自局部后缀，或者从父宿主及其邻居中选出。对各个可能的跳转并行作检验。每个子宿主的成本与父宿主地址的位宽成正比。

**英文原文**

Expanding relative reset headers

An address bit is either copied from the local suffix or selected
from the parent and its neighbors. Test each possible hop in
parallel. The cost per child is linear in the parent address width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
open Coloring Install
open scoped Classical

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun x j => decide (∃ u, ∀ v, bad x ((j, u), v) = false))` 均在 `F` 上有顶点数至多为 `(Fintype.card I + Fintype.card J * (1 + 40 * Fintype.card U * (Fintype.card V + 1)))` 的网络实现。
/-- 检验一个由若干合取式组成的析取式，其中每个基本检验至多依赖一个输入比特。

英文原文：Test a disjunction of conjunctions, each test depending on at
most one input bit.
-/
private theorem any_all (F I J U V : Type) [Field F] [Fintype I] [Fintype J]
    [Fintype U] [Fintype V] (bad : (I → Bool) → (J × U) × V → Bool)
    (h : Depends bad 1) :
    BNet F (fun x j => decide (∃ u, ∀ v, bad x ((j, u), v) = false))
      (Fintype.card I + Fintype.card J * (1 + 40 * Fintype.card U * (Fintype.card V + 1))) := by
  have reject := (h.bnet F).comp ((BNet.any F V).copies (J × U))
  have neg : Depends (fun (x : (J × U) × Unit → Bool) (p : J × U) => !(x (p, ()))) 1 := by
    intro p
    exact ⟨{(p, ())}, by simp, fun _ _ e => congrArg Bool.not (e _ (by simp))⟩
  have accept := (reject.comp (neg.bnet F)).comp ((BNet.any F U).copies J)
  have net := accept.rename (.refl I) (Equiv.prodUnique J Unit)
  convert net.mono (n := Fintype.card I +
    Fintype.card J * (1 + 40 * Fintype.card U * (Fintype.card V + 1))) ?_ using 1
  · funext x j
    apply Bool.eq_iff_iff.mpr
    simp [Function.comp_def]
    exact decide_eq_true_iff.symm
  · simp only [localCost, Fintype.card_prod, Fintype.card_unit]
    ring_nf
    omega

-- 读法：`Selects` 的结果类型为 `Prop`。
/-- 每个键比特都是投影，每个候选值则为投影或常量。

英文原文：The key bits are projections and each candidate value is a projection
or a constant.
-/
private def Selects (A : Format) (n : ℕ) (f : A.obj → Bool) : Prop :=
  ∃ (key : A.obj → B n) (kn : slots (word n) → A.pins)
    (val : B n → A.pins ⊕ Bool),
    (∀ x i, (Format.addr n).code (key x) i = A.code x (kn i)) ∧
    ∀ x, f x = Sum.elim (A.code x) id (val (key x))

-- 读法：在 `F` 上按格式 `A`、`D` 编码输入输出，映射 `f` 的电路规模至多为 `(A.width + D.width * (1 + 40 * 2 ^ n * (n + 2)))`。
private theorem select_net (F : Type) [Field F] {A D : Format} {n : ℕ}
    {f : A.obj → D.obj} (H : ∀ j, Selects A n (fun x => D.code (f x) j)) :
    Circuit F A D f (A.width + D.width * (1 + 40 * 2 ^ n * (n + 2))) := by
  choose key kn val hk hv using H
  let bad (x : A.pins → Bool) (p : (D.pins × B n) × Option (slots (word n))) :=
    let j := p.1.1
    let u := p.1.2
    match p.2 with
    | none => !(Sum.elim x id (val j u))
    | some i => decide (x (kn j i) ≠ (Format.addr n).code u i)
  have hd : Depends bad 1 := by
    rintro ⟨⟨j, u⟩, _|i⟩
    · cases he : val j u with
      | inl v => exact ⟨{v}, by simp, fun x y h => by simp [bad, he, h v (by simp)]⟩
      | inr b => exact ⟨∅, by simp, fun _ _ _ => by simp [bad, he]⟩
    · exact ⟨{kn j i}, by simp, fun x y h => by simp [bad, h (kn j i) (by simp)]⟩
  have net := any_all F _ _ _ _ bad hd
  have valid (x : A.obj) (j) (u) :
      (∀ i, bad (A.code x) ((j, u), i) = false) ↔
      key j x = u ∧ Sum.elim (A.code x) id (val j u) = true := by
    constructor
    · intro ht
      refine ⟨(Format.addr n).code.injective (funext fun i => ?_), by simpa [bad] using ht none⟩
      simpa [bad, hk] using ht (some i)
    · rintro ⟨rfl, ht⟩ (_ | i)
      · simp [bad, ht]
      · simp [bad, hk]
  unfold Circuit
  convert net using 1
  · funext x j
    -- 推导：从 `A.code.surjective x` 中取出 `v, rfl`。
    obtain ⟨v, rfl⟩ := A.code.surjective x
    apply Bool.eq_iff_iff.mpr
    simp [Function.comp_def, valid, hv]
  · simp [Format.width, B, Nat.add_assoc]

-- 读法：要证明的命题是 `Selects (Input m d k l) (d + 1) (fun x => (Graph (m + k) l).code (build m d k l x) t)`。
private theorem build_selects (m d k l : ℕ) (t : (Graph (m + k) l).pins) :
    Selects (Input m d k l) (d + 1) (fun x => (Graph (m + k) l).code (build m d k l x) t) := by
  let I := Input m d k l
  let hop (i : B (m + k)) (j : B l) (x : I.obj) := ((x.2 i).2 j).2.1
  have useHop {g : I.obj → Bool} (i : B (m + k)) (j : B l)
      (v : B (d + 1) → I.pins ⊕ Bool) (he : ∀ x, g x = Sum.elim (I.code x) id (v (hop i j x))) :
      Selects I (d + 1) g :=
    ⟨hop i j, fun t => .inr (i, .inr (j, .inr (.inl t))), v, fun _ _ => rfl, he⟩
  rcases t with ⟨i, j, z⟩ | ⟨i, z|⟨j, z⟩⟩
  · let parent := (Match.rowIndex m k i).1
    -- 推导：从 `Match.append_pin m k z` 中取出 `q, hq`。
    obtain ⟨q, hq⟩ := Match.append_pin m k z
    rcases q with q | q
    · let v (a : B (d + 1)) : I.pins ⊕ Bool :=
        if he : a.val < 2 ^ d then .inl (.inl (parent, ⟨a.val, he⟩, q))
        else .inr ((Format.addr m).code parent q)
      refine useHop i j v fun x => ?_
      refine (hq (follow x.1 parent (hop i j x)) ((x.2 i).2 j).2.2).trans ?_
      simp only [Sum.elim_inl, follow, v]
      split <;> rfl
    · refine useHop i j (fun _ => .inl (.inr (i, .inr (j, .inr (.inr q))))) fun x => ?_
      exact hq (follow x.1 parent (hop i j x)) ((x.2 i).2 j).2.2
  · exact useHop i 0 (fun _ => .inl (.inr (i, .inl z))) fun _ => rfl
  · exact useHop i j (fun _ => .inl (.inr (i, .inr (j, .inl z)))) fun _ => rfl

-- 读法：`buildCost` 的取值由 `1000 * 2 ^ (m + k + l + d) * (2 + d) * (4 + k + m)` 给出。
def buildCost (m d k l : ℕ) := 1000 * 2 ^ (m + k + l + d) * (2 + d) * (4 + k + m)

-- 读法：在 `F` 上按格式 `(Input m d k l)`、`(Graph (m + k) l)` 编码输入输出，映射 `(build m d k l)` 的电路规模至多为 `(buildCost m d k l)`。这里调用 `select_net`。
theorem build_net (F : Type) [Field F] (m d k l : ℕ) :
    Circuit F (Input m d k l) (Graph (m + k) l) (build m d k l) (buildCost m d k l) := by
  apply (select_net F (build_selects m d k l)).mono
  have h₀ := Nat.pow_le_pow_right (by decide : 0 < 2) (show m + d ≤ m + k + l + d by omega)
  have h₁ := Nat.pow_le_pow_right (by decide : 0 < 2) (show m + k ≤ m + k + l by omega)
  have h₂ := Nat.pow_le_pow_right (by decide : 0 < 2) (show m + k + l ≤ m + k + l + d by omega)
  have hi : (Input m d k l).width ≤ 2 ^ (m + k + l + d) * (m + 5 + d + k) := by
    have hu := Nat.mul_le_mul_right m h₀
    have hv := Nat.mul_le_mul_right (5 + d + k) h₂
    simp only [Input, Suffix, Neighborhood.Rows, Format.width_vec, Format.width_pair, Format.width_addr]
    rw [Format.width_bit, Format.width_addr (d + 1)]
    simp only [pow_add] at hu hv h₁ ⊢
    ring_nf at hu hv h₁ ⊢
    omega
  -- 推导：记下中间结论 `ho`：`(Graph (m + k) l).width ≤ 2 ^ (m + k + l) * (4 + m + k)`。
  have ho : (Graph (m + k) l).width ≤ 2 ^ (m + k + l) * (4 + m + k) := by
    simp only [Graph, Group.Flags, Neighborhood.Rows, Format.width_vec, Format.width_pair, Format.width_addr]
    rw [Format.width_bit]
    simp only [pow_add] at h₁ ⊢
    ring_nf at h₁ ⊢
    omega
  have hcost : 1 + 40 * 2 ^ (d + 1) * (d + 1 + 2) ≤ 200 * 2 ^ d * (2 + d) := by
    have := Nat.two_pow_pos d
    rw [pow_succ]
    ring_nf
    omega
  refine (Nat.add_le_add hi (Nat.mul_le_mul ho hcost)).trans ?_
  unfold buildCost
  rw [pow_add 2 (m + k + l) d]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
end

/-!
# 不使用块数据比较重置首部

公共子图只需图掩码、基础深度和接触项总量。选定的混合器与各块记录都不参与该比较。

**英文原文**

Comparing reset headers without block data

The common child graph only needs the graph masks, base depths
and contact totals. Neither the chosen mixer nor the block records
enter this comparison.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
    {U V : Setup S h u a Δ D Y w B'} {full : Bool}
    (P : U.Reading full) (Q : V.Reading full) (R : Relation U V) (n : ℕ)

-- 读法：结构的字段包括 `widen`、`same`、`next`、`margin`、`flags`。
structure Preview : Prop where
  widen : ∀ {k j v z}, k ≤ j → R k v z → R j v z
  same : ∀ {v z v' z'}, R n v z → R n v' z' → (v = v' ↔ z = z')
  next : ∀ {k v z}, R k v z → ∀ j, R (k + 1) (U.post.nav v j) (V.post.nav z j)
  margin : U.g = V.g
  flags : ∀ {v z}, R n v z → P.flags v = Q.flags z
  counts : ∀ {v z}, R n v z → P.counts v = Q.counts z
  base : ∀ {v z}, R n v z → U.Z.base v = V.Z.base z

variable {P Q R n}

-- 读法：要证明的命题是 `Preview P Q R n`。
theorem Look.preview {σ : Cell a} (p : Look P Q σ R n) : Preview P Q R n :=
  ⟨p.widen, p.same, p.next, p.margin, p.flags, p.counts, p.base⟩

namespace Preview

variable (p : Preview P Q R n) {v v' : U.G.V} {z z' : V.G.V} {k : ℕ}
include p

-- 读法：要证明的命题是 `Preview Q P (flip R) n`。
theorem symm : Preview Q P (flip R) n :=
  ⟨fun h r => p.widen h r, fun r s => (p.same r s).symm, fun r j => p.next r j,
   p.margin.symm, fun r => (p.flags r).symm, fun r => (p.counts r).symm, fun r => (p.base r).symm⟩

section
variable (hk : k < n) (hr : R k v z) (ht : R n v' z')
include hk hr ht

-- 读法：`U.post.nav v j = v'` 与 `V.post.nav z j = z'` 等价。使用 `p.same` 给出的结论。
theorem reach (j : B S.d) : U.post.nav v j = v' ↔ V.post.nav z j = z' :=
  p.same (p.widen hk (p.next hr j)) ht

-- 读法：`U.chart.label v v'` 等于 `V.chart.label z z'`。这里调用 `label_eq`。
theorem labels : U.chart.label v v' = V.chart.label z z' := by
  rw [P.chart, Q.chart]
  exact label_eq (p.same (p.widen hk.le hr) ht) (p.reach hk hr ht)

-- 读法：`hops U.post.nav v v'` 等于 `hops V.post.nav z z'`。
theorem columns : hops U.post.nav v v' = hops V.post.nav z z' := by
  ext j
  simp only [hops, mem_filter, mem_univ, true_and, p.reach hk hr ht]

-- 读法：`v' ∈ U.adj full v` 与 `z' ∈ V.adj full z` 等价。
theorem links : v' ∈ U.adj full v ↔ z' ∈ V.adj full z := by
  simp only [P.links, Q.links, p.reach hk hr ht, p.flags (p.widen hk.le hr)]

-- 读法：`v' ∈ U.G.C v` 与 `z' ∈ V.G.C z` 等价。
theorem core : v' ∈ U.G.C v ↔ z' ∈ V.G.C z := by
  simp only [P.core, Q.core, p.reach hk hr ht, p.flags (p.widen hk.le hr)]

end

-- 读法：存在 `z' ∈ V.G.C z`，要证明的命题是 `R (k + 1) v' z'`。
theorem neighbor (hk : k < n) (hr : R k v z) (he : v' ∈ U.G.C v) :
    ∃ z' ∈ V.G.C z, R (k + 1) v' z' := by
  obtain ⟨j, hj, _⟩ := (P.core _ _).mp he
  have ht := hj ▸ p.next hr j
  exact ⟨_, (p.core hk hr (p.widen hk ht)).mp he, ht⟩

-- 读法：要证明的命题是 `U.chart.Maps V.chart v z`。
theorem maps (hk : k < n) (hr : R k v z) : U.chart.Maps V.chart v z := by
  intro i hi
  obtain ⟨j, hj, he⟩ := p.neighbor hk hr hi
  exact ⟨j, hj, p.labels hk hr (p.widen hk he)⟩

-- 读法：`U.Z.capacity c` 等于 `V.Z.capacity c'`。
theorem capacity {c : CoreContact U.G.C} {c' : CoreContact V.G.C}
    (hk : k < n) (hr : R k c.val.1 c'.val.1) (ht : R k c.val.2 c'.val.2) :
    U.Z.capacity c = V.Z.capacity c' := by
  have ha := p.widen hk.le hr
  have hb := p.widen hk.le ht
  have hc : (∑ j, U.amount c j) = (∑ j, V.amount c' j) := by
    rw [P.total, Q.total, p.columns hk hr hb, p.counts ha]
  have hd : contactDepth U.Z.base unitEnds c = contactDepth V.Z.base unitEnds c' :=
    congrArg₂ max (p.base ha) (p.base hb)
  change (∑ j, U.amount c j) / 2 ^ (contactDepth U.Z.base unitEnds c) + 1 / U.g =
    (∑ j, V.amount c' j) / 2 ^ (contactDepth V.Z.base unitEnds c') + 1 / V.g
  rw [hc, hd, p.margin]

-- 读法：对 `t` 分类讨论。
theorem opposite (hk : k + 1 < n) (hr : R k v z) (c : CoreContact U.G.C)
    (t : Bool) (he : unitEnds c t = v) :
    ∃ c' : CoreContact V.G.C, unitEnds c' t = z ∧
      R (k + 1) (unitEnds c (!t)) (unitEnds c' (!t)) ∧
      Chart.Matches (relBase a U.Z.base) (relBase a V.Z.base) c c' ∧
      U.Z.capacity c = V.Z.capacity c' := by
  have hm : unitEnds c (!t) ∈ U.G.C v := he ▸ Chart.partner_mem U.G.cs c t
  obtain ⟨w, hw, ht⟩ := p.neighbor (by omega) hr hm
  have hv : R (k + 1) (unitEnds c t) z := he.symm ▸ p.widen (by omega) hr
  have base {i j} (r : R (k + 1) i j) : relBase a U.Z.base i = relBase a V.Z.base j :=
    congrArg (· - a) (p.base (p.widen hk.le r))
  cases t
  · let c' : CoreContact V.G.C := ⟨(z, w), hw⟩
    exact ⟨c', rfl, ht, fun b => by cases b <;> first | exact base hv | exact base ht,
      p.capacity (c' := c') hk hv ht⟩
  · let c' : CoreContact V.G.C := ⟨(w, z), V.G.cs _ _ hw⟩
    exact ⟨c', rfl, ht, fun b => by cases b <;> first | exact base ht | exact base hv,
      p.capacity (c' := c') hk ht hv⟩

-- 读法：要证明的命题是 `U.chart.Reserves U.Z.capacity V.chart V.Z.capacity (relBase a U.Z.base) (relBase a V.Z.base) v z`。
theorem relative (hk : k + 1 < n) (hr : R k v z) :
    U.chart.Reserves U.Z.capacity V.chart V.Z.capacity (relBase a U.Z.base) (relBase a V.Z.base) v z := by
  intro c t ht
  obtain ⟨c', ht', he, hd, hc⟩ := p.opposite hk hr c t ht
  exact ⟨c', ht', p.labels (by omega) hr (p.widen hk.le he), hd, hc⟩

end Preview
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 预留输出连接的两端一致

**英文原文**

Agreement of both ends of the reserved output links
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U : Setup S h u a Δ D Y w B')

-- 读法：在后续公式中，`Contact` 是 `Link (relBase a U.Z.base) (unitEnds (C := U.G.C))` 的缩写。
private abbrev Contact := Link (relBase a U.Z.base) (unitEnds (C := U.G.C))
-- 读法：在后续公式中，`Place` 是 `Fin ⌈U.Z.capacity e.1 * Y / 8⌉₊` 的缩写。
private abbrev Place (e : U.Contact) := Fin ⌈U.Z.capacity e.1 * Y / 8⌉₊
-- 读法：在后续公式中，`anchor` 是 `outLeaf (relBase a U.Z.base) (unitEnds (C := U.G.C)) (relHi a U.Z.depth)` 的缩写。
private abbrev anchor := outLeaf (relBase a U.Z.base) (unitEnds (C := U.G.C)) (relHi a U.Z.depth)

-- 读法：`reserved` 的取值由 `(U.anchor e t, U.plugs _ ⟨⟨(e, t), rfl⟩, i⟩)` 给出。
private def reserved (e : U.Contact) (t : Bool) (i : U.Place e) : Site U.G.V (h - a) × Fin Y :=
  (U.anchor e t, U.plugs _ ⟨⟨(e, t), rfl⟩, i⟩)

-- 读法：`(U.reserved e t i).2` 等于 `U.plugs x ⟨⟨(e, t), hx⟩, i⟩`。
private theorem reserved_slot (e : U.Contact) (t : Bool) (i : U.Place e)
    (x : Site U.G.V (h - a)) (hx : U.anchor e t = x) :
    (U.reserved e t i).2 = U.plugs x ⟨⟨(e, t), hx⟩, i⟩ := by subst x; rfl

-- 读法：`Packing.peer U.plugs x` 等于 `x`。这里调用 `dite_eq_right`。
private theorem peer_unused (x : Site U.G.V (h - a) × Fin Y)
    (hn : ¬∃ e t i, U.reserved e t i = x) : Packing.peer U.plugs x = x := by
  unfold Packing.peer
  exact dite_eq_right (by rintro ⟨⟨⟨e, i⟩, t⟩, he⟩; exact hn ⟨e, t, i, he⟩)

-- 读法：`Packing.peer U.plugs (U.reserved e t i)` 等于 `U.reserved e (!t) i`。
private theorem peer_at (e : U.Contact) (t : Bool) (i : U.Place e) :
    Packing.peer U.plugs (U.reserved e t i) = U.reserved e (!t) i := by
  unfold Packing.peer
  split
  · rename_i he
    have hh := he.choose_spec
    generalize he.choose = p at *
    rcases p with ⟨⟨q, j⟩, b⟩
    change U.reserved q b j = U.reserved e t i at hh
    have hz : U.anchor q b = U.anchor e t := congrArg Prod.fst hh
    -- 推导：记下中间结论 `hn`：`U.plugs _ ⟨⟨(q, b), hz⟩, j⟩ = U.plugs (U.anchor e t) ⟨⟨(e, t), rfl⟩, i⟩`。
    have hn : U.plugs _ ⟨⟨(q, b), hz⟩, j⟩ = U.plugs (U.anchor e t) ⟨⟨(e, t), rfl⟩, i⟩ :=
      (U.reserved_slot q b j _ hz).symm.trans (congrArg Prod.snd hh)
    obtain ⟨hk, hi⟩ := Sigma.mk.inj ((U.plugs _).injective hn)
    have hp : (q, b) = (e, t) := congrArg Subtype.val hk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    cases eq_of_heq hi
    rfl
  · rename_i hn
    exact (hn ⟨(⟨e, i⟩, t), rfl⟩).elim

-- 读法：`(Packing.peer U.plugs ((v, d), i)).1.1` 属于 `insert v (U.G.C v)`。按 `∃ e t k, U.reserved e t k = ((v, d), i)` 成立与否分情况。
/-- 未使用的终端留在原位，已使用的终端到达核心邻居。

英文原文：Unused terminals stay at home. Used terminals reach core neighbors.
-/
theorem peer_host (v : U.G.V) (d : Schedule.Address (h - a)) (i : Fin Y) :
    (Packing.peer U.plugs ((v, d), i)).1.1 ∈ insert v (U.G.C v) := by
  by_cases he : ∃ e t k, U.reserved e t k = ((v, d), i)
  · obtain ⟨e, t, k, hk⟩ := he
    rw [← hk, peer_at]
    have hv : unitEnds e.1 t = v := congrArg (·.1.1) hk
    exact Finset.mem_insert_of_mem (hv ▸ Chart.partner_mem U.G.cs e.1 t)
  · rw [peer_unused U _ he]
    exact Finset.mem_insert_self _ _

variable {U} {V : Setup S h u a Δ D Y w B'} {full : Bool} {P : U.Reading full} {Q : V.Reading full}
    {R : Relation U V} {n k : ℕ} (p : Preview P Q R n) {v : U.G.V} {z : V.G.V}

include p in
-- 读法：`(U.reserved e t i).2` 等于 `(V.reserved f t j).2`。这里调用 `Chart.plugs_eq`。
private theorem Preview.slot_eq (hk : k + 1 < n) {e : U.Contact} {f : V.Contact}
    (t : Bool) (hr : R k (unitEnds e.1 t) (unitEnds f.1 t))
    (hs : R n (unitEnds e.1 (!t)) (unitEnds f.1 (!t)))
    (hd : (U.anchor e t).2 = (V.anchor f t).2) (ha : Chart.address e = Chart.address f)
    {i : U.Place e} {j : V.Place f} (hi : i.val = j.val) :
    (U.reserved e t i).2 = (V.reserved f t j).2 := by
  let x := (U.anchor e t).2
  have hu : U.anchor e t = (unitEnds e.1 t, x) := rfl
  have hv : V.anchor f t = (unitEnds f.1 t, x) := Prod.ext rfl hd.symm
  rw [U.reserved_slot _ _ _ _ hu, V.reserved_slot _ _ _ _ hv]
  apply Chart.plugs_eq U.chart U.G.cs _ _ V.chart V.G.cs _ _
    (p.relative hk hr) (p.symm.relative hk hr)
  exact Prod.ext rfl (Prod.ext (p.labels (by omega) hr hs) (Prod.ext ha hi))

include p in
-- 读法：结论为 `let x := Packing.peer U.plugs ((v, d), i) let y := Packing.peer V.plugs ((z, d), i) R (k + 1) x.1.1 y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2`。
private theorem Preview.peer_on (hk : k + 3 ≤ n) (hr : R k v z) {d : Schedule.Address (h - a)} {i : Fin Y}
    (e : U.Contact) (t : Bool) (j : U.Place e) (he : U.reserved e t j = ((v, d), i)) :
    let x := Packing.peer U.plugs ((v, d), i)
    let y := Packing.peer V.plugs ((z, d), i)
    R (k + 1) x.1.1 y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2 := by
  have hv : unitEnds e.1 t = v := congrArg (·.1.1) he
  obtain ⟨c, hz, hp, hm, hc⟩ := p.opposite (by omega) hr e.1 t hv
  obtain ⟨f, rfl, ha⟩ := Chart.link_exists e c hm
  let l : V.Place f := ⟨j.val, hc ▸ j.isLt⟩
  have hs (b) : (U.anchor e b).2 = (V.anchor f b).2 :=
    Chart.Matches.site _ _ hm ha b
  have hr' : R k (unitEnds e.1 t) (unitEnds f.1 t) := by rw [hv, hz]; exact hr
  -- 推导：记下中间结论 `hf`：`V.reserved f t l = ((z, d), i)`。
  have hf : V.reserved f t l = ((z, d), i) := by
    have eq := p.slot_eq (by omega) t hr' (p.widen (by omega) hp) (hs t) ha (i := j) (j := l) rfl
    exact Prod.ext (Prod.ext hz ((hs t).symm.trans (congrArg (·.1.2) he)))
      (eq.symm.trans (congrArg Prod.snd he))
  rw [← he, ← hf, U.peer_at, V.peer_at]
  refine ⟨hp, hs (!t), p.slot_eq (by omega) (!t) hp ?_ (hs (!t)) ha rfl⟩
  rw [Bool.not_not]
  exact p.widen (by omega) hr'

include p in
-- 读法：结论为 `let x := Packing.peer U.plugs ((v, d), i) let y := Packing.peer V.plugs ((z, d), i) R (k + 1) x.1.1 y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2`。按 `∃ e t j, U.reserved e t j = ((v, d), i)` 成立与否分情况。
/-- 增加的半径使近端和远端的预留位置都能进行比较。

英文原文：The extra radius compares both the near and far reservations.
-/
theorem Preview.peer (hk : k + 3 ≤ n) (hr : R k v z) (d : Schedule.Address (h - a)) (i : Fin Y) :
    let x := Packing.peer U.plugs ((v, d), i)
    let y := Packing.peer V.plugs ((z, d), i)
    R (k + 1) x.1.1 y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2 := by
  by_cases hu : ∃ e t j, U.reserved e t j = ((v, d), i)
  · obtain ⟨e, t, j, he⟩ := hu
    exact p.peer_on hk hr e t j he
  by_cases hv : ∃ f t j, V.reserved f t j = ((z, d), i)
  · obtain ⟨f, t, j, hf⟩ := hv
    obtain ⟨he, hd, hi⟩ := p.symm.peer_on hk hr f t j hf
    exact ⟨he, hd.symm, hi.symm⟩
  rw [U.peer_unused _ hu, V.peer_unused _ hv]
  exact ⟨p.widen (by omega) hr, rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 重置图中连接的形式

**英文原文**

The forms of links in a reset graph
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ}
  {B' c : ℝ} [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)

local notation "L" => terminalWidth Δ Y
local notation "SiteAddr" => Schedule.Address (h - a)
local notation "Part" => Child.Part R Δ (h - a)

-- 读法：归纳构造子包括 `rotor`、`peer`、`enter`、`leave`、`tree`、`bridge`、`tether`。
inductive PartLink (mode : Bool) : U.G.V → Part → U.G.V → Part → Prop where
  | rotor (v s r t) (he : t ∈ R.support r) : PartLink mode v (.inl (s, r)) v (.inl (s, t))
  | peer (v s i z t j) (he : Packing.peer U.plugs ((v, s), i) = ((z, t), j)) :
      PartLink mode v (.inl (s, R.root true i)) z (.inl (t, R.root true j))
  | enter (v s i) : PartLink mode v (.inl (s, R.root false i)) v (.inr ((s, i), Tree.root L))
  | leave (v s i) : PartLink mode v (.inr ((s, i), Tree.root L)) v (.inl (s, R.root false i))
  | tree (v s i p q) (he : q ∈ Tree.adj p) : PartLink mode v (.inr ((s, i), p)) v (.inr ((s, i), q))
  | bridge (v s i z t j) (he : ((z, t), j) ∈ U.switch.near ((v, s), i)) :
      PartLink mode v (.inr ((s, i), Tree.tip (U.pins _ ⟨_, he⟩)))
        z (.inr ((t, j), Tree.tip (U.pins _ ⟨_, U.switch.sym _ _ he⟩)))
  | tether (v s i z t j) (hm : mode = true) (he : ((z, t), j) ∈ terminalNear U.G.N D Y ((v, s), i)) :
      PartLink mode v (.inl (s, R.root false i)) z (.inl (t, R.root false j))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 硬件连接与编号部件之间的转换

**英文原文**

Translating between hardware links and numbered parts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

-- 读法：这里调用 `Finset.notMem_empty`。
private theorem detour_cases {X : Type} [Fintype X] {l : ℕ} (sw : Detour.Switch X l)
    (x : X) (p : Tree.Node l) {q : Detour.Hub X l} (hq : q ∈ sw.adj (.inr (x, p))) :
    (∃ t ∈ Tree.adj p, q = .inr (x, t)) ∨ (p = Tree.root l ∧ q = .inl x) ∨
    (∃ y, ∃ h : y ∈ sw.near x, p = Tree.tip (sw.pin x ⟨y, h⟩) ∧
      q = .inr (y, Tree.tip (sw.pin y ⟨x, sw.sym _ _ h⟩))) := by
  rcases mem_union.mp hq with hq|hq
  · rcases mem_union.mp hq with hq|hq
    · obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
      exact .inl ⟨t, ht, rfl⟩
    · split_ifs at hq with hp
      · exact .inr (.inl ⟨hp, mem_singleton.mp hq⟩)
      · exact (Finset.notMem_empty _ hq).elim
  · obtain ⟨⟨y, t⟩, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨he, hp, ht⟩ := (mem_filter.mp ht).2
    exact .inr (.inr ⟨y, he, hp.symm, congrArg (fun i => Sum.inr (y, i)) ht.symm⟩)

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ}
  {B' c : ℝ} [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)

local notation "L" => terminalWidth Δ Y
local notation "SiteAddr" => Schedule.Address (h - a)
local notation "Part" => Child.Part R Δ (h - a)

variable (fits : U.Fits R c) (mode : Bool)
local notation "parts" => (Setup.parts U R fits)
local notation "links" => (Rotor.links R (switch U) (Packing.peer (plugs U)))

-- 读法：要证明的命题是 `PartLink U R mode (parts x).1 (parts x).2 (parts y).1 (parts y).2`。
private theorem core_link {x y : (U.graph R fits).V} (he : y ∈ links x) :
    PartLink U R mode (parts x).1 (parts x).2 (parts y).1 (parts y).2 := by
  rcases x with ⟨⟨v, s⟩, r⟩|⟨⟨⟨v, s⟩, i⟩, p⟩
  · rcases mem_union.mp he with he|he
    · obtain ⟨⟨⟨z, t⟩, q⟩, hq, rfl⟩ := mem_image.mp he
      rcases (R.mem_net ..).mp hq with ⟨hx, hq⟩|⟨i, hi, hq⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        exact .rotor _ _ _ _ hq
      · change r = R.root true i at hi
        subst r
        generalize hh : Packing.peer U.plugs ((v, s), i) = j at hq
        obtain ⟨⟨z', t'⟩, j⟩ := j
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq
        exact .peer _ _ _ _ _ _ hh
    -- 推导：从 `mem_image.mp he` 中取出 `i, hi, rfl`。
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      have hr : r = R.root false i := (mem_filter.mp hi).2
      subst r
      exact .enter _ _ _
  · obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    rcases detour_cases U.switch _ _ hq with ⟨t, ht, rfl⟩|⟨rfl, rfl⟩|⟨⟨⟨z, t⟩, j⟩, hn, rfl, rfl⟩
    · exact .tree _ _ _ _ _ ht
    · exact .leave _ _ _
    · exact .bridge _ _ _ _ _ _ hn

-- 读法：要证明的命题是 `PartLink U R mode (parts x).1 (parts x).2 (parts y).1 (parts y).2`。对 `mode` 分类讨论。
theorem part_link {x y : (U.graph R fits).V} (he : y ∈ U.neighbors R fits mode x) :
    PartLink U R mode (parts x).1 (parts x).2 (parts y).1 (parts y).2 := by
  cases mode
  · exact core_link U R fits false he
  rcases mem_union.mp he with he|he
  · exact core_link U R fits true he
  · split_ifs at he with hx
    · obtain ⟨⟨⟨z, t⟩, j⟩, hz, rfl⟩ := mem_image.mp he
      have hv := hx.choose_spec
      generalize hx.choose = i at hv hz
      obtain ⟨⟨v, s⟩, i⟩ := i
      rw [← hv]
      exact .tether _ _ _ _ _ _ rfl hz
    · exact (Finset.notMem_empty _ he).elim

-- 读法：`y` 属于 `U.neighbors R fits mode x`。对 `mode` 分类讨论。
private theorem from_core (x y : (U.graph R fits).V) (hy : y ∈ links x) :
    y ∈ U.neighbors R fits mode x := by
  cases mode
  · exact hy
  · exact (U.graph R fits).sub _ hy

-- 读法：`(parts).symm (y, t)` 属于 `U.neighbors R fits mode ((parts).symm (x, s))`。对 `he` 分类讨论。
set_option maxHeartbeats 650000 in
theorem link_part {x y : U.G.V} {s t : Part} (he : PartLink U R mode x s y t) :
    (parts).symm (y, t) ∈ U.neighbors R fits mode ((parts).symm (x, s)) := by
  cases he with
  | rotor j p q he =>
    apply from_core U R fits mode
    exact R.links_net U.switch _ ((R.mem_net ..).mpr (.inl ⟨rfl, he⟩))
  | peer i p z j q he =>
    apply from_core U R fits mode
    apply R.links_net
    apply (R.mem_net ..).mpr
    exact .inr ⟨p, rfl, by rw [he]⟩
  | enter j i =>
    apply from_core U R fits mode
    exact R.links_detour U.switch (Packing.peer U.plugs) (v:=.inl ((x, j), i)) (mem_singleton_self _)
  | leave j i =>
    apply from_core U R fits mode
    exact R.links_detour U.switch (Packing.peer U.plugs) (U.switch.adj_symm (.inl ((x, j), i)) _ (mem_singleton_self _))
  | tree j i p q he =>
    apply from_core U R fits mode
    exact R.links_detour U.switch (Packing.peer U.plugs) (U.switch.adj_inner ((x, j), i) he)
  | bridge j i z q l he =>
    apply from_core U R fits mode
    have ht := U.switch.adj_bridge _ _ he
    -- 推导：记下中间结论 `heq`：`U.switch.pin = U.pins`。
    have heq : U.switch.pin = U.pins := rfl
    rw [heq] at ht
    have link := R.links_detour U.switch (Packing.peer U.plugs) ht
    exact link
  | tether i p z j q hm he =>
    subst mode
    have hh := R.input_full U.switch (Packing.peer U.plugs) (terminalNear U.G.N D Y) he
    exact hh

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 在相匹配的父宿主邻域间迁移子连接

**英文原文**

Transporting a child link between matching parent neighborhoods
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ}
    {B' : ℝ} {U V : Setup S h u a Δ D Y w B'} {full : Bool}
    {P : U.Reading full} {Q : V.Reading full} {T : Relation U V} {k n : ℕ}

namespace Preview
variable (p : Preview P Q T n) {x x' : U.G.V} {y y' : V.G.V}
    {s t : Schedule.Address (h - a)} {i j : Fin Y}
include p

-- 读法：存在 `z`，`((z, t), j) ∈ terminalNear C' L Y ((y, s), i)` 与 `T (k + 1) x' z` 同时成立。
private theorem move_terminal {C : U.G.V → Finset U.G.V} {C' : V.G.V → Finset V.G.V}
    {L : ℕ} (hr : T k x y) (hc : ∀ v ∈ C x, ∃ z ∈ C' y, T (k + 1) v z)
    (he : ((x', t), j) ∈ terminalNear C L Y ((x, s), i)) :
    ∃ z, ((z, t), j) ∈ terminalNear C' L Y ((y, s), i) ∧ T (k + 1) x' z := by
  rcases (mem_near ..).mp (mem_product.mp he).1 with eq | ⟨hv, ht⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact ⟨y, mem_product.mpr ⟨near_self _ _ _, mem_univ _⟩, p.widen (by omega) hr⟩
  obtain ⟨z, hz, r⟩ := hc _ hv
  exact ⟨z, mem_product.mpr ⟨(mem_near ..).mpr (.inr ⟨hz, ht⟩), mem_univ _⟩, r⟩

-- 读法：`U.pins _ ⟨_, he⟩` 等于 `V.pins _ ⟨_, hf⟩`。
private theorem pin_eq (hn : k < n) (hr : T k x y) (ht : T n x' y')
    (he : ((x', t), j) ∈ terminalNear U.G.C Δ Y ((x, s), i))
    (hf : ((y', t), j) ∈ terminalNear V.G.C Δ Y ((y, s), i)) :
    U.pins _ ⟨_, he⟩ = V.pins _ ⟨_, hf⟩ :=
  U.chart.treePin_eq V.chart (p.maps hn hr) (p.symm.maps hn hr)
    U.hΔ U.deg V.deg s i _ _ (Prod.ext (p.labels hn hr ht) rfl)

-- 读法：存在 `y'`，`PartLink V R mode y i y' j` 与 `T (k + 1) x' y'` 同时成立。对 `hx` 分类讨论。
/-- 若对父宿主重新命名，连接的两个部分均保持不变。

英文原文：Both parts of a link are unchanged when its parent hosts are relabeled.
-/
theorem move_link (R : Rotor F Y w) (mode : Bool) (hm : mode = true → full = true)
    {i j : Child.Part R Δ (h - a)} (hn : k + 4 ≤ n) (hr : T k x y)
    (hx : PartLink U R mode x i x' j) :
    ∃ y', PartLink V R mode y i y' j ∧ T (k + 1) x' y' := by
  have hk : k < n := by omega
  have hw : T (k + 1) x y := p.widen (by omega) hr
  cases hx with
  | rotor s r t he => exact ⟨y, .rotor _ _ _ _ he, hw⟩
  | enter s i => exact ⟨y, .enter _ _ _, hw⟩
  | leave s i => exact ⟨y, .leave _ _ _, hw⟩
  | tree s i b c he => exact ⟨y, .tree _ _ _ _ _ he, hw⟩
  | peer s i z t j he =>
    have hp := p.peer (by omega) hr s i
    rw [he] at hp
    exact ⟨_, .peer _ _ _ _ _ _ (Prod.ext (Prod.ext rfl hp.2.1.symm) hp.2.2.symm), hp.1⟩
  | bridge s i z t j he =>
    -- 推导：从 `p.move_terminal hr (fun _ h => p.neighbor hk hr h) he` 中取出 `b, hb, hz`。
    obtain ⟨b, hb, hz⟩ := p.move_terminal hr (fun _ h => p.neighbor hk hr h) he
    have hf := p.pin_eq hk hr (p.widen hk hz) he hb
    have hg := p.pin_eq (by omega) hz (p.widen hk.le hr)
      (U.switch.sym _ _ he) (V.switch.sym _ _ hb)
    rw [hf, hg]
    exact ⟨b, .bridge _ _ _ _ _ _ hb, hz⟩
  | tether s i z t j ha he =>
    have hh := hm ha
    subst full
    have hc (v) (hv : v ∈ U.G.N x) : ∃ b ∈ V.G.N y, T (k + 1) v b := by
      -- 推导：从 `(P.links _ _).mp hv` 中取出 `q, hq, _`。
      obtain ⟨q, hq, _⟩ := (P.links _ _).mp hv
      have hb := hq ▸ p.next hr q
      exact ⟨_, (p.links hk hr (p.widen hk hb)).mp hv, hb⟩
    obtain ⟨b, hb, hz⟩ := p.move_terminal hr hc he
    exact ⟨b, .tether _ _ _ _ _ _ ha hb, hz⟩

end Preview
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 依据父宿主的计算结果重建子宿主的邻接关系

**英文原文**

Reconstructing child adjacency from the parent computation
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ}
  {B' c : ℝ} [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w)

local notation "Part" => Child.Part R Δ (h - a)

omit [NeZero Y] [NeZero w] in
-- 读法：`z` 属于 `insert v (U.adj full v)`。对 `full` 分类讨论。
private theorem part_parent (full : Bool) {v z : U.G.V} {i j : Part}
    (e : PartLink U R full v i z j) : z ∈ insert v (U.adj full v) := by
  have sub (v : U.G.V) : insert v (U.G.C v) ⊆ insert v (U.adj full v) := by
    cases full
    · exact subset_rfl
    · exact insert_subset_insert _ (U.G.sub v)
  cases e with
  | rotor | enter | leave | tree => exact mem_insert_self ..
  | peer s i z t j he =>
    have ht := U.peer_host v s i
    rw [he] at ht
    exact sub _ ht
  | bridge s i z t j he =>
    exact sub _ (Chart.near_host (mem_product.mp he).1)
  | tether s i z t j hm he =>
    subst full
    exact Chart.near_host (mem_product.mp he).1

-- 读法：`(U.parts R fits y).1` 属于 `insert (U.parts R fits x).1 (U.adj full (U.parts R fits x).1)`。使用 `part_parent` 给出的结论。
theorem parent_mem (fits : U.Fits R c) (full : Bool) {x y : (U.graph R fits).V}
    (he : y ∈ U.neighbors R fits full x) :
    (U.parts R fits y).1 ∈ insert (U.parts R fits x).1 (U.adj full (U.parts R fits x).1) :=
  part_parent U R full (part_link U R fits full he)

variable {U} {V : Setup S h u a Δ D Y w B'} {full : Bool} {k n : ℕ}
    {P : U.Reading full} {Q : V.Reading full} {T : Relation U V}

-- 读法：存在 `y' ∈ V.neighbors R fv mode y`，`T (k + 1) (U.parts R fu x').1 (V.parts R fv y').1` 与 `(U.parts R fu x').2 = (V.parts R fv y').2` 同时成立。
theorem Preview.adjacent (p : Preview P Q T n) (R : Rotor F Y w) (fu : U.Fits R c) (fv : V.Fits R c)
    (mode : Bool) (hm : mode = true → full = true) {x x' : (U.graph R fu).V} {y : (V.graph R fv).V}
    (hn : k + 4 ≤ n) (hr : T k (U.parts R fu x).1 (V.parts R fv y).1)
    (he : (U.parts R fu x).2 = (V.parts R fv y).2) (hx : x' ∈ U.neighbors R fu mode x) :
    ∃ y' ∈ V.neighbors R fv mode y, T (k + 1) (U.parts R fu x').1 (V.parts R fv y').1 ∧
      (U.parts R fu x').2 = (V.parts R fv y').2 := by
  obtain ⟨z, ha, hz⟩ := p.move_link R mode hm hn hr (part_link U R fu mode hx)
  rw [he] at ha
  have hh := link_part V R fv mode ha
  rw [Prod.mk.eta, Equiv.symm_apply_apply] at hh
  refine ⟨_, hh, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact ⟨hz, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 根据相对名称为子宿主的邻居编号

零号槽位为子宿主自身预留。用父宿主处的返回跳转与硬件后缀给其余邻居编号。所得次序无须用到环境中的宿主名称。

**英文原文**

Numbering child neighbors by relative names

Slot zero is reserved for the child itself. Number its strict
neighbors by the return hop at the parent and the hardware suffix.
The resulting order needs no ambient host names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Coloring Packing Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fits : U.Fits R c)


-- 读法：`coord` 的取值由 `(U.chart.label (U.parts R fits x).1 (U.parts R fits y).1, (U.parts R fits y).2)` 给出。
private def coord (x y : (U.graph R fits).V) :=
  (U.chart.label (U.parts R fits x).1 (U.parts R fits y).1, (U.parts R fits y).2)

-- 读法：`candidates` 的取值由 `((U.neighbors R fits mode x).image (U.coord R fits x)).erase (U.coord R fits x x)` 给出。
private def candidates (mode : Bool) (x : (U.graph R fits).V) :=
  ((U.neighbors R fits mode x).image (U.coord R fits x)).erase (U.coord R fits x x)

-- 读法：`(U.candidates R fits mode x).card` 严格小于 `2 ^ (Child.width D Y mode)`。对 `mode` 分类讨论。
private theorem card_candidates (mode : Bool) (x : (U.graph R fits).V) :
    (U.candidates R fits mode x).card < 2 ^ (Child.width D Y mode) := by
  refine lt_of_le_of_lt (card_erase_le.trans card_image_le) ?_
  cases mode
  · exact Nat.lt_succ_of_le ((U.result R fits).core_degree x)
  · have hd := (U.result R fits).full_degree x
    have ht := Nat.le_pow_clog (by decide : 1 < 2) (4 + terminalWidth D Y)
    change ((U.result R fits).full x).card < 2 ^ Nat.clog 2 (4 + terminalWidth D Y)
    omega

-- 读法：当 `hp : x ∈ s` 成立时取 `(s.equivFin ⟨x, hp⟩).val + 1`，否则取 `0`。
private def number {A : Type} (s : Finset A) (x : A) : ℕ :=
  if hp : x ∈ s then (s.equivFin ⟨x, hp⟩).val + 1 else 0

-- 读法：`number s x` 不超过 `s.card`。这里调用 `s.equivFin`。
private theorem number_le {A : Type} (s : Finset A) (x : A) : number s x ≤ s.card := by
  unfold number
  split
  · exact (s.equivFin _).isLt
  · exact Nat.zero_le _

-- 读法：要证明的命题是 `Set.InjOn (number s) (insert x (s : Set A))`。这里调用 `hi.resolve_right`。
private theorem number_inj {A : Type} (s : Finset A) (x : A) :
    Set.InjOn (number s) (insert x (s : Set A)) := by
  intro i hi j hj he
  unfold number at he
  split at he <;> split at he
  · exact congrArg Subtype.val (s.equivFin.injective (Fin.ext (Nat.add_right_cancel he)))
  · omega
  · omega
  · rename_i h₁ h₂
    exact (hi.resolve_right h₁).trans (hj.resolve_right h₂).symm

-- 读法：`index` 的取值由 `⟨number (U.candidates R fits full x) (U.coord R fits x y), (number_le ..).trans_lt (U.card_candidates R fits full x)⟩` 给出。
def index (full : Bool) (x y : (U.graph R fits).V) : B (Child.width D Y full) :=
  ⟨number (U.candidates R fits full x) (U.coord R fits x y),
    (number_le ..).trans_lt (U.card_candidates R fits full x)⟩

-- 读法：`U.index R fits full x x` 等于 `0`。按 `Fin.ext` 的外延性准则比较各分量。
theorem index_self (full : Bool) (x : (U.graph R fits).V) : U.index R fits full x x = 0 := by
  apply Fin.ext
  simp [index, number, candidates]

-- 读法：要证明的命题是 `Set.InjOn (U.index R fits full x) (↑(insert x (U.neighbors R fits full x)))`。
theorem index_inj (full : Bool) (P : U.Reading full) (x : (U.graph R fits).V) :
    Set.InjOn (U.index R fits full x) (↑(insert x (U.neighbors R fits full x))) := by
  let f := U.coord R fits x
  let A := U.candidates R fits full x
  let base := (U.parts R fits x).1
  have info (i : (U.graph R fits).V) (hi : i ∈ insert x (U.neighbors R fits full x)) :
      f i ∈ insert (f x) (A : Set _) ∧
        (f i).1.elim base (U.post.nav base) = (U.parts R fits i).1 := by
    have hm : (U.parts R fits i).1 ∈ insert base (U.adj full base) := by
      rcases mem_insert.mp hi with rfl | hi
      · exact mem_insert_self ..
      · exact U.parent_mem R fits full hi
    refine ⟨?_, ?_⟩
    · by_cases he : f i = f x
      · exact .inl he
      · have hi' := (mem_insert.mp hi).resolve_left (mt (congrArg f) he)
        exact .inr (mem_erase.mpr ⟨he, mem_image_of_mem _ hi'⟩)
    · change (U.chart.label base _).elim base _ = _
      rw [P.chart]
      refine label_spec _ ((mem_insert.mp hm).imp_right (fun h => ?_))
      -- 推导：从 `(P.links _ _).mp h` 中取出 `j, hj, _`。
      obtain ⟨j, hj, _⟩ := (P.links _ _).mp h
      exact ⟨j, hj⟩
  intro i hi j hj he
  obtain ⟨hi, di⟩ := info i hi
  obtain ⟨hj, dj⟩ := info j hj
  have hh : f i = f j := number_inj A (f x) hi hj (congrArg Fin.val he)
  apply (U.parts R fits).injective
  exact Prod.ext (di.symm.trans (hh ▸ dj)) (congrArg (fun t => t.2) hh)

namespace Preview

variable {U} {V : Setup S h u a Δ D Y w B'} {full : Bool} {n k : ℕ}
    {P : U.Reading full} {Q : V.Reading full} {T : Relation U V} (p : Preview P Q T n)
    (R : Rotor F Y w) (fu : U.Fits R c) (fv : V.Fits R c)
    {x x' : (U.graph R fu).V} {y y' : (V.graph R fv).V}
    (hk : k + 4 ≤ n) (hr : T k (U.parts R fu x).1 (V.parts R fv y).1)
    (he : (U.parts R fu x).2 = (V.parts R fv y).2)
    (hr' : T n (U.parts R fu x').1 (V.parts R fv y').1)
    (he' : (U.parts R fu x').2 = (V.parts R fv y').2)

include p hk hr he hr' he'

-- 读法：`y'` 属于 `V.neighbors R fv mode y`。
private theorem neighbor_forward (mode : Bool) (hm : mode = true → full = true)
    (hx : x' ∈ U.neighbors R fu mode x) : y' ∈ V.neighbors R fv mode y := by
  obtain ⟨z, hz, ht, heq⟩ := p.adjacent R fu fv mode hm hk hr he hx
  have same : z = y' := (V.parts R fv).injective (Prod.ext
    ((p.same (p.widen (by omega) ht) hr').mp rfl) (heq.symm.trans he'))
  rwa [same] at hz

-- 读法：`x' ∈ U.neighbors R fu mode x` 与 `y' ∈ V.neighbors R fv mode y` 等价。
theorem neighbors_iff (mode : Bool) (hm : mode = true → full = true) :
    x' ∈ U.neighbors R fu mode x ↔ y' ∈ V.neighbors R fv mode y :=
  ⟨p.neighbor_forward R fu fv hk hr he hr' he' mode hm,
   p.symm.neighbor_forward R fv fu hk hr he.symm hr' he'.symm mode hm⟩

omit he in
-- 读法：`U.coord R fu x x'` 等于 `V.coord R fv y y'`。使用 `Prod.ext` 给出的结论。
private theorem same_coord : U.coord R fu x x' = V.coord R fv y y' :=
  Prod.ext (p.labels (by omega) hr hr') he'

omit hr' he' in
-- 读法：`(U.neighbors R fu full x).image (U.coord R fu x)` 包含于 `(V.neighbors R fv full y).image (V.coord R fv y)`。这里调用 `mem_image.mpr`。
private theorem image_sub :
    (U.neighbors R fu full x).image (U.coord R fu x) ⊆
      (V.neighbors R fv full y).image (V.coord R fv y) := by
  intro a ha
  obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
  obtain ⟨b, hb, ht, heq⟩ := p.adjacent R fu fv full id hk hr he hz
  exact mem_image.mpr ⟨b, hb, (p.same_coord R fu fv hk hr (p.widen (by omega) ht) heq).symm⟩

-- 读法：`U.index R fu full x x'` 等于 `V.index R fv full y y'`。按 `Fin.ext` 的外延性准则比较各分量。
theorem idx_match : U.index R fu full x x' = V.index R fv full y y' := by
  have hset := subset_antisymm (p.image_sub R fu fv hk hr he)
    (p.symm.image_sub R fv fu hk hr he.symm)
  have self := p.same_coord R fu fv hk hr (p.widen (by omega) hr) he
  have eq := p.same_coord R fu fv hk hr hr' he'
  apply Fin.ext
  change number (U.candidates R fu full x) _ = number (V.candidates R fv full y) _
  unfold candidates
  rw [self, hset, eq]

end Preview
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 由图首部与各块的决策重组重置结果

**英文原文**

Reassembling a reset from graph headers and block decisions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
variable {F : Type} (A D : Template F)

-- 读法：在后续公式中，`graph` 是 `Format.pair (Neighborhood.Rows D.scheme.m D.scheme.d) (.vec D.scheme.m (.pair (.pair .bit .bit) (Group.Flags D.scheme.d)))` 的缩写。
abbrev graph := Format.pair (Neighborhood.Rows D.scheme.m D.scheme.d)
  (.vec D.scheme.m (.pair (.pair .bit .bit) (Group.Flags D.scheme.d)))

-- 读法：`header` 的取值由 `(D.nav r, fun v => ((D.live r v, D.frozen r v), D.flags r v))` 给出。
def header (r : D.format.obj) : (graph D).obj :=
  (D.nav r, fun v => ((D.live r v, D.frozen r v), D.flags r v))

-- 读法：在后续公式中，`body` 是 `Format.vec D.scheme.m (.vec D.scheme.h (output A D))` 的缩写。
abbrev body := Format.vec D.scheme.m (.vec D.scheme.h (output A D))

-- 读法：`assemble` 的结果类型为 `(whole A D).obj`。
def assemble (r : (Format.pair (graph D) (body A D)).obj) : (whole A D).obj :=
  ((fun v => (r.1.1 v, fun j => (r.2 v j).1.1),
    fun v => ((r.1.2 v).1, (r.1.2 v).2, fun j => (r.2 v j).1.2)),
    fun v j => (r.2 v j).2)

-- 读法：`assemble A D (header D x.1, part A D x)` 等于 `x`。两端由定义化简为同一项。
theorem assemble_part (x : (whole A D).obj) :
    assemble A D (header D x.1, part A D x) = x := rfl

-- 读法：`assembleCost` 的取值由 `(Format.pair (graph D) (body A D)).width + 2 * (whole A D).width` 给出。
def assembleCost := (Format.pair (graph D) (body A D)).width + 2 * (whole A D).width

-- 读法：在 `F` 上按格式 `(.pair (graph D) (body A D))`、`(whole A D)` 编码输入输出，映射 `(assemble A D)` 的电路规模至多为 `(assembleCost A D)`。这里调用 `Circuit.project`。
theorem assemble_net [Field F] :
    Circuit F (.pair (graph D) (body A D)) (whole A D) (assemble A D) (assembleCost A D) := by
  let idx : (whole A D).pins → (Format.pair (graph D) (body A D)).pins
    | .inl (.inl (v, .inl j)) => .inl (.inl (v, j))
    | .inl (.inl (v, .inr (b, j))) => .inr (v, b, .inl (.inl j))
    | .inl (.inr (v, .inl j)) => .inl (.inr (v, .inl j))
    | .inl (.inr (v, .inr (.inl j))) => .inl (.inr (v, .inr j))
    | .inl (.inr (v, .inr (.inr (b, j)))) => .inr (v, b, .inl (.inr j))
    | .inr (v, b, j) => .inr (v, b, .inr j)
  apply Circuit.project idx
  rintro _ ((⟨v, j|⟨b, j⟩⟩|⟨v, j|j|⟨b, j⟩⟩)|⟨v, b, j⟩) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-!
# 对每个宿主的短字段应用选定的混合器

**英文原文**

Applying a selected mixer to the short fields of every host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
variable {F : Type} (A : Template F) (a k : ℕ) (ha : a ≤ A.scheme.h)
local notation "G" => Mixing.Groups A.scheme.h a (data A) A.scheme.m
local notation "D" => Format.pair (Format.addr A.scheme.h) (Mixing.Data A.scheme.h (data A) A.scheme.m)
local notation "R" => pair A k
local notation "B" => bank A a k

-- 读法：`split` 的取值由 `(x.2.1, fun v i => ((x.1.1 v).2 i, A.counter x.1 v i))` 给出。
private def split (x : (R).obj) : (D).obj :=
  (x.2.1, fun v i => ((x.1.1 v).2 i, A.counter x.1 v i))

-- 读法：输入 `v` 时返回 `(A.nav x.1.1 v, fun i => (x.1.2.2 v, A.flags x.1.1 v, x.2 v i))`。
private def join (x : (Format.pair R G).obj) : (B).obj :=
  fun v => (A.nav x.1.1 v, fun i => (x.1.2.2 v, A.flags x.1.1 v, x.2 v i))

-- 读法：`packetCost` 的取值由 `10 * (R).width + 2 * (D).width + (G).width + 2 * (B).width + Mixing.applyCost A.scheme.h (data A) A.scheme.m` 给出。
def packetCost := 10 * (R).width + 2 * (D).width + (G).width + 2 * (B).width + Mixing.applyCost A.scheme.h (data A) A.scheme.m

variable [Field F]

-- 读法：在 `F` 上按格式 `R`、`D` 编码输入输出，映射 `(split A k)` 的电路规模至多为 `((R).width + 2 * (D).width)`。这里调用 `Circuit.project`。
private theorem split_net : Circuit F R D (split A k) ((R).width + 2 * (D).width) := by
  let idx : (D).pins → (R).pins
    | .inl j => .inr (.inl j)
    | .inr (v, i, .inl j) => .inl (.inl (v, .inr (i, j)))
    | .inr (v, i, .inr j) => .inl (.inr (v, .inr (.inr (i, j))))
  exact Circuit.project idx (by rintro _ (j|⟨v, i, j|j⟩) <;> rfl)

-- 读法：在 `F` 上按格式 `(.pair R G)`、`B` 编码输入输出，映射 `(join A a k)` 的电路规模至多为 `((Format.pair R G).width + 2 * (B).width)`。这里调用 `Circuit.project`。
private theorem join_net : Circuit F (.pair R G) B (join A a k) ((Format.pair R G).width + 2 * (B).width) := by
  let idx : (B).pins → (Format.pair R G).pins
    | (v, .inl j) => .inl (.inl (.inl (v, .inl j)))
    | (v, .inr (_, .inl j)) => .inl (.inr (.inr (v, j)))
    | (v, .inr (_, .inr (.inl j))) => .inl (.inl (.inr (v, .inr (.inl j))))
    | (v, .inr (i, .inr (.inr j))) => .inr (v, i, j)
  exact Circuit.project idx (by rintro _ ⟨v, j|⟨i, j|j|j⟩⟩ <;> rfl)

-- 读法：在 `F` 上按格式 `R`、`B` 编码输入输出，映射 `(packet A a k ha)` 的电路规模至多为 `(packetCost A a k)`。这里调用 `net.mono`。
theorem packet_net : Circuit F R B (packet A a k ha) (packetCost A a k) := by
  have mix := (split_net A k).comp (Mixing.apply_mixer A.scheme.h a ha (data A) A.scheme.m)
  have net := ((Circuit.id F R).pair mix).comp (join_net A a k)
  exact net.mono (by rw [packetCost, Format.width_pair R G]; omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end
