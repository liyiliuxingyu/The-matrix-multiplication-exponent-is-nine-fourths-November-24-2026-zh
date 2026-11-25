-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Rig
import OAI.LinearAlgebra.MatrixExponent.Protocol.Focus
import OAI.LinearAlgebra.MatrixExponent.Transport.Table
import OAI.LinearAlgebra.MatrixExponent.Protocol.Wired
import OAI.LinearAlgebra.MatrixExponent.Routing.Packets

/-!
# 分支的局部配置

库存协议在抽象坐标中计算一个局部线性核。需求坐标从两个外部数组中读取，供给坐标从为其分配的物理插口读取。

**英文原文**

Local profiles of a branch

The inventory protocol computes a local linear kernel in abstract
coordinates. Read its demand coordinates in the two exterior arrays
and its supply coordinates at their assigned physical sockets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig

open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m h : ℕ} (T : Routes F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h))

-- 读法：在后续公式中，`arena` 是 `letI := T.action h σ T.params.balls (Site h)` 的缩写。
abbrev arena :=
  letI := T.action h σ
  T.params.balls (Site h)

-- 读法：在后续公式中，`Path` 是 `letI := T.action h σ s.clock.path (Site h)` 的缩写。
abbrev Path :=
  letI := T.action h σ
  s.clock.path (Site h)

-- 读法：在后续公式中，`requests` 是 `letI := T.action h σ s.widthAt u` 的缩写。
abbrev requests (u : Path T s σ) : (arena T σ).Edge → ℕ :=
  letI := T.action h σ
  s.widthAt u

-- 读法：在后续公式中，`choose` 是 `letI := T.action h σ s.clock.selector u` 的缩写。
abbrev choose (u : Path T s σ) : Site h → B s.clock.bits :=
  letI := T.action h σ
  s.clock.selector u

-- 读法：在后续公式中，`place` 是 `letI := T.action h σ s.endpoints u` 的缩写。
abbrev place (u : Path T s σ) : Protocol.End (requests T s σ u) ↪ Port h s.p :=
  letI := T.action h σ
  s.endpoints u

-- 读法：在后续公式中，`src` 是 `(arena T σ).name e.1 e.2.val.1` 的缩写。
abbrev src (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.1
-- 读法：在后续公式中，`dst` 是 `(arena T σ).name e.1 e.2.val.2` 的缩写。
abbrev dst (e : (arena T σ).Edge) := (arena T σ).name e.1 e.2.val.2

-- 读法：在后续公式中，`initial` 是 `Protocol.Demand F σ s.clock.width` 的缩写。
abbrev initial := Protocol.Demand F σ s.clock.width
-- 读法：在后续公式中，`result` 是 `Protocol.Links F (src T σ) (dst T σ) (requests T s σ u)` 的缩写。
abbrev result (u : Path T s σ) := Protocol.Links F (src T σ) (dst T σ) (requests T s σ u)

-- 读法：`(arena T σ).name i ((arena T σ).shape i).dst` 等于 `inflate h σ i`。这里调用 `T.target_action`。
theorem target_at (i : Site h) :
    (arena T σ).name i ((arena T σ).shape i).dst = inflate h σ i := by
  let _ := T.action h σ
  change (market _ _ _ _ _).name i ((market _ _ _ _ _).shape i).dst = _
  rw [market_dst, inv_inv]
  exact T.target_action h σ i

-- 读法：`execute` 的构造用到 `Protocol.program`、`a.balls`、`a.offers`。
def execute {G J I : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [Fintype I] [Nonempty I] [MulAction G I] :
    let b := a.balls I
    (Protocol.Board.orders (Protocol.request b a.table)
      (Stock.copies (b.payload a.table) s.clock.width)).Expansion
      (fun u : s.clock.path I => Protocol.Board.orders (Protocol.edge F b) (s.widthAt u)) :=
  Protocol.program (a.balls I) a.offers
    (marketPorts (I := I) a.core a.radius a.unit g a.reach s.w s.hw)
    s.clock.height a.nz s.clock.room s.clock.μ a.path s.clock.width
    (a.ready I) a.local_supply (s.clock.runs I)

-- 读法：`transfer` 的取值由 `(s.execute (I := Site h)).rename (Protocol.demandRename (a.balls (Site h)) a.table σ s.clock.width hc) (fun _ => .refl _)` 给出。
private def transfer {G J : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [MulAction G (Site h)]
    (hc : ∀ i : Site h, (a.balls (Site h)).name i ((a.balls (Site h)).shape i).dst = inflate h σ i) :
    (Protocol.Demand F σ s.clock.width).Expansion
      (fun u : s.clock.path (Site h) =>
        Protocol.Board.orders (Protocol.edge F (a.balls (Site h))) (s.widthAt u)) :=
  (s.execute (I := Site h)).rename
    (Protocol.demandRename (a.balls (Site h)) a.table σ s.clock.width hc) (fun _ => .refl _)

-- 读法：`operator` 的结果类型为 `(initial T s σ).Expansion (result T s σ)`。
def operator : (initial T s σ).Expansion (result T s σ) := by
  let _ := T.action h σ
  exact transfer σ s (target_at T σ)

-- 读法：当 `(x.val.2 : Bool) = true` 成立时取 `.inr x.val.1.2`，否则取 `.inl x.val.1.2`。
def side (i : Site h) (x : (initial T s σ).localPort i) : Fin s.clock.width ⊕ Fin s.clock.width :=
  if (x.val.2 : Bool) = true then .inr x.val.1.2 else .inl x.val.1.2

-- 读法：`channel` 的取值由 `(place T s σ u x.val).2` 给出。
def channel (u : Path T s σ) (i : Site h) (x : (result T s σ u).localPort i) : B s.p :=
  (place T s σ u x.val).2

-- 读法：结构的字段包括 `h`、`σ`、`u`、`i`。
structure Example where
  h : ℕ
  σ : Equiv.Perm (B h)
  u : Path T s σ
  i : Site h

-- 读法：`sample` 的取值由 `((operator T s t.σ).kernel t.u t.i).pull (side T s t.σ t.i) (channel T s t.σ t.u t.i)` 给出。
def sample (t : Example T s) : Profile F s.p s.clock.width :=
  ((operator T s t.σ).kernel t.u t.i).pull (side T s t.σ t.i) (channel T s t.σ t.u t.i)

-- 读法：`observed` 的取值由 `⟨@Root.mk _ _ _ (T.action t.h t.σ) t.i, choose T s t.σ t.u⟩` 给出。
def observed (t : Example T s) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action t.h t.σ) t.i, choose T s t.σ t.u⟩

-- 读法：`Compatible` 的结果类型为 `Prop`。
def Compatible : Prop :=
  ∃ E : Finset (controllers F T.embed), ∀ x y : Example T s,
    let u := observed T s x
    let v := observed T s y
    Root.Agree E u.toRoot v.toRoot →
    (∀ i ∈ E, u.mark (u.label i) = v.mark (v.label i)) → sample T s x = sample T s y

end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# 局部配置的有限选项集

配置仅能通过有限多个观测量依赖于分支。记录这些观测、局部准入条件和启用掩码。没有代表元的类赋予权重零。

**英文原文**

The finite menu of local profiles

A profile can depend on the branch only through finitely many
observations. Record these observations, the local guard, and the
enable mask. A class with no representative receives weight zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig

open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m : ℕ} (T : Routes F m) (s : Rig T.params)

-- 读法：在后续公式中，`active` 是 `(s.bank.program T.params.unit _ T.params.reach s.count x j).1` 的缩写。
abbrev active (x : s.clock.Input) (j : B s.p) :=
  (s.bank.program T.params.unit _ T.params.reach s.count x j).1

-- 读法：`masked` 的取值由 `(sample T s v).mask (s.clock.guard s.w (observed T s v)) (active T s (observed T s v))` 给出。
def masked (v : Example T s) : Profile F s.p s.clock.width :=
  (sample T s v).mask (s.clock.guard s.w (observed T s v)) (active T s (observed T s v))

-- 读法：结构的字段包括 `l`、`key`、`local_key`、`table`、`fast`。
structure Palette where
  l : ℕ
  key : s.clock.Input → B l
  local_key : Decor.Local key
  table : B l → Profile F s.p s.clock.width
  fast : ∀ i, Protocol.Frame.Fast (table i)
  agrees : ∀ v, table (key (observed T s v)) = masked T s v
  valid : ∀ x z a c, table (key x) z a c ≠ 0 →
    s.clock.guard s.w x = true ∧ ∀ j, active T s x j ≠ true → ∀ i, c j i = false

-- 读法：在后续公式中，`Pattern` 是 `((↥E → ↥E → Bool) × (↥E → B s.clock.bits)) × Bool × (B s.p → Bool)` 的缩写。
private abbrev Pattern (E : Finset (controllers F T.embed)) :=
  ((↥E → ↥E → Bool) × (↥E → B s.clock.bits)) × Bool × (B s.p → Bool)

-- 读法：`pattern` 的取值由 `((fun i j => x.see i j, fun i => x.mark (x.label i)), s.clock.guard s.w x, active T s x)` 给出。
private def pattern (E : Finset (controllers F T.embed)) (x : s.clock.Input) : Pattern T s E :=
  ((fun i j => x.see i j, fun i => x.mark (x.label i)), s.clock.guard s.w x, active T s x)

-- 读法：要证明的命题是 `Decor.Local (pattern T s E)`。这里调用 `ho.pair`。
private theorem pattern_local (E : Finset (controllers F T.embed)) :
    Decor.Local (pattern T s E) := by
  have ho : Decor.Local (fun x : s.clock.Input => (pattern T s E x).1) :=
    ⟨E, fun _ _ hh hm => Prod.ext (funext fun i => funext fun j => hh _ i.property _ j.property)
      (funext fun i => hm _ i.property)⟩
  have he := s.bank.program_local T.params.unit _ T.params.reach s.count
    (s.clock.count_local s.w s.j₀)
  exact ho.pair ((s.clock.guard_local s.w).pair (he.map (fun v j => (v j).1)))

-- 读法：`(Palette T s)` 有元素。
theorem palette (he : Compatible T s) : Nonempty (Palette T s) := by
  obtain ⟨E, hE⟩ := he
  let code := Coloring.encode (Pattern T s E)
  let k := code ∘ pattern T s E
  have same (x y : Example T s) (eq : k (observed T s x) = k (observed T s y)) :
      masked T s x = masked T s y := by
    have e := code.injective eq
    have hs := hE x y
      (fun i hi j hj => congrArg (fun z => z.1.1 ⟨i, hi⟩ ⟨j, hj⟩) e)
      (fun i hi => congrArg (fun z => z.1.2 ⟨i, hi⟩) e)
    exact congrArg₂ (fun (f : Profile F s.p s.clock.width) v => f.mask v.1 v.2)
      hs (congrArg Prod.snd e)
  let off : Profile F s.p s.clock.width := Protocol.Frame.diagonal (fun _ _ => 0)
  let f i := if h : ∃ v, k (observed T s v) = i then masked T s h.choose else off
  refine ⟨⟨_, k, (pattern_local T s E).map code, f, ?_, ?_, ?_⟩⟩
  · intro i
    dsimp only [f]
    split
    · rename_i hh
      apply Profile.mask_fast
      exact ((operator T s hh.choose.σ).fast _ _).pull _ _
    · exact Protocol.Frame.fast_diagonal _
  · intro v
    -- 推导：记下中间结论 `hv`：`∃ u, k (observed T s u) = k (observed T s v)`。
    have hv : ∃ u, k (observed T s u) = k (observed T s v) := ⟨v, rfl⟩
    simp only [f, dite_eq_left hv]
    exact same _ _ hv.choose_spec
  · intro x z a c hn
    dsimp only [f] at hn
    split at hn
    · rename_i hv
      have eq := congrArg Prod.snd (code.injective hv.choose_spec)
      obtain ⟨hg, ha⟩ := Prod.mk.inj eq
      unfold masked Profile.mask at hn
      rw [hg, ha] at hn
      by_contra hh
      exact hn (ite_eq_right hh)
    · simp [off, Protocol.Frame.diagonal] at hn

end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# 在每个位点解析配置指令和槽位指令

**英文原文**

Resolving profile and slot commands at every site
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m h : ℕ} (T : Routes F m) (s : Rig T.params)
    (P : Palette T s)

-- 读法：在后续公式中，`Selectors` 是 `Format.vec (h + 1) (.addr s.clock.bits)` 的缩写。
abbrev Selectors (h : ℕ) := Format.vec (h + 1) (.addr s.clock.bits)
-- 读法：在后续公式中，`Commands` 是 `Controls h s.p (.addr P.l)` 的缩写。
abbrev Commands (h : ℕ) := Controls h s.p (.addr P.l)

-- 读法：`atSite` 的取值由 `⟨@Root.mk _ _ _ (T.action h σ) i, z⟩` 给出。
def atSite (σ : Equiv.Perm (B h)) (z : (Selectors T s h).obj) (i : Site h) : s.clock.Input :=
  ⟨@Root.mk _ _ _ (T.action h σ) i, z⟩

-- 读法：结构的字段包括 `f`、`group`、`resolves`、`groups`。
structure Engine (h : ℕ) where
  f : ((Perm h).pair (Selectors T s h)).obj → (Commands T s P h).obj
  group : Port h s.p → ℕ
  resolves : ∀ σ : Equiv.Perm (B h), ∀ z i, f (σ, z) i =
    Decor.resolve (s.program P.key (atSite T s σ z i))
      (fun j => (T.action h σ).smul (s.bank.hop j) i)
  groups : ∀ σ x y i j, s.bank.generator T.params.unit i = s.bank.generator T.params.unit j →
    (T.action h σ).smul (s.bank.generator T.params.unit i).val x = y →
    group (x, i) = group (y, j)

namespace Engine

variable {T s P} (H : Engine T s P h) (σ : Equiv.Perm (B h))

-- 读法：在后续公式中，`system` 是 `selector := Selectors T s h config := .addr P.l group := H.group dispatch := H.f kernel i := (P.table i).apply z` 的缩写。
abbrev system (z : ℕ) : System F h s.p s.clock.width (2 ^ z) where
  selector := Selectors T s h
  config := .addr P.l
  group := H.group
  dispatch := H.f
  kernel i := (P.table i).apply z

-- 读法：`(H.f (σ, z) i).1` 等于 `P.key (atSite T s σ z i)`。
theorem key (z : (Selectors T s h).obj) (i : Site h) :
    (H.f (σ, z) i).1 = P.key (atSite T s σ z i) := by rw [H.resolves]; rfl

-- 读法：要证明的命题是 `letI`。用函数外延性比较等号两侧在 `⟨i, j⟩` 处的取值。
theorem orders (z : (Selectors T s h).obj) :
    letI := T.action h σ
    commands (H.f (σ, z)) = s.bank.orders T.params.unit _ T.params.reach s.count z := by
  funext ⟨i, j⟩
  unfold commands
  rw [H.resolves]
  rfl

-- 读法：`(i, j) ∈ Enabled (commands (H.f (σ, z)))` 与 `active T s (atSite T s σ z i) j = true` 等价。
theorem enabled (z : (Selectors T s h).obj) (i : Site h) (j : B s.p) :
    (i, j) ∈ Enabled (commands (H.f (σ, z))) ↔ active T s (atSite T s σ z i) j = true := by
  simp only [Enabled, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [H.orders]
  rfl

-- 读法：`placement` 的结果类型为 `Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) H.group (commands (H.f (σ, choose T s σ u)))`。
def placement (u : Path T s σ) :
    Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) H.group
      (commands (H.f (σ, choose T s σ u))) := by
  let _ := T.action h σ
  exact s.bank.placement T.params.unit _ T.params.reach s.count (s.clock.selector u) (s.widthAt u)
    (s.bounded u) (s.clock.count_branch s.w s.j₀ s.hw s.h₀ u)
    H.group (H.groups σ) _ (H.orders σ _)

end Engine
end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# 在物理引脚处读取分支核

**英文原文**

Reading a branch kernel at its physical pins
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m h z : ℕ} (T : Routes F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h)) (u : Path T s σ) (i : Site h)

-- 读法：用函数外延性比较等号两侧在 `⟨⟨⟨j, k⟩, b⟩, e⟩ t` 处的取值。
theorem sample_apply {group : Port h s.p → ℕ} {a : Orders h s.p}
    (P : Protocol.Placement (src T σ) (dst T σ) (requests T s σ u) group a)
    (hP : P.embed = place T s σ u) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) :
    (sample T s ⟨h, σ, u, i⟩).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i (P.inside c)) := by
  unfold sample Profile.apply Protocol.Frame.pull
  refine congrArg₂ ((operator T s σ).kernel u i z) ?_ ?_
  · funext ⟨⟨⟨j, k⟩, b⟩, e⟩ t
    let v := Sum.elim (Function.curry (x i)) (Function.curry (y i))
    cases b
    -- 推导：记下中间结论 `hs`：`side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩ = .inl k`。
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩ = .inl k := ite_eq_right Bool.false_ne_true
      change v (side T s σ i ⟨⟨⟨j, k⟩, false⟩, e⟩) t = x j (k, t)
      rw [hs]
      exact congrArg (fun l => x l (k, t)) (show j = i from e).symm
    · have hs : side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩ = .inr k := ite_eq_left rfl
      change v (side T s σ i ⟨⟨⟨j, k⟩, true⟩, e⟩) t = y (inflate h σ j) (k, t)
      rw [hs]
      exact congrArg (fun l => y l (k, t)) (show inflate h σ j = i from e).symm
  · funext k t
    have he : (P.embed k.val).1 = i := (P.owner _).trans k.property
    change c i ((place T s σ u k.val).2, t) = c (P.embed k.val).1 ((P.embed k.val).2, t)
    rw [he, hP]

end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# 编程实现的运输过程的正确性

每个保留的选择器恰好描述一个合法分支。将该分支已停用的槽位固定为零，在其余槽位上执行分支核的物理副本。

**英文原文**

Correctness of the programmed transport

Every surviving selector describes exactly one legal branch. Its
disabled slots are pinned to zero. On all other slots the program
executes the physical copy of the branch kernel.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F] {m h z : ℕ}

-- 读法：`(s.clock.selector (I := I))` 是单射。使用 `a.balls` 给出的结论。
private theorem injective_selector {G J I : Type} [Group G] {U : J → Subgroup G} {g : G}
    {a : Parameters F U g} (s : Rig a) [Fintype I] [MulAction G I] :
    Function.Injective (s.clock.selector (I := I)) :=
  (a.balls I).selector_injective a.offers s.clock.batch s.clock.bound s.clock.μ a.path s.clock.width

namespace Engine
variable {T : Routes F m} {s : Rig T.params} {P : Palette T s} (H : Engine T s P h)
    (σ : Equiv.Perm (B h))

-- 读法：`codes` 的结果类型为 `Path T s σ ↪ (Selectors T s h).obj`。
private def codes : Path T s σ ↪ (Selectors T s h).obj := by
  let _ := T.action h σ
  exact ⟨choose T s σ, s.injective_selector⟩

-- 读法：`(∀ i, s.clock.guard s.w (atSite T s σ t i) = true)` 与 `∃ u, choose T s σ u = t` 等价。
private theorem eligible (t : (Selectors T s h).obj) :
    (∀ i, s.clock.guard s.w (atSite T s σ t i) = true) ↔ ∃ u, choose T s σ u = t := by
  let _ := T.action h σ
  have ht := s.clock.guard_iff s.w s.hw t
  refine ⟨fun h => (ht.mp h).exists, fun ⟨u, hu⟩ => ht.mpr ⟨u, hu, ?_⟩⟩
  exact fun v hv => s.injective_selector (hv.trans hu.symm)

-- 读法：结论为 `(P.table (H.f (σ, choose T s σ u) i).1).apply z (x i) (y i) (c i) = (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y)) ((result T s σ u).view i ((H.placement σ u).inside c))`。
private theorem agrees (u : Path T s σ) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hc : Protocol.Padded (commands (H.f (σ, choose T s σ u))) c)
    (i : Site h) :
    (P.table (H.f (σ, choose T s σ u) i).1).apply z (x i) (y i) (c i) =
      (operator T s σ).kernel u i z ((initial T s σ).view i (Protocol.outside σ _ x y))
        ((result T s σ u).view i ((H.placement σ u).inside c)) := by
  let e : Example T s := ⟨h, σ, u, i⟩
  rw [H.key]
  change (P.table (P.key (observed T s e))).apply _ _ _ _ = _
  rw [P.agrees]
  have hg : s.clock.guard s.w (observed T s e) = true :=
    (eligible σ (choose T s σ u)).mpr ⟨u, rfl⟩ i
  have hy : ∀ j, active T s (observed T s e) j ≠ true → ∀ k, c i (j, k) = false := by
    intro j hj
    exact hc (i, j) (mt (H.enabled σ _ i j).mp hj)
  trans (sample T s e).apply z (x i) (y i) (c i)
  · exact ite_eq_left ⟨hg, hy⟩
  · exact sample_apply T s σ u i _ rfl x y c

-- 读法：`(∃ u, choose T s σ u = t)` 与 `Protocol.Padded (commands (H.f (σ, t))) c` 同时成立。这里调用 `P.valid`。
private theorem surviving (t : (Selectors T s h).obj) (x y : Site h → Data s.clock.width (2 ^ z))
    (c : Site h → Channels s.p (2 ^ z)) (hne : (H.system z).value (H.f (σ, t)) x y c ≠ 0) :
    (∃ u, choose T s σ u = t) ∧ Protocol.Padded (commands (H.f (σ, t))) c := by
  have hi (i : Site h) : s.clock.guard s.w (atSite T s σ t i) = true ∧
      ∀ j, active T s (atSite T s σ t i) j ≠ true → ∀ k, c i (j, k) = false := by
    have hw := Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ _)
    change (P.table (H.f (σ, t) i).1).apply z (x i) (y i) (c i) ≠ 0 at hw
    rw [H.key] at hw
    exact P.valid _ _ _ _ hw
  refine ⟨(eligible σ t).mp (fun i => (hi i).1), ?_⟩
  rintro ⟨i, j⟩ hij k
  exact (hi i).2 _ (mt (H.enabled σ t i j).mpr hij) k

-- 读法：`2 * (∑ e, requests T s σ u e)` 不超过 `4812 * s.clock.width * 2 ^ h`。这里调用 `Nat.mul_le_mul_left`。
private theorem width (u : Path T s σ) :
    2 * (∑ e, requests T s σ u e) ≤ 4812 * s.clock.width * 2 ^ h := by
  let _ := T.action h σ
  have he := s.clock.width_total s.w s.hw u
  change (∑ e, requests T s σ u e) ≤ 1203 * Fintype.card (Site h) * s.clock.width at he
  rw [show Fintype.card (Site h) = 2 ^ h * 2 by simp [pow_succ]] at he
  exact (Nat.mul_le_mul_left 2 he).trans_eq (by ring)

-- 读法：要证明的命题是 `(H.system z).Correct 4812`。这里调用 `Protocol.system_correct`。
theorem correct (z : ℕ) : (H.system z).Correct 4812 := by
  apply Protocol.system_correct
  intro σ
  exact ⟨{
    E := (arena T σ).Edge
    I := Path T s σ
    src := src T σ
    dst := dst T σ
    m := requests T s σ
    proc := operator T s σ
    choose := codes σ
    place := H.placement σ
    cost := width σ
    agrees := H.agrees σ
    invalid := H.surviving σ
  }⟩

end Engine
end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# 适用于不同宽度的统一路由

先选高度比，再确定可用选项表。所有依赖于该表的额外开销都可吸收到最终的高度阈值和多项式成本指数中。被传输宽度的上界仍为 4812。

**英文原文**

Uniform routing across widths

Choose a height ratio before fixing the menu. All overhead depending
on the menu can be absorbed into the eventual height cutoff and a
polynomial cost exponent. The bound on transported width stays 4812.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Coloring Transport
open scoped Classical

-- 读法：存在 `m : ℕ`，`0 < m` 与 `∀ K : ℕ, ∀ᶠ h : ℕ in Filter.atTop, h / m + K ≤ h ∧ (↑(h / m + K) : ℝ) ≤ τ * h` 同时成立。这里调用 `Nat.add_le_add`。
private theorem heights (τ : ℝ) (hτ : 0 < τ) :
    ∃ m : ℕ, 0 < m ∧ ∀ K : ℕ, ∀ᶠ h : ℕ in Filter.atTop,
      h / m + K ≤ h ∧ (↑(h / m + K) : ℝ) ≤ τ * h := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (2 / τ))
  have hm' : 2 < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm)
  have ht : 2 ≤ (m : ℝ) * τ := ((div_lt_iff₀ hτ).mp ((le_max_right _ _).trans_lt hm)).le
  refine ⟨m, by omega, fun K => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (K * m)] with h hh
  have he : (h / m + K) * m ≤ 2 * h := by
    rw [add_mul, two_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self h m) hh
  constructor
  · have := (Nat.mul_le_mul_left (h / m + K) hm'.le).trans he
    omega
  · apply le_of_mul_le_mul_right _ (by exact_mod_cast (by omega : 0 < m) : (0 : ℝ) < m)
    have hh' : (↑(h / m + K) : ℝ) * m ≤ 2 * h := by exact_mod_cast he
    exact hh'.trans (by nlinarith only [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg h)])

variable {F : Type} [Field F]

-- 读法：要证明的命题是 `LocalProtocol F`。
theorem local_of_routes
    (routes : ∀ m : ℕ, 0 < m → ∃ (T : Routes F m) (s : Rig T.params), Rig.Compatible T s) :
    LocalProtocol F := by
  refine ⟨4812, fun τ hτ => ?_⟩
  obtain ⟨m, hm, hcut⟩ := heights τ hτ
  obtain ⟨T, s, hr⟩ := routes m hm
  obtain ⟨P⟩ := Rig.palette T s hr
  obtain ⟨d, k, hd⟩ := (s.program_local P.local_key).dispatch (T := T) s.bank.hop
  obtain ⟨c, hc⟩ := profile_weight P.table P.fast
  refine ⟨s.p, s.clock.width, max d c, s.clock.wide, ?_⟩
  filter_upwards [hcut (T.overhead + s.p + 22), Filter.eventually_ge_atTop k] with h hb hk
  -- 推导：从 `hd h hk` 中取出 `f, hf, he`。
  obtain ⟨f, hf, he⟩ := hd h hk
  let b := h / m + T.overhead
  obtain ⟨g, hg, hm⟩ := T.portGroup h b s.p le_rfl (by dsimp [b]; omega)
    (s.bank.generator T.params.unit)
  let engine : Rig.Engine T s P h := ⟨f, g, he, hm⟩
  refine ⟨b + s.p + 22, Nat.add_le_add_right (Nat.le_add_left ..) 22, by dsimp [b]; omega, ?_, fun j _ => ?_⟩
  · simpa [b, Nat.add_assoc] using hb.2
  · refine ⟨engine.system j, engine.correct j, ?_, hf.mono (le_max_left ..), ?_⟩
    · exact fun i => (hg i).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact (hc j).mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right ..)))

end OAI.LinearAlgebra.MatrixExponent.Routing
end
