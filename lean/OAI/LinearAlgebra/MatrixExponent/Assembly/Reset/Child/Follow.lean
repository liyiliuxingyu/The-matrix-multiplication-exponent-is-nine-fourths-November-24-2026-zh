-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Width
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.Model
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Routes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Mixer.Choice
import OAI.LinearAlgebra.MatrixExponent.Assembly.Mixer.Apply
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths

/-!
# 为挂接在各父宿主上的硬件编址

**英文原文**

Addressing the hardware attached to each parent host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
open Coloring Packing

-- 读法：在后续公式中，`Suffix` 是 `Format.pair (.pair .bit .bit) (.vec l (.pair (.pair .bit .bit) (.pair (.addr (d + 1)) (.addr k))))` 的缩写。
abbrev Suffix (d k l : ℕ) :=
  Format.pair (.pair .bit .bit) (.vec l (.pair (.pair .bit .bit) (.pair (.addr (d + 1)) (.addr k))))

-- 读法：在后续公式中，`Input` 是 `Format.pair (Neighborhood.Rows m d) (.vec (m + k) (Suffix d k l))` 的缩写。
abbrev Input (m d k l : ℕ) := Format.pair (Neighborhood.Rows m d) (.vec (m + k) (Suffix d k l))
-- 读法：在后续公式中，`Graph` 是 `Format.pair (Neighborhood.Rows m l) (.vec m (.pair (.pair .bit .bit) (Group.Flags l)))` 的缩写。
abbrev Graph (m l : ℕ) :=
  Format.pair (Neighborhood.Rows m l) (.vec m (.pair (.pair .bit .bit) (Group.Flags l)))

-- 读法：当 `h : hop.val < 2 ^ d` 成立时取 `nav parent ⟨hop.val, h⟩`，否则取 `parent`。
def follow {m d : ℕ} (nav : (Neighborhood.Rows m d).obj) (parent : B m) (hop : B (d + 1)) :=
  if h : hop.val < 2 ^ d then nav parent ⟨hop.val, h⟩ else parent

-- 读法：`build` 的结果类型为 `(Graph (m + k) l).obj`。
def build (m d k l : ℕ) (r : (Input m d k l).obj) : (Graph (m + k) l).obj :=
  (fun i j =>
    let parent := (Match.rowIndex m k i).1
    let q := ((r.2 i).2 j).2
    (Match.rowIndex m k).symm (follow r.1 parent q.1, q.2),
   fun i => ((r.2 i).1, fun j => ((r.2 i).2 j).1))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
end

section
/-!
# 重置后图首部所表示的信息

**英文原文**

Information represented by the graph header after a reset
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
open Packing Coloring

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {a u m d : ℕ}

-- 读法：结构的字段包括 `live`、`frozen`、`closed`、`reciprocal`、`edge`。
structure Describes (full : Bool) (G : HostNet F L a u) (host : G.V ↪ B m)
    (index : G.V → G.V → B d) (g : (Graph m d).obj) : Prop where
  live : ∀ i, (g.2 i).1.1 = true ↔ i ∈ Set.range host
  frozen : ∀ v, (g.2 (host v)).1.2 = true ↔ G.frozen v
  closed : ∀ v j, g.1 (host v) j ∈ Set.range host
  reciprocal : ∀ i j, g.1 i j ≠ i → ∃! l, g.1 (g.1 i j) l = i
  edge : ∀ v z, z ∈ (if full then G.N else G.C) v ↔
    ∃ j, g.1 (host v) j = host z ∧ ((g.2 (host v)).2 j).1 = true
  core : ∀ v z, z ∈ G.C v ↔ ∃ j, g.1 (host v) j = host z ∧ ((g.2 (host v)).2 j).2 = true
  hop : ∀ v z, z ∈ G.C v → g.1 (host v) (index v z) = host z

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
end

/-!
# 依据活跃列与空置列验证图首部

**英文原文**

Certifying the graph header from the active and vacant columns
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
open Packing Coloring
open scoped Classical

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {a u m d : ℕ}
  (full : Bool) (G : HostNet F L a u) (host : G.V ↪ B m)
  (index : G.V → G.V → B d) (g : (Graph m d).obj)
local notation "adj" => (ite (full = true) G.N G.C)

-- 读法：要证明的命题是 `Describes full G host index g`。对 `full` 分类讨论。
theorem describes_of_columns
    (live : ∀ i, (g.2 i).1.1 = true ↔ i ∈ Set.range host)
    (frozen : ∀ v, (g.2 (host v)).1.2 = true ↔ G.frozen v)
    (idle : ∀ i ∉ Set.range host, ∀ j, g.1 i j = i)
    (used : ∀ v w, w ∈ adj v → g.1 (host v) (index v w) = host w ∧
      (g.2 (host v)).2 (index v w) = (true, decide (w ∈ G.C v)))
    (spare : ∀ v j, (∀ w ∈ adj v, index v w ≠ j) →
      g.1 (host v) j = host v ∧ (g.2 (host v)).2 j = (false, false)) :
    Describes full G host index g := by
  have sym : ∀ v w, w ∈ adj v → v ∈ adj w := by
    cases full
    · exact G.cs
    · exact G.ns
  have sub : ∀ v, G.C v ⊆ adj v := by
    cases full
    · exact fun _ _ h => h
    · exact G.sub
  have split (v j) :
      (∃ w ∈ adj v, index v w = j) ∨ (g.1 (host v) j = host v ∧ (g.2 (host v)).2 j = (false, false)) := by
    by_cases h : ∃ w ∈ adj v, index v w = j
    · exact .inl h
    exact .inr (spare v j (fun w hw he => h ⟨w, hw, he⟩))
  refine ⟨live, frozen, ?_, ?_, ?_, ?_, fun v w hw => (used v w (sub v hw)).1⟩
  · intro v j
    rcases split v j with ⟨w, hw, rfl⟩|⟨he, _⟩
    · exact ⟨w, (used _ _ hw).1.symm⟩
    · exact ⟨v, he.symm⟩
  · intro i j hn
    by_cases hi : i ∈ Set.range host
    swap
    · exact (hn (idle i hi j)).elim
    -- 推导：从 `hi` 中取出 `v, rfl`。
    obtain ⟨v, rfl⟩ := hi
    rcases split v j with ⟨w, hw, rfl⟩|⟨he, _⟩
    swap
    · exact (hn he).elim
    rw [(used v w hw).1] at hn ⊢
    refine ⟨index w v, (used _ _ (sym _ _ hw)).1, fun l hl => ?_⟩
    rcases split w l with ⟨z, hz, rfl⟩|⟨he, _⟩
    · exact congrArg (index w) (host.injective ((used w z hz).1.symm.trans hl))
    · exact (hn (he.symm.trans hl)).elim
  · intro v w
    constructor
    · intro h
      exact ⟨index v w, (used v w h).1, congrArg Prod.fst (used v w h).2⟩
    rintro ⟨j, hj, h⟩
    rcases split v j with ⟨z, hz, rfl⟩|⟨_, he⟩
    · exact host.injective ((used v z hz).1.symm.trans hj) ▸ hz
    · rw [he] at h; cases h
  · intro v w
    constructor
    · intro h
      -- 推导：从 `used v w (sub v h)` 中取出 `he, hf`。
      obtain ⟨he, hf⟩ := used v w (sub v h)
      exact ⟨index v w, he, by simp [hf, h]⟩
    rintro ⟨j, hj, h⟩
    rcases split v j with ⟨z, hz, rfl⟩|⟨_, he⟩
    · have : z = w := host.injective ((used v z hz).1.symm.trans hj)
      subst z
      simpa only [(used _ _ hz).2, decide_eq_true_eq] using h
    · rw [he] at h; cases h

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
end

/-!
# 用公共后缀为各重置宿主上的硬件编码

**英文原文**

Encoding the hardware at each reset host by a common suffix
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {Y w : ℕ}

namespace Child

-- 读法：在后续公式中，`Part` 是 `R.Host (Schedule.Address n) (terminalWidth Δ Y)` 的缩写。
abbrev Part (R : Rotor F Y w) (Δ n : ℕ) := R.Host (Schedule.Address n) (terminalWidth Δ Y)

-- 读法：`code` 的结果类型为 `Part R Δ n ↪ B (extra R Δ n)`。
def code (R : Rotor F Y w) (Δ n : ℕ) : Part R Δ n ↪ B (extra R Δ n) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  have h := Fintype.card_le_of_embedding (intervalCode n)
  rw [Fintype.card_fin, pow_succ] at h
  have ht := Nat.le_pow_clog (by decide : 1 < 2) (resetPositions R Δ)
  rw [Fintype.card_fin, extra, pow_add 2 n]
  refine le_trans ?_ (Nat.mul_le_mul_left _ ht)
  unfold Part Rotor.Host resetPositions
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  rw [mul_assoc, ← mul_add, ← mul_assoc]
  exact Nat.mul_le_mul_right _ h

end Child
namespace Setup

variable {S : Scheme F} {h u a Δ D : ℕ} {B' c : ℝ} [NeZero Y] [NeZero w]
  (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (fits : U.Fits R c)

-- 读法：在后续公式中，`parts` 是 `Schedule.splitHost R a h (terminalWidth Δ Y)` 的缩写。
abbrev parts : (U.graph R fits).V ≃ U.G.V × Child.Part R Δ (h - a) :=
  Schedule.splitHost R a h (terminalWidth Δ Y)

-- 读法：在后续公式中，`neighbors` 是 `if full then (U.graph R fits).N else (U.graph R fits).C` 的缩写。
abbrev neighbors (full : Bool) := if full then (U.graph R fits).N else (U.graph R fits).C

-- 读法：`host` 的结果类型为 `(U.graph R fits).V ↪ B (S.m + Child.extra R Δ (h - a))`。
def host : (U.graph R fits).V ↪ B (S.m + Child.extra R Δ (h - a)) :=
  (U.parts R fits).toEmbedding.trans ((U.post.host.prodMap (Child.code R Δ (h - a))).trans
    (Match.rowIndex S.m (Child.extra R Δ (h - a))).symm.toEmbedding)

-- 读法：`Match.rowIndex S.m (Child.extra R Δ (h - a)) (U.host R fits i)` 等于 `(U.post.host (U.parts R fits i).1, Child.code R Δ (h - a) (U.parts R fits i).2)`。使用 `Match.rowIndex` 给出的结论。
@[simp] theorem host_parts (i : (U.graph R fits).V) :
    Match.rowIndex S.m (Child.extra R Δ (h - a)) (U.host R fits i) =
      (U.post.host (U.parts R fits i).1, Child.code R Δ (h - a) (U.parts R fits i).2) :=
  (Match.rowIndex _ _).apply_symm_apply _

-- 读法：`(U.graph R fits).frozen i` 等于 `U.G.frozen (U.parts R fits i).1`。
theorem frozen_parts (i : (U.graph R fits).V) :
    (U.graph R fits).frozen i = U.G.frozen (U.parts R fits i).1 := by
  rcases i with a|b <;> rfl

end Setup
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# 依据上一首部为重置后的邻居编号

**英文原文**

Numbering reset neighbors from the previous header
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Packing Coloring Finset
open scoped Classical

variable {V W : Type} {C : V → Finset V} {d : ℕ}

-- 读法：`hops` 的取值由 `univ.filter fun i => nav v i = w` 给出。
def hops (nav : V → B d → V) (v w : V) : Finset (B d) :=
  univ.filter fun i => nav v i = w

-- 读法：`label` 的取值由 `if v = w then none else if h : (hops nav v w).Nonempty then some h.choose else none` 给出。
def label (nav : V → B d → V) (v w : V) : Option (B d) :=
  if v = w then none else if h : (hops nav v w).Nonempty then some h.choose else none

-- 读法：`(label nav v w).elim v (nav v)` 等于 `w`。按 `v = w` 成立与否分情况。
theorem label_spec (nav : V → B d → V) {v w : V} (h : w = v ∨ ∃ i, nav v i = w) :
    (label nav v w).elim v (nav v) = w := by
  unfold label
  by_cases he : v = w
  · simp [he]
  obtain ⟨i, hi⟩ := h.resolve_left (Ne.symm he)
  have hh : (hops nav v w).Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  rw [ite_eq_right he, dite_eq_left hh]
  exact (mem_filter.mp hh.choose_spec).2

-- 读法：`label nav v t` 等于 `label nav' w z`。
theorem label_eq {nav : V → B d → V} {nav' : W → B d → W} {v t : V} {w z : W}
    (he : v = t ↔ w = z) (ht : ∀ j, nav v j = t ↔ nav' w j = z) :
    label nav v t = label nav' w z := by
  have hh : hops nav v t = hops nav' w z := by ext i; simp [hops, ht]
  simp only [label, he, hh]

-- 读法：用字段 `label`、`self`、`inj` 构造 `Chart C d`。
def chart (nav : V → B d → V) (ok : ∀ v w, w ∈ C v → ∃ i, nav v i = w) : Chart C d where
  label := label nav
  self v := by simp [label]
  inj v i hi j hj he := by
    have decode (i : V) (h : i ∈ insert v (C v)) : (label nav v i).elim v (nav v) = i :=
      label_spec nav ((mem_insert.mp h).imp_right (ok v i))
    rw [← decode i hi, he, decode j hj]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
open Packing Coloring
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {D : Template F} {G : HostNet F L D.scheme.h u} {r : D.format.obj} (p : D.Encodes r G)

-- 读法：`p.post.host (p.post.nav v j)` 等于 `D.nav r (p.post.host v) j`。这里调用 `hh.choose_spec`。
theorem host_nav (v : G.V) (j : B D.scheme.d) :
    p.post.host (p.post.nav v j) = D.nav r (p.post.host v) j := by
  have hh : ∃ w, p.post.host w = (r.1 (p.post.host v)).1 j := p.closed v j
  rw [Scheme.Posting.nav, dite_eq_left hh]
  exact hh.choose_spec

-- 读法：`resetChart` 的结果类型为 `History.Reset.Chart G.C D.scheme.d`。
def resetChart : History.Reset.Chart G.C D.scheme.d :=
  History.Reset.chart p.post.nav fun v w he => by
    obtain ⟨i, hi, _⟩ := (p.core v w).mp he
    exact ⟨i, p.post.host.injective ((p.host_nav v i).trans hi)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
end

/-!
# 对重复出现的邻居列求和

所有填充列的需求为零。因此对某一邻居的整个原像纤维求和时，结果与为未用接触项选了哪一列无关。

**英文原文**

Summing over repeated neighbor columns

All padding columns have zero demand. Their presence makes a sum
over the whole neighbor fiber independent of which column was chosen
for an unused contact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
open Packing Coloring History.Reset Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {D : Template F} {G : HostNet F L D.scheme.h u} {r : D.format.obj} (p : D.Encodes r G)
  (hu : 0 < u) (c : CoreContact G.C)

-- 读法：在后续公式中，`columns` 是 `hops p.post.nav c.val.1 c.val.2` 的缩写。
abbrev columns := hops p.post.nav c.val.1 c.val.2

-- 读法：`p.contactCol c` 属于 `p.columns c`。这里调用 `mem_filter.mpr`。
theorem contact_mem : p.contactCol c ∈ p.columns c := by
  exact mem_filter.mpr ⟨mem_univ _, p.post.host.injective ((p.host_nav _ _).trans (p.nav_contact c))⟩

include hu in
-- 读法：`p.usedCol c.val.1 b j` 等于 `∅`。这里调用 `p.unused`。
private theorem no_units (j : B D.scheme.d) (hj : j ∈ p.columns c) (hn : j ≠ p.contactCol c)
    (b : Cell D.scheme.h) : p.usedCol c.val.1 b j = ∅ := by
  apply p.unused hu
  rintro ⟨c', he⟩
  obtain ⟨hv, hj'⟩ := Prod.mk.inj he
  have hs : c'.val.1 = c.val.1 := p.post.host.injective hv
  have ht : p.post.nav c'.val.1 (p.contactCol c') = c'.val.2 := (mem_filter.mp (p.contact_mem c')).2
  rw [hs, hj'] at ht
  have eq : c' = c := Subtype.ext (Prod.ext hs (ht.symm.trans (mem_filter.mp hj).2))
  exact hn (hj'.symm.trans (congrArg p.contactCol eq))

include hu in
-- 读法：`(coreDemands G.ix G.edge).amounts w c b` 等于 `(∑ j ∈ p.columns c, (p.usedCol c.val.1 b j).card : ℕ) * w`。
theorem column_load (b : Cell D.scheme.h) (w : ℝ) :
    (coreDemands G.ix G.edge).amounts w c b =
      (∑ j ∈ p.columns c, (p.usedCol c.val.1 b j).card : ℕ) * w := by
  rw [p.contact_load hu, sum_eq_single_of_mem _ (p.contact_mem c)]
  exact fun j hj hn => by rw [p.no_units hu c j hj hn, card_empty]

include hu in
-- 读法：`(∑ b, (coreDemands G.ix G.edge).amounts w c b)` 等于 `(∑ j ∈ p.columns c, (D.unitCount r (p.post.host c.val.1) j).val : ℕ) * w`。
theorem column_total (w : ℝ) :
    (∑ b, (coreDemands G.ix G.edge).amounts w c b) =
      (∑ j ∈ p.columns c, (D.unitCount r (p.post.host c.val.1) j).val : ℕ) * w := by
  rw [p.amount_total hu, sum_eq_single_of_mem _ (p.contact_mem c)]
  intro j hj hn
  simp only [p.unit_count, p.no_units hu c j hj hn, card_empty, sum_const_zero]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
end

/-!
# 从局部发布记录中还原一个单位的两个半边

**英文原文**

Recovering both stubs of a unit from a local posting
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U V : Setup S h u a Δ D Y w B')

-- 读法：在后续公式中，`tag` 是 `(U.r (U.post.host v)).2 (U.post.block x)` 的缩写。
abbrev tag (v : U.G.V) (x : Cell h) := (U.r (U.post.host v)).2 (U.post.block x)
-- 读法：在后续公式中，`pat` 是 `S.decode (U.tag v x)` 的缩写。
abbrev pat (v : U.G.V) (x : Cell h) := S.decode (U.tag v x)

-- 读法：结论为 `let v := Scheme.side U.G i t let q := Scheme.side U.G i (!t) (U.pat v (U.G.ix i)).peer 0 (U.post.stub i t) = some (U.post.index v q, 0, U.post.stub i (!t))`。使用 `U.post.link` 给出的结论。
theorem stub_link (i : U.G.E) (t : Bool) :
    let v := Scheme.side U.G i t
    let q := Scheme.side U.G i (!t)
    (U.pat v (U.G.ix i)).peer 0 (U.post.stub i t) = some (U.post.index v q, 0, U.post.stub i (!t)) :=
  U.post.link i t

-- 读法：存在 `f`，`Scheme.side U.G f t = v` 与 `U.G.ix f = x ∧ U.post.stub f t = i` 同时成立。
theorem endpoint (v : U.G.V) (x : Cell h) (t : Bool) (i : B S.e)
    (hp : 0 < (U.pat v x).width 0 i) (hd : (U.pat v x).direction 0 i = t)
    (he : ((U.pat v x).peer 0 i).isSome) :
    ∃ f, Scheme.side U.G f t = v ∧ U.G.ix f = x ∧ U.post.stub f t = i := by
  let p := U.post
  let z : S.Span := ((p.host v, p.block x, 0), i)
  have used : (S.peer U.r z).isSome := by simpa [Scheme.peer, Scheme.pattern, z, p, pat, tag] using he
  obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨z, ⟨0, hp⟩⟩
  have hit := congrArg Sigma.fst hq
  have key (i' : U.G.E) (b : Bool) (j : Fin u)
      (hs : (p.toSeating.ends (Scheme.endBit U.G i' b j)).1 = z) :
      ∃ f, Scheme.side U.G f t = v ∧ U.G.ix f = x ∧ U.post.stub f t = i := by
    have hspan := (p.ordered i' b j).1.symm.trans hs
    -- 推导：记下中间结论 `hb`：`b = t`。
    have hb : b = t := (p.dir i' b).symm.trans ((congrArg (S.direction U.r) hspan).trans hd)
    subst b
    obtain ⟨ha, hi⟩ := Prod.mk.inj hspan
    exact ⟨i', p.host.injective (Prod.mk.inj ha).1, p.block.injective (Prod.mk.inj (Prod.mk.inj ha).2).1, hi⟩
  change (p.toSeating.ends q).1 = z at hit
  rcases q with (i|e)|(i|e)
  · rw [← hit, p.input] at used
    cases used
  · obtain ⟨⟨f, j⟩, rfl⟩ := U.G.units.bits.symm.surjective e
    exact key f false j hit
  · rw [← hit, p.output] at used
    cases used
  -- 推导：从 `U.G.units.bits.symm.surjective e` 中取出 `⟨f, j⟩, rfl`。
  · obtain ⟨⟨f, j⟩, rfl⟩ := U.G.units.bits.symm.surjective e
    exact key f true j hit

-- 读法：结论为 `let x := Scheme.side U.G e t let y := Scheme.side U.G e (!t) U.post.nav x (U.post.index x y) = y`。对 `t` 分类讨论。
theorem stub_nav (e : U.G.E) (t : Bool) :
    let x := Scheme.side U.G e t
    let y := Scheme.side U.G e (!t)
    U.post.nav x (U.post.index x y) = y := by
  cases t
  · exact U.post.nav_target U.hu e
  · exact U.post.return_nav U.hu e

-- 读法：结论为 `∃ f : V.G.E, Scheme.side V.G f t = z ∧ U.G.ix e = V.G.ix f ∧ (∀ b, U.post.stub e b = V.post.stub f b) ∧ U.post.index v (Scheme.side U.G e (!t)) = V.post.index z (Scheme.side V.G f (!t))`。
theorem transfer {e : U.G.E} {t : Bool} {v : U.G.V} {z : V.G.V}
    (hv : Scheme.side U.G e t = v) (ht : U.tag v (U.G.ix e) = V.tag z (U.G.ix e)) :
    ∃ f : V.G.E, Scheme.side V.G f t = z ∧ U.G.ix e = V.G.ix f ∧
      (∀ b, U.post.stub e b = V.post.stub f b) ∧
      U.post.index v (Scheme.side U.G e (!t)) = V.post.index z (Scheme.side V.G f (!t)) := by
  subst v
  let i := U.post.stub e t
  let x := U.G.ix e
  let v := Scheme.side U.G e t
  have pat : U.pat v x = V.pat z x := congrArg S.decode ht
  have eq := U.stub_link e t
  change (U.pat v x).peer 0 i = some _ at eq
  -- 推导：从 `V.endpoint z x t i` 中取出 `f, hf, hx, hi`。
  obtain ⟨f, hf, hx, hi⟩ := V.endpoint z x t i
    (by rw [← pat]; exact U.hu.trans_eq (U.post.length e t).symm)
    (by rw [← pat]; exact U.post.dir e t)
    (by rw [← pat, eq]; rfl)
  have other := V.stub_link f t
  dsimp only at other
  rw [hf, hx, hi, ← pat, eq, Option.some.injEq] at other
  refine ⟨f, hf, hx.symm, ?_, (Prod.mk.inj other).1⟩
  intro b
  by_cases hb : b = t
  · rw [hb]; exact hi.symm
  have : b = !t := by cases b <;> cases t <;> first | rfl | contradiction
  rw [this]
  exact (Prod.mk.inj (Prod.mk.inj other).2).2

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 从模板首部中读出的公共信息

当非核心边在当前高度不会影响分裂时，即使图的总度数很大，也可以略去这些边。

**英文原文**

Common information read from a template header

A graph with very large full degree can omit its noncore edges
when they cannot affect a split at the present height.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U V : Setup S h u a Δ D Y w B') (full : Bool)

-- 读法：在后续公式中，`adj` 是 `if full then U.G.N else U.G.C` 的缩写。
abbrev adj := if full then U.G.N else U.G.C

-- 读法：结构的字段包括 `flags`、`counts`、`chart`、`links`、`core`。
structure Reading where
  flags : U.G.V → (Group.Flags S.d).obj
  counts : U.G.V → B S.d → ℕ
  chart : U.chart.label = label U.post.nav
  links : ∀ v z, z ∈ U.adj full v ↔ ∃ j, U.post.nav v j = z ∧ (flags v j).1 = true
  core : ∀ v z, z ∈ U.G.C v ↔ ∃ j, U.post.nav v j = z ∧ (flags v j).2 = true
  weight : ∀ (c : CoreContact U.G.C) x,
    U.amount c x = (∑ j ∈ hops U.post.nav c.val.1 c.val.2, ((U.pat c.val.1 x).uses j).card : ℕ) * ((u : ℝ) / B')
  total : ∀ c : CoreContact U.G.C,
    (∑ x, U.amount c x) = (∑ j ∈ hops U.post.nav c.val.1 c.val.2, counts c.val.1 j : ℕ) * ((u : ℝ) / B')

-- 读法：用字段 `flags`、`counts`、`chart`、`links` 构造 `U.Reading T.full`。
def reading {T : Template F} (U : Setup T.scheme T.scheme.h u a Δ D Y w B')
    (b : (Format.vec T.scheme.m T.header).obj) (p : T.Encodes (U.r, b) U.G)
    (he : p.post = U.post) (hc : U.chart = p.resetChart) : U.Reading T.full where
  flags v := T.flags (U.r, b) (U.post.host v)
  counts v j := (T.unitCount (U.r, b) (U.post.host v) j).val
  chart := by rw [hc, ← he]; rfl
  links v z := by
    change z ∈ T.adj U.G v ↔ _
    rw [p.edge, ← he]
    apply exists_congr
    intro j
    rw [← p.host_nav, p.post.host.injective.eq_iff]
  core v z := by
    rw [p.core, ← he]
    apply exists_congr
    intro j
    rw [← p.host_nav, p.post.host.injective.eq_iff]
  weight c x := by
    simp only [pat, tag, ← he, p.block]
    exact p.column_load U.hu c x _
  total c := by
    rw [← he]
    exact p.column_total U.hu c _

variable {U V full} (P : U.Reading full) (Q : V.Reading full)
  (σ : Cell a) (R : Relation U V) (n : ℕ)

-- 读法：结构的字段包括 `widen`、`same`、`next`、`margin`、`mix`。
structure Look : Prop where
  widen : ∀ {k j v z}, k ≤ j → R k v z → R j v z
  same : ∀ {v z v' z'}, R n v z → R n v' z' → (v = v' ↔ z = z')
  next : ∀ {k v z}, R k v z → ∀ j, R (k + 1) (U.post.nav v j) (V.post.nav z j)
  margin : U.g = V.g
  mix : U.Z.π = V.Z.π
  flags : ∀ {v z}, R n v z → P.flags v = Q.flags z
  counts : ∀ {v z}, R n v z → P.counts v = Q.counts z
  base : ∀ {v z}, R n v z → U.Z.base v = V.Z.base z
  tag : ∀ {v z}, R n v z → ∀ j, U.Z.group j = σ → U.tag v j = V.tag z j
  load : ∀ {v z}, R n v z → ∀ j, U.Z.group j = σ → U.G.load v j = V.G.load z j

namespace Look
variable {P Q σ R n} (p : Look P Q σ R n)
  {v v' : U.G.V} {z z' : V.G.V} {k : ℕ}
include p

-- 读法：`U.Z.group x` 等于 `V.Z.group x`。
theorem group (x : Cell h) : U.Z.group x = V.Z.group x := by unfold Schedule.group; rw [p.mix]

-- 读法：要证明的命题是 `Look Q P σ (flip R) n`。
theorem symm : Look Q P σ (flip R) n :=
  ⟨fun h r => p.widen h r, fun r s => (p.same r s).symm, fun r j => p.next r j,
   p.margin.symm, p.mix.symm, fun r => (p.flags r).symm, fun r => (p.counts r).symm,
   fun r => (p.base r).symm, fun r x h => (p.tag r x ((p.group x).trans h)).symm,
   fun r x h => (p.load r x ((p.group x).trans h)).symm⟩

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

end Look
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# 由相匹配的记录确定相匹配的重置区域

**英文原文**

From matching records to a matching reset region
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup.Look
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w k n : ℕ} {B' : ℝ}
  {U V : Setup S h u a Δ D Y w B'} {full : Bool} {P : U.Reading full} {Q : V.Reading full}
  {σ : Cell a} {R : Relation U V} (p : Look P Q σ R n)
  {v v' : U.G.V} {z z' : V.G.V} {c : CoreContact U.G.C} {c' : CoreContact V.G.C}

include p in
-- 读法：由 `U.Z.capacity c = V.Z.capacity c' ∧ ∀ j, U.Z.group j = σ` 推出 `U.amount c j = V.amount c' j`。
theorem amounts (hk : k < n) (hr : R k c.val.1 c'.val.1) (ht : R k c.val.2 c'.val.2) :
    U.Z.capacity c = V.Z.capacity c' ∧ ∀ j, U.Z.group j = σ → U.amount c j = V.amount c' j := by
  have ha := p.widen hk.le hr
  have hb := p.widen hk.le ht
  have hs := p.columns hk hr hb
  have hc : (∑ j, U.amount c j) = (∑ j, V.amount c' j) := by
    rw [P.total, Q.total, hs, p.counts ha]
  have hd : contactDepth U.Z.base unitEnds c = contactDepth V.Z.base unitEnds c' :=
    congrArg₂ max (p.base ha) (p.base hb)
  constructor
  · change (∑ j, U.amount c j) / 2 ^ (contactDepth U.Z.base unitEnds c) + 1 / U.g =
      (∑ j, V.amount c' j) / 2 ^ (contactDepth V.Z.base unitEnds c') + 1 / V.g
    rw [hc, hd, p.margin]
  · intro j hj
    rw [P.weight, Q.weight, hs]
    simp only [pat, p.tag ha j hj]

include p in
-- 读法：要证明的命题是 `Siblings U V σ R k v z`。
theorem siblings (hk : k + 1 < n) (hr : R k v z) : Siblings U V σ R k v z := by
  intro c t he
  have hm : unitEnds c (!t) ∈ U.G.C v := he ▸ Chart.partner_mem U.G.cs c t
  obtain ⟨j, hj, _⟩ := (P.core _ _).mp hm
  let w := V.post.nav z j
  have ht : R (k + 1) (unitEnds c (!t)) w := hj ▸ p.next hr j
  have hm' := (p.core (by omega) hr (p.widen hk.le ht)).mp hm
  have hl := p.labels (by omega) hr (p.widen hk.le ht)
  have hv : R (k + 1) (unitEnds c t) z := he.symm ▸ p.widen (by omega) hr
  cases t
  · let c' : CoreContact V.G.C := ⟨(z, w), hm'⟩
    exact ⟨c', rfl, ht, hl, p.amounts (c' := c') hk hv ht⟩
  · let c' : CoreContact V.G.C := ⟨(w, z), V.G.cs _ _ hm'⟩
    exact ⟨c', rfl, ht, hl, p.amounts (c' := c') hk ht hv⟩

include p in
-- 读法：要证明的命题是 `SurveySide U V σ R k`。按 `full = true` 成立与否分情况。
theorem side (hn : k < n) (hD : 0 < D) (delayed : full = false → h - a ≤ 32 * Nat.clog 2 (2 * D)) :
    SurveySide U V σ R k := by
  refine ⟨p.mix, fun _ _ _ hr hi => p.base (p.widen (hi.trans hn.le) hr),
    fun _ _ _ hr hi => p.load (p.widen (hi.trans hn.le) hr), ?_, ?_, ?_⟩
  · intro i v z hr hi t ht hd
    have hm : t ∈ U.adj full v := by
      by_cases he : full = true
      · simpa [adj, he] using ht
      have h' := delayed (by simpa using he)
      have hc : t ∈ U.G.C v := by
        by_contra hbad
        simp only [delay, resetDelay, hbad, ite_false] at hd
        omega
      simpa [adj, he] using hc
    -- 推导：从 `(P.links _ _).mp hm` 中取出 `j, hj, _`。
    obtain ⟨j, hj, _⟩ := (P.links _ _).mp hm
    let t' := V.post.nav z j
    have ht' : R (i + 1) t t' := hj ▸ p.next hr j
    have hh := p.widen (by omega : i + 1 ≤ n) ht'
    have he := (p.links (by omega) hr hh).mp hm
    have hc := p.core (by omega) hr hh
    refine ⟨?_, t', ?_, ?_, ht'⟩
    · unfold delay resetDelay
      apply Nat.mul_pos (by decide)
      apply Nat.clog_pos (by decide)
      have := U.hΔ
      split_ifs <;> omega
    · unfold adj at he
      split at he <;> first | exact he | exact V.G.sub _ he
    · simp only [delay, resetDelay, hc]
  · intro i v z hr hi
    exact p.siblings (by omega) hr
  · intro i v z hr hi e t hx hv
    -- 推导：从 `U.transfer V hv (p.tag (p.widen (by omega) hr) _ hx)` 中取出 `f, hz, hb, hs, he`。
    obtain ⟨f, hz, hb, hs, he⟩ := U.transfer V hv (p.tag (p.widen (by omega) hr) _ hx)
    have ht := p.next hr (U.post.index v (Scheme.side U.G e (!t)))
    have eh := U.stub_nav e t
    have fh := V.stub_nav f t
    dsimp only at eh fh
    rw [hv] at eh
    rw [hz] at fh
    rw [eh, he, fh] at ht
    exact ⟨f, hz, ⟨hb, hs, p.labels (by omega) hr (p.widen (by omega) ht)⟩, ht⟩

include p in
-- 读法：要证明的命题是 `Region U V σ R k`。
theorem region (hn : k < n) (hD : 0 < D) (delayed : full = false → h - a ≤ 32 * Nat.clog 2 (2 * D)) :
    Region U V σ R k :=
  ⟨⟨p.side hn hD delayed, p.symm.side hn hD delayed⟩, p.widen,
    fun r s => p.same (p.widen hn.le r) (p.widen hn.le s),
    fun h r s => p.labels (h.trans hn) r (p.widen hn.le s)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup.Look
end

/-!
# 模板控制器所选出的具体重置

**英文原文**

The explicit reset selected by a template's controller
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
open Packing History.Reset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {A : Template F} {G : HostNet F L A.scheme.h u} {r : A.format.obj}
  (p : A.Encodes r G) {a t Δ D Y w Z k d : ℕ} {W ε : ℝ}

-- 读法：`margin` 的取值由 `2 * Δ * 2 ^ (32 * Nat.clog 2 (2 * Δ))` 给出。
def margin (Δ : ℕ) := 2 * Δ * 2 ^ (32 * Nat.clog 2 (2 * Δ))

-- 读法：`(margin Δ : ℝ)` 等于 `reserveCount Δ`。
theorem margin_eq (Δ : ℕ) : (margin Δ : ℝ) = reserveCount Δ := by simp [margin, reserveCount]

variable (ok : Fits (G := G) a t Δ D (margin Δ) Z k d W ε) (enough : 4 * coreBins Δ ≤ Y)
  (space : Y ^ 2 * w ≤ 2 ^ t) (unit : (u : ℝ) / W ≤ 1 / (2 : ℝ) ^ t)

-- 读法：用字段 `T`、`x`、`y`、`L` 构造 `Setup A.scheme A.scheme.h u a Δ D Y w W`。
def elected : Setup A.scheme A.scheme.h u a Δ D Y w W where
  T := T
  x := x
  y := y
  L := L
  G := G
  r := r.1
  post := p.post
  chart := p.resetChart
  k := t
  g := margin Δ
  ε := ε
  Z := p.resetSchedule ok
  bound := (p.resetSchedule ok).reserve G.cs G.sub ok.corePos ok.cdeg enough (margin_eq _)
  hu := ok.width
  hB := ok.capacity
  hΔ := ok.corePos
  deg := ok.cdeg
  space := space
  unit := unit

-- 读法：`reading` 的取值由 `Setup.reading _ r.2 p rfl rfl` 给出。
def reading : (p.elected ok enough space unit).Reading A.full :=
  Setup.reading _ r.2 p rfl rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
end

/-!
# 重置控制器的短记录

混合器与各接触项的全部总量只选定一次。随后的查找在短游走所到达的每个宿主上取一组块，同时使用布尔掩码记录哪些宿主名称相同。

**英文原文**

Short records for the reset controller

The mixer and full contact totals are selected once. A subsequent
lookup uses one group of blocks at every host reached by a short
walk, with a Boolean mask for coincidences of host names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
open Coloring
open scoped Classical
variable {F : Type} (A : Template F) (a k : ℕ) (ha : a ≤ A.scheme.h)
local notation "S" => A.scheme

-- 读法：在后续公式中，`summary` 是 `Format.pair (.addr A.scheme.h) (.vec A.scheme.m (A.Statistics k))` 的缩写。
abbrev summary := Format.pair (.addr A.scheme.h) (.vec A.scheme.m (A.Statistics k))
-- 读法：在后续公式中，`pair` 是 `A.format.pair (summary A k)` 的缩写。
abbrev pair := A.format.pair (summary A k)
-- 读法：在后续公式中，`data` 是 `Format.pair (.addr A.scheme.ℓ) (.addr A.count)` 的缩写。
abbrev data := Format.pair (.addr A.scheme.ℓ) (.addr A.count)
-- 读法：在后续公式中，`row` 是 `(A.Statistics k).pair ((Group.Flags A.scheme.d).pair (.vec (A.scheme.h - a) (data A)))` 的缩写。
abbrev row := (A.Statistics k).pair ((Group.Flags A.scheme.d).pair (.vec (A.scheme.h - a) (data A)))
-- 读法：在后续公式中，`bank` 是 `Fmt.groups A.scheme.m A.scheme.d a (row A a k)` 的缩写。
abbrev bank := Fmt.groups A.scheme.m A.scheme.d a (row A a k)

-- 读法：`packet` 的结果类型为 `(bank A a k).obj`。
def packet (x : (pair A k).obj) : (bank A a k).obj :=
  fun v => (A.nav x.1 v, fun i => (x.2.2 v, A.flags x.1 v, fun j =>
    let b := cellIndex _ (Mixing.original A.scheme.h a ha x.2.1 i j)
    ((x.1.1 v).2 b, A.counter x.1 v b)))

-- 读法：在后续公式中，`coincides` 是 `Format.vec ((d + 1) * n) (.vec ((d + 1) * n) .bit)` 的缩写。
abbrev coincides (d n : ℕ) := Format.vec ((d + 1) * n) (.vec ((d + 1) * n) .bit)

-- 读法：输入 `i j` 时返回 `decide (Neighborhood.walks n (A.nav r) v i = Neighborhood.walks n (A.nav r) v j)`。
def mask (n : ℕ) (r : A.format.obj) (v : B A.scheme.m) : (coincides A.scheme.d n).obj :=
  fun i j => decide (Neighborhood.walks n (A.nav r) v i = Neighborhood.walks n (A.nav r) v j)

-- 读法：`sample` 的构造用到 `Format.pair`、`A.scheme.h`、`A.scheme.d`。
abbrev sample (n t : ℕ) :=
  Format.pair (.pair .bit (.addr t)) (.pair (.pair (.addr A.scheme.h) (.addr a))
    (.pair (coincides A.scheme.d n) (Window.Walks n A.scheme.d (row A a k))))

-- 读法：`look` 的结果类型为 `(sample A a k n t).obj`。
def look (n t : ℕ) (x : (pair A k).obj) (v : B (A.scheme.m + t)) (i : B a) :
    (sample A a k n t).obj :=
  let p := Match.rowIndex A.scheme.m t v
  ((A.live x.1 p.1, p.2), (x.2.1, i), mask A n x.1 p.1, (Window.reads n (packet A a k ha x) p.1).2 i)

-- 读法：在后续公式中，`output` 是 `(data D).pair (.vec D.scheme.k (.vec D.scheme.e (BatchDescent.Trail.pointer S 0)))` 的缩写。
abbrev output (D : Template F) :=
  (data D).pair (.vec D.scheme.k (.vec D.scheme.e (BatchDescent.Trail.pointer S 0)))

-- 读法：在后续公式中，`whole` 是 `D.format.pair (BatchDescent.Trail.controls S D.scheme 0)` 的缩写。
abbrev whole (D : Template F) := D.format.pair (BatchDescent.Trail.controls S D.scheme 0)

-- 读法：`part` 的取值由 `(((x.1.1 v).2 i, D.counter x.1 v i), x.2 v i)` 给出。
def part (D : Template F) (x : (whole A D).obj) (v : B D.scheme.m) (i : B D.scheme.h) :
    (output A D).obj :=
  (((x.1.1 v).2 i, D.counter x.1 v i), x.2 v i)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Tile
end

/-!
# 用短记录与长记录表示选出的重置

**英文原文**

Representation of an elected reset by its short and long records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Coloring Packing
open scoped Classical
variable {F : Type} [Field F] (A : Template F) {u a Δ D Y w : ℕ} {W : ℝ}
  (U : Setup A.scheme A.scheme.h u a Δ D Y w W)

-- 读法：结构的字段包括 `read`、`tape`、`nav`、`live`、`frozen`。
structure Board (k : ℕ) where
  read : U.Reading A.full
  tape : (Tile.pair A k).obj
  nav : ∀ v i, U.post.host (U.post.nav v i) = A.nav tape.1 (U.post.host v) i
  live : ∀ i, A.live tape.1 i = true ↔ i ∈ Set.range U.post.host
  frozen : ∀ v, A.frozen tape.1 (U.post.host v) = true ↔ U.G.frozen v
  flags : ∀ v, read.flags v = A.flags tape.1 (U.post.host v)
  counts : ∀ v j, read.counts v j = ((tape.2.2 (U.post.host v)).2 j).val
  depth : ∀ v, U.Z.base v = (tape.2.2 (U.post.host v)).1.val
  mix : U.Z.π = menu A.scheme.h tape.2.1
  margin : U.g = reserveCount Δ
  block : ∀ x, U.post.block x = cellIndex _ x
  tag : ∀ v x, U.tag v x = (tape.1.1 (U.post.host v)).2 (cellIndex _ x)
  load : ∀ v x, U.G.load v x = A.load (A.counter tape.1 (U.post.host v) (cellIndex _ x))
  park : ∀ v x, push U.G.park U.L.charge (v, x) = A.park (A.counter tape.1 (U.post.host v) (cellIndex _ x))
  past : ∀ v x, U.G.past (v, x) = A.past (A.counter tape.1 (U.post.host v) (cellIndex _ x))

variable {A} {T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {G : HostNet F L A.scheme.h u}
  {r : A.format.obj} (p : A.Encodes r G) {t Z k d : ℕ} {ε : ℝ}
  (ok : Template.Encodes.Fits (G := G) a t Δ D (Template.Encodes.margin Δ) Z k d W ε)
  (enough : 4 * coreBins Δ ≤ Y) (space : Y ^ 2 * w ≤ 2 ^ t) (unit : (u : ℝ) / W ≤ 1 / (2 : ℝ) ^ t)

-- 读法：用字段 `read`、`tape`、`nav`、`live` 构造 `Board A (p.elected ok enough space unit) k`。
def electedBoard : Board A (p.elected ok enough space unit) k where
  read := p.reading ok enough space unit
  tape := (r, A.mixerChoice a t Δ D u _ Z k d ok.depth W r,
    fun v => (A.baseDepth a t Δ D Z k d W r v, A.unitCount r v))
  nav := p.host_nav
  live := p.live
  frozen := p.frozen
  flags _ := rfl
  counts _ _ := rfl
  depth := p.reset_depth ok
  mix := p.reset_mixer ok
  margin := Template.Encodes.margin_eq Δ
  block := p.block
  tag v x := congrArg (r.1 (p.post.host v)).2 (p.block x)
  load v x := (p.load v x).symm.trans (by rw [p.block]; rfl)
  park v x := (p.park v x).symm.trans (by rw [p.block]; rfl)
  past v x := (p.past v x).symm.trans (by rw [p.block]; rfl)

namespace Board
variable {U} (b : Board A U k) (v : U.G.V)

-- 读法：`node` 的取值由 `Window.visit U.post.nav v p` 给出。
def node (p : List (B A.scheme.d)) := Window.visit U.post.nav v p

include b in
-- 读法：`U.post.host (node v p)` 等于 `Window.visit (A.nav b.tape.1) (U.post.host v) p`。对 `p` 作归纳。
theorem at_node (p : List (B A.scheme.d)) :
    U.post.host (node v p) = Window.visit (A.nav b.tape.1) (U.post.host v) p := by
  induction p with
  | nil => rfl
  | cons j p ih =>
    rw [show node v (j::p) = U.post.nav (node v p) j from rfl, b.nav, ih]
    rfl

-- 读法：`localRow` 的取值由 `((Tile.packet A a k U.groups b.tape) (U.post.host v)).2 (cellIndex a σ)` 给出。
def localRow (σ : Cell a) :=
  ((Tile.packet A a k U.groups b.tape) (U.post.host v)).2 (cellIndex a σ)

-- 读法：要证明的命题是 `Mixing.original A.scheme.h a U.groups b.tape.2.1 (cellIndex _ (U.Z.group x)) (cellIndex _ (splitCell a U.groups (U.Z.π x)).2) = x`。
theorem original (x : Cell A.scheme.h) :
    Mixing.original A.scheme.h a U.groups b.tape.2.1 (cellIndex _ (U.Z.group x))
      (cellIndex _ (splitCell a U.groups (U.Z.π x)).2) = x := by
  simp only [Mixing.original, Mixing.merge, Equiv.symm_apply_apply, ← b.mix]
  change U.Z.π.symm ((splitCell a U.groups).symm (splitCell a U.groups (U.Z.π x))) = x
  simp

end Board
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# 解码通往父宿主的短跳转并附加硬件地址

**英文原文**

Decoding a short parent hop and appending a hardware address
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Coloring Packing Finset
open scoped Classical

namespace Child
variable {m d k l : ℕ} (r : (Input m d k l).obj)

-- 读法：`follow r.1 x (BatchDescent.Trail.hop d p)` 等于 `p.elim x (r.1 x)`。
theorem follow_hop (x : B m) (p : Option (B d)) :
    follow r.1 x (BatchDescent.Trail.hop d p) = p.elim x (r.1 x) := by
  cases p <;> simp [follow, BatchDescent.Trail.hop]

-- 读法：结论为 `let v := (Match.rowIndex m k x).1 (build m d k l r).1 x j = (Match.rowIndex m k).symm (p.elim v (r.1 v), z)`。
theorem build_hop (x : B (m + k)) (j : B l) (p : Option (B d)) (z : B k)
    (he : ((r.2 x).2 j).2 = (BatchDescent.Trail.hop d p, z)) :
    let v := (Match.rowIndex m k x).1
    (build m d k l r).1 x j = (Match.rowIndex m k).symm (p.elim v (r.1 v), z) := by
  simp only [build, he, follow_hop]

-- 读法：`(build m d k l r).1 x j` 等于 `x`。使用 `build_hop` 给出的结论。
theorem build_stay (x : B (m + k)) (j : B l)
    (he : ((r.2 x).2 j).2 = (BatchDescent.Trail.hop d none, (Match.rowIndex m k x).2)) :
    (build m d k l r).1 x j = x :=
  (build_hop r x j none _ he).trans ((Match.rowIndex m k).symm_apply_apply _)

end Child

namespace Board
variable {F : Type} [Field F] {A : Template F} {u a Δ D Y w k : ℕ} {W : ℝ}
  {U : Setup A.scheme A.scheme.h u a Δ D Y w W} (b : Board A U k)

-- 读法：`(U.chart.label v z).elim (U.post.host v) (A.nav b.tape.1 (U.post.host v))` 等于 `U.post.host z`。
theorem parent_hop (v z : U.G.V) (h : z ∈ insert v (U.adj A.full v)) :
    (U.chart.label v z).elim (U.post.host v) (A.nav b.tape.1 (U.post.host v)) = U.post.host z := by
  have ht : z = v ∨ ∃ i, U.post.nav v i = z := by
    rcases mem_insert.mp h with he|he
    · exact .inl he
    obtain ⟨i, hi, _⟩ := (b.read.links _ _).mp he
    exact .inr ⟨i, hi⟩
  have he := label_spec U.post.nav ht
  rw [← b.read.chart] at he
  cases hm : U.chart.label v z with
  | none => simp only [hm, Option.elim_none] at he; exact congrArg U.post.host he
  | some i =>
    simp only [hm, Option.elim_some] at he
    exact (b.nav _ i).symm.trans (congrArg U.post.host he)

end Board
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end
