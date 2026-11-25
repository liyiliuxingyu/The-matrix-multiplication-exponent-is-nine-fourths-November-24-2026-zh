-- 本文件所属证明环节：在有限域上把具有短标签的调用编成批量下降过程；结合带标签置换的难度和对角抵抗性，导出多份独立列表同时判重的规模下界。
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.TraceNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.ResetRate
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect

/-!
# 初始宿主的短邻点索引与端口索引

**英文原文**

Short neighbor and port indices for the initial host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Coloring Assembly Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} (G : Diagram F x y) (m : ℕ)

-- 读法：结构的字段包括 `host`、`link`、`localPort`。
structure Addresses where
  host : G.V × Bool ↪ B m
  link : ∀ v, ↥(adjacent G v) ↪ B 3
  localPort : ∀ v, G.Port v ↪ B 2

-- 读法：`(Addresses G m)` 有元素。这里调用 `Function.Embedding.nonempty_of_card_le`。
theorem addresses (ht : G.Trivalent) (hm : 2 * Fintype.card G.V ≤ 2 ^ m) :
    Nonempty (Addresses G m) := by
  obtain ⟨host⟩ : Nonempty (G.V × Bool ↪ B m) :=
    Function.Embedding.nonempty_of_card_le (by simpa [mul_comm] using hm)
  have link v : Nonempty (↥(adjacent G v) ↪ B 3) :=
    Function.Embedding.nonempty_of_card_le (by simpa using adj_size G ht v)
  have localPort v : Nonempty (G.Port v ↪ B 2) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [Diagram.Port, Diagram.arity] using (ht v).trans (by decide : 3 ≤ 4)
  exact ⟨⟨host, fun v => (link v).some, fun v => (localPort v).some⟩⟩

namespace Addresses
variable {G m} (A : Addresses G m)

-- 读法：`get` 的取值由 `if h : ∃ v, A.host v = i then if g : ∃ w, A.link h.choose w = j then some (A.host g.choose.val) else none else none` 给出。
/-- 填充项以宿主自身的名称为值。掩码区分填充项与实际自接触。初始时，完整列表与核心列表相同。

英文原文：Padding names the host itself. The mask separates padding from
true self contacts. Initially the full and core lists coincide.
-/
def get (i : B m) (j : B 3) : Option (B m) :=
  if h : ∃ v, A.host v = i then
    if g : ∃ w, A.link h.choose w = j then some (A.host g.choose.val) else none
  else none

-- 读法：`nav` 的取值由 `(A.get i j).getD i` 给出。
def nav (i : B m) (j : B 3) := (A.get i j).getD i

-- 读法：`mask` 的取值由 `((A.get i j).isSome, (A.get i j).isSome)` 给出。
def mask (i : B m) (j : B 3) : Bool × Bool := ((A.get i j).isSome, (A.get i j).isSome)

-- 读法：当 `h : z ∈ adjacent G v` 成立时取 `A.link v ⟨z, h⟩`，否则取 `0`。
def index (v z : G.V × Bool) := if h : z ∈ adjacent G v then A.link v ⟨z, h⟩ else 0

-- 读法：`A.get i j = some w` 与 `∃ v, A.host v = i ∧ ∃ t : ↥(adjacent G v), A.link v t = j ∧ A.host t.val = w` 等价。
theorem get_iff (i : B m) (j : B 3) (w : B m) :
    A.get i j = some w ↔ ∃ v, A.host v = i ∧ ∃ t : ↥(adjacent G v),
      A.link v t = j ∧ A.host t.val = w := by
  unfold get
  split
  · rename_i h
    split
    · rename_i g
      refine ⟨fun he => ⟨_, h.choose_spec, _, g.choose_spec, Option.some.inj he⟩, ?_⟩
      rintro ⟨v, hv, t, ht, hw⟩
      have := A.host.injective (hv.trans h.choose_spec.symm)
      subst v
      rw [(A.link _).injective (g.choose_spec.trans ht.symm), hw]
    · rename_i g
      refine iff_of_false (by simp) ?_
      rintro ⟨v, hv, t, ht, _⟩
      have := A.host.injective (hv.trans h.choose_spec.symm)
      subst v
      exact g ⟨t, ht⟩
  · rename_i h
    exact iff_of_false (by simp) fun ⟨v, hv, _⟩ => h ⟨v, hv⟩

-- 读法：`A.get (A.host v) (A.index v z)` 等于 `some (A.host z)`。使用 `A.get_iff` 给出的结论。
theorem get_link {v z : G.V × Bool} (hz : z ∈ adjacent G v) :
    A.get (A.host v) (A.index v z) = some (A.host z) :=
  (A.get_iff ..).mpr ⟨v, rfl, ⟨z, hz⟩, by simp [index, hz], rfl⟩

-- 读法：`A.nav (A.host v) (A.index v z)` 等于 `A.host z`。
theorem nav_link {v z : G.V × Bool} (hz : z ∈ adjacent G v) :
    A.nav (A.host v) (A.index v z) = A.host z := by simp [nav, A.get_link hz]

-- 读法：`A.nav (A.host v) j` 属于 `Set.range A.host`。
theorem closed (v : G.V × Bool) (j : B 3) : A.nav (A.host v) j ∈ Set.range A.host := by
  unfold nav
  cases h : A.get _ _ with
  | none => exact ⟨v, rfl⟩
  | some w =>
    obtain ⟨_, _, q, _, hq⟩ := (A.get_iff ..).mp h
    exact ⟨q.val, hq⟩

-- 读法：`z ∈ adjacent G v` 与 `∃ j, A.nav (A.host v) j = A.host z ∧ (A.mask (A.host v) j).1 = true` 等价。这里调用 `A.host.injective`。
theorem mask_eq (v z : G.V × Bool) : z ∈ adjacent G v ↔
    ∃ j, A.nav (A.host v) j = A.host z ∧ (A.mask (A.host v) j).1 = true := by
  refine ⟨fun h => ⟨A.index v z, A.nav_link h, by simp [mask, A.get_link h]⟩, ?_⟩
  rintro ⟨j, hj, ht⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ht
  obtain ⟨u, hu, t, _, he⟩ := (A.get_iff ..).mp ha
  have := A.host.injective hu
  subst u
  simp only [nav, ha, Option.getD_some] at hj
  exact A.host.injective (he.trans hj) ▸ t.property

-- 读法：`A.get i j` 等于 `some w`。
private theorem occupiedFromAddresses {i j w} (hw : A.nav i j = w) (hne : w ≠ i) :
    A.get i j = some w := by
  unfold nav at hw
  cases he : A.get i j with
  | none => rw [he] at hw; exact (hne hw.symm).elim
  | some _ => simpa [he] using hw

-- 读法：`a` 等于 `b`。
theorem unique {i a b} (hne : A.nav i a ≠ i) (h : A.nav i a = A.nav i b) : a = b := by
  obtain ⟨v, hv, t, ht, he⟩ := (A.get_iff ..).mp (A.occupiedFromAddresses rfl hne)
  obtain ⟨v', hv', t', ht', he'⟩ := (A.get_iff ..).mp (A.occupiedFromAddresses h.symm hne)
  have := A.host.injective (hv'.trans hv.symm)
  subst v'
  have : t = t' := Subtype.ext (A.host.injective (he.trans he'.symm))
  rw [← ht, ← ht', this]

-- 读法：存在唯一的 `k`，`A.nav (A.nav i j) k` 等于 `i`。
theorem reciprocal (i : B m) (j : B 3) (h : A.nav i j ≠ i) :
    ∃! k, A.nav (A.nav i j) k = i := by
  obtain ⟨v, hv, t, _, he⟩ := (A.get_iff ..).mp (A.occupiedFromAddresses rfl h)
  have hk : A.nav (A.nav i j) (A.index t.val v) = i := by
    rw [← he, A.nav_link (adj_symm G _ _ t.property), hv]
  exact ⟨_, hk, fun k hm => A.unique (fun e => h (e.symm.trans hm)) (hm.trans hk.symm)⟩

end Addresses
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

/-!
# 所有初始栈共用的固定调色板

模式存储一张三价表及其关联端口的短名称。相应的字典条目计算整个栈上各项的乘积。标签长度仅依赖基域。

**英文原文**

A fixed palette for all initial stacks

A pattern stores one trivalent table and the short names of its
incident ports. Its dictionary entry evaluates the product across
the stack. The label length depends only on the ground field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Coloring Assembly Packing Transcript
open scoped Classical

-- 读法：在后续公式中，`PortInfo` 是 `Bool × Option (B 3 × B 0 × B 2)` 的缩写。
abbrev PortInfo := Bool × Option (B 3 × B 0 × B 2)
-- 读法：在后续公式中，`Atom` 是 `(B 2 → Option PortInfo) × ((B 2 → Bool) → F)` 的缩写。
abbrev Atom (F : Type) := (B 2 → Option PortInfo) × ((B 2 → Bool) → F)

variable {F : Type} [Field F] {a b : Wire} {m h u : ℕ} {G : Diagram F a b}

-- 读法：当 `i.isSome` 成立时取 `u`，否则取 `0`。
def width (u : ℕ) (i : Option PortInfo) := if i.isSome then u else 0

-- 读法：用字段 `width`、`direction`、`peer`、`value` 构造 `Pattern F 3 0 2`。
def pattern (u : ℕ) (a : Atom F) : Pattern F 3 0 2 where
  width _ q := width u (a.1 q)
  direction _ q := ((a.1 q).map Prod.fst).getD false
  peer _ q := (a.1 q).bind Prod.snd
  value _ z := ∏ i : Fin u, a.2 fun q =>
    if h : i.val < width u (a.1 q) then z q ⟨i.val, h⟩ else false

namespace Addresses
variable (A : Addresses G m)

-- 读法：`stub` 的取值由 `A.localPort (G.portEquiv.symm q).1 (G.portEquiv.symm q).2` 给出。
def stub (q : G.End) : B 2 :=
  A.localPort (G.portEquiv.symm q).1 (G.portEquiv.symm q).2

omit [Field F] in
-- 读法：`A.stub (G.portEquiv ⟨v, t⟩)` 等于 `A.localPort v t`。
@[simp] theorem stub_port (v : G.V) (t : G.Port v) :
    A.stub (G.portEquiv ⟨v, t⟩) = A.localPort v t :=
  congrArg (fun z : Σ i, G.Port i => A.localPort z.1 z.2) (G.portEquiv.symm_apply_apply ⟨v, t⟩)

-- 读法：`key` 的取值由 `(A.host (G.station q, false), A.stub q)` 给出。
def key (q : G.End) := (A.host (G.station q, false), A.stub q)

omit [Field F] in
-- 读法：`A.key` 是单射。
theorem key_inj : Function.Injective A.key := by
  intro p q he
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective p
  obtain ⟨⟨w, j⟩, rfl⟩ := G.portEquiv.surjective q
  simp only [key, Diagram.station_port, stub_port, Prod.mk.injEq, A.host.injective.eq_iff, and_true] at he
  obtain ⟨rfl, h⟩ := he
  rw [(A.localPort _).injective h]

-- 读法：`linkAt` 的结果类型为 `PortInfo`。
def linkAt (q : G.End) : PortInfo :=
  (q.isRight, match q with
    | .inl (.inr e) => some (A.index (G.source e, false) (G.target e, false), 0, A.stub (.inr (.inr e)))
    | .inr (.inr e) => some (A.index (G.target e, false) (G.source e, false), 0, A.stub (.inl (.inr e)))
    | _ => none)

-- 读法：`atom` 的结果类型为 `Atom F`。
def atom (v : B m) : Atom F :=
  (fun i => Function.extend A.key (fun q => some (A.linkAt q)) (fun _ => none) (v, i),
    if h : ∃ z, A.host (z, false) = v then
      fun x => sample (G.table h.choose) (x ∘ A.localPort h.choose)
    else fun _ => 1)

-- 读法：`(A.atom (A.key q).1).1 (A.key q).2` 等于 `some (A.linkAt q)`。使用 `A.key_inj.extend_apply` 给出的结论。
theorem info (q : G.End) : (A.atom (A.key q).1).1 (A.key q).2 = some (A.linkAt q) :=
  A.key_inj.extend_apply (fun q => some (A.linkAt q)) (fun _ => none) q

-- 读法：存在 `q`，`A.key q` 等于 `(v, i)`。
theorem info_of (v : B m) (i : B 2) (hi : (A.atom v).1 i ≠ none) :
    ∃ q, A.key q = (v, i) := by
  by_contra h
  exact hi (Function.extend_apply' (fun q => some (A.linkAt q)) (fun _ => none) _ h)

-- 读法：`(A.atom (A.host (v, false))).2` 等于 `fun x => sample (G.table v) (x ∘ A.localPort v)`。
theorem scalar (v : G.V) : (A.atom (A.host (v, false))).2 =
    fun x => sample (G.table v) (x ∘ A.localPort v) := by
  have h : ∃ z, A.host (z, false) = A.host (v, false) := ⟨v, rfl⟩
  unfold atom
  rw [dite_eq_left h, (Prod.mk.inj (A.host.injective h.choose_spec)).1]

end Addresses

variable (F) [Fintype F]

-- 读法：`length` 的取值由 `Nat.clog 2 (Nat.card (Atom F))` 给出。
def length := Nat.clog 2 (Nat.card (Atom F))

-- 读法：`label` 的结果类型为 `Atom F ↪ B (length F)`。
def label : Atom F ↪ B (length F) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, length, Nat.card_eq_fintype_card]
    exact Nat.le_pow_clog (by decide) _))

-- 读法：用字段 `m`、`h`、`k`、`e` 构造 `Scheme F`。
abbrev scheme (m h u : ℕ) : Scheme F where
  m := m
  h := h
  k := 0
  e := 2
  d := 3
  ℓ := length F
  decode := Function.extend (label F) (pattern u) (fun _ => pattern u (fun _ => none, fun _ => 1))

variable {F} (A : Addresses G m)

-- 读法：输入 `i` 时返回 `(A.nav i, fun _ => (label F) (A.atom i))`。
def records (h u : ℕ) : (scheme F m h u).format.obj :=
  fun i => (A.nav i, fun _ => (label F) (A.atom i))

-- 读法：`(scheme F m h u).pattern (records A h u) i` 等于 `pattern u (A.atom i.1)`。
theorem pattern_at (i : (scheme F m h u).Vtx) :
    (scheme F m h u).pattern (records A h u) i = pattern u (A.atom i.1) :=
  (label F).injective.extend_apply (pattern u) (fun _ => pattern u (fun _ => none, fun _ => 1)) (A.atom i.1)

-- 读法：要证明的命题是 `Fmt.Reciprocal (.vec h (.addr (length F))) (records A h u)`。使用 `A.reciprocal` 给出的结论。
theorem records_reciprocal (h u : ℕ) :
    Fmt.Reciprocal (.vec h (.addr (length F))) (records A h u) := A.reciprocal

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

/-!
# 初始布置中的区段

**英文原文**

Spans of the initial posting
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
open Coloring Assembly Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {a b : Wire} {m h u : ℕ} {G : Diagram F a b}
  (A : Addresses G m)

local notation "S" => scheme F m h u
local notation "R" => records A h u

-- 读法：用字段 `toFun`、`inj'`、`obtain` 构造 `Cell h × G.V ↪ B m × B h × B 0`。
def vertex (h : ℕ) : Cell h × G.V ↪ B m × B h × B 0 where
  toFun x := (A.host (x.2, false), cellIndex h x.1, 0)
  inj' := by
    intro x y he
    obtain ⟨hv, hb, _⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
    exact Prod.ext ((cellIndex h).injective hb) (Prod.mk.inj (A.host.injective hv)).1

-- 读法：`span` 的取值由 `(A.vertex h (z, G.station e), A.stub e)` 给出。
def span (z : Cell h) (e : G.End) := (A.vertex h (z, G.station e), A.stub e)

-- 读法：`(S).width R p` 等于 `width u ((A.atom p.1.1).1 p.2)`。
theorem width_eq (p : (S).Span) : (S).width R p = width u ((A.atom p.1.1).1 p.2) := by
  rw [Scheme.width, pattern_at]; rfl

-- 读法：`(S).width R (A.span z e)` 等于 `u`。
theorem width_at (z : Cell h) (e : G.End) : (S).width R (A.span z e) = u := by
  rw [width_eq]
  change width u ((A.atom (A.key e).1).1 (A.key e).2) = u
  rw [A.info]; rfl

-- 读法：`(S).direction R (A.span z e)` 等于 `e.isRight`。
theorem direction_at (z : Cell h) (e : G.End) : (S).direction R (A.span z e) = e.isRight := by
  rw [Scheme.direction, pattern_at]
  change (((A.atom (A.key e).1).1 (A.key e).2).map Prod.fst).getD false = _
  rw [A.info]; rfl

-- 读法：`((S).pattern R (A.span z e).1).peer (A.span z e).1.2.2 (A.span z e).2` 等于 `(A.linkAt e).2`。
theorem link_at (z : Cell h) (e : G.End) :
    ((S).pattern R (A.span z e).1).peer (A.span z e).1.2.2 (A.span z e).2 = (A.linkAt e).2 := by
  rw [pattern_at]
  change ((A.atom (A.key e).1).1 (A.key e).2).bind Prod.snd = _
  rw [A.info]; rfl

-- 读法：存在 `z e`，`p` 等于 `A.span z e`。这里调用 `Prod.ext`。
theorem represent (p : (S).Span) (hp : (A.atom p.1.1).1 p.2 ≠ none) :
    ∃ z e, p = A.span z e := by
  obtain ⟨e, h⟩ := A.info_of _ _ hp
  obtain ⟨hx, hy⟩ := Prod.mk.inj h
  refine ⟨(cellIndex _).symm p.1.2.1, e, Prod.ext ?_ hy.symm⟩
  exact Prod.ext hx.symm (Prod.ext ((cellIndex _).apply_symm_apply _).symm (Fin.eq_zero _))

-- 读法：存在 `z e`，`p` 等于 `A.span z e`。
theorem occupied (p : (S).Span) (hp : 0 < (S).width R p) : ∃ z e, p = A.span z e := by
  refine A.represent p fun he => ?_
  simp [width_eq, he, width] at hp

-- 读法：`edgeEnd` 的取值由 `cond b (.inr (.inr e)) (.inl (.inr e))` 给出。
/-- 每条内部边有两个具名端点。

英文原文：An internal edge has two named ends.
-/
def edgeEnd (e : G.E) (b : Bool) : G.End := cond b (.inr (.inr e)) (.inl (.inr e))

-- 读法：`(S).peer R (A.span z (edgeEnd e t))` 等于 `some (A.span z (edgeEnd e (!t)))`。对 `t` 分类讨论。
theorem peer_edge (z : Cell h) (e : G.E) (t : Bool) :
    (S).peer R (A.span z (edgeEnd e t)) = some (A.span z (edgeEnd e (!t))) := by
  have hz : (G.target e, false) ∈ adjacent G (G.source e, false) :=
    Finset.mem_product.mpr ⟨target_mem G e, Finset.mem_univ _⟩
  rw [Scheme.peer, link_at]
  cases t
  · exact congrArg (fun x => some ((x, cellIndex h z, 0), A.stub (.inr (.inr e)))) (A.nav_link hz)
  · exact congrArg (fun x => some ((x, cellIndex h z, 0), A.stub (.inl (.inr e))))
      (A.nav_link (adj_symm G _ _ hz))

-- 读法：`(S).peer R (A.span z (boundaryEnd G i))` 等于 `none`。
theorem peer_outer (z : Cell h) (i : Outer a b) :
    (S).peer R (A.span z (boundaryEnd G i)) = none := by
  rw [Scheme.peer, link_at]
  cases i <;> rfl

-- 读法：要证明的命题是 `(S).Proper R`。
theorem proper : (S).Proper R := by
  intro p q hp
  have used : (A.atom p.1.1).1 p.2 ≠ none := by
    intro hh
    rw [Scheme.peer, pattern_at] at hp
    simp [pattern, hh] at hp
  obtain ⟨z, e, rfl⟩ := A.represent p used
  have internal (e : G.E) (t : Bool) (hp : (S).peer R (A.span z (edgeEnd e t)) = some q) :
      (S).peer R q = some (A.span z (edgeEnd e t)) ∧
        (S).width R (A.span z (edgeEnd e t)) = (S).width R q ∧
        (S).direction R (A.span z (edgeEnd e t)) ≠ (S).direction R q := by
    rw [peer_edge, Option.some.injEq] at hp
    subst q
    rw [peer_edge, Bool.not_not, width_at, width_at, direction_at, direction_at]
    exact ⟨rfl, rfl, by cases t <;> simp [edgeEnd]⟩
  rcases e with (i|e)|(j|e)
  · have := (A.peer_outer (u := u) z (.inl i)).symm.trans hp; cases this
  · exact internal e false hp
  · have := (A.peer_outer (u := u) z (.inr j)).symm.trans hp; cases this
  · exact internal e true hp

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
end

/-!
# 初始乘积表的局部引脚双射

**英文原文**

Local pin bijections for the initial product tables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
open Assembly Packing Coloring Transcript
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {a b : Wire} {m h u n : ℕ} {G : Diagram F a b}
  (A : Addresses G m)

local notation "S" => scheme F m h u
local notation "R" => records A h u

-- 读法：`(S).width R (A.vertex h v, A.localPort v.2 p)` 等于 `u`。这里调用 `A.width_at`。
theorem port_width (v : Cell h × G.V) (p : G.Port v.2) :
    (S).width R (A.vertex h v, A.localPort v.2 p) = u := by
  simpa only [span, Diagram.station_port, stub_port] using A.width_at (u := u) v.1 (G.portEquiv ⟨v.2, p⟩)

-- 读法：`carrying` 的取值由 `⟨A.localPort v.2 p.2, p.1.cast (A.port_width v p.2).symm⟩` 给出。
def carrying (v : Cell h × G.V) (p : Fin u × G.Port v.2) :
    (S).LocalPin R (A.vertex h v) := ⟨A.localPort v.2 p.2, p.1.cast (A.port_width v p.2).symm⟩

-- 读法：`(A.carrying (u := u) v)` 是双射。这里调用 `Prod.ext`。
private theorem bijective (v : Cell h × G.V) : Function.Bijective (A.carrying (u := u) v) := by
  constructor
  · intro x y he
    have hi := congrArg (fun p => p.2.val) he
    have hs := congrArg Sigma.fst he
    exact Prod.ext (Fin.ext hi) ((A.localPort _).injective hs)
  · rintro ⟨s, j⟩
    obtain ⟨z, e, he⟩ := A.occupied (A.vertex h v, s) (Nat.zero_lt_of_lt j.isLt)
    obtain ⟨⟨a, i⟩, rfl⟩ := G.portEquiv.surjective e
    simp only [span, Diagram.station_port, stub_port, Prod.mk.injEq, (A.vertex h).injective.eq_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨(j.cast (A.port_width (z, a) i), i), rfl⟩

-- 读法：`pins` 的取值由 `(pin (G.table v.2) u).trans (Equiv.ofBijective _ (A.bijective v))` 给出。
def pins (v : Cell h × G.V) : Ports (tensor (G.table v.2) u) ≃ (S).LocalPin R (A.vertex h v) :=
  (pin (G.table v.2) u).trans (Equiv.ofBijective _ (A.bijective v))

omit [Fintype F] in
-- 读法：`p.value k x` 等于 `∏ i : Fin u, a.2 (fun s => if h : i.val < p.width k s then x s ⟨i.val, h⟩ else false)`。
private theorem eval_pattern (p : Pattern F 3 0 2) (a : Atom F) (he : p = pattern u a)
    (k : B 0) (x : ∀ s, Fin (p.width k s) → Bool) :
    p.value k x = ∏ i : Fin u, a.2 (fun s => if h : i.val < p.width k s then x s ⟨i.val, h⟩ else false) := by
  subst p; rfl

-- 读法：`(S).table R v x` 等于 `∏ i : Fin u, (A.atom v.1).2 (fun q => if h : i.val < (S).width R (v, q) then x ⟨q, ⟨i.val, h⟩⟩ else false)`。使用 `eval_pattern` 给出的结论。
theorem value_at (v : (S).Vtx) (x : (S).LocalPin R v → Bool) :
    (S).table R v x = ∏ i : Fin u, (A.atom v.1).2
      (fun q => if h : i.val < (S).width R (v, q) then x ⟨q, ⟨i.val, h⟩⟩ else false) :=
  eval_pattern _ _ (pattern_at A v) v.2.2 (fun q i => x ⟨q, i⟩)

-- 读法：`(S).table R (A.vertex h v) x` 等于 `sample (tensor (G.table v.2) u) (x ∘ A.pins v)`。这里调用 `Finset.prod_congr`。
theorem sample_at (v : Cell h × G.V) (x : (S).LocalPin R (A.vertex h v) → Bool) :
    (S).table R (A.vertex h v) x = sample (tensor (G.table v.2) u) (x ∘ A.pins v) := by
  rw [value_at, sample_tensor, show (A.vertex h v).1 = A.host (v.2, false) from rfl, A.scalar]
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (sample (G.table v.2))
  funext q
  have lt : i.val < (S).width R (A.vertex h v, A.localPort v.2 q) := by rw [port_width]; exact i.isLt
  simp only [Function.comp_apply, dite_eq_left lt, pins, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

-- 读法：`(S).table R v x` 等于 `1`。这里调用 `Prod.ext`。
theorem vacant (v : (S).Vtx) (hv : v ∉ Set.range (A.vertex h)) (x : (S).LocalPin R v → Bool) :
    (S).table R v x = 1 := by
  have hn : ¬∃ z, A.host (z, false) = v.1 := by
    rintro ⟨z, hz⟩
    refine hv ⟨((cellIndex _).symm v.2.1, z), ?_⟩
    exact Prod.ext hz (Prod.ext ((cellIndex _).apply_symm_apply _) (Fin.eq_zero _).symm)
  rw [value_at]
  simp only [atom, dite_eq_right hn, Finset.prod_const_one]

-- 读法：用字段 `vertex`、`pin`、`cover`、`obtain` 构造 `(S).Seating R (gathered G c)`。
def seating (c : Cell h × Fin u ≃ Fin n) : (S).Seating R (gathered G c) where
  vertex := A.vertex h
  pin := A.pins
  cover p := by
    obtain ⟨z, e, he⟩ := A.occupied p.1 (Nat.zero_lt_of_lt p.2.isLt)
    exact ⟨(z, G.station e), congrArg Prod.fst he.symm⟩
  sample := A.sample_at
  vacant := A.vacant

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
end

/-!
# 每个原始栈恰有一个区段的布置

**英文原文**

A posting with one span for each original stack
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {x y : Wire} {m h u n : ℕ} {G : Diagram F x y}
  (A : Addresses G m) (c : Cell h × Fin u ≃ Fin n)

local notation "S" => scheme F m h u
local notation "R" => records A h u

-- 读法：`copyPort` 的取值由 `⟨(t.1, p.1), (pin (G.table p.1) u).symm (t.2, p.2)⟩` 给出。
private def copyPort (t : Cell h × Fin u) (p : Σ v, G.Port v) : Σ j, (gathered G c).Port j :=
  ⟨(t.1, p.1), (pin (G.table p.1) u).symm (t.2, p.2)⟩

-- 读法：`((A.seating c).ends q).1 = A.span t.1 p` 与 `((A.seating c).ends q).2.val = t.2.val` 同时成立。
private theorem read (t : Cell h × Fin u) (p : G.End) (q : (gathered G c).End)
    (hp : (gathered G c).portEquiv.symm q = copyPort c t (G.portEquiv.symm p)) :
    ((A.seating c).ends q).1 = A.span t.1 p ∧ ((A.seating c).ends q).2.val = t.2.val := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective p
  rw [Equiv.symm_apply_apply] at hp
  rw [← (gathered G c).portEquiv.apply_symm_apply q, hp, copyPort, (A.seating c).ends_at]
  have eq : (A.seating c).pin (t.1, v) ((pin (G.table v) u).symm (t.2, i)) =
      A.carrying (t.1, v) (t.2, i) :=
    congrArg (A.carrying (t.1, v)) ((pin (G.table v) u).apply_symm_apply (t.2, i))
  rw [eq]
  simp only [span, stub_port, Diagram.station_port]
  exact ⟨rfl, rfl⟩

-- 读法：结论为 `let q := (A.seating c).ends (edgeEnd (t, e) s) q.1 = A.span t.1 (edgeEnd e s) ∧ q.2.val = t.2.val`。这里调用 `A.read`。
theorem read_edge (t : Cell h × Fin u) (e : G.E) (s : Bool) :
    let q := (A.seating c).ends (edgeEnd (t, e) s)
    q.1 = A.span t.1 (edgeEnd e s) ∧ q.2.val = t.2.val := by
  apply A.read c
  cases s <;> rfl

-- 读法：结论为 `let r := Diagonal.port x n i let t := c.symm r.1 let q := (A.seating c).ends (.inl (.inl i)) q.1 = A.span t.1 (.inl (.inl r.2)) ∧ q.2.val = t.2.val`。使用 `A.read` 给出的结论。
theorem read_input (i : slots (copies x n)) :
    let r := Diagonal.port x n i
    let t := c.symm r.1
    let q := (A.seating c).ends (.inl (.inl i))
    q.1 = A.span t.1 (.inl (.inl r.2)) ∧ q.2.val = t.2.val :=
  A.read c _ _ _ rfl

-- 读法：结论为 `let r := Diagonal.port y n i let t := c.symm r.1 let q := (A.seating c).ends (.inr (.inl i)) q.1 = A.span t.1 (.inr (.inl r.2)) ∧ q.2.val = t.2.val`。使用 `A.read` 给出的结论。
theorem read_output (i : slots (copies y n)) :
    let r := Diagonal.port y n i
    let t := c.symm r.1
    let q := (A.seating c).ends (.inr (.inl i))
    q.1 = A.span t.1 (.inr (.inl r.2)) ∧ q.2.val = t.2.val :=
  A.read c _ _ _ rfl

-- 读法：用字段 `toSeating`、`proper`、`internal`、`obtain` 构造 `(S).Presentation R (gathered G c)`。
def presentation : (S).Presentation R (gathered G c) where
  toSeating := A.seating c
  proper := A.proper
  internal e := by
    obtain ⟨t, e⟩ := e
    have a := A.read_edge c t e false
    have b := A.read_edge c t e true
    change (S).Joins R ((A.seating c).ends (edgeEnd (t, e) false)) ((A.seating c).ends (edgeEnd (t, e) true))
    exact ⟨by rw [a.1, b.1, peer_edge]; rfl, a.2.trans b.2.symm⟩
  input i := by rw [(A.read_input c i).1]; exact A.peer_outer _ (.inl _)
  output i := by rw [(A.read_output c i).1]; exact A.peer_outer _ (.inr _)

-- 读法：用字段 `toPresentation`、`host`、`block`、`stub` 构造 `(S).Posting R (groups G c)`。
def posting : (S).Posting R (groups G c) where
  toPresentation := A.presentation c
  host := A.host
  block := (cellIndex h).toEmbedding
  stub i t := A.stub (edgeEnd i.1 t)
  index := A.index
  vertex_eq _ := rfl
  ordered i t j := by
    have h := A.read_edge c (i.2, j) i.1 t
    cases t <;> exact h
  length i t := by
    have h := A.width_at (u := u) i.2 (edgeEnd i.1 t)
    cases t <;> exact h
  dir i t := by
    have h := A.direction_at (u := u) i.2 (edgeEnd i.1 t)
    cases t <;> exact h
  link i t := by
    have h := A.link_at (u := u) i.2 (edgeEnd i.1 t)
    cases t <;> exact h

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack.Addresses
end

/-!
# 外部历史与各次出现的初始负载

**英文原文**

Exterior history and initial occurrence loads
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Assembly Coloring Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h u m : ℕ} {G : Diagram F x y}

-- 读法：`push (start G h u).park (fun _ => 1) ((v, t), z)` 等于 `if t then (exterior G id v : ℝ) * u else 0`。
theorem parked (v : G.V) (t : Bool) (z : Cell h) :
    push (start G h u).park (fun _ => 1) ((v, t), z) =
      if t then (exterior G id v : ℝ) * u else 0 := by
  rw [push, ← (bit h u x y).sum_comp, Fintype.sum_prod_type, sum_comm]
  simp_rw [Fintype.sum_prod_type, start_park]
  rw [port_load]
  change (∑ i : Outer x y, ∑ s : Cell h, ∑ _ : Fin u,
    @ite ℝ (((portEnd G i, true), s) = ((v, t), z)) (Classical.propDecidable _) 1 0) = _
  simp only [Prod.mk.injEq]
  cases t <;> simp [ite_and, push, add_mul, sum_mul, ite_mul, -sum_boole]

-- 读法：`((start G h u).reserve k l).load (v, t) z` 等于 `(if t then exterior G id v else G.arity v : ℕ) * (u : ℝ)`。
theorem load_initial (v : G.V) (t : Bool) (z : Cell h) (k l : ℕ) :
    ((start G h u).reserve k l).load (v, t) z =
      (if t then exterior G id v else G.arity v : ℕ) * (u : ℝ) := by
  let Q := (start G h u).reserve k l
  rw [Q.load_eq ((v, t), z)]
  simp only [show Q.past ((v, t), z) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero]
  change push (locate G (ordinal h u) false) (fun i => ((gathered G (ordinal h u)).arity i : ℝ)) _ +
      1 * push (start G h u).park (fun _ => 1) ((v, t), z) = _
  rw [parked, one_mul]
  have eq (i : Cell h × G.V) : (gathered G (ordinal h u)).arity i = u * G.arity i.2 := by
    simp only [Diagram.arity, wd_copies, mul_add]
  unfold push
  simp_rw [eq]
  change (∑ i : Cell h × G.V, @ite ℝ (((i.2, false), i.1) = ((v, t), z)) (Classical.propDecidable _)
    (↑(u * G.arity i.2)) 0) + _ = _
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  cases t <;> simp [ite_and, mul_comm]

namespace Addresses
variable [Fintype F] (A : Addresses G m)
local notation "S" => scheme F m h u
local notation "R" => records A h u

-- 读法：`initial` 的结果类型为 `(S).Posting R ((start G h u).reserve k l)`。
def initial (k l : ℕ) : (S).Posting R ((start G h u).reserve k l) :=
  let p := A.posting (ordinal h u)
  ⟨p.toPresentation, p.host, p.block, p.stub, p.index, p.vertex_eq, p.ordered, p.length, p.dir, p.link⟩

-- 读法：结论为 `let q := ((A.initial (h := h) (u := u) k l).toPresentation.boundary (bit h u x y ((z, t), i))).val q.1 = A.span z (boundaryEnd G i) ∧ q.2.val = t.val`。对 `i` 分类讨论。
theorem boundary (k l : ℕ) (i : Outer x y) (z : Cell h) (t : Fin u) :
    let q := ((A.initial (h := h) (u := u) k l).toPresentation.boundary (bit h u x y ((z, t), i))).val
    q.1 = A.span z (boundaryEnd G i) ∧ q.2.val = t.val := by
  let c := ordinal h u
  cases i with
  | inl i =>
    have hx := A.read_input c ((Diagonal.port x (2 ^ h * u)).symm (c (z, t), i))
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at hx
    exact hx
  | inr i =>
    have hy := A.read_output c ((Diagonal.port y (2 ^ h * u)).symm (c (z, t), i))
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at hy
    exact hy

-- 读法：存在 `a : Trail.Record (scheme F m h u) h d e`，要证明的命题是 `Trail.Tracks (A.initial (h := h) (u := u) k l).toPresentation name a`。
theorem history (ht : G.Trivalent) (k l : ℕ) (hu : 0 < u) {d e : ℕ} (hd : 3 ≤ d)
    (name : Outer x y ↪ (Fin e → Bool)) :
    ∃ a : Trail.Record (scheme F m h u) h d e,
      Trail.Tracks (A.initial (h := h) (u := u) k l).toPresentation name a := by
  let host : G.V ↪ B m := ⟨fun v => A.host (v, false), fun _ _ h => (Prod.mk.inj (A.host.injective h)).1⟩
  refine Trail.initial G ht _ host hu hd name fun i z => ?_
  refine ⟨A.span z (boundaryEnd G i), A.width_at z _, ?_, A.boundary k l i z⟩
  change A.host (G.station (boundaryEnd G i), false) = _
  rw [station_boundary]; rfl

end Addresses
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

/-!
# 块记录长度恒定的初始模板

计数器指明一侧和从零到三的一个重数。调色板及计数器长度均与栈宽、站点数和复制倍数无关。

**英文原文**

Initial template with constant-length block records

The counter names a side and a multiplicity from zero to three.
Both the palette and the counter length are independent of the
stack width, the number of stations and the replication factor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Assembly Coloring Packing Finset
open scoped Classical

-- 读法：`counterCode` 的取值由 `Fintype.equivOfCardEq (by simp)` 给出。
private def counterCode : Bool × Fin 4 ≃ B 3 := Fintype.equivOfCardEq (by simp)

variable (F : Type) [Field F] [Fintype F]

-- 读法：用字段 `scheme`、`count`、`load`、`park` 构造 `Template F`。
abbrev template (m h u : ℕ) : Template F where
  scheme := scheme F m h u
  count := 3
  load i := (counterCode.symm i).2.val * (u : ℝ)
  park i := if (counterCode.symm i).1 then (counterCode.symm i).2.val * (u : ℝ) else 0
  past _ := 0
  order := Equiv.refl _
  full := false

-- 读法：`(template F m h u).format.width` 等于 `2 ^ m * (8 * (m + 2) + 2 + 2 ^ h * (length F + 3))`。
theorem template_width (m h u : ℕ) :
    (template F m h u).format.width = 2 ^ m * (8 * (m + 2) + 2 + 2 ^ h * (length F + 3)) :=
  (template F m h u).width

namespace Addresses
variable {F} {a b : Wire} {h u m : ℕ} {G : Diagram F a b} (A : Addresses G m) (ht : G.Trivalent)

omit [Field F] [Fintype F] in
-- 读法：`exterior G id v` 不超过 `G.arity v`。这里调用 `Nat.cast_le`。
private theorem exterior_le (v : G.V) : exterior G id v ≤ G.arity v := by
  have := site_arity G id v
  simp only [push, id_eq, sum_ite_eq', mem_univ, ite_true] at this
  apply Nat.cast_le (α := ℝ) |>.mp
  rw [this]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

-- 读法：`meter` 的结果类型为 `B 3`。
private def meter (v : G.V × Bool) : B 3 :=
  counterCode (v.2, ⟨if v.2 then exterior G id v.1 else G.arity v.1, by
    have := ht v.1
    have := exterior_le v.1
    split_ifs <;> omega⟩)

-- 读法：`header` 的取值由 `((true, v.2), A.mask (A.host v), fun _ => meter ht v)` 给出。
private def header (h : ℕ) (v : G.V × Bool) : (Bool × Bool) × ((B 3 → Bool × Bool) × (B h → B 3)) :=
  ((true, v.2), A.mask (A.host v), fun _ => meter ht v)

-- 读法：`idle` 的取值由 `((false, false), fun _ => (false, false), fun _ => 0)` 给出。
private def idle (h : ℕ) : (Bool × Bool) × ((B 3 → Bool × Bool) × (B h → B 3)) :=
  ((false, false), fun _ => (false, false), fun _ => 0)

-- 读法：`snapshot` 的取值由 `(records A h u, Function.extend A.host (A.header ht h) (fun _ => idle h))` 给出。
def snapshot (h u : ℕ) : (template F m h u).format.obj :=
  (records A h u, Function.extend A.host (A.header ht h)
    (fun _ => idle h))

-- 读法：`(A.snapshot ht h u).2 (A.host v)` 等于 `A.header ht h v`。使用 `A.host.injective.extend_apply` 给出的结论。
private theorem header_at (v : G.V × Bool) :
    (A.snapshot ht h u).2 (A.host v) = A.header ht h v :=
  A.host.injective.extend_apply (A.header ht h) (fun _ => idle h) v

-- 读法：用字段 `post`、`block`、`live`、`frozen` 构造 `(template F m h u).Encodes (A.snapshot ht h u) ((start G h u).reserve k l)`。
/-- 任意历史预算都可使用相同的初始元数据。

英文原文：The same initial metadata works with any history budget.
-/
def encodes (h u k l : ℕ) :
    (template F m h u).Encodes (A.snapshot ht h u) ((start G h u).reserve k l) where
  post := A.initial k l
  block _ := rfl
  live i := by
    change ((A.snapshot ht h u).2 i).1.1 = true ↔ i ∈ Set.range A.host
    by_cases hi : i ∈ Set.range A.host
    · obtain ⟨v, rfl⟩ := hi
      rw [header_at]
      exact iff_of_true rfl ⟨v, rfl⟩
    · have he : ((A.snapshot ht h u).2 i).1.1 = false := by
        exact congrArg (fun x => x.1.1) (Function.extend_apply' (A.header ht h) (fun _ => idle h) i hi)
      simp [he, hi]
  frozen v := by
    change G.V × Bool at v
    change ((A.snapshot ht h u).2 (A.host v)).1.2 = true ↔ v.2 = true
    rw [header_at]; rfl
  closed := A.closed
  reciprocal := records_reciprocal A h u
  edge v z := by
    change G.V × Bool at v z
    change _ ↔ ∃ j, A.nav (A.host v) j = A.host z ∧ (((A.snapshot ht h u).2 (A.host v)).2.1 j).1 = true
    rw [header_at]
    exact A.mask_eq v z
  core v z := by
    change G.V × Bool at v z
    change _ ↔ ∃ j, A.nav (A.host v) j = A.host z ∧ (((A.snapshot ht h u).2 (A.host v)).2.1 j).2 = true
    rw [header_at]
    exact A.mask_eq v z
  load v i := by
    change G.V × Bool at v
    change (template F m h u).load (((A.snapshot ht h u).2 (A.host v)).2.2 _) = _
    rw [header_at]
    obtain ⟨v, b⟩ := v
    rw [load_initial]
    simp only [template, header, meter, Equiv.symm_apply_apply]
  park v i := by
    change G.V × Bool at v
    change (template F m h u).park (((A.snapshot ht h u).2 (A.host v)).2.2 _) =
      push (start G h u).park (fun _ => 1) (v, i)
    rw [header_at]
    obtain ⟨v, b⟩ := v
    rw [parked]
    cases b <;> simp [template, header, meter]
  past _ _ := rfl

end Addresses
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

/-!
# 下降过程的初始数据

每个非空活动位置至少携带一个完整栈，足以承担其定长标签的成本。在第一阶段之前扫描一次，取出各孤立标量站点的系数。

**英文原文**

Initial data for the descent

Each nonempty active position carries at least one whole stack.
This pays for its constant-length label. A sweep extracts the
coefficients of isolated scalar stations before the first phase.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Assembly Coloring Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (S : Setup F x y)

-- 读法：`S.first.tetherLoad ((v, t), b) + degree S.first.pair ((v, t), b) * S.U` 等于 `(if t then 0 else S.G.arity v) * S.U`。这里调用 `Nat.cast_injective`。
private theorem incidence (v : S.G.V) (t : Bool) (b : Cell S.h) :
    S.first.tetherLoad ((v, t), b) + degree S.first.pair ((v, t), b) * S.U =
      (if t then 0 else S.G.arity v) * S.U := by
  have he := load_initial (G := S.G) (u := S.U) v t b S.cap S.discount
  change (S.first.tetherLoad ((v, t), b) : ℝ) + degree S.first.pair ((v, t), b) * (S.U : ℝ) +
    1 * push (start S.G S.h S.U).park (fun _ => 1) ((v, t), b) +
      S.first.rate * (0 : ℕ) = _ at he
  rw [parked] at he
  apply Nat.cast_injective (R := ℝ)
  push_cast
  cases t <;> simp at he ⊢ <;> linarith

-- 读法：要证明的命题是 `S.first.Tracks S.first 1`。这里调用 `mem_singleton.mpr`。
private theorem first_tracks : S.first.Tracks S.first 1 := by
  have he (v : S.first.V) : (S.first.reach S.first v).card ≤ 1 := by
    refine (card_le_card (t := {v}) ?_).trans_eq (card_singleton v)
    intro i hi
    obtain ⟨_, h, h'⟩ := (HostNet.mem_reach _ _).mp hi
    exact mem_singleton.mpr (h'.symm.trans h)
  exact ⟨he, by simpa using he⟩

variable [Fintype F] (w M : ℕ)

-- 读法：在后续公式中，`initialTemplate` 是 `template F (max w (Nat.clog 2 (2 * M))) S.h S.U` 的缩写。
abbrev initialTemplate := template F (max w (Nat.clog 2 (2 * M))) S.h S.U

-- 读法：`initialBudget` 的取值由 `⟨6 * (S.U / S.z), length F + 1, 1, 3 * (M : ℝ) * S.count, 0⟩` 给出。
def initialBudget (S : Setup F x y) (M : ℕ) : Budget :=
  ⟨6 * (S.U / S.z), length F + 1, 1, 3 * (M : ℝ) * S.count, 0⟩

local notation "T" => initialTemplate S w M

-- 读法：存在 `d : Snapshot.Data S T S.U`，`d.G.diagram.eval = power S.G.eval S.count` 与 `Ready 8 (initialBudget S M) d.sweep` 同时成立。
private theorem first_ready (ht : S.G.Trivalent) (hn : Nonempty S.G.V)
    (hM : Fintype.card S.G.V ≤ M) (hu : 0 < S.U) (hz : S.z ∣ S.U) (hd : 3 ≤ S.d) :
    ∃ d : Snapshot.Data S T S.U, d.G.diagram.eval = power S.G.eval S.count ∧
      Ready 8 (initialBudget S M) d.sweep := by
  let m := max w (Nat.clog 2 (2 * M))
  have hm : 2 * Fintype.card S.G.V ≤ 2 ^ m :=
    (Nat.mul_le_mul_left _ hM).trans ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))
  obtain ⟨a⟩ := addresses S.G m ht hm
  obtain ⟨trail, htrail⟩ := a.history (h := S.h) ht S.cap S.discount hu hd S.name
  let d : Snapshot.Data S T S.U :=
    ⟨S.first, a.snapshot ht S.h S.U, trail, a.encodes ht S.h S.U S.cap S.discount,
      htrail, HostNet.Preserves.refl _⟩
  -- 推导：记下中间结论 `empty`：`(start S.G S.h S.U).mass = 0`。
  have empty : (start S.G S.h S.U).mass = 0 := by
    change ∑ _ : (start S.G S.h S.U).V × Cell S.h, (0 : ℕ) = 0
    simp
  refine ⟨d, start_exact _, ⟨⟨(hn.some, false)⟩, d.sweep_neutral, ?_, ?_, first_tracks S, ?_, ?_⟩⟩
  · apply (d.sweep_tagged _).mpr
    rintro ⟨v, t⟩ b hab
    have hl : S.z ≤ S.first.tetherLoad ((v, t), b) + degree S.first.pair ((v, t), b) * S.U := by
      change 0 < S.first.tetherLoad ((v, t), b) + degree S.first.pair ((v, t), b) * S.U at hab
      rw [incidence] at hab ⊢
      exact (Nat.le_of_dvd hu hz).trans (Nat.le_mul_of_pos_left S.U (Nat.pos_of_mul_pos_right hab))
    apply Nat.mul_le_mul
    · exact (History.Dense.used_le.mpr (Fin.isLt _)).trans (Nat.le_succ _)
    · exact hl.trans (by change _ ≤ 0 + S.first.tetherLoad _ + degree S.first.pair _ * S.U; omega)
  · have hb : S.first.Bounded 8 8 (3 * (S.U : ℝ)) :=
      (bounded S.G (ordinal S.h S.U) ht).start_budget _ empty S.cap S.discount
    -- 推导：记下中间结论 `hb'`：`8 ≤ degreeBound S (T).sweep 8`。
    have hb' : 8 ≤ degreeBound S (T).sweep 8 :=
      (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    refine ⟨hb.1, fun v => (hb.2.1 v).trans hb', ?_⟩
    intro v i
    refine (hb.2.2 v i).trans ?_
    change 3 * (S.U : ℝ) ≤ (6 * (S.U / S.z) : ℕ) * (S.z : ℝ)
    rw [← Nat.cast_mul, mul_assoc, Nat.div_mul_cancel hz, Nat.cast_mul]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) S.U]
  · have hh := S.G.cost_trivalent ht
    rw [S.G.cost_eq] at hh
    -- 推导：记下中间结论 `hE`：`Fintype.card S.G.E ≤ 3 * M`。
    have hE : Fintype.card S.G.E ≤ 3 * M := by omega
    change ((start S.G S.h S.U).X : ℝ) ≤ 3 * (M : ℝ) * S.count
    rw [start_width, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (by positivity)
  · change ((start S.G S.h S.U).mass : ℝ) ≤ 0
    rw [empty, Nat.cast_zero]

-- 读法：这里调用 `Snapshot.sweep`。
theorem begin_frame (ht : S.G.Trivalent) (hn : Nonempty S.G.V)
    (hM : Fintype.card S.G.V ≤ M) (hu : 0 < S.U) (hz : S.z ∣ S.U) (hd : 3 ≤ S.d) :
    ∃ (X : Assembly.Snapshot.{1} F S.input S.output) (i : X.state) (v : X.port.obj),
      X.port.width = (S.format T).width ∧ X.eval i = power S.G.eval S.count ∧
      (∀ a b, X.encode i a b = v) ∧
      Transforms F (3 + 2 * length F) {Snapshot.sweepTable T} X
        (frame S (T).sweep S.U 8 (initialBudget S M)) (Snapshot.sweepCost S T) := by
  obtain ⟨d, he, h⟩ := first_ready S w M ht hn hM hu hz hd
  let P := fun q : Snapshot.Data S T S.U => Ready 8 (initialBudget S M) q.sweep
  refine ⟨Snapshot.restrict P, ⟨d, h⟩, d.code, rfl, he, fun _ _ => rfl, ?_⟩
  exact Snapshot.sweep (fun _ h => h) (by omega)
    (show 2 * length F ≤ 3 + 2 * length F by omega) (Set.mem_singleton _)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end

section
/-!
# 初始帧的成本与控制界

**英文原文**

Cost and control limits for the initial frame
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
open Assembly Coloring

variable {F : Type} [Field F] [Fintype F] {x y : Wire}

omit [Field F] [Fintype F] in
-- 读法：`Snapshot.sweepCost S T + (S.format T).width` 不超过 `6 * (S.format T).width`。这里调用 `le_trans`。
private theorem sweep_cost (S : Setup F x y) (T : Template F) (hc : 1 ≤ T.count) :
    Snapshot.sweepCost S T + (S.format T).width ≤ 6 * (S.format T).width := by
  have he : (S.format T).width = T.scheme.format.width +
      (Format.vec T.scheme.m T.header).width + (Trail.format T.scheme S.h S.d S.e).width := by
    rw [Format.width_pair, Format.width_pair]
  have hw : 2 ^ T.scheme.m * 2 ^ T.scheme.h ≤ (S.format T).width := by
    rw [Format.width_pair, Template.width]
    apply le_trans _ (Nat.le_add_right _ _)
    apply Nat.mul_le_mul_left
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _)
  have hu : updateCost T.scheme.m T.scheme.d T.scheme.h (.addr T.scheme.ℓ) (.addr T.scheme.ℓ) ≤
      4 * T.scheme.format.width + 2 ^ T.scheme.m * 2 ^ T.scheme.h := by
    rw [updateCost, Fmt.width_rows, Format.width_addr]
    ring_nf
    omega
  unfold Snapshot.sweepCost
  omega

-- 读法：结论为 `let T := initialTemplate S w M Snapshot.sweepCost S T + (S.format T).width ≤ 600 * A ^ 3 * 2 ^ (T.scheme.m + S.h) + 600 * L * 2 ^ T.scheme.m * w`。
theorem start_bound {S : Setup F x y} {w M A L : ℕ} (hL : 8 ≤ L) (ha : L ≤ A) (hw : 1 ≤ w)
    (hm : max w (Nat.clog 2 (2 * M)) ≤ 3 * w) (he : S.e ≤ 3 * w)
    (hd : S.d ≤ L) (hh : S.h ≤ A) (ht : length F ≤ A) :
    let T := initialTemplate S w M
    Snapshot.sweepCost S T + (S.format T).width ≤
      600 * A ^ 3 * 2 ^ (T.scheme.m + S.h) + 600 * L * 2 ^ T.scheme.m * w := by
  let T := initialTemplate S w M
  have hv := Regroup.format_bound (T := T) (by omega : 2 ≤ L) ha hw rfl hm he hL hd hh ht
    (show 4 ≤ A by omega) (show 3 ≤ A by omega)
  calc
    _ ≤ 6 * (S.format T).width := sweep_cost S T (show 1 ≤ 3 by decide)
    _ ≤ 6 * (100 * A ^ 3 * 2 ^ (T.scheme.m + S.h) + 100 * L * 2 ^ T.scheme.m * w) := Nat.mul_le_mul_left 6 hv
    _ = _ := by ring

-- 读法：要证明的命题是 `Inside S L (initialTemplate S L.w M).sweep (initialBudget S M) S.U d 0`。
theorem first_inside (S : Setup F x y) (L : Limits) (M d : ℕ) (H : Enough S L) (hd : 3 ≤ d)
    (hp : L.start = initialBudget S M) (hm : L.m = max L.w (Nat.clog 2 (2 * M)))
    (hz : S.z ∣ S.U) (hlen : length F + 1 ≤ L.A) :
    Inside S L (initialTemplate S L.w M).sweep (initialBudget S M) S.U d 0 := by
  have hA : 4 ≤ L.A := by
    have := H.basic
    have := Nat.two_pow_pos L.r
    have := Nat.two_pow_pos S.discount
    omega
  have hw := Nat.pow_le_pow_right (by omega : 0 < L.A) H.positive
  -- 推导：记下中间结论 `ha`：`L.A ≤ L.A ^ L.K`。
  have ha : L.A ≤ L.A ^ L.K := by simpa using hw
  have hc : L.A ≤ L.code := calc
    _ ≤ 3 * L.A ^ L.K := by omega
    _ ≤ L.extra := by
      simpa only [pow_one, Limits.extra] using
        Nat.pow_le_pow_right (by omega : 0 < 3 * L.A ^ L.K) H.positive
    _ ≤ L.code := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, le_max_left _ _, ?_, hd, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change S.h + 0 * L.r = S.h
    omega
  · rw [hm, zero_mul, add_zero]
  · exact hA.trans ha
  · exact le_trans (by decide : 3 ≤ 4) (hA.trans ha)
  · exact (Nat.le_succ _).trans (hlen.trans hc)
  · simp [hp]
  · change S.U ≤ 6 * (S.U / S.z) * S.z
    rw [mul_assoc, Nat.div_mul_cancel hz]
    omega
  · simp [hp]
  · exact Nat.zero_lt_one
  · simp [hp]
  · exact mul_nonneg (by positivity) (by positivity)
  · exact le_rfl
  · simp [hp]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Stack
end
