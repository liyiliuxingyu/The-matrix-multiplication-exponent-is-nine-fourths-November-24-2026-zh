-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-!
# 传送分组后的记录表

选举只读取短计数器。再作一次交换，即可把每个宿主的所有块表作为一条记录一并传送。

**英文原文**

Transmitting the grouped sheets

The election reads short counters. One additional exchange carries
all block sheets as a single record per host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "q" => ((d + 1) * n)
local notation "Bin" => D.Binning a H T R θ

-- 读法：在后续公式中，`Elected` 是 `Format.vec (m + a) (Group.Labels n)` 的缩写。
abbrev Elected (_ : Bin) := Format.vec (m + a) (Group.Labels n)
-- 读法：在后续公式中，`stack` 是 `Format.vec a (D.Sheet n)` 的缩写。
abbrev stack (_ : Bin) := Format.vec a (D.Sheet n)
-- 读法：在后续公式中，`Bank` 是 `Fmt.bank m d b.stack` 的缩写。
abbrev Bank := Fmt.bank m d b.stack
-- 读法：在后续公式中，`Remote` 是 `Format.vec m (.vec d b.stack)` 的缩写。
abbrev Remote := Format.vec m (.vec d b.stack)
-- 读法：在后续公式中，`cutoff` 是 `(H : ℝ) * T / 2` 的缩写。
abbrev cutoff (_ : Bin) := (H : ℝ) * T / 2

-- 读法：`tagKeys` 的取值由 `Group.keys F q n D.count 5 5 (D.relative 1 b.cutoff)` 给出。
def tagKeys := Group.keys F q n D.count 5 5 (D.relative 1 b.cutoff)
-- 读法：在后续公式中，`tagArity` 是 `Group.arity q n D.count` 的缩写。
abbrev tagArity (_ : Bin) := Group.arity q n D.count
-- 读法：在后续公式中，`tagCap` 是 `(Group.Parcel d a n D.count).width` 的缩写。
abbrev tagCap (_ : Bin) := (Group.Parcel d a n D.count).width
-- 读法：在后续公式中，`tagDepth` 是 `m + q` 的缩写。
abbrev tagDepth (_ : Bin) := m + q
-- 读法：在后续公式中，`sheetDepth` 是 `m + d` 的缩写。
abbrev sheetDepth (_ : Bin) := m + d

-- 读法：`preBank` 的结果类型为 `b.Bank.obj`。
def preBank (s : (D.format.pair b.Elected).obj) : b.Bank.obj := fun i =>
  (D.nav s.1 i, fun l j =>
    let t := D.position a b.ha.le l j
    ((s.1.1 i).2 t, D.counter s.1 i t, s.2 ((Match.rowIndex m a).symm (i, l)) j))

-- 读法：在 `F` 上按格式 `(D.format.pair b.Elected)`、`b.Bank` 编码输入输出，映射 `b.preBank` 的电路规模至多为 `((D.format.pair b.Elected).width + 2 * b.Bank.width)`。这里调用 `Circuit.project`。
private theorem preBank_net :
    Circuit F (D.format.pair b.Elected) b.Bank b.preBank ((D.format.pair b.Elected).width + 2 * b.Bank.width) := by
  let f : b.Bank.pins → (D.format.pair b.Elected).pins
    | (i, .inl h) => .inl (.inl (i, .inl h))
    | (i, .inr (l, j, .inl h)) => .inl (.inl (i, .inr (D.position a b.ha.le l j, h)))
    | (i, .inr (l, j, .inr (.inl h))) => .inl (.inr (i, .inr (.inr (D.position a b.ha.le l j, h))))
    | (i, .inr (l, j, .inr (.inr h))) => .inr ((Match.rowIndex m a).symm (i, l), j, h)
  apply Circuit.project f
  rintro x ⟨i, h|⟨l, j, h|h|h⟩⟩ <;> rfl

-- 读法：输入 `i` 时返回 `(D.nav s i, D.sheet a b.ha 5 H T s i)`。
def bank (s : D.format.obj) : b.Bank.obj := fun i => (D.nav s i, D.sheet a b.ha 5 H T s i)
-- 读法：`banks` 的取值由 `(b.bank s, Fmt.gather b.stack (b.bank s))` 给出。
def banks (s : D.format.obj) : (b.Bank.pair b.Remote).obj := (b.bank s, Fmt.gather b.stack (b.bank s))

-- 读法：`bankCost` 的构造用到 `D.format.width`、`D.groupInput`、`b.Elected.width`。
def bankCost (p t : ℕ) :=
  100 * (D.format.width + (D.groupInput a).width + b.Elected.width + b.Bank.width) +
  Group.patchCost m d a n D.count b.tagCap p + Group.cost (m + a) q n D.count +
    gatherCost m d b.stack.width t

variable {u p t : ℕ} {L : Set (Table F)} {I : Type*}

-- 读法：要证明的命题是 `Computes F u L D.format (b.Bank.pair b.Remote) X (b.banks ∘ X) (fun _ => 1) (b.bankCost p t)`。
theorem banks_net (hu : 3 ≤ u) (hg : Access F u L b.tagDepth b.tagCap p)
    (hs : Access F u L b.sheetDepth b.stack.width t)
    (ha : b.tagArity ≤ u) (hk : (b.tagKeys : Set _) ⊆ L) (X : I → D.format.obj)
    (recip : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (X i).1) :
    Computes F u L D.format (b.Bank.pair b.Remote) X (b.banks ∘ X) (fun _ => 1) (b.bankCost p t) := by
  let Y := D.groups a b.ha.le ∘ X
  have prep := Computes.of_map (x := X) (y := Y) (Map.circuit (L := L) hu (D.groups_circuit a b.ha.le))
    (fun _ => rfl)
  have elect := prep.comp (Group.labels_net hu (Nat.sub_pos_of_lt b.ha) hg le_rfl Y recip ha hk)
  let Z := b.bank ∘ X
  -- 推导：记下中间结论 `keep`：`= Computes.of_map (x`。
  have keep := Computes.of_map (x := X) (y := X) (Map.circuit (L := L) hu (Circuit.id F D.format)) (fun _ => rfl)
  have get := (keep.pair hu elect).comp
    (Computes.of_map (y := Z) (Map.circuit hu b.preBank_net) (fun _ => rfl))
  have back := Computes.of_map (x := Z) (y := Z) (Map.circuit (L := L) hu (Circuit.id F b.Bank)) (fun _ => rfl)
  have all := get.comp (back.pair hu (gather_neighbors b.stack hu hs le_rfl Z recip))
  simp only [one_mul] at all
  refine all.mono ?_
  unfold bankCost
  rw [Format.width_pair D.format b.Elected]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# 为短查询准备公共导航数据

**英文原文**

Preparing common navigation data for short lookups
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "M" => D.childM a
local notation "e" => D.childD a 5
local notation "Bin" => D.Binning a H T R θ

-- 读法：在后续公式中，`Nav` 是 `Neighborhood.Rows M e` 的缩写。
abbrev Nav (_ : Bin) := Neighborhood.Rows M e
-- 读法：在后续公式中，`Prior` 是 `Neighborhood.Rows m (d + 1)` 的缩写。
abbrev Prior (_ : Bin) := Neighborhood.Rows m (d + 1)
-- 读法：在后续公式中，`Mask` 是 `Neighborhood.Mask m ((d + 1) + (n + 1)) e` 的缩写。
abbrev Mask (_ : Bin) := Neighborhood.Mask m ((d + 1) + (n + 1)) e

-- 读法：输入 `v j` 时返回 `let q := (Pattern.tag d).symm j if q.1 then v else D.nav s v q.2`。
def prior (s : D.format.obj) : b.Prior.obj := fun v j =>
  let q := (Pattern.tag d).symm j
  if q.1 then v else D.nav s v q.2

omit [Field F] in
-- 读法：`b.prior s v (Pattern.tag d (true, 0))` 等于 `v`。
theorem prior_self (s : D.format.obj) (v : B m) : b.prior s v (Pattern.tag d (true, 0)) = v := by
  simp [prior]

omit [Field F] in
-- 读法：`b.prior s v (Pattern.tag d (false, j))` 等于 `D.nav s v j`。
theorem prior_peer (s : D.format.obj) (v : B m) (j : B d) :
    b.prior s v (Pattern.tag d (false, j)) = D.nav s v j := by simp [prior]

-- 读法：`mask` 的取值由 `Child.mask (b.prior s) (D.binNav a b.ha 5 s)` 给出。
def mask (s : D.format.obj) : b.Mask.obj := Child.mask (b.prior s) (D.binNav a b.ha 5 s)
-- 读法：`links` 的取值由 `(D.binNav a b.ha 5 s, b.mask s)` 给出。
def links (s : D.format.obj) : (b.Nav.pair b.Mask).obj := (D.binNav a b.ha 5 s, b.mask s)

-- 读法：在 `F` 上按格式 `D.format`、`b.Prior` 编码输入输出，映射 `b.prior` 的电路规模至多为 `(D.format.width + 34 * b.Prior.width)`。对 `f` 分类讨论。
private theorem prior_net : Circuit F D.format b.Prior b.prior (D.format.width + 34 * b.Prior.width) := by
  have hd : Install.Depends (b.Prior.code ∘ b.prior ∘ D.format.code.symm) 1 := by
    rintro ⟨v, j, i⟩
    obtain ⟨⟨f, k⟩, rfl⟩ := (Pattern.tag d).surjective j
    cases f
    · let t : D.format.pins := .inl (v, .inl (k, i))
      refine ⟨{t}, by simp, fun x y he => ?_⟩
      change (Format.addr m).code (b.prior (D.format.code.symm x) v (Pattern.tag d (false, k))) i =
        (Format.addr m).code (b.prior (D.format.code.symm y) v (Pattern.tag d (false, k))) i
      rw [prior_peer, prior_peer]
      exact (congrFun (D.format.code.apply_symm_apply x) t).trans
        ((he t (by simp)).trans (congrFun (D.format.code.apply_symm_apply y) t).symm)
    · refine ⟨∅, by simp, fun x y _ => ?_⟩
      change (Format.addr m).code (b.prior (D.format.code.symm x) v (Pattern.tag d (true, k))) i =
        (Format.addr m).code (b.prior (D.format.code.symm y) v (Pattern.tag d (true, k))) i
      simp only [prior, Equiv.symm_apply_apply, ite_true]
  exact hd.bnet F

-- 读法：在后续公式中，`precision` 是 `M + 2 ^ ((d + 1) + (n + 1)) + 2 ^ e` 的缩写。
abbrev precision (_ : Bin) := M + 2 ^ ((d + 1) + (n + 1)) + 2 ^ e
-- 读法：`linkCost` 的取值由 `12 * D.format.width + 34 * b.Prior.width + 2 * (D.navCost a e) + 2 ^ M * (100 + b.precision) ^ 40` 给出。
def linkCost := 12 * D.format.width + 34 * b.Prior.width + 2 * (D.navCost a e) + 2 ^ M * (100 + b.precision) ^ 40

-- 读法：在 `F` 上按格式 `D.format`、`(b.Nav.pair b.Mask)` 编码输入输出，映射 `b.links` 的电路规模至多为 `b.linkCost`。
theorem links_net : Circuit F D.format (b.Nav.pair b.Mask) b.links b.linkCost := by
  have nav : Circuit F D.format b.Nav (D.binNav a b.ha 5) (D.navCost a e) := D.nav_net a b.ha.le false 5
  have hm : M ≤ b.precision := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hp : 2 ^ ((d + 1) + (n + 1)) ≤ b.precision := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hq : 2 ^ e ≤ b.precision := Nat.le_add_left _ _
  obtain ⟨k, hk, hc⟩ := Child.cheap_mask F («m» := m) («e» := n + 1) hm hp hq
  have h : k ≤ 2 ^ M * (100 + b.precision) ^ 40 := (Nat.le_add_left _ _).trans hc
  refine (nav.pair ((b.prior_net.pair nav).comp hk)).mono ?_
  unfold linkCost
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# 写入宿主状态与直接邻接标志的成本

**英文原文**

Cost of writing host status and direct adjacency flags
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => b.target.m
local notation "d" => b.target.d
local notation "N" => D.scheme.d + Child.width n 5
local notation "t" => (m + 2 ^ d)
local notation "cost" => D.navCost a d

-- 读法：`2 ^ N` 不超过 `2 ^ d`。使用 `Nat.pow_le_pow_right` 给出的结论。
private theorem small : 2 ^ N ≤ 2 ^ d :=
  Nat.pow_le_pow_right (by decide) (by change N ≤ (N + 1) * 3; omega)

-- 读法：`2 ^ m * x` 不超过 `cost`。通过传递性衔接 `Nat.mul_le_mul_left` 与 `Nat.le_add_left`。
private theorem charge (x : ℕ) (hx : x ≤ (100 + t) ^ 201) : 2 ^ m * x ≤ cost :=
  (Nat.mul_le_mul_left _ hx).trans (Nat.le_add_left _ _)

-- 读法：`b.Flags.width` 不超过 `cost`。这里调用 `Nat.le_self_pow`。
theorem flags_bound : b.Flags.width ≤ cost := by
  rw [Flags, Format.width_vec, Format.width_pair, Format.width_vec, Format.width_bit, mul_one]
  refine b.charge _ ((show 1 + 2 ^ d ≤ 100 + t by omega).trans ?_)
  exact Nat.le_self_pow (by decide) _

-- 读法：`(Neighborhood.Rows m N).width` 不超过 `cost`。这里调用 `Nat.mul_le_mul`。
private theorem step_bound : (Neighborhood.Rows m N).width ≤ cost := by
  rw [Neighborhood.Rows, Format.width_vec, Format.width_vec, Format.width_addr]
  have hp := Nat.zero_le (2 ^ d)
  refine b.charge _ (le_trans ?_ (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 201)))
  rw [pow_two]
  exact Nat.mul_le_mul (b.small.trans (by omega)) (by omega)

-- 读法：在 `F` 上按格式 `D.format`、`(Neighborhood.Rows m N)` 编码输入输出，映射 `b.step` 的电路规模至多为 `(100 * cost)`。
private theorem step_net : Circuit F D.format (Neighborhood.Rows m N) b.step (100 * cost) := by
  have start := (D.groups_circuit a b.ha.le).comp (Child.fromGroup_circuit F false)
  have walk : Circuit F (Child.Input D.scheme.m D.scheme.d) (Neighborhood.Rows m N) (Child.step n 5)
      ((Child.Input D.scheme.m D.scheme.d).width + 68 * (Neighborhood.Rows m N).width) :=
    Child.step_depends.bnet F
  refine (start.comp walk).mono ?_
  have h := b.step_bound
  unfold Template.navCost Template.groupInput at h ⊢
  omega

-- 读法：在后续公式中，`Adj` 是 `Format.vec m (.vec d .bit)` 的缩写。
private abbrev Adj := Format.vec m (.vec d .bit)
-- 读法：在后续公式中，`Raw` 是 `(D.Status a).pair b.Adj` 的缩写。
private abbrev Raw := (D.Status a).pair b.Adj
-- 读法：输入 `v` 时返回 `(x.1 v, x.2 v)`。
private def pair (x : b.Raw.obj) : b.Flags.obj := fun v => (x.1 v, x.2 v)

-- 读法：在 `F` 上按格式 `b.Raw`、`b.Flags` 编码输入输出，映射 `b.pair` 的电路规模至多为 `(3 * b.Flags.width)`。这里调用 `Circuit.project`。
private theorem pair_net : Circuit F b.Raw b.Flags b.pair (3 * b.Flags.width) := by
  have h : Circuit F b.Raw b.Flags b.pair (b.Raw.width + 2 * b.Flags.width) := by
    apply Circuit.project (fun (j : b.Flags.pins) => Sum.map (fun i => (j.1, i)) (fun i => (j.1, i)) j.2)
    rintro x ⟨i, j|j⟩ <;> rfl
  have he : b.Raw.width = b.Flags.width := by
    change (Format.pair (.vec m .bit) (.vec m (.vec d .bit))).width = _
    simp only [Flags, Format.width_pair, Format.width_vec, mul_add]
  exact h.mono (by omega)

-- 读法：在 `F` 上按格式 `D.format`、`b.Flags` 编码输入输出，映射 `b.status` 的电路规模至多为 `(200 * cost)`。
theorem status_net : Circuit F D.format b.Flags b.status (200 * cost) := by
  have hnav : Circuit F D.format (Neighborhood.Rows m d) (D.binNav a b.ha 5) cost :=
    D.nav_net a b.ha.le false 5
  obtain ⟨s, g, hg⟩ := Child.cheap_coreFlags F (Nat.le_add_right m (2 ^ d)) (Nat.le_add_left (2 ^ d) m)
    (b.small.trans (Nat.le_add_left _ _))
  have hb : s ≤ cost := (le_trans (Nat.le_add_left _ _) hg).trans
    (b.charge _ (Nat.pow_le_pow_right (by positivity) (by decide)))
  have ha := (hnav.pair b.step_net).comp (g.mono hb)
  have hh := ((D.status_net a).pair ha).comp b.pair_net
  have h₁ : (D.Status a).width ≤ b.Flags.width := by
    change (Format.vec m .bit).width ≤ _
    simp only [Flags, Format.width_pair, Format.width_vec]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  have h₂ := b.flags_bound
  -- 推导：记下中间结论 `h₃`：`D.format.width ≤ cost`。
  have h₃ : D.format.width ≤ cost := by unfold navCost; omega
  have eq : b.pair ∘ (fun i => (D.childLive a i,
      Child.coreFlags (D.binNav a b.ha 5 i) (b.step i))) = b.status := by
    funext i v; simp only [Function.comp_apply, pair, status]
  rw [← eq]
  simp only [Function.comp_def] at hh ⊢
  refine hh.mono ?_
  unfold Template.statusCost
  have same : cost = D.navCost a (D.childD a 5) := rfl
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# 在每个子宿主出现位置执行一次标准化局部查找

**英文原文**

One standardized local lookup per child occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "M" => D.childM a
local notation "e" => D.childD a 5
local notation "Bin" => D.Binning a H T R θ
local notation "orig" => Match.rowIndex m (n + 1)
local notation "pre" => Equiv.symm (Match.rowIndex (d + 1) (n + 1))

-- 读法：在后续公式中，`View` 是 `(b.Bank.pair b.Remote).pair (b.Nav.pair b.Mask)` 的缩写。
abbrev View := (b.Bank.pair b.Remote).pair (b.Nav.pair b.Mask)
-- 读法：`Tile` 的构造用到 `Format.pair`、`D.Sheet`。
abbrev Tile (_ : Bin) :=
  Format.pair (.addr (n + 1)) (.pair (.addr a) (.pair (D.Sheet n)
    (.pair (.vec d (D.Sheet n)) (.vec d (.vec (n + 1) (.vec e .bit))))))
-- 读法：在后续公式中，`Fields` 是 `Format.pair (.addr b.target.ℓ) (.vec b.target.k (.vec b.target.e (Trail.pointer D.scheme 0)))` 的缩写。
abbrev Fields := Format.pair (.addr b.target.ℓ) (.vec b.target.k (.vec b.target.e (Trail.pointer D.scheme 0)))
-- 读法：在后续公式中，`Rows` 是 `Fmt.rows M e a` 的缩写。
abbrev Rows (_ : Bin) := Fmt.rows M e a
-- 读法：在后续公式中，`Output` 是 `b.target.format.pair (Trail.controls D.scheme b.target 0)` 的缩写。
abbrev Output := b.target.format.pair (Trail.controls D.scheme b.target 0)

-- 读法：`view` 的取值由 `(b.banks r, b.links r)` 给出。
def view (r : D.format.obj) : b.View.obj := (b.banks r, b.links r)

-- 读法：`tiles` 的结果类型为 `(b.Rows b.Tile).obj`。
def tiles (v : b.View.obj) : (b.Rows b.Tile).obj := fun i =>
  (v.2.1 i, fun l =>
    let j := (orig i).1
    let z := (orig i).2
    (z, l, (v.1.1 j).2 l, fun s => v.1.2 j s l,
      fun s t k => v.2.2 j (pre (Pattern.tag d (true, 0), z)) k (pre (Pattern.tag d (false, s), t))))

-- 读法：`label` 的结果类型为 `B b.target.ℓ`。
def label (v : b.Tile.obj) : B b.target.ℓ :=
  (Parcel.record D.scheme e (Sheet.slots H) b.depth).serial
    (Sheet.record D v.2.2.1 H T b.pos b.depth e v.2.2.2.1
      (fun _ s t => Child.select (v.2.2.2.2 s t)) v.1)

-- 读法：`issue` 的取值由 `(b.label v, fun i j => Trail.point D.scheme (b.marked v.2.2.1 v.1 v.2.1 (b.label v) i j))` 给出。
def issue (v : b.Tile.obj) : b.Fields.obj :=
  (b.label v, fun i j => Trail.point D.scheme (b.marked v.2.2.1 v.1 v.2.1 (b.label v) i j))

-- 读法：`deliver` 的取值由 `(fun i => ((s i).1, fun l => ((s i).2 l).1), fun i l => ((s i).2 l).2)` 给出。
def deliver (s : (b.Rows b.Fields).obj) : b.Output.obj :=
  (fun i => ((s i).1, fun l => ((s i).2 l).1), fun i l => ((s i).2 l).2)

-- 读法：`result` 的取值由 `(b.data s, (b.move s).commands)` 给出。
def result (s : D.format.obj) : b.Output.obj := (b.data s, (b.move s).commands)

omit [Field F] in
-- 读法：`Sheet.record D sheet H T hH u k near x z` 等于 `Sheet.record D sheet H T hH u k near y z`。用函数外延性比较等号两侧在 `i` 处的取值。
private theorem record_congr {v k : ℕ} (sheet : (D.Sheet v).obj) (u : ℕ) (hH : 0 < H)
    (near : B D.scheme.d → (D.Sheet v).obj) (x y : B (v + 1) → B D.scheme.d → B (v + 1) → B k)
    (z : B (v + 1)) (he : ∀ s t, x z s t = y z s t) :
    Sheet.record D sheet H T hH u k near x z = Sheet.record D sheet H T hH u k near y z := by
  funext i
  unfold Sheet.record
  cases h : Sheet.find D sheet u z i with
  | none => rfl
  | some j =>
    have ht := (Sheet.find_spec _ _ _ _ _ _ h).2.1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change Sheet.target D sheet H T hH u k near x j = Sheet.target D sheet H T hH u k near y j
    funext s
    unfold Sheet.target
    cases (D.scheme.decode (sheet j).1).peer 0 s with
    | none => rfl
    | some t => simp only [ht, he]

-- 读法：`b.label ((b.tiles (b.view r) i).2 l)` 等于 `(b.data r i).2 l`。
private theorem label_eq (r : D.format.obj) (i : B M) (l : B a) :
    b.label ((b.tiles (b.view r) i).2 l) = (b.data r i).2 l := by
  let y := orig i
  let page := D.sheet a b.ha 5 H T r
  let near := fun s => page (D.nav r y.1 s) l
  let nav := D.binNav a b.ha 5 r
  let raw := fun z s t => Child.index nav ((orig).symm (y.1, z)) ((orig).symm (D.nav r y.1 s, t))
  let short := fun (_ : B (n + 1)) s t => Child.select
    (fun k => b.mask r y.1 (pre (Pattern.tag d (true, 0), y.2)) k (pre (Pattern.tag d (false, s), t)))
  have he (s : B d) (t : B (n + 1)) : short y.2 s t = raw y.2 s t := by
    have h := Child.index_eq (b.prior r) nav y.1 (Pattern.tag d (true, 0)) (Pattern.tag d (false, s)) y.2 t
    rw [b.prior_self, b.prior_peer] at h
    exact h.symm
  let code := (Parcel.record D.scheme e (Sheet.slots H) b.depth).serial
  simp only [label, tiles, view, banks, links, bank, Fmt.gather, data, frame, Parcel.encode, childFrame]
  change code (Sheet.record D (page y.1 l) H T b.pos b.depth e near short y.2) =
    code (Sheet.record D (page y.1 l) H T b.pos b.depth e near raw y.2)
  exact congrArg code (record_congr _ _ b.pos _ _ _ _ he)

-- 读法：`b.deliver (Fmt.update b.issue (b.tiles (b.view r)))` 等于 `b.result r`。按 `Prod.ext` 的外延性准则比较各分量。
theorem issued (r : D.format.obj) :
    b.deliver (Fmt.update b.issue (b.tiles (b.view r))) = b.result r := by
  simp only [deliver, Fmt.update, issue, result]
  apply Prod.ext
  · funext i
    exact Prod.ext rfl (funext fun j => b.label_eq r i j)
  · funext i l j s
    let t := (b.tiles (b.view r) i).2 l
    change Trail.point _ (b.marked t.2.2.1 t.1 t.2.1 (b.label t) j s) = _
    rw [show b.label t = _ from b.label_eq r i l]
    simp only [move, Trail.Move.commands, t, tiles, view, banks, bank]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# 计算分组标签与外部前驱的网络

**英文原文**

The network computing grouped labels and exterior predecessors
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "M" => D.childM a
local notation "e" => D.childD a 5
local notation "Bin" => D.Binning a H T R θ
local notation "orig" => Match.rowIndex m (n + 1)
local notation "pre" => Equiv.symm (Match.rowIndex (d + 1) (n + 1))

-- 读法：在 `F` 上按格式 `b.View`、`(b.Rows b.Tile)` 编码输入输出，映射 `b.tiles` 的电路规模至多为 `(b.View.width + 34 * (b.Rows b.Tile).width)`。
private theorem tiles_net :
    Circuit F b.View (b.Rows b.Tile) b.tiles (b.View.width + 34 * (b.Rows b.Tile).width) := by
  let X := b.View
  let Y := b.Rows b.Tile
  have h : Install.Depends (Y.code ∘ b.tiles ∘ X.code.symm) 1 := by
    have pin (i : Y.pins) (j : X.pins) (he : ∀ t, Y.code (b.tiles t) i = X.code t j) :
        ∃ s : Finset X.pins, s.card ≤ 1 ∧ ∀ x y, (∀ l ∈ s, x l = y l) →
          (Y.code ∘ b.tiles ∘ X.code.symm) x i = (Y.code ∘ b.tiles ∘ X.code.symm) y i := by
      refine ⟨{j}, by simp, fun x y h => ?_⟩
      simp only [Function.comp_apply, he, Equiv.apply_symm_apply]
      exact h j (by simp)
    rintro ⟨v, h|⟨l, i|j|k|⟨s, t⟩|⟨s, r, k, t⟩⟩⟩
    · exact pin _ (.inr (.inl (v, h))) fun _ => rfl
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
    · exact pin _ (.inl (.inl ((orig v).1, .inr (l, k)))) fun _ => rfl
    · exact pin _ (.inl (.inr ((orig v).1, s, l, t))) fun _ => rfl
    · exact pin _ (.inr (.inr ((orig v).1, pre (Pattern.tag d (true, 0), (orig v).2),
        k, pre (Pattern.tag d (false, s), r), t))) fun _ => rfl
  exact h.bnet F

-- 读法：在 `F` 上按格式 `(b.Rows b.Fields)`、`b.Output` 编码输入输出，映射 `b.deliver` 的电路规模至多为 `((b.Rows b.Fields).width + 2 * b.Output.width)`。这里调用 `Circuit.project`。
private theorem deliver_net : Circuit F (b.Rows b.Fields) b.Output b.deliver
    ((b.Rows b.Fields).width + 2 * b.Output.width) := by
  let f : b.Output.pins → (b.Rows b.Fields).pins
    | .inl (v, .inl i) => (v, .inl i)
    | .inl (v, .inr (l, j)) => (v, .inr (l, .inl j))
    | .inr (v, l, j) => (v, .inr (l, .inr j))
  apply Circuit.project f
  rintro x (⟨_, _|_⟩|_) <;> rfl

-- 读法：`gate` 的取值由 `weightTable b.issue (fun _ => 1)` 给出。
def gate : Table F := weightTable b.issue (fun _ => 1)
-- 读法：`keys` 的取值由 `insert b.gate b.tagKeys` 给出。
def keys := insert b.gate b.tagKeys
-- 读法：`arity` 的取值由 `b.tagArity + b.Tile.width + b.Fields.width` 给出。
def arity := b.tagArity + b.Tile.width + b.Fields.width

-- 读法：`b.keys.card` 不超过 `3`。通过传递性衔接 `Finset.card_insert_le` 与 `Nat.succ_le_succ`。
theorem card_keys : b.keys.card ≤ 3 :=
  (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Group.card_keys F))

-- 读法：`cost` 的构造用到 `D.format.width`、`b.bankCost`、`b.linkCost`。
def cost (p t : ℕ) :=
  20 * D.format.width + b.bankCost p t + 4 * b.linkCost + 4 * (b.View.width + 34 * (b.Rows b.Tile).width)
    + updateCost M e a b.Tile b.Fields + 4 * ((b.Rows b.Fields).width + 2 * b.Output.width)

variable {u p t : ℕ} {L : Set (Table F)} {I : Type*}

-- 读法：要证明的命题是 `Computes F u L D.format b.Output X (b.result ∘ X) (fun _ => 1) (b.cost p t)`。
theorem computes (hu : 3 ≤ u) (hg : Access F u L b.tagDepth b.tagCap p)
    (hs : Access F u L b.sheetDepth b.stack.width t)
    (ha : b.arity ≤ u) (hk : (b.keys : Set _) ⊆ L) (X : I → D.format.obj)
    (recip : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (X i).1) :
    Computes F u L D.format b.Output X (b.result ∘ X) (fun _ => 1) (b.cost p t) := by
  unfold arity at ha
  have hb := b.banks_net hu hg hs (by omega) (fun _ h => hk (Finset.mem_insert_of_mem h)) X recip
  have ht := Computes.of_map (L := L) (x := X) (y := b.links ∘ X) (Map.circuit hu b.links_net) (fun _ => rfl)
  let Y := b.tiles ∘ b.view ∘ X
  have hi := (hb.pair hu ht).comp
    (Computes.of_map (y := Y) (Map.circuit hu b.tiles_net) (fun _ => rfl))
  have update := computes_update b.issue (fun _ => (1 : F)) hu (by omega)
    (hk (Finset.mem_insert_self _ _)) Y
  -- 推导：记下中间结论 `h`：`= (hi.comp update).comp (Computes.of_map (y`。
  have h := (hi.comp update).comp (Computes.of_map (y := b.result ∘ X) (Map.circuit hu b.deliver_net)
    (fun i => b.issued (X i)))
  simp only [Fmt.weight, Function.comp_apply, Finset.prod_const_one, one_mul] at h
  refine h.mono ?_
  unfold cost
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# 收缩准备工作的统一上界

索引包含系数域。在每个单元中重复计入的开销只用短参数作为底数；长参数还包括宿主地址及路由价格所要求计费的最小有效载荷。

**英文原文**

Uniform bounds for preparing a contraction

The index includes the coefficient field. Charges repeated in each
cell only use the short base. Host addresses and the minimum payload
charged by a routing price are included in the long base.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open BatchDescent.Phase

-- 读法：结构的字段包括 `F`、`D`、`a`、`H`、`T`。
structure Case where
  F : Type
  [field : Field F]
  D : Template F
  a : ℕ
  H : ℕ
  T : ℕ
  R : ℕ
  θ : ℝ
  b : D.Binning a H T R θ
  p : Rounds.Contraction.Prices F
  t : ℕ
  hd : D.scheme.d ≤ 4
  hk : D.scheme.k = 0

attribute [instance] Case.field

namespace Case
variable (i : Case)
-- 读法：在后续公式中，`m` 是 `i.D.scheme.m` 的缩写。
abbrev m := i.D.scheme.m
-- 读法：在后续公式中，`h` 是 `i.D.scheme.h` 的缩写。
abbrev h := i.D.scheme.h
-- 读法：在后续公式中，`n` 是 `i.h - i.a` 的缩写。
abbrev n := i.h - i.a
-- 读法：在后续公式中，`d` 是 `i.D.scheme.d` 的缩写。
abbrev d := i.D.scheme.d
-- 读法：在后续公式中，`q` 是 `(i.d + 1) * i.n` 的缩写。
abbrev q := (i.d + 1) * i.n
-- 读法：在后续公式中，`short` 是 `1000000 + i.H + 2 ^ i.b.depth + i.D.scheme.ℓ + i.D.count + 2 ^ i.D.scheme.e + i.h + 2 ^ i.n + i.p.W + i.t` 的缩写。
abbrev short := 1000000 + i.H + 2 ^ i.b.depth + i.D.scheme.ℓ + i.D.count +
  2 ^ i.D.scheme.e + i.h + 2 ^ i.n + i.p.W + i.t
-- 读法：在后续公式中，`long` 是 `i.short + i.m + i.p.w + i.p.w ^ i.p.power` 的缩写。
abbrev long := i.short + i.m + i.p.w + i.p.w ^ i.p.power

-- 读法：结论为 `2 ≤ i.short ∧ i.H ≤ i.short ∧ 2 ^ i.b.depth ≤ i.short ∧ i.D.scheme.ℓ ≤ i.short ∧ i.D.count ≤ i.short ∧ 2 ^ i.D.scheme.e ≤ i.short ∧ i.h ≤ i.short ∧ 2 ^ i.n ≤ i.short ∧ i.p.W ≤ i.short ∧ i.t ≤ i.short`。
theorem parts : 2 ≤ i.short ∧ i.H ≤ i.short ∧ 2 ^ i.b.depth ≤ i.short ∧
    i.D.scheme.ℓ ≤ i.short ∧ i.D.count ≤ i.short ∧ 2 ^ i.D.scheme.e ≤ i.short ∧
    i.h ≤ i.short ∧ 2 ^ i.n ≤ i.short ∧ i.p.W ≤ i.short ∧ i.t ≤ i.short := by
  unfold short
  generalize 2 ^ i.b.depth = x, 2 ^ i.D.scheme.e = y, 2 ^ i.n = z
  omega

-- 读法：`2` 不超过 `i.short`。使用 `i.parts.1` 给出的结论。
theorem short_two : 2 ≤ i.short := i.parts.1
-- 读法：`i.short` 不超过 `i.long`。
theorem short_long : i.short ≤ i.long := by unfold long; omega
-- 读法：`2` 不超过 `i.long`。使用 `i.short_two.trans` 给出的结论。
theorem long_two : 2 ≤ i.long := i.short_two.trans i.short_long
end Case

-- 读法：在后续公式中，`Short` 是 `Poly Case.short` 的缩写。
abbrev Short := Poly Case.short
-- 读法：在后续公式中，`Long` 是 `Poly Case.long` 的缩写。
abbrev Long := Poly Case.long

-- 读法：`Mixed` 表示以下条件：存在 `k : ℕ`，对每个 `i`，`f i` 不超过 `2 ^ (j i) * i.long ^ k + 2 ^ (j i + i.h) * i.short ^ k`。
def Mixed (j f : Case → ℕ) : Prop :=
  ∃ k : ℕ, ∀ i, f i ≤ 2 ^ (j i) * i.long ^ k + 2 ^ (j i + i.h) * i.short ^ k

-- 读法：在后续公式中，`Cost` 是 `Mixed Case.m` 的缩写。
abbrev Cost := Mixed Case.m
-- 读法：在后续公式中，`Row` 是 `Mixed (fun _ => 0)` 的缩写。
abbrev Row := Mixed (fun _ => 0)

variable {j f g n : Case → ℕ}

-- 读法：要证明的命题是 `Long f`。使用 `h.grow` 给出的结论。
theorem Short.long (h : Short f) : Long f := h.grow Case.short_long
-- 读法：要证明的命题是 `Short (fun _ => k)`。使用 `Poly.const` 给出的结论。
theorem short_const (k : ℕ) : Short (fun _ => k) := Poly.const Case.short_two k
-- 读法：要证明的命题是 `Long (fun _ => k)`。使用 `Poly.const` 给出的结论。
theorem long_const (k : ℕ) : Long (fun _ => k) := Poly.const Case.long_two k

namespace Mixed
-- 读法：要证明的命题是 `Mixed j g`。
theorem mono (h : Mixed j f) (hg : ∀ i, g i ≤ f i) : Mixed j g :=
  let ⟨k, hk⟩ := h
  ⟨k, fun i => (hg i).trans (hk i)⟩

-- 读法：要证明的命题是 `Mixed j (fun i => f i + g i)`。这里调用 `Nat.add_le_add`。
theorem add (h : Mixed j f) (h' : Mixed j g) : Mixed j (fun i => f i + g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'
  refine ⟨max l k + 1, fun i => (Nat.add_le_add (hl i) (hk i)).trans ?_⟩
  rw [add_add_add_comm, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.long_two ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.short_two ..))

-- 读法：要证明的命题是 `Mixed j (fun i => f i * g i)`。这里调用 `i.short_long`。
theorem mul (h : Mixed j f) (h' : Short g) : Mixed j (fun i => f i * g i) := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨k, hk⟩ := h'.bound
  refine ⟨l + k, fun i => (Nat.mul_le_mul (hl i) (hk i)).trans ?_⟩
  simp only [add_mul, mul_assoc, pow_add]
  gcongr
  exact i.short_long

-- 读法：要证明的命题是 `Mixed j (fun i => g i * f i)`。使用 `h.mul` 给出的结论。
theorem left (h : Mixed j f) (h' : Short g) : Mixed j (fun i => g i * f i) :=
  (h.mul h').mono fun _ => le_of_eq (mul_comm ..)

-- 读法：要证明的命题是 `Mixed j (fun i => k * f i)`。使用 `h.left` 给出的结论。
theorem scale (h : Mixed j f) (k : ℕ) : Mixed j (fun i => k * f i) := h.left (short_const k)

-- 读法：要证明的命题是 `Mixed j (fun i => 2 ^ (j i) * f i)`。
theorem long (j : Case → ℕ) (h : Long f) : Mixed j (fun i => 2 ^ (j i) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_right ..)⟩

-- 读法：要证明的命题是 `Mixed j (fun i => 2 ^ (j i + i.h) * f i)`。
theorem short (j : Case → ℕ) (h : Short f) : Mixed j (fun i => 2 ^ (j i + i.h) * f i) :=
  let ⟨k, hk⟩ := h.bound
  ⟨k, fun i => (Nat.mul_le_mul_left _ (hk i)).trans (Nat.le_add_left ..)⟩
end Mixed

-- 读法：要证明的命题是 `Row f`。这里调用 `Mixed.long`。
theorem Long.row (h : Long f) : Row f := by
  simpa only [pow_zero, one_mul] using Mixed.long (fun _ => 0) h

-- 读法：要证明的命题是 `Row (fun i => 2 ^ i.h * f i)`。这里调用 `Mixed.short`。
theorem Short.blocks (h : Short f) : Row (fun i => 2 ^ i.h * f i) := by
  simpa only [zero_add] using Mixed.short (fun _ => 0) h

-- 读法：要证明的命题是 `Row (fun i => 2 ^ i.a * f i)`。使用 `h.blocks.mono` 给出的结论。
theorem Short.groups (h : Short f) : Row (fun i => 2 ^ i.a * f i) :=
  h.blocks.mono (fun i => Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) i.b.ha.le))

-- 读法：要证明的命题是 `Cost (fun i => 2 ^ i.m * f i)`。这里调用 `Nat.mul_le_mul_left`。
theorem Row.hosts (h : Row f) : Cost (fun i => 2 ^ i.m * f i) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun i => ?_⟩
  simpa only [pow_zero, one_mul, zero_add, mul_add, ← mul_assoc, ← pow_add] using Nat.mul_le_mul_left (2 ^ i.m) (hk i)

-- 读法：要证明的命题是 `Cost (fun i => 2 ^ (i.m + n i) * f i)`。这里调用 `Row.hosts`。
theorem Row.expand (h : Row f) (h' : Short (fun i => 2 ^ n i)) :
    Cost (fun i => 2 ^ (i.m + n i) * f i) := by
  simpa only [pow_add, mul_assoc] using Row.hosts (h.left h')

-- 读法：要证明的命题是 `Cost f`。使用 `h.hosts.mono` 给出的结论。
theorem Row.cost (h : Row f) : Cost f :=
  h.hosts.mono fun _ => Nat.le_mul_of_pos_left _ (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-!
# 分组步骤中位数较少的数值参数

**英文原文**

The short numerical parameters of a grouped step
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open BatchDescent.Phase

-- 读法：要证明的命题是 `Short (fun i => i.H)`。使用 `Poly.of_le` 给出的结论。
theorem bins : Short (fun i => i.H) :=
  Poly.of_le Case.short_two fun i => i.parts.2.1

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.b.depth)`。使用 `Poly.of_le` 给出的结论。
theorem depths : Short (fun i => 2 ^ i.b.depth) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.1

-- 读法：要证明的命题是 `Short (fun i => i.D.scheme.ℓ)`。使用 `Poly.of_le` 给出的结论。
theorem labels : Short (fun i => i.D.scheme.ℓ) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => i.D.count)`。使用 `Poly.of_le` 给出的结论。
theorem counters : Short (fun i => i.D.count) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.D.scheme.e)`。使用 `Poly.of_le` 给出的结论。
theorem spans : Short (fun i => 2 ^ i.D.scheme.e) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => i.h)`。使用 `Poly.of_le` 给出的结论。
theorem height : Short (fun i => i.h) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.n)`。使用 `Poly.of_le` 给出的结论。
theorem tiles : Short (fun i => 2 ^ i.n) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => i.p.W)`。使用 `Poly.of_le` 给出的结论。
theorem weights : Short (fun i => i.p.W) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.2.2.2.2.1

-- 读法：要证明的命题是 `Short (fun i => i.t)`。使用 `Poly.of_le` 给出的结论。
theorem payload : Short (fun i => i.t) :=
  Poly.of_le Case.short_two fun i => i.parts.2.2.2.2.2.2.2.2.2

-- 读法：要证明的命题是 `Long Case.m`。使用 `Poly.of_le` 给出的结论。
theorem hosts : Long Case.m := Poly.of_le Case.long_two fun i => by unfold Case.long; omega

-- 读法：要证明的命题是 `Long (fun i => i.p.w ^ i.p.power)`。使用 `Poly.of_le` 给出的结论。
theorem threshold : Long (fun i => i.p.w ^ i.p.power) :=
  Poly.of_le Case.long_two fun _ => Nat.le_add_left ..

-- 读法：要证明的命题是 `Short Case.a`。使用 `height.mono` 给出的结论。
theorem groupHeight : Short Case.a := height.mono fun i => i.b.ha.le

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.d)`。使用 `short_const` 给出的结论。
theorem slots : Short (fun i => 2 ^ i.d) :=
  (short_const (2 ^ 4)).mono fun i => Nat.pow_le_pow_right (by decide) i.hd

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.D.scheme.k)`。
theorem stations : Short (fun i => 2 ^ i.D.scheme.k) := by
  refine (short_const 1).mono fun i => ?_
  simp only [i.hk, pow_zero, le_refl]

-- 读法：要证明的命题是 `Short (fun i => 2 ^ (i.n + 1))`。使用 `Poly.exp_add` 给出的结论。
theorem suffix : Short (fun i => 2 ^ (i.n + 1)) :=
  Poly.exp_add tiles (short_const 2)

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.q)`。这里调用 `Nat.pow_le_pow_right`。
theorem path : Short (fun i => 2 ^ i.q) := by
  refine (tiles.pow 5).mono fun i => ?_
  rw [← pow_mul, mul_comm i.n]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.succ_le_succ i.hd))

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.b.target.d)`。
theorem childSlots : Short (fun i => 2 ^ i.b.target.d) := by
  have hw : Short (fun i => 2 ^ Child.width i.n 5) :=
    suffix.mono (fun i => Nat.pow_le_pow_right (by decide) (min_le_left ..))
  refine (((slots.exp_add hw).exp_add (g := fun _ => 1) (short_const 2)).pow 3).mono fun i => ?_
  rw [← pow_mul]

-- 读法：要证明的命题是 `Long (fun i => i.b.target.m)`。使用 `hosts.add` 给出的结论。
theorem childHosts : Long (fun i => i.b.target.m) := hosts.add (Short.long suffix.of_exp)

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.b.target.k)`。使用 `bins.add` 给出的结论。
theorem childStations : Short (fun i => 2 ^ i.b.target.k) :=
  (bins.add (short_const 1)).exp_clog

-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.b.target.e)`。
theorem childSpans : Short (fun i => 2 ^ i.b.target.e) :=
  ((depths.exp_add spans).exp_add (short_const 2)).exp_add (short_const 2)

-- 读法：要证明的命题是 `Short (fun i => i.b.target.ℓ)`。
theorem childLabels : Short (fun i => i.b.target.ℓ) := by
  have hk := childStations.of_exp
  have hd := childSlots.of_exp
  have hu := depths.of_exp
  refine (depths.mul (hk.add (labels.add (spans.mul (hd.add (hk.add hu)))))).mono fun i => ?_
  change (Parcel.record i.D.scheme (i.D.childD i.a 5) (Sheet.slots i.H) i.b.depth).width ≤ _
  rw [Parcel.width]

variable {f : Case → ℕ}
-- 读法：要证明的命题是 `Cost (fun i => 2 ^ i.b.target.m * f i)`。使用 `h.expand` 给出的结论。
theorem Row.children (h : Row f) : Cost (fun i => 2 ^ i.b.target.m * f i) :=
  h.expand suffix

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-!
# 局部元数与复制行的宽度

**英文原文**

Local arities and replicated row widths
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open BatchDescent Coloring

-- 读法：要证明的命题是 `Short (fun i => (i.D.Sheet i.n).width)`。
theorem sheet : Short (fun i => (i.D.Sheet i.n).width) := by
  refine (tiles.mul (labels.add (counters.add suffix.of_exp))).mono fun i => ?_
  rw [Template.sheet_width]

-- 读法：要证明的命题是 `Row (fun i => i.b.stack.width)`。使用 `sheet.groups.mono` 给出的结论。
theorem stack : Row (fun i => i.b.stack.width) :=
  sheet.groups.mono fun i => by rw [Binning.stack, Format.width_vec]

-- 读法：要证明的命题是 `Row (fun i => i.b.tagCap)`。
theorem parcel : Row (fun i => i.b.tagCap) := by
  have h := Short.groups (tiles.mul counters)
  refine ((long_const 1).row.add ((Long.row (slots.long.mul (long_const 2))).add h)).mono fun i => ?_
  simp only [Binning.tagCap, Group.Parcel, Group.Flags, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]

-- 读法：要证明的命题是 `Short (fun i => (Group.Patch i.q i.n i.D.count).width)`。
theorem patch : Short (fun i => (Group.Patch i.q i.n i.D.count).width) := by
  refine ((short_const 1).add (path.mul ((path.mul (short_const 2)).add (tiles.mul counters)))).mono fun i => ?_
  rw [Group.width_patch]

-- 读法：要证明的命题是 `Short (fun i => (Group.Labels i.n).width)`。
theorem groupLabels : Short (fun i => (Group.Labels i.n).width) := by
  refine (tiles.mul suffix.of_exp).mono fun i => ?_
  rw [Group.Labels, Format.width_vec, Format.width_addr]

-- 读法：要证明的命题是 `Short (fun i => i.b.tagArity)`。
theorem tagArity : Short (fun i => i.b.tagArity) := by
  have hs : Short (fun i => (Group.Summary i.n).width) :=
    (tiles.mul (tiles.of_exp.add (tiles.mul suffix.of_exp))).mono fun i => by rw [Group.width_summary]
  exact ((patch.add hs).add tiles.of_exp).add groupLabels

-- 读法：要证明的命题是 `Short (fun i => (Trail.pointer i.D.scheme 0).width)`。
theorem pointer : Short (fun i => (Trail.pointer i.D.scheme 0).width) := by
  refine ((short_const 1).add ((short_const 0).add (height.add
    (stations.of_exp.add spans.of_exp)))).mono fun i => ?_
  simp only [Trail.pointer, Format.width_pair, Format.width_addr]
  rfl

-- 读法：要证明的命题是 `Short (fun i => i.b.Fields.width)`。
theorem fields : Short (fun i => i.b.Fields.width) := by
  refine (childLabels.add (childStations.mul (childSpans.mul pointer))).mono fun i => ?_
  rw [Fields, Format.width_pair, Format.width_addr, Format.width_vec, Format.width_vec]

-- 读法：要证明的命题是 `Short (fun i => i.b.Tile.width)`。
theorem tile : Short (fun i => i.b.Tile.width) := by
  have hf := slots.mul (suffix.mul (childSlots.mul (short_const 1)))
  refine (suffix.of_exp.add (groupHeight.add (sheet.add ((slots.mul sheet).add hf)))).mono fun i => ?_
  simp only [Tile, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_addr (i.D.scheme.h - i.a + 1), Format.width_bit]

-- 读法：要证明的命题是 `Short (fun i => i.b.arity)`。使用 `tagArity.add` 给出的结论。
theorem arity : Short (fun i => i.b.arity) := (tagArity.add tile).add fields

variable {A B : Case → Format} {f : Case → ℕ}

-- 读法：要证明的命题是 `Cost (fun i => ((A i).pair (B i)).width)`。使用 `h.add` 给出的结论。
theorem pair_cost (h : Cost (fun i => (A i).width)) (h' : Cost (fun i => (B i).width)) :
    Cost (fun i => ((A i).pair (B i)).width) :=
  (h.add h').mono fun _ => (Format.width_pair _ _).le

-- 读法：要证明的命题是 `Cost (fun i => (i.b.Rows (A i)).width)`。
theorem rows (h : Short (fun i => (A i).width)) : Cost (fun i => (i.b.Rows (A i)).width) :=
  (Row.children ((Long.row (childSlots.long.mul childHosts)).add h.groups)).mono
    fun _ => (Fmt.width_rows ..).le

-- 读法：要证明的命题是 `Cost (fun i => i.b.target.format.width)`。
theorem targetFormat : Cost (fun i => i.b.target.format.width) :=
  rows (A := fun i => .addr i.b.target.ℓ) (childLabels.mono fun _ => (Format.width_addr _).le)

-- 读法：要证明的命题是 `Cost (fun i => i.D.format.width)`。这里调用 `pair_cost`。
theorem format : Cost (fun i => i.D.format.width) := by
  have h : Cost (fun i => i.D.scheme.format.width) := by
    refine (Row.hosts ((Long.row (slots.long.mul hosts)).add labels.blocks)).mono fun i => ?_
    rw [Scheme.format, Fmt.width_rows, Format.width_addr]
  apply pair_cost h
  have flags := Long.row (slots.long.mul (long_const 2))
  refine (Row.hosts ((long_const 2).row.add (flags.add counters.blocks))).mono fun i => ?_
  simp only [Template.header, Group.Flags, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]

-- 读法：要证明的命题是 `Cost (fun i => (Fmt.bank i.m i.d (A i)).width)`。
theorem bankFmt (h : Row (fun i => (A i).width)) :
    Cost (fun i => (Fmt.bank i.m i.d (A i)).width) := by
  refine (Row.hosts ((Long.row (slots.long.mul hosts)).add h)).mono fun i => ?_
  rw [Fmt.bank, Format.width_vec, Format.width_pair, Format.width_vec, Format.width_addr]

-- 读法：要证明的命题是 `Cost (fun i => i.b.Bank.width)`。
theorem bank : Cost (fun i => i.b.Bank.width) := bankFmt stack

-- 读法：要证明的命题是 `Cost (fun i => (i.D.groupInput i.a).width)`。
theorem groupInput : Cost (fun i => (i.D.groupInput i.a).width) := bankFmt parcel

-- 读法：要证明的命题是 `Cost (fun i => i.b.Remote.width)`。使用 `Row.hosts` 给出的结论。
theorem remote : Cost (fun i => i.b.Remote.width) :=
  (Row.hosts (stack.left slots)).mono fun i => by rw [Remote, Format.width_vec, Format.width_vec]

-- 读法：要证明的命题是 `Cost (fun i => i.b.Output.width)`。这里调用 `pair_cost`。
theorem output : Cost (fun i => i.b.Output.width) := by
  apply pair_cost targetFormat
  refine (Short.groups (childStations.mul (childSpans.mul pointer))).children.mono fun i => ?_
  rw [Trail.controls, Format.width_vec, Trail.localCommands, Format.width_vec, Format.width_vec, Format.width_vec]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-!
# 访问、修补与选举的成本

**英文原文**

Access, patch, and election costs
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open Coloring

-- 读法：在后续公式中，`Case.tagFee` 是 `i.p.fee i.b.tagDepth i.b.tagCap` 的缩写。
abbrev Case.tagFee (i : Case) := i.p.fee i.b.tagDepth i.b.tagCap
-- 读法：在后续公式中，`Case.sheetFee` 是 `i.p.fee i.b.sheetDepth i.b.stack.width` 的缩写。
abbrev Case.sheetFee (i : Case) := i.p.fee i.b.sheetDepth i.b.stack.width

variable {j v : Case → ℕ}

-- 读法：要证明的命题是 `Cost (fun i => i.p.fee (i.m + j i) (v i))`。这里调用 `h.mono`。
theorem fee (hj : Short (fun i => 2 ^ j i)) (hv : Row v) :
    Cost (fun i => i.p.fee (i.m + j i) (v i)) := by
  have h := (Row.expand ((hv.add (long_const 1).row).add threshold.row) hj).left
    ((short_const 1000).mul ((short_const 1).add weights))
  exact h.mono fun i => by rw [Rounds.Contraction.Prices.fee, mul_assoc]

-- 读法：要证明的命题是 `Cost (fun i => gatherCost i.m (j i) (v i) (i.p.fee (i.m + j i) (v i)))`。
theorem gather (hj : Short (fun i => 2 ^ j i)) (hv : Row v) :
    Cost (fun i => gatherCost i.m (j i) (v i) (i.p.fee (i.m + j i) (v i))) := by
  have hm : Long (fun i => i.m + j i) := hosts.add (Short.long hj.of_exp)
  have hc := ((long_const 100).add ((hm.add ((long_const 3).mul hosts)).add (long_const 1))).pow 200
  have hw := Row.expand ((hm.row.add hv).add (long_const 1).row) hj
  refine ((((fee hj hv).scale 4).add ((Long.row hc).expand hj |>.scale 4)).add
    (hw.scale 1100)).mono fun i => ?_
  rw [gatherCost, mul_assoc 1100]

-- 读法：要证明的命题是 `Cost (fun i => 2 ^ (i.m + i.a) * f i)`。使用 `h.groups.hosts.mono` 给出的结论。
theorem Short.hostGroups {f : Case → ℕ} (h : Short f) : Cost (fun i => 2 ^ (i.m + i.a) * f i) :=
  h.groups.hosts.mono fun i => by rw [pow_add, mul_assoc]

-- 读法：要证明的命题是 `Cost (fun i => Group.patchCost i.m i.d i.a i.n i.D.count i.b.tagCap i.tagFee)`。
private theorem patchCost :
    Cost (fun i => Group.patchCost i.m i.d i.a i.n i.D.count i.b.tagCap i.tagFee) := by
  have patches : Cost (fun i => (Group.Patches i.m i.d i.a i.n i.D.count).width) :=
    patch.hostGroups.mono fun i => by rw [Group.Patches, Format.width_vec]
  have loads : Cost (fun i => (Format.vec i.m (.vec i.q (Group.Parcel i.d i.a i.n i.D.count))).width) :=
    (Row.hosts (parcel.left path)).mono fun i => by rw [Format.width_vec, Format.width_vec]
  have cost := Mixed.long Case.m (((long_const 100).add (hosts.add path.long)).pow 220)
  exact (((((groupInput.add patches).add loads).add cost).scale 1000).add (gather path parcel))

-- 读法：要证明的命题是 `Cost (fun i => Group.electionCost (i.m + i.a) i.n)`。这里调用 `hr.add`。
private theorem election : Cost (fun i => Group.electionCost (i.m + i.a) i.n) := by
  have hr := Short.hostGroups (((short_const 100).add tiles.of_exp).pow 5)
  have hl : Long Case.n := Short.long tiles.of_exp
  have hc := ((long_const 100).add (hl.add (hl.add (hosts.add groupHeight.long)))).pow 42
  exact (hr.add (Long.row hc).cost).left tiles

-- 读法：要证明的命题是 `Cost (fun i => Group.cost (i.m + i.a) i.q i.n i.D.count)`。
private theorem groupCost : Cost (fun i => Group.cost (i.m + i.a) i.q i.n i.D.count) :=
  ((Short.hostGroups ((short_const 1).add tagArity)).scale 100).add (election.scale 4)

-- 读法：要证明的命题是 `Cost (fun i => i.b.bankCost i.tagFee i.sheetFee)`。
theorem bankCost : Cost (fun i => i.b.bankCost i.tagFee i.sheetFee) := by
  have he : Cost (fun i => i.b.Elected.width) :=
    groupLabels.hostGroups.mono fun i => by rw [Elected, Format.width_vec]
  exact ((((((format.add groupInput).add he).add bank).scale 100).add patchCost).add
    groupCost).add (gather slots stack)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-!
# 宿主导航与分组标签网络

**英文原文**

Host navigation and the grouped-label network
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open Coloring

-- 读法：要证明的命题是 `Short (fun i => 2 ^ (i.d + 1))`。使用 `slots.exp_add` 给出的结论。
private theorem priorSlots : Short (fun i => 2 ^ (i.d + 1)) := slots.exp_add (short_const 2)

-- 读法：要证明的命题是 `Short (fun i => 2 ^ ((i.d + 1) + (i.n + 1)))`。使用 `priorSlots.exp_add` 给出的结论。
private theorem maskSlots : Short (fun i => 2 ^ ((i.d + 1) + (i.n + 1))) := priorSlots.exp_add suffix

-- 读法：要证明的命题是 `Cost (fun i => i.b.Prior.width)`。
theorem prior : Cost (fun i => i.b.Prior.width) :=
  (Mixed.long Case.m (priorSlots.long.mul hosts)).mono (fun i => by
    rw [Prior, Neighborhood.Rows, Format.width_vec, Format.width_vec, Format.width_addr])

-- 读法：要证明的命题是 `Cost (fun i => i.b.Nav.width)`。
theorem nav : Cost (fun i => i.b.Nav.width) :=
  (Long.row (childSlots.long.mul childHosts)).children.mono (fun i => by
    rw [Nav, Neighborhood.Rows, Format.width_vec, Format.width_vec, Format.width_addr])

-- 读法：要证明的命题是 `Cost (fun i => i.b.Mask.width)`。
theorem mask : Cost (fun i => i.b.Mask.width) := by
  have h := maskSlots.mul (childSlots.mul (maskSlots.mul (short_const 1)))
  refine (Mixed.long Case.m (Short.long h)).mono fun i => ?_
  rw [Mask, Neighborhood.Mask, Format.width_vec, Format.width_vec, Format.width_vec,
    Format.width_vec, Format.width_bit]

-- 读法：要证明的命题是 `Cost (fun i => i.b.View.width)`。使用 `pair_cost` 给出的结论。
theorem view : Cost (fun i => i.b.View.width) :=
  pair_cost (pair_cost bank remote) (pair_cost nav mask)

-- 读法：要证明的命题是 `Cost (fun i => (Child.Input i.m i.d).width)`。
private theorem childInput : Cost (fun i => (Child.Input i.m i.d).width) := by
  refine (Mixed.long Case.m (slots.long.mul ((long_const 1).add hosts))).mono fun i => ?_
  rw [Child.Input, Format.width_vec, Format.width_vec, Format.width_pair, Format.width_bit, Format.width_addr]

-- 读法：要证明的命题是 `Cost (fun i => i.D.navCost i.a i.b.target.d)`。
private theorem navCost : Cost (fun i => i.D.navCost i.a i.b.target.d) := by
  have h := ((long_const 100).add (childHosts.add childSlots.long)).pow 201
  exact ((format.add (groupInput.scale 3)).add (childInput.scale 68)).add (Long.row h).children

-- 读法：要证明的命题是 `Cost (fun i => i.b.linkCost)`。
theorem linkCost : Cost (fun i => i.b.linkCost) := by
  have h := ((long_const 100).add ((childHosts.add maskSlots.long).add childSlots.long)).pow 40
  exact (((format.scale 12).add (prior.scale 34)).add (navCost.scale 2)).add (Long.row h).children

-- 读法：要证明的命题是 `Cost (fun i => updateCost i.b.target.m i.b.target.d i.a i.b.Tile i.b.Fields)`。
private theorem update : Cost (fun i => updateCost i.b.target.m i.b.target.d i.a i.b.Tile i.b.Fields) :=
  Row.children (((Long.row (childSlots.long.mul childHosts)).scale 4).add
    (Short.groups (((short_const 1).add tile).add fields)))

-- 读法：要证明的命题是 `Cost (fun i => i.b.cost i.tagFee i.sheetFee)`。
theorem charge : Cost (fun i => i.b.cost i.tagFee i.sheetFee) := by
  have send := (view.add ((rows tile).scale 34)).scale 4
  have recv := ((rows fields).add (output.scale 2)).scale 4
  exact (((((format.scale 20).add bankCost).add (linkCost.scale 4)).add send).add update).add recv

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end
