-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Weight
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
import OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Overlay
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding

/-!
经过验证的展开为每个分支给出有界的局部额度。

**英文原文**

A certified expansion supplies bounded local credits for every branch.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Geometry Rounds
open scoped Classical

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
  {w : Scenario F N A a x y} {hF : a.M * (2 * a.D + 1) < Fintype.card F}
  {e k g ℓ D : ℕ} {menu : a.Menu F N A e} {start : w.Code 0 menu}
  {c : w.History k a.waves} {q : w.AtCode hF menu k a.waves le_rfl}

-- 读法：`Certified.check` 的证明用到 `a.historyRow`、`a.waves`、`q.tape`。
theorem Certified.check (hc : w.Certified hF menu k start a.waves c q.frame)
    (written : q.tape = a.path start.tape a.waves (w.tapes c))
    (hu : 0 < a.chart * a.H) {E M : w.V → ℕ}
    (initial : ∀ v, clip a.waves (a.chart * a.H) (start.frame.stage.energyCre a.chart a.H a.g v) ≤ E v ∧
      start.frame.stage.timeCre a.chart a.H a.U v ≤ M v)
    (bound : ∀ (i : ℕ) (u : w.At i) (v : w.V),
      clip a.waves (a.chart * a.H) (u.stage.energyCre a.chart a.H a.g v) ≤ Input.energyLimit g D a.waves ∧
      u.stage.timeCre a.chart a.H a.U v ≤ Input.timeLimit g ℓ D) :
    let z := fun v : w.V => a.credits hF menu k g ℓ D ((q.tape (w.atlas.coord v).1).2 (w.atlas.coord v).2)
    Credits.Check w.loc z E M ∧ ∀ v,
      (z v).power (Fin.last a.waves) = clip a.waves (a.chart * a.H) (q.frame.stage.energyCre a.chart a.H a.g v) ∧
      (z v).time (Fin.last a.waves) = q.frame.stage.timeCre a.chart a.H a.U v := by
  let row (v : w.V) := a.historyRow hF menu k a.waves le_rfl ((q.tape (w.atlas.coord v).1).2 (w.atlas.coord v).2)
  let f v i := Metadata.energyCre (row v i) a.chart a.H a.g
  let t v i := Metadata.timeCre (row v i) a.chart a.H a.U
  have read (i : Fin (a.waves + 1)) (u : w.AtCode hF menu k i.val (Nat.le_of_lt_succ i.isLt))
      (ht : u.tape = a.path start.tape i.val (w.tapes (before c (Nat.le_of_lt_succ i.isLt)))) :
      (fun v => f v i) = u.frame.stage.energyCre a.chart a.H a.g ∧
      (fun v => t v i) = u.frame.stage.timeCre a.chart a.H a.U := by
    have eq (v : w.V) : row v i = (w.stored u.frame (w.atlas.coord v)).2 := by
      unfold row
      rw [written, Design.historyRow_path, ← u.read, ht]
      rfl
    exact ⟨funext fun v => by simp only [f, eq, w.stored_energyCre],
      funext fun v => by simp only [t, eq, w.stored_timeCre]⟩
  have first := read 0 start rfl
  have last := read (Fin.last a.waves) q written
  have step (j : Fin a.waves) :
      Geometry.Balanced (w.loc j) 0 (fun v => f v j.castSucc) (fun v => f v j.succ) ∧
      Geometry.Balanced (w.loc j) 0 (fun v => t v j.castSucc) (fun v => t v j.succ) := by
    -- 推导：从 `hc j j.isLt` 中取出 `u, u', hp, hq, hb`。
    obtain ⟨u, u', hp, hq, hb⟩ := hc j j.isLt
    obtain ⟨h₁, h₂⟩ := read j.castSucc u hp
    obtain ⟨h₃, h₄⟩ := read j.succ u' hq
    rw [h₁, h₂, h₃, h₄]
    exact ⟨hb.energy, hb.time⟩
  have lim (v : w.V) (i : Fin (a.waves + 1)) :
      clip a.waves (a.chart * a.H) (f v i) ≤ Input.energyLimit g D a.waves ∧ t v i ≤ Input.timeLimit g ℓ D := by
    induction i using Fin.lastCases with
    | last =>
      rw [congrFun last.1 v, congrFun last.2 v]
      exact bound _ q.frame v
    | cast j =>
      -- 推导：从 `hc j j.isLt` 中取出 `u, _, hp, _`。
      obtain ⟨u, _, hp, _⟩ := hc j j.isLt
      obtain ⟨h₁, h₂⟩ := read j.castSucc u hp
      rw [congrFun h₁ v, congrFun h₂ v]
      exact bound _ u.frame v
  refine ⟨Credits.check_issue (a := f) (b := t) _ hu ?_ (fun j => (step j).1) (fun j => (step j).2) lim, fun v => ?_⟩
  · intro v
    rw [congrFun first.1 v, congrFun first.2 v]
    exact initial v
  · obtain ⟨hl, ht⟩ := lim v (Fin.last a.waves)
    exact ⟨(Credits.issue_power _ _ _ _ hl).trans (congrArg _ (congrFun last.1 v)),
      (Credits.issue_time _ _ _ _ ht).trans (congrFun last.2 v)⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-!
对所有初始形状，额度和区域检查都使用同一条局部规则。

**英文原文**

The credits and regional checks use one local rule across all initial shapes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
open Finset
open scoped Classical
variable {F T V E X : Type} {r t : ℕ} [Fintype V] (s : Stage F r t T V E X)

-- 读法：结论为 `U * Fintype.card {i : Fin (s.scene.cell v).stations.length // (Sphere.Layout.item s.scene.cell ⟨v, i⟩).label.role = .collector} ≤ s.timeCre P H U v`。
theorem collectors_timeCre (P H U : ℕ) (v : V) :
    U * Fintype.card {i : Fin (s.scene.cell v).stations.length //
      (Sphere.Layout.item s.scene.cell ⟨v, i⟩).label.role = .collector} ≤ s.timeCre P H U v := by
  have eq (r : Role) : (if r = .collector then 1 else 0) = r.collected 1 := by
    cases r <;> simp [Role.collected]
  refine le_trans (Nat.mul_le_mul_left U (le_of_eq ?_))
    ((Nat.le_add_right (U * s.tally P collectorUnit v) _).trans (Nat.le_add_right ..))
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter]
  let l := (s.scene.cell v).stations
  let f := fun a : s.St => a.label.role.collected 1
  trans ∑ i : Fin l.length, f (l.get i)
  · exact sum_congr rfl fun i _ => eq _
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = (l.map f).sum
  rw [← List.map_ofFn, List.ofFn_get]

-- 读法：`s.tally P Role.collected v` 不超过 `s.energyCre P H g v`。使用 `Nat.le_add_left` 给出的结论。
theorem collected_energyCre (P H g : ℕ) (v : V) :
    s.tally P Role.collected v ≤ s.energyCre P H g v := Nat.le_add_left ..

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
  {x y : Wire} {g ℓ D T b d p l : ℕ} [ExpChar F p] {W : ℝ}

section
variable (S : Scheme F)
local notation "Cfg" => design S g ℓ D b d p l

-- 读法：在后续公式中，`credits` 是 `(Cfg).credits hF (localMenu S hK mobility k) k g ℓ D raw` 的缩写。
abbrev credits (hK : Ready K ℓ D g (p ^ l) b d)
    (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (mobility : B S.ℓ → B S.k → Bool) (k : ℕ)
    (raw : B ((Cfg).widthAt (panelQuery S g ℓ D b d p l k).width k (Cfg).waves)) :=
  (Cfg).credits hF (localMenu S hK mobility k) k g ℓ D raw
end

variable {S : Scheme F} (P : Input F x y S.h D T (d * b) g W) {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)

local notation "Cfg" => design S g ℓ D b d p l
local notation "H" => SphereScale.energy ℓ D (d * b)

omit [Fintype F] [ExpChar F p] in
-- 读法：`(P.localWorld A sc hK s).loc` 等于 `(P.localWorld A sc hK t).loc`。两端由定义化简为同一项。
theorem loc_eq (s t : P.Occupied → Shape (probes ℓ D) b d) :
    (P.localWorld A sc hK s).loc = (P.localWorld A sc hK t).loc := rfl

variable {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
  {mobility : B S.ℓ → B S.k → Bool} {k : ℕ} {pres : S.Presentation z P.diagram}
  {placed : P.Placed pres A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val)
    (fun v => mobility ((z v.1).2 v.2.1) v.2.2)}
  {ranks : P.LocalRanks} {init : initialChoices ℓ D b d ≤ 2 ^ k}

-- 读法：`check_motion` 的证明用到 `Scenario.Certified.check`、`motion.good`、`motion.written`。
theorem check_motion (s : P.Occupied → Shape (probes ℓ D) b d)
    (motion : (P.localWorld A sc hK s).CompleteRun hF (localMenu S hK mobility k) k
      (P.localCode A sc hK s placed ranks init)) (i : motion.I)
    {E M : P.Occupied → ℕ}
    (initial : ∀ v, clip (Cfg).waves (p ^ l * H) ((P.plant (P.kit sc hK) s).energyCre (p ^ l) H (2 * g) v) ≤ E v ∧
      (P.plant (P.kit sc hK) s).timeCre (p ^ l) H (D ^ 5) v ≤ M v) :
    let q := motion.code i
    let vtx := fun v => credits S hK hF mobility k ((q.tape (A.coord v).1).2 (A.coord v).2)
    Credits.Check (P.localWorld A sc hK s).loc vtx E M ∧ ∀ v,
      (vtx v).power (Fin.last (Cfg).waves) = clip (Cfg).waves (p ^ l * H) (q.frame.stage.energyCre (p ^ l) H (2 * g) v) ∧
      (vtx v).time (Fin.last (Cfg).waves) = q.frame.stage.timeCre (p ^ l) H (D ^ 5) v :=
  Scenario.Certified.check (motion.good i) (motion.written i)
    (Nat.mul_pos sc.pos sc.Hpos) initial fun _ a v =>
      P.credit_limits (P.kit sc hK) s sc a.reach a.valid (Cfg).waves v

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# 局部展开的标签与可见检验

下述预言机仅用于计算标量表项。可见的检查只读取候选蓝图和候选额度。

**英文原文**

The labels and the visible checks of the local expansion

The oracle below is used only inside scalar table entries. The
visible checks operate on a proposed blueprint and proposed credits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
local notation "PanelOK" => P.ReadyPanel A hK hF mobility k U status pres

-- 读法：在后续公式中，`Book` 是 `Journal P.Occupied k (Cfg).waves U.digits` 的缩写。
abbrev Book (_h : PanelOK) := Journal P.Occupied k (Cfg).waves U.digits
-- 读法：在后续公式中，`Guess` 是 `U.Tag S g ℓ (Cfg).waves` 的缩写。
abbrev Guess (_h : PanelOK) := U.Tag S g ℓ (Cfg).waves
-- 读法：`zeroShape` 的取值由 `(fun _ => 0, fun _ => 0)` 给出。
def zeroShape (_h : PanelOK) : P.InitialShapes ℓ := fun _ => (fun _ => 0, fun _ => 0)

variable (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

-- 读法：在后续公式中，`printing` 是 `U.advance (lastPage S sc z A.coord c) status (c.close A.coord U.pad)` 的缩写。
abbrev printing (c : h.Book) := U.advance (lastPage S sc z A.coord c) status (c.close A.coord U.pad)

-- 读法：在后续公式中，`partition` 是 `(P.localWorld A sc hK h.zeroShape).loc` 的缩写。
abbrev partition := (P.localWorld A sc hK h.zeroShape).loc

-- 读法：`admissible` 的构造用到 `U.passes`、`A.coord`、`h.partition`。
def admissible (c : h.Book) (a : P.Occupied → h.Guess) :=
  U.passes S A.coord (h.partition sc) (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves) P.initialTimeTokens
    (T / u) z (h.printing sc c) a

-- 读法：在后续公式中，`Paths` 是 `Candidate (h.admissible sc)` 的缩写。
abbrev Paths := Candidate (h.admissible sc)

-- 读法：`actual` 的结果类型为 `h.Guess`。
def actual (c : h.Book) (v : P.Occupied) : h.Guess :=
  let i := A.coord v
  (U.canonical S z (h.printing sc c) i.1 i.2,
    Input.credits S hK hF mobility k (((lastPage S sc z A.coord c) i.1).2 i.2))

-- 读法：在后续公式中，`geometry` 是 `U.complete S A.coord (fun i => (c.2.val i).1)` 的缩写。
abbrev geometry (c : h.Paths sc) := U.complete S A.coord (fun i => (c.2.val i).1)
-- 读法：在后续公式中，`data` 是 `U.overlay S z (h.printing sc c.1) (h.geometry sc c)` 的缩写。
abbrev data (c : h.Paths sc) := U.overlay S z (h.printing sc c.1) (h.geometry sc c)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# 每个成立的分支都有一个可接受的证书

**英文原文**

Every true branch has an admissible certificate
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (E : Expansion sc h) (i : E.I)

-- 读法：`creditAt` 的取值由 `Input.credits S hK hF mobility k (((((E.motion i.1).code i.2.1).tape (A.coord v).1).2 (A.coord v).2))` 给出。
def creditAt (v : P.Occupied) :=
  Input.credits S hK hF mobility k (((((E.motion i.1).code i.2.1).tape (A.coord v).1).2 (A.coord v).2))

-- 读法：在后续公式中，`CertifiedTerm` 是 `U.Checked pres ℓ A.coord (creditAt E i) (E.record i) (E.term i) (E.shows i)` 的缩写。
abbrev CertifiedTerm := U.Checked pres ℓ A.coord (creditAt E i) (E.record i) (E.term i) (E.shows i)

-- 读法：`h.actual sc (E.select.write i)` 等于 `fun v => (U.canonical S z (E.record i) (A.coord v).1 (A.coord v).2, creditAt E i v)`。用函数外延性比较等号两侧在 `v` 处的取值。
theorem actual_eq : h.actual sc (E.select.write i) = fun v =>
    (U.canonical S z (E.record i) (A.coord v).1 (A.coord v).2, creditAt E i v) := by
  funext v
  unfold actual printing
  rw [←E.record_eq, E.written]
  rfl

-- 读法：要证明的命题是 `h.admissible sc (E.select.write i) (h.actual sc (E.select.write i))`。
theorem accepted (M : CertifiedTerm E i) :
    h.admissible sc (E.select.write i) (h.actual sc (E.select.write i)) := by
  have eq := U.complete_of_vacant S A.coord (U.canonical S z (E.record i)) M.away
  let init := P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves
  have hl := (P.check_motion A sc hK i.1 (E.motion i.1) i.2.1 (E := init) (M := P.initialTimeTokens)
    (fun v => ⟨P.initial_energy_fits (P.kit sc hK) i.1 _ v, P.initial_time_fits (P.kit sc hK) i.1 sc v⟩)).1
  rw [P.loc_eq A sc hK i.1 h.zeroShape] at hl
  unfold admissible printing
  rw [← E.record_eq, actual_eq E i]
  refine ⟨?_, hl, M.quota⟩
  change U.Valid S z (E.record i) (U.complete S A.coord (fun v =>
    U.canonical S z (E.record i) (A.coord v).1 (A.coord v).2))
  rw [eq]
  exact M.valid

variable (h sc)

-- 读法：`weight` 的取值由 `journalWeight S z sc hK hF mobility U A.coord c (A.coord v)` 给出。
def weight (c : h.Book) (v : P.Occupied) := journalWeight S z sc hK hF mobility U A.coord c (A.coord v)

-- 读法：`factor` 的取值由 `Geometry.factor (h.actual sc) (h.admissible sc) (h.weight sc) c` 给出。
def factor (c : h.Paths sc) := Geometry.factor (h.actual sc) (h.admissible sc) (h.weight sc) c

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# 从可见的几何选择读取图式

**英文原文**

Reading a diagram from the visible choice of geometry
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

variable (h sc)

-- 读法：`(lastPage S sc z A.coord c i).1` 等于 `A.graph i`。使用 `Copy.path_nav` 给出的结论。
theorem sameGraph (c : h.Book) (i : B S.m) : (lastPage S sc z A.coord c i).1 = A.graph i :=
  Copy.path_nav (design S g ℓ D b d p l) (panelTape S sc z (c.opening A.coord)) _ _ i

include sc in
-- 读法：`g` 不超过 `D ^ Layout.Sharing.allocation g ℓ`。
theorem ports_fit : g ≤ D ^ Layout.Sharing.allocation g ℓ := by
  have hpos : 0 < Layout.Sharing.allocation g ℓ := by unfold Layout.Sharing.allocation; omega
  exact ((Nat.le_mul_of_pos_left g (by decide)).trans sc.degree).trans (Nat.le_self_pow hpos.ne' _)

-- 读法：在后续公式中，`hostGraph` 是 `U.graph h.parents (h.sameGraph sc c) (ports_fit sc) (c.close A.coord U.pad)` 的缩写。
abbrev hostGraph (c : h.Book) :=
  U.graph h.parents (h.sameGraph sc c) (ports_fit sc) (c.close A.coord U.pad)

-- 读法：`board` 的取值由 `U.admitted S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) pres h.directed` 给出。
def board (c : h.Paths sc) : Geometry.Board (U.revised S) (h.data sc c) x y u :=
  U.admitted S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) pres h.directed

-- 读法：在后续公式中，`term` 是 `(h.board sc c).term` 的缩写。
abbrev term (c : h.Paths sc) := (h.board sc c).term
-- 读法：在后续公式中，`shows` 是 `(h.board sc c).shows` 的缩写。
abbrev shows (c : h.Paths sc) := (h.board sc c).shows

-- 读法：要证明的命题是 `Payload.Retains pres (h.shows sc c).pres U.split U.outer`。使用 `U.admitted_retains` 给出的结论。
theorem retains (c : h.Paths sc) : Payload.Retains pres (h.shows sc c).pres U.split U.outer :=
  U.admitted_retains S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) pres h.directed

-- 读法：`((h.shows sc c).pres.boundary i).val.1.1` 等于 `U.destination S (h.geometry sc c) (pres.boundary i).val.1.1`。使用 `U.admitted_address` 给出的结论。
theorem destination (c : h.Paths sc) (i : slots x ⊕ slots y) :
    ((h.shows sc c).pres.boundary i).val.1.1 =
      U.destination S (h.geometry sc c) (pres.boundary i).val.1.1 :=
  U.admitted_address S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) pres h.directed i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# 将公共子图投影到原宿主图

**英文原文**

Projection of the common child graph to the original host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Sharing Trie)
open scoped Classical
variable {F K : Type} [Field F] [Finite K] {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g : ℕ} {x y : Wire} {W : ℝ} {P : Input F x y S.h D T R g W}
  (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  {old : P.V ↪ B S.m} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {nav : B S.m → B d → B S.m} (A : Children.Shows P.adj old (nav, status))
  (hdata : ∀ i, (data i).1 = nav i) (hg : g ≤ D ^ k) (c : U.selectors.obj)

-- 读法：`(root w).1` 属于 `insert (root v).1 (P.adj (root v).1)`。
theorem graph_neighbors {v w : Host P.V M D k n}
    (hw : w ∈ (U.graph A hdata hg c).adj v) : (root w).1 ∈ insert (root v).1 (P.adj (root v).1) :=
  (Finset.mem_product.mp (Children.adj_near (U.graphTree A hg) (fun _ => Finset.mem_product.mpr
    ⟨Finset.mem_insert_self .., Finset.mem_univ _⟩) hw)).1

-- 读法：`((U.split (U.destination S mat v).1).1, (U.destination S mat v).2.1)` 等于 `(v.1, v.2.1)`。
private theorem dest_parent (mat : U.Matrix S) (v : S.Vtx) :
    ((U.split (U.destination S mat v).1).1, (U.destination S mat v).2.1) = (v.1, v.2.1) := by
  simp only [destination, centerAt, Equiv.apply_symm_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

variable (h sc)

local notation "L" => Layout.Sharing.allocation g ℓ
local notation "H" => Print.Host P.V (chunks ℓ D) D L n
local notation "shape" => Print.Children.Part (chunks ℓ D) D L n

-- 读法：`parent` 的取值由 `(Print.root (show H from v)).1` 给出。
def parent (c : h.Paths sc) (v : (h.term sc c).V) : P.V := (Print.root (show H from v)).1

-- 读法：`h.parent sc c w` 属于 `insert (h.parent sc c v) (P.adj (h.parent sc c v))`。使用 `U.graph_neighbors` 给出的结论。
theorem parent_mem (c : h.Paths sc) {v w : (h.term sc c).V} (hw : w ∈ (h.term sc c).frame.N v) :
    h.parent sc c w ∈ insert (h.parent sc c v) (P.adj (h.parent sc c v)) :=
  U.graph_neighbors h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord U.pad) hw

-- 读法：结论为 `(h.term sc c).V = H ∧ (h.term sc c).frame.N = (U.graphTree h.parents (ports_fit sc)).adj ∧ (h.term sc c).frame.frozen = (U.graphTree h.parents (ports_fit sc)).fixed`。
theorem common (c : h.Paths sc) : (h.term sc c).V = H ∧
    (h.term sc c).frame.N = (U.graphTree h.parents (ports_fit sc)).adj ∧
    (h.term sc c).frame.frozen = (U.graphTree h.parents (ports_fit sc)).fixed :=
  ⟨rfl, rfl, rfl⟩

include h sc in
-- 读法：`Fintype.card shape` 不超过 `D ^ (terminalExponent g ℓ)`。这里调用 `Nat.le_of_mul_le_mul_right`。
theorem per_parent : Fintype.card shape ≤ D ^ (terminalExponent g ℓ) := by
  have he := Fintype.card_congr (Print.Children.parts P.V (chunks ℓ D) D L n)
  rw [Fintype.card_prod] at he
  have hk := U.graph_cells h.parents (ports_fit sc) (σ:=ℓ) rfl
  rw [he, mul_comm (Fintype.card P.V)] at hk
  exact Nat.le_of_mul_le_mul_right hk (Fintype.card_pos_iff.mpr h.populated)

-- 读法：结论为 `let v := (h.term sc c).frame.place (Packing.portEnd (h.term sc c).diagram i) (h.parent sc c v.1, v.2) = P.place (Packing.portEnd P.diagram i)`。
set_option maxHeartbeats 550000 in
theorem parent_ext (c : h.Paths sc) (i : slots x ⊕ slots y) :
    let v := (h.term sc c).frame.place (Packing.portEnd (h.term sc c).diagram i)
    (h.parent sc c v.1, v.2) = P.place (Packing.portEnd P.diagram i) := by
  intro v
  let v₀ := Packing.portEnd P.diagram i
  have h₁ := (congrArg (fun w : U.Actors S => ((U.split w.1).1, w.2.1))
    (h.destination sc c i)).trans (U.dest_parent (h.geometry sc c) _)
  rw [Payload.owner, Payload.owner, (h.shows sc c).vertex] at h₁
  have hs := congrArg Prod.fst (Print.Children.host_split A.host U.slot v.1)
  have he' : (A.host (h.parent sc c v.1), cellIndex S.h v.2) =
      ((pres.vertex v₀).1, (pres.vertex v₀).2.1) :=
    (congrArg (fun i => (i, cellIndex S.h v.2)) hs.symm).trans h₁
  have h₀ := h.placed.location (Packing.portEnd P.diagram i)
  rw [h.location] at h₀
  have eq := he'.trans h₀
  exact Prod.ext (A.host.injective (Prod.mk.inj eq).1) ((cellIndex S.h).injective (Prod.mk.inj eq).2)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# 经检验的和中各项的通用元数界

**英文原文**

Universal arity bounds for the terms of the checked sum
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (h sc)

-- 证明只用到有限编码的宽度，因此让编码的基数保持不透明。
attribute [local irreducible] Print.indexBits

-- 读法：要证明的命题是 `Concentrated P (h.term sc c) (Geometry.overhead g (terminalExponent g ℓ)) n ℓ`。这里调用 `U.approved_term`。
theorem concentrated (c : h.Paths sc) :
    Concentrated P (h.term sc c) (Geometry.overhead g (terminalExponent g ℓ)) n ℓ := by
  have he := P.initial_energy_total sc (Cfg).waves
  have ht := P.initial_time_total (P.kit sc hK) h.zeroShape sc
  rw [Nat.cast_sum] at he ht
  exact U.approved_term (P := P) h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord U.pad)
    pres h.directed c.2.val c.2.property rfl he ht

-- 读法：`((h.term sc c).frame.C i).card` 不超过 `3`。使用 `U.graph_coreDegree` 给出的结论。
theorem trivalent (c : h.Paths sc) (i : (h.term sc c).V) : ((h.term sc c).frame.C i).card ≤ 3 :=
  U.graph_coreDegree h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord U.pad) i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
对候选方案的可见检查与此前的移动历史无关。

**英文原文**

Visible proposal checks are independent of the motion history.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable (h : P.ReadyPanel A hK hF mobility k U status pres)

-- 读法：`h.admissible sc c a` 与 `h.admissible sc c' a` 等价。这里调用 `U.passes_advance`。
theorem admissible_eq (sc : Scales g ℓ D T (p ^ l) b d) (c c' : h.Book)
    (a : P.Occupied → h.Guess) : h.admissible sc c a ↔ h.admissible sc c' a := by
  have nav (t : h.Book) (i : B S.m) : (lastPage S sc z A.coord t i).1 = (z i).1 :=
    Copy.path_nav Cfg ..
  exact U.passes_advance S A.coord _ _ _ _ z a status _ _ (fun i => (nav c i).trans (nav c' i).symm)

include h in
-- 读法：要证明的命题是 `Print.Printer.vacantHeld S A.coord z`。
theorem vacantHeld : Print.Printer.vacantHeld S A.coord z := by
  intro i b hb l
  have no := mt (h.placed.live_iff (i, b)).mp hb
  have : IsEmpty ((S.decode ((z i).2 b)).Pin l) := ⟨fun j => no ⟨l, ⟨j⟩⟩⟩
  simp [Print.Printer.held, Scheme.extWidth]

-- 读法：`(A.coord v).2 = (A.coord u').2` 与 `Neighborhood.Reach A.graph ((Cfg).U + 1) (A.coord v).1 (A.coord u').1` 同时成立。按 `y ∈ Set.range A.coord` 成立与否分情况。
/-- 所有非空查询都局限于相应的块以及给定邻域之内。

英文原文：All nonempty queries stay in the block and the prescribed neighborhood.
-/
theorem query_near (sc : Scales g ℓ D T (p ^ l) b d) (c : h.Book) (v u' : P.Occupied)
    (i : U.Queries S (P.localWorld A sc hK h.zeroShape) v)
    (hi : U.query S (P.localWorld A sc hK h.zeroShape) A.coord (h.printing sc c) v i = some u') :
    (A.coord v).2 = (A.coord u').2 ∧
      Neighborhood.Reach A.graph ((Cfg).U + 1) (A.coord v).1 (A.coord u').1 := by
  rcases i with _ | i | i
  · have he : v = u' := Option.some.inj hi
    subst u'
    exact ⟨rfl, .refl ..⟩
  · let y := U.targetCell S A.coord (h.printing sc c) v i
    change Function.extend A.coord some (fun _ => none) y = some u' at hi
    -- 推导：记下中间结论 `he`：`A.coord u' = y`。
    have he : A.coord u' = y := by
      by_cases hv : y ∈ Set.range A.coord
      · obtain ⟨j, hj⟩ := hv
        rw [← hj, A.coord.injective.extend_apply] at hi
        exact (Option.some.inj hi) ▸ hj
      · rw [Function.extend_apply' _ _ _ hv] at hi
        cases hi
    rw [he]
    refine ⟨rfl, ?_⟩
    have nav : (fun j => (lastPage S sc z A.coord c j).1) = A.graph :=
      funext fun _ => Copy.path_nav Cfg ..
    have hn := U.nav_reach S (lastPage S sc z A.coord c) status (c.close A.coord U.pad)
      (U.split.symm ((A.coord v).1, i.1)) i.2
    rw [Equiv.apply_symm_apply, nav] at hn
    exact (Neighborhood.Reach.refl A.graph (Cfg).U (A.coord v).1).join hn
  -- 推导：记下中间结论 `he`：`i.val = u'`。
  · have he : i.val = u' := Option.some.inj hi
    subst u'
    exact (Finset.mem_filter.mp i.property).2

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
所有候选方案的检查都只编译一次，与选择器无关。

**英文原文**

Compile all proposal checks once, independently of the selectors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable (h : P.ReadyPanel A hK hF mobility k U status pres)
  (sc : Scales g ℓ D T (p ^ l) b d)

local notation "world" => P.localWorld A sc hK h.zeroShape

-- 读法：在后续公式中，`checkPins` 是 `U.checkPins S world g ℓ v` 的缩写。
abbrev checkPins (v : P.Occupied) := U.checkPins S world g ℓ v

-- 读法：在后续公式中，`checkInputs` 是 `U.checkInputs S world A.coord (h.printing sc c) (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves) P.initialTimeTokens z a v` 的缩写。
abbrev checkInputs (c : h.Book) (a : P.Occupied → h.Guess) (v : P.Occupied) :
    h.checkPins sc v → Bool :=
  U.checkInputs S world A.coord (h.printing sc c) (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves)
    P.initialTimeTokens z a v

-- 读法：`admissible_binary` 的证明用到 `U.passes_binary`、`A.coord`、`h.printing`。
/-- 对于每个候选历史，选取任意参考选择器字都会给出相同的检验。

英文原文：Any reference selector word gives the same tests for every proposed history.
-/
theorem admissible_binary (c₀ : h.Book) :
    let b' := U.checkWidth S g ℓ Cfg
    ∃ test : ∀ v, BitFormula (h.checkPins sc v),
      (∀ v, (test v).cost ≤ (3 * b' + 2) * 2 ^ b' + 1) ∧
      ∀ (c : h.Book) (a : P.Occupied → h.Guess),
        h.admissible sc c a ↔ ∀ v, (test v).eval (h.checkInputs sc c₀ a v) = true := by
  obtain ⟨test, small, works⟩ :=
    U.passes_binary S world (g := g) (σ := ℓ) A.coord (h.printing sc c₀) (T / u)
  exact ⟨test, small, fun c a => (h.admissible_eq sc c c₀ a).trans (works _ _ _ h.vacantHeld a)⟩

-- 读法：在后续公式中，`requests` 是 `Σ v, h.checkPins sc v` 的缩写。
abbrev requests := Σ v, h.checkPins sc v

-- 读法：`Fintype.card (Σ v, Q v)` 不超过 `Fintype.card V * n`。这里调用 `Finset.sum_le_sum`。
private theorem requests_card {V : Type} [Fintype V] (Q : V → Type) [∀ v, Fintype (Q v)]
    (n : ℕ) (hn : ∀ v, Nat.card (Q v) ≤ n) :
    Fintype.card (Σ v, Q v) ≤ Fintype.card V * n := by
  simp only [Nat.card_eq_fintype_card] at hn
  rw [Fintype.card_sigma]
  exact (Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hn v).trans_eq (by simp)

-- 读法：`Fintype.card (h.requests sc)` 不超过 `Fintype.card P.Occupied * U.checkWidth S g ℓ Cfg`。
theorem requests_bound :
    Fintype.card (h.requests sc) ≤ Fintype.card P.Occupied * U.checkWidth S g ℓ Cfg := by
  refine requests_card (h.checkPins sc) _ fun v => ?_
  have hh := U.check_size S world g ℓ v
  rw [← Nat.card_eq_fintype_card] at hh
  exact hh

-- 读法：`checkPlan` 的结果类型为 `Copy.Plan src A.graph ((Cfg).U + 1) (fun i : h.requests sc => A.coord i.1) (fun i s => h.checkInputs sc c₀ (a s) i.1 i.2)`。
/-- 固定面板后，只有标签比特可变。每个这样的比特要么是填充常量，要么复制自同一块内、波作用半径内的位置。

英文原文：For a fixed panel, only the tag bits vary. Every such bit is either
a padding constant or a copy from the same block within the wave radius.
-/
def checkPlan (c₀ : h.Book) {Ω : Type*} {src : Copy.Source Ω S.m S.h}
    (a : Ω → P.Occupied → h.Guess)
    (ha : ∀ v i, (fun s => U.tagCode S g ℓ (Cfg).waves (a s v) i) ∈ src (A.coord v)) :
    Copy.Plan src A.graph ((Cfg).U + 1) (fun i : h.requests sc => A.coord i.1)
      (fun i s => h.checkInputs sc c₀ (a s) i.1 i.2) := by
  apply Copy.plan A.sym
  rintro ⟨v, i|i|⟨r', i⟩⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  change Copy.Visible src A.graph ((Cfg).U + 1) (A.coord v)
    (fun s => U.tagCode S g ℓ (Cfg).waves
      ((U.query S world A.coord (h.printing sc c₀) v r').elim (U.blankTag S g ℓ (Cfg).waves) (a s)) i)
  cases he : U.query S world A.coord (h.printing sc c₀) v r' with
  | none => exact .inl ⟨U.tagCode S g ℓ (Cfg).waves (U.blankTag S g ℓ (Cfg).waves) i, rfl⟩
  | some u' =>
    obtain ⟨hb, hr⟩ := h.query_near sc c₀ v u' r' he
    refine .inr ⟨(A.coord u').1, hr, ?_⟩
    rw [hb]
    exact ha u' i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end
