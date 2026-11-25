-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sigma
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Concentration.Kits
import OAI.LinearAlgebra.MatrixExponent.Sphere.Scalar.Term
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local

/-!
# 用有界字母表核验各区域的预算

每一步同时激活一组互不相交的区域，分别检验每一区域内的总和。能量取整在每一步、每个单元上至多造成一个单位的误差。将精度取为步数加一即可吸收总误差。

**英文原文**

Checking regional budgets using a bounded alphabet

At every step a disjoint set of regions is active. We verify the
sum over each region separately. Truncating each energy to an integer
can cost one unit per cell per step. Choosing the precision one
greater than the number of steps absorbs the resulting error.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Finset
open scoped Classical

variable {V : Type} [Fintype V]

-- 读法：`region` 的取值由 `univ.filter fun w => p w = v` 给出。
def region (p : V → V) (v : V) := univ.filter fun w => p w = v

-- 读法：`Balanced` 的取值由 `∀ v, (∑ w ∈ region p v, b w) ≤ ∑ w ∈ region p v, (a w + loss)` 给出。
def Balanced (p : V → V) (loss : ℕ) (a b : V → ℕ) :=
  ∀ v, (∑ w ∈ region p v, b w) ≤ ∑ w ∈ region p v, (a w + loss)

-- 读法：`(∑ v, b v)` 不超过 `(∑ v, a v) + Fintype.card V * loss`。
theorem Balanced.total {p : V → V} {loss : ℕ} {a b : V → ℕ} (h : Balanced p loss a b) :
    (∑ v, b v) ≤ (∑ v, a v) + Fintype.card V * loss := by
  have he (f : V → ℕ) : (∑ v, ∑ w ∈ region p v, f w) = ∑ w, f w := by
    simp only [region, sum_filter]
    rw [sum_comm]
    simp
  have hr := sum_le_sum (fun v (_ : v ∈ univ) => h v)
  rw [he, he, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul] at hr
  exact hr

-- 读法：`clip` 的取值由 `(n + 1) * x / unit` 给出。
def clip (n unit x : ℕ) := (n + 1) * x / unit

-- 读法：`clip n u a * u` 不超过 `(n + 1) * a`。使用 `Nat.div_mul_le_self` 给出的结论。
theorem clip_low (n u a : ℕ) : clip n u a * u ≤ (n + 1) * a := Nat.div_mul_le_self ..

-- 读法：`(n + 1) * a` 不超过 `(clip n u a + 1) * u`。使用 `Nat.lt_mul_div_succ` 给出的结论。
theorem clip_high (n a : ℕ) {u : ℕ} (hu : 0 < u) : (n + 1) * a ≤ (clip n u a + 1) * u :=
  (Nat.lt_mul_div_succ _ hu).le.trans_eq (mul_comm ..)

-- 读法：`clip n u a` 不超过 `clip n u b`。使用 `Nat.div_le_div_right` 给出的结论。
theorem clip_mono (n u : ℕ) {a b : ℕ} (h : a ≤ b) : clip n u a ≤ clip n u b :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

-- 读法：`clip n u x` 不超过 `(n + 1) * B`。这里调用 `Nat.le_of_mul_le_mul_right`。
theorem clip_bound (n u x B : ℕ) (hu : 0 < u) (hx : x ≤ B * u) : clip n u x ≤ (n + 1) * B := by
  apply Nat.le_of_mul_le_mul_right _ hu
  rw [mul_assoc]
  exact (clip_low n u x).trans (Nat.mul_le_mul_left _ hx)

-- 读法：要证明的命题是 `Balanced p 1 (clip n u ∘ a) (clip n u ∘ b)`。这里调用 `Nat.le_of_mul_le_mul_right`。
theorem Balanced.clip {p : V → V} {a b : V → ℕ} (h : Balanced p 0 a b)
    (n : ℕ) {u : ℕ} (hu : 0 < u) : Balanced p 1 (clip n u ∘ a) (clip n u ∘ b) := by
  intro v
  apply Nat.le_of_mul_le_mul_right _ hu
  rw [sum_mul, sum_mul]
  calc
    _ ≤ ∑ w ∈ region p v, (n + 1) * b w := sum_le_sum (fun i _ => clip_low n u (b i))
    _ ≤ ∑ w ∈ region p v, (n + 1) * a w := by
      rw [←mul_sum, ←mul_sum]
      exact Nat.mul_le_mul_left _ (h v)
    _ ≤ _ := sum_le_sum (fun i _ => clip_high n (a i) hu)

-- 读法：`Admitted` 的取值由 `∀ i : Fin n, Balanced (p i) loss (f i.castSucc) (f i.succ)` 给出。
def Admitted {n : ℕ} (p : Fin n → V → V) (loss : ℕ) (f : Fin (n + 1) → V → ℕ) :=
  ∀ i : Fin n, Balanced (p i) loss (f i.castSucc) (f i.succ)

-- 读法：`(∑ v, f (Fin.last n) v)` 不超过 `(∑ v, f 0 v) + n * (Fintype.card V * loss)`。对 `i` 作归纳，采用 `Fin.induction` 的归纳原则。
theorem Admitted.total {n : ℕ} {p : Fin n → V → V} {loss : ℕ} {f : Fin (n + 1) → V → ℕ}
    (h : Admitted p loss f) :
    (∑ v, f (Fin.last n) v) ≤ (∑ v, f 0 v) + n * (Fintype.card V * loss) := by
  suffices ∀ i : Fin (n + 1), (∑ v, f i v) ≤ (∑ v, f 0 v) + i.val * (Fintype.card V * loss) from this _
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [Fin.val_succ, Nat.succ_mul, ←add_assoc]
    exact (h i).total.trans (Nat.add_le_add_right ih _)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# 在不作除法的情况下加入唯一证书

一项可见检查可能接受多个证书。当一个单元的猜测数据与实际局部数据不同时，字典为该单元赋予零权重。因此每个真实项恰好出现一次。

**英文原文**

Adding a unique certificate without division

The visible check can admit more than one certificate. The dictionary
assigns weight zero at a cell where its guessed data differ from the
actual local data. Consequently a genuine term occurs exactly once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Finset Transcript
open scoped Classical
variable {I J V C F : Type} [Fintype I] [Fintype J] [Fintype V] [Fintype C]

-- 读法：在后续公式中，`Candidate` 是 `Σ j, {c // ok j c}` 的缩写。
abbrev Candidate (ok : J → (V → C) → Prop) := Σ j, {c // ok j c}

variable (s : Selector I J) (actual : J → V → C) (ok : J → (V → C) → Prop)
    (valid : ∀ i, ok (s.write i) (actual (s.write i)))

-- 读法：`genuine` 的取值由 `⟨s.write i, actual (s.write i), valid i⟩` 给出。
def genuine (i : I) : Candidate ok := ⟨s.write i, actual (s.write i), valid i⟩

-- 读法：用字段 `write`、`read`、`valid`、`obtain` 构造 `Selector I (Candidate ok)`。
def checkedSelector : Selector I (Candidate ok) where
  write := genuine s actual ok valid
  read v := if v.2.val = actual v.1 then s.read v.1 else none
  valid v i := by
    obtain ⟨j, c, h⟩ := v
    constructor
    · split_ifs with he
      · intro h'
        change c = actual j at he
        have eq : j = s.write i := (s.valid _ _).mp h'
        subst j c
        rfl
      · simp
    · intro eq
      have hj := congrArg Sigma.fst eq
      have hc := congrArg (fun x : Candidate ok => x.2.val) eq
      change j = s.write i at hj
      change c = actual (s.write i) at hc
      subst j c
      exact (ite_eq_left rfl).trans ((s.valid _ i).mpr rfl)

variable [CommSemiring F] (weight : J → V → F) (coeff : I → F)
    (hw : ∀ j, ∏ v, weight j v = (s.read j).elim 0 coeff)

-- 读法：当 `x.2.val v = actual x.1 v` 成立时取 `weight x.1 v`，否则取 `0`。
def factor (x : Candidate ok) (v : V) := if x.2.val v = actual x.1 v then weight x.1 v else 0

omit [Fintype I] [Fintype J] [Fintype C] in
include hw in
-- 读法：`(∏ v, factor actual ok weight x v)` 等于 `((checkedSelector s actual ok valid).read x).elim 0 coeff`。按 `x.2.val = actual x.1` 成立与否分情况。
theorem checked_weight (x : Candidate ok) :
    (∏ v, factor actual ok weight x v) = ((checkedSelector s actual ok valid).read x).elim 0 coeff := by
  by_cases he : x.2.val = actual x.1
  · simp only [factor, checkedSelector, he, ↓reduceIte, hw]
  · simp only [checkedSelector, ite_eq_right he, Option.elim_none]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

include hw in
-- 读法：结论为 `∑ x : Candidate ok, (∏ v, factor actual ok weight x v) * eval x = ∑ i, coeff i * src i`。这里调用 `sum_congr`。
theorem checked_sum (eval : Candidate ok → F) (src : I → F)
    (he : ∀ i, eval (genuine s actual ok valid i) = src i) :
    ∑ x : Candidate ok, (∏ v, factor actual ok weight x v) * eval x = ∑ i, coeff i * src i := by
  let t := checkedSelector s actual ok valid
  rw [←t.sum (fun i => coeff i * src i)]
  apply sum_congr rfl
  intro x _
  rw [checked_weight s actual ok valid weight coeff hw x]
  change (t.read x).elim 0 coeff * eval x = _
  cases h : t.read x with
  | none => simp
  | some i =>
    have hx : x = genuine s actual ok valid i := (t.valid x i).mp h
    rw [hx, he]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# 逐单元记录能量和移动开销所用的有界整数

**英文原文**

Bounded integers for the per-cell energy and motion accounts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset SphereScale Routing.Private
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F]
    {x y : Wire} {h D T b d g ℓ m : ℕ} {W ε : ℝ} (P : Input F x y h D T (d * b) g W)
    (p : P.Kits K m (probes ℓ D) ε) (s : P.Occupied → Shape (probes ℓ D) b d)
    (sc : Scales g ℓ D T m b d)
    {z : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam (P.Parameters p)}
    (hz : (P.plant p s).Reach m (2 * g) (SphereScale.energy ℓ D (d * b)) (D ^ 5) z)

local notation "H" => SphereScale.energy ℓ D (d * b)
local notation "N" => depth ℓ D g m (d * b)
local notation "M" => room ℓ D g

include sc hz in
-- 读法：`z.energyCre m H (2 * g) v + (∑ e ∈ z.edges v, (z.ledger m H).seam e)` 不超过 `N`。
theorem credit_site (v : P.Occupied) :
    z.energyCre m H (2 * g) v + (∑ e ∈ z.edges v, (z.ledger m H).seam e) ≤ N := by
  have h := hz.budget.site v
  have hi := (mul_le_mul_of_nonneg_left (P.plant_local_energy p s sc.Rpos H v)
    (Nat.cast_nonneg (1 + 4 * g))).trans sc.initial_bound
  let I := (P.plant p s).ledger m H
  have ht : (1 + 4 * g) * (I.mobile v + I.collected v + ∑ e ∈ (P.plant p s).edges v, I.seam e) ≤ N :=
    (Nat.cast_le (α := ℝ)).mp (by rw [Nat.cast_mul]; exact hi)
  have aux (a b c k : ℕ) : (1 + k) * a + b + (1 + k) * c ≤ (1 + k) * (a + b + c) := by ring_nf; omega
  rw [show 4 * g = 2 * (2 * g) by omega] at ht
  rw [hz.edges_eq]
  exact (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega : 0 < 1 + 2 * (2 * g))) _).trans
    (h.trans ((aux ..).trans ht))

include sc hz in
-- 读法：`(∑ e ∈ z.edges v, (z.ledger m H).seam e / (2 * m * H))` 不超过 `budget g * D ^ 2`。这里调用 `Nat.le_of_mul_le_mul_right`。
theorem seam_credit (v : P.Occupied) :
    (∑ e ∈ z.edges v, (z.ledger m H).seam e / (2 * m * H)) ≤ budget g * D ^ 2 := by
  have hm := sc.pos
  have hH := sc.Hpos
  apply Nat.le_of_mul_le_mul_right _ (by positivity : 0 < 2 * m * H)
  rw [sum_mul]
  refine (sum_le_sum (fun i _ => Nat.div_mul_le_self ..)).trans ?_
  have h := P.credit_site p s sc hz v
  refine (Nat.le_add_left ..).trans (h.trans ?_)
  unfold depth
  rw [mul_assoc (budget g * D ^ 2)]
  gcongr
  omega

-- 读法：`(ls.map f).sum` 不超过 `ls.length * b`。对 `ls` 作归纳。
private theorem tally_limit {α : Type} (ls : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ v ∈ ls, f v ≤ b) : (ls.map f).sum ≤ ls.length * b := by
  induction ls with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (h _ (by simp)) (ih (by intro v hv; exact h v (.tail _ hv)))).trans_eq (add_comm ..)

-- 读法：`energyLimit` 的取值由 `(n + 1) * (budget g * D ^ 2)` 给出。
def energyLimit (g D n : ℕ) := (n + 1) * (budget g * D ^ 2)
-- 读法：`timeLimit` 的取值由 `2 * room ℓ D g * D ^ 5 + budget g * D ^ 2` 给出。
def timeLimit (g ℓ D : ℕ) := 2 * room ℓ D g * D ^ 5 + budget g * D ^ 2

include sc hz in
-- 读法：`Geometry.clip n (m * H) (z.energyCre m H (2 * g) v) ≤ energyLimit g D n` 与 `z.timeCre m H (D ^ 5) v ≤ timeLimit g ℓ D` 同时成立。这里调用 `Nat.le_add_right`。
theorem credit_limits (hv : z.Valid (D ^ 5)) (n : ℕ) (v : P.Occupied) :
    Geometry.clip n (m * H) (z.energyCre m H (2 * g) v) ≤ energyLimit g D n ∧
      z.timeCre m H (D ^ 5) v ≤ timeLimit g ℓ D := by
  have he := P.credit_site p s sc hz v
  have hlen := (P.moved_room p s sc hz).length v
  refine ⟨Geometry.clip_bound _ _ _ _ (Nat.mul_pos sc.pos sc.Hpos) ?_, ?_⟩
  · rw [←mul_assoc]
    exact (Nat.le_add_right ..).trans he
  · have ht : z.tally m (fun c _ => c.clock) v ≤ M * D ^ 5 :=
      (tally_limit _ _ _ (hv.bound v)).trans (Nat.mul_le_mul_right _ hlen)
    have hc : z.tally m Stage.collectorUnit v ≤ M := by
      have h : ∀ a : Role, a.collected 1 ≤ 1 := by intro a; cases a <;> simp [Role.collected]
      exact (tally_limit _ _ 1 (fun i _ => h i.label.role)).trans ((mul_one _).le.trans hlen)
    unfold Stage.timeCre timeLimit
    rw [two_mul M, add_mul M M, mul_comm (D ^ 5)]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hc) ht) (P.seam_credit p s sc hz v)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# 对候选布局作整数检验

谱论证给出真实分支，其权重可能很复杂。以下结构检查只读取大小有界的整数数据，精度由步数确定。

**英文原文**

Integer checks for a proposed layout

The spectrum argument supplies true branches with potentially
complicated weights. The structural checks below take only integer
data of bounded size. The number of steps sets the precision.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Rounds Finset
open scoped Classical
variable {V : Type} [Fintype V] {g ℓ D n : ℕ}

-- 读法：在后续公式中，`Credits` 是 `Fin (n + 1) → Fin (Input.energyLimit g D n + 1) × Fin (Input.timeLimit g ℓ D + 1)` 的缩写。
abbrev Credits (g ℓ D n : ℕ) :=
  Fin (n + 1) → Fin (Input.energyLimit g D n + 1) × Fin (Input.timeLimit g ℓ D + 1)

namespace Credits

-- 读法：`power` 的取值由 `(z i).1.val` 给出。
def power (z : Credits g ℓ D n) (i : Fin (n + 1)) := (z i).1.val
-- 读法：`time` 的取值由 `(z i).2.val` 给出。
def time (z : Credits g ℓ D n) (i : Fin (n + 1)) := (z i).2.val

-- 读法：输入 `i` 时返回 `(Fin.ofNat _ (clip n unit (a i)), Fin.ofNat _ (b i))`。
/-- 规范选取方式。越界值按字母表大小取模解释，这只在展开的支持集之外产生影响。

英文原文：The canonical choice. A value out of range is interpreted modulo
the alphabet size, which matters only off the support of an expansion.
-/
def issue (g ℓ D n : ℕ) (unit : ℕ) (a b : Fin (n + 1) → ℕ) : Credits g ℓ D n := fun i =>
  (Fin.ofNat _ (clip n unit (a i)), Fin.ofNat _ (b i))

-- 读法：`(issue g ℓ D n unit a b).power i` 等于 `clip n unit (a i)`。使用 `Nat.mod_eq_of_lt` 给出的结论。
theorem issue_power (unit : ℕ) (a b : Fin (n + 1) → ℕ) (i : Fin (n + 1))
    (h : clip n unit (a i) ≤ Input.energyLimit g D n) :
    (issue g ℓ D n unit a b).power i = clip n unit (a i) := Nat.mod_eq_of_lt (Nat.lt_succ_of_le h)

-- 读法：`(issue g ℓ D n unit a b).time i` 等于 `b i`。使用 `Nat.mod_eq_of_lt` 给出的结论。
theorem issue_time (unit : ℕ) (a b : Fin (n + 1) → ℕ) (i : Fin (n + 1))
    (h : b i ≤ Input.timeLimit g ℓ D) :
    (issue g ℓ D n unit a b).time i = b i := Nat.mod_eq_of_lt (Nat.lt_succ_of_le h)

-- 读法：结构的字段包括 `initial`、`power`、`time`。
structure Check (p : Fin n → V → V) (z : V → Credits g ℓ D n) (E M : V → ℕ) : Prop where
  initial : ∀ v, (z v).power 0 ≤ E v ∧ (z v).time 0 ≤ M v
  power : Admitted p 1 (fun i v => (z v).power i)
  time : Admitted p 0 (fun i v => (z v).time i)

-- 读法：要证明的命题是 `Check p (fun v => issue g ℓ D n unit (a v) (b v)) E M`。
theorem check_issue {p : Fin n → V → V} {a b : V → Fin (n + 1) → ℕ} {E M : V → ℕ}
    (unit : ℕ) (hu : 0 < unit) (start : ∀ v, clip n unit (a v 0) ≤ E v ∧ b v 0 ≤ M v)
    (ha : Admitted p 0 fun i v => a v i) (hb : Admitted p 0 fun i v => b v i)
    (h : ∀ v i, clip n unit (a v i) ≤ Input.energyLimit g D n ∧ b v i ≤ Input.timeLimit g ℓ D) :
    Check p (fun v => issue g ℓ D n unit (a v) (b v)) E M := by
  have hx v i := issue_power (ℓ := ℓ) unit (a v) (b v) i (h v i).1
  have hy v i := issue_time unit (a v) (b v) i (h v i).2
  constructor
  · simpa only [hx, hy] using start
  · simp only [hx]
    exact fun i => (ha i).clip n hu
  · simpa only [hy] using hb

-- 读法：`(∑ v, (z v).power (Fin.last n))` 不超过 `(∑ v, E v) + n * Fintype.card V ∧ (∑ v, (z v).time (Fin.last n)) ≤ ∑ v, M v`。
theorem Check.final {p : Fin n → V → V} {z : V → Credits g ℓ D n} {E M : V → ℕ}
    (h : Check p z E M) :
    (∑ v, (z v).power (Fin.last n)) ≤ (∑ v, E v) + n * Fintype.card V ∧
      (∑ v, (z v).time (Fin.last n)) ≤ ∑ v, M v := by
  have ha := h.power.total
  have hb := h.time.total
  simp only [mul_one, mul_zero, add_zero] at ha hb
  exact ⟨ha.trans (Nat.add_le_add_right (sum_le_sum fun i _ => (h.initial i).1) _),
    hb.trans (sum_le_sum fun i _ => (h.initial i).2)⟩

end Credits
end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# 由数据包大小和不可移动性计算初始额度

许可额度与选择器选取的形状无关。在全局估计中，站点可能具有的初始能量由其数据包宽度的平方承担，每个收集器的开销则计入其占用的单元。

**英文原文**

Initial credits computed from packet sizes and immobility

The allowance is independent of the shape chosen by a selector. The
global bounds charge the possible initial station energies to their
squared packet widths and each collector to its occupied cell.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface SphereScale Finset Routing.Private
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F]
    {x y : Wire} {h D T b d g ℓ m : ℕ} {W ε : ℝ}
    (P : Input F x y h D T (d * b) g W)

local notation "H" => SphereScale.energy ℓ D (d * b)
local notation "A" => SphereScale.size ℓ D

-- 读法：`packetEnergy` 的取值由 `∑ j : Fin (P.grid.stations v).card, (d * b) * (8 * P.grid.width v (Fin.castAdd _ j) ^ 2)` 给出。
private def packetEnergy (v : P.Occupied) :=
  ∑ j : Fin (P.grid.stations v).card, (d * b) * (8 * P.grid.width v (Fin.castAdd _ j) ^ 2)

-- 读法：`initialPacketCredit` 的取值由 `(1 + 4 * g) * (reserve D b d (probes ℓ D) m (SphereScale.energy ℓ D (d * b)) + m * P.packetEnergy v)` 给出。
private def initialPacketCredit (ℓ m : ℕ) (v : P.Occupied) :=
  (1 + 4 * g) * (reserve D b d (probes ℓ D) m (SphereScale.energy ℓ D (d * b)) + m * P.packetEnergy v)

-- 读法：`initialEnergyTokens` 的取值由 `Geometry.clip n (m * SphereScale.energy ℓ D (d * b)) (P.initialPacketCredit ℓ m v)` 给出。
def initialEnergyTokens (ℓ m n : ℕ) (v : P.Occupied) :=
  Geometry.clip n (m * SphereScale.energy ℓ D (d * b)) (P.initialPacketCredit ℓ m v)

-- 读法：`initialTimeTokens` 的取值由 `D ^ 5 * P.collectorCount v + budget g * D ^ 2` 给出。
def initialTimeTokens (v : P.Occupied) :=
  D ^ 5 * P.collectorCount v + budget g * D ^ 2

variable (p : P.Kits K m (probes ℓ D) ε) (s : P.Occupied → Shape (probes ℓ D) b d)
    (sc : Scales g ℓ D T m b d)

-- 读法：`Geometry.clip n (m * H) ((P.plant p s).energyCre m H (2 * g) v)` 不超过 `P.initialEnergyTokens ℓ m n v`。
theorem initial_energy_fits (n : ℕ) (v : P.Occupied) :
    Geometry.clip n (m * H) ((P.plant p s).energyCre m H (2 * g) v) ≤
      P.initialEnergyTokens ℓ m n v := by
  let z := (P.plant p s).ledger m H
  have hsum : z.mobile v + z.collected v ≤ reserve D b d (probes ℓ D) m H + m * P.packetEnergy v :=
    P.initial_sum p s H v
  have h : (P.plant p s).energyCre m H (2 * g) v ≤ P.initialPacketCredit ℓ m v := calc
    _ = (1 + 4 * g) * z.mobile v + z.collected v := by
      unfold Stage.energyCre Ledger.cost z
      ring_nf
    _ ≤ (1 + 4 * g) * (z.mobile v + z.collected v) := by
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
    _ ≤ _ := Nat.mul_le_mul_left _ hsum
  unfold initialEnergyTokens Geometry.clip
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

include sc in
-- 读法：`(P.plant p s).timeCre m H (D ^ 5) v` 不超过 `P.initialTimeTokens v`。这里调用 `Nat.eq_zero_of_le_zero`。
theorem initial_time_fits (v : P.Occupied) :
    (P.plant p s).timeCre m H (D ^ 5) v ≤ P.initialTimeTokens v := by
  let z := P.plant p s
  have hz : z.tally m (fun c _ => c.clock) v = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      _ ≤ (z.ledger m H).clock := single_le_sum (fun a _ => Nat.zero_le _) (mem_univ v)
      _ = 0 := P.plant_zero p s H
  have hs : (∑ e ∈ z.edges v, (z.ledger m H).seam e) ≤ budget g * D ^ 2 * m * H := by
    have h := P.plant_local_energy p s sc.Rpos H v
    have hr := sc.initial_bound
    have ha : ((∑ e ∈ z.edges v, (z.ledger m H).seam e : ℕ) : ℝ) ≤
        Input.initialEnergy D T b d (probes ℓ D) m H := by
      exact (Nat.cast_le.mpr (Nat.le_add_left ..)).trans h
    -- 推导：记下中间结论 `hb`：`(1 : ℝ) ≤ (1 + 4 * g : ℕ)`。
    have hb : (1 : ℝ) ≤ (1 + 4 * g : ℕ) := by exact_mod_cast (show 1 ≤ 1 + 4 * g by omega)
    have hb' := le_mul_of_one_le_left
      (show 0 ≤ Input.initialEnergy D T b d (probes ℓ D) m H by unfold Input.initialEnergy; positivity) hb
    exact_mod_cast ha.trans (hb'.trans hr)
  have hm : 0 < m * H := Nat.mul_pos sc.pos sc.Hpos
  have he : (∑ e ∈ z.edges v, (z.ledger m H).seam e / (2 * m * H)) ≤ budget g * D ^ 2 := by
    apply Nat.le_of_mul_le_mul_right _ hm
    rw [sum_mul]
    have aux (e : P.grid.Seam) :
        (z.ledger m H).seam e / (2 * m * H) * (m * H) ≤ (z.ledger m H).seam e :=
      (Nat.mul_le_mul_left _ (by rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by decide))).trans
        (Nat.div_mul_le_self ..)
    exact (sum_le_sum fun e _ => aux e).trans (hs.trans_eq (mul_assoc ..))
  unfold Stage.timeCre initialTimeTokens
  change D ^ 5 * z.tally m (fun c _ => c.collected 1) v + z.tally m (fun c _ => c.clock) v +
    (∑ e ∈ z.edges v, (z.ledger m H).seam e / (2 * m * H)) ≤ _
  rw [P.plant_collector_cell p s m, hz, add_zero]
  exact Nat.add_le_add_left he _

include sc in
omit [Field F] in
-- 读法：`((∑ v, P.initialEnergyTokens ℓ m n v : ℕ) : ℝ) * T` 不超过 `2 * budget g * ((n : ℝ) + 1) * W`。这里调用 `P.occupied`。
theorem initial_energy_total (n : ℕ) :
    ((∑ v, P.initialEnergyTokens ℓ m n v : ℕ) : ℝ) * T ≤ 2 * budget g * ((n : ℝ) + 1) * W := by
  let E := P.initialEnergyTokens ℓ m n
  let raw := P.initialPacketCredit ℓ m
  have hn : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    simpa only [Occupied, Fintype.card_coe] using P.occupied
  have hW := (by positivity : (0 : ℝ) ≤ (Fintype.card P.Occupied : ℝ) * D * T).trans hn
  have hsum : (∑ v, raw v) =
      (1 + 4 * g) * (Fintype.card P.Occupied * reserve D b d (probes ℓ D) m H + m*∑ v, P.packetEnergy v) := by
    simp only [raw, initialPacketCredit, ←mul_sum, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul]
  -- 推导：记下中间结论 `hraw`：`((∑ v, raw v : ℕ) : ℝ) ≤ budget g * (m : ℝ) * A * W`。
  have hraw : ((∑ v, raw v : ℕ) : ℝ) ≤ budget g * (m : ℝ) * A * W := calc
    _ = ((1 + 4 * g : ℕ) : ℝ) * ((Fintype.card P.Occupied : ℝ) * reserve D b d (probes ℓ D) m H +
        (m : ℝ) * (∑ v, (P.packetEnergy v : ℝ))) := by rw [hsum]; push_cast; ring
    _ ≤ ((1 + 4 * g : ℕ) : ℝ) * ((Fintype.card P.Occupied : ℝ) * reserve D b d (probes ℓ D) m H +
        (m : ℝ) * (8 * W * T / (d * b : ℕ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [packetEnergy, Nat.cast_sum] using P.station_energy sc.Rpos
    _ ≤ _ := sc.global_bound _ W hn
  -- 推导：记下中间结论 `round`：`(∑ v, E v) * (m * H) ≤ (n + 1) * (∑ v, raw v)`。
  have round : (∑ v, E v) * (m * H) ≤ (n + 1) * (∑ v, raw v) := by
    rw [sum_mul, mul_sum]
    exact sum_le_sum fun v _ => Nat.div_mul_le_self ..
  have hdv : ((∑ v, E v : ℕ) : ℝ) * ((m : ℝ) * H) ≤ ((n : ℝ) + 1) * ((∑ v, raw v : ℕ) : ℝ) := by
    exact_mod_cast round
  have hclip := hdv.trans (mul_le_mul_of_nonneg_left hraw (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity))
  have ht : (A : ℝ) * T ≤ 2 * (H : ℝ) := calc
    _ ≤ (A : ℝ) * (2 * (d * b * A) : ℕ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr sc.upper) (by positivity)
    _ = _ := by unfold SphereScale.energy; push_cast; ring
  apply le_of_mul_le_mul_right _ (mul_pos (Nat.cast_pos.mpr sc.pos) (Nat.cast_pos.mpr sc.Hpos))
  calc
    _ = (((∑ v, E v : ℕ) : ℝ) * ((m : ℝ) * H)) * T := by ring
    _ ≤ (((n : ℝ) + 1) * (budget g * (m : ℝ) * A * W)) * T :=
      mul_le_mul_of_nonneg_right hclip (by positivity)
    _ = (budget g * ((n : ℝ) + 1) * W * (m : ℝ)) * ((A : ℝ) * T) := by ring
    _ ≤ (budget g * ((n : ℝ) + 1) * W * (m : ℝ)) * (2 * H) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

include p s sc in
-- 读法：`((∑ v, P.initialTimeTokens v : ℕ) : ℝ) * D * T` 不超过 `3 * (D : ℝ) ^ 5 * W`。这里调用 `P.occupied`。
theorem initial_time_total :
    ((∑ v, P.initialTimeTokens v : ℕ) : ℝ) * D * T ≤ 3 * (D : ℝ) ^ 5 * W := by
  have ht : budget g * D ^ 2 ≤ D ^ 5 := calc
    _ ≤ D * D ^ 2 := Nat.mul_le_mul_right _ (by have := sc.large; omega)
    _ = D ^ 3 := (pow_succ' D 2).symm
    _ ≤ _ := Nat.pow_le_pow_right sc.Dpos (by decide)
  have hn : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    simpa only [Occupied, Fintype.card_coe] using P.occupied
  have hc : (∑ v, P.collectorCount v) = (P.plant p s).collectors := by
    unfold Stage.collectors
    apply sum_congr rfl
    intro v _
    exact (P.plant_collector_cell p s 0 v).symm
  have htotal : (∑ v, P.initialTimeTokens v) ≤
      D ^ 5 * (2 * Fintype.card P.Occupied + Fintype.card {v // ¬P.mobile v}) := calc
    _ ≤ ∑ v : P.Occupied, (D ^ 5 * P.collectorCount v + D ^ 5) := by
      unfold initialTimeTokens
      exact sum_le_sum fun v _ => Nat.add_le_add_left ht _
    _ = _ := by
      rw [sum_add_distrib, ←mul_sum, hc, P.plant_collectors]
      simp only [sum_const, card_univ, Nat.nsmul_eq_mul]
      ring
  calc
    _ ≤ ((D ^ 5 * (2 * Fintype.card P.Occupied + Fintype.card {v // ¬P.mobile v}) : ℕ) : ℝ) * D * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr htotal) (by positivity)) (by positivity)
    _ = (D : ℝ) ^ 5 * (2 * ((Fintype.card P.Occupied : ℝ) * D * T)+
        (Fintype.card {v // ¬P.mobile v} : ℝ) * D * T) := by push_cast; ring
    _ ≤ (D : ℝ) ^ 5 * (2 * W + W) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hn (by norm_num)) P.immobile) (by positivity)
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# 输出元数的有限局部检验

内部区段的长度都是同一单位的整数倍。整数阈值等于尺度除以该单位后向下取整，随着尺度增大仍有统一上界。外部长度原样传递。

**英文原文**

A finite local check for output arities

Internal span lengths are multiples of a common unit. The integer
threshold is the scale divided by this unit, rounded down. It stays
bounded when the scale grows. Exterior lengths pass through unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Rounds Coloring Finset
open scoped Classical

variable {g ℓ D n w d e k : ℕ}

-- 读法：结构的字段包括 `count`、`square`、`mobile`、`large`、`small`。
structure Quota (C h K : ℕ) (fixed : B w → Bool) (a : Blueprint w d e k) (c : Credits g ℓ D n) : Prop where
  count : D ^ 5 * a.count fixed ≤ c.time (Fin.last n)
  square : (n + 1) * a.square fixed ≤ 512 * (D * (n + 1) + c.power (Fin.last n) + 1) * K ^ 2
  mobile : a.mobile fixed ≤ 2 * C * (1 + a.count fixed) * D * (1 + h) ^ 2 * K
  large : ∀ i, fixed i = true → (a i).toll ≤ 2 * C * D * K
  small : ∀ i, fixed i = false → (a i).toll * D ^ ℓ ≤ K

-- 读法：`T` 不超过 `2 * (T / u) * u`。这里调用 `he.le.trans`。
private theorem scale_le (u T : ℕ) (hu : 0 < u) (h : u ≤ T) : T ≤ 2 * (T / u) * u := by
  have pos : 0 < T / u := Nat.div_pos h hu
  have he := Nat.lt_mul_div_succ T hu
  exact he.le.trans ((Nat.mul_le_mul_left u (show T / u + 1 ≤ 2 * (T / u) by omega)).trans_eq (mul_comm ..))

-- 读法：`(n + 1) * R` 不超过 `512 * (D * (n + 1) + y + 1) * K ^ 2`。这里调用 `le_of_mul_le_mul_right`。
private theorem square_high (R f u K T n D y E : ℝ)
    (hf : 0 < f) (hT : 0 ≤ T) (hu : 0 < u) (hn : 0 ≤ n) (hD : 0 ≤ D) (hy : 0 ≤ y)
    (hK : T ≤ 2 * K * u) (he : (n + 1) * E ≤ (y + 1) * (f * T))
    (hs : R * u ^ 2 ≤ 128 * (T * E / f + D * T ^ 2)) :
    (n + 1) * R ≤ 512 * (D * (n + 1) + y + 1) * K ^ 2 := by
  have ha : (n + 1) * (T * E / f) ≤ (y + 1) * T ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hf]
    convert mul_le_mul_of_nonneg_left he hT using 1 <;> ring
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hu)
  calc
    _ ≤ (n + 1) * (128 * (T * E / f + D * T ^ 2)) := by rw [mul_assoc]; gcongr
    _ ≤ 128 * (D * (n + 1) + y + 1) * T ^ 2 := by linarith only [ha]
    _ ≤ 128 * (D * (n + 1) + y + 1) * (2 * K * u) ^ 2 := by gcongr
    _ = _ := by ring

-- 读法：要证明的命题是 `Quota C h (T / u) fixed a c`。这里调用 `Nat.mul_le_mul_left`。
theorem Quota.make {T b l m u C h E : ℕ} (sc : SphereScale.Scales g ℓ D T m b l)
    (fixed : B w → Bool) (a : Blueprint w d e k) (c : Credits g ℓ D n)
    (hu : 0 < u) (ht : u ≤ T) (hE : clip n (m * SphereScale.energy ℓ D (l * b)) E ≤ c.power (Fin.last n))
    (count : D ^ 5 * a.count fixed ≤ c.time (Fin.last n))
    (square : (a.square fixed : ℝ) * u ^ 2 ≤ 128 * ((T : ℝ) * E / ((m : ℝ) * SphereScale.size ℓ D) + D * (T : ℝ) ^ 2))
    (mobile : a.mobile fixed * u ≤ C * (1 + a.count fixed) * D * T * (1 + h) ^ 2)
    (large : ∀ i, fixed i = true → (a i).toll * u ≤ C * D * T)
    (small : ∀ i, fixed i = false → (a i).toll * u * D ^ ℓ ≤ T) :
    Quota C h (T / u) fixed a c := by
  let K := T / u
  -- 推导：记下中间结论 `hh`：`T ≤ 2 * K * u`。
  have hh : T ≤ 2 * K * u := scale_le u T hu ht
  have he : (n + 1) * E ≤ (c.power (Fin.last n) + 1) * ((m * SphereScale.size ℓ D) * T) := by
    refine (clip_high n E (Nat.mul_pos sc.pos sc.Hpos)).trans (Nat.mul_le_mul (Nat.succ_le_succ hE) ?_)
    rw [mul_assoc, mul_comm (SphereScale.size ℓ D)]
    exact Nat.mul_le_mul_left _ sc.smallH
  refine ⟨count, ?_, ?_, ?_, ?_⟩
  · have hf : 0 < (m : ℝ) * SphereScale.size ℓ D := mul_pos (Nat.cast_pos.mpr sc.pos) (Nat.cast_pos.mpr sc.apos)
    change (n + 1) * a.square fixed ≤ 512 * (D * (n + 1) + c.power (Fin.last n) + 1) * K ^ 2
    exact_mod_cast square_high (a.square fixed) _ u K T n D (c.power (Fin.last n)) E
      hf (by positivity) (Nat.cast_pos.mpr hu) (by positivity) (by positivity) (by positivity)
      (by exact_mod_cast hh) (by exact_mod_cast he) square
  · apply Nat.le_of_mul_le_mul_right _ hu
    exact mobile.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh)).trans_eq (by unfold K; ring))
  · intro i hi
    apply Nat.le_of_mul_le_mul_right _ hu
    exact (large i hi).trans ((Nat.mul_le_mul_left _ hh).trans_eq (by unfold K; ring))
  · intro i hi
    rw [Nat.le_div_iff_mul_le hu, mul_right_comm]
    exact small i hi

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# 对独立提出的布局中的活动位置计费

**英文原文**

Charging active positions of an independently proposed layout
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Rounds Coloring Packing
open scoped Classical
variable {F : Type} {x y : Wire} {h w d e k u : ℕ}

-- 读法：结构的字段包括 `addr`、`live`、`frozen`、`charge`。
structure Support (V : Type) (a : V → Blueprint w d e k) (fixed : V → B w → Bool)
    (Q : LocalTerm F x y h u) where
  addr : Q.diagram.V ↪ V × B w
  live : ∀ i, (a (addr i).1 (addr i).2).live = true
  frozen : ∀ i, Q.freeze.frozen i ↔ fixed (addr i).1 (addr i).2 = true
  charge : ∀ i, Q.charge i = ((a (addr i).1 (addr i).2).toll : ℝ) * u +
    Fintype.card {q // portEnd Q.diagram q = i}

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# 将计数与内部元数推至候选槽位

**英文原文**

Pushing the counts and internal arities to the proposed slots
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Support
open Rounds Coloring Packing Finset
open scoped Classical

-- 读法：`(∑ i, g (f i))` 不超过 `∑ j, g j`。这里调用 `sum_le_sum_of_subset_of_nonneg`。
private theorem sum_injection {A B : Type} [Fintype A] [Fintype B]
    (f : A ↪ B) (g : B → ℝ) (h : ∀ i, 0 ≤ g i) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  rw [← sum_map univ f g]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => h i)

variable {F V : Type} [Fintype V] {x y : Wire} {h w d e k u : ℕ}
  {a : V → Blueprint w d e k} {fixed : V → B w → Bool} {Q : LocalTerm F x y h u}
  (H : Support V a fixed Q)

-- 读法：在后续公式中，`cellTag` 是 `a (H.addr v).1 (H.addr v).2` 的缩写。
abbrev cellTag (v : Q.diagram.V) := a (H.addr v).1 (H.addr v).2

-- 读法：`(∑ i : {v // p v}, f (H.cellTag i.val))` 不超过 `∑ v, ∑ j, if fixed v j = b then f (a v j) else 0`。
private theorem lift (p : Q.diagram.V → Prop) [DecidablePred p] (b : Bool)
    (h : ∀ i, p i → fixed (H.addr i).1 (H.addr i).2 = b)
    (f : Outline d e k → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : {v // p v}, f (H.cellTag i.val)) ≤
      ∑ v, ∑ j, if fixed v j = b then f (a v j) else 0 := by
  let e := (Function.Embedding.subtype p).trans H.addr
  let r (i : V × B w) := if fixed i.1 i.2 = b then f (a i.1 i.2) else 0
  have h' (i : {v // p v}) : r (e i) = f (H.cellTag i.val) := ite_eq_left (h _ i.property)
  have ht := sum_injection e r (fun i => by unfold r; split; exact hf _; exact le_rfl)
  simp only [h', Fintype.sum_prod_type] at ht
  exact ht

include H in
-- 读法：`(Fintype.card Q.freeze.Fixed : ℝ)` 不超过 `∑ v, ((a v).count (fixed v) : ℝ)`。这里调用 `sum_congr`。
theorem count : (Fintype.card Q.freeze.Fixed : ℝ) ≤ ∑ v, ((a v).count (fixed v) : ℝ) := by
  have h := H.lift Q.freeze.frozen true (fun i => (H.frozen i).mp)
    (fun i => if i.live then 1 else 0) (by intro i; positivity)
  have ha (i : Q.freeze.Fixed) : (H.cellTag i.val).live = true := H.live _
  simp only [ha, ite_true, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  refine h.trans_eq (sum_congr rfl fun v _ => ?_)
  unfold Blueprint.count
  rw [card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro j _
  cases (a v j).live <;> cases fixed v j <;> simp

-- 读法：`(∑ i : Q.freeze.Fixed, ((H.cellTag i.val).toll : ℝ) ^ 2)` 不超过 `∑ v, ((a v).square (fixed v) : ℝ)`。
theorem square : (∑ i : Q.freeze.Fixed, ((H.cellTag i.val).toll : ℝ) ^ 2) ≤
    ∑ v, ((a v).square (fixed v) : ℝ) := by
  have h := H.lift Q.freeze.frozen true (fun i => (H.frozen i).mp)
    (fun i => (i.toll : ℝ) ^ 2) (fun _ => sq_nonneg _)
  simpa only [Blueprint.square, Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_zero] using h

-- 读法：`(∑ i : Q.freeze.Core, ((H.cellTag i.val).toll : ℝ))` 不超过 `∑ v, ((a v).mobile (fixed v) : ℝ)`。这里调用 `sum_congr`。
theorem mobile : (∑ i : Q.freeze.Core, ((H.cellTag i.val).toll : ℝ)) ≤
    ∑ v, ((a v).mobile (fixed v) : ℝ) := by
  have h := H.lift (fun v => ¬ Q.freeze.frozen v) false
    (fun i hi => Bool.eq_false_iff.mpr (mt (H.frozen i).mpr hi))
    (fun i => (i.toll : ℝ)) (fun _ => Nat.cast_nonneg _)
  refine h.trans_eq (sum_congr rfl fun v _ => ?_)
  simp only [Blueprint.mobile, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  apply sum_congr rfl
  intro j _
  cases fixed v j <;> simp

-- 读法：`(∑ i : Q.freeze.Fixed, f i.val ^ 2)` 不超过 `∑ i, f i ^ 2`。使用 `sum_injection` 给出的结论。
theorem partial_square (f : Q.diagram.V → ℝ) :
    (∑ i : Q.freeze.Fixed, f i.val ^ 2) ≤ ∑ i, f i ^ 2 :=
  sum_injection (Function.Embedding.subtype _) (fun i => f i ^ 2) (fun _ => sq_nonneg _)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Support
end

/-!
# 每个几何上允许的分支都有界计费量

这些估计既不使用站点的权重，也不使用其隐藏选择器。因此，即使分支并非真实分支，只要其几何形状有效，哪怕权重为零也具有规定的元数。

**英文原文**

Every geometrically admitted branch has bounded charges

These estimates use neither the weight nor the hidden selector of a
station. Thus even a spurious but geometrically valid branch with
weight zero has the required arities.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Coloring Finset Rounds
open scoped Classical
variable {V : Type} [Fintype V] {g ℓ D n w d e k C h T u : ℕ} {W : ℝ}

-- 读法：`s * u ^ 2` 不超过 `512 * (2 * b + 2) * W * T`。这里调用 `mul_le_mul_of_nonneg_right`。
private theorem square_sum (T u W D b n K x y s r : ℝ)
    (ht : 0 ≤ T) (hu : 0 ≤ u) (hn : 0 ≤ n) (hd : 1 ≤ D) (hk : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hT : K * u ≤ T)
    (hocc : x * D * T ≤ W) (hp : r * T ≤ 2 * b * (n + 1) * W) (hterm : y ≤ r + n * x)
    (hc : (n + 1) * s ≤ 512 * (x * (D * (n + 1)) + y + x) * K ^ 2) :
    s * u ^ 2 ≤ 512 * (2 * b + 2) * W * T := by
  have hsimple : x * T ≤ W := by
    simpa using (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hx) ht).trans hocc
  have hs : (x * (D * (n + 1)) + y + x) * T ≤ (n + 1) * (2 * b + 2) * W := by
    linarith only [mul_le_mul_of_nonneg_right hterm ht, hp,
      mul_le_mul_of_nonneg_left hocc (show 0 ≤ n + 1 by linarith),
      mul_le_mul_of_nonneg_left hsimple (show 0 ≤ n + 1 by linarith)]
  apply le_of_mul_le_mul_left _ (by linarith : 0 < n + 1)
  calc
    _ ≤ 512 * (x * (D * (n + 1)) + y + x) * (K * u) ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg u)]
    _ ≤ 512 * (x * (D * (n + 1)) + y + x) * T ^ 2 := by gcongr
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hs ht]

-- 读法：`x * D * T` 不超过 `3 * W`。这里调用 `le_of_mul_le_mul_left`。
private theorem count_sum (x y t D T W : ℝ) (hD : 0 < D) (hT : 0 ≤ T)
    (h : D ^ 5 * x ≤ y) (ht : y ≤ t) (hw : t * D * T ≤ 3 * D ^ 5 * W) : x * D * T ≤ 3 * W := by
  apply le_of_mul_le_mul_left _ (pow_pos hD 5)
  linarith only [mul_le_mul_of_nonneg_right (h.trans ht) (mul_nonneg hD.le hT), hw]

-- 读法：`m * u` 不超过 `8 * c * W * (1 + n) ^ 2`。这里调用 `mul_le_mul_of_nonneg_left`。
private theorem mobile_sum (m u c n k x y D T W : ℝ) (hD : 0 ≤ D) (hu : 0 ≤ u)
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : k * u ≤ T)
    (h₁ : x * D * T ≤ W) (h₂ : y * D * T ≤ 3 * W) (h₃ : m ≤ 2 * c * (x + y) * D * (1 + n) ^ 2 * k) :
    m * u ≤ 8 * c * W * (1 + n) ^ 2 := calc
  _ ≤ 2 * c * (x + y) * D * (1 + n) ^ 2 * k * u := mul_le_mul_of_nonneg_right h₃ hu
  _ = 2 * c * (1 + n) ^ 2 * ((x + y) * D * (k * u)) := by ring
  _ ≤ 2 * c * (1 + n) ^ 2 * ((x + y) * D * T) := by gcongr
  _ ≤ 2 * c * (1 + n) ^ 2 * (4 * W) := by
    exact mul_le_mul_of_nonneg_left (by linarith only [h₁, h₂]) (by positivity)
  _ = _ := by ring

-- 读法：`squareConstant` 的取值由 `512 * (2 * SphereScale.budget g + 2)` 给出。
def squareConstant (g : ℕ) := 512 * (2 * SphereScale.budget g + 2)

variable (a : V → Blueprint w d e k) (fixed : V → B w → Bool)

-- 读法：结构的字段包括 `count`、`square`、`mobile`。
structure Totals (D T u C h g : ℕ) (W : ℝ) : Prop where
  count : (∑ v, ((a v).count (fixed v) : ℝ)) * D * T ≤ 3 * W
  square : (∑ v, ((a v).square (fixed v) : ℝ)) * u ^ 2 ≤ squareConstant g * W * T
  mobile : (∑ v, ((a v).mobile (fixed v) : ℝ)) * u ≤ 8 * C * W * (1 + (h : ℝ)) ^ 2

-- 读法：要证明的命题是 `Totals a fixed D T u C h g W`。
theorem totals {p : Fin n → V → V} {z : V → Credits g ℓ D n} {E M : V → ℕ}
    (hD : 0 < D) (hv : (Fintype.card V : ℝ) * D * T ≤ W)
    (hE : (∑ v, (E v : ℝ)) * T ≤ 2 * SphereScale.budget g * ((n : ℝ) + 1) * W)
    (hM : (∑ v, (M v : ℝ)) * D * T ≤ 3 * (D : ℝ) ^ 5 * W)
    (hcheck : Credits.Check p z E M) (hq : ∀ v, Quota C h (T / u) (fixed v) (a v) (z v)) :
    Totals a fixed D T u C h g W := by
  let K := T / u
  have ht : (K : ℝ) * u ≤ T := by exact_mod_cast Nat.div_mul_le_self T u
  let c v := (a v).count (fixed v)
  let s v := (a v).square (fixed v)
  let m v := (a v).mobile (fixed v)
  let t v := (z v).time (Fin.last n)
  let b v := (z v).power (Fin.last n)
  -- 推导：记下中间结论 `hx`：`D ^ 5 * (∑ v, c v) ≤ ∑ v, t v`。
  have hx : D ^ 5 * (∑ v, c v) ≤ ∑ v, t v := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => (hq i).count
  have hy : (n + 1) * (∑ v, s v) ≤ 512 * (Fintype.card V * (D * (n + 1)) + (∑ v, b v) + Fintype.card V) * K ^ 2 := by
    rw [←mul_assoc (Fintype.card V)]
    have hh := sum_le_sum fun v (_ : v ∈ univ) => (hq v).square
    simpa only [←sum_mul, ←mul_sum, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one] using hh
  have hm : (∑ v, m v) ≤ 2 * C * (Fintype.card V+∑ v, c v) * D * (1 + h) ^ 2 * K := by
    have hh := sum_le_sum fun v (_ : v ∈ univ) => (hq v).mobile
    simpa only [←sum_mul, ←mul_sum, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one] using hh
  -- 推导：记下中间结论 `hc`：`(∑ v, (c v : ℝ)) * D * T ≤ 3 * W`。
  have hc : (∑ v, (c v : ℝ)) * D * T ≤ 3 * W :=
    count_sum _ (∑ v, (t v : ℝ)) _ _ _ _ (Nat.cast_pos.mpr hD) (by positivity)
      (by exact_mod_cast hx) (by exact_mod_cast hcheck.final.2) hM
  refine ⟨hc, ?_, ?_⟩
  · unfold squareConstant
    push_cast
    apply square_sum T u W D _ n K (Fintype.card V) (∑ v, (b v : ℝ)) _ (∑ v, (E v : ℝ))
      (by positivity) (by positivity) (by positivity) (by exact_mod_cast hD) (by positivity)
      (by positivity) (by positivity) ht hv hE
    · exact_mod_cast hcheck.final.1
    · exact_mod_cast hy
  · apply mobile_sum _ _ _ _ K _ _ _ _ _ (Nat.cast_nonneg D) (by positivity)
      (by positivity) (by positivity) (by positivity) ht hv hc
    exact_mod_cast hm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end
