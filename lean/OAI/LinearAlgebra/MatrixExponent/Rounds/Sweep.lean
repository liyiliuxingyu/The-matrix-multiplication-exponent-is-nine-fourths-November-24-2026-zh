-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply

section
/-!
# 连接元数预算和表预算各异的阶段

**英文原文**

Joining stages with their own arity and table budgets
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Transforms

universe v
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {X Y Z : Snapshot.{v} F x y}
  {u w m n : ℕ} {L M : Finset (Table F)}

-- 读法：要证明的命题是 `Transforms F (max u w) (↑(L ∪ M) : Set (Table F)) X Z (m + n)`。这里调用 `f.widen`。
theorem comp_union (f : Transforms F u L X Y m) (g : Transforms F w M Y Z n) :
    Transforms F (max u w) (↑(L ∪ M) : Set (Table F)) X Z (m + n) := by
  classical
  exact (f.widen (Nat.le_max_left _ _) (fun t ht => Finset.mem_union_left _ ht)).comp
    (g.widen (Nat.le_max_right _ _) (fun t ht => Finset.mem_union_right _ ht))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Transforms
end

/-!
# 在任意整数尺度和线束下进行局部集中

**英文原文**

Local concentration with arbitrary integral scales and bundles
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter

-- 读法：这里调用 `tendsto_atTop.2`。
/-- 对实际的有序线束补零后应用集中步骤。调用时需给出元数为正的无自环图及其宿主，对原线束宽度没有整除要求。

英文原文：Apply concentration after zero-padding the actual ordered bundles.
The caller supplies a positive loopless diagram and its host, with no
condition on the divisibility of the old bundle widths.
-/
theorem LocalLaw.with_padding {k : Type} [Field k] {ℓ : ℕ}
    (law : LocalLaw k (ℓ + 1)) (g : ℕ) (hg : 0 < g) :
    ∃ C : ℕ, ∀ᶠ D : ℕ in atTop,
      ∃ (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
        ∀ᶠ T : ℕ in atTop, ∃ r u : ℕ, 0 < r ∧ r * D ^ 2 ≤ 2 * T ∧ 0 < u ∧ T ≤ u * D ^ (2 * C + 1) ∧
          ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
            A * (1 + 2 * T) ^ A ≤ Fintype.card K →
            ∀ (x y : Wire) (h R : ℕ) (W : ℝ) (P : Input K x y h D T R g W),
              LocalExpansion P u (202 * (2 * C)) (Nat.clog 2 D) ℓ (2 * A) := by
  obtain ⟨C, hC⟩ := law.arbitrary g hg
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (400 * (g + 1))] with D hD scope
  -- 推导：从 `hD` 中取出 `A, L, _, _, _, hT`。
  obtain ⟨A, L, _, _, _, hT⟩ := hD
  refine ⟨A, L, inferInstance, inferInstance, inferInstance, ?_⟩
  have twice : Tendsto (fun T : ℕ => 2 * T) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with T ht
    omega
  filter_upwards [twice.eventually hT] with T h
  obtain ⟨r, u, hr, hr', hu, hlo, run⟩ := h
  refine ⟨r, u, hr, hr', hu, (show T ≤ 2 * T by omega).trans hlo, ?_⟩
  intro K _ _ _ field x y h R W P
  exact LocalExpansion.of_packetize P hr scope hr'
    (run K inferInstance inferInstance inferInstance field x y h (101 * W)
      (P.packetize r hr scope hr'))

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 将计费站点装入终端求值器

**英文原文**

Fitting the charged stations into the terminal evaluator
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {Q : Layer F x y} {D T V t : ℕ} {L θ : ℝ}
  (i : Q.State)

local notation "S" => Q.template.scheme
local notation "r" => Prod.fst (Q.data i)
local notation "G" => Q.graph i
local notation "pr" => Template.Presents.pres (Q.presents i)

-- 读法：`Fintype.card ((S).LocalPin r ((pr).vertex v))` 等于 `(G).arity v`。
private theorem local_size (v : (G).V) :
    Fintype.card ((S).LocalPin r ((pr).vertex v)) = (G).arity v := by
  rw [← Fintype.card_congr ((pr).pin v)]
  simp only [Diagram.Port, Fintype.card_sum, card_slots, Diagram.arity]

-- 读法：`Terminal.Active S r ((pr).vertex v)` 与 `0 < (G).arity v` 等价。
private theorem active (v : (G).V) :
    Terminal.Active S r ((pr).vertex v) ↔ 0 < (G).arity v := by
  rw [Terminal.Active, ← Fintype.card_pos_iff, local_size]

-- 读法：`Fintype.card (Terminal.Live S r)` 等于 `Fintype.card {v : (G).V // 0 < (G).arity v}`。
private theorem live :
    Fintype.card (Terminal.Live S r) = Fintype.card {v : (G).V // 0 < (G).arity v} := by
  let f : {v : (G).V // 0 < (G).arity v} → Terminal.Live S r :=
    fun v => ⟨(pr).vertex v.val, (active i v.val).mpr v.property⟩
  symm
  refine Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · exact fun _ _ he => Subtype.ext ((pr).vertex.injective (Subtype.mk.inj he))
  · rintro ⟨v, ⟨j⟩⟩
    obtain ⟨w, hw⟩ := (pr).cover ((S).port r v j)
    change (pr).vertex w = v at hw
    subst v
    exact ⟨⟨w, (active i w).mp ⟨j⟩⟩, rfl⟩

-- 读法：要证明的命题是 `Terminal.Neutral S r`。按 `v ∈ Set.range (pr).vertex` 成立与否分情况。
theorem Neutral.terminal (h : Q.Neutral) : Terminal.Neutral S r := by
  intro v hn t
  by_cases hv : v ∈ Set.range (pr).vertex
  · obtain ⟨w, rfl⟩ := hv
    rw [(pr).sample]
    exact h i w (Nat.eq_zero_of_not_pos (mt (active i w).mpr hn)) _
  · exact (pr).vacant v hv t

-- 读法：`(Fintype.card (Terminal.Live S r) : ℝ) * (θ * T)` 不超过 `L`。
theorem Ready.live_bound (h : Q.Ready D T L θ) :
    (Fintype.card (Terminal.Live S r) : ℝ) * (θ * T) ≤ L := by
  rw [live]
  let f := (Q.board i).charge
  have nonneg (v : (G).V) : 0 ≤ f v := (by positivity : (0 : ℝ) ≤ (G).arity v) |>.trans ((Q.board i).cover v)
  let s := Finset.univ.filter (fun v : (G).V => 0 < (G).arity v)
  have he : Fintype.card {v : (G).V // 0 < (G).arity v} = s.card := Fintype.card_subtype _
  rw [he, ← nsmul_eq_mul, ← Finset.sum_const]
  calc
    _ ≤ ∑ v ∈ s, f v := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hp := (Finset.mem_filter.mp hv).2
      have hg := (Nat.cast_pos.mpr hp).trans_le ((Q.board i).cover v)
      exact ((h.2.2 i).2.2.2 v).2.resolve_left hg.ne'
    _ ≤ ∑ v, f v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => nonneg v)
    _ ≤ _ := (h.2.2 i).2.1

-- 读法：`(S).width r w` 不超过 `D * T`。按 `0 < (S).width r (v, j)` 成立与否分情况。
private theorem Ready.span_bound (h : Q.Ready D T L θ) (w : (S).Span) : (S).width r w ≤ D * T := by
  rcases w with ⟨v, j⟩
  by_cases hw : 0 < (S).width r (v, j)
  swap
  · exact (Nat.eq_zero_of_not_pos hw).le.trans (Nat.zero_le _)
  obtain ⟨a, ha⟩ := (pr).cover ⟨(v, j), ⟨0, hw⟩⟩
  change (pr).vertex a = v at ha
  subst v
  have hcard := local_size i a
  simp only [Scheme.LocalPin, Fintype.card_sigma, Fintype.card_fin] at hcard
  apply le_trans (b := (G).arity a)
  · rw [← hcard]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · have hp := ((Q.board i).cover a).trans ((h.2.2 i).2.2.2 a).1
    have ht : ((G).arity a : ℝ) ≤ (D : ℝ) * T := hp.trans (div_le_self (by positivity) (by norm_num))
    exact_mod_cast ht

-- 读法：`Terminal.Fits S (Q.data i).1 V t` 与 `Terminal.Neutral S (Q.data i).1` 同时成立。这里调用 `Nat.add_le_add_left`。
theorem Ready.terminal (h : Q.Ready D T L θ) (hθ : 0 < θ) (hT : 0 < T) (ht : D * T ≤ 2 ^ t)
    (cap : 2 ^ Q.template.scheme.m + ⌊L / (θ * T)⌋₊*2 ^ (Q.template.scheme.e + t) ≤ V)
    (i : Q.State) : Terminal.Fits S (Q.data i).1 V t ∧ Terminal.Neutral S (Q.data i).1 := by
  refine ⟨⟨fun w => (h.span_bound i w).trans ht, ?_⟩, h.2.1.terminal i⟩
  have hc := Nat.le_floor ((le_div_iff₀ (by positivity : 0 < θ * (T : ℝ))).mpr (h.live_bound i))
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _).trans cap

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# 对一系列编码轮次进行开销核算

每轮有自己的有限字典。这些字典的并足以供整个序列使用，网络成本为各轮成本之和。初始化和终端收缩另行计费。

**英文原文**

Accounting for a sequence of encoded rounds

Each round carries its own finite dictionary. Their union suffices for
the entire sequence, and the network cost is the sum of the round costs.
The initialization and terminal contraction are paid separately.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Finset
open scoped Classical

namespace Assembly.Transforms
universe v
variable {F : Type} [Field F] {x y : Wire}

-- 读法：要证明的命题是 `Transforms F cap (↑((range n).biUnion keys) : Set (Table F)) (X 0) (X n) (∑ i ∈ range n, cost i)`。对 `n` 作归纳。
/-- 复合一个非空序列，整段序列共用一个元数上限。复合时无需支付复制中间连线的成本。

英文原文：Compose a nonempty sequence, with one arity ceiling for the whole
sequence. No copy of the intermediate wires is charged at composition.
-/
theorem sequence (X : ℕ → Snapshot.{v} F x y) (keys : ℕ → Finset (Table F))
    (cost : ℕ → ℕ) {cap n : ℕ} (hn : 0 < n)
    (step : ∀ i < n, Transforms F cap (keys i) (X i) (X (i + 1)) (cost i)) :
    Transforms F cap (↑((range n).biUnion keys) : Set (Table F))
      (X 0) (X n) (∑ i ∈ range n, cost i) := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ, range_add_one, biUnion_insert]
    have last := (step n (by omega)).widen le_rfl
      (show (↑(keys n) : Set (Table F)) ⊆ ↑(keys n ∪ (range n).biUnion keys) from
        fun t ht => mem_union_left _ ht)
    by_cases hz : n = 0
    · subst n
      simpa using last
    · have first := (ih (Nat.pos_of_ne_zero hz) (fun i hi => step i (by omega))).widen le_rfl
        (show (↑((range n).biUnion keys) : Set (Table F)) ⊆ ↑(keys n ∪ (range n).biUnion keys) from
          fun t ht => mem_union_right _ ht)
      exact first.comp last

end Assembly.Transforms

namespace Rounds
variable {F : Type} [Field F] {x y : Wire}

-- 读法：证明中先建立 `stop`，即 `= finish.widen (v`。
/-- 在初始化与终端求值器之间实现各轮，保留原有精确张量幂，并把每个标签都计入成本。

英文原文：Install the rounds between initialization and the terminal evaluator,
keeping the original exact tensor power and accounting for every label.
-/
theorem Layer.install_sequence {k : Val x → Val y → F} {d cap j m : ℕ}
    (P : ℕ → Layer F (copies x d) (copies y d))
    (keys : ℕ → Finset (Table F)) (endKeys : Finset (Table F))
    (cost : ℕ → ℕ) (hj : 0 < j) (hu : 3 ≤ cap)
    (i : (P 0).State) (scalar : F)
    (exactPower : (fun a b => scalar * ((P 0).graph i).eval a b) = power k d)
    (step : ∀ l < j, Transforms F cap (keys l) (P l).snapshot (P (l + 1)).snapshot (cost l))
    (finish : Finishes F cap endKeys (P j).snapshot m) :
    ∃ I : Installation k d, I.u = cap ∧
      I.labels = (range j).biUnion keys ∪ endKeys ∧
      I.labels.card ≤ (∑ l ∈ range j, (keys l).card) + endKeys.card ∧
      I.cost ≤ 140 * ((P 0).snapshot.port.width + d * (wd x + wd y)) +
        (∑ l ∈ range j, cost l) + m + 1 := by
  classical
  let L := (range j).biUnion keys ∪ endKeys
  have run := (Transforms.sequence (fun l => (P l).snapshot) keys cost hj step).widen le_rfl
    (show (↑((range j).biUnion keys) : Set (Table F)) ⊆ ↑L from fun t ht => mem_union_left _ ht)
  -- 推导：记下中间结论 `stop`：`= finish.widen (v`。
  have stop := finish.widen (v := cap) (T := (↑L : Set (Table F))) le_rfl
    (fun t ht => mem_union_right _ ht)
  obtain ⟨I, hL, hU, hcost⟩ := (P 0).installation (P j) i scalar exactPower hu run stop
  refine ⟨I, hU, hL, ?_, hcost⟩
  rw [hL]
  exact (card_union_le _ _).trans (Nat.add_le_add_right card_biUnion_le _)

end Rounds
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# 有界轮次构造的迭代

每一步都可依据当前表示来选择下一种表示及其表。这里将所有选择组合成一套实现，其成本和词汇量由给定各项之和控制。

**英文原文**

Iteration of bounded round constructions

Each step may choose the next representation and its tables from the
current representation. This packages those choices into one
installation, with the cost and vocabulary bounded by the given sums.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer

open Assembly Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire}

-- 读法：对 `j` 作归纳。
private theorem choose_rounds {cap j : ℕ} (P : Layer F x y)
    (good : ℕ → Layer F x y → Prop) (start : good 0 P)
    (cost limit : ℕ → ℕ)
    (next : ∀ i < j, ∀ Q : Layer F x y, good i Q →
      ∃ (R : Layer F x y) (L : Finset (Table F)), good (i + 1) R ∧ L.card ≤ limit i ∧
        Transforms F cap L Q.snapshot R.snapshot (cost i)) :
    ∃ (R : ℕ → Layer F x y) (keys : ℕ → Finset (Table F)), R 0 = P ∧
      (∀ i ≤ j, good i (R i)) ∧
      ∀ i < j, (keys i).card ≤ limit i ∧
        Transforms F cap (keys i) (R i).snapshot (R (i + 1)).snapshot (cost i) := by
  induction j with
  | zero =>
    exact ⟨fun _ => P, fun _ => ∅, rfl, fun i hi => (Nat.eq_zero_of_le_zero hi) ▸ start,
      fun i hi => by omega⟩
  | succ j ih =>
    -- 推导：从 `ih (fun i hi => next i (Nat.lt_succ_of_lt hi))` 中取出 `R, keys, hzero, hgood, hstep`。
    obtain ⟨R, keys, hzero, hgood, hstep⟩ := ih (fun i hi => next i (Nat.lt_succ_of_lt hi))
    obtain ⟨Q, L, hQ, hL, step⟩ := next j (Nat.lt_succ_self _) (R j) (hgood j le_rfl)
    refine ⟨Function.update R (j + 1) Q, Function.update keys j L, ?_, ?_, ?_⟩
    · simpa using hzero
    · intro i hi
      by_cases he : i = j + 1
      · subst i
        simpa using hQ
      · rw [Function.update_of_ne he]
        exact hgood i (by omega)
    · intro i hi
      by_cases he : i = j
      · subst i
        simpa [Function.update_of_ne (show j ≠ j + 1 by omega)] using And.intro hL step
      · rw [Function.update_of_ne he, Function.update_of_ne (show i ≠ j + 1 by omega),
          Function.update_of_ne (show i + 1 ≠ j + 1 by omega)]
        exact hstep i (by omega)

-- 读法：结论为 `∃ I : Installation k d, I.u = cap ∧ I.labels.card ≤ (∑ i ∈ range j, limit i) + endLimit ∧ I.cost ≤ 140 * (P.snapshot.port.width + d * (wd a + wd b)) + (∑ i ∈ range j, cost i) + endCost + 1`。
theorem install_rounds {a b : Wire} {k : Val a → Val b → F} {d cap j : ℕ}
    (P : Layer F (copies a d) (copies b d)) (good : ℕ → Layer F (copies a d) (copies b d) → Prop)
    (start : good 0 P) (hj : 0 < j) (hcap : 3 ≤ cap)
    (state : P.State) (z : F)
    (exactPower : (fun x y => z * (P.graph state).eval x y) = power k d)
    (cost limit : ℕ → ℕ)
    (next : ∀ i < j, ∀ Q : Layer F (copies a d) (copies b d), good i Q →
      ∃ (R : Layer F (copies a d) (copies b d)) (L : Finset (Table F)),
        good (i + 1) R ∧ L.card ≤ limit i ∧ Transforms F cap L Q.snapshot R.snapshot (cost i))
    (endCost endLimit : ℕ)
    (terminal : ∀ Q : Layer F (copies a d) (copies b d), good j Q →
      ∃ L : Finset (Table F), L.card ≤ endLimit ∧ Finishes F cap L Q.snapshot endCost) :
    ∃ I : Installation k d, I.u = cap ∧
      I.labels.card ≤ (∑ i ∈ range j, limit i) + endLimit ∧
      I.cost ≤ 140 * (P.snapshot.port.width + d * (wd a + wd b)) +
        (∑ i ∈ range j, cost i) + endCost + 1 := by
  classical
  -- 推导：从 `choose_rounds P good start cost limit next` 中取出 `R, keys, hzero, hgood, hstep`。
  obtain ⟨R, keys, hzero, hgood, hstep⟩ := choose_rounds P good start cost limit next
  obtain ⟨L, hL, finish⟩ := terminal (R j) (hgood j le_rfl)
  have hin : ∃ state : (R 0).State, (fun x y => z * ((R 0).graph state).eval x y) = power k d := by
    rw [hzero]
    exact ⟨state, exactPower⟩
  obtain ⟨i, hi⟩ := hin
  obtain ⟨I, hu, _, hk, hc⟩ := Layer.install_sequence R keys L cost hj hcap i z hi
    (fun l hl => (hstep l hl).2) finish
  refine ⟨I, hu, hk.trans (Nat.add_le_add ?_ hL), ?_⟩
  · exact sum_le_sum (fun l hl => (hstep l (mem_range.mp hl)).1)
  · simpa only [hzero] using hc

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# 分别核算地址、控制和载荷开销

长地址的成本按宿主计费。在末端保留足够的块数，即可从出现位置的预算中支付此项开销。短记录可使用分组大小的某个固定次幂，再乘一个多对数因子。终端载荷与外部数据上的指数可取任意小的正数。

**英文原文**

Separating the cost of addresses, controls and payloads

The long-address cost is charged per host. Retaining enough blocks at
the end pays for this cost from the occurrence budget. Short records
may use a fixed power of the grouping size, with a polylogarithmic
factor. The exponent on the terminal payload and the exterior can be
arbitrarily small.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter
variable {δ : ℝ} {p : Design δ} {R : ℕ}

-- 读法：`Levels.expense` 的结果类型为 `ℝ`。
/-- 吸收固定常数和对数因子之前的原始成本。

英文原文：Raw cost before absorbing fixed constants and logarithmic factors.
-/
def Levels.expense (v : Levels p R) (h : ℝ) (m e q : ℕ) : ℝ :=
  ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) *
    ((2 : ℝ) ^ (q * v.group) + h ^ R / (2 : ℝ) ^ v.remaining) +
    v.finalBudget m + (v.batch * e : ℕ)

-- 读法：结论为 `let h : ℝ := Nat.clog 2 n v.expense h m e q ≤ ((2 : ℝ) ^ (2 * p.groupRate * q) + 1) * v.work m e h a (p.groupRate * q)`。
theorem Levels.expense_le {v : Levels p R} {n T₀ m e q : ℕ} {a b ξ : ℝ}
    (ha : 0 ≤ a) (ok : v.Suits n T₀ a b ξ) :
    let h : ℝ := Nat.clog 2 n
    v.expense h m e q ≤ ((2 : ℝ) ^ (2 * p.groupRate * q) + 1) * v.work m e h a (p.groupRate * q) := by
  let h : ℝ := Nat.clog 2 n
  let A : ℝ := (2 : ℝ) ^ (2 * p.groupRate * q) + 1
  have hpos : 0 < h := zero_lt_one.trans ok.2.1
  have hh : 1 ≤ h := ok.2.1.le
  have hA : 1 ≤ A := le_add_of_nonneg_left (by positivity : 0 ≤ (2 : ℝ) ^ (2 * p.groupRate * q))
  have hheight : h ≤ (2 : ℝ) ^ v.height := ok.2.2.1
  -- 推导：记下中间结论 `hgroup`：`(2 : ℝ) ^ v.group ≤ 2 ^ (2 * p.groupRate) * h ^ (p.groupRate * a)`。
  have hgroup : (2 : ℝ) ^ v.group ≤ 2 ^ (2 * p.groupRate) * h ^ (p.groupRate * a) := by
    rcases ok with ⟨_, _, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  have long : h ^ R / (2 : ℝ) ^ v.remaining ≤ 1 := by
    apply (div_le_one (by positivity)).2
    unfold Levels.remaining
    rw [mul_comm R, pow_mul]
    exact pow_le_pow_left₀ hpos.le hheight _
  have short : (2 : ℝ) ^ (q * v.group) ≤ (2 : ℝ) ^ (2 * p.groupRate * q) * h ^ ((p.groupRate * q : ℕ) * a) := calc
    _ = ((2 : ℝ) ^ v.group) ^ q := by rw [mul_comm, pow_mul]
    _ ≤ ((2 : ℝ) ^ (2 * p.groupRate) * h ^ (p.groupRate * a)) ^ q :=
      pow_le_pow_left₀ (by positivity) hgroup _
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast hpos.le]
      congr 1
      push_cast
      ring_nf
  -- 推导：记下中间结论 `scale`：`1 ≤ h ^ ((p.groupRate * q : ℕ) * a)`。
  have scale : 1 ≤ h ^ ((p.groupRate * q : ℕ) * a) := Real.one_le_rpow hh (by positivity)
  have controls : (2 : ℝ) ^ (q * v.group) + h ^ R / (2 : ℝ) ^ v.remaining ≤ A * h ^ ((p.groupRate * q : ℕ) * a) := by
    unfold A
    rw [add_mul, one_mul]
    exact add_le_add short (long.trans scale)
  let N : ℝ := ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ)
  have hctrl :
      N * ((2 : ℝ) ^ (q * v.group) + h ^ R / (2 : ℝ) ^ v.remaining) ≤
        A * (N * h ^ ((p.groupRate * q : ℕ) * a)) :=
    (mul_le_mul_of_nonneg_left controls (by unfold N; positivity)).trans_eq (by ring)
  change N * _ + v.finalBudget m + (v.batch * e : ℕ) ≤
    A * (N * h ^ ((p.groupRate * q : ℕ) * a) + v.finalBudget m + (v.batch * e : ℕ))
  -- 推导：记下中间结论 `hfinal`：`0 ≤ v.finalBudget m`。
  have hfinal : 0 ≤ v.finalBudget m := by unfold Levels.finalBudget; positivity
  calc
    _ ≤ A * (N * h ^ ((p.groupRate * q : ℕ) * a)) + A * v.finalBudget m + A * (v.batch * e : ℕ) :=
      add_le_add (add_le_add hctrl (le_mul_of_one_le_left hfinal hA))
        (le_mul_of_one_le_left (by positivity) hA)
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 吸收实现时的额外开销

对数余量足以吸收固定因子和高度对数的各个幂次。词汇量预算可容纳高度的任意固定多项式。

**英文原文**

Absorbing the implementation overhead

The logarithmic slack pays for fixed factors and powers of the logarithm
of the height. The vocabulary budget accommodates any fixed polynomial
in the height.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter

-- 读法：对每个 `ᶠ n : ℕ in atTop`，`C * (Nat.clog 2 n) ^ s` 不超过 `Shaving.dictionary n`。这里调用 `Nat.pow_le_pow_iff_right`。
theorem dictionary_dominates (C s : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (Nat.clog 2 n) ^ s ≤ Shaving.dictionary n := by
  let S := C + s + 1
  have hS := Shaving.tendsto_height.eventually_ge_atTop ((2 : ℕ) ^ S : ℝ)
  filter_upwards [hS] with n hn
  let h := Nat.clog 2 n
  let t := Nat.clog 2 h
  have hh : h ≤ 2 ^ t := Nat.le_pow_clog (by decide : 1 < 2) _
  have ht : S ≤ t := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (show (2 : ℕ) ^ S ≤ h by exact_mod_cast hn).trans hh
  -- 推导：记下中间结论 `hC`：`C ≤ (2 : ℕ) ^ t`。
  have hC : C ≤ (2 : ℕ) ^ t := by
    exact (show C ≤ S by unfold S; omega).trans (ht.trans Nat.lt_two_pow_self.le)
  calc
    _ ≤ (2 : ℕ) ^ t * ((2 : ℕ) ^ t) ^ s := Nat.mul_le_mul hC (Nat.pow_le_pow_left hh _)
    _ = (2 : ℕ) ^ (t * (s + 1)) := by rw [pow_mul, pow_succ']
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      change t * (s + 1) ≤ t ^ 2
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (by unfold S at ht; omega)

variable {δ : ℝ} {p : Design δ} {R T₀ : ℕ}
-- 读法：证明中先建立 `hσ`，即 `0 < σ`。
theorem Levels.installed_of_expense {a b ξ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (C : ℝ) (r q B s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p R) (m : ℕ),
      v.Suits n T₀ a b ξ →
      ∀ (K : Type) [Field K] (x y : Wire) (k : Val x → Val y → K),
      let h : ℝ := Nat.clog 2 n
      let σ := a * δ / 12
      ∀ I : Installation k v.batch,
        I.labels.card ≤ B * (Nat.clog 2 n) ^ s →
        (I.cost : ℝ) ≤ |C| *(Real.log h) ^ r * h ^ σ * v.expense h m (wd x + wd y) q →
        (I.u : ℝ) ≤ |C| *(Real.log h) ^ r * h ^ σ * (p.D * (v.finalWidth : ℝ)) →
        v.Installed n m (p.groupRate * q) a k := by
  let A : ℝ := (2 : ℝ) ^ (2 * p.groupRate * q) + 1
  let σ := a * δ / 12
  -- 推导：记下中间结论 `hσ`：`0 < σ`。
  have hσ : 0 < σ := by unfold σ; positivity
  have ht := Shaving.tendsto_height
  filter_upwards [dictionary_dominates B s,
    ht.eventually (Shaving.polylog_le (|C| *A) r hσ),
    ht.eventually (Shaving.polylog_le |C| r hσ)] with n hd hc hu v m hv K _ x y k
  dsimp only
  intro I hb hcost harity
  let h : ℝ := Nat.clog 2 n
  let e := wd x + wd y
  have hh : 1 < h := hv.2.1
  -- 推导：记下中间结论 `hpos`：`0 < h`。
  have hpos : 0 < h := zero_lt_one.trans hh
  have hlog := (Real.log_pos hh).le
  have hwork : 0 ≤ v.work m e h a (p.groupRate * q) := by
    unfold Levels.work Levels.finalBudget
    positivity
  have hw : 0 ≤ (p.D : ℝ) * v.finalWidth := by positivity
  have he := v.expense_le (q:=q) (m:=m) (e:=e) ha.le hv
  change v.expense h m e q ≤ A * _ at he
  have hsc : h ^ σ * h ^ σ = h ^ (a * δ / 6) := by
    rw [← Real.rpow_add hpos]
    congr 1
    unfold σ
    ring
  refine ⟨I, hb.trans hd, ?_, ?_⟩
  · calc
      _ ≤ _ := hcost
      _ ≤ |C| *(Real.log h) ^ r * h ^ σ * (A * v.work m e h a (p.groupRate * q)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = ((|C| *A) * (Real.log h) ^ r) * h ^ σ * v.work m e h a (p.groupRate * q) := by ring
      _ ≤ h ^ σ * h ^ σ * v.work m e h a (p.groupRate * q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hwork
      _ = _ := by rw [hsc]
  · calc
      _ ≤ _ := harity
      _ ≤ h ^ σ * h ^ σ * (p.D * (v.finalWidth : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) hw
      _ = _ := by rw [hsc]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 各轮求和的额外开销

**英文原文**

The overhead of summing the rounds
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Filter
variable {δ : ℝ} {p : Design δ} {R n T₀ : ℕ} {a b ξ : ℝ} {v : Levels p R}

-- 读法：`2 ^ v.j` 不超过 `(Nat.clog 2 n) ^ 2`。
theorem Levels.Suits.rounds_pow (ok : v.Suits n T₀ a b ξ) (ha : a ≤ 1) :
    2 ^ v.j ≤ (Nat.clog 2 n) ^ 2 := by
  let h : ℝ := Nat.clog 2 n
  have hh : 1 ≤ h := ok.2.1.le
  have hD : 1 ≤ (p.D : ℝ) := by have := p.large; exact_mod_cast (show 1 ≤ p.D by omega)
  obtain ⟨_, _, _, _, _, _, _, _, hw, _, _, _, _⟩ := ok
  have hj : (2 : ℝ) ^ v.j ≤ h ^ 2 := calc
    _ ≤ (2 : ℝ) ^ (p.gain * v.j) := pow_le_pow_right₀ (by norm_num)
      (Nat.le_mul_of_pos_left _ p.gain_pos)
    _ ≤ (p.D : ℝ) * (2 : ℝ) ^ (p.gain * v.j) := le_mul_of_one_le_left (by positivity) hD
    _ ≤ h ^ (2 * a) := hw
    _ ≤ h ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh (by linarith)
    _ = _ := Real.rpow_two h
  unfold h at hj
  exact_mod_cast hj

-- 读法：`(v.j : ℝ)` 不超过 `2 / (Real.log 2) * Real.log (Nat.clog 2 n)`。
theorem Levels.Suits.rounds_log (ok : v.Suits n T₀ a b ξ) (ha : a ≤ 1) :
    (v.j : ℝ) ≤ 2 / (Real.log 2) * Real.log (Nat.clog 2 n) := by
  have hp : (2 : ℝ) ^ v.j ≤ (Nat.clog 2 n : ℝ) ^ 2 := by exact_mod_cast ok.rounds_pow ha
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
  exact hl

-- 读法：证明中先建立 `hlog`，即 `0 < Real.log 2`。
/-- 总成本为每一轮计一项估计，并为初始和终止阶段再计两项。词汇量计数包含终端求值器。最终成立的各个界对工作域一致。

英文原文：The total cost allows one estimate per round and two more for the
initial and terminal stages. The vocabulary counts include the terminal
evaluator. All eventual bounds are uniform in the working field.
-/
theorem Levels.installed_of_round_budget (ha : 0 < a) (ha' : a ≤ 1) (hδ : 0 < δ)
    (C : ℝ) (r q B s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p R) (m : ℕ),
      v.Suits n T₀ a b ξ →
      ∀ (K : Type) [Field K] (x y : Wire) (k : Val x → Val y → K),
      let h : ℝ := Nat.clog 2 n
      let σ := a * δ / 12
      ∀ I : Installation k v.batch,
        I.labels.card ≤ (v.j + 1) * (B * (Nat.clog 2 n) ^ s) →
        (I.cost : ℝ) ≤ (v.j + 2) * (|C| * (Real.log h) ^ r * h ^ σ * v.expense h m (wd x + wd y) q) →
        (I.u : ℝ) ≤ (v.j + 2) * (|C| * (Real.log h) ^ r * h ^ σ * (p.D * (v.finalWidth : ℝ))) →
        v.Installed n m (p.groupRate * q) a k := by
  let J : ℝ := 2 / (Real.log 2) + 2
  -- 推导：记下中间结论 `hlog`：`0 < Real.log 2`。
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ : 0 ≤ J := by unfold J; positivity
  have h := (Real.tendsto_log_atTop.comp Shaving.tendsto_height).eventually_ge_atTop 1
  filter_upwards [h, Levels.installed_of_expense (p:=p) (R:=R) (T₀:=T₀)
    (b:=b) (ξ:=ξ) ha hδ (J*|C|) (r + 1) q B (s + 2)] with n hn go v m ok K _ x y k
  dsimp only
  intro I keys size arity
  let h : ℝ := Nat.clog 2 n
  let σ := a * δ / 12
  have hh : 0 < h := zero_lt_one.trans ok.2.1
  change 1 ≤ Real.log h at hn
  -- 推导：记下中间结论 `hlogh`：`0 ≤ Real.log h`。
  have hlogh : 0 ≤ Real.log h := zero_le_one.trans hn
  have hs : (v.j : ℝ) + 2 ≤ J * Real.log h := by
    have ht := ok.rounds_log ha'
    have htwo := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2)
    unfold J
    rw [add_mul]
    exact add_le_add ht (by simpa only [mul_one] using htwo)
  have hcard : (v.j + 1) * (B * (Nat.clog 2 n) ^ s) ≤ B * (Nat.clog 2 n) ^ (s + 2) := calc
    _ ≤ (Nat.clog 2 n) ^ 2 * (B * (Nat.clog 2 n) ^ s) := Nat.mul_le_mul_right _
      (Nat.lt_two_pow_self.trans_le (ok.rounds_pow ha'))
    _ = _ := by rw [pow_add]; ring
  refine go v m ok K x y k I (keys.trans hcard) ?_ ?_
  -- 推导：记下中间结论 `hexp`：`0 ≤ v.expense h m (wd x + wd y) q`。
  · have hexp : 0 ≤ v.expense h m (wd x + wd y) q := by
      unfold Levels.expense Levels.finalBudget
      positivity
    calc
      _ ≤ _ := size
      _ ≤ J * Real.log h * (|C| * (Real.log h) ^ r * h ^ σ * v.expense h m (wd x + wd y) q) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by rw [abs_of_nonneg (mul_nonneg hJ (abs_nonneg C)), pow_succ]; ring
  · calc
      _ ≤ _ := arity
      _ ≤ J * Real.log h * (|C| * (Real.log h) ^ r * h ^ σ * (p.D * (v.finalWidth : ℝ))) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by rw [abs_of_nonneg (mul_nonneg hJ (abs_nonneg C)), pow_succ]; ring

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 将阶段操作计入公共压缩预算

**英文原文**

Charging phase operations to the shared compression budget
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

variable {δ : ℝ} {p : Design δ} {R : ℕ} (v : Levels p R)

-- 读法：`(2 : ℝ) ^ addr` 不超过 `((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) / (2 : ℝ) ^ v.remaining`。这里调用 `le_div_iff₀`。
/-- 只要保留的块数达到指定下限，各出现位置的预算就足以支付长地址的成本。

英文原文：Keeping at least the prescribed number of blocks pays for long
addresses out of a budget on occurrences.
-/
theorem Levels.host_budget {m addr blocks : ℕ}
    (remain : v.remaining ≤ blocks)
    (seats : 2 ^ (addr + blocks) ≤ p.overhead ^ v.j * v.allocation m) :
    (2 : ℝ) ^ addr ≤ ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) / (2 : ℝ) ^ v.remaining := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [← pow_add]
  exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.add_le_add_left remain addr)).trans seats

-- 读法：`(cost : ℝ)` 不超过 `W * v.expense h m e q`。
/-- 一个阶段可以为长地址、各出现位置上的短记录以及全部外露载荷分别采用不同的布局。

英文原文：A phase may use a separate layout for long addresses, for short
records at each occurrence, and for the full exposed payload.
-/
theorem Levels.phase_expense {h W : ℝ} {m e q addr blocks long short ext cost : ℕ}
    (hh : 0 ≤ h) (hW : 0 ≤ W) (remain : v.remaining ≤ blocks)
    (seats : 2 ^ (addr + blocks) ≤ p.overhead ^ v.j * v.allocation m)
    (size : cost ≤ 2 ^ addr * long + 2 ^ (addr + blocks) * short + v.batch * e * ext)
    (hc₁ : (long : ℝ) ≤ W * h ^ R) (hc₂ : (short : ℝ) ≤ W * (2 : ℝ) ^ (q * v.group))
    (hc₃ : (ext : ℝ) ≤ W) :
    (cost : ℝ) ≤ W * v.expense h m e q := by
  let N : ℝ := ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ)
  have ht : 0 ≤ h ^ R := by positivity
  have a : (2 : ℝ) ^ addr * (long : ℝ) ≤ W * (N * (h ^ R / (2 : ℝ) ^ v.remaining)) := calc
    _ ≤ (N / (2 : ℝ) ^ v.remaining) * (W * h ^ R) :=
      mul_le_mul (v.host_budget remain seats) hc₁ (by positivity) (by positivity)
    _ = _ := by ring
  -- 推导：记下中间结论 `b`：`(2 : ℝ) ^ (addr + blocks) * (short : ℝ) ≤ W * (N * (2 : ℝ) ^ (q * v.group))`。
  have b : (2 : ℝ) ^ (addr + blocks) * (short : ℝ) ≤ W * (N * (2 : ℝ) ^ (q * v.group)) := calc
    _ ≤ N * (W * (2 : ℝ) ^ (q * v.group)) :=
      mul_le_mul (by dsimp only [N]; exact_mod_cast seats) hc₂ (by positivity) (by positivity)
    _ = _ := by ring
  have c : ((v.batch * e : ℕ) : ℝ) * (ext : ℝ) ≤ W * ((v.batch * e : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hc₃ (by positivity)).trans_eq (mul_comm _ _)
  have hfin : 0 ≤ v.finalBudget m := by unfold Levels.finalBudget; positivity
  calc
    _ ≤ (2 : ℝ) ^ addr * (long : ℝ) + (2 : ℝ) ^ (addr + blocks) * (short : ℝ) + ((v.batch * e : ℕ) : ℝ) * (ext : ℝ) := by
      exact_mod_cast size
    _ ≤ W * (N * (h ^ R / (2 : ℝ) ^ v.remaining)) + W * (N * (2 : ℝ) ^ (q * v.group)) +
        W * ((v.batch * e : ℕ) : ℝ) := add_le_add (add_le_add a b) c
    _ ≤ W * v.expense h m e q := by
      change _ ≤ W * (N * ((2 : ℝ) ^ (q * v.group) + h ^ R / (2 : ℝ) ^ v.remaining) +
        v.finalBudget m + ((v.batch * e : ℕ) : ℝ))
      nlinarith only [mul_nonneg hW hfin]

-- 读法：`(cost : ℝ)` 不超过 `W * v.expense h m e q`。这里调用 `size.trans`。
/-- 终端求值器使用活动图的最终费用和外露比特的费用。控制与布线的成本也可使用本阶段的预算。

英文原文：The terminal evaluator uses the final charge of the live graph and
the exposed bits. Control and wiring costs can also use the phase budget.
-/
theorem Levels.terminal_expense {h W : ℝ} {m e q cost : ℕ}
    (hh : 0 ≤ h) (hW : 0 ≤ W)
    (size : (cost : ℝ) ≤ W * (v.finalBudget m + (v.batch * e : ℕ))) :
    (cost : ℝ) ≤ W * v.expense h m e q := by
  apply size.trans
  apply mul_le_mul_of_nonneg_left _ hW
  unfold Levels.expense
  have hp : 0 ≤ ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) *
      ((2 : ℝ) ^ (q * v.group) + h ^ R / (2 : ℝ) ^ v.remaining) := by positivity
  linarith only [hp]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 按统一的逐阶段开销安装整个序列

**英文原文**

Installing a sequence with a uniform per-stage cost
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer

open Assembly Finset

variable {F : Type} [Field F] {x y : Wire}

-- 读法：存在 `I : Installation k d`，`I.u = cap` 与 `I.labels.card ≤ (j + 1) * labelLimit ∧ (I.cost : ℝ) ≤ (j + 2) * budget` 同时成立。
theorem install_with_bounds {k : Val x → Val y → F} {d cap j labelLimit : ℕ}
    (P : Layer F (copies x d) (copies y d))
    (good : ℕ → Layer F (copies x d) (copies y d) → Prop)
    (start : good 0 P) (hj : 0 < j) (hcap : 3 ≤ cap)
    (state : P.State) (z : F)
    (exactPower : (fun a b => z * (P.graph state).eval a b) = power k d)
    (budget : ℝ) (hb : 0 ≤ budget)
    (startCost : ((140 * (P.snapshot.port.width + d * (wd x + wd y)) + 1 : ℕ) : ℝ) ≤ budget)
    (next : ∀ i < j, ∀ Q : Layer F (copies x d) (copies y d), good i Q →
      ∃ (R : Layer F (copies x d) (copies y d)) (L : Finset (Table F)) (u m : ℕ),
        good (i + 1) R ∧ L.card ≤ labelLimit ∧ u ≤ cap ∧ (m : ℝ) ≤ budget ∧
        Transforms F u L Q.snapshot R.snapshot m)
    (terminal : ∀ Q : Layer F (copies x d) (copies y d), good j Q →
      ∃ (L : Finset (Table F)) (u m : ℕ),
        L.card ≤ labelLimit ∧ u ≤ cap ∧ (m : ℝ) ≤ budget ∧ Finishes F u L Q.snapshot m) :
    ∃ I : Installation k d, I.u = cap ∧ I.labels.card ≤ (j + 1) * labelLimit ∧
      (I.cost : ℝ) ≤ (j + 2) * budget := by
  let w := ⌊budget⌋₊
  have next' i (hi : i < j) Q (hQ : good i Q) :
      ∃ (R : Layer F (copies x d) (copies y d)) (L : Finset (Table F)),
        good (i + 1) R ∧ L.card ≤ labelLimit ∧ Transforms F cap L Q.snapshot R.snapshot w := by
    -- 推导：从 `next i hi Q hQ` 中取出 `R, L, u, m, hr, hl, hu, hm, ht`。
    obtain ⟨R, L, u, m, hr, hl, hu, hm, ht⟩ := next i hi Q hQ
    exact ⟨R, L, hr, hl, (ht.mono (Nat.le_floor hm)).widen hu Set.Subset.rfl⟩
  have terminal' Q (hQ : good j Q) :
      ∃ L : Finset (Table F), L.card ≤ labelLimit ∧ Finishes F cap L Q.snapshot w := by
    obtain ⟨L, u, m, hl, hu, hm, ht⟩ := terminal Q hQ
    obtain ⟨f, hf, he⟩ := ht.widen hu Set.Subset.rfl
    exact ⟨L, hl, f, hf.mono (Nat.le_floor hm), he⟩
  obtain ⟨I, hi, hl, hcost⟩ := install_rounds P good start hj hcap state z exactPower
    (fun _ => w) (fun _ => labelLimit) next' w labelLimit terminal'
  simp only [sum_const, card_range, nsmul_eq_mul] at hl hcost
  change I.labels.card ≤ j * labelLimit + labelLimit at hl
  change I.cost ≤ _ + j * w + w + 1 at hcost
  refine ⟨I, hi, hl.trans_eq (by rw [add_mul, one_mul]), ?_⟩
  -- 推导：记下中间结论 `hf`：`(w : ℝ) ≤ budget`。
  have hf : (w : ℝ) ≤ budget := Nat.floor_le hb
  have hprod := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ j by positivity)
  have hc : (I.cost : ℝ) ≤ (140 : ℝ) * (P.snapshot.port.width + d * (wd x + wd y)) +
      (j : ℝ) * w + w + 1 := by exact_mod_cast hcost
  push_cast at startCost
  nlinarith only [hc, startCost, hf, hprod]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# 移除板的表示中仅含标量的条目

**英文原文**

Removing scalar-only entries from presented boards
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly

variable {F : Type} [Field F] {x y : Wire}

-- 读法：在后续公式中，`Rounds.Board.sweep` 是 `{ B with diagram := B.diagram.sweep }` 的缩写。
abbrev Rounds.Board.sweep {h : ℕ} (B : Rounds.Board F x y h) : Rounds.Board F x y h :=
  { B with diagram := B.diagram.sweep }

namespace Assembly.Template.Presents
variable {D : Template F} {r : D.format.obj} {B : Rounds.Board F x y D.scheme.h} (p : D.Presents r B)

-- 读法：用字段 `pres`、`host`、`vertex`、`directed` 构造 `D.sweep.Presents r B.sweep`。
def sweep : D.sweep.Presents r B.sweep where
  pres := p.pres.sweep
  host := p.host
  vertex := p.vertex
  directed t := by
    change D.scheme.direction r.1 (p.pres.sweepSeats.ends t).1 = t.isRight
    rw [p.pres.sweep_end]
    exact p.directed t
  live := p.live
  closed := p.closed
  reciprocal := p.reciprocal
  edge := p.edge
  core := p.core
  load := p.load

-- 读法：用字段 `template`、`volume`、`height`、`State` 构造 `Rounds.Layer F x y`。
/-- 单块板的表示，另行给出一个初始标量。

英文原文：Presentation of a single board, with a separate initial scalar.
-/
abbrev singleton {t : ℕ} (bound : ∀ v, B.diagram.arity v ≤ 2 ^ t) : Rounds.Layer F x y where
  template := D.sweep
  volume := 2 ^ D.scheme.m + wd x + wd y
  height := D.scheme.h + t
  State := PUnit.{2}
  board _ := B.sweep
  data _ := r
  presents _ := p.sweep
  fits _ := p.fits bound

end Assembly.Template.Presents
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# 已就绪层的终端电路

**英文原文**

A terminal circuit for a ready layer
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Contraction
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} (Q : Layer F a b) (W : Prices F)
  (V t w : ℕ)
local notation "S" => Q.template.scheme
local notation "J" => Terminal.instruction Q.template.scheme V t (Q.template.scheme.d + 1) w Q.template.scheme.spanRows
local notation "Y" => Q.encoding.payload

-- 读法：`finishCost` 的构造用到 `Q.template.format.width`、`format.width`、`Terminal.price`。
def finishCost (c : ℕ) :=
  4 * (Q.template.format.width + 2 * (S).format.width) + c + 4 * (Y).width +
    Terminal.price W (S) V t Q.volume Q.height ((S).d + 1) w (S).spanRows

-- 读法：要证明的命题是 `Finishes F u K Q.snapshot (Q.finishCost W V t w c)`。
theorem finish {u c : ℕ} {K : Set (Table F)}
    (hu : 3 ≤ u) (hm : 1 ≤ (S).m)
    (ht : 2 ^ ((S).d + 1) * ((max (Terminal.height (S) t) Q.height + 1) * (2 ^ (S).m + 2 ^ (S).m)) < 2 ^ W.w)
    (size : Terminal.Dictionary.arity (S) t ≤ u) (label : Terminal.Dictionary.label (S) t ∈ K)
    (ok : ∀ i, Terminal.Fits (S) (Q.data i).1 V t ∧ Terminal.Neutral (S) (Q.data i).1)
    (hw : Terminal.height (S) t < w) (hk : Q.height < w)
    (generate : Map F u K (S).format J (Terminal.orders (S) V t w) c) :
    Finishes F u K Q.snapshot (Q.finishCost W V t w c) := by
  have read : Circuit F Q.template.format (S).format Prod.fst
      (Q.template.format.width + 2 * (S).format.width) := Circuit.project Sum.inl (fun _ _ => rfl)
  -- 推导：记下中间结论 `start`：`= ((Map.circuit (L`。
  have start := ((Map.circuit (L := K) hu read).comp generate).par
    (Map.circuit (L := K) hu (Circuit.id F Y))
  have stop := Terminal.evaluate (S) V t Q.volume Q.height ((S).d + 1) w (S).spanRows W hu hm ht size label
  let f (z : Q.encoding.port.obj) :=
    Terminal.value (S) V t Q.volume Q.height ((S).d + 1) w (S).spanRows
      (Terminal.orders (S) V t w z.1.1) z.2
  have go : Kernel F u K Q.encoding.port (.wire .unit) (fun z _ => f z) (Q.finishCost W V t w c) :=
    start.then_kernel stop
  refine Q.encoding.finishes go fun i x => ?_
  exact Terminal.value_orders (ok i).1 (Q.fits i) (Q.presents i).pres.proper (Q.presents i).reciprocal
    (ok i).2 hw hk x

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# 层的统一终止

选定三个标签，即可供这一层的每个加数使用。所有隐藏赋值都在同一个网络内求和。

**英文原文**

Uniform termination of a layer

One choice of the three labels serves every summand of the layer.
All hidden assignments are summed inside the same network.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Contraction

-- 读法：这里调用 `Nat.pow_le_pow_iff_right`。
theorem terminal : ∃ K : ℕ, ∀ (F : Type) [Field F] (x y : Wire) (Q : Layer F x y)
    (W : Prices F) (V t : ℕ),
    let i := Terminal.Rates.Size.mk F Q.template.scheme W V t Q.volume Q.height
    1 ≤ i.S.m → 2 ^ i.p * (i.w * (2 ^ i.S.m + 2 ^ i.S.m)) < 2 ^ W.w →
    (∀ j, Terminal.Fits i.S (Q.data j).1 V t ∧ Terminal.Neutral i.S (Q.data j).1) →
    ∀ (u : ℕ) (L : Set (Table F)), 3 ≤ u → Terminal.arity i.S t i.w ≤ u →
      (↑(Terminal.labels i.S t i.w) : Set (Table F)) ⊆ L →
      Finishes F u L Q.snapshot (4 * Q.snapshot.port.width + i.bound K) := by
  classical
  obtain ⟨K, hK⟩ := Terminal.Rates.terminal
  refine ⟨K, ?_⟩
  intro F _ x y Q W V t i hm hw ok u L hu ha hl
  -- 推导：记下中间结论 `room`：`i.S.m ≤ W.w`。
  have room : i.S.m ≤ W.w := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    refine (Nat.le_add_right _ (2 ^ i.S.m)).trans ?_
    exact ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))).trans hw.le
  have size : Terminal.Dictionary.arity i.S t ≤ u := by unfold Terminal.arity at ha; omega
  have label : Terminal.Dictionary.label i.S t ∈ L := hl (by simp [Terminal.labels])
  have build := Terminal.generate i hm room hu ha hl
  obtain ⟨f, hf, he⟩ := Q.finish W V t i.w hu hm hw size label ok
    (Nat.lt_succ_of_le (le_max_left ..)) (Nat.lt_succ_of_le (le_max_right ..)) build
  refine ⟨f, hf.mono ?_, he⟩
  -- 推导：记下中间结论 `b`：`8 * i.S.format.width + Terminal.orderCost i + i.price ≤ i.bound K`。
  have b : 8 * i.S.format.width + Terminal.orderCost i + i.price ≤ i.bound K := hK i
  change 4 * (Q.template.format.width + 2 * i.S.format.width) + Terminal.orderCost i+
    4 * Q.encoding.payload.width + i.price ≤ 4 * (Q.template.format.pair Q.encoding.payload).width + i.bound K
  rw [Format.width_pair Q.template.format Q.encoding.payload]
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end
