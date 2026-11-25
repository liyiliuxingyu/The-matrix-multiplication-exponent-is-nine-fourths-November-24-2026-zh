-- 本文件所属证明环节：对二进分组的站点和线束装包、匹配及重新布线，逐项控制异常基区、临界负载、重置度数以及核心连线宽度的递推。
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.LinearAlgebra.MatrixExponent.Packing.BadBases
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift

/-!
# 在按线性顺序排列的箱中匹配完整物件

**英文原文**

Matching whole items in a linear stream of bins
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {A I D : Type} (item : A → I) (bin : A → Option D)

-- 读法：当 `∀ j, item j = item i → bin j = bin i` 成立时取 `bin i`，否则取 `none`。
/-- 只保留能完整放入同一个箱中的项。

英文原文：Keep exactly those items that fit entirely in a single bin.
-/
def plan (i : A) : Option D :=
  if ∀ j, item j = item i → bin j = bin i then bin i else none

-- 读法：`(univ.filter fun i => (bin i).isSome).card` 不超过 `(univ.filter fun i => (plan item bin i).isSome).card + b * ((univ.filter fun i => (bin i).isSome).image bin).card`。按 `i ∈ bad` 成立与否分情况。
/-- 将一个被分开的项计入某个箱的成本，该箱占用的连续区段在此项内部结束。两个不同的项无法计入同一个箱。

英文原文：Charge a split item to a bin whose run ends inside it. Two distinct
items cannot be charged to the same bin.
-/
theorem straddles [Fintype A] [LinearOrder A] [DecidableEq I] [DecidableEq D]
    (hitem : ∀ i j k, i ≤ j → j ≤ k → item i = item k → item j = item i)
    (hbin : ∀ i j k, i ≤ j → j ≤ k → bin i = bin k → (bin i).isSome → bin j = bin i)
    (hprefix : ∀ i j, i ≤ j → item i = item j → (bin j).isSome → (bin i).isSome)
    (b : ℕ) (bound : ∀ t, (univ.filter fun i => item i = t).card ≤ b) :
    (univ.filter fun i => (bin i).isSome).card ≤
      (univ.filter fun i => (plan item bin i).isSome).card +
        b * ((univ.filter fun i => (bin i).isSome).image bin).card := by
  let eligible := univ.filter fun i => (bin i).isSome
  let matched := univ.filter fun i => (plan item bin i).isSome
  let bad := eligible \ matched
  have witness (i : A) : ∃ l r : A, i ∈ bad →
      l ≤ r ∧ item l = item i ∧ item r = item i ∧ (bin l).isSome ∧ bin r ≠ bin l := by
    by_cases hi : i ∈ bad
    · have ha := (mem_filter.mp (mem_sdiff.mp hi).1).2
      -- 推导：记下中间结论 `hn`：`¬ ∀ j, item j = item i → bin j = bin i`。
      have hn : ¬ ∀ j, item j = item i → bin j = bin i := by
        intro h
        apply (mem_sdiff.mp hi).2
        exact mem_filter.mpr ⟨mem_univ _, by simpa only [plan, ite_eq_left h] using ha⟩
      push Not at hn
      obtain ⟨j, hj, hne⟩ := hn
      rcases le_total i j with h | h
      · exact ⟨i, j, fun _ => ⟨h, rfl, hj, ha, hne⟩⟩
      · exact ⟨j, i, fun _ => ⟨h, hj, rfl, hprefix j i h hj ha, hne.symm⟩⟩
    · exact ⟨i, i, fun h => (hi h).elim⟩
  choose l r hr using witness
  have same (i j : A) (hi : i ∈ bad) (hj : j ∈ bad)
      (he : bin (l i) = bin (l j)) (hle : l i ≤ l j) : item i = item j := by
    -- 推导：从 `hr i hi` 中取出 `hil, hli, hri, hs, hne`。
    obtain ⟨hil, hli, hri, hs, hne⟩ := hr i hi
    rcases le_total (l j) (r i) with h | h
    · have := hitem _ _ _ hle h (hli.trans hri.symm)
      exact hli.symm.trans (this.symm.trans (hr j hj).2.1)
    · exact (hne (hbin _ _ _ hil h he hs)).elim
  have maps : Set.MapsTo (fun i => bin (l i)) bad (eligible.image bin) := by
    intro i hi
    exact mem_image.mpr ⟨l i, mem_filter.mpr ⟨mem_univ _, (hr i hi).2.2.2.1⟩, rfl⟩
  have hb : bad.card ≤ b * (eligible.image bin).card := by
    rw [card_eq_sum_card_fiberwise maps]
    calc
      _ ≤ ∑ _d ∈ eligible.image bin, b := by
        apply sum_le_sum
        intro d _
        by_cases hd : (bad.filter fun i => bin (l i) = d).Nonempty
        · obtain ⟨j, hj⟩ := hd
          obtain ⟨hj, ej⟩ := mem_filter.mp hj
          refine le_trans (card_le_card ?_) (bound (item j))
          intro i hi
          obtain ⟨hi, ei⟩ := mem_filter.mp hi
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          rcases le_total (l i) (l j) with h | h
          · exact same i j hi hj (ei.trans ej.symm) h
          · exact (same j i hj hi (ej.trans ei.symm) h).symm
        · simp only [not_nonempty_iff_eq_empty.mp hd, card_empty, Nat.zero_le]
      _ = _ := by simp [Nat.mul_comm]
  have h := card_sdiff_add_card_inter eligible matched
  have h' := card_le_card (inter_subset_right : eligible ∩ matched ⊆ matched)
  change eligible.card ≤ matched.card + b * (eligible.image bin).card
  unfold bad at hb
  omega

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 由平均负载计算基块深度

每次更新邻点时，影响范围至少缩短一层。经过 `b - a` 次更新后，各深度稳定。它们在每一点都不大于任何可行选择给出的深度，因此已有的几何计数估计仍然适用。

**英文原文**

Computing base depths from mean loads

Each neighbor update loses at least one level of influence. After
`b - a` updates the depths are stable. They are bounded pointwise by
every feasible choice, so the existing geometric count also applies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

-- 读法：`requested` 的取值由 `max a (Nat.clog 2 ⌈x⌉₊)` 给出。
def requested (a : ℕ) (x : ℝ) := max a (Nat.clog 2 ⌈x⌉₊)

-- 读法：`requested a x ≤ k` 与 `a ≤ k ∧ x ≤ (2 : ℝ) ^ k` 等价。
theorem requested_le (a k : ℕ) (x : ℝ) : requested a x ≤ k ↔ a ≤ k ∧ x ≤ (2 : ℝ) ^ k := by
  rw [requested, max_le_iff, Nat.clog_le_iff_le_pow (by decide), Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]

variable {V : Type} (E : V → Finset V) (d : V → V → ℕ) (r : V → ℕ)

-- 读法：逐一匹配以下输入模式：`0`、`t + 1`。
def iterateDepth : ℕ → V → ℕ
  | 0 => r
  | t + 1 => fun v => max (r v) ((E v).sup fun w => iterateDepth t w - 8 * d v w)

-- 读法：`r v` 不超过 `iterateDepth E d r t v`。对 `t` 分类讨论。
theorem depth_ge (t : ℕ) (v : V) : r v ≤ iterateDepth E d r t v := by
  cases t
  · exact le_rfl
  · exact le_max_left _ _

-- 读法：`iterateDepth E d r t v` 不超过 `c v`。对 `t` 作归纳，并把 `v` 保持为任意参数。
theorem depth_bounded (c : V → ℕ) (hc : ∀ v, r v ≤ c v)
    (h : ∀ v w, w ∈ E v → c w ≤ c v + 8 * d v w) (t : ℕ) (v : V) :
    iterateDepth E d r t v ≤ c v := by
  induction t generalizing v with
  | zero => exact hc v
  | succ t ih =>
    refine max_le (hc v) (Finset.sup_le fun w hw => ?_)
    exact Nat.sub_le_iff_le_add.mpr ((ih w).trans (h v w hw))

-- 读法：`iterateDepth E d r (t + 1) v` 不超过 `max (iterateDepth E d r t v) (b - (t + 1))`。对 `t` 作归纳，并把 `v` 保持为任意参数。
private theorem influence (b : ℕ) (hd : ∀ v w, w ∈ E v → 0 < d v w)
    (hr : ∀ v, r v ≤ b) (t : ℕ) (v : V) :
    iterateDepth E d r (t + 1) v ≤ max (iterateDepth E d r t v) (b - (t + 1)) := by
  induction t generalizing v with
  | zero =>
    refine max_le (le_max_left _ _) (Finset.sup_le fun w hw => le_max_of_le_right ?_)
    have h := hd _ _ hw
    have := hr w
    change r w - 8 * d v w ≤ _
    omega
  | succ t ih =>
    refine max_le ((depth_ge E d r _ v).trans (le_max_left _ _)) (Finset.sup_le fun w hw => ?_)
    have ha : iterateDepth E d r t w - 8 * d v w ≤ iterateDepth E d r (t + 1) v :=
      (le_sup (f := fun w => iterateDepth E d r t w - 8 * d v w) hw).trans (le_max_right _ _)
    have hm := ih w
    have hx := hd _ _ hw
    change iterateDepth E d r (t + 1) w - 8 * d v w ≤ _
    omega

-- 读法：`iterateDepth E d r (b - a) w` 不超过 `iterateDepth E d r (b - a) v + 8 * d v w`。
theorem depth_drop (a b : ℕ) (hd : ∀ v w, w ∈ E v → 0 < d v w)
    (hr : ∀ v, a ≤ r v ∧ r v ≤ b) (v w : V) (hw : w ∈ E v) :
    iterateDepth E d r (b - a) w ≤ iterateDepth E d r (b - a) v + 8 * d v w := by
  have hi := influence E d r b hd (fun v => (hr v).2) (b - a) v
  have hl := (hr v).1.trans (depth_ge E d r (b - a) v)
  have hs : iterateDepth E d r (b - a) w - 8 * d v w ≤ iterateDepth E d r (b - a + 1) v :=
    (le_sup (f := fun w => iterateDepth E d r (b - a) w - 8 * d v w) hw).trans (le_max_right _ _)
  omega

-- 读法：`baseDepths` 的取值由 `iterateDepth E d (requested a ∘ l) (b - a)` 给出。
def baseDepths (a b : ℕ) (l : V → ℝ) := iterateDepth E d (requested a ∘ l) (b - a)

-- 读法：结论为 `let base := baseDepths E d a b l (∀ v, a ≤ base v ∧ base v ≤ b ∧ l v ≤ (2 : ℝ) ^ (base v)) ∧ (∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u) ∧ (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, l v)`。
theorem baseDepths_spec [Fintype V]
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (a b : ℕ) (hab : a ≤ b) (l : V → ℝ) (hl : ∀ v, 0 ≤ l v ∧ l v ≤ (2 : ℝ) ^ b) :
    let base := baseDepths E d a b l
    (∀ v, a ≤ base v ∧ base v ≤ b ∧ l v ≤ (2 : ℝ) ^ (base v)) ∧
    (∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u) ∧
    (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, l v) := by
  intro base
  have hd v u (hu : u ∈ E v) : 0 < d v u := by
    let cost v := if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0
    -- 推导：记下中间结论 `ht`：`cost v ≤ 1 / 2`。
    have ht : cost v ≤ 1 / 2 := (single_le_sum (fun x _ => show 0 ≤ cost x by unfold cost; positivity)
      (mem_univ v)).trans (budget u)
    by_contra! bad
    norm_num [cost, hu, show d v u = 0 by omega] at ht
  obtain ⟨c, hc, he, hs⟩ := choose_bases E d budget a b hab l hl
  have demand v : requested a (l v) ≤ c v := (requested_le _ _ _).mpr ⟨(hc v).1, (hc v).2.2⟩
  have bound v : base v ≤ c v := depth_bounded E d _ c demand he _ _
  refine ⟨fun v => ?_, depth_drop E d _ a b hd (fun v => ⟨le_max_left _ _, (demand v).trans (hc v).2.1⟩),
    (sum_le_sum (fun v _ => pow_le_pow_right₀ (by norm_num) (bound v))).trans hs⟩
  have hx := (requested_le a (base v) (l v)).mp (depth_ge E d (requested a ∘ l) (b - a) v)
  exact ⟨hx.1, (bound v).trans (hc v).2.1, hx.2⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 为中间连线的关联历史预留单独预算

**英文原文**

Reserving a separate budget for intermediate wire incidence histories
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset

variable {F T : Type} {x y : Wire} {h u : ℕ} {L : Fringe x y T}

-- 读法：`reserve` 的取值由 `{ G with past := G.past }` 给出。
def reserve (G : HostNet F L h u) (cap discount : ℕ) :
    HostNet F { L with cap, discount } h u :=
  { G with past := G.past }

-- 读法：`G.past p` 不超过 `G.mass`。使用 `Finset.single_le_sum` 给出的结论。
theorem past_le_mass (G : HostNet F L h u) (p : G.V × Cell h) : G.past p ≤ G.mass :=
  Finset.single_le_sum (f := G.past) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

-- 读法：`G.rate * (G.past p : ℝ)` 等于 `0`。按 `G.mass ≤ L.cap` 成立与否分情况。
theorem unpaid (G : HostNet F L h u) (hc : L.cap = 0) (p : G.V × Cell h) :
    G.rate * (G.past p : ℝ) = 0 := by
  by_cases h : G.mass ≤ L.cap
  · have hp := (G.past_le_mass p).trans h
    rw [show G.past p = 0 by omega, Nat.cast_zero, mul_zero]
  · rw [rate, ite_eq_right h, zero_mul]

variable [Fintype T] (G : HostNet F L h u) {B : ℝ} {Δ D : ℕ}

-- 读法：要证明的命题是 `(G.reserve n r).Bounded Δ D B`。
theorem Bounded.start_budget (hG : G.Bounded Δ D B) (hg : G.mass = 0) (n r : ℕ) :
    (G.reserve n r).Bounded Δ D B := by
  refine ⟨hG.1, hG.2.1, fun v i => ?_⟩
  change G.V at v
  have hp : G.past (v, i) = 0 := Nat.eq_zero_of_le_zero ((G.past_le_mass _).trans_eq hg)
  have hb := hG.2.2 v i
  simp only [load, reserve, hp, Nat.cast_zero, mul_zero] at hb ⊢
  exact hb

-- 读法：要证明的命题是 `(G.reserve 0 r).Bounded Δ D B`。这里调用 `le_add_of_nonneg_right`。
theorem Bounded.drop_budget (hG : G.Bounded Δ D B) (r : ℕ) :
    (G.reserve 0 r).Bounded Δ D B := by
  refine ⟨hG.1, hG.2.1, fun v i => ?_⟩
  rw [load, unpaid _ rfl, add_zero]
  exact (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _))).trans (hG.2.2 v i)

-- 读法：`(G.past p : ℝ)` 不超过 `B * 2 ^ L.discount`。这里调用 `div_le_iff₀`。
theorem Bounded.past (hG : G.Bounded Δ D B) (hg : G.mass ≤ L.cap) (p : G.V × Cell h) :
    (G.past p : ℝ) ≤ B * 2 ^ L.discount := by
  apply (div_le_iff₀ (by positivity)).mp
  have h := hG.2.2 p.1 p.2
  rw [load, rate, ite_eq_left hg, one_div_mul_eq_div] at h
  exact (le_add_of_nonneg_left
    (add_nonneg (by positivity) (mul_nonneg L.pos.le (push_nonneg _ _ L.nonneg _)))).trans h

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# 匹配子轮实际插入的局部表

只有基本的六站点包是通过存在性选取的。其每份副本分别在自己的选择器与比特切片上求值。未匹配的比特由相等约束传输。

**英文原文**

The actual local tables inserted by a matched subround

Only the basic six-site packet is chosen by existence. Its copies
are evaluated on their own selector and bit slices. Unmatched bits
are transported by equality constraints.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Grouping
open Classical

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) {G : Diagram F a b} {z : ℕ}
  (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z)

-- 读法：两端由定义化简为同一项。
theorem expansion_pair (i : g.Choice m P) (e : m.items) (j : Fin 6) (x y : G.E → Bool)
    (u : g.Supply m P i × Fin z → Bool) :
    (g.expansion m P s hz).entry i (.inl ⟨e, j⟩) x y u =
      (P.packet z hz).rule.entry (i e) j
        (fun p => x (s.bits.symm (m.pairEdge (e, p.1), p.2)))
        (fun p => y (s.bits.symm (m.pairEdge (e, p.1), p.2)))
        (fun p => u (.inl ⟨e, p.1, (finProdFinEquiv.symm p.2).1⟩,
          (finProdFinEquiv.symm p.2).2)) := rfl

-- 读法：两端由定义化简为同一项。
theorem expansion_single (i : g.Choice m P) (v : V × Cell h) (x y : G.E → Bool)
    (u : g.Supply m P i × Fin z → Bool) :
    (g.expansion m P s hz).entry i (.inr v) x y u =
      Spectral.Packet.checkAt F (fun p : m.unpaired × Fin (P.b * z) => (src p.1, ix p.1)) v
        (fun p => x (s.bits.symm (p.1, p.2)))
        (fun p => u (.inr (p.1, (finProdFinEquiv.symm p.2).1), (finProdFinEquiv.symm p.2).2)) *
      Spectral.Packet.checkAt F (fun p : m.unpaired × Fin (P.b * z) => (dst p.1, ix p.1)) v
        (fun p => y (s.bits.symm (p.1, p.2)))
        (fun p => u (.inr (p.1, (finProdFinEquiv.symm p.2).1), (finProdFinEquiv.symm p.2).2)) := rfl

end OAI.LinearAlgebra.MatrixExponent.Packing.Grouping
end
