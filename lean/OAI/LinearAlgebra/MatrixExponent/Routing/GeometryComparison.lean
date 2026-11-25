-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Routing.Round
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometrySector
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.ScaleSlope
import OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing.Form
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryJets
import OAI.LinearAlgebra.MatrixExponent.Sphere.FusedTerms

/-!
# 局部干预的固定调度

每轮注入一个单位。即使均价较低，也采用所有在局部可行的操作。价格较高时，总节省足以支付一次完整注入的成本。调度不需要全局价格检验或打包算法。

**英文原文**

A fixed schedule of local interventions

There is one unit of injection at every round. Use all locally
available moves, even when the mean price is low. At high prices the
aggregate saving pays for an entire injection. No global price test
or packing algorithm is required by the schedule.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Stock Finset

section Run

variable {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
  (L : Finset I) (a : I → ℝ) (Q : (I → ℕ) → Intervention I E) (budget : ℝ)

-- 读法：逐一匹配以下输入模式：`0, z, v`、`k + 1, z, v`。
def Runs : ℕ → (I → ℕ) → ℝ → Prop
  | 0, z, v => v + total a z ≤ budget
  | k + 1, z, v => (Q z).take ≤ z ∧ ∀ j,
      Runs k ((Q z).next z j + copies L 1) (v + (Q z).cost j)

-- 读法：要证明的命题是 `Plan a P budget k (z + copies L k) v`。对 `k` 作归纳，并把 `z v` 保持为任意参数。
theorem Runs.plan {P : Intervention I E → Prop} (hp : ∀ z, P (Q z))
    (k : ℕ) (z : I → ℕ) (v : ℝ) (h : Runs L a Q budget k z v) :
    Plan a P budget k (z + copies L k) v := by
  induction k generalizing z v with
  | zero =>
    rw [show copies L 0 = 0 by ext i; simp [copies], add_zero]
    exact Plan.close h
  | succ k ih =>
    obtain ⟨hz, hn⟩ := h
    apply Plan.step (z := z + copies L (k + 1)) (Q z) (hp z) (fun i => (hz i).trans (Nat.le_add_right _ _))
    intro j
    have he : (Q z).next (z + copies L (k + 1)) j = ((Q z).next z j + copies L 1) + copies L k := by
      funext i
      have hh : (Q z).take i ≤ z i := hz i
      by_cases h : i ∈ L <;> simp [Intervention.next, copies, h]
      omega
    rw [he]
    exact ih _ _ (hn j)

-- 读法：要证明的命题是 `Runs L a Q budget k z v`。对 `k` 作归纳，并把 `z v` 保持为任意参数。
private theorem runs_of_change {μ : ℝ} (hμ : 0 < μ) (r : ℝ)
    (h : ∀ z, (Q z).take ≤ z ∧ ∀ j,
      potential μ a ((Q z).next z j + copies L 1) + (Q z).cost j ≤ potential μ a z + r)
    (k : ℕ) (z : I → ℕ) (v : ℝ)
    (hv : v + potential μ a z + r * k + μ * (∑ i, a i ^ 2) / 2 ≤ budget) : Runs L a Q budget k z v := by
  induction k generalizing z v with
  | zero =>
    have he : total a z ≤ potential μ a z + μ * (∑ i, a i ^ 2) / 2 := by
      simpa only [total, mul_comm] using potential_close (z := z) (a := a) hμ
    change v + total a z ≤ budget
    simp only [Nat.cast_zero, mul_zero, add_zero] at hv
    linarith
  | succ k ih =>
    obtain ⟨hq, hg⟩ := h z
    refine ⟨hq, fun j => ih _ _ ?_⟩
    rw [Nat.cast_succ] at hv
    linarith only [hv, hg j]

end Run

-- 读法：证明中先建立 `hm`，即 `m₀ ≤ 2 ^ h`。
theorem schedule (N B A m₀ : ℕ) {δ ρ C : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hC : 0 ≤ C) :
    ∃ h μ W : ℕ, m₀ ≤ 2 ^ h ∧ 0 < μ ∧ 4 ≤ W ∧
      ∀ (I E : Type) [Fintype I] [Fintype E] [DecidableEq I] (L : Finset I)
        (a : I → ℝ) (Q : (I → ℕ) → Intervention I E),
        Fintype.card I ≤ A * L.card → (∀ i, 0 ≤ a i ∧ a i ≤ A) →
        (∀ z : I → ℕ, let p := fun i => price μ (a i) (z i)
          ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (q : J → Intervention I E),
            (C * L.card < ∑ i ∈ L, p i → ρ * L.card ≤ Fintype.card J) ∧
            Intervention.Overlap q N ∧ (∀ j, (q j).Efficient p δ B (2 ^ h)) ∧
            Q z = Intervention.parallel q) →
        Runs L a Q ((C + 2) * L.card * W) W 0 0 := by
  -- 推导：从 `pow_unbounded_of_one_lt (max (m₀ : ℝ) (A / (ρ * δ))) (by norm_num : (1 : ℝ) < 2)` 中取出 `h, hh`。
  obtain ⟨h, hh⟩ := pow_unbounded_of_one_lt (max (m₀ : ℝ) (A / (ρ * δ))) (by norm_num : (1 : ℝ) < 2)
  let m : ℕ := 2 ^ h
  have hm : m₀ ≤ 2 ^ h := by exact_mod_cast ((le_max_left _ _).trans_lt hh).le
  have hpay : (A : ℝ) ≤ (m : ℝ) * (ρ * δ) := by
    simpa [m] using ((div_lt_iff₀ (mul_pos hρ hδ)).mp ((le_max_right _ _).trans_lt hh)).le
  let R := N * (B * m)
  obtain ⟨μ, hμ⟩ := exists_nat_gt (max ((R : ℝ) / δ) ((A : ℝ) * ((R : ℝ) + 1) ^ 2))
  have hsize := ((div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hμ)).le
  have herr := ((le_max_right _ _).trans_lt hμ).le
  have hμpos : (0 : ℝ) < μ := (show (0 : ℝ) ≤ _ by positivity).trans_lt hμ
  let W := μ * (A ^ 3 + 4)
  -- 推导：记下中间结论 `hW`：`4 ≤ W`。
  have hW : 4 ≤ W := (Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_left _ (Nat.cast_pos.mp hμpos))
  refine ⟨h, μ, W, hm, Nat.cast_pos.mp hμpos, hW, ?_⟩
  intro I E _ _ _ L a Q hi ha hact
  have hi' : (Fintype.card I : ℝ) ≤ A * (L.card : ℝ) := by exact_mod_cast hi
  have hl : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
  have error : (Fintype.card I : ℝ) * ((R : ℝ) + 1) ^ 2 / (2 * μ) ≤ L.card := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left herr hl, mul_nonneg hl hμpos.le,
      mul_le_mul_of_nonneg_right hi' (sq_nonneg ((R : ℝ) + 1))]
  apply runs_of_change L a Q _ hμpos ((C + 1) * L.card)
  · intro z
    let p i := price (μ : ℝ) (a i) (z i)
    -- 推导：从 `hact z` 中取出 `J, _, _, q, hd, ho, he, hq`。
    obtain ⟨J, _, _, q, hd, ho, he, hq⟩ := hact z
    rw [hq]
    obtain ⟨hz, ht⟩ := Intervention.parallel_change q (copies L 1) (M := 1)
      (by intro i; unfold copies; split <;> omega) hμpos ho he hsize
    have cost : ∑ i ∈ L, p i ≤ C * L.card + Fintype.card J * ((m : ℝ) * δ) := by
      by_cases hp : C * L.card < ∑ i ∈ L, p i
      · have hmax : ∑ i ∈ L, p i ≤ L.card * (A : ℝ) := by
          simpa using sum_le_sum (s := L) (fun i _ => (show p i ≤ (A : ℝ) from price_le.trans (ha i).2))
        linarith only [hmax, mul_nonneg hC hl, mul_le_mul_of_nonneg_left hpay hl,
          mul_le_mul_of_nonneg_right (hd hp) (by positivity : 0 ≤ (m : ℝ) * δ)]
      · exact (le_of_not_gt hp).trans (le_add_of_nonneg_right (by positivity))
    refine ⟨hz, fun j => ?_⟩
    have hg := ht j
    rw [total_copies, Nat.cast_one, one_mul] at hg
    change _ + _ + Fintype.card J * ((m : ℝ) * δ) ≤ _ + ∑ i ∈ L, p i +
      (Fintype.card I : ℝ) * ((R : ℝ) + 1) ^ 2 / (2 * μ) at hg
    linarith only [hg, error, cost]
  -- 推导：记下中间结论 `hsum`：`∑ i, a i ^ 2 ≤ L.card * (A : ℝ) ^ 3`。
  · have hsum : ∑ i, a i ^ 2 ≤ L.card * (A : ℝ) ^ 3 := calc
      _ ≤ ∑ _ : I, (A : ℝ) ^ 2 := sum_le_sum fun i _ => pow_le_pow_left₀ (ha i).1 (ha i).2 _
      _ ≤ _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        nlinarith only [mul_le_mul_of_nonneg_right hi' (sq_nonneg (A : ℝ))]
    rw [potential_zero (fun i => (ha i).1)]
    unfold W
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hsum hμpos.le, mul_nonneg hl hμpos.le,
      show 0 ≤ (L.card : ℝ) * (μ : ℝ) * (A : ℝ) ^ 3 by positivity]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 为各频率取整预留额外供给

在供给侧，为字母表中的每个符号增加一次重复。只要固定的重复次数足够大，就可以吸收这一额外开销。

**英文原文**

Reserving extra supplies to round each frequency

Add one repetition per alphabet symbol on the supply side. A large
enough fixed number of repetitions absorbs this slack.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Proposal

open Spectral Stock Finset

variable {K S I E J : Type} [Field K] [Fintype S] [Fintype J]
  [DecidableEq I] [DecidableEq E] [DecidableEq J] {T : J → Tensor K S} {H : ℝ}
  (q : Proposal T H) (g : J → I ⊕ E) (u : Finset J) (m : ℕ)

-- 读法：`flex` 的取值由 `{ q.trade g u (m + Fintype.card q.move.letter) with take := (q.trade g u m).take }` 给出。
/-- 库存消耗不变，结果和供给均留有取整余量。

英文原文：Stock consumption is unchanged. Outcomes and supplies have rounding room.
-/
def flex : Intervention I E :=
  { q.trade g u (m + Fintype.card q.move.letter) with take := (q.trade g u m).take }

-- 读法：存在 `j`，`g j` 等于 `.inl i`。这里调用 `q.trade_support`。
theorem flex_support {i : I} (h : (q.flex g u m).affects i) : ∃ j, g j = .inl i := by
  rcases h with h | h
  · exact q.trade_support g u m (.inl h)
  · exact q.trade_support g u _ (.inr h)

variable [Fintype I] [Fintype E]

-- 读法：要证明的命题是 `(q.flex g u m).Efficient p (δ / 2) (2 * B) m`。
theorem flex_efficient (hg : Function.Injective g)
    (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i)
    (hu : ∀ j ∈ u, ∃ e, g j = .inr e) (hc : (u.card : ℝ) ≤ H)
    {p : I → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : q.Works δ (Sum.elim p (fun _ => 1) ∘ g))
    {B : ℕ} (hb : q.move.block ≤ B) (ho : ∀ j, ∑ k, q.move.count j k ≤ B)
    (hm : Fintype.card q.move.letter ≤ m)
    (hm' : (Fintype.card q.move.letter : ℝ) * q.move.block *
      (∑ j ∈ q.demand, (Sum.elim p (fun _ => 1) ∘ g) j) ≤ m * (δ / 2)) :
    (q.flex g u m).Efficient p (δ / 2) (2 * B) m := by
  let k := Fintype.card q.move.letter
  have he (n) := q.trade_efficient g u n hg hd hu hc hδ hw hb ho
  constructor
  · intro i
    -- 推导：从 `(he m).1 i` 中取出 `hi, hk`。
    obtain ⟨hi, hk⟩ := (he m).1 i
    exact ⟨hi.trans (by rw [mul_assoc]; omega), fun e => (half_le_self hδ).trans (hk e)⟩
  intro j
  obtain ⟨hi, hs⟩ := (he (m + k)).2 j
  refine ⟨fun i => (hi i).trans ?_, ?_⟩
  · calc
      _ ≤ B * (m + m) := Nat.mul_le_mul_left B (Nat.add_le_add_left hm _)
      _ = _ := by ring
  let v := ∑ j ∈ q.demand, (Sum.elim p (fun _ => 1) ∘ g) j
  have cost (n : ℕ) : total p (q.trade g u n).take = (q.move.block * n : ℕ) * v := by
    unfold v
    rw [← total_copies, ← total_collect, total_split]
    simp only [q.take_core g n hd, sum_const_zero, Nat.cast_zero, add_zero]
    rfl
  change total p ((q.trade g u (m + k)).put j) + (q.trade g u (m + k)).cost j + _ ≤
    total p (q.trade g u m).take
  rw [cost] at hs ⊢
  change (k : ℝ) * q.move.block * v ≤ m * (δ / 2) at hm'
  push_cast at hs ⊢
  linarith only [hs, hm', mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hδ]

end OAI.LinearAlgebra.MatrixExponent.Routing.Proposal
end

/-!
# 插值与中点判据

由细分和唯一性得到等速性。将线段参数加倍，可以把距离平方比较中的最大缺陷减半。

**英文原文**

Interpolation and the midpoint criterion

Subdivision and uniqueness give constant speed. Doubling a segment
parameter halves the maximal defect in squared-distance comparison.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {Y : Type*} [PseudoMetricSpace Y] (h : Busemann Y) (s : Segments Y)

-- 读法：`Segments.pt` 的取值由 `(s t x y).choose` 给出。
def Segments.pt (t : Fraction) (x y : Y) : Y := (s t x y).choose

-- 读法：要证明的命题是 `Divides t x y (s.pt t x y)`。
theorem Segments.divides (t : Fraction) (x y : Y) : Divides t x y (s.pt t x y) :=
  (s t x y).choose_spec

-- 读法：要证明的命题是 `Divides t.rev y x m`。
theorem Divides.rev {x y m : Y} {t : Fraction} (hm : Divides t x y m) :
    Divides t.rev y x m := by
  simp only [Divides, Fraction.rev, sub_sub_cancel, dist_comm y m, dist_comm y x, dist_comm m x]
  exact ⟨hm.2, hm.1⟩

include h s in
-- 读法：要证明的命题是 `Divides v x b a`。这里调用 `Divides.of_le`。
theorem nested {x y a b : Y} {t u v : Fraction} (ha : Divides t x y a)
    (hb : Divides u x y b) (he : t.val = v.val * u.val) : Divides v x b a := by
  obtain ⟨m, hm⟩ := s v x b
  have hm' : Divides t x y m := by
    apply Divides.of_le
    · rw [hm.1, hb.1, he, mul_assoc]
    · have hd := dist_triangle m b y
      rw [hm.2, hb.1, hb.2] at hd
      rw [he]
      linarith only [hd]
  exact hm.replace (h.unique hm' ha)

include h s in
-- 读法：`dist a b` 等于 `|t.val - u.val| * dist x y`。
theorem speed {x y a b : Y} {t u : Fraction} (ha : Divides t x y a)
    (hb : Divides u x y b) : dist a b = |t.val - u.val| * dist x y := by
  wlog hle : t.val ≤ u.val generalizing a b t u
  · rw [dist_comm, abs_sub_comm]
    exact this hb ha (le_of_not_ge hle)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  rcases u.2.1.eq_or_lt with hz | hp
  · have he : t = u := Subtype.ext (le_antisymm hle (hz ▸ t.2.1))
    subst t
    rw [h.unique ha hb, sub_self, neg_zero, zero_mul]
  let v : Fraction := ⟨t.val / u.val, div_nonneg t.2.1 hp.le, (div_le_one hp).mpr hle⟩
  have he : t.val = v.val * u.val := (div_mul_cancel₀ _ hp.ne').symm
  rw [(nested h s ha hb he).2, hb.1, he]
  ring

include h in
-- 读法：`u.val * dist (s.pt t x y) (s.pt t x z)` 不超过 `t.val * dist (s.pt u x y) (s.pt u x z)`。这里调用 `mul_nonneg`。
theorem Segments.radial (x y z : Y) {t u : Fraction} (hle : t.val ≤ u.val) :
    u.val * dist (s.pt t x y) (s.pt t x z) ≤ t.val * dist (s.pt u x y) (s.pt u x z) := by
  rcases u.2.1.eq_or_lt with hz | hp
  · rw [← hz, zero_mul]
    exact mul_nonneg t.2.1 dist_nonneg
  let v : Fraction := ⟨t.val / u.val, div_nonneg t.2.1 hp.le, (div_le_one hp).mpr hle⟩
  have he : t.val = v.val * u.val := (div_mul_cancel₀ _ hp.ne').symm
  have hv (w : Y) := nested h s (s.divides t x w) (s.divides u x w) he
  have hh := h v _ _ _ _ _ _ (hv y) (hv z)
  rw [dist_self, mul_zero, zero_add] at hh
  rw [he]
  linarith only [mul_le_mul_of_nonneg_left hh hp.le]

-- 读法：`half` 的结果类型为 `Fraction`。
def half : Fraction := ⟨1 / 2, by norm_num, by norm_num⟩

-- 读法：`MidpointBound` 表示以下条件：对每个 `x y m : Y`，由 `Divides half x y m` 推出 `Along half x y m`。
def MidpointBound (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ x y m : Y, Divides half x y m → Along half x y m

-- 读法：`excess` 的取值由 `dist m z ^ 2 - (1 - t.val) * dist x z ^ 2 - t.val * dist y z ^ 2 + t.val * (1 - t.val) * dist x y ^ 2` 给出。
private def excess (x y z m : Y) (t : Fraction) :=
  dist m z ^ 2 - (1 - t.val) * dist x z ^ 2 - t.val * dist y z ^ 2 +
    t.val * (1 - t.val) * dist x y ^ 2

-- 读法：`excess y x z m t.rev` 等于 `excess x y z m t`。
private theorem excess_rev (x y z m : Y) (t : Fraction) :
    excess y x z m t.rev = excess x y z m t := by
  unfold excess Fraction.rev
  rw [dist_comm y x]
  ring

include h s in
-- 读法：存在 `b u`，`Divides u x y b` 与 `2 * excess x y z m t ≤ excess x y z b u` 同时成立。
private theorem double_excess (hm : MidpointBound Y) (x y z m : Y) (t : Fraction)
    (ht : Divides t x y m) (hle : t.val ≤ 1 / 2) :
    ∃ b u, Divides u x y b ∧ 2 * excess x y z m t ≤ excess x y z b u := by
  let u : Fraction := ⟨2 * t.val, mul_nonneg (by norm_num) t.2.1, by linarith⟩
  obtain ⟨b, hb⟩ := s u x y
  have he : t.val = half.val * u.val := by dsimp [u, half]; ring
  have hh := hm x b m (nested h s ht hb he) z
  rw [hb.1] at hh
  refine ⟨b, u, hb, ?_⟩
  dsimp only [excess, half, u] at hh ⊢
  linarith only [hh]

include h s in
-- 读法：要证明的命题是 `Along t x y m`。
theorem MidpointBound.all (hm : MidpointBound Y) {x y m : Y} {t : Fraction}
    (ht : Divides t x y m) : Along t x y m := by
  intro z
  let E := {a : ℝ | ∃ b u, Divides u x y b ∧ a = excess x y z b u}
  have ht' : excess x y z m t ∈ E := ⟨m, t, ht, rfl⟩
  have hbd : BddAbove E := by
    refine ⟨(dist x y + dist x z) ^ 2 + dist x y ^ 2, ?_⟩
    rintro _ ⟨b, u, hb, rfl⟩
    have hu := u.2.1
    have hu' := sub_nonneg.mpr u.2.2
    -- 推导：记下中间结论 `hd`：`dist b z ≤ dist x y + dist x z`。
    have hd : dist b z ≤ dist x y + dist x z := by
      have := dist_triangle b x z
      rw [dist_comm b x, hb.1] at this
      linarith [mul_nonneg hu' (dist_nonneg (x := x) (y := y))]
    have he : u.val * (1 - u.val) ≤ 1 := by nlinarith
    unfold excess
    linarith only [pow_le_pow_left₀ dist_nonneg hd 2, mul_nonneg hu' (sq_nonneg (dist x z)),
      mul_nonneg hu (sq_nonneg (dist y z)), mul_le_mul_of_nonneg_right he (sq_nonneg (dist x y))]
  have hsup : sSup E ≤ sSup E / 2 := by
    apply csSup_le ⟨_, ht'⟩
    rintro _ ⟨b, u, hb, rfl⟩
    by_cases hu : u.val ≤ 1 / 2
    -- 推导：从 `double_excess h s hm x y z b u hb hu` 中取出 `c, v, hc, he`。
    · obtain ⟨c, v, hc, he⟩ := double_excess h s hm x y z b u hb hu
      exact (le_div_iff₀ (by norm_num)).mpr (by linarith [le_csSup hbd ⟨c, v, hc, rfl⟩])
    · have hu' : u.rev.val ≤ 1 / 2 := by change 1 - u.val ≤ _; linarith
      obtain ⟨c, v, hc, he⟩ := double_excess h s hm y x z b u.rev hb.rev hu'
      rw [excess_rev, ← excess_rev y x z c] at he
      linarith [le_csSup hbd ⟨c, v.rev, hc.rev, rfl⟩]
  have he := le_csSup hbd ht'
  unfold excess at he
  linarith only [hsup, he]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 仿射扇形上的距离

将两端点沿平行线段同时滑动，其间距离不变。由此可在整个坐标平面上定义一个半范数，包括扇形退化为直线的情形。

**英文原文**

Distances on affine sectors

Sliding both endpoints along parallel segments does not change their
distance. This gives a seminorm on the whole coordinate plane, also
when the sector collapses to a line.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {Y : Type*} [PseudoMetricSpace Y] {F : Coord → Y}

-- 读法：`dist (F a) (F b)` 不超过 `dist (F x) (F y)`。这里调用 `le_of_forall_pos_le_add`。
private theorem slide_le (hf : AffineSector F) (hb : Busemann Y)
    {a b x y : Coord} (ha : 0 ≤ a) (hb' : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : a - b = x - y) : dist (F a) (F b) ≤ dist (F x) (F y) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let M := dist (F a) (F x) + dist (F b) (F y) + 1
  have hM : 0 < M := by unfold M; positivity
  let t : Fraction := ⟨min 1 (ε / M), (lt_min zero_lt_one (div_pos hε hM)).le, min_le_left _ _⟩
  have ht : 0 < t.val := lt_min zero_lt_one (div_pos hε hM)
  have heps : t.val * M ≤ ε := (le_div_iff₀ hM).mp (min_le_right _ _)
  let A := mix t a x
  let B := mix t b y
  -- 推导：记下中间结论 `hA`：`0 ≤ A`。
  have hA : 0 ≤ A := add_nonneg (smul_nonneg (sub_nonneg.mpr t.2.2) ha) (smul_nonneg ht.le hx)
  have hB : 0 ≤ B := add_nonneg (smul_nonneg (sub_nonneg.mpr t.2.2) hb') (smul_nonneg ht.le hy)
  have hh : mix t A B = mix t a y := by
    have eqb : b = a - x + y := by rw [show a - x + y = a - (x - y) by abel, ← he]; abel
    unfold A B mix
    rw [eqb]
    module
  have h₁ := hf t a x ha hx
  have h₂ := hf t b y hb' hy
  have hd : dist (F A) (F B) ≤ dist (F x) (F y) := by
    apply le_of_mul_le_mul_left _ ht
    rw [← (hf t A B hA hB).1, hh]
    simpa only [dist_self, mul_zero, zero_add] using hb t _ _ _ _ _ _ h₁ (hf t a y ha hy)
  have ht' := dist_triangle4 (F a) (F A) (F B) (F b)
  rw [dist_comm (F B), h₁.1, h₂.1] at ht'
  unfold M at heps
  linarith

-- 读法：`dist (F a) (F b)` 等于 `dist (F x) (F y)`。使用 `le_antisymm` 给出的结论。
/-- 共同平移到象限内会诱导相同的距离。

英文原文：A common translation into the quadrant induces the same distance.
-/
private theorem same_length (hf : AffineSector F) (hb : Busemann Y)
    {a b x y : Coord} (ha : 0 ≤ a) (hb' : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : a - b = x - y) : dist (F a) (F b) = dist (F x) (F y) :=
  le_antisymm (slide_le hf hb ha hb' hx hy he) (slide_le hf hb hx hy ha hb' he.symm)

-- 读法：存在 `z`，对每个 `x ∈ s`，`0` 不超过 `x + z`。
private theorem translate (s : Finset Coord) : ∃ z, ∀ x ∈ s, 0 ≤ x + z := by
  obtain ⟨y, hy⟩ := s.finite_toSet.bddBelow
  exact ⟨-y, fun x hx => by rw [← sub_eq_add_neg]; exact sub_nonneg.mpr (hy hx)⟩

-- 读法：存在 `p : Seminorm ℝ Coord`，对每个 `x y : Coord`，由 `0 ≤ x` 推出 `0 ≤ y → p (x - y) = dist (F x) (F y)`。
theorem AffineSector.seminorm (hf : AffineSector F) (hb : Busemann Y) :
    ∃ p : Seminorm ℝ Coord, ∀ x y : Coord, 0 ≤ x → 0 ≤ y → p (x - y) = dist (F x) (F y) := by
  have hdec (x : Coord) : ∃ a b : Coord, 0 ≤ a ∧ 0 ≤ b ∧ x = a - b := by
    obtain ⟨z, hz⟩ := translate {0, x}
    exact ⟨x + z, z, hz _ (by simp), by simpa using hz 0 (by simp), by abel⟩
  choose a b ha hb' heq using hdec
  let p := fun x => dist (F (a x)) (F (b x))
  have hp (x y : Coord) (hx : 0 ≤ x) (hy : 0 ≤ y) : p (x - y) = dist (F x) (F y) :=
    same_length hf hb (ha _) (hb' _) hx hy (heq _).symm
  have hneg (x : Coord) : p (-x) = p x := by
    rw [heq x, neg_sub, hp _ _ (hb' _) (ha _), hp _ _ (ha _) (hb' _), dist_comm]
  have hadd (x y : Coord) : p (x + y) ≤ p x + p y := by
    -- 推导：从 `translate {0, x, x + y}` 中取出 `z, hz`。
    obtain ⟨z, hz⟩ := translate {0, x, x + y}
    have hz' : 0 ≤ z := by simpa using hz 0 (by simp)
    have hx := hz x (by simp)
    have hy := hz (x + y) (by simp)
    have h := dist_triangle (F (x + y + z)) (F (x + z)) (F z)
    rw [← hp _ _ hy hz', ← hp _ _ hy hx, ← hp _ _ hx hz'] at h
    rwa [add_sub_cancel_right, show x + y + z - (x + z) = y by abel, add_sub_cancel_right, add_comm (p y)] at h
  have hsmul (t : Fraction) (x : Coord) : p (t.val • x) = t.val * p x := by
    have h := (hf t (b x) (a x) (hb' x) (ha x)).1
    have hy : 0 ≤ mix t (b x) (a x) :=
      add_nonneg (smul_nonneg (sub_nonneg.mpr t.2.2) (hb' x)) (smul_nonneg t.2.1 (ha x))
    -- 推导：记下中间结论 `he`：`mix t (b x) (a x) - b x = t.val • x`。
    have he : mix t (b x) (a x) - b x = t.val • x := by
      rw [show t.val • x = t.val • (a x - b x) by rw [← heq]]
      unfold mix
      module
    rw [dist_comm (F (b x)), ← hp _ _ hy (hb' x), he, dist_comm (F (b x))] at h
    exact h
  have hpos (r : ℝ) (hr : 0 ≤ r) (x : Coord) : p (r • x) = r * p x := by
    rcases le_total r 1 with hl | hl
    · exact hsmul ⟨r, hr, hl⟩ x
    have h₀ : r ≠ 0 := (zero_lt_one.trans_le hl).ne'
    have h := hsmul ⟨r⁻¹, inv_nonneg.mpr hr, inv_le_one_of_one_le₀ hl⟩ (r • x)
    dsimp only at h
    rw [inv_smul_smul₀ h₀] at h
    rw [h, mul_inv_cancel_left₀ h₀]
  refine ⟨Seminorm.of p hadd ?_, hp⟩
  intro r x
  rw [Real.norm_eq_abs]
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, hpos r hr]
  · rw [abs_of_nonpos hr, ← hpos (-r) (neg_nonneg.mpr hr), neg_smul, hneg]

-- 读法：要证明的命题是 `CutBound (fun x y => p (x - y))`。
theorem sector_cuts (h : CutBound (dist : Y → Y → ℝ)) (p : Seminorm ℝ Coord)
    (hf : ∀ x y : Coord, 0 ≤ x → 0 ≤ y → p (x - y) = dist (F x) (F y)) :
    CutBound (fun x y => p (x - y)) := by
  intro x x' y y' z z' w w' t u α β ht hu hα hβ hh
  let S : Finset Coord := {x, x', y, y', z, z', w, w'}
  obtain ⟨a, ha⟩ := translate S
  let f := fun v => F (v + a)
  have he (v v' : Coord) (hv : v ∈ S) (hv' : v' ∈ S) :
      dist (f v) (f v') = p (v - v') := by
    rw [← hf _ _ (ha v hv) (ha v' hv'), add_sub_add_right_eq_sub]
  have H := h (f x) (f x') (f y) (f y') (f z) (f z') (f w) (f w') t u α β ht hu hα hβ hh
  simpa (disch := simp [S]) only [he] using H

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 三条射线的比较

平行四边形恒等式使二阶差分沿坐标轴的整数平移保持不变。对于两条相反射线，再用三角不等式控制一次项系数。

**英文原文**

Comparison for three rays

The parallelogram law makes the second differences constant along
integer translates of an axis. For opposite rays the triangle
inequality then controls the linear coefficient.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

-- 读法：`p ((n : ℝ) • x - y) ^ 2` 等于 `n * p (x - y) ^ 2 + n * ((n : ℝ) - 1) * p x ^ 2 - ((n : ℝ) - 1) * p y ^ 2`。对 `n` 作归纳，采用 `Nat.twoStepInduction` 的归纳原则。
private theorem quadratic (p : Seminorm ℝ Coord) (hc : CutBound (fun x y => p (x - y)))
    (x y : Coord) (n : ℕ) :
    p ((n : ℝ) • x - y) ^ 2 =
      n * p (x - y) ^ 2 + n * ((n : ℝ) - 1) * p x ^ 2 - ((n : ℝ) - 1) * p y ^ 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have h := parallelogram_of_cuts p hc (((n : ℝ) + 1) • x - y) x
    have he : ((n : ℝ) + 1) • x - y + x = ((n : ℝ) + 2) • x - y := by module
    have he' : ((n : ℝ) + 1) • x - y - x = (n : ℝ) • x - y := by module
    push_cast at h₁ ⊢
    rw [he, he', h₀, h₁] at h
    linarith only [h]

variable {Y : Type*} [PseudoMetricSpace Y]

-- 读法：`dist x y` 等于 `dist z t`。
theorem dist_match {x y z t : Y} (h : dist x z = 0) (h' : dist y t = 0) :
    dist x y = dist z t := by
  linarith only [h, h', dist_triangle4 x z t y, dist_triangle4 z x y t, dist_comm x z, dist_comm y t]

-- 读法：`dist (a n) (b 1) ^ 2` 等于 `n * c ^ 2 + n * ((n : ℝ) - 1) * A ^ 2 - ((n : ℝ) - 1) * B ^ 2`。
theorem ray_polynomial (h : Busemann Y) (hs : Segments Y) (hc : CutBound (@dist Y _))
    {a b : ℝ → Y} {A B c : ℝ} (ha : Ray a A) (hb : Ray b B)
    (he : ∀ r, 0 ≤ r → dist (a r) (b r) = r * c) (n : ℕ) :
    dist (a n) (b 1) ^ 2 = n * c ^ 2 + n * ((n : ℝ) - 1) * A ^ 2 - ((n : ℝ) - 1) * B ^ 2 := by
  obtain ⟨F, hF, hab⟩ := exists_sector h hs ha hb he
  obtain ⟨p, hp⟩ := hF.seminorm h
  have h₁ (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
      p ((r, 0) - (0, s)) = dist (a r) (b s) :=
    (hp (r, 0) (0, s) ⟨hr, le_rfl⟩ ⟨le_rfl, hs⟩).trans (dist_match (hab r hr).1 (hab s hs).2)
  have h₀ : dist (a 0) (b 0) = 0 := by simpa using he 0 le_rfl
  -- 推导：记下中间结论 `hA`：`p (1, 0) = A`。
  have hA : p (1, 0) = A := by
    have hx := h₁ 1 0 zero_le_one le_rfl
    rw [← dist_match (dist_self (a 1)) h₀, ha 1 0 zero_le_one le_rfl] at hx
    simpa using hx
  have hB : p (0, 1) = B := by
    have hx := h₁ 0 1 le_rfl zero_le_one
    rw [dist_match h₀ (dist_self (b 1)), hb 0 1 le_rfl zero_le_one] at hx
    change p (0 - (0, 1)) = _ at hx
    rw [zero_sub, map_neg_eq_map] at hx
    simpa using hx
  have H := quadratic p (sector_cuts hc p hp) (1, 0) (0, 1) n
  rw [show (n : ℝ) • ((1, 0) : Coord) = ((n : ℝ), 0) by simp,
    h₁ _ _ (by positivity) zero_le_one, h₁ _ _ zero_le_one zero_le_one, he 1 zero_le_one,
    one_mul, hA, hB] at H
  exact H

-- 读法：`2 * (A ^ 2 + B ^ 2)` 不超过 `X ^ 2 + Z ^ 2`。
/-- 无穷小几何中在公共原点处的中点比较。

英文原文：Midpoint comparison at the common origin in the infinitesimal geometry.
-/
theorem opposite_rays (h : Busemann Y) (hs : Segments Y) (hc : CutBound (@dist Y _))
    {a b z : ℝ → Y} {A B X Z : ℝ} (ha : Ray a A) (hb : Ray b A) (hz : Ray z B)
    (ho : ∀ r, 0 ≤ r → dist (a r) (b r) = 2 * r * A)
    (hx : ∀ r, 0 ≤ r → dist (a r) (z r) = r * X)
    (hy : ∀ r, 0 ≤ r → dist (b r) (z r) = r * Z) :
    2 * (A ^ 2 + B ^ 2) ≤ X ^ 2 + Z ^ 2 := by
  by_contra! bad
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * B ^ 2 / (2 * (A ^ 2 + B ^ 2) - (X ^ 2 + Z ^ 2)))
  rw [div_lt_iff₀ (sub_pos.mpr bad)] at hn
  have hh := pow_le_pow_left₀ dist_nonneg (dist_triangle (a n) (z 1) (b n)) 2
  rw [ho _ (Nat.cast_nonneg _), dist_comm (z 1)] at hh
  linarith only [hh, hn, ray_polynomial h hs hc ha hz hx n, ray_polynomial h hs hc hb hz hy n,
    sq_nonneg (dist (a n) (z 1) - dist (b n) (z 1))]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 由缩放后的线段距离得到无穷小射线

由 Busemann 凸性，两条曲线上相同时刻的点间距离除以已过时间后所得之比单调不减。因此极限斜率与取极限时采用的参数化无关。

**英文原文**

Infinitesimal rays from scaled segment distances

The distance of two equal-time points, divided by elapsed time,
is nondecreasing by Busemann convexity. Its limiting slope is
therefore independent of the parametrization used in the limit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Filter
open scoped Topology

-- 读法：`time` 的结果类型为 `Fraction`。
private def time (n : ℕ) (r : ℝ) : Fraction :=
  if h : 0 ≤ r ∧ r ≤ (n : ℝ) + 1
  then ⟨r / (n + 1), div_nonneg h.1 (by positivity), (div_le_one (by positivity)).mpr h.2⟩
  else ⟨0, le_rfl, zero_le_one⟩

-- 读法：`((n : ℝ) + 1) * (time n r).val` 等于 `r`。这里调用 `mul_div_cancel₀`。
private theorem time_scale {n : ℕ} {r : ℝ} (h : 0 ≤ r ∧ r ≤ (n : ℝ) + 1) :
    ((n : ℝ) + 1) * (time n r).val = r := by
  rw [time, dite_eq_left h]
  exact mul_div_cancel₀ _ (by positivity)

-- 读法：对每个 `ᶠ n : ℕ in atTop`，`r` 不超过 `(n : ℝ) + 1`。这里调用 `hN.le.trans`。
private theorem eventually_large (r : ℝ) : ∀ᶠ n : ℕ in atTop, r ≤ (n : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt r
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hN.le.trans (Nat.cast_le.mpr hn)).trans (le_add_of_nonneg_right zero_le_one)

variable {Y Z : Type} [PseudoMetricSpace Y] [PseudoMetricSpace Z]

-- 读法：`rescale` 的取值由 `s.pt (time n p.2) o p.1` 给出。
def rescale (s : Segments Y) (o : Y) (n : ℕ) (p : Y × ℝ) := s.pt (time n p.2) o p.1

-- 读法：存在 `D : ℝ`，对每个 `n : ℕ`，`((n : ℝ) + 1) * dist (rescale s o n p) o` 不超过 `D`。这里调用 `mul_le_mul_of_nonneg_right`。
theorem rescale_bound (s : Segments Y) (o : Y) (p : Y × ℝ) :
    ∃ D : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) * dist (rescale s o n p) o ≤ D := by
  refine ⟨|p.2| * dist o p.1, fun n => ?_⟩
  unfold rescale
  rw [dist_comm, (s.divides _ _ _).1, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  by_cases h : 0 ≤ p.2 ∧ p.2 ≤ (n : ℝ) + 1
  · rw [time_scale h]; exact le_abs_self _
  · simp only [time, dite_eq_right h, mul_zero]; exact abs_nonneg _

-- 读法：`Rescaled` 表示以下条件：对每个 `a b`，`(fun n : ℕ => ((n : ℝ) + 1) * dist (rescale s o n a) (rescale s o n b))` 沿滤子 `v` 收敛到 `(dist (g a) (g b))`。
def Rescaled (s : Segments Y) (o : Y) (g : Y × ℝ → Z) (v : Filter ℕ) : Prop :=
  ∀ a b, Tendsto (fun n : ℕ => ((n : ℝ) + 1) * dist (rescale s o n a) (rescale s o n b))
    v (𝓝 (dist (g a) (g b)))

namespace Rescaled

variable {s : Segments Y} {o : Y} {g : Y × ℝ → Z} {v : Filter ℕ} [v.NeBot]
  (h : Rescaled s o g v) (hv : v ≤ atTop) (hb : Busemann Y)

include h hv hb in
-- 读法：要证明的命题是 `Ray (fun r => g (x, r)) (dist o x)`。这里调用 `tendsto_const_nhds.congr'`。
theorem ray (x : Y) : Ray (fun r => g (x, r)) (dist o x) := by
  intro r t hr ht
  refine tendsto_nhds_unique (h (x, r) (x, t)) ?_
  apply tendsto_const_nhds.congr'
  filter_upwards [hv (eventually_large r), hv (eventually_large t)] with n hn hn'
  simp only [rescale]
  rw [speed hb s (s.divides _ _ _) (s.divides _ _ _), ← mul_assoc,
    show ((n : ℝ) + 1) * |(time n r).val - (time n t).val| =
      |((n : ℝ) + 1) * ((time n r).val - (time n t).val)| by rw [abs_mul, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)],
    mul_sub, time_scale ⟨hr, hn⟩, time_scale ⟨ht, hn'⟩]

include h hv hb in
-- 读法：`u.val * dist (g (x, r)) (g (y, r))` 不超过 `r * dist (s.pt u o x) (s.pt u o y)`。这里调用 `le_of_tendsto`。
private theorem lower (x y : Y) {r : ℝ} (hr : 0 ≤ r) (u : Fraction) (hu : 0 < u.val) :
    u.val * dist (g (x, r)) (g (y, r)) ≤ r * dist (s.pt u o x) (s.pt u o y) := by
  apply le_of_tendsto ((h (x, r) (y, r)).const_mul u.val)
  filter_upwards [hv (eventually_large r), hv (eventually_large (r / u.val))] with n hn hn'
  rw [div_le_iff₀ hu] at hn'
  have he := time_scale ⟨hr, hn⟩
  have hl : (time n r).val ≤ u.val :=
    le_of_mul_le_mul_left (he.le.trans hn') (by positivity)
  have hd := mul_le_mul_of_nonneg_left (Segments.radial hb s o x y hl)
    (show 0 ≤ (n : ℝ) + 1 by positivity)
  rw [← mul_assoc _ (time n r).val, he, mul_left_comm] at hd
  exact hd

include h hv hb in
-- 读法：`t * dist (g (x, r)) (g (y, r))` 不超过 `r * dist (g (x, t)) (g (y, t))`。这里调用 `ge_of_tendsto`。
private theorem slope (x y : Y) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    t * dist (g (x, r)) (g (y, r)) ≤ r * dist (g (x, t)) (g (y, t)) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_mul]; exact mul_nonneg hr dist_nonneg
  apply ge_of_tendsto ((h (x, t) (y, t)).const_mul r)
  filter_upwards [hv (eventually_large t)] with n hn
  have he := time_scale ⟨ht.le, hn⟩
  have hu : 0 < (time n t).val := by
    apply pos_of_mul_pos_right (he.symm ▸ ht) (by positivity)
  have hd := mul_le_mul_of_nonneg_left (h.lower hv hb x y hr _ hu)
    (show 0 ≤ (n : ℝ) + 1 by positivity)
  rw [← mul_assoc, he, mul_left_comm] at hd
  exact hd

include h hv hb in
-- 读法：`dist (g (x, r)) (g (y, r))` 等于 `r * dist (g (x, 1)) (g (y, 1))`。这里调用 `le_antisymm`。
theorem linear (x y : Y) (r : ℝ) (hr : 0 ≤ r) :
    dist (g (x, r)) (g (y, r)) = r * dist (g (x, 1)) (g (y, 1)) := by
  simpa only [one_mul] using le_antisymm (h.slope hv hb x y hr zero_le_one)
    (h.slope hv hb x y zero_le_one hr)

include h hb in
-- 读法：`dist (g (x, 1)) (g (y, 1))` 不超过 `dist x y`。这里调用 `le_of_tendsto'`。
theorem contract (x y : Y) : dist (g (x, 1)) (g (y, 1)) ≤ dist x y := by
  apply le_of_tendsto' (h (x, 1) (y, 1))
  intro n
  let t := time n 1
  have he : ((n : ℝ) + 1) * t.val = 1 := time_scale ⟨zero_le_one, by linarith⟩
  have hh := hb t _ _ _ _ _ _ (s.divides t o x) (s.divides t o y)
  rw [dist_self, mul_zero, zero_add] at hh
  simpa only [rescale, ← mul_assoc, he, one_mul] using
    mul_le_mul_of_nonneg_left hh (show 0 ≤ (n : ℝ) + 1 by positivity)

include h hb in
-- 读法：`dist (g (x, 1)) (g (y, 1))` 等于 `dist x y`。
theorem opposite {x y : Y} (heq : dist x o + dist o y = dist x y) :
    dist (g (x, 1)) (g (y, 1)) = dist x y := by
  refine le_antisymm (h.contract hb _ _) (ge_of_tendsto' (h (x, 1) (y, 1)) ?_)
  intro n
  let t := time n 1
  have he : ((n : ℝ) + 1) * t.val = 1 := time_scale ⟨zero_le_one, by linarith⟩
  have hh := dist_triangle4 x (s.pt t o x) (s.pt t o y) y
  rw [dist_comm x (s.pt t o x), (s.divides t o x).2, (s.divides t o y).2,
    dist_comm o x, ← heq] at hh
  have hd : t.val * dist x y ≤ dist (s.pt t o x) (s.pt t o y) := by rw [← heq]; linarith
  simpa only [rescale, ← mul_assoc, he, one_mul] using
    mul_le_mul_of_nonneg_left hd (show 0 ≤ (n : ℝ) + 1 by positivity)

end Rescaled
end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 谱距离平方的比较

以公共原点为中心将三条线段放大。在极限中，前两条射线方向相反，每对射线都张成一个仿射扇形。平移交叉定理推出这些扇形满足平行四边形恒等式。对相反射线作比较，在原空间中得到中点不等式，继而得到对每一分点比例成立的不等式。

**英文原文**

Spectral squared-distance comparison

Blow up three segments about their common origin. In the limit the
first two rays are opposite, and each pair spans an affine sector.
The shifted crossing theorem forces the parallelogram law on these
sectors. The comparison for opposite rays gives the midpoint
inequality downstairs, which implies the inequality at every fraction.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Filter

-- 读法：要证明的命题是 `MidpointBound Y`。
theorem WireModels.midpoints {K Y : Type} [Field K] [PseudoMetricSpace Y]
    (h : WireModels K Y) (s : Segments Y) : MidpointBound Y := by
  intro x y m hm z
  let v := Ultrafilter.of (atTop : Filter ℕ)
  have hv : (v : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Z, _, g, hg, hs, hu⟩ := h.zoom s m (rescale s m) (rescale_bound s m) v
  change Rescaled s m g v at hu
  have hb := h.busemann
  have hx := hm.1
  have hy := hm.2
  dsimp only [half] at hx hy ⊢
  -- 推导：记下中间结论 `he`：`dist m y = dist m x`。
  have he : dist m y = dist m x := by rw [dist_comm m x]; linarith
  have ho := hu.opposite hb (show dist x m + dist m y = dist x y by linarith)
  have hy' := hu.ray hv hb y
  rw [he] at hy'
  have hc (t : ℝ) (ht : 0 ≤ t) : dist (g (x, t)) (g (y, t)) = 2 * t * dist m x := by
    rw [hu.linear hv hb _ _ t ht, ho, dist_comm m x, hx]
    ring
  have hbnd := opposite_rays hg.busemann hs (hg.cuts (Sphere.shifted_crossing K))
    (hu.ray hv hb x) hy' (hu.ray hv hb z) hc (hu.linear hv hb x z) (hu.linear hv hb y z)
  rw [dist_comm m x, hx] at hbnd
  linarith only [hbnd, pow_le_pow_left₀ dist_nonneg (hu.contract hb x z) 2,
    pow_le_pow_left₀ dist_nonneg (hu.contract hb y z) 2]

-- 读法：要证明的命题是 `SpectralComparison K`。这里调用 `TermModel.length_ordinary`。
/-- 对按指定比例划分一根连线的任意谱站址，比较式均成立。论证适用于任意系数域。

英文原文：Comparison holds at any spectral site which divides a wire in the
prescribed ratio. The argument applies over every coefficient field.
-/
theorem spectralComparison (K : Type) [Field K] : SpectralComparison K := by
  intro S _ _ _ f hf a m b u hm z
  let := TermModel.termMetric hf 1 zero_le_one
  have hd (x y : Term S) : dist x y = TermModel.length hf x y := one_mul _
  have h : WireModels K (Term S) := by
    intro B _ _ _ x D hD hx
    simp only [hd] at hx ⊢
    exact TermModel.length_ordinary hf B x D hD hx
  have hs : Segments (Term S) := by
    intro t x y
    refine ⟨.seg t x y, ?_⟩
    simp only [Divides, hd]
    exact TermModel.length_seg hf t x y
  have ht : Divides u (Term.mark a) (.mark b) (.mark m) := by
    simp only [Divides, hd, TermModel.length_mark]
    exact hm
  have he := (h.midpoints hs).all h.busemann hs ht (.mark z)
  simpa only [hd, TermModel.length_mark] using he

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
一个仿射点配置在其实际碰撞块处的候选融合项。

**英文原文**

Fusion candidates at the actual collision blocks of an affine arrangement.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Motion

open Polynomial Sphere Finset
open scoped Classical

variable {F A : Type} [Field F] [Fintype A] (a : A → Fin 2 → F) (d : Option F)

-- 读法：`centers` 的取值由 `univ.image fun i => projection (a i) d` 给出。
def centers : Finset F := univ.image fun i => projection (a i) d

-- 读法：在后续公式中，`Index` 是 `Fin (centers a d).card` 的缩写。
abbrev Index := Fin (centers a d).card

-- 读法：`label` 的取值由 `(Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm` 给出。
def label : Index a d ≃ ↥(centers a d) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

-- 读法：`point` 的取值由 `(label a d j).1` 给出。
def point (j : Index a d) : F := (label a d j).1

-- 读法：`group` 的取值由 `(label a d).symm ⟨projection (a i) d, mem_image_of_mem (fun j => projection (a j) d) (mem_univ i)⟩` 给出。
def group (i : A) := (label a d).symm
  ⟨projection (a i) d, mem_image_of_mem (fun j => projection (a j) d) (mem_univ i)⟩

-- 读法：`point a d (group a d i)` 等于 `projection (a i) d`。
theorem group_spec (i : A) : point a d (group a d i) = projection (a i) d := by
  simp [point, group]

-- 读法：`(point a d)` 是单射。使用 `Subtype.val_injective.comp` 给出的结论。
theorem point_inj : Function.Injective (point a d) :=
  Subtype.val_injective.comp (label a d).injective

-- 读法：`point a d j` 属于 `centers a d`。
theorem point_mem (j : Index a d) : point a d j ∈ centers a d := (label a d j).2

-- 读法：`group a d i = j` 与 `i ∈ pointsOn a (d, point a d j)` 等价。
theorem at_block (j : Index a d) (i : A) :
    group a d i = j ↔ i ∈ pointsOn a (d, point a d j) := by
  rw [← (point_inj a d).eq_iff, group_spec]
  simp [pointsOn]

-- 读法：存在 `j`，`point a k.1 j` 等于 `k.2`。
theorem block_index (k : Option F × F) (h : k ∈ blocks a) : ∃ j, point a k.1 j = k.2 := by
  obtain ⟨i, hi⟩ := (mem_blocks.mp h).2
  exact ⟨group a k.1 i, (group_spec _ _ _).trans (mem_filter.mp hi).2⟩

-- 读法：结论为 `∑ k ∈ blocks a, b k = ∑ d ∈ directions a, ∑ j, b (d, point a d j)`。这里调用 `mem_filter.mpr`。
theorem sum_blocks {R : Type*} [AddCommMonoid R] (b : Option F × F → R) :
    ∑ k ∈ blocks a, b k = ∑ d ∈ directions a, ∑ j, b (d, point a d j) := by
  rw [← sum_fiberwise_of_maps_to (fun k h => (mem_blocks.mp h).1) b]
  refine sum_congr rfl fun d hd => ?_
  symm
  refine sum_bij (fun j _ => (d, point a d j)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    obtain ⟨i, _, hi⟩ := mem_image.mp (point_mem a d j)
    exact mem_filter.mpr ⟨mem_blocks.mpr ⟨hd, i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩, rfl⟩
  · exact fun _ _ _ _ h => point_inj a d (congrArg Prod.snd h)
  · intro k h
    obtain ⟨hk, rfl⟩ := mem_filter.mp h
    obtain ⟨j, hj⟩ := block_index a k hk
    exact ⟨j, mem_univ _, Prod.ext rfl hj⟩

-- 读法：在后续公式中，`Choice` 是 `Pattern (centers a d).card M` 的缩写。
abbrev Choice (M : ℕ) := Pattern (centers a d).card M

variable {M : ℕ}

-- 读法：`budget` 的取值由 `∑ j, (t j).val` 给出。
def budget (t : Choice a d M) := ∑ j, (t j).val

-- 读法：`term` 的取值由 `fusedTerm (point a d) (group a d) (fun i => collisionOffset (a i) d) (fun i => (t i).val)` 给出。
def term (t : Choice a d M) {e : A → ℕ} : States 1 e → F :=
  fusedTerm (point a d) (group a d) (fun i => collisionOffset (a i) d) (fun i => (t i).val)

-- 读法：`form` 的取值由 `wick (fun i j => fieldKernel (position (a i.1) s 1, i.2) (position (a j.1) s 1, j.2)) (inputs x)` 给出。
def form (e : A → ℕ) (s : F) (x : States 1 e) : F :=
  wick (fun i j => fieldKernel (position (a i.1) s 1, i.2) (position (a j.1) s 1, j.2)) (inputs x)

-- 读法：`degree` 的取值由 `((directions a).card - 1) * ((∑ i, e i) / 2)` 给出。
def degree (e : A → ℕ) := ((directions a).card - 1) * ((∑ i, e i) / 2)

-- 读法：`(fun b : States 1 e => jetAt (degree a e) d i (correlatorPoly a (X : F[X]) 1 (inputs b)))` 属于 `Submodule.span F {v | ∃ t : Choice a d M, budget a d t ≤ 2 * i ∧ term a d t = v}`。这里调用 `Submodule.span_le.mpr`。
theorem jets (hd : d ∈ directions a) (e : A → ℕ) (hM : 2 * degree a e < M)
    {i : ℕ} (hi : i ≤ degree a e) :
    (fun b : States 1 e => jetAt (degree a e) d i (correlatorPoly a (X : F[X]) 1 (inputs b))) ∈
      Submodule.span F {v | ∃ t : Choice a d M, budget a d t ≤ 2 * i ∧ term a d t = v} := by
  obtain ⟨c, hc⟩ := fusion_terms (r := 1) (e := e) (point a d) (point_inj a d)
    (group a d) (fun j => collisionOffset (a j) d) (jetVar F M) M (jetVar_pow F M)
  rw [show point a d ∘ group a d = fun j => projection (a j) d from funext (group_spec a d)] at hc
  have h := jets_of_fusion a (inputs (r := 1) (e := e)) d hd ((∑ i, e i) / 2)
    (degree a e) M (fun b => by rw [weight_inputs]) rfl hM
    (fun t : Choice a d M => c • term a d t) (budget a d) hc _ hi
  apply (Submodule.span_le.mpr ?_) h
  rintro _ ⟨t, ht, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)

-- 读法：存在 `t : ∀ d`，使 `Choice a d M, (∀ d ∈ directions a, term a d (t d) ∉ W) ∧ ∑ d ∈ directions a, budget a d (t d) ≤ 2 * degree a e` 成立。这里调用 `correlator_form`。
theorem select (e : A → ℕ) (hM : 2 * degree a e < M) (W : Submodule F (States 1 e → F))
    (s : F) (hs : denominator (directions a) s 1 ≠ 0) (he : form a e s ∉ W) :
    ∃ t : ∀ d, Choice a d M, (∀ d ∈ directions a, term a d (t d) ∉ W) ∧
      ∑ d ∈ directions a, budget a d (t d) ≤ 2 * degree a e := by
  let P (x : States 1 e) := correlatorPoly a (X : F[X]) 1 (inputs x)
  refine select_fusions (directions a) P (degree a e)
    (fun d (t : Choice a d M) => term a d t (e := e)) (fun d t => budget a d t)
    ?_ (fun d hd _ hi => jets a d hd e hM hi) W s ?_
  · intro b
    simpa [P, degree, weight_inputs] using (correlator_form a (inputs b)).1
  · have eqn : (fun b => (P b).eval s) =
        (denominator (directions a) s 1 ^ ((∑ i, e i) / 2)) • form a e s := by
      funext b
      have e := correlator_map (aeval s) a (X : F[X]) 1 (inputs b)
      simp only [aeval_X, map_one, correlator_specialize a s 1 hs, weight_inputs] at e
      simpa [P, form] using e
    rw [eqn, W.smul_mem_iff (pow_ne_zero _ hs)]
    exact he

-- 读法：`menu` 的取值由 `(directions a).biUnion fun d => univ.image (fun t : Choice a d M => term a d t)` 给出。
def menu (e : A → ℕ) (M : ℕ) : Finset (States 1 e → F) :=
  (directions a).biUnion fun d => univ.image (fun t : Choice a d M => term a d t)

-- 读法：`(menu a e M).card` 不超过 `(directions a).card * (M + 1) ^ Fintype.card A`。这里调用 `card_biUnion_le.trans`。
theorem menu_size (e : A → ℕ) (M : ℕ) :
    (menu a e M).card ≤ (directions a).card * (M + 1) ^ Fintype.card A := by
  apply card_biUnion_le.trans
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun d _ => card_image_le.trans ?_
  simp only [card_univ, Choice, Pattern, Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by omega) card_image_le

-- 读法：`select_cuts` 的证明用到 `mem_blocks.mp`、`mem_biUnion.mpr`。
/-- 每个块对高成本项都有自己的切分分解；这些切分共用两倍能量的预算。

英文原文：Every block has its own cut decomposition of an expensive term, paid
for from a common budget of doubled energy.
-/
theorem select_cuts (e : A → ℕ) (hM : 2 * degree a e < M) (W : Submodule F (States 1 e → F))
    (s : F) (hs : denominator (directions a) s 1 ≠ 0) (he : form a e s ∉ W) :
    ∃ b : Option F × F → ℕ, (∑ k ∈ blocks a, b k) ≤ 2 * degree a e ∧
      ∀ k ∈ blocks a, ∃ T ∈ menu a e M, T ∉ W ∧
        ∃ L R : Level 1 (b k) → States 1 e → F,
          (∀ x, T x = ∑ j, L j x * R j x) ∧
          (∀ j x y, (∀ i ∈ pointsOn a k, x i = y i) → L j x = L j y) ∧
          (∀ j x y, (∀ i ∉ pointsOn a k, x i = y i) → R j x = R j y) := by
  obtain ⟨t, ht, hcost⟩ := select a e hM W s hs he
  let b (k : Option F × F) := if h : k.2 ∈ centers a k.1 then
    (t k.1 ((label a k.1).symm ⟨k.2, h⟩)).val else 0
  have hb (d : Option F) (j : Index a d) : b (d, point a d j) = (t d j).val := by
    simp [b, point]
  refine ⟨b, ?_, ?_⟩
  · simpa [sum_blocks, hb, budget] using hcost
  · rintro ⟨d, v⟩ hk
    have hd := (mem_blocks.mp hk).1
    -- 推导：从 `block_index a _ hk` 中取出 `j, hj`。
    obtain ⟨j, hj⟩ := block_index a _ hk
    change Index a d at j
    change point a d j = v at hj
    subst v
    refine ⟨term a d (t d), mem_biUnion.mpr ⟨d, hd, mem_image_of_mem _ (mem_univ _)⟩, ht d hd, ?_⟩
    rw [hb]
    simp_rw [← at_block a d j]
    exact fused_separates (point a d) (group a d) (fun i => collisionOffset (a i) d) (fun i => (t d i).val) j

end OAI.LinearAlgebra.MatrixExponent.Routing.Motion
end
