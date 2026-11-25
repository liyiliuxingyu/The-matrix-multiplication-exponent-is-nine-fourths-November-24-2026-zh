-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import OAI.LinearAlgebra.MatrixExponent.Prices.Padding
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Constrained
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank

section
/-!
# 施加一项价格界

给定严格高于 X 的被检验价格的目标 r，用 M(X^n U) / r^n 对 n 的和替换加性泛函 M(U)。移动求和指标便得到所需不等式。所有先前在乘法下稳定的线性不等式仍然成立。

**英文原文**

Imposing one price bound

For a target r strictly above the tested price of X, replace the
additive functional M(U) by the sum of M(X^n U) / r^n over n.
Shifting the index gives the desired inequality. All earlier linear
inequalities stable under multiplication are preserved.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices

variable {T I : Type*} [CommSemiring T] [PartialOrder T]

-- 读法：`StableLE` 表示以下条件：对每个 `u`，`M (a * u)` 不超过 `c * M (b * u)`。
def StableLE (M : T → ℝ) (a b : T) (c : ℝ) : Prop :=
  ∀ u, M (a * u) ≤ c * M (b * u)

-- 读法：`ProductBound` 表示以下条件：存在 `K : ℝ`，对每个 `w : List I`，`M (w.map X).prod` 不超过 `K * (w.map p).prod`。
def ProductBound (X : I → T) (p : I → ℝ) (M : T → ℝ) : Prop :=
  ∃ K : ℝ, ∀ w : List I, M (w.map X).prod ≤ K * (w.map p).prod

-- 读法：存在 `N : T →+ ℝ`，由 `Monotone N ∧ 0 < N 1 ∧ ProductBound X p N ∧ StableLE N (X i) 1 r ∧ ∀ a b c, StableLE M a b c` 推出 `StableLE N a b c`。
theorem discount (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a)
    {X : I → T} {p : I → ℝ} {M : T →+ ℝ} (hm : Monotone M) (hpos : 0 < M 1)
    (hbound : ∀ x, ∃ c ≥ 0, StableLE M x 1 c)
    (hb : ProductBound X p M) (i : I) {r : ℝ} (hi : 0 ≤ p i) (hr : p i < r) :
    ∃ N : T →+ ℝ, Monotone N ∧ 0 < N 1 ∧ ProductBound X p N ∧
      StableLE N (X i) 1 r ∧ ∀ a b c, StableLE M a b c → StableLE N a b c := by
  obtain ⟨K, hK⟩ := hb
  have hr0 := hi.trans_lt hr
  let q := p i / r
  -- 推导：记下中间结论 `hq`：`Summable (fun n : ℕ => q ^ n)`。
  have hq : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one (div_nonneg hi hr0.le) ((div_lt_one hr0).mpr hr)
  let t (u : T) (n : ℕ) := M (X i ^ n * u) / r ^ n
  have ht (u : T) (n : ℕ) : 0 ≤ t u n :=
    div_nonneg (by rw [← map_zero M]; exact hm (hzero _)) (pow_nonneg hr0.le n)
  have htest (w : List I) (n : ℕ) :
      t (w.map X).prod n ≤ q ^ n * (K * (w.map p).prod) := by
    have h := hK (List.replicate n i ++ w)
    simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate] at h
    calc
      _ ≤ (K * (p i ^ n * (w.map p).prod)) / r ^ n :=
        div_le_div_of_nonneg_right h (pow_nonneg hr0.le n)
      _ = _ := by unfold q; rw [div_pow]; ring
  have hs (u : T) : Summable (t u) := by
    -- 推导：从 `hbound u` 中取出 `m, hm, hu`。
    obtain ⟨m, hm, hu⟩ := hbound u
    refine Summable.of_nonneg_of_le (ht u) ?_ (hq.mul_right (K * m))
    intro n
    have h := hu (X i ^ n)
    rw [mul_comm u, one_mul] at h
    have hn := htest [] n
    simp only [List.map_nil, List.prod_nil, mul_one] at hn
    calc
      _ ≤ (m : ℝ) * M (X i ^ n) / r ^ n :=
        div_le_div_of_nonneg_right h (pow_nonneg hr0.le n)
      _ = t 1 n * m := by unfold t; rw [mul_one]; ring
      _ ≤ q ^ n * K * m := mul_le_mul_of_nonneg_right hn hm
      _ = _ := mul_assoc _ _ _
  let N : T →+ ℝ :=
    { toFun := fun u => ∑' n, t u n
      map_zero' := by simp [t]
      map_add' := fun u v => by
        rw [← (hs u).tsum_add (hs v)]
        exact tsum_congr (fun n => by simp only [t, mul_add, map_add, add_div]) }
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    refine Summable.tsum_le_tsum (fun n => ?_) (hs u) (hs v)
    exact div_le_div_of_nonneg_right (hm (hmul _ _ _ h)) (pow_nonneg hr0.le n)
  · have h := (hs 1).le_tsum 0 (fun n _ => ht 1 n)
    exact hpos.trans_le (by simpa [N, t] using h)
  · refine ⟨(∑' n : ℕ, q ^ n) * K, fun w => ?_⟩
    change (∑' n, t (w.map X).prod n) ≤ _
    rw [mul_assoc, ← tsum_mul_right]
    exact Summable.tsum_le_tsum (htest w) (hs _) (hq.mul_right _)
  · intro u
    rw [one_mul, mul_comm r, ← div_le_iff₀ hr0]
    change (∑' n, t (X i * u) n) / r ≤ ∑' n, t u n
    rw [← tsum_div_const, (hs u).tsum_eq_zero_add]
    have shift (n : ℕ) : t (X i * u) n / r = t u (n + 1) := by
      simp only [t, pow_succ, div_div, mul_assoc]
    simp only [shift]
    exact le_add_of_nonneg_left (ht u 0)
  · intro a b c h u
    change (∑' n, t (a * u) n) ≤ c * ∑' n, t (b * u) n
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (hs _) ((hs _).mul_left c)
    unfold t
    rw [mul_left_comm (X i ^ n) a, mul_left_comm (X i ^ n) b, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h _) (pow_nonneg hr0.le n)

end OAI.LinearAlgebra.MatrixExponent.Prices
end

section
/-!
# 加性闭包的包络

在所有经限制得到且在新增站点具有平凡输出腿的张量上，对原有谱值取上确界。

**英文原文**

The additive closure envelope

Take the supremum of the old spectral value over tensors obtained from
a restriction with trivial output legs at the added sites.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices

variable {S T : Type*} [CommSemiring S] [CommSemiring T]
    [PartialOrder S] [PartialOrder T] {pad : S → T}

-- 读法：存在 `M : T →+ ℝ`，`M 1 = 1` 与 `Monotone M ∧ (∀ s x, M (pad s * x) = f s * M x) ∧ (∀ x r, M x ≤ r ↔ ∀ s, pad s ≤ x → f s ≤ r)` 同时成立。对 `n` 作归纳，并把 `s` 保持为任意参数。
theorem Padding.envelope (hp : Padding pad)
    (hadd : ∀ a b c : T, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a) (hbound : ∀ a : T, ∃ (s : S) (n : ℕ), a ≤ pad s * n)
    (f : S →+* ℝ) (hf : Monotone f) :
    ∃ M : T →+ ℝ, M 1 = 1 ∧ Monotone M ∧
      (∀ s x, M (pad s * x) = f s * M x) ∧
      (∀ x r, M x ≤ r ↔ ∀ s, pad s ≤ x → f s ≤ r) := by
  let V (x : T) : Set ℝ := {r | ∃ s, pad s ≤ x ∧ f s = r}
  let M (x : T) := sSup (V x)
  have hn (x : T) : (V x).Nonempty :=
    ⟨f 0, 0, hp.zero.symm ▸ hzero x, rfl⟩
  have hb (n : ℕ) (s : S) (hs : pad s ≤ (n : T)) : f s ≤ n := by
    induction n generalizing s with
    | zero =>
      rw [Nat.cast_zero, ← hp.zero] at hs
      simpa using hf ((hp.le_iff _ _).mp hs)
    | succ n ih =>
      rw [Nat.cast_succ, ← hp.one] at hs
      -- 推导：从 `hp.split hs` 中取出 `a, b, ha, h1, hab`。
      obtain ⟨a, b, ha, h1, hab⟩ := hp.split hs
      have he := hf ((hp.le_iff _ _).mp h1)
      rw [map_one] at he
      rw [Nat.cast_succ]
      exact (hf hab).trans (by rw [map_add]; exact add_le_add (ih a ha) he)
  have hbd (x : T) : BddAbove (V x) := by
    obtain ⟨a, n, h⟩ := hbound x
    have ha : 0 ≤ f a := by
      rw [← map_zero f]
      exact hf ((hp.le_iff _ _).mp (hp.zero.symm ▸ hzero _))
    refine ⟨f a * n, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    -- 推导：从 `hp.factor (hs.trans h)` 中取出 `b, hh, h'`。
    obtain ⟨b, hh, h'⟩ := hp.factor (hs.trans h)
    exact (hf h').trans (by rw [map_mul]; exact mul_le_mul_of_nonneg_left (hb n b hh) ha)
  have lo (x : T) (s : S) (hs : pad s ≤ x) : f s ≤ M x :=
    le_csSup (hbd x) ⟨s, hs, rfl⟩
  have hi (x : T) (r : ℝ) : M x ≤ r ↔ ∀ s, pad s ≤ x → f s ≤ r := by
    refine ⟨fun h s hs => (lo x s hs).trans h, fun h => csSup_le (hn x) ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have mono : Monotone M := fun x y h => (hi x _).mpr fun s hs => lo y s (hs.trans h)
  have old (s : S) : M (pad s) = f s :=
    le_antisymm ((hi _ _).mpr fun a ha => hf ((hp.le_iff _ _).mp ha)) (lo _ s le_rfl)
  -- 推导：记下中间结论 `zero`：`M 0 = 0`。
  have zero : M 0 = 0 := by rw [← hp.zero, old, map_zero]
  have one : M 1 = 1 := by rw [← hp.one, old, map_one]
  have hsum (x y : T) : M (x + y) = M x + M y := by
    apply le_antisymm
    · refine (hi _ _).mpr fun s hs => ?_
      obtain ⟨a, b, ha, hb, h⟩ := hp.split hs
      exact (hf h).trans (by rw [map_add]; exact add_le_add (lo x a ha) (lo y b hb))
    · apply le_sub_iff_add_le.mp
      refine (hi x _).mpr fun a ha => ?_
      apply le_sub_comm.mp
      refine (hi y _).mpr fun b hb => ?_
      rw [le_sub_iff_add_le', ← map_add]
      apply lo
      refine (hp.add_le _ _).trans ((hadd _ _ _ ha).trans ?_)
      simpa only [add_comm] using hadd _ _ x hb
  refine ⟨{ toFun := M, map_zero' := zero, map_add' := hsum }, one, mono, ?_, hi⟩
  intro s x
  change M (pad s * x) = f s * M x
  -- 推导：记下中间结论 `hs`：`0 ≤ f s`。
  have hs : 0 ≤ f s := by rw [← old, ← zero]; exact mono (hzero _)
  apply le_antisymm
  · refine (hi _ _).mpr fun a ha => ?_
    obtain ⟨b, hb, hab⟩ := hp.factor ha
    exact (hf hab).trans (by rw [map_mul]; exact mul_le_mul_of_nonneg_left (lo x b hb) hs)
  · rcases hs.eq_or_lt with hz | hs
    · rw [← hz, zero_mul, ← zero]
      exact mono (hzero _)
    · rw [mul_comm, ← le_div_iff₀ hs]
      refine (hi x _).mpr fun b hb => ?_
      rw [le_div_iff₀ hs, mul_comm, ← map_mul]
      exact lo _ _ (by rw [hp.mul]; exact hmul _ _ _ hb)

end OAI.LinearAlgebra.MatrixExponent.Prices
end

section
/-!
# 同时延拓各项价格

这里使用谱值，即对单位尺度的价格取指数。检验遍历所有允许重复元素的有限列表，因而也涵盖了将任意多份副本耦合起来的闭包。

**英文原文**

Simultaneous price extension

We work with spectral values, i.e. exponentiated unit-scale prices.
The test runs through finite lists with repetitions. It therefore
includes closures that couple arbitrarily many copies.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices

variable {S T I : Type*} [CommSemiring T] [PartialOrder T]

-- 读法：存在 `g : T →+* ℝ`，由 `Monotone g ∧ (∀ i, g (X i) ≤ p i) ∧ ∀ a b c, StableLE M a b c` 推出 `g a ≤ c * g b`。
/-- 将线性闭包界转化为一个乘法性求值。

英文原文：Turn the linear closure bounds into a single multiplicative evaluation.
-/
theorem character_of_products
    (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a)
    {X : I → T} {p : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (M : T →+ ℝ) (hm : Monotone M) (hm1 : 0 < M 1) (hb : ProductBound X p M)
    (hlower : ∀ x ≠ 0, ∃ c, StableLE M 1 x c)
    (hupper : ∀ x, ∃ c ≥ 0, StableLE M x 1 c) :
    ∃ g : T →+* ℝ, Monotone g ∧ (∀ i, g (X i) ≤ p i) ∧
      ∀ a b c, StableLE M a b c → g a ≤ c * g b := by
  classical
  let J := {t : T × T × ℝ // StableLE M t.1 t.2.1 t.2.2 ∨
    ∃ i, X i = t.1 ∧ 1 = t.2.1 ∧ p i < t.2.2}
  let A (j : J) := j.val.1
  let B (j : J) := j.val.2.1
  let C (j : J) := j.val.2.2
  have step (s : Finset J) :
      ∃ N : T →+ ℝ, Monotone N ∧ 0 < N 1 ∧ ProductBound X p N ∧
        (∀ a b c, StableLE M a b c → StableLE N a b c) ∧
        (∀ j ∈ s, StableLE N (A j) (B j) (C j)) := by
    induction s using Finset.induction with
    | empty => exact ⟨M, hm, hm1, hb, fun _ _ _ h => h, by simp⟩
    | @insert j s _ ih =>
      -- 推导：从 `ih` 中取出 `N, hn, hn1, hN, keep, hs`。
      obtain ⟨N, hn, hn1, hN, keep, hs⟩ := ih
      rcases j.property with h | ⟨i, ha, hb, hc⟩
      · refine ⟨N, hn, hn1, hN, keep, fun l hl => ?_⟩
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact keep _ _ _ h
        · exact hs _ hl
      · obtain ⟨R, hr, hr1, hR, hj, preserve⟩ :=
          discount hmul hzero hn hn1 (fun x => by
            obtain ⟨c, hc, h⟩ := hupper x
            exact ⟨c, hc, keep _ _ _ h⟩) hN i (hp i) hc
        refine ⟨R, hr, hr1, hR, fun a b c h => preserve a b c (keep a b c h), fun l hl => ?_⟩
        rcases Finset.mem_insert.mp hl with hl | hl
        · subst l
          simpa only [A, B, C, ← ha, ← hb] using hj
        · exact preserve _ _ _ (hs l hl)
  let fixed : Set J := {j | StableLE M (A j) (B j) (C j)}
  have hl (x : T) (hx : x ≠ 0) : ∃ j ∈ fixed, A j = 1 ∧ B j = x := by
    -- 推导：从 `hlower x hx` 中取出 `c, hc`。
    obtain ⟨c, hc⟩ := hlower x hx
    exact ⟨⟨(1, x, c), Or.inl hc⟩, hc, rfl, rfl⟩
  have hu (x : T) : ∃ j ∈ fixed, A j = x ∧ B j = 1 := by
    obtain ⟨c, _, hc⟩ := hupper x
    exact ⟨⟨(x, 1, c), Or.inl hc⟩, hc, rfl, rfl⟩
  have norm (s : Finset J) : ∃ N : T →+ ℝ, N 1 = 1 ∧ Monotone N ∧
      ∀ j, j ∈ fixed ∨ j ∈ s → ∀ u, N (A j * u) ≤ C j * N (B j * u) := by
    obtain ⟨N, hn, hn1, _, keep, hs⟩ := step s
    let R : T →+ ℝ :=
      { toFun := fun x => N x / N 1
        map_zero' := by rw [map_zero, zero_div]
        map_add' := fun x y => by rw [map_add, add_div] }
    refine ⟨R, div_self hn1.ne', fun _ _ h => div_le_div_of_nonneg_right (hn h) hn1.le, ?_⟩
    intro j hj u
    change N (A j * u) / N 1 ≤ C j * (N (B j * u) / N 1)
    rw [← mul_div_assoc]
    have h := hj.elim (fun h => keep _ _ _ h) (hs j)
    exact div_le_div_of_nonneg_right (h u) hn1.le
  -- 推导：从 `Spectrum.constrained_character hmul hzero A B C fixed hl hu norm` 中取出 `g, hg, h`。
  obtain ⟨g, hg, h⟩ := Spectrum.constrained_character hmul hzero A B C fixed hl hu norm
  refine ⟨g, hg, ?_, fun a b c hab => h ⟨(a, b, c), Or.inl hab⟩⟩
  intro i
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hl := h ⟨(X i, 1, r), Or.inr ⟨i, rfl, rfl, hr⟩⟩
  simpa only [A, B, C, map_one, mul_one] using hl

variable [CommSemiring S] [PartialOrder S] {pad : S → T}

-- 读法：`(∃ g : T →+* ℝ, Monotone g ∧ (∀ s, g (pad s) = f s) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, ∀ s, pad s ≤ (w.map X).prod → f s ≤ (w.map p).prod` 等价。对 `w` 作归纳。
theorem Padding.weighted_extension (hp : Padding pad)
    (hadd : ∀ a b c : T, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a)
    (f : S →+* ℝ) (hf : Monotone f)
    (hunit : ∀ x ≠ 0, ∃ s, pad s ≤ x ∧ 0 < f s)
    (hbound : ∀ x, ∃ (s : S) (n : ℕ), x ≤ pad s * n)
    (X : I → T) (p : I → ℝ) :
    (∃ g : T →+* ℝ, Monotone g ∧ (∀ s, g (pad s) = f s) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, ∀ s, pad s ≤ (w.map X).prod → f s ≤ (w.map p).prod := by
  constructor
  · rintro ⟨g, hg, he, hu⟩ w s h
    have hn (x : T) : 0 ≤ g x := by rw [← map_zero g]; exact hg (hzero _)
    have ht (w : List I) : g (w.map X).prod ≤ (w.map p).prod := by
      induction w with
      | nil => simp
      | cons i w ih =>
        simp only [List.map_cons, List.prod_cons, map_mul]
        exact mul_le_mul (hu i) ih (hn _) ((hn _).trans (hu i))
    rw [← he]
    exact (hg h).trans (ht w)
  · intro h
    -- 推导：从 `hp.envelope hadd hmul hzero hbound f hf` 中取出 `M, h1, hm, he, hu`。
    obtain ⟨M, h1, hm, he, hu⟩ := hp.envelope hadd hmul hzero hbound f hf
    have hb : ProductBound X p M :=
      ⟨1, fun w => by rw [one_mul]; exact (hu _ _).mpr (h w)⟩
    have hn (i : I) : 0 ≤ p i := by
      simpa using h [i] 0 (by rw [hp.zero]; exact hzero _)
    have hlower (x : T) (hx : x ≠ 0) : ∃ c, StableLE M 1 x c := by
      obtain ⟨s, h, hs⟩ := hunit x hx
      refine ⟨(f s)⁻¹, fun u => ?_⟩
      rw [le_inv_mul_iff₀ hs, one_mul, ← he, mul_comm (pad s), mul_comm x]
      exact hm (hmul _ _ _ h)
    have hupper (x : T) : ∃ c ≥ 0, StableLE M x 1 c := by
      -- 推导：从 `hbound x` 中取出 `s, n, h`。
      obtain ⟨s, n, h⟩ := hbound x
      have hs : 0 ≤ f s := by
        rw [← map_zero f]
        exact hf ((hp.le_iff _ _).mp (hp.zero.symm ▸ hzero _))
      refine ⟨f s * (n : ℝ), mul_nonneg hs (Nat.cast_nonneg _), fun u => ?_⟩
      rw [one_mul, mul_assoc, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul,
        ← he, ← mul_assoc, mul_comm x, mul_comm (pad s * n)]
      exact hm (hmul _ _ _ h)
    obtain ⟨g, hg, hb, hs⟩ :=
      character_of_products hmul hzero hn M hm (by rw [h1]; exact zero_lt_one) hb hlower hupper
    refine ⟨g, hg, ?_, hb⟩
    intro s
    apply le_antisymm
    · have hl := hs (pad s) 1 (f s) (fun u => by rw [one_mul, he])
      simpa using hl
    · rcases le_or_gt (f s) 0 with h | h
      · exact h.trans (by rw [← map_zero g]; exact hg (hzero _))
      · have hl := hs 1 (pad s) (f s)⁻¹ (fun u => by rw [one_mul, he, inv_mul_cancel_left₀ h.ne'])
        rwa [map_one, le_inv_mul_iff₀ h, mul_one] at hl

-- 读法：`(∃ g : T →+* ℝ, Monotone g ∧ (∀ s, g (pad s) = f s) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, ∀ s, pad s ≤ (w.map X).prod → f s ≤ (w.map p).prod` 等价。
theorem Padding.extension (hp : Padding pad)
    (hadd : ∀ a b c : T, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : T, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : T, 0 ≤ a) (hunit : ∀ a : T, a ≠ 0 → 1 ≤ a)
    (hbound : ∀ a : T, ∃ n : ℕ, a ≤ (n : T))
    (f : S →+* ℝ) (hf : Monotone f) (X : I → T) (p : I → ℝ) :
    (∃ g : T →+* ℝ, Monotone g ∧ (∀ s, g (pad s) = f s) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, ∀ s, pad s ≤ (w.map X).prod → f s ≤ (w.map p).prod := by
  refine hp.weighted_extension hadd hmul hzero f hf ?_ ?_ X p
  · exact fun x hx => ⟨1, by rw [hp.one]; exact hunit x hx, by simp⟩
  · intro x
    obtain ⟨n, hn⟩ := hbound x
    exact ⟨1, n, by simpa only [hp.one, one_mul] using hn⟩

end OAI.LinearAlgebra.MatrixExponent.Prices
end

/-!
# 辅助成本与同时插值

**英文原文**

Assisted costs and simultaneous interpolation
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices

variable {S T : Type*} [CommSemiring S] [CommSemiring T] [PartialOrder S] [PartialOrder T]

-- 读法：结构的字段包括 `padLaw`、`mono`、`add`、`mul`、`zero`。
/-- 对普通价格延拓和带赋值的价格延拓均适用的统一假设。

英文原文：Uniform hypotheses for ordinary and valued price extensions.
-/
structure ExtensionData (pad : S → T) (f : S →+* ℝ) : Prop where
  padLaw : Padding pad
  mono : Monotone f
  add (a b c : T) : a ≤ b → a + c ≤ b + c
  mul (a b c : T) : a ≤ b → c * a ≤ c * b
  zero (a : T) : 0 ≤ a
  lower : ∀ x ≠ 0, ∃ s, pad s ≤ x ∧ 0 < f s
  upper : ∀ x, ∃ (s : S) (n : ℕ), x ≤ pad s * n

-- 读法：`assisted` 的取值由 `sSup {r | ∃ (m : ℕ) (B : S), 0 < m ∧ pad B ≤ A ^ m ∧ r = f B ^ (m : ℝ)⁻¹}` 给出。
/-- 取指数后的辅助成本。检验所有正整数次幂，并检验其到新增站点上各条腿均平凡的张量的每一种限制。

英文原文：The exponentiated assisted cost. All positive powers and all restrictions
to a tensor with trivial legs at the added sites are tested.
-/
def assisted (pad : S → T) (f : S →+* ℝ) (A : T) : ℝ :=
  sSup {r | ∃ (m : ℕ) (B : S), 0 < m ∧ pad B ≤ A ^ m ∧ r = f B ^ (m : ℝ)⁻¹}

namespace ExtensionData
variable {pad : S → T} {f : S →+* ℝ} (H : ExtensionData pad f)
include H

-- 读法：`(∃ g : T →+* ℝ, Monotone g ∧ (∀ B, g (pad B) = f B) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, ∀ B, pad B ≤ (w.map X).prod → f B ≤ (w.map p).prod` 等价。使用 `H.padLaw.weighted_extension` 给出的结论。
theorem extension_iff {I : Type*} (X : I → T) (p : I → ℝ) :
    (∃ g : T →+* ℝ, Monotone g ∧ (∀ B, g (pad B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, ∀ B, pad B ≤ (w.map X).prod → f B ≤ (w.map p).prod :=
  H.padLaw.weighted_extension H.add H.mul H.zero f H.mono H.lower H.upper X p

-- 读法：存在 `g : T →+* ℝ`，`Monotone g` 与 `∀ B, g (pad B) = f B` 同时成立。对 `w` 分类讨论。
theorem exists_extension :
    ∃ g : T →+* ℝ, Monotone g ∧ ∀ B, g (pad B) = f B := by
  obtain ⟨g, hg, he, _⟩ := (H.extension_iff (fun _ : Empty => 1) (fun _ => 1)).mpr
    (by
      intro w B h
      cases w with
      | nil =>
        change pad B ≤ 1 at h
        rw [← H.padLaw.one] at h
        simpa using H.mono ((H.padLaw.le_iff B 1).mp h)
      | cons i _ => exact i.elim)
  exact ⟨g, hg, he⟩

-- 读法：`0` 不超过 `f A`。这里调用 `H.mono`。
private theorem nonneg (A : S) : 0 ≤ f A := by
  rw [← map_zero f]
  exact H.mono ((H.padLaw.le_iff _ _).mp (H.padLaw.zero.symm ▸ H.zero _))

-- 读法：`0` 不超过 `g B`。
private theorem value_nonneg {g : T →+* ℝ} (hg : Monotone g) (B : T) :
    0 ≤ g B := by simpa using hg (H.zero B)

-- 读法：要证明的命题是 `IsLeast {r | ∃ g : T →+* ℝ, Monotone g ∧ (∀ B, g (pad B) = f B) ∧ g A = r} (assisted pad f A)`。
theorem assisted_minimum (A : T) :
    IsLeast {r | ∃ g : T →+* ℝ,
      Monotone g ∧ (∀ B, g (pad B) = f B) ∧ g A = r} (assisted pad f A) := by
  let V : Set ℝ := {r | ∃ (m : ℕ) (B : S), 0 < m ∧ pad B ≤ A ^ m ∧
    r = f B ^ (m : ℝ)⁻¹}
  have hv : 0 ∈ V :=
    ⟨1, 0, by decide, by rw [H.padLaw.zero]; exact H.zero _, by simp⟩
  have upper (g : T →+* ℝ) (hg : Monotone g) (he : ∀ B, g (pad B) = f B) :
      g A ∈ upperBounds V := by
    rintro _ ⟨m, B, hm, hB, rfl⟩
    rw [Real.rpow_inv_le_iff_of_pos (H.nonneg _) (H.value_nonneg hg _) (Nat.cast_pos.mpr hm),
      Real.rpow_natCast, ← map_pow, ← he]
    exact hg hB
  have lower (g : T →+* ℝ) (hg : Monotone g) (he : ∀ B, g (pad B) = f B) :
      assisted pad f A ≤ g A := csSup_le ⟨0, hv⟩ (upper g hg he)
  have hb : BddAbove V := by
    -- 推导：从 `H.exists_extension` 中取出 `g, hg, he`。
    obtain ⟨g, hg, he⟩ := H.exists_extension
    exact ⟨g A, upper g hg he⟩
  have hp : 0 ≤ assisted pad f A := le_csSup hb hv
  have test (m : ℕ) (B : S) (h : pad B ≤ A ^ m) : f B ≤ assisted pad f A ^ m := by
    by_cases hm : m = 0
    · subst m
      rw [pow_zero, ← H.padLaw.one] at h
      simpa using H.mono ((H.padLaw.le_iff B 1).mp h)
    · have hm' := Nat.pos_of_ne_zero hm
      rw [← Real.rpow_natCast, ← Real.rpow_inv_le_iff_of_pos (H.nonneg _) hp
        (Nat.cast_pos.mpr hm')]
      exact le_csSup hb ⟨m, B, hm', h, rfl⟩
  -- 推导：从 `(H.extension_iff (fun _ : Unit => A) (fun _ => assisted pad f A)).mpr` 中取出 `g, hg, he, hA`。
  obtain ⟨g, hg, he, hA⟩ := (H.extension_iff (fun _ : Unit => A) (fun _ => assisted pad f A)).mpr
    (by
      intro w B h
      have hm : pad B ≤ (List.replicate w.length A).prod := by simpa using h
      have hA := hm.trans_eq (List.prod_replicate w.length A)
      simpa [List.prod_replicate] using test w.length B hA)
  refine ⟨⟨g, hg, he, le_antisymm (hA ()) (lower g hg he)⟩, ?_⟩
  rintro _ ⟨g', hg', he', rfl⟩
  exact lower g' hg' he'

-- 读法：`(∃ g : T →+* ℝ, Monotone g ∧ (∀ B, g (pad B) = f B) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, assisted pad f (w.map X).prod ≤ (w.map p).prod` 等价。对 `w` 作归纳。
/-- 用辅助成本表述的乘积检验。

英文原文：The product test in terms of assisted costs.
-/
theorem assisted_extension_iff {I : Type*}
    (X : I → T) (p : I → ℝ) :
    (∃ g : T →+* ℝ, Monotone g ∧
      (∀ B, g (pad B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, assisted pad f (w.map X).prod ≤ (w.map p).prod := by
  constructor
  · rintro ⟨g, hg, he, hu⟩ w
    refine ((H.assisted_minimum _).2 ⟨g, hg, he, rfl⟩).trans ?_
    induction w with
    | nil => simp
    | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      refine (g.map_mul _ _).trans_le ?_
      exact mul_le_mul (hu i) ih (H.value_nonneg hg _) ((H.value_nonneg hg _).trans (hu i))
  · intro h
    refine (H.extension_iff X p).mpr fun w B hB => ?_
    -- 推导：从 `(H.assisted_minimum (w.map X).prod).1` 中取出 `g, hg, he, hA`。
    obtain ⟨g, hg, he, hA⟩ := (H.assisted_minimum (w.map X).prod).1
    exact ((he B).symm.trans_le (hg hB)).trans (hA.trans_le (h w))

-- 读法：存在 `k : T →+* ℝ`，`Monotone k` 与 `(∀ B, k (pad B) = f B) ∧ ∀ A, k A ≤ g A ^ t * h A ^ (1 - t)` 同时成立。对 `w` 作归纳。
/-- 对所有张量求值同时作插值，且保持原有价格。

英文原文：Interpolate all tensor evaluations at once, preserving the old price.
-/
theorem interpolate
    (g h : T →+* ℝ) (hg : Monotone g) (hh : Monotone h)
    (eg : ∀ B, g (pad B) = f B) (eh : ∀ B, h (pad B) = f B)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∃ k : T →+* ℝ, Monotone k ∧ (∀ B, k (pad B) = f B) ∧
      ∀ A, k A ≤ g A ^ t * h A ^ (1 - t) := by
  let p (A : T) := g A ^ t * h A ^ (1 - t)
  have ep (w : List (T)) : p w.prod = (w.map p).prod := by
    induction w with
    | nil => simp [p]
    | cons X w ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
      unfold p
      rw [map_mul, map_mul, Real.mul_rpow (H.value_nonneg hg _) (H.value_nonneg hg _),
        Real.mul_rpow (H.value_nonneg hh _) (H.value_nonneg hh _)]
      exact mul_mul_mul_comm _ _ _ _
  apply (H.extension_iff id p).mpr
  intro w B hB
  rw [List.map_id] at hB
  rw [← ep]
  have hz := H.nonneg B
  have ht1 := sub_nonneg.mpr ht'
  -- 推导：记下中间结论 `e`：`f B = f B ^ t * f B ^ (1 - t)`。
  have e : f B = f B ^ t * f B ^ (1 - t) := by
    rw [← Real.rpow_add_of_nonneg hz ht ht1, add_sub_cancel, Real.rpow_one]
  rw [e]
  exact mul_le_mul (Real.rpow_le_rpow hz ((eg B).symm.trans_le (hg hB)) ht)
    (Real.rpow_le_rpow hz ((eh B).symm.trans_le (hh hB)) ht1)
    (Real.rpow_nonneg hz _) (Real.rpow_nonneg (H.value_nonneg hg _) _)

end ExtensionData
end OAI.LinearAlgebra.MatrixExponent.Prices
end

/-!
# 延拓普通张量价格

使用谱值后，不必给零指定无穷的对数值。由 `pad_le_ofRaw_iff`，对单调价格而言，检验 `pad U B ≤ A` 等价于检验 A 在 U 处的每个同时闭包。每个泛函都可以使用其站点的整个局部空间。

**英文原文**

Extending an ordinary tensor price

We use spectral values so that zero needs no infinite logarithm.
By `pad_le_ofRaw_iff`, testing `pad U B ≤ A` is equivalent (for
monotone prices) to testing every simultaneous closure of A at U.
Each functional has access to the entire local space of its site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype U]

-- 读法：要证明的命题是 `Prices.ExtensionData (pad U) f`。
private theorem data (f : Tensor K S →+* ℝ) (hf : Monotone f) :
    Prices.ExtensionData (pad U) f := by
  refine ⟨padding U, hf, add_le_add_right, mul_le_mul_left, zero_le, ?_, ?_⟩
  · intro x hx
    exact ⟨1, by rw [(padding U).one]; exact one_le x hx, by simp⟩
  · intro x
    obtain ⟨n, hn⟩ := exists_bound x
    exact ⟨1, n, by rw [(padding U).one, one_mul]; exact hn⟩

-- 读法：`(∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, ∀ B, pad U B ≤ (w.map X).prod → f B ≤ (w.map p).prod` 等价。
theorem extension_iff {I : Type*} (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (X : I → Tensor K (S ⊕ U)) (p : I → ℝ) :
    (∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧
      (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, ∀ B, pad U B ≤ (w.map X).prod → f B ≤ (w.map p).prod :=
  (data (U := U) f hf).extension_iff X p

-- 读法：存在 `g : Tensor K (S ⊕ U) →+* ℝ`，`Monotone g` 与 `∀ B, g (pad U B) = f B` 同时成立。
theorem exists_extension (f : Tensor K S →+* ℝ) (hf : Monotone f) :
    ∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧ ∀ B, g (pad U B) = f B :=
  (data (U := U) f hf).exists_extension

-- 读法：`assisted` 的取值由 `Prices.assisted (pad U) f A` 给出。
/-- 取指数后的辅助成本。检验所有正整数次幂，并检验其到新增站点上各条腿均平凡的张量的每一种限制。

英文原文：The exponentiated assisted cost. All positive powers and all restrictions
to a tensor with trivial legs at the added sites are tested.
-/
def assisted (f : Tensor K S →+* ℝ) (A : Tensor K (S ⊕ U)) : ℝ :=
  Prices.assisted (pad U) f A

-- 读法：要证明的命题是 `IsLeast {r | ∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ g A = r} (assisted f A)`。
theorem assisted_minimum (f : Tensor K S →+* ℝ) (hf : Monotone f) (A : Tensor K (S ⊕ U)) :
    IsLeast {r | ∃ g : Tensor K (S ⊕ U) →+* ℝ,
      Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ g A = r} (assisted f A) :=
  (data (U := U) f hf).assisted_minimum A

-- 读法：`(∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i))` 与 `∀ w : List I, assisted f (w.map X).prod ≤ (w.map p).prod` 等价。
/-- 用辅助成本表述的乘积检验。

英文原文：The product test in terms of assisted costs.
-/
theorem assisted_extension_iff {I : Type*} (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (X : I → Tensor K (S ⊕ U)) (p : I → ℝ) :
    (∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧
      (∀ B, g (pad U B) = f B) ∧ (∀ i, g (X i) ≤ p i)) ↔
      ∀ w : List I, assisted f (w.map X).prod ≤ (w.map p).prod :=
  (data (U := U) f hf).assisted_extension_iff X p

-- 读法：存在 `k : Tensor K (S ⊕ U) →+* ℝ`，`Monotone k` 与 `(∀ B, k (pad U B) = f B) ∧ ∀ A, k A ≤ g A ^ t * h A ^ (1 - t)` 同时成立。
/-- 对所有张量求值同时作插值，且保持原有价格。

英文原文：Interpolate all tensor evaluations at once, preserving the old price.
-/
theorem interpolate (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (g h : Tensor K (S ⊕ U) →+* ℝ) (hg : Monotone g) (hh : Monotone h)
    (eg : ∀ B, g (pad U B) = f B) (eh : ∀ B, h (pad U B) = f B)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∃ k : Tensor K (S ⊕ U) →+* ℝ, Monotone k ∧ (∀ B, k (pad U B) = f B) ∧
      ∀ A, k A ≤ g A ^ t * h A ^ (1 - t) :=
  (data (U := U) f hf).interpolate g h hg hh eg eh ht ht'

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
