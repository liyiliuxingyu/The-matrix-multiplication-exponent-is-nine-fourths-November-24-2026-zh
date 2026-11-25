-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryTerms
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecificLimits.Basic

section
/-!
# 有限乘积上的置换路由

在起点与终点的第一坐标之间逐次取出完美匹配。在给定置换之前和之后分别置换第二坐标，可使每个匹配成为一行。这里证明存在性，不估计运行时间。

**英文原文**

Routing permutations of a finite product

Peel off perfect matchings between the source and destination first coordinates.
Each matching becomes a row by permuting second coordinates before and after
the given permutation. This is an existence result without runtime bounds.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Equiv

variable {A B : Type*} [Fintype A]

-- 读法：`(g (a, b)).2` 属于 `s`。
/-- 若双射对 `s` 以外的每个点都保持其所在的行，则其余各行构成的集合也保持不变。

英文原文：A bijection fixing the row of every point outside `s` preserves the
remaining rows as a set.
-/
private lemma stays_inside (g : Perm (A × B)) (s : Finset B)
    (hg : ∀ a b, b ∉ s → (g (a, b)).2 = b) (a : A) (b : B) (hb : b ∈ s) :
    (g (a, b)).2 ∈ s := by
  by_contra h
  let c := (g (a, b)).2
  have inj : Function.Injective (fun x => (g (x, c)).1) := by
    intro x y hxy
    exact congrArg Prod.fst (g.injective (Prod.ext hxy ((hg x c h).trans (hg y c h).symm)))
  obtain ⟨x, hx⟩ := inj.bijective_of_finite.2 (g (a, b)).1
  have he : (x, c) = (a, b) := g.injective (Prod.ext hx (hg x c h))
  have : c = b := congrArg Prod.snd he
  exact h (show c ∈ s from this.symm ▸ hb)

-- 读法：存在 `p : Perm A`，对每个 `a`，存在 `b ∈ s`，`(g (a, b)).1` 等于 `p a`。这里调用 `Finset.mem_product.mpr`。
private lemma matching (g : Perm (A × B)) (s : Finset B) (hs : s.Nonempty)
    (hg : ∀ a b, b ∉ s → (g (a, b)).2 = b) :
    ∃ p : Perm A, ∀ a, ∃ b ∈ s, (g (a, b)).1 = p a := by
  classical
  let N (a : A) := s.image fun b => (g (a, b)).1
  have hall (t : Finset A) : t.card ≤ (t.biUnion N).card := by
    have maps : Set.MapsTo g (↑(t ×ˢ s)) (↑(t.biUnion N ×ˢ s)) := by
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩,
         stays_inside g s hg a b hb⟩
    have h := Finset.card_le_card_of_injOn g maps g.injective.injOn
    simp only [Finset.card_product] at h
    exact Nat.le_of_mul_le_mul_right h hs.card_pos
  -- 推导：从 `(Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall` 中取出 `f, hf, hm`。
  obtain ⟨f, hf, hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  exact ⟨Equiv.ofBijective f hf.bijective_of_finite, fun a => Finset.mem_image.mp (hm a)⟩

-- 读法：存在 `u v w : Perm (A × B)`，`(∀ p, (u p).1 = p.1)` 与 `(∀ p, (v p).2 = p.2) ∧ (∀ p, (w p).1 = p.1) ∧ g = u * v * w` 同时成立。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
/-- 任意置换都可分解为依次进行的列内置换、行内置换和列内置换。

英文原文：Any permutation factors into permutations of columns, rows, then columns.
-/
theorem perm_factor [Fintype B] (g : Perm (A × B)) :
    ∃ u v w : Perm (A × B),
      (∀ p, (u p).1 = p.1) ∧ (∀ p, (v p).2 = p.2) ∧ (∀ p, (w p).1 = p.1) ∧
      g = u * v * w := by
  classical
  suffices ∀ (s : Finset B) (g : Perm (A × B)), (∀ a b, b ∉ s → (g (a, b)).2 = b) →
      ∃ u v w : Perm (A × B),
        (∀ p, (u p).1 = p.1) ∧ (∀ p, (v p).2 = p.2) ∧ (∀ p, (w p).1 = p.1) ∧
        g = u * v * w from this Finset.univ g (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨1, g, 1, fun _ => rfl, fun p => hg _ _ (by simp), fun _ => rfl, by simp⟩
  | @insert b s hb ih =>
    intro g hg
    obtain ⟨p, hp⟩ := matching g (insert b s) ⟨b, by simp⟩ hg
    choose x hx he using hp
    let y (a : A) := (g (p.symm a, x (p.symm a))).2
    have hy (a : A) : y a ∈ insert b s := stays_inside g _ hg _ _ (hx _)
    let X := prodCongrRight fun a => swap b (x a)
    let Y := prodCongrRight fun a => swap b (y a)
    have ht (a : A) (c : B) (hc : c ∉ s) : ((Y * g * X) (a, c)).2 = c := by
      by_cases heq : c = b
      · subst c
        have ht : g (a, x a) = (p a, y (p a)) := Prod.ext (he a) (by simp [y])
        simp [X, Y, Perm.mul_apply, ht]
      · have h : c ∉ insert b s := by simp [heq, hc]
        have xne : c ≠ x a := fun e => h (e.symm ▸ hx a)
        have yne (j : A) : c ≠ y j := fun e => h (e.symm ▸ hy j)
        change (Y (g (a, swap b (x a) c))).2 = c
        rw [swap_apply_of_ne_of_ne heq xne]
        change swap b (y (g (a, c)).1) (g (a, c)).2 = c
        rw [hg a c h, swap_apply_of_ne_of_ne heq (yne _)]
    -- 推导：从 `ih (Y * g * X) ht` 中取出 `u, v, w, hu, hv, hw, he`。
    obtain ⟨u, v, w, hu, hv, hw, he⟩ := ih (Y * g * X) ht
    refine ⟨Y⁻¹ * u, v, w * X⁻¹, hu, hv, fun z => hw (X⁻¹ z), ?_⟩
    calc
      g = Y⁻¹ * (Y * g * X) * X⁻¹ := by simp [mul_assoc]
      _ = (Y⁻¹ * u) * v * (w * X⁻¹) := by rw [he]; simp [mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 有限配置与有界群轨道的中心

对一族强凸函数的公共上界求极小，可同时处理距离平方的平均值和最大值。

**英文原文**

Centers for finite placements and bounded group orbits

Minimizing the common upper bound of a family of strongly convex
functions treats both the average and the largest squared distance.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Topology
open Filter

variable {Y : Type*} [MetricSpace Y]

-- 读法：存在 `(o : Y) (a : ℝ)`，由 `(∀ i, f i o ≤ a) ∧ ∀ (z : Y) (b : ℝ), (∀ i, f i z ≤ b)` 推出 `a + dist o z ^ 2 ≤ b`。
/-- 最小化一个共同上界。由中点估计，每个单调递减的极小化序列都是柯西序列。

英文原文：Minimize a simultaneous upper bound. The midpoint estimate forces any
decreasing minimizing sequence to be Cauchy.
-/
theorem minimize [CompleteSpace Y] {I : Type*} [Nonempty I]
    (f : I → Y → ℝ) (hc : ∀ i, Continuous (f i)) (hn : ∀ i z, 0 ≤ f i z)
    (hb : ∃ (a : ℝ) (z : Y), ∀ i, f i z ≤ a)
    (hv : ∀ (x y : Y) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ m, ∀ i,
      f i m ≤ (1 - t) * f i x + t * f i y - t * (1 - t) * dist x y ^ 2) :
    ∃ (o : Y) (a : ℝ), (∀ i, f i o ≤ a) ∧
      ∀ (z : Y) (b : ℝ), (∀ i, f i z ≤ b) → a + dist o z ^ 2 ≤ b := by
  let S := {a : ℝ | ∃ z, ∀ i, f i z ≤ a}
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro b ⟨z, hz⟩
    exact (hn (Classical.arbitrary I) z).trans (hz _)
  let a := sInf S
  have hmin (z : Y) (b : ℝ) (h : ∀ i, f i z ≤ b) : a ≤ b :=
    csInf_le hbelow ⟨z, h⟩
  -- 推导：从 `exists_seq_tendsto_sInf (show S.Nonempty from hb) hbelow` 中取出 `u, hu, hlim, hS`。
  obtain ⟨u, hu, hlim, hS⟩ := exists_seq_tendsto_sInf (show S.Nonempty from hb) hbelow
  choose x hx using hS
  have hxu : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0' (fun n => Real.sqrt (4 * (u n - a))) ?_ ?_
    · intro n k hnk
      obtain ⟨m, hm⟩ := hv (x n) (x k) (1 / 2) (by norm_num) (by norm_num)
      have h : a ≤ u n - dist (x n) (x k) ^ 2 / 4 := by
        apply hmin m
        intro i
        linarith [hm i, hx n i, hx k i, hu hnk]
      exact Real.le_sqrt_of_sq_le (by linarith)
    · have ha : Tendsto u atTop (𝓝 a) := hlim
      simpa using ((ha.sub_const a).const_mul 4).sqrt
  -- 推导：从 `cauchySeq_tendsto_of_complete hxu` 中取出 `o, ho`。
  obtain ⟨o, ho⟩ := cauchySeq_tendsto_of_complete hxu
  have hfo (i : I) : f i o ≤ a :=
    le_of_tendsto_of_tendsto' ((hc i).tendsto o |>.comp ho) hlim (fun n => hx n i)
  refine ⟨o, a, hfo, ?_⟩
  intro z b hz
  have hab := hmin z b hz
  by_contra! bad
  have hd : 0 < dist o z ^ 2 := by linarith
  let t := (a + dist o z ^ 2 - b) / (2 * dist o z ^ 2)
  have hpos : 0 < t := div_pos (sub_pos.mpr bad) (by positivity)
  -- 推导：记下中间结论 `hle`：`t ≤ 1`。
  have hle : t ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have he : t * (2 * dist o z ^ 2) = a + dist o z ^ 2 - b :=
    div_mul_cancel₀ _ (by positivity)
  obtain ⟨m, hm⟩ := hv o z t hpos.le hle
  have hh : a ≤ (1 - t) * a + t * b - t * (1 - t) * dist o z ^ 2 := by
    apply hmin m
    intro i
    refine (hm i).trans ?_
    gcongr
    · exact hfo i
    · exact hz i
  have : 0 < t * (a + dist o z ^ 2 - b - t * dist o z ^ 2) :=
    mul_pos hpos (by linarith)
  linarith

-- 读法：存在 `o`，要证明的命题是 `Bary x o`。
theorem Comparison.bary [CompleteSpace Y] (h : Comparison Y)
    {A : Type*} [Fintype A] [Nonempty A] (x : A → Y) : ∃ o, Bary x o := by
  let f (_ : Unit) (z : Y) := 𝔼 i, dist z (x i) ^ 2
  have hc (i : Unit) : Continuous (f i) := by
    simp only [f, Fintype.expect_eq_sum_div_card]
    fun_prop
  have hn (i : Unit) (z : Y) : 0 ≤ f i z :=
    Finset.expect_nonneg fun _ _ => sq_nonneg _
  let z := x (Classical.arbitrary A)
  obtain ⟨o, a, ha, ho⟩ := minimize f hc hn ⟨f () z, z, fun _ => le_rfl⟩ (by
    intro u v t ht ht'
    obtain ⟨m, _, hm⟩ := h u v t ht ht'
    refine ⟨m, fun _ => ?_⟩
    have he := Finset.expect_le_expect (s := Finset.univ) fun i _ => hm (x i)
    simpa only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
      Fintype.expect_const] using he)
  exact ⟨o, fun y => (add_le_add_left (ha ()) _).trans (ho y (f () y) fun _ => le_rfl)⟩

variable {G : Type*} [Group G] [MulAction G Y] [IsIsometricSMul G Y]

-- 读法：`g • o` 等于 `o`。这里调用 `dist_eq_zero.mp`。
theorem Bary.fixed {A : Type*} [Fintype A] {x : A → Y} {o : Y}
    (h : Bary x o) {g : G} (hx : ∀ i, g • x i = x i) : g • o = o := by
  have hd (i : A) : dist (g • o) (x i) = dist o (x i) := by
    rw [← hx i, dist_smul, hx]
  have hv := h (g • o)
  simp_rw [hd] at hv
  exact (dist_eq_zero.mp (by nlinarith : dist o (g • o) = 0)).symm

-- 读法：存在 `o`，`(∀ g ∈ K, g • o = o)` 与 `2 * dist x o ^ 2 ≤ R` 同时成立。
/-- 有界轨道的中心是不动点，它与起点的距离平方不超过所给上界的一半。这里的上界针对距离的平方。

英文原文：The center of a bounded orbit is fixed and within half the squared bound of
the starting point. The bound is on squared distances.
-/
theorem Comparison.orbit [CompleteSpace Y] (h : Comparison Y) (K : Subgroup G)
    (x : Y) (R : ℝ) (hb : ∀ g ∈ K, dist x (g • x) ^ 2 ≤ R) :
    ∃ o, (∀ g ∈ K, g • o = o) ∧ 2 * dist x o ^ 2 ≤ R := by
  let f (g : K) (y : Y) := dist y ((g : G) • x) ^ 2
  obtain ⟨o, a, ha, ho⟩ := minimize f (fun _ => by unfold f; fun_prop)
    (fun _ _ => sq_nonneg _) ⟨R, x, fun g => hb g g.property⟩ (by
      intro u v t ht ht'
      obtain ⟨m, _, hm⟩ := h u v t ht ht'
      exact ⟨m, fun g => hm _⟩)
  refine ⟨o, ?_, ?_⟩
  · intro g hg
    -- 推导：记下中间结论 `hk`：`∀ i, f i (g • o) ≤ a`。
    have hk : ∀ i, f i (g • o) ≤ a := by
      intro i
      have hh := ha ⟨g⁻¹ * i, K.mul_mem (K.inv_mem hg) i.property⟩
      change dist o ((g⁻¹ * i.val) • x) ^ 2 ≤ a at hh
      rw [← dist_smul g, ← mul_smul, mul_inv_cancel_left] at hh
      exact hh
    have := ho (g • o) a hk
    exact (dist_eq_zero.mp (by nlinarith : dist o (g • o) = 0)).symm
  · have hrad : dist o x ^ 2 ≤ a := by simpa [f] using ha 1
    rw [dist_comm]
    linarith [ho x R fun g => hb g g.property]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 匹配独立划分

由 `g` 表示的划分是原划分稳定子群的陪集 `g H`。一对独立的列表 `e, f` 能以两种方式同第三个列表匹配。下述群论条件是位移估计所用的唯一匹配性质。

**英文原文**

Matching independent partitions

The partition represented by `g` is the coset `g H` of the stabilizer of
the original partition. An independent pair `e, f` of lists can be matched
with a third list in two ways. The group-theoretic condition below is all
that the displacement estimate uses about matching.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

-- 读法：`Bridges` 表示以下条件：对每个 `g ∈ K`，存在 `v w : G`，`(∀ i, (e i)⁻¹ * (v * e i) ∈ H)` 与 `(∀ i, (g * e i)⁻¹ * (w * e i) ∈ H) ∧ (∀ i, (v * f i)⁻¹ * (w * f i) ∈ H)` 同时成立。
/-- `v` 固定各个 `e` 分划，`w` 把它们送到它们的 `g` 平移；两者都将各个 `f` 分划送到同一个第三列表。

英文原文：`v` fixes the `e`-partitions, `w` takes them to their `g`-translates,
and both take the `f`-partitions to the same third list.
-/
def Bridges {G : Type*} [Group G] (H K : Subgroup G) {d : ℕ} (e f : Fin d → G) : Prop :=
  ∀ g ∈ K, ∃ v w : G,
    (∀ i, (e i)⁻¹ * (v * e i) ∈ H) ∧
    (∀ i, (g * e i)⁻¹ * (w * e i) ∈ H) ∧
    (∀ i, (v * f i)⁻¹ * (w * f i) ∈ H)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 独立划分列表可同时匹配

在每条纤维中，把地址表示为第一份名称列表与附带未用坐标的第二份名称列表的乘积。三阶段置换路由即给出位移估计所需的公共第三列表。在对此分解封闭的较小群中，同一论证仍然成立。

**英文原文**

Independent partition lists admit simultaneous matching

In each fiber write the address as a product of the first list of names
and the second list with its unused coordinates. Three-stage permutation
routing then gives the common third list needed in the displacement estimate.
The same argument works in a smaller group closed under this factorization.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

-- 读法：要证明的命题是 `Bridges H K e f`。这里调用 `H.inv_mem`。
/-- 在两个联合稳定子之间交替选取因子的分解，给出位移估计所需的两次匹配。

英文原文：A factorization alternating between the two joint stabilizers produces
the two matches required for the displacement estimate.
-/
theorem bridges_of_factor {G : Type*} [Group G] (H K : Subgroup G) {d : ℕ}
    (e f : Fin d → G)
    (factor : ∀ g ∈ K, ∃ u v w : G, g = u * v * w ∧
      (∀ i, (e i)⁻¹ * (u * e i) ∈ H) ∧ (∀ i, (f i)⁻¹ * (v * f i) ∈ H) ∧
      (∀ i, (e i)⁻¹ * (w * e i) ∈ H)) :
    Bridges H K e f := by
  intro g hg
  obtain ⟨u, v, w, rfl, hu, hv, hw⟩ := factor g hg
  refine ⟨u, u * v, hu, ?_, ?_⟩
  · intro i
    simpa [mul_inv_rev, mul_assoc] using H.inv_mem (hw i)
  · intro i
    simpa [mul_inv_rev, mul_assoc] using hv i

variable {J : Type} {X C : J → Type}

-- 读法：用字段 `carrier`、`one_mem'`、`mul_mem'`、`inv_mem'` 构造 `Subgroup (∀ i, Equiv.Perm (X i))`。
/-- 在所有实例上同时保持每个名称的置换。

英文原文：The permutations preserving each name, simultaneously for all instances.
-/
def preserving (name : ∀ i, X i → C i) : Subgroup (∀ i, Equiv.Perm (X i)) where
  carrier := {g | ∀ i x, name i (g i x) = name i x}
  one_mem' := fun _ _ => rfl
  mul_mem' hg hh := fun i x => (hg i _).trans (hh i x)
  inv_mem' {g} hg := fun i x => by simpa using (hg i ((g i).symm x)).symm

-- 读法：结论为 `∃ u v w : Equiv.Perm X, g = u * v * w ∧ (∀ x, (s (u x)).1 = (s x).1 ∧ (s (u x)).2.1 = (s x).2.1) ∧ (∀ x, (s (v x)).1 = (s x).1 ∧ (s (v x)).2.2 = (s x).2.2) ∧ (∀ x, (s (w x)).1 = (s x).1 ∧ (s (w x)).2.1 = (s x).2.1)`。
theorem factor_in_fibers {X C A B : Type} [Fintype A] [Fintype B]
    (s : X ≃ C × (A × B)) (g : Equiv.Perm X) (hg : ∀ x, (s (g x)).1 = (s x).1) :
    ∃ u v w : Equiv.Perm X, g = u * v * w ∧
      (∀ x, (s (u x)).1 = (s x).1 ∧ (s (u x)).2.1 = (s x).2.1) ∧
      (∀ x, (s (v x)).1 = (s x).1 ∧ (s (v x)).2.2 = (s x).2.2) ∧
      (∀ x, (s (w x)).1 = (s x).1 ∧ (s (w x)).2.1 = (s x).2.1) := by
  let r := s.permCongr g
  have hr (c : C) (p : A × B) : (r (c, p)).1 = c := by simp [r, hg]
  let φ (c : C) (p : A × B) := (r (c, p)).2
  have hi (c : C) : Function.Injective (φ c) := by
    intro x y h
    exact congrArg Prod.snd (r.injective (Prod.ext ((hr c x).trans (hr c y).symm) h))
  let ψ (c : C) := Equiv.ofBijective (φ c) ⟨hi c, Finite.surjective_of_injective (hi c)⟩
  choose u v w hu hv hw he using fun c => perm_factor (ψ c)
  let lift (t : C → Equiv.Perm (A × B)) := s.symm.permCongr (Equiv.prodCongrRight t)
  have hl (t : C → Equiv.Perm (A × B)) (x : X) :
      s (lift t x) = ((s x).1, t (s x).1 (s x).2) := by
    simp [lift, Equiv.prodCongrRight]
  refine ⟨lift u, lift v, lift w, ?_, ?_, ?_, ?_⟩
  · apply Equiv.ext
    intro x
    apply s.injective
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hl, hl, hl]
    refine Prod.ext (hg x) ?_
    have hx := DFunLike.congr_fun (he (s x).1) (s x).2
    simpa [ψ, φ, r] using hx
  · intro x; rw [hl]; exact ⟨rfl, hu _ _⟩
  · intro x; rw [hl]; exact ⟨rfl, hv _ _⟩
  · intro x; rw [hl]; exact ⟨rfl, hw _ _⟩

-- 读法：结构的字段包括 `World`、`read`、`fixed`、`read_fixed`、`factor`。
/-- 一个置换函数族。实例索引决定地址格式，一个全局状态则为每个实例给定输入。需要能够使用固定的函数族以及乘积坐标图中的三个因子。

英文原文：A family of permutation functions. An instance index determines the
address format, and a world supplies the input at every instance. Fixed
families and the three factors in a product chart must be available.
-/
structure PermSystem (X : J → Type) (G : Type) [Group G] where
  World : Type
  read : World → G →* (∀ j, Equiv.Perm (X j))
  fixed : (∀ j, Equiv.Perm (X j)) → G
  read_fixed : ∀ t a, read t (fixed a) = a
  factor : ∀ {C A B : J → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (s : ∀ i, X i ≃ C i × (A i × B i)) (g : G),
    (∀ t i x, (s i (read t g i x)).1 = (s i x).1) →
    ∃ u v w : G, g = u * v * w ∧
      (∀ t i x, (s i (read t u i x)).1 = (s i x).1 ∧ (s i (read t u i x)).2.1 = (s i x).2.1) ∧
      (∀ t i x, (s i (read t v i x)).1 = (s i x).1 ∧ (s i (read t v i x)).2.2 = (s i x).2.2) ∧
      (∀ t i x, (s i (read t w i x)).1 = (s i x).1 ∧ (s i (read t w i x)).2.1 = (s i x).2.1)

namespace PermSystem
variable {G : Type} [Group G] (M : PermSystem X G)

-- 读法：用字段 `carrier`、`one_mem'`、`mul_mem'`、`inv_mem'` 构造 `Subgroup G`。
/-- 要求对每个输入均满足成员关系。

英文原文：Require membership on every input.
-/
def pull (H : Subgroup (∀ i, Equiv.Perm (X i))) : Subgroup G where
  carrier := {g | ∀ t, M.read t g ∈ H}
  one_mem' := by simp
  mul_mem' ha hb t := by rw [map_mul]; exact H.mul_mem (ha t) (hb t)
  inv_mem' ha t := by rw [map_inv]; exact H.inv_mem (ha t)

-- 读法：`M.pull H` 不超过 `M.pull K`。
theorem pull_mono {H K : Subgroup (∀ i, Equiv.Perm (X i))} (h : H ≤ K) :
    M.pull H ≤ M.pull K := fun _ hg t => h (hg t)

-- 读法：用字段 `World`、`read`、`fixed`、`read_fixed` 构造 `PermSystem X (∀ i, Equiv.Perm (X i))`。
def full (X : J → Type) : PermSystem X (∀ i, Equiv.Perm (X i)) where
  World := Unit
  read _ := MonoidHom.id _
  fixed := id
  read_fixed _ _ := rfl
  factor s g h := by
    choose u v w he hu hv hw using fun i => factor_in_fibers (s i) (g i) (h () i)
    exact ⟨u, v, w, funext he, fun _ => hu, fun _ => hv, fun _ => hw⟩

-- 读法：`(full X).pull H` 等于 `H`。使用 `le_antisymm` 给出的结论。
@[simp] theorem full_pull (H : Subgroup (∀ i, Equiv.Perm (X i))) : (full X).pull H = H :=
  le_antisymm (fun _ hg => hg ()) (fun _ hg _ => hg)

-- 读法：要证明的命题是 `Bridges (M.pull (preserving name)) (M.pull (preserving base)) (M.fixed ∘ e) (M.fixed ∘ f)`。这里调用 `bridges_of_factor`。
/-- 在基底的每条纤维上，联合名称给出一个乘积的坐标。未用的坐标可以归入两个因子中的任一个。

英文原文：The joint names are coordinates on a product in each base fiber.
Unused coordinates may be included in either of the two factors.
-/
theorem bridges_of_product {Y A B : J → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (base : ∀ i, X i → C i) (name : ∀ i, X i → Y i)
    {d : ℕ} (e f : Fin d → ∀ i, Equiv.Perm (X i)) (s : ∀ i, X i ≃ C i × (A i × B i))
    (hs : ∀ i x, (s i x).1 = base i x)
    (he : ∀ j i x y, (s i x).1 = (s i y).1 → (s i x).2.1 = (s i y).2.1 →
      name i ((e j i).symm x) = name i ((e j i).symm y))
    (hf : ∀ j i x y, (s i x).1 = (s i y).1 → (s i x).2.2 = (s i y).2.2 →
      name i ((f j i).symm x) = name i ((f j i).symm y)) :
    Bridges (M.pull (preserving name)) (M.pull (preserving base)) (M.fixed ∘ e) (M.fixed ∘ f) := by
  apply bridges_of_factor
  intro g hg
  have hg' (t : M.World) (i : J) (x : X i) : (s i (M.read t g i x)).1 = (s i x).1 := by
    rw [hs, hs, hg t]
  -- 推导：从 `M.factor s g hg'` 中取出 `u, v, w, heq, hu, hv, hw`。
  obtain ⟨u, v, w, heq, hu, hv, hw⟩ := M.factor s g hg'
  refine ⟨u, v, w, heq, ?_, ?_, ?_⟩
  · intro j t
    simp only [map_inv, map_mul, Function.comp_apply, read_fixed]
    intro i x
    simpa using he j i _ _ (hu t i (e j i x)).1 (hu t i (e j i x)).2
  · intro j t
    simp only [map_inv, map_mul, Function.comp_apply, read_fixed]
    intro i x
    simpa using hf j i _ _ (hv t i (f j i x)).1 (hv t i (f j i x)).2
  · intro j t
    simp only [map_inv, map_mul, Function.comp_apply, read_fixed]
    intro i x
    simpa using he j i _ _ (hw t i (e j i x)).1 (hw t i (e j i x)).2

end PermSystem
end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 单个平面上的位移

只需对成对出现的划分作匹配。对至少一半的有序对，匹配论证给出轨道直径不超过该对距离的两倍。平方后取平均，即可用仿射放置的方差控制直径。

**英文原文**

Displacement on a single plane

We only need to match *pairs* of partitions. For at least half of the
ordered pairs the matching argument bounds the diameter of the orbit by
twice the pair distance. Squaring and averaging gives a diameter bound
in terms of the variance of the affine placement.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Classical

variable {Y A B D E G : Type*} [MetricSpace Y]

-- 读法：`Incidence` 表示以下条件：对每个 `(x : A → Y) (y : B → Y) (o : Y)`，使 `Bary x o → 9 * (∑ i, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) ≤ 10 * ∑ i, dist (x (p i)) (y (l i)) ^ 2` 成立。
/-- 按旗标计数作归一化时，`q ≥ 100` 下的关联估计。

英文原文：The incidence estimate at `q ≥ 100` in flag-counting normalization.
-/
def Incidence (Y : Type*) [MetricSpace Y] [Fintype E] [Fintype A]
    (p : E → A) (l : E → B) : Prop :=
  ∀ (x : A → Y) (y : B → Y) (o : Y), Bary x o →
    9 * (∑ i, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) ≤
      10 * ∑ i, dist (x (p i)) (y (l i)) ^ 2

-- 读法：`9 * ((𝔼 i, dist o (x (p i)) ^ 2) + (𝔼 i, dist o (y (l i)) ^ 2))` 不超过 `10 * (𝔼 i, dist (x (p i)) (y (l i)) ^ 2)`。这里调用 `div_le_div_of_nonneg_right`。
theorem Incidence.estimate [Fintype E] [Nonempty E] [Fintype A]
    {p : E → A} {l : E → B} (h : Incidence Y p l)
    {x : A → Y} (y : B → Y) {o : Y} (ho : Bary x o) :
    9 * ((𝔼 i, dist o (x (p i)) ^ 2) + (𝔼 i, dist o (y (l i)) ^ 2)) ≤
      10 * (𝔼 i, dist (x (p i)) (y (l i)) ^ 2) := by
  rw [← Finset.expect_add_distrib]
  simp only [Fintype.expect_eq_sum_div_card, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h x y o ho) (by positivity)

-- 读法：`(𝔼 p, f p)` 等于 `𝔼 i, 𝔼 j, f (i, j)`。
theorem expect_pair [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 i, 𝔼 j, f (i, j) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

-- 读法：`dist x z ^ 2` 不超过 `2 * dist x y ^ 2 + 2 * dist y z ^ 2`。
theorem dist_sq_triangle (x y z : Y) :
    dist x z ^ 2 ≤ 2 * dist x y ^ 2 + 2 * dist y z ^ 2 := by
  have h := pow_le_pow_left₀ dist_nonneg (dist_triangle x y z) 2
  nlinarith only [h, sq_nonneg (dist x y - dist y z)]

variable [Group G] [MulAction G Y] [IsIsometricSMul G Y]

-- 读法：`Fixes` 表示以下条件：对每个 `g ∈ K`，`g • x` 等于 `x`。
def Fixes (K : Subgroup G) (x : Y) : Prop := ∀ g ∈ K, g • x = x

omit [MetricSpace Y] [IsIsometricSMul G Y] in
-- 读法：`h • x` 等于 `g • x`。
private theorem Fixes.coset {K : Subgroup G} {x : Y} (hx : Fixes K x)
    {g h : G} (he : g⁻¹ * h ∈ K) : h • x = g • x := by
  rw [← mul_inv_cancel_left g h, mul_smul, hx _ he]

-- 读法：`dist x (g • x)` 不超过 `2 * dist (a • x) (b • x)`。
private theorem pair_displacement {H K : Subgroup G} {x : Y} (hx : Fixes H x)
    {a b : G} (ha : a ∈ K)
    (hp : Bridges H K (fun _ : Fin 1 => a) (fun _ => b)) {g : G} (hg : g ∈ K) :
    dist x (g • x) ≤ 2 * dist (a • x) (b • x) := by
  obtain ⟨v, w, hv, hw, hb⟩ := hp (a * g * a⁻¹) (K.mul_mem (K.mul_mem ha hg) (K.inv_mem ha))
  have h₁ : v • (a • x) = a • x := by simpa [mul_smul] using hx.coset (hv 0)
  have h₂ : w • (a • x) = a • (g • x) := by simpa [mul_smul] using hx.coset (hw 0)
  have h₃ : w • (b • x) = v • (b • x) := by simpa [mul_smul] using hx.coset (hb 0)
  calc
    dist x (g • x) = dist (v • (a • x)) (w • (a • x)) := by rw [h₁, h₂, dist_smul]
    _ ≤ dist (v • (a • x)) (v • (b • x)) + dist (w • (b • x)) (w • (a • x)) := by
      rw [h₃]
      exact dist_triangle _ _ _
    _ = _ := by rw [dist_smul, dist_smul, dist_comm (b • x), two_mul]

-- 读法：结构的字段包括 `mem`、`projects`、`half`。
/-- 仿射点分划的陪集及其沿各方向的投影。`l` 给出经过一个旗标的仿射直线。

英文原文：Cosets for the affine point partitions and their projections along
each direction. `l` gives the affine line through a flag.
-/
structure PlaneAction [Fintype A] (H K : Subgroup G) (L : D → Subgroup G)
    (l : A × D → B) (σ : A → G) : Prop where
  mem : ∀ a, σ a ∈ K
  projects : ∀ a a' d d', l (a, d) = l (a', d') →
    d = d' ∧ (σ a)⁻¹ * σ a' ∈ L d
  half : Fintype.card (A × A) ≤ 2 * (Finset.univ.filter fun p : A × A =>
    Bridges H K (fun _ : Fin 1 => σ p.1) (fun _ => σ p.2)).card

-- 读法：`v` 不超过 `2 * (𝔼 e, f e)`。这里调用 `le_of_mul_le_mul_left`。
private theorem half_bound [Fintype E] [Nonempty E] (s : Finset E) (f : E → ℝ) (v : ℝ)
    (hv : 0 ≤ v) (hf : ∀ e, 0 ≤ f e) (hs : Fintype.card E ≤ 2 * s.card)
    (h : ∀ e ∈ s, v ≤ f e) : v ≤ 2 * (𝔼 e, f e) := by
  have hm : (s.card : ℝ) * v ≤ ∑ e : E, f e := by
    calc
      _ = ∑ _ ∈ s, v := by simp
      _ ≤ ∑ e ∈ s, f e := Finset.sum_le_sum h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => hf i)
  rw [← Fintype.card_mul_expect] at hm
  have hs' : (Fintype.card E : ℝ) ≤ 2 * s.card := by exact_mod_cast hs
  apply le_of_mul_le_mul_left _ (show 0 < (Fintype.card E : ℝ) by positivity)
  linarith only [hm, mul_le_mul_of_nonneg_right hs' hv]

variable [Fintype A] [Nonempty A] {H K : Subgroup G} {L : D → Subgroup G}
  {l : A × D → B} {σ : A → G}

-- 读法：`dist x (g • x) ^ 2` 不超过 `32 * (𝔼 i, dist o (σ i • x) ^ 2)`。
private theorem PlaneAction.orbit_bound (h : PlaneAction H K L l σ) {x : Y}
    (hx : Fixes H x) (o : Y) (g : G) (hg : g ∈ K) :
    dist x (g • x) ^ 2 ≤ 32 * (𝔼 i, dist o (σ i • x) ^ 2) := by
  let f (e : A × A) := 8 * dist o (σ e.1 • x) ^ 2 + 8 * dist o (σ e.2 • x) ^ 2
  have hb : dist x (g • x) ^ 2 ≤ 2 * (𝔼 e, f e) := by
    refine half_bound _ f _ (sq_nonneg _) (fun _ => by unfold f; positivity) h.half ?_
    intro e he
    have ht := dist_sq_triangle (σ e.1 • x) o (σ e.2 • x)
    rw [dist_comm (σ e.1 • x) o] at ht
    have hd := pair_displacement hx (h.mem _) (Finset.mem_filter.mp he).2 hg
    dsimp only [f]
    linarith only [ht, pow_le_pow_left₀ dist_nonneg hd 2]
  rw [expect_pair] at hb
  simp only [f, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hb
  linarith

-- 读法：存在 `z`，`Fixes K z` 与 `9 * dist x z ^ 2 ≤ 160 * (𝔼 d, dist x (y d) ^ 2)` 同时成立。按 `∃ e, l e = b` 成立与否分情况。
/-- 给定一个被基底固定的点，并为每个方向给定一个被该方向固定的点，则存在一个被整个平面固定的点，其相应距离受从基底到各方向的平均能量控制。

英文原文：Given a point fixed by the base and one fixed by each direction, there
is a plane-fixed point controlled by the mean base-to-direction energy.
-/
theorem PlaneAction.fixed [Fintype D] [Nonempty D] [CompleteSpace Y]
    (h : PlaneAction H K L l σ) (C : Comparison Y) (hi : Incidence Y Prod.fst l)
    {x : Y} (hx : Fixes H x) (y : D → Y) (hy : ∀ d, Fixes (L d) (y d)) :
    ∃ z, Fixes K z ∧ 9 * dist x z ^ 2 ≤ 160 * (𝔼 d, dist x (y d) ^ 2) := by
  let v := fun a => σ a • x
  let w := fun e : A × D => σ e.1 • y e.2
  have hline : ∃ u : B → Y, ∀ e, u (l e) = w e := by
    have hw : ∀ b, ∃ z, ∀ e, l e = b → z = w e := by
      intro b
      by_cases he : ∃ e, l e = b
      -- 推导：从 `he` 中取出 `⟨a, d⟩, h₁`。
      · obtain ⟨⟨a, d⟩, h₁⟩ := he
        refine ⟨w (a, d), ?_⟩
        rintro ⟨a', d'⟩ h₂
        obtain ⟨rfl, hp⟩ := h.projects _ _ _ _ (h₁.trans h₂.symm)
        exact ((hy d).coset hp).symm
      · exact ⟨x, fun e he' => (he ⟨e, he'⟩).elim⟩
    choose u hu using hw
    exact ⟨u, fun e => hu _ e rfl⟩
  obtain ⟨u, hu⟩ := hline
  obtain ⟨o, ho⟩ := C.bary v
  -- 推导：从 `C.orbit K x _ (h.orbit_bound hx o)` 中取出 `z, hz, hd`。
  obtain ⟨z, hz, hd⟩ := C.orbit K x _ (h.orbit_bound hx o)
  refine ⟨z, hz, ?_⟩
  have hb := hi.estimate u ho
  have hn : 0 ≤ (𝔼 i : A × D, dist o (u (l i)) ^ 2) :=
    Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hv : 9 * (𝔼 i : A × D, dist o (v i.1) ^ 2) ≤
      10 * (𝔼 i : A × D, dist (v i.1) (u (l i)) ^ 2) := by linarith
  simp only [hu, v, w, dist_smul] at hv
  rw [expect_pair, expect_pair] at hv
  simp only [Fintype.expect_const] at hv
  linarith only [hd, hv]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 逐次构造测地均值

样本空间是完整的有限笛卡尔幂。在给定元组尾部的条件下，均方误差的计算可归结为一步方差计算。

**英文原文**

Successive geodesic means

The sample space is a full finite power. Conditioning on the tail of a
tuple reduces the mean squared error to a one-step variance computation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators

variable {Y : Type*} [MetricSpace Y] (C : Comparison Y)

-- 读法：`weight` 的结果类型为 `Set.Icc (0 : ℝ) 1`。
private def weight (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / ((n : ℝ) + 2), by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩

-- 读法：逐一匹配以下输入模式：`0, x`、`n + 1, x`。
/-- 有序元组的均值，按从最后一项到第一项的次序计算。

英文原文：Mean of an ordered tuple, read from its last entry to its first.
-/
def sampleMean {T : Type*} (f : Fraction → T → T → T) :
    (n : ℕ) → (Fin (n + 1) → T) → T
  | 0, x => x 0
  | n + 1, x => f (weight n) (sampleMean f n (Fin.tail x)) (x 0)

-- 读法：`φ (sampleMean f n x)` 等于 `sampleMean g n (φ ∘ x)`。对 `n` 作归纳。
theorem sampleMean_map {T T' : Type*} (f : Fraction → T → T → T)
    (g : Fraction → T' → T' → T') (φ : T → T')
    (h : ∀ u x y, φ (f u x y) = g u (φ x) (φ y)) (n : ℕ) (x : Fin (n + 1) → T) :
    φ (sampleMean f n x) = sampleMean g n (φ ∘ x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sampleMean, h, ih]
    rfl

-- 读法：`(sampleMean C.seg n)` 是连续映射。对 `n` 作归纳。
@[fun_prop] theorem continuous_sampleMean (n : ℕ) : Continuous (sampleMean C.seg n) := by
  induction n with
  | zero => exact continuous_apply _
  | succ n ih =>
    have h := (uniformContinuous_along (C.seg (weight n)) (C.along (weight n))).continuous
    have ht : Continuous (fun x : Fin (n + 1 + 1) → Y => Fin.tail x) :=
      continuous_pi fun i => continuous_apply i.succ
    exact h.comp ((ih.comp ht).prodMk (continuous_apply 0))

variable {A : Type*} [Fintype A] [Nonempty A]

-- 读法：`((n : ℝ) + 2) ^ 2 * (𝔼 i, dist (C.seg (weight n) y (x i)) o ^ 2)` 不超过 `((n : ℝ) + 1) ^ 2 * dist y o ^ 2 + (𝔼 i, dist o (x i) ^ 2)`。这里调用 `C.along`。
private theorem step_estimate {x : A → Y} {o : Y} (ho : Bary x o) (n : ℕ) (y : Y) :
    ((n : ℝ) + 2) ^ 2 * (𝔼 i, dist (C.seg (weight n) y (x i)) o ^ 2) ≤
      ((n : ℝ) + 1) ^ 2 * dist y o ^ 2 + (𝔼 i, dist o (x i) ^ 2) := by
  let t := (weight n).val
  have ht : 0 ≤ t * (1 - t) := mul_nonneg (weight n).2.1 (sub_nonneg.mpr (weight n).2.2)
  have h (i : A) : dist (C.seg (weight n) y (x i)) o ^ 2 ≤
      (1 - t) * dist y o ^ 2 + t * dist o (x i) ^ 2 - t * (1 - t) * dist y (x i) ^ 2 := by
    rw [dist_comm o]
    exact C.along _ _ _ o
  have he := Finset.expect_le_expect (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const] at he
  have hb := mul_le_mul_of_nonneg_left (ho y) ht
  rw [dist_comm o y] at hb
  have hh : (𝔼 i, dist (C.seg (weight n) y (x i)) o ^ 2) ≤
      (1 - t) ^ 2 * dist y o ^ 2 + t ^ 2 * (𝔼 i, dist o (x i) ^ 2) := by linarith only [he, hb]
  calc
    _ ≤ ((n : ℝ) + 2) ^ 2 * ((1 - t) ^ 2 * dist y o ^ 2 + t ^ 2 * (𝔼 i, dist o (x i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by dsimp [t, weight]; field_simp; ring

-- 读法：`((n : ℝ) + 1) * (𝔼 u : Fin (n + 1) → A, dist (sampleMean C.seg n (x ∘ u)) o ^ 2)` 不超过 `𝔼 i, dist o (x i) ^ 2`。对 `n` 作归纳。
/-- 样本均值的期望平方误差至多为单次抽样的方差除以独立抽样次数。

英文原文：The expected squared error of the sample mean is at most the variance
of one draw divided by the number of independent draws.
-/
theorem sampleMean_error {x : A → Y} {o : Y} (ho : Bary x o) (n : ℕ) :
    ((n : ℝ) + 1) * (𝔼 u : Fin (n + 1) → A, dist (sampleMean C.seg n (x ∘ u)) o ^ 2) ≤
      𝔼 i, dist o (x i) ^ 2 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_mul]
    refine le_of_eq (Fintype.expect_equiv (Equiv.funUnique (Fin 1) A) _ _ ?_)
    intro u
    exact congrArg (· ^ 2) (dist_comm _ _)
  | succ n ih =>
    let f := fun u : Fin (n + 1) → A => sampleMean C.seg n (x ∘ u)
    have he : (𝔼 u : Fin (n + 1 + 1) → A, dist (sampleMean C.seg (n + 1) (x ∘ u)) o ^ 2) =
        𝔼 u : Fin (n + 1) → A, 𝔼 i, dist (C.seg (weight n) (f u) (x i)) o ^ 2 := by
      let E := (Fin.consEquiv (fun _ : Fin (n + 1 + 1) => A)).symm.trans (Equiv.prodComm _ _)
      let F := fun p : (Fin (n + 1) → A) × A => dist (C.seg (weight n) (f p.1) (x p.2)) o ^ 2
      exact (Fintype.expect_equiv E _ F (fun _ => rfl)).trans (expect_pair F)
    -- 推导：记下中间结论 `h`：`= Finset.expect_le_expect (s`。
    have h := Finset.expect_le_expect (s := Finset.univ)
      (fun u _ => step_estimate C ho n (f u))
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at h
    rw [he, Nat.cast_succ]
    have hb := mul_le_mul_of_nonneg_left ih (show 0 ≤ (n : ℝ) + 1 by positivity)
    dsimp only [f] at h ⊢
    apply le_of_mul_le_mul_left _ (show 0 < (n : ℝ) + 2 by positivity)
    linarith only [h, hb]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 用有限多个测地项的不等式表示关联关系

用随机逐次均值代替重心。关于任何锚点的二阶矩都能一致控制其均方误差。所得检验对距离平方呈线性，因此可与有限均匀平均及逐点极限交换，无须选择彼此相容的重心。

**英文原文**

Incidence as inequalities in finitely many geodesic terms

Replace the barycenter by a random successive mean. Its mean squared
error is uniformly controlled by the second moment about any anchor.
The resulting tests are linear in squared distances. They pass through
uniform finite averages and pointwise limits without any choice of
compatible barycenters.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators Topology
open Filter

variable {Y A E B T : Type*} [MetricSpace Y]

-- 读法：`dsq` 的取值由 `dist x y ^ 2` 给出。
def dsq (x y : Y) : ℝ := dist x y ^ 2

-- 读法：`dsq x z` 不超过 `(1 + t) * dsq y z + (1 + t⁻¹) * dsq x y`。这里调用 `le_of_mul_le_mul_left`。
private theorem young (x y z : Y) {t : ℝ} (ht : 0 < t) :
    dsq x z ≤ (1 + t) * dsq y z + (1 + t⁻¹) * dsq x y := by
  have h := pow_le_pow_left₀ dist_nonneg (dist_triangle x y z) 2
  apply le_of_mul_le_mul_left _ ht
  unfold dsq
  rw [mul_add, ← mul_assoc t (1 + t⁻¹), mul_add t 1, mul_inv_cancel₀ ht.ne']
  linarith only [mul_le_mul_of_nonneg_left h ht.le, sq_nonneg (t * dist y z - dist x y)]

variable [Fintype E] [Nonempty E] [Fintype A] [Nonempty A]

-- 读法：`joint` 的取值由 `𝔼 i, (R z (u i) + R z (v i))` 给出。
/-- 将旗标分布的两侧都移到 `z` 的成本。

英文原文：Cost of moving both sides of the flag distribution to `z`.
-/
def joint (R : T → T → ℝ) (u v : E → T) (z : T) : ℝ :=
  𝔼 i, (R z (u i) + R z (v i))

-- 读法：`joint dsq u v z` 不超过 `(1 + t) * joint dsq u v w + 2 * (1 + t⁻¹) * dsq z w`。
private theorem joint_le (u v : E → Y) (z w : Y) {t : ℝ} (ht : 0 < t) :
    joint dsq u v z ≤ (1 + t) * joint dsq u v w + 2 * (1 + t⁻¹) * dsq z w := by
  have h (i : E) : dsq z (u i) + dsq z (v i) ≤
      (1 + t) * (dsq w (u i) + dsq w (v i)) + 2 * (1 + t⁻¹) * dsq z w := by
    linarith only [young z w (u i) ht, young z w (v i) ht]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ => h i)
  simpa only [joint, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] using hh

-- 读法：`Tests` 的结果类型为 `Prop`。
def Tests (R : T → T → ℝ) (s : Fraction → T → T → T) (p : E → A) (l : E → B) : Prop :=
  ∀ (x : A → T) (y : B → T) (b : T) (n : ℕ) (t : ℝ), 0 < t →
    9 * (𝔼 u : Fin (n + 1) → A, joint R (x ∘ p) (y ∘ l) (sampleMean s n (x ∘ u))) ≤
      10 * (1 + t) * (𝔼 i, R (x (p i)) (y (l i))) +
        18 * (1 + t⁻¹) / (n + 1) * (𝔼 i, R b (x i))

omit [Nonempty E] in
-- 读法：`(𝔼 u : Fin (n + 1) → A, dsq (sampleMean C.seg n (x ∘ u)) o)` 不超过 `(𝔼 i, dsq b (x i)) / (n + 1)`。这里调用 `le_div_iff₀`。
private theorem sample_variance (C : Comparison Y) {x : A → Y} {o : Y}
    (ho : Bary x o) (b : Y) (n : ℕ) :
    (𝔼 u : Fin (n + 1) → A, dsq (sampleMean C.seg n (x ∘ u)) o) ≤
      (𝔼 i, dsq b (x i)) / (n + 1) := by
  unfold dsq
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [sampleMean_error C ho n, ho b, sq_nonneg (dist o b)]

-- 读法：要证明的命题是 `Tests dsq C.seg p l`。这里调用 `h.estimate`。
theorem Incidence.tests [CompleteSpace Y] {p : E → A} {l : E → B}
    (h : Incidence Y p l) (C : Comparison Y) : Tests dsq C.seg p l := by
  intro x y b n t ht
  obtain ⟨o, ho⟩ := C.bary x
  let J := joint dsq (x ∘ p) (y ∘ l)
  let m := fun u : Fin (n + 1) → A => sampleMean C.seg n (x ∘ u)
  have hJ : 9 * J o ≤ 10 * (𝔼 i, dsq (x (p i)) (y (l i))) := by
    unfold J joint dsq
    rw [Finset.expect_add_distrib]
    exact h.estimate y ho
  have h₁ (u : Fin (n + 1) → A) : J (m u) ≤ (1 + t) * J o + 2 * (1 + t⁻¹) * dsq (m u) o :=
    joint_le _ _ _ _ ht
  -- 推导：记下中间结论 `he`：`= Finset.expect_le_expect (s`。
  have he := Finset.expect_le_expect (s := Finset.univ) (fun u _ => h₁ u)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at he
  have hv := mul_le_mul_of_nonneg_left (sample_variance C ho b n)
    (show 0 ≤ 18 * (1 + t⁻¹) by positivity)
  have hi := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 1 + t by positivity)
  dsimp only [m, J] at he hi
  simp only [div_eq_mul_inv] at hv ⊢
  linarith only [he, hv, hi]

-- 读法：要证明的命题是 `Incidence Y p l`。这里调用 `tendsto_one_div_add_atTop_nhds_zero_nat`。
theorem Tests.incidence {p : E → A} {l : E → B}
    {C : Comparison Y} (h : Tests dsq C.seg p l) : Incidence Y p l := by
  intro x y o ho
  let J := joint dsq (x ∘ p) (y ∘ l)
  let R := 𝔼 i, dsq (x (p i)) (y (l i))
  let V := 𝔼 i, dsq o (x i)
  have htend : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim (t : ℝ) (ht : 0 < t) : 9 * J o ≤ 10 * (1 + t) ^ 2 * R := by
    let K := 18 * (2 + t) * (1 + t⁻¹) * V
    have hb (n : ℕ) : 9 * J o ≤ 10 * (1 + t) ^ 2 * R + K * ((n : ℝ) + 1)⁻¹ := by
      let m := fun u : Fin (n + 1) → A => sampleMean C.seg n (x ∘ u)
      have h₁ (u : Fin (n + 1) → A) : J o ≤ (1 + t) * J (m u) + 2 * (1 + t⁻¹) * dsq (m u) o := by
        rw [show dsq (m u) o = dsq o (m u) by simp only [dsq, dist_comm]]
        exact joint_le _ _ _ _ ht
      -- 推导：记下中间结论 `he`：`= Finset.expect_le_expect (s`。
      have he := Finset.expect_le_expect (s := Finset.univ) (fun u _ => h₁ u)
      simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at he
      have hv := mul_le_mul_of_nonneg_left (sample_variance C ho o n)
        (show 0 ≤ 18 * (1 + t⁻¹) by positivity)
      have hi := mul_le_mul_of_nonneg_left (h x y o n t ht) (show 0 ≤ 1 + t by positivity)
      dsimp only [m, J, K, R, V] at he ⊢
      simp only [div_eq_mul_inv] at hi hv
      linarith only [he, hi, hv]
    simpa using ge_of_tendsto' ((htend.const_mul K).const_add (10 * (1 + t) ^ 2 * R)) hb
  have hf : Continuous (fun t : ℝ => 10 * (1 + t) ^ 2 * R) := by fun_prop
  -- 推导：记下中间结论 `hJ`：`9 * J o ≤ 10 * R`。
  have hJ : 9 * J o ≤ 10 * R := by
    simpa using ge_of_tendsto' ((hf.tendsto 0).comp htend) (fun n => hlim _ (by positivity))
  simp only [J, joint, R, dsq, Function.comp_apply, Fintype.expect_eq_sum_div_card,
    ← mul_div_assoc, div_le_div_iff_of_pos_right (show 0 < (Fintype.card E : ℝ) by positivity)] at hJ
  exact hJ

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 补全测地项之间的距离平方表

该表不必区分不同的项。度量完备化把距离为零的项等同，并同时延拓插值和群作用。

**英文原文**

Completing a table of squared distances on geodesic terms

The table need not separate terms. Metric completion identifies terms
of zero distance and extends both interpolation and the group action.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped BigOperators
open UniformSpace

variable {G Y A B E T : Type*}

-- 读法：要证明的命题是 `Tests dsq C.seg p l`。
theorem Tests.dense [MetricSpace Y] [Fintype E] [Fintype A] {p : E → A} {l : E → B}
    {R : T → T → ℝ} {s : Fraction → T → T → T}
    (h : Tests R s p l) (C : Comparison Y) (f : T → Y)
    (hd : DenseRange f) (hs : ∀ u x y, f (s u x y) = C.seg u (f x) (f y))
    (hr : ∀ x y, dsq (f x) (f y) = R x y) : Tests dsq C.seg p l := by
  intro x y b n t ht
  let P := fun z : (A → Y) × (B → Y) × Y =>
    9 * (𝔼 u : Fin (n + 1) → A,
      joint dsq (z.1 ∘ p) (z.2.1 ∘ l) (sampleMean C.seg n (z.1 ∘ u))) ≤
      10 * (1 + t) * (𝔼 i, dsq (z.1 (p i)) (z.2.1 (l i))) +
        18 * (1 + t⁻¹) / (n + 1) * (𝔼 i, dsq z.2.2 (z.1 i))
  have hclosed : IsClosed {z | P z} := by
    simp only [P, joint, dsq, Fintype.expect_eq_sum_div_card, Function.comp_def]
    exact isClosed_le (by fun_prop) (by fun_prop)
  have h' := (DenseRange.piMap (fun _ : A => hd)).prodMap
    ((DenseRange.piMap (fun _ : B => hd)).prodMap hd)
  refine h'.induction_on (p := P) (x, y, b) hclosed ?_
  rintro ⟨a, c, d⟩
  change P (f ∘ a, f ∘ c, f d)
  have hm (u : Fin (n + 1) → A) :
      sampleMean C.seg n ((f ∘ a) ∘ u) = f (sampleMean s n (a ∘ u)) :=
    (sampleMean_map s C.seg f hs n _).symm
  dsimp only [P]
  simp only [hm, joint, Function.comp_apply, hr]
  exact h a c d n t ht

-- 读法：`Table` 的结果类型为 `Prop`。
/-- 平方距离表上的比较律和伪度量公理。

英文原文：Comparison and pseudometric laws on a table of squared distances.
-/
def Table (R : Term G → Term G → ℝ) : Prop :=
  (∀ x y, 0 ≤ R x y) ∧
  (∀ x, R x x = 0) ∧
  (∀ x y, R x y = R y x) ∧
  (∀ x y z, Real.sqrt (R x z) ≤ Real.sqrt (R x y) + Real.sqrt (R y z)) ∧
  ∀ t x y z, R (.seg t x y) z ≤
    (1 - t.val) * R x z + t.val * R y z - t.val * (1 - t.val) * R x y

-- 读法：用字段 `dist`、`dist_self`、`dist_comm`、`dist_triangle` 构造 `PseudoMetricSpace (Term G)`。
private abbrev Table.metric {R : Term G → Term G → ℝ} (h : Table R) :
    PseudoMetricSpace (Term G) where
  dist x y := Real.sqrt (R x y)
  dist_self x := by rw [h.2.1]; exact Real.sqrt_zero
  dist_comm x y := by rw [h.2.2.1]
  dist_triangle := h.2.2.2.1

-- 读法：要证明的命题是 `Along u x y (Completion.map₂ s x y)`。这里调用 `isClosed_le`。
theorem completion_along [PseudoMetricSpace T] {s : T → T → T} {u : Fraction}
    (h : ∀ x y, Along u x y (s x y)) (x y : Completion T) :
    Along u x y (Completion.map₂ s x y) := by
  intro z
  induction x, y, z using Completion.induction_on₃ with
  | hp =>
    have hc : Continuous (fun a : Completion T × Completion T × Completion T =>
        Completion.map₂ s a.1 a.2.1) := Completion.continuous_map₂ (by fun_prop) (by fun_prop)
    exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x y z =>
    rw [Completion.map₂_coe_coe _ _ _ (uniformContinuous_along s h)]
    simpa only [Completion.dist_eq] using h x y z

-- 读法：这里调用 `h.2.2.2.2`。
/-- 一个不变的表给出完备空间上的等距作用。

英文原文：An invariant table gives an isometric action on a complete space.
-/
theorem Table.realize {G : Type} [Group G] {R : Term G → Term G → ℝ}
    (h : Table R) (hg : ∀ (g : G) x y, R (g • x) (g • y) = R x y) :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (_ : MulAction G Y)
      (_ : IsIsometricSMul G Y) (C : Comparison Y) (f : Term G → Y),
      DenseRange f ∧ (∀ t x y, f (.seg t x y) = C.seg t (f x) (f y)) ∧
        (∀ x y, dsq (f x) (f y) = R x y) ∧ ∀ (g : G) x, f (g • x) = g • f x := by
  let := h.metric
  have he (x y : Term G) : dist x y ^ 2 = R x y := Real.sq_sqrt (h.1 x y)
  have hs (u : Fraction) (x y : Term G) : Along u x y (.seg u x y) := by
    intro z
    simp only [he]
    exact h.2.2.2.2 _ _ _ _
  have hi (g : G) : Isometry ((g • ·) : Term G → Term G) :=
    Isometry.of_dist_eq (fun x y => congrArg Real.sqrt (hg g x y))
  have : UniformContinuousConstSMul G (Term G) := ⟨fun g => (hi g).uniformContinuous⟩
  let Y := Completion (Term G)
  have : IsIsometricSMul G Y := ⟨fun g => (hi g).completion_map⟩
  have C : Comparison Y := by
    intro x y t ht ht'
    have ha := completion_along (hs ⟨t, ht, ht'⟩) x y
    exact ⟨_, ha.start, ha⟩
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, C, Completion.coe',
    Completion.denseRange_coe, ?_, ?_, Completion.coe_smul⟩
  · intro t x y
    have ha := completion_along (hs t) (x : Y) (y : Y)
    rw [Completion.map₂_coe_coe _ _ _ (uniformContinuous_along _ (hs t))] at ha
    exact ha.unique (C.along _ _ _)
  · intro x y
    exact (congrArg (· ^ 2) (Completion.dist_eq x y)).trans (he x y)

end OAI.LinearAlgebra.MatrixExponent.Routing
end
