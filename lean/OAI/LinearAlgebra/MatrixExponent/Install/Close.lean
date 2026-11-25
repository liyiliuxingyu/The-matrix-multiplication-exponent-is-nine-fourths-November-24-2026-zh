-- 本文件所属证明环节：把带名称的比特、局部权重、控制位与分批请求安装到共同网络中，对隐藏位求和并证明合成后仍给出规定的收缩值及成本。
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Radix.Protocol
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Control.Address
import Mathlib.Logic.Equiv.Fin.Basic

section
/-!
# 将掩码分批装填

每个标记槽位从零起计的序号同时决定其批次与批内位置。因而每批至多含 `2^q` 个槽位，已用批次的总容量至多浪费一个批次的空间。

**英文原文**

Packing a mask into batches

A marked slot's zero-based rank determines both its batch and its
position within the batch. Hence each batch has at most `2^q` slots
and the total capacity of the used batches wastes at most one batch.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {b : ℕ}

-- 读法：`bucket` 的取值由 `x i && decide (Control.histogram x true (some i) / 2 ^ q = z)` 给出。
def bucket (q z : ℕ) (x : Fin (2 ^ b) → Bool) (i : Fin (2 ^ b)) : Bool :=
  x i && decide (Control.histogram x true (some i) / 2 ^ q = z)

-- 读法：在后续公式中，`rank` 是 `Control.histogram x true (some i)` 的缩写。
private abbrev rank (x : Fin (2 ^ b) → Bool) (i : Fin (2 ^ b)) := Control.histogram x true (some i)

-- 读法：`rank x i` 严格小于 `(Finset.univ.filter fun j => x j).card`。这里调用 `Control.rank_lt`。
private theorem rank_lt {x : Fin (2 ^ b) → Bool} {i : Fin (2 ^ b)} (hi : x i = true) :
    rank x i < (Finset.univ.filter fun j => x j).card := by
  simpa only [Control.rank, hi, Control.histogram_none] using Control.rank_lt x i

-- 读法：`(Finset.univ.filter fun i => bucket q z x i).card` 不超过 `2 ^ q`。这里调用 `Finset.card_le_card_of_injOn`。
theorem bucket_card (q z : ℕ) (x : Fin (2 ^ b) → Bool) :
    (Finset.univ.filter fun i => bucket q z x i).card ≤ 2 ^ q := by
  rw [← Finset.card_range (2 ^ q)]
  apply Finset.card_le_card_of_injOn (fun i => rank x i % 2 ^ q)
  · exact fun _ _ => Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos q))
  intro i hi j hj eq
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, bucket,
    Bool.and_eq_true, decide_eq_true_eq] at hi hj
  have he : rank x i = rank x j := by
    rw [← Nat.mod_add_div (rank x i) (2 ^ q), ← Nat.mod_add_div (rank x j) (2 ^ q)]
    exact congrArg₂ (fun r d => r + 2 ^ q * d) eq (hi.2.trans hj.2.symm)
  apply Control.rank_injective x
  exact Prod.ext (hi.1.trans hj.1.symm) (by simpa only [Control.rank, hi.1, hj.1] using he)

-- 读法：`(Finset.univ.filter fun z : Fin (2 ^ c) => ∃ i, bucket q z.val x i = true).card * 2 ^ q` 不超过 `(Finset.univ.filter fun i => x i).card + 2 ^ q`。
theorem buckets_card (c q : ℕ) (x : Fin (2 ^ b) → Bool) :
    (Finset.univ.filter fun z : Fin (2 ^ c) => ∃ i, bucket q z.val x i = true).card * 2 ^ q ≤
      (Finset.univ.filter fun i => x i).card + 2 ^ q := by
  let n := (Finset.univ.filter fun i => x i).card
  have hc : (Finset.univ.filter fun z : Fin (2 ^ c) => ∃ i, bucket q z.val x i = true).card ≤
      n / 2 ^ q + 1 := by
    rw [← Finset.card_range (n / 2 ^ q + 1)]
    refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
    intro z hz
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hz).2
    simp only [bucket, Bool.and_eq_true, decide_eq_true_eq] at hi
    apply Finset.mem_range.mpr
    rw [← hi.2]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (rank_lt hi.1).le)
  calc
    _ ≤ (n / 2 ^ q + 1) * 2 ^ q := Nat.mul_le_mul_right _ hc
    _ ≤ n + 2 ^ q := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

-- 读法：存在唯一的 `z : Fin (2 ^ c)`，`bucket q z.val x i` 等于 `true`。这里调用 `Nat.div_lt_iff_lt_mul`。
theorem mem_bucket {c q : ℕ} (h : b ≤ c + q) {x : Fin (2 ^ b) → Bool} {i : Fin (2 ^ b)}
    (hi : x i = true) : ∃! z : Fin (2 ^ c), bucket q z.val x i = true := by
  have hr : rank x i / 2 ^ q < 2 ^ c := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).mpr
    rw [← Nat.pow_add]
    calc
      rank x i < (Finset.univ.filter fun j => x j).card := rank_lt hi
      _ ≤ 2 ^ b := by simpa using Finset.card_le_univ (Finset.univ.filter fun j => x j)
      _ ≤ 2 ^ (c + q) := Nat.pow_le_pow_right (by decide) h
  refine ⟨⟨_, hr⟩, by simp [bucket, hi], fun z hz => ?_⟩
  simp only [bucket, Bool.and_eq_true, decide_eq_true_eq] at hz
  exact Fin.ext hz.2.symm

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 稀疏路由中每个源点有六个邻点可选的图

对所有为每个源指定六个邻点的函数计数，允许邻点重复。给定 r 个源和 4r 个候选目的地，所有连线都落入这些目的地的比例为 (4r/n)^(6r)。先对这两个集合求和，再对 r 求和，就能得到一张满足所需扩张性的图。

**英文原文**

A six-choice graph for sparse routing

Count all functions assigning six neighbors per source, allowing repetitions.
For r sources and 4r candidate destinations the fraction trapped in those
destinations is (4r/n)^(6r). Summing over both sets and then over r leaves
a graph with the required expansion.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install
open Finset

-- 读法：`(n.choose r : ℝ)` 不超过 `(3 * n / r : ℝ) ^ r`。
private theorem choose_bound (n r : ℕ) (hr : 0 < r) :
    (n.choose r : ℝ) ≤ (3 * n / r : ℝ) ^ r := by
  have h : (r : ℝ) ^ r / r.factorial ≤ (3 : ℝ) ^ r := calc
    _ ≤ Real.exp (r : ℝ) := Real.pow_div_factorial_le_exp _ (by positivity) _
    _ = (Real.exp 1) ^ r := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 3 ^ r := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le _
  calc
    _ ≤ (n : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r n
    _ = ((n : ℝ) / r) ^ r * ((r : ℝ) ^ r / r.factorial) := by
      rw [div_pow, div_mul_div_cancel₀ (by positivity)]
    _ ≤ ((n : ℝ) / r) ^ r * 3 ^ r := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [← mul_pow]; ring

-- 读法：`((2 * (2 * n)).choose r : ℝ) * n.choose (4 * r) * (4 * r / n : ℝ) ^ (6 * r)` 不超过 `(1 / 2 : ℝ) ^ r`。
private theorem failure_bound {n r : ℕ} (hr : 0 < r) (hn : 0 < n) (hs : r * 65536 ≤ n) :
    ((2 * (2 * n)).choose r : ℝ) * n.choose (4 * r) * (4 * r / n : ℝ) ^ (6 * r) ≤ (1 / 2 : ℝ) ^ r := by
  have h₁ := choose_bound (2 * (2 * n)) r hr
  have h₂ := choose_bound n (4 * r) (by omega)
  push_cast at h₁ h₂
  calc
    _ ≤ (3 * (2 * (2 * n)) / r : ℝ) ^ r * (3 * n / (4 * r) : ℝ) ^ (4 * r) * (4 * r / n : ℝ) ^ (6 * r) := by gcongr
    _ = (15552 * r / n : ℝ) ^ r := by
      rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      field_simp
      ring
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ (by positivity)]
      have : (r : ℝ) * 65536 ≤ n := by exact_mod_cast hs
      linarith

-- 读法：在后续公式中，`Raw` 是 `Candidate (2 * n) → Fin 6 → Fin n` 的缩写。
private abbrev Raw (n : ℕ) := Candidate (2 * n) → Fin 6 → Fin n

-- 读法：`trapped` 的取值由 `Fintype.piFinset fun i => Fintype.piFinset fun _ => if i ∈ S then T else univ` 给出。
private def trapped {n : ℕ} (S : Finset (Candidate (2 * n))) (T : Finset (Fin n)) : Finset (Raw n) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ => if i ∈ S then T else univ

-- 读法：`((trapped S T).card : ℝ)` 等于 `Fintype.card (Raw n) * (T.card / n : ℝ) ^ (6 * S.card)`。这里调用 `prod_congr`。
private theorem trapped_count {n : ℕ} (hn : 0 < n) (S : Finset (Candidate (2 * n))) (T : Finset (Fin n)) :
    ((trapped S T).card : ℝ) =
      Fintype.card (Raw n) * (T.card / n : ℝ) ^ (6 * S.card) := by
  rw [trapped, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ = ∏ i : Candidate (2 * n), ((n : ℝ) ^ 6 * (if i ∈ S then (T.card / n : ℝ) ^ 6 else 1)) := by
      apply prod_congr rfl
      intro i _
      rw [Fintype.card_piFinset_const]
      by_cases h : i ∈ S
      · rw [ite_eq_left h, ite_eq_left h, Nat.cast_pow, ← mul_pow, mul_div_cancel₀ _ (by positivity)]
      · simp [h]
    _ = _ := by
      rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const, prod_const, pow_mul]
      simp [Raw]

-- 读法：`failures` 的取值由 `((univ.powersetCard r) ×ˢ (univ.powersetCard (4 * r))).biUnion fun st => trapped st.1 st.2` 给出。
private def failures (n r : ℕ) : Finset (Raw n) :=
  ((univ.powersetCard r) ×ˢ (univ.powersetCard (4 * r))).biUnion fun st => trapped st.1 st.2

-- 读法：`((failures n r).card : ℝ)` 不超过 `Fintype.card (Raw n) * (1 / 2 : ℝ) ^ r`。这里调用 `card_biUnion_le`。
private theorem failures_count {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (hs : r * 65536 ≤ n) :
    ((failures n r).card : ℝ) ≤ Fintype.card (Raw n) * (1 / 2 : ℝ) ^ r := by
  let st := (univ : Finset (Candidate (2 * n))).powersetCard r ×ˢ
    (univ : Finset (Fin n)).powersetCard (4 * r)
  calc
    _ ≤ ∑ p ∈ st, ((trapped p.1 p.2).card : ℝ) := by
      rw [← Nat.cast_sum, Nat.cast_le]
      exact card_biUnion_le
    _ = st.card * (Fintype.card (Raw n) * (4 * r / n : ℝ) ^ (6 * r)) := by
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro p hp
      -- 推导：从 `mem_product.mp hp` 中取出 `h₁, h₂`。
      obtain ⟨h₁, h₂⟩ := mem_product.mp hp
      rw [trapped_count hn, (mem_powersetCard.mp h₁).2, (mem_powersetCard.mp h₂).2]
      push_cast
      rfl
    _ = Fintype.card (Raw n) * (((2 * (2 * n)).choose r : ℝ) * n.choose (4 * r) * (4 * r / n : ℝ) ^ (6 * r)) := by
      simp only [st, card_product, card_powersetCard, card_univ, Fintype.card_fin, Nat.cast_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (failure_bound hr hn hs) (by positivity)

-- 读法：`(∑ i ∈ range k, (1 / 2 : ℝ) ^ (i + 1))` 等于 `1 - (1 / 2 : ℝ) ^ k`。对 `k` 作归纳。
private theorem half_sum (k : ℕ) :
    (∑ i ∈ range k, (1 / 2 : ℝ) ^ (i + 1)) = 1 - (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih, pow_succ]; ring

-- 读法：存在 `g : Raw n`，对每个 `S : Finset (Candidate (2 * n))`，由 `S.card * 65536 ≤ n` 推出 `4 * S.card ≤ (S.biUnion (fun i => univ.image (g i))).card`。这里调用 `card_biUnion_le`。
private theorem raw_exists (n : ℕ) (hn : 0 < n) :
    ∃ g : Raw n, ∀ S : Finset (Candidate (2 * n)), S.card * 65536 ≤ n →
      4 * S.card ≤ (S.biUnion (fun i => univ.image (g i))).card := by
  let k := n / 65536
  let bad := (range k).biUnion fun i => failures n (i + 1)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hb : (bad.card : ℝ) < Fintype.card (Raw n) := calc
    _ ≤ ∑ i ∈ range k, ((failures n (i + 1)).card : ℝ) := by
      rw [← Nat.cast_sum, Nat.cast_le]
      exact card_biUnion_le
    _ ≤ ∑ i ∈ range k, Fintype.card (Raw n) * (1 / 2 : ℝ) ^ (i + 1) := by
      apply sum_le_sum
      intro i hi
      have := mem_range.mp hi
      exact failures_count hn (by omega) (by omega)
    _ = Fintype.card (Raw n) * (1 - (1 / 2 : ℝ) ^ k) := by rw [← mul_sum, half_sum]
    _ < _ := mul_lt_of_lt_one_right (by exact_mod_cast Fintype.card_pos (α := Raw n))
      (sub_lt_self _ (by positivity))
  -- 推导：从 `exists_mem_notMem_of_card_lt_card` 中取出 `g, _, hg`。
  obtain ⟨g, _, hg⟩ := exists_mem_notMem_of_card_lt_card
    (show bad.card < (univ : Finset (Raw n)).card from Nat.cast_lt.mp hb)
  refine ⟨g, fun S hS => ?_⟩
  by_contra! hlt
  obtain ⟨T, hT, hc⟩ := exists_superset_card_eq hlt.le
    (by simpa using (show 4 * S.card ≤ n by omega))
  apply hg
  refine mem_biUnion.mpr ⟨S.card - 1, mem_range.mpr (by omega), ?_⟩
  rw [show S.card - 1 + 1 = S.card by omega, failures]
  refine mem_biUnion.mpr ⟨(S, T), by simp [hc], ?_⟩
  refine Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mpr (fun j => ?_))
  by_cases hi : i ∈ S
  · simpa only [ite_eq_left hi] using hT (mem_biUnion.mpr ⟨i, hi, mem_image_of_mem _ (mem_univ j)⟩)
  · simp [hi]

-- 读法：要证明的命题是 `∃ (e : Link (2 * n) → Fin (2 * n) × Fin 24) (old : Fin (2 * n) → Fin n), Function.Injective e ∧ ∀ x, old (e x).1 = f x`。
/-- 为每个目标将链路分成至多含 24 条的小组。在链路总数除以 24 之外，每个原目标至多额外计入一个未满的小组。

英文原文：Split each target into groups of at most 24 links. At most one
partially filled group per old target is charged in addition to the
total number of links divided by 24.
-/
private theorem split_links (n : ℕ) (hn : 0 < n) (f : Link (2 * n) → Fin n) :
    ∃ (e : Link (2 * n) → Fin (2 * n) × Fin 24) (old : Fin (2 * n) → Fin n),
      Function.Injective e ∧ ∀ x, old (e x).1 = f x := by
  classical
  let fiber := fun j => {x // f x = j}
  let block := fun j => Fin (Fintype.card (fiber j) / 24 + 1)
  have hl : (∑ j, Fintype.card (fiber j)) = 24 * n := by
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv f)]
    simp [Link, Candidate]
    omega
  -- 推导：记下中间结论 `hb`：`Fintype.card (Sigma block) ≤ Fintype.card (Fin (2 * n))`。
  have hb : Fintype.card (Sigma block) ≤ Fintype.card (Fin (2 * n)) := by
    have he : (∑ j, Fintype.card (fiber j) / 24) * 24 ≤ 24 * n := by
      rw [sum_mul, ← hl]
      exact sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
    simp only [Fintype.card_sigma, block, Fintype.card_fin, sum_add_distrib, sum_const,
      card_univ, nsmul_eq_mul, Nat.cast_id, mul_one]
    omega
  let enc := Classical.choice (Function.Embedding.nonempty_of_card_le hb)
  have : Nonempty (Sigma block) := ⟨⟨⟨0, hn⟩, ⟨0, by omega⟩⟩⟩
  obtain ⟨dec, hdec⟩ := enc.injective.hasLeftInverse
  have hsize (j) : Fintype.card (fiber j) ≤ Fintype.card (block j × Fin 24) := by
    simp only [block, Fintype.card_prod, Fintype.card_fin]
    omega
  let spot (j) := Classical.choice (Function.Embedding.nonempty_of_card_le (hsize j))
  let route (x : Sigma fiber) : Fin (2 * n) × Fin 24 :=
    (enc ⟨x.1, (spot x.1 x.2).1⟩, (spot x.1 x.2).2)
  have hi : Function.Injective route := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have he := enc.injective (congrArg Prod.fst h)
    -- 推导：记下中间结论 `hij`：`i = j`。
    have hij : i = j := congrArg Sigma.fst he
    subst j
    have hs := congrArg Prod.snd h
    have hxy : spot i x = spot i y :=
      Prod.ext (eq_of_heq (Sigma.mk.inj he).2) hs
    rw [(spot i).injective hxy]
  refine ⟨route ∘ (Equiv.sigmaFiberEquiv f).symm, fun j => (dec j).1,
    hi.comp (Equiv.sigmaFiberEquiv f).symm.injective, ?_⟩
  intro x
  exact congrArg Sigma.fst (hdec _)

-- 读法：存在 `g : Graph (2 * n)`，`Expands g` 与 `∀ j, degree g univ j ≤ 24` 同时成立。
theorem graph_exists (n : ℕ) (hn : 0 < n) :
    ∃ g : Graph (2 * n), Expands g ∧ ∀ j, degree g univ j ≤ 24 := by
  obtain ⟨f, hf⟩ := raw_exists n hn
  obtain ⟨e, old, he, hold⟩ := split_links n hn (Function.uncurry f)
  let g : Graph (2 * n) := fun i j => (e (i, j)).1
  refine ⟨g, ?_, fun j => ?_⟩
  · intro S hS
    have hS' : S.card * 65536 ≤ n := by linarith only [hS]
    refine (hf S hS').trans (card_le_card_of_surjOn old ?_)
    intro y hy
    obtain ⟨i, hi, hj⟩ := mem_biUnion.mp hy
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    exact ⟨g i k, mem_biUnion.mpr ⟨i, hi, mem_image_of_mem _ hk⟩, hold (i, k)⟩
  · unfold degree
    rw [← card_fin 24]
    apply card_le_card_of_injOn (fun x => (e x).2) (fun _ _ => mem_univ _)
    intro x hx y hy hxy
    exact he (Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hxy)

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 用有界的局部更新实现各轮剥离

**英文原文**

Implementing the peeling rounds by bounded local updates
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {n : ℕ} {g : Graph n}

-- 读法：要证明的命题是 `Depends (init (n := n)) 1`。对 `k` 分类讨论。
theorem depends_init (n : ℕ) : Depends (init (n := n)) 1 := by
  rintro ⟨i, k⟩
  refine ⟨{i}, by simp, fun x y h => ?_⟩
  cases k
  · exact h _ (by simp)
  · rfl

-- 读法：要证明的命题是 `Depends (step g) 200`。
/-- 用六个列表即可算出当前的度数，每个列表至多含 24 条关联链路。还须读取输出的旧值及其活动标志位。

英文原文：Six lists of at most 24 incident links suffice to compute the current
degrees. The previous value of the output and its activity bit are also read.
-/
theorem depends_step (h : ∀ j, degree g Finset.univ j ≤ 24) : Depends (step g) 200 := by
  rintro ⟨i, r⟩
  let links (j : Fin n) : Finset (Link n) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun e => g e.1 e.2 = j)
  let neighbors (k : Fin 6) : Finset (Status n) :=
    (links (g i k)).image (fun e => (e.1, none))
  let U := Finset.univ.biUnion neighbors
  refine ⟨insert (i, r) (insert (i, none) U), ?_, fun x y he => ?_⟩
  · have hu : U.card ≤ 144 := calc
      U.card ≤ ∑ k, (neighbors k).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin 6, 24 := Finset.sum_le_sum (fun k _ => Finset.card_image_le.trans (h (g i k)))
      _ = _ := by simp
    have := Finset.card_insert_le (i, r) (insert (i, none) U)
    have := Finset.card_insert_le (i, none) U
    omega
  have hd (k : Fin 6) : degree g (active x) (g i k) = degree g (active y) (g i k) := by
    unfold degree
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter, Finset.mem_product, mem_active, Finset.mem_univ, and_true]
    by_cases hj : g e.1 e.2 = g i k
    -- 推导：记下中间结论 `hm`：`(e.1, none) ∈ U`。
    · have hm : (e.1, none) ∈ U := Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨e, by simp [links, hj], rfl⟩⟩
      rw [he _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))]
    · simp only [hj, and_false]
  have hf : first g (active x) i = first g (active y) i := by simp only [first, hd]
  have ha := he (i, none) (by simp)
  have hb := he (i, r) (by simp)
  cases r <;> simp only [step, hf, ha, hb]

-- 读法：`readLinks` 的取值由 `x (e.1, some e.2)` 给出。
private def readLinks (x : Status n → Bool) (e : Link n) := x (e.1, some e.2)

-- 读法：要证明的命题是 `Depends (readLinks (n := n)) 1`。
private theorem depends_read (n : ℕ) : Depends (readLinks (n := n)) 1 :=
  fun e => ⟨{(e.1, some e.2)}, by simp, fun _ _ h => h _ (by simp)⟩

-- 读法：`assignCost` 的取值由 `100 * (1 + localCost 1 + localCost 200)` 给出。
def assignCost := 100 * (1 + localCost 1 + localCost 200)

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun mask (e : Link n) => assign g mask e.1 e.2)` 均在 `F` 上有顶点数至多为 `(assignCost * n * (1 + rounds n))` 的网络实现。
theorem assign_net (F : Type) [Field F] (h : ∀ j, degree g Finset.univ j ≤ 24) :
    BNet F (fun mask (e : Link n) => assign g mask e.1 e.2) (assignCost * n * (1 + rounds n)) := by
  let M := 14 * (1 + localCost 1 + localCost 200) * n
  have seed : BNet F (init (n := n)) M := by
    apply ((depends_init n).bnet F).mono
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, M]
    ring_nf
    omega
  have next : BNet F (step g) M := by
    apply ((depends_step h).bnet F).mono
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, M]
    ring_nf
    omega
  have last : BNet F (readLinks (n := n)) M := by
    apply ((depends_read n).bnet F).mono
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, M]
    ring_nf
    omega
  have run (r : ℕ) : BNet F (fun mask => (step g)^[r] (init mask)) (M + r * M) := by
    induction r with
    | zero => simpa using seed
    | succ r ih =>
      simpa only [Function.comp_def, Function.iterate_succ_apply', Nat.succ_mul, Nat.add_assoc] using
        ih.comp next
  apply ((run (rounds n)).comp last).mono
  unfold M assignCost
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 将稀疏数据压紧到容量固定为二的幂的空间中

连续减半的成本构成等比级数，因而载荷项无需再乘一个对数因子。

**英文原文**

Sparse compaction into a fixed dyadic capacity

The costs of successive halvings sum to a geometric series. In
particular there is no logarithmic factor multiplying the payload.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

-- 读法：`switchCost` 的取值由 `20 * (assignCost + localCost 48 + 1)` 给出。
def switchCost := 20 * (assignCost + localCost 48 + 1)

variable (F J : Type) [Field F] [Fintype J]

-- 读法：存在 `f : Records (Fin (2 * 2 ^ l)) J → Records (Fin (2 ^ l)) J`，要证明的命题是 `BNet F f (switchCost * 2 ^ l * (1 + l + Fintype.card J)) ∧ ∀ x, (marked x).card * 131072 ≤ 2 ^ l → Carries x (f x)`。对 `l` 分类讨论。
private theorem half_net (l : ℕ) (hl : 1 ≤ l) :
    ∃ f : Records (Fin (2 * 2 ^ l)) J → Records (Fin (2 ^ l)) J,
      BNet F f (switchCost * 2 ^ l * (1 + l + Fintype.card J)) ∧
      ∀ x, (marked x).card * 131072 ≤ 2 ^ l → Carries x (f x) := by
  have hex : ∃ g : Graph (2 ^ l), Expands g ∧ ∀ j, degree g Finset.univ j ≤ 24 := by
    cases l with
    | zero => omega
    | succ l =>
      rw [pow_succ']
      exact graph_exists (2 ^ l) (by positivity)
  -- 推导：从 `hex` 中取出 `g, he, hd`。
  obtain ⟨g, he, hd⟩ := hex
  have sig := (assign_net F hd).parallel (BNet.id F (Candidate (2 ^ l) × J))
  have sw := (depends_switch (J := J) g hd).bnet F
  refine ⟨switch g ∘ signal g, (sig.comp sw).mono ?_, switch_carries g (by positivity) he⟩
  simp only [rounds, Nat.clog_pow _ _ (by decide : 1 < 2), switchCost,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring_nf
  omega

-- 读法：存在 `f : Records (Fin (2 ^ (h + k))) J → Records (Fin (2 ^ h)) J`，要证明的命题是 `BNet F f ((switchCost + 1) * 2 ^ (h + k) * (1 + h + k + Fintype.card J)) ∧ ∀ x, (marked x).card * 131072 ≤ 2 ^ h → Carries x (f x)`。对 `k` 作归纳。
/-- 将有标记的记录从 `2^(h+k)` 个候选槽位压紧至 `2^h` 个槽位。

英文原文：Compact the marked records from `2^(h+k)` candidate slots to `2^h` slots.
-/
theorem compact (h k : ℕ) (hh : 1 ≤ h) :
    ∃ f : Records (Fin (2 ^ (h + k))) J → Records (Fin (2 ^ h)) J,
      BNet F f ((switchCost + 1) * 2 ^ (h + k) * (1 + h + k + Fintype.card J)) ∧
      ∀ x, (marked x).card * 131072 ≤ 2 ^ h → Carries x (f x) := by
  induction k with
  | zero =>
    refine ⟨id, (BNet.id F _).mono ?_, fun _ _ => ⟨.refl _, fun _ _ => rfl⟩⟩
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Nat.add_zero]
    ring_nf
    omega
  | succ k ih =>
    rw [← Nat.add_assoc h k, pow_succ']
    -- 推导：从 `half_net F J (h + k) (by omega)` 中取出 `f, hf, ef`。
    obtain ⟨f, hf, ef⟩ := half_net F J (h + k) (by omega)
    obtain ⟨g, hg, eg⟩ := ih
    refine ⟨_, (hf.comp hg).mono ?_, fun x hx => ?_⟩
    · ring_nf
      omega
    · have ht := ef x (hx.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right h k)))
      exact ht.trans (eg _ (by rwa [ht.card]))

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 汇集对同一标量表的查询

只有标记的实参产生贡献。将它们压紧到较小的表调用存储区，再用权重为一的实参填满未使用的位置。

**英文原文**

Pooling queries to the same scalar table

Only marked arguments contribute. Compact them into the smaller bank of
table calls and fill unused positions with an argument of weight one.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {F I J K : Type} [Field F]

-- 读法：`(∏ i ∈ marked y, f (payload y i))` 等于 `∏ i ∈ marked x, f (payload x i)`。这里调用 `Fintype.prod_equiv`。
theorem Carries.prod [Fintype I] [Fintype K] {x : Records I J} {y : Records K J}
    (h : Carries x y) (f : (J → Bool) → F) :
    (∏ i ∈ marked y, f (payload y i)) = ∏ i ∈ marked x, f (payload x i) := by
  rw [← Finset.prod_coe_sort (marked y), ← Finset.prod_coe_sort (marked x)]
  symm
  exact Fintype.prod_equiv h.choose _ _ (fun i => congrArg f (funext (h.choose_spec i)).symm)

-- 读法：当 `x (.inl ij.1)` 成立时取 `x (.inr ij)`，否则取 `dummy ij.2`。
private def fill (dummy : J → Bool) (x : Records I J) (ij : I × J) : Bool :=
  if x (.inl ij.1) then x (.inr ij) else dummy ij.2

-- 读法：要证明的命题是 `Depends (fill (I := I) dummy) 2`。
private theorem fill_depends (dummy : J → Bool) : Depends (fill (I := I) dummy) 2 := by
  classical
  intro ij
  refine ⟨{.inl ij.1, .inr ij}, by simp, fun x y h => ?_⟩
  simp only [fill, h (.inl ij.1) (by simp), h (.inr ij) (by simp)]

-- 读法：`(∏ i, f (fun j => fill dummy x (i, j)))` 等于 `∏ i ∈ marked x, f (payload x i)`。这里调用 `Finset.prod_congr`。
private theorem filled_prod [Fintype I] {f : (J → Bool) → F} {dummy : J → Bool}
    (he : f dummy = 1) (x : Records I J) :
    (∏ i, f (fun j => fill dummy x (i, j))) = ∏ i ∈ marked x, f (payload x i) := by
  rw [marked, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x (.inl i) = true
  · simp [h, fill]; rfl
  · simp [h, fill, he]

-- 读法：`poolCost` 的取值由 `switchCost + 2 + localCost 2` 给出。
def poolCost := switchCost + 2 + localCost 2

-- 读法：结论为 `∃ g : Records (Fin (2 ^ (h + k))) J → F, Weight F g (2 ^ h * m + poolCost * 2 ^ (h + k) * (1 + h + k + Fintype.card J)) ∧ ∀ x, (marked x).card * 131072 ≤ 2 ^ h → g x = ∏ i ∈ marked x, f (payload x i)`。
theorem pool [Fintype J] {h k m : ℕ} {f : (J → Bool) → F}
    (hh : 1 ≤ h) (hf : Weight F f m) (dummy : J → Bool) (he : f dummy = 1) :
    ∃ g : Records (Fin (2 ^ (h + k))) J → F,
      Weight F g (2 ^ h * m + poolCost * 2 ^ (h + k) * (1 + h + k + Fintype.card J)) ∧
      ∀ x, (marked x).card * 131072 ≤ 2 ^ h → g x = ∏ i ∈ marked x, f (payload x i) := by
  obtain ⟨c, hc, heq⟩ := compact F J h k hh
  have ht := (fill_depends (I := Fin (2 ^ h)) dummy).bnet F
  have hw := (hc.comp ht).weight (hf.prod h)
  refine ⟨_, hw.mono ?_, fun x hx => (filled_prod he (c x)).trans ((heq x hx).prod f)⟩
  have hk : 2 ^ h ≤ 2 ^ (h + k) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Bus, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hu : 2 ^ h + 2 ^ h * Fintype.card J + localCost 2 * (2 ^ h * Fintype.card J) ≤
      (1 + localCost 2) * 2 ^ (h + k) * (1 + h + k + Fintype.card J) := by
    calc
      _ ≤ (1 + localCost 2) * 2 ^ h * (1 + Fintype.card J) := by ring_nf; omega
      _ ≤ _ := by gcongr; omega
  unfold poolCost
  grw [hu]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 将一组传输分成若干批

每个标记端点都给出其源端的物理槽位。两个端点查询同一个源槽位来确定所属批次。

**英文原文**

Dividing one group of transports into batches

Each marked endpoint identifies the physical slot of its source. Both
endpoints consult the same source slot to determine their batch.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

-- 读法：在后续公式中，`Idx` 是 `Fin (2 ^ s)` 的缩写。
abbrev Idx (s : ℕ) := Fin (2 ^ s)

variable {s r : ℕ}

-- 读法：`Aligned` 表示以下条件：`(∀ i ∈ marked x, idOf (payload x i) ∈ marked x)` 与 `Set.InjOn (fun i => (idOf (payload x i), payload x i o)) (marked x)` 同时成立。
def Aligned (o : Fin r) (idOf : (Fin r → Bool) → Idx s)
    (x : Records (Idx s) (Fin r)) : Prop :=
  (∀ i ∈ marked x, idOf (payload x i) ∈ marked x) ∧
    Set.InjOn (fun i => (idOf (payload x i), payload x i o)) (marked x)

-- 读法：`select` 的取值由 `Sum.elim (fun i => x (.inl i) && bucket q j (x ∘ Sum.inl) (idOf (payload x i))) (x ∘ Sum.inr)` 给出。
def select (idOf : (Fin r → Bool) → Idx s) (q j : ℕ)
    (x : Records (Idx s) (Fin r)) : Records (Idx s) (Fin r) :=
  Sum.elim (fun i => x (.inl i) && bucket q j (x ∘ Sum.inl) (idOf (payload x i))) (x ∘ Sum.inr)

-- 读法：`batches` 的取值由 `Sum.elim (fun j => decide (∃ i, bucket q j.val (x ∘ Sum.inl) i = true)) (fun z => select idOf q z.1.val x z.2)` 给出。
def batches (idOf : (Fin r → Bool) → Idx s) (q c : ℕ)
    (x : Records (Idx s) (Fin r)) : Records (Idx c) (Bus (Idx s) (Fin r)) :=
  Sum.elim (fun j => decide (∃ i, bucket q j.val (x ∘ Sum.inl) i = true))
    (fun z => select idOf q z.1.val x z.2)

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 组的拆分保持有向配对

两个方向查询同一标识符。（标识符，方向）为单射，因而所选端点数至多为该批次标识符数的两倍。

**英文原文**

Dividing a group preserves oriented pairing

Both orientations consult the same identifier. Injectivity of
(identifier, orientation) bounds the selected endpoints by twice the
number of identifiers in the batch.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

variable {s r q c : ℕ} {idOf : (Fin r → Bool) → Idx s}
variable {x : Records (Idx s) (Fin r)} {o : Fin r}

-- 读法：`i ∈ marked (select idOf q z x)` 与 `i ∈ marked x ∧ bucket q z (x ∘ Sum.inl) (idOf (payload x i)) = true` 等价。
private theorem mem_select {z : ℕ} {i : Idx s} : i ∈ marked (select idOf q z x) ↔
    i ∈ marked x ∧ bucket q z (x ∘ Sum.inl) (idOf (payload x i)) = true := by
  simp [select]

-- 读法：`(marked (select idOf q z x)).card ≤ 2 * 2 ^ q` 与 `Unambiguous (select idOf q z x)` 同时成立。
private theorem selected (hx : Aligned o idOf x) (q z : ℕ) :
    (marked (select idOf q z x)).card ≤ 2 * 2 ^ q ∧ Unambiguous (select idOf q z x) := by
  let f (i) := (idOf (payload x i), payload x i o)
  let S := Finset.univ.filter (fun i => bucket q z (x ∘ Sum.inl) i)
  have inj : Set.InjOn f (marked (select idOf q z x)) :=
    fun _ hi _ hj => hx.2 (mem_select.mp hi).1 (mem_select.mp hj).1
  constructor
  · calc
      _ ≤ (S ×ˢ (Finset.univ : Finset Bool)).card := by
        refine Finset.card_le_card_of_injOn f ?_ inj
        intro i hi
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_select.mp hi).2⟩, Finset.mem_univ _⟩
      _ = 2 * S.card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ (bucket_card q z _)
  · intro i hi j hj h
    apply inj hi hj
    exact congrArg (fun p => (idOf p, p o)) h

-- 读法：这里调用 `buckets_card`。
theorem divide {s r q c : ℕ} (o : Fin r) (idOf : (Fin r → Bool) → Idx s)
    (hf : ∀ p, idOf (flip o p) = idOf p) (hc : s ≤ c + q)
    (x : Records (Idx s) (Fin r)) (hx : Aligned o idOf x) :
    let y := batches idOf q c x
    (marked y).card * 2 ^ q ≤ (marked x).card + 2 ^ q ∧
    (∀ j ∈ marked y, (marked (payload y j)).card ≤ 2 * 2 ^ q ∧ Unambiguous (payload y j)) ∧
    ((∀ j ∈ marked y, Closed o (payload y j)) ↔ Closed o x) := by
  let y := batches idOf q c x
  have hy : marked y = Finset.univ.filter (fun z : Idx c => ∃ i, bucket q z.val (x ∘ Sum.inl) i = true) :=
    by ext; simp [y, batches]
  refine ⟨?_, fun j _ => selected hx q j.val, ?_, ?_⟩
  · rw [hy]
    exact buckets_card c q (x ∘ Sum.inl)
  · intro h i hi
    -- 推导：从 `mem_bucket hc (x := x ∘ Sum.inl) (mem_marked.mp (hx.1 i hi))` 中取出 `z, hz, _`。
    obtain ⟨z, hz, _⟩ := mem_bucket hc (x := x ∘ Sum.inl) (mem_marked.mp (hx.1 i hi))
    have hzy : z ∈ marked y := by
      rw [hy]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hz⟩
    have hh : Closed o (select idOf q z.val x) := h z hzy
    obtain ⟨j, hj, he⟩ := hh i (mem_select.mpr ⟨hi, hz⟩)
    exact ⟨j, (mem_select.mp hj).1, he⟩
  · intro h z _
    change Closed o (select idOf q z.val x)
    intro i hi
    -- 推导：从 `mem_select.mp hi` 中取出 `hi, hb`。
    obtain ⟨hi, hb⟩ := mem_select.mp hi
    obtain ⟨j, hj, he⟩ := h i hi
    exact ⟨j, mem_select.mpr ⟨hj, by rw [he, hf]; exact hb⟩, he⟩

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 由较短的置换调用组成的一层

每个候选模块列出分块传送的有向端点。闭合时检验相对的两端是否具有匹配的标识符和载荷。实际使用哪些模块，以及每个模块使用哪些端点，均可依赖选择器和输入。

**英文原文**

A layer of shorter permutation calls

A candidate module lists oriented ends of chunk transports. Its closure
tests that opposite ends have matching identifiers and payloads. Both
the set of modules in use and the set of endpoints within each module
may depend on the selector and the input.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

-- 读法：结构的字段包括 `l`、`u`、`o`、`c`、`d`。
structure Layer where
  /-- 较短调用的高度。

英文原文：Height of a shorter call.
-/
  l : ℕ
  /-- 较短调用的宽度。

英文原文：Width of a shorter call.
-/
  u : ℕ
  /-- 该配置预留 `2^o` 个物理模块。

英文原文：The installation reserves `2^o` physical modules.
-/
  o : ℕ
  /-- 候选模块数量在对数尺度上的超额。

英文原文：Excess log count of candidate modules.
-/
  c : ℕ
  /-- 每个模块的候选端点数在对数尺度上的超额。

英文原文：Excess log count of candidate endpoints per module.
-/
  d : ℕ
  /-- 含方向位在内的端点宽度。

英文原文：Endpoint width including the orientation bit.
-/
  r : ℕ
  orientation : Fin r
  l_pos : 1 ≤ l
  o_pos : 1 ≤ o
  fits : 1 + l + r ≤ u

namespace Layer

variable (p : Layer)

-- 读法：在后续公式中，`Footprint` 是 `Bus (Fin (2 ^ (p.l + p.d))) (Fin p.r)` 的缩写。
abbrev Footprint := Bus (Fin (2 ^ (p.l + p.d))) (Fin p.r)
-- 读法：在后续公式中，`Ports` 是 `Bus (Fin (2 ^ (p.o + p.c))) p.Footprint` 的缩写。
abbrev Ports := Bus (Fin (2 ^ (p.o + p.c))) p.Footprint

-- 读法：`Valid` 表示以下条件：`(marked x).card * 131072 ≤ 2 ^ p.o` 与 `∀ i ∈ marked x, (marked (payload x i)).card * 131072 ≤ 2 ^ p.l ∧ Unambiguous (payload x i)` 同时成立。
def Valid (x : p.Ports → Bool) : Prop :=
  (marked x).card * 131072 ≤ 2 ^ p.o ∧ ∀ i ∈ marked x,
    (marked (payload x i)).card * 131072 ≤ 2 ^ p.l ∧ Unambiguous (payload x i)

open Classical in
-- 读法：`close` 的取值由 `∏ i ∈ marked x, if Closed p.orientation (payload x i) then 1 else 0` 给出。
noncomputable def close (F : Type) [Field F] (x : p.Ports → Bool) : F :=
  ∏ i ∈ marked x, if Closed p.orientation (payload x i) then 1 else 0

-- 读法：`work` 的取值由 `2 ^ (p.o + p.c) * (1 + p.o + p.c + 2 ^ (p.l + p.d) * (1 + p.l + p.d + p.u))` 给出。
/-- 处理候选端点与模块掩码的成本。

英文原文：The cost of handling candidate endpoints and the module masks.
-/
def work : ℕ :=
  2 ^ (p.o + p.c) * (1 + p.o + p.c + 2 ^ (p.l + p.d) * (1 + p.l + p.d + p.u))

-- 读法：`Open` 的结果类型为 `Prop`。
/-- 网络一直构造到必须为分块传送布线的位置。在检验任何传送之前，无效配置的系数已经为零。

英文原文：The network up to the point where the chunk transports must be wired.
Invalid configurations have coefficient zero before any transports are checked.
-/
def Open (F : Type) [Field F] (h v m : ℕ) : Prop :=
  ∃ (b : Wire) (e : p.Ports ≃ slots b) (f : Val (Tagged.inputs h (word v)) → Val b → F),
    Net F (Tagged.inputs h (word v)) b f m ∧
    (∀ x y, f x y ≠ 0 → p.Valid (bits b y ∘ e)) ∧
    ∀ x, Tagged.tag F h (word v) x () = ∑ y, f x y * p.close F (bits b y ∘ e)

end Layer

-- 读法：`OpenProtocol` 的结果类型为 `Prop`。
/-- 安装递归调用之前的协议构造。

英文原文：Protocol construction before installing the recursive calls.
-/
def OpenProtocol (F : Type) [Field F] : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∃ Y : ℝ, 0 < Y ∧ ∃ J : ℕ,
    ∀ A : ℕ, J ≤ A → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in Filter.atTop,
      ∃ (p : Layer) (m : ℕ), (p.l : ℝ) ≤ τ * h ∧ Y * (h : ℝ) ^ A ≤ p.u ∧
        (2 : ℝ) ^ p.o * (2 : ℝ) ^ p.l * p.u ≤ C * (2 : ℝ) ^ h * (h : ℝ) ^ A ∧
        (m + p.work : ℕ) ≤ (2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ ζ ∧ p.Open F h (h ^ A) m

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 安装传输模块

先在每个候选模块内压紧端点，再把选中的模块作为完整记录压紧。只有实际的物理模块槽位才调用较小的带标签置换验证器。

**英文原文**

Installing the transport modules

First compact endpoints inside a candidate module, then compact the
selected modules as whole records. Only physical module slots invoke
the smaller tagged permutation verifier.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

open Classical
variable {F : Type} [Field F] {m : ℕ}

-- 读法：`cost` 的取值由 `poolCost + switchCost + 1002` 给出。
private def cost := poolCost + switchCost + 1002

-- 读法：这里调用 `Nat.mul_le_mul`。
private theorem Layer.bill (p : Layer) (m : ℕ) :
    2 ^ p.o * ((switchCost + 1) * 2 ^ (p.l + p.d) * (1 + p.l + p.d + p.r) + (m + 1000 * 2 ^ p.l * p.u)) +
        poolCost * 2 ^ (p.o + p.c) * (1 + p.o + p.c + Fintype.card p.Footprint) ≤
      2 ^ p.o * m + cost * p.work := by
  have hr := p.fits
  have ho : 2 ^ p.o ≤ 2 ^ (p.o + p.c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hl : 2 ^ p.l ≤ 2 ^ (p.l + p.d) := Nat.pow_le_pow_right (by decide) (by omega)
  have a : 2 ^ p.o * 2 ^ (p.l + p.d) * (1 + p.l + p.d + p.r) ≤ p.work := by
    unfold work
    rw [mul_assoc]
    apply Nat.mul_le_mul ho
    exact (Nat.mul_le_mul_left _ (show 1 + p.l + p.d + p.r ≤ 1 + p.l + p.d + p.u by omega)).trans
      (Nat.le_add_left ..)
  -- 推导：记下中间结论 `b`：`2 ^ p.o * 2 ^ p.l * p.u ≤ p.work`。
  have b : 2 ^ p.o * 2 ^ p.l * p.u ≤ p.work := by
    unfold work
    rw [mul_assoc]
    apply Nat.mul_le_mul ho
    exact (Nat.mul_le_mul hl (Nat.le_add_left ..)).trans (Nat.le_add_left ..)
  have c : 2 ^ (p.o + p.c) * (1 + p.o + p.c + Fintype.card p.Footprint) ≤ p.work := by
    unfold work
    gcongr
    simp only [Footprint, Bus, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← mul_one_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have h₁ := Nat.mul_le_mul_left (switchCost + 1) a
  have h₂ := Nat.mul_le_mul_left 1000 b
  have h₃ := Nat.mul_le_mul_left poolCost c
  unfold cost
  ring_nf at h₁ h₂ h₃ ⊢
  omega

-- 读法：存在 `f : (p.Ports → Bool) → F`，由 `Weight F f (2 ^ p.o * m + cost * p.work) ∧ ∀ x, p.Valid x` 推出 `f x = p.close F x`。
private theorem Layer.install (p : Layer) (ht : Radix.Tag F p.l p.u m) :
    ∃ f : (p.Ports → Bool) → F, Weight F f (2 ^ p.o * m + cost * p.work) ∧
      ∀ x, p.Valid x → f x = p.close F x := by
  obtain ⟨s, hs, es⟩ := compact F (Fin p.r) p.l p.d p.l_pos
  obtain ⟨g, hg, eg⟩ := check_turns p.orientation (by simpa using p.fits) ht
  have verify (x : p.Footprint → Bool) (hx : (marked x).card * 131072 ≤ 2 ^ p.l)
      (hy : Unambiguous x) : (g ∘ s) x = if Closed p.orientation x then 1 else 0 := by
    have he := es x hx
    simp only [Function.comp_apply, eg _ (he.unambiguous hy), he.closed_iff]
  let dummy : p.Footprint → Bool := fun _ => false
  -- 推导：记下中间结论 `hd`：`marked dummy = ∅`。
  have hd : marked dummy = ∅ := by simp [marked, dummy]
  have he : (g ∘ s) dummy = 1 := by
    rw [verify dummy (by simp [hd]) (by simp [Unambiguous, hd])]
    simp [Closed, hd]
  obtain ⟨f, hf, ef⟩ := pool (k := p.c) p.o_pos (hs.weight hg) dummy he
  refine ⟨f, hf.mono ?_, fun x hx => ?_⟩
  · simpa only [Fintype.card_fin] using p.bill m
  · rw [ef x hx.1]
    exact Finset.prod_congr rfl fun i hi => verify _ (hx.2 i hi).1 (hx.2 i hi).2

-- 读法：存在 `n ≤ (m + cost * p.work) + 2 ^ p.o * s`，要证明的命题是 `Radix.Tag F h v n`。用函数外延性比较等号两侧在 `x _` 处的取值。
private theorem Layer.contract (p : Layer) {h v s : ℕ} (ho : p.Open F h v m)
    (ht : Radix.Tag F p.l p.u s) :
    ∃ n ≤ (m + cost * p.work) + 2 ^ p.o * s, Radix.Tag F h v n := by
  obtain ⟨g, hg, he⟩ := p.install ht
  obtain ⟨b, e, f, hf, hv, hsum⟩ := ho
  obtain ⟨u, hu, hk⟩ := hg b e
  refine ⟨m + u, by omega, ?_⟩
  unfold Radix.Tag
  convert hf.comp hk using 1
  funext x _
  rw [hsum x]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : f x y = 0
  · simp only [hy, zero_mul]
  · rw [he _ (hv x y hy)]

-- 读法：要证明的命题是 `Radix.Protocol F`。
/-- 安装宽度有统一上界便足以建立归纳协议。控制、交换和填充仅带来次多项式开销。

英文原文：Uniformly bounded installed width suffices for the inductive
protocol. Control, switching and padding cost subpolynomial overhead.
-/
theorem protocol_of_open (ho : OpenProtocol F) : Radix.Protocol F := by
  obtain ⟨C, hC, hh⟩ := ho
  refine ⟨C, hC, fun τ hτ => ?_⟩
  obtain ⟨Y, hY, J, hJ⟩ := hh τ hτ
  refine ⟨Y, hY, J, fun A hA ζ hζ => ?_⟩
  have grow := ((tendsto_rpow_atTop (half_pos hζ)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hJ A hA _ (half_pos hζ), grow.eventually_ge_atTop (cost + 1 : ℕ),
    Filter.eventually_gt_atTop 0] with h H hb hp
  obtain ⟨p, m, hl, hu, hL, hm, hg⟩ := H
  refine ⟨p.l, p.u, m + cost * p.work, 2 ^ p.o, p.l_pos, hl, hu, by simpa using hL, ?_,
    fun s ht => p.contract hg ht⟩
  calc
    (↑(m + cost * p.work) : ℝ) ≤ (↑(m + p.work) : ℝ) * (cost + 1 : ℕ) := by
      exact_mod_cast (show m + cost * p.work ≤ (m + p.work) * (cost + 1) by ring_nf; omega)
    _ ≤ ((2 : ℝ) ^ h * (h : ℝ) ^ A * (h : ℝ) ^ (ζ / 2)) * (h : ℝ) ^ (ζ / 2) :=
      mul_le_mul hm hb (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add (by positivity), add_halves]

end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 将可用传输槽位作固定划分

局部电路分组提供端点。使用哪些槽位、它们之间的匹配及其载荷都可以依赖输入和选择器。每一组只需要一个总容量界。电路会自行找出该组中的活动批次。

**英文原文**

A fixed partition of the available transport slots

The local circuits supply endpoints in groups. Which slots are used,
their matching, and their payload may depend on the input and selector.
A group needs only a bound on total capacity. The circuit itself finds
the active batches within each group.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

-- 读法：结构的字段包括 `layer`、`g`、`t`、`q`、`partition`。
structure Plan where
  layer : Layer
  /-- 分组数量的对数。

英文原文：Number of groups, in log scale.
-/
  g : ℕ
  /-- 每组批次数量的对数。

英文原文：Number of batches per group, in log scale.
-/
  t : ℕ
  /-- 每批标识符数量的对数。

英文原文：Number of identifiers in a batch, in log scale.
-/
  q : ℕ
  partition : Idx g × Idx t ≃ Idx (layer.o + layer.c)
  enough : layer.l + layer.d ≤ t + q
  fits : q + 18 ≤ layer.l
  ids : slots (word (layer.l + layer.d)) → Fin layer.r
  disjoint : ∀ i, ids i ≠ layer.orientation

namespace Plan

variable (p : Plan)

-- 读法：在后续公式中，`width` 是 `p.layer.l + p.layer.d` 的缩写。
abbrev width := p.layer.l + p.layer.d
-- 读法：在后续公式中，`Ports` 是 `Idx p.g × p.layer.Footprint` 的缩写。
abbrev Ports := Idx p.g × p.layer.Footprint

-- 读法：`block` 的取值由 `x (i, j)` 给出。
def block (x : p.Ports → Bool) (i : Idx p.g) (j : p.layer.Footprint) : Bool := x (i, j)

-- 读法：`idOf` 的取值由 `Control.decode p.width (v ∘ p.ids)` 给出。
noncomputable def idOf (v : Fin p.layer.r → Bool) : Idx p.width :=
  Control.decode p.width (v ∘ p.ids)

-- 读法：`Valid` 表示以下条件：`(∀ i, Aligned p.layer.orientation p.idOf (p.block x i))` 与 `((∑ i, (marked (p.block x i)).card) + 2 ^ p.g * 2 ^ p.q) * 131072 ≤ 2 ^ p.layer.o * 2 ^ p.q` 同时成立。
def Valid (x : p.Ports → Bool) : Prop :=
  (∀ i, Aligned p.layer.orientation p.idOf (p.block x i)) ∧
  ((∑ i, (marked (p.block x i)).card) + 2 ^ p.g * 2 ^ p.q) * 131072 ≤ 2 ^ p.layer.o * 2 ^ p.q

open Classical in
-- 读法：当 `∀ i, Closed p.layer.orientation (p.block x i)` 成立时取 `1`，否则取 `0`。
noncomputable def close (F : Type) [Field F] (x : p.Ports → Bool) : F :=
  if ∀ i, Closed p.layer.orientation (p.block x i) then 1 else 0

-- 读法：`layout` 的结果类型为 `Idx p.g × Bus (Idx p.t) p.layer.Footprint ≃ p.layer.Ports`。
def layout : Idx p.g × Bus (Idx p.t) p.layer.Footprint ≃ p.layer.Ports :=
  (Equiv.prodSumDistrib _ _ _).trans
    (p.partition.sumCongr ((Equiv.prodAssoc _ _ _).symm.trans
      (p.partition.prodCongr (.refl _))))

-- 读法：`distribute` 的取值由 `let z := p.layout.symm j batches p.idOf p.q p.t (p.block x z.1) z.2` 给出。
noncomputable def distribute (x : p.Ports → Bool) (j : p.layer.Ports) : Bool :=
  let z := p.layout.symm j
  batches p.idOf p.q p.t (p.block x z.1) z.2

end Plan
end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 将各组端点对分配给候选模块

**英文原文**

Distributing groups of endpoint pairs among the candidate modules
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install.Plan

variable (p : Plan) (x : p.Ports → Bool)

-- 读法：在后续公式中，`split` 是 `batches p.idOf p.q p.t (p.block x i)` 的缩写。
private noncomputable abbrev split (i : Idx p.g) := batches p.idOf p.q p.t (p.block x i)

-- 读法：`p.distribute x (.inl (p.partition (i, j)))` 等于 `p.split x i (.inl j)`。
private theorem flags (i : Idx p.g) (j : Idx p.t) :
    p.distribute x (.inl (p.partition (i, j))) = p.split x i (.inl j) := by
  change p.distribute x (p.layout (i, .inl j)) = _
  simp only [distribute, Equiv.symm_apply_apply]

-- 读法：`payload (p.distribute x) (p.partition (i, j))` 等于 `payload (p.split x i) j`。用函数外延性比较等号两侧在 `k` 处的取值。
private theorem values (i : Idx p.g) (j : Idx p.t) :
    payload (p.distribute x) (p.partition (i, j)) = payload (p.split x i) j := by
  funext k
  change p.distribute x (p.layout (i, .inr (j, k))) = _
  simp only [distribute, Equiv.symm_apply_apply]
  rfl

-- 读法：`p.partition (i, j) ∈ marked (p.distribute x)` 与 `j ∈ marked (p.split x i)` 等价。
private theorem in_partition (i : Idx p.g) (j : Idx p.t) :
    p.partition (i, j) ∈ marked (p.distribute x) ↔ j ∈ marked (p.split x i) := by
  rw [mem_marked, flags, mem_marked]

-- 读法：`(marked (p.distribute x)).card` 等于 `∑ i, (marked (p.split x i)).card`。
private theorem count_distributed :
    (marked (p.distribute x)).card = ∑ i, (marked (p.split x i)).card := by
  simp only [marked, Finset.card_filter]
  rw [← p.partition.sum_comp, Fintype.sum_prod_type]
  simp only [flags]

-- 读法：`p.idOf (flip p.layer.orientation y)` 等于 `p.idOf y`。用函数外延性比较等号两侧在 `j` 处的取值。
private theorem idOf_flip (y : Fin p.layer.r → Bool) :
    p.idOf (flip p.layer.orientation y) = p.idOf y := by
  unfold idOf
  apply congrArg
  funext j
  simp [flip, p.disjoint j]

-- 读法：`p.layer.Valid (p.distribute x)` 与 `p.layer.close F (p.distribute x) = p.close F x` 同时成立。
theorem distributed (p : Plan) (F : Type) [Field F] (x : p.Ports → Bool) (h : p.Valid x) :
    p.layer.Valid (p.distribute x) ∧ p.layer.close F (p.distribute x) = p.close F x := by
  have hd (i : Idx p.g) := divide _ _ p.idOf_flip p.enough (p.block x i) (h.1 i)
  have hc : (marked (p.distribute x)).card * 2 ^ p.q ≤
      (∑ i, (marked (p.block x i)).card) + 2 ^ p.g * 2 ^ p.q := by
    rw [count_distributed, Finset.sum_mul]
    calc
      _ ≤ ∑ i, ((marked (p.block x i)).card + 2 ^ p.q) :=
        Finset.sum_le_sum fun i _ => (hd i).1
      _ = _ := by simp [Finset.sum_add_distrib]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos p.q)
    rw [Nat.mul_right_comm]
    exact (Nat.mul_le_mul_right 131072 hc).trans h.2
  · intro k hk
    -- 推导：从 `p.partition.surjective k` 中取出 `⟨i, j⟩, rfl`。
    obtain ⟨⟨i, j⟩, rfl⟩ := p.partition.surjective k
    rw [values]
    obtain ⟨hb, hu⟩ := (hd i).2.1 j ((p.in_partition x i j).mp hk)
    refine ⟨(Nat.mul_le_mul_right _ hb).trans ?_, hu⟩
    calc
      2 * 2 ^ p.q * 131072 = 2 ^ (p.q + 18) := by rw [pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) p.fits
  · have iffClosed : (∀ k ∈ marked (p.distribute x),
        Closed p.layer.orientation (payload (p.distribute x) k)) ↔
        ∀ i, Closed p.layer.orientation (p.block x i) := by
      constructor
      · intro H i
        apply (hd i).2.2.mp
        intro j hj
        have hm := H _ ((p.in_partition x i j).mpr hj)
        rw [values] at hm
        exact hm
      · intro H k hk
        obtain ⟨⟨i, j⟩, rfl⟩ := p.partition.surjective k
        rw [values]
        exact (hd i).2.2.mpr (H i) j ((p.in_partition x i j).mp hk)
    classical
    rw [Layer.close, Finset.prod_boole, close]
    congr 1
    exact propext iffClosed

end OAI.LinearAlgebra.MatrixExponent.Install.Plan
end
