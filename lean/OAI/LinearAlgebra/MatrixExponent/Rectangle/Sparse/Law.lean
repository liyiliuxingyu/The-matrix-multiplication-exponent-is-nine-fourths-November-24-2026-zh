-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Model
import OAI.LinearAlgebra.TensorSpectrum.TagWords
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.TensorSpectrum.TagEntropy
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask

section
/-!
# 加权矩形乘积的分解

**英文原文**

Decompositions of weighted rectangular products
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k i' j' k' I J K r s : ℕ}

-- 读法：要证明的命题是 `WeightedRankLE w (i * j * k)`。
/-- 行、列与内部索引的每个组合对应一个加项。

英文原文：One term for every row, column and inner index.
-/
theorem weighted_volume (w : Fin i → Fin j → Fin k → F) : WeightedRankLE w (i * j * k) := by
  rw [mul_right_comm i j k]
  let e : Fin (i * k * j) ≃ Pos i k × Fin j :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))
  refine ⟨fun l x => if (e l).1 = x then 1 else 0,
    fun l y => if (e l).1.2 = y.1 ∧ (e l).2 = y.2 then 1 else 0,
    fun l z => if (e l).1.1 = z.1 ∧ (e l).2 = z.2 then w (e l).1.1 (e l).2 (e l).1.2 else 0, ?_⟩
  intro x y z
  rw [Fintype.sum_eq_single (e.symm (x, y.2))]
  · by_cases h : x.2 = y.1 <;> simp [h]
  · intro l hl
    by_cases h : (e l).1 = x
    · have h' : (e l).2 ≠ y.2 := fun h' => hl (e.eq_symm_apply.mpr (Prod.ext h h'))
      simp [h']
    · simp [h]

-- 读法：要证明的命题是 `WeightedRankLE (fun x y z => w (u x).1 (q y).1 (p z).1 * v (u x).2 (q y).2 (p z).2) (r * s)`。
/-- 将两个分解取张量积，允许任意枚举配对得到的边索引。对配成对的各项求和后，系数恒等式分解为两个因子的乘积。

英文原文：Tensor two decompositions, allowing an arbitrary enumeration of paired
side indices. Summing over the paired terms factors the coefficient identity.
-/
theorem WeightedRankLE.tensor {w : Fin i → Fin j → Fin k → F} {v : Fin i' → Fin j' → Fin k' → F}
    (h : WeightedRankLE w r) (h' : WeightedRankLE v s)
    (u : Fin I ≃ Pos i i') (q : Fin J ≃ Pos j j') (p : Fin K ≃ Pos k k') :
    WeightedRankLE (fun x y z => w (u x).1 (q y).1 (p z).1 * v (u x).2 (q y).2 (p z).2) (r * s) := by
  obtain ⟨a, b, c, h⟩ := h
  obtain ⟨a', b', c', h'⟩ := h'
  let coeff {n m g l N M : ℕ} (e : Fin N ≃ Pos n m) (f : Fin M ≃ Pos g l)
      (α : Fin r → Pos n g → F) (β : Fin s → Pos m l → F) (t : Fin (r * s)) (x : Pos N M) :=
    α (finProdFinEquiv.symm t).1 ((e x.1).1, (f x.2).1) *
      β (finProdFinEquiv.symm t).2 ((e x.1).2, (f x.2).2)
  refine ⟨coeff u p a a', coeff p q b b', coeff u q c c', ?_⟩
  intro x y z
  calc
    _ = (∑ l, a l ((u x.1).1, (p x.2).1) * b l ((p y.1).1, (q y.2).1) *
          c l ((u z.1).1, (q z.2).1)) *
        (∑ l, a' l ((u x.1).2, (p x.2).2) * b' l ((p y.1).2, (q y.2).2) *
          c' l ((u z.1).2, (q z.2).2)) := by
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l' _
      simp only [coeff, Equiv.symm_apply_apply]
      rw [mul_mul_mul_comm (a _ _), mul_mul_mul_comm]
    _ = _ := by
      rw [h, h', ite_mul, zero_mul, mul_ite, mul_zero, ← ite_and]
      have he {n m N : ℕ} (e : Fin N ≃ Pos n m) (u v : Fin N) :
          u = v ↔ (e u).1 = (e v).1 ∧ (e u).2 = (e v).2 :=
        e.injective.eq_iff.symm.trans Prod.ext_iff
      simp only [he u x.1 z.1, he p x.2 y.1, he q y.2 z.2, and_assoc, and_left_comm, and_comm]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
置换对称性与基本的面积、体积上界和下界。

**英文原文**

Permutation symmetry and the elementary area and volume bounds.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ}

-- 读法：在 `F` 上，三个尺寸为 `j`、`k`、`i` 的矩阵乘法张量的秩至多为 `r`。
theorem RankLE.cycle (h : RankLE F i j k r) : RankLE F j k i r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => c l x.swap, a, fun l z => b l z.swap, ?_⟩
  intro x y z
  simpa only [Prod.fst_swap, Prod.snd_swap, mul_assoc, mul_comm, mul_left_comm,
    and_assoc, and_comm, and_left_comm, eq_comm] using h y z.swap x.swap

-- 读法：在 `F` 上，三个尺寸为 `j`、`i`、`k` 的矩阵乘法张量的秩至多为 `r`。
theorem RankLE.transpose (h : RankLE F i j k r) : RankLE F j i k r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => b l x.swap, fun l y => a l y.swap, fun l z => c l z.swap, ?_⟩
  intro x y z
  simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm, and_assoc, and_comm, and_left_comm,
    eq_comm] using h y.swap x.swap z.swap

-- 读法：`i * j` 不超过 `r`。
/-- 固定内部索引后，在输出展平矩阵中得到一个单位子矩阵。

英文原文：Fixing the inner index gives an identity submatrix of the output flattening.
-/
theorem RankLE.area (h : RankLE F i j k r) (hk : 0 < k) : i * j ≤ r := by
  obtain ⟨a, b, c, h⟩ := h
  let v : Fin k := ⟨0, hk⟩
  let A : Matrix (Pos i j) (Fin r) F := fun x l => a l (x.1, v) * b l (v, x.2)
  let B : Matrix (Fin r) (Pos i j) F := c
  have hAB : A * B = 1 := by
    ext x z
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [A, B, Prod.ext_iff, true_and] using h (x.1, v) (v, x.2) z
  have := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  simpa only [hAB, Matrix.rank_one, Pos, Fintype.card_prod, Fintype.card_fin] using this

-- 读法：在 `F` 上，三个尺寸为 `i`、`j`、`k` 的矩阵乘法张量的秩至多为 `(i * j * k)`。使用 `weighted_volume` 给出的结论。
/-- 行、列与内部索引的每个组合对应一个乘积。

英文原文：One product per row, column and inner index.
-/
theorem rank_volume (F : Type*) [Field F] (i j k : ℕ) : RankLE F i j k (i * j * k) :=
  weighted_volume (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
矩形分解的张量积、取幂与循环对称化。

**英文原文**

Tensor products, powers and cyclic symmetrization of rectangular decompositions.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F K : Type*} [Field F] [Field K] {i j k i' j' k' r s : ℕ}

-- 读法：在 `K` 上，三个尺寸为 `i`、`j`、`k` 的矩阵乘法张量的秩至多为 `r`。
theorem RankLE.map (h : RankLE F i j k r) (f : F →+* K) : RankLE K i j k r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => f (a l x), fun l y => f (b l y), fun l z => f (c l z), ?_⟩
  intro x y z
  simpa only [map_sum, map_mul, apply_ite f, map_one, map_zero] using congrArg f (h x y z)

-- 读法：在 `F` 上，三个尺寸为 `(i * i')`、`(j * j')`、`(k * k')` 的矩阵乘法张量的秩至多为 `(r * s)`。
/-- 将每个矩阵索引拆成两个数位，并将相应系数相乘。对成对的各项求和后，系数恒等式分解为两个因子的乘积。

英文原文：Split each matrix index into two digits and multiply the corresponding
coefficients. Summing over pairs of terms factors the coefficient identity.
-/
theorem RankLE.tensor (h : RankLE F i j k r) (h' : RankLE F i' j' k' s) :
    RankLE F (i * i') (j * j') (k * k') (r * s) := by
  have hw : WeightedRankLE (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) r := h
  have hv : WeightedRankLE (fun (_ : Fin i') (_ : Fin j') (_ : Fin k') => (1 : F)) s := h'
  have ht := hw.tensor hv finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm
  simp only [one_mul] at ht
  exact ht

-- 读法：在 `F` 上，三个尺寸为 `(i ^ p)`、`(j ^ p)`、`(k ^ p)` 的矩阵乘法张量的秩至多为 `(r ^ p)`。对 `p` 作归纳。
theorem RankLE.pow (h : RankLE F i j k r) (p : ℕ) :
    RankLE F (i ^ p) (j ^ p) (k ^ p) (r ^ p) := by
  induction p with
  | zero => simpa using rank_volume F 1 1 1
  | succ p ih => simpa only [pow_succ] using ih.tensor h

-- 读法：要证明的命题是 `MatrixExponent.RankLE F (i * j * k) (r ^ 3)`。
/-- 对三种循环排列取张量积后，所有边长均等于体积。

英文原文：Tensoring the three cyclic arrangements makes all sides equal to the volume.
-/
theorem RankLE.symmetrize (h : RankLE F i j k r) : MatrixExponent.RankLE F (i * j * k) (r ^ 3) := by
  change RankLE F (i * j * k) (i * j * k) (i * j * k) (r ^ 3)
  simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (h.tensor h.cycle).tensor h.cycle.cycle

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# 加权乘积的各次幂

幂的各边索引由数位串表示。系数按数位相乘，因此支撑大小相乘，秩上界则具有次乘性。

**英文原文**

Powers of weighted products

Side indices of a power are digit strings. Coefficients multiply over
digits, so support sizes multiply and rank bounds are submultiplicative.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ}

-- 读法：要证明的命题是 `WeightedRankLE w (rankW w)`。使用 `Nat.sInf_mem` 给出的结论。
theorem rankW_spec (w : Fin i → Fin j → Fin k → F) : WeightedRankLE w (rankW w) :=
  Nat.sInf_mem (show {r : ℕ | WeightedRankLE w r}.Nonempty from ⟨_, weighted_volume w⟩)

-- 读法：`rankW w` 不超过 `r`。使用 `Nat.sInf_le` 给出的结论。
theorem rankW_le {w : Fin i → Fin j → Fin k → F} (h : WeightedRankLE w r) : rankW w ≤ r :=
  Nat.sInf_le h

-- 读法：`WPower (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) n` 等于 `fun _ _ _ => 1`。用函数外延性比较等号两侧在 `a b c` 处的取值。
@[simp] theorem WPower_one (n : ℕ) :
    WPower (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) n = fun _ _ _ => 1 := by
  funext a b c
  simp [WPower]

-- 读法：`split` 的结果类型为 `Fin (d ^ (n + m)) ≃ Fin (d ^ n) × Fin (d ^ m)`。
private def split (d n m : ℕ) : Fin (d ^ (n + m)) ≃ Fin (d ^ n) × Fin (d ^ m) :=
  finFunctionFinEquiv.symm.trans ((Fin.appendEquiv n m).symm.trans
    (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv))

-- 读法：`rankW (WPower w (n + m))` 不超过 `rankW (WPower w n) * rankW (WPower w m)`。这里调用 `rankW_le`。
theorem rankW_add (w : Fin i → Fin j → Fin k → F) (n m : ℕ) :
    rankW (WPower w (n + m)) ≤ rankW (WPower w n) * rankW (WPower w m) := by
  apply rankW_le
  have h := (rankW_spec (WPower w n)).tensor (rankW_spec (WPower w m))
    (split i n m) (split j n m) (split k n m)
  convert h using 1
  funext a b c
  unfold WPower
  rw [Fin.prod_univ_add]
  simp [split, Fin.appendEquiv]

-- 读法：`(∑ a : Fin (d ^ n), ∏ l, f l (finFunctionFinEquiv.symm a l))` 等于 `∏ l, ∑ a, f l a`。
private theorem sum_words {n d : ℕ} (f : Fin n → Fin d → ℕ) :
    (∑ a : Fin (d ^ n), ∏ l, f l (finFunctionFinEquiv.symm a l)) = ∏ l, ∑ a, f l a := by
  rw [← finFunctionFinEquiv.sum_comp, Fintype.prod_sum]
  simp only [Equiv.symm_apply_apply]

open Classical in
-- 读法：`(if ∏ l, f l = 0 then 0 else 1)` 等于 `∏ l, if f l = 0 then (0 : ℕ) else 1`。按 `∃ l, f l = 0` 成立与否分情况。
private theorem indicator_prod {n : ℕ} (f : Fin n → F) :
    (if ∏ l, f l = 0 then 0 else 1) = ∏ l, if f l = 0 then (0 : ℕ) else 1 := by
  by_cases h : ∃ l, f l = 0
  · obtain ⟨l, hl⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ l) hl, ite_eq_left rfl]
    exact (Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])).symm
  · push Not at h
    simp [h, Finset.prod_ne_zero_iff]

-- 读法：`supportSize (WPower w n)` 等于 `(supportSize w) ^ n`。
theorem supportSize_power (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    supportSize (WPower w n) = (supportSize w) ^ n := by
  classical
  unfold supportSize WPower
  simp_rw [indicator_prod]
  let f a b c := if w a b c = 0 then (0 : ℕ) else 1
  have h₁ (a : Fin (i ^ n)) (b : Fin (j ^ n)) :=
    sum_words (fun l c => f (finFunctionFinEquiv.symm a l) (finFunctionFinEquiv.symm b l) c)
  have h₂ (b : Fin (j ^ n)) :=
    sum_words (fun l a => ∑ c, f a (finFunctionFinEquiv.symm b l) c)
  have h₃ := sum_words (fun (_ : Fin n) b => ∑ a, ∑ c, f a b c)
  unfold f at h₁ h₂ h₃
  simp_rw [h₁, h₂, h₃]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

-- 读法：`rankW (WPower w (n * m))` 不超过 `(rankW (WPower w n)) ^ m`。这里调用 `rankW_add`。
theorem rankW_mul (w : Fin i → Fin j → Fin k → F) (n m : ℕ) (hm : 1 ≤ m) :
    rankW (WPower w (n * m)) ≤ (rankW (WPower w n)) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => rw [mul_one, pow_one]
  | succ m _ ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (rankW_add w _ _).trans (Nat.mul_le_mul_right _ ih)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# 给三个字母表着色以分离三元组

对两个不同标签，在所有 `m` 色着色中，只有 `1/m` 会令它们同色。由并集界和取平均，三个步骤的每一步都至少保留六分之五的候选三元组。补全列表始终相对于原支撑定义。

**英文原文**

Isolating triples by coloring the three alphabets

For two different labels only a fraction `1/m` of the `m`-colorings
identify them. The union bound and averaging retain at least five
sixths of the candidate triples at each of the three steps. Completion
lists always refer to the original support.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {α : Type*} {i m d : ℕ}

-- 读法：`collisions` 的取值由 `univ.filter fun c : Fin i → Fin m => c x = c y` 给出。
private def collisions (m : ℕ) (x y : Fin i) :=
  univ.filter fun c : Fin i → Fin m => c x = c y

-- 读法：`(collisions m x y).card * m` 不超过 `Fintype.card (Fin i → Fin m)`。按 `Subtype.ext` 的外延性准则比较各分量。
private theorem collision_bound {x y : Fin i} (h : x ≠ y) :
    (collisions m x y).card * m ≤ Fintype.card (Fin i → Fin m) := by
  let f (p : (collisions m x y) × Fin m) := Function.update p.1.val x p.2
  have hi : Function.Injective f := by
    rintro ⟨c, a⟩ ⟨c', a'⟩ he
    have ha : a = a' := by simpa [f] using congrFun he x
    have hc (z) (hz : z ≠ x) : c.val z = c'.val z := by simpa [f, hz] using congrFun he z
    have hh : c = c' := by
      apply Subtype.ext
      funext z
      by_cases hz : z = x
      · subst z
        exact (mem_filter.mp c.property).2.trans ((hc y h.symm).trans (mem_filter.mp c'.property).2.symm)
      · exact hc z hz
    exact Prod.ext hh ha
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hi

-- 读法：存在 `(c : Fin i → Fin (6 * d)) (V : Finset α)`，由 `V ⊆ U ∧ 5 * U.card ≤ 6 * V.card ∧ ∀ t ∈ V, ∀ x ∈ N t, c x = c (label t)` 推出 `x = label t`。这里调用 `Nat.le_of_mul_le_mul_right`。
private theorem one_label (U : Finset α) (label : α → Fin i) (N : α → Finset (Fin i))
    (hd : 0 < d) (hN : ∀ t ∈ U, (N t).card ≤ d) :
    ∃ (c : Fin i → Fin (6 * d)) (V : Finset α),
      V ⊆ U ∧ 5 * U.card ≤ 6 * V.card ∧ ∀ t ∈ V, ∀ x ∈ N t, c x = c (label t) → x = label t := by
  classical
  let C := Fin i → Fin (6 * d)
  let bad (t : α) : Finset C := ((N t).erase (label t)).biUnion fun x => collisions (6 * d) x (label t)
  have hb (t) (ht : t ∈ U) : 6 * (bad t).card ≤ Fintype.card C := by
    let A := (N t).erase (label t)
    have hA : A.card ≤ d := card_erase_le.trans (hN t ht)
    apply Nat.le_of_mul_le_mul_right _ hd
    calc
      6 * (bad t).card * d = (bad t).card * (6 * d) := by ring
      _ ≤ (∑ x ∈ A, (collisions (6 * d) x (label t)).card) * (6 * d) :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ ≤ ∑ _ ∈ A, Fintype.card C := by
        rw [sum_mul]
        exact sum_le_sum (fun x hx => collision_bound (mem_erase.mp hx).1)
      _ ≤ Fintype.card C * d := by
        simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm A.card]
        exact Nat.mul_le_mul_left _ hA
  -- 推导：记下中间结论 `havg`：`(∑ c : C, 6 * (U.filter fun t => c ∈ bad t).card) ≤ ∑ _ : C, U.card`。
  have havg : (∑ c : C, 6 * (U.filter fun t => c ∈ bad t).card) ≤ ∑ _ : C, U.card := by
    calc
      _ = ∑ t ∈ U, 6 * (bad t).card := by
        simp_rw [card_filter, mul_sum]
        rw [sum_comm]
        simp [← mul_sum, mul_comm]
      _ ≤ ∑ _ ∈ U, Fintype.card C := sum_le_sum hb
      _ = _ := by simp [mul_comm]
  have : Nonempty C := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨c, _, hc⟩ := exists_le_of_sum_le univ_nonempty havg
  refine ⟨c, U.filter (fun t => c ∉ bad t), filter_subset _ _, ?_, ?_⟩
  -- 推导：记下中间结论 `he`：`= card_filter_add_card_filter_not (s`。
  · have he := card_filter_add_card_filter_not (s := U) (fun t => c ∈ bad t)
    omega
  · intro t ht x hx he
    by_contra hne
    exact (mem_filter.mp ht).2 (mem_biUnion.mpr
      ⟨x, mem_erase.mpr ⟨hne, hx⟩, mem_filter.mpr ⟨mem_univ _, he⟩⟩)

-- 读法：`color` 的证明用到 `hV.trans`、`hY.trans`。
theorem color {i j k d e f : ℕ} (S U : Finset (Cell i j k))
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hr : ∀ t ∈ U, (rows S t).card ≤ d) (hc : ∀ t ∈ U, (cols S t).card ≤ e)
    (hi : ∀ t ∈ U, (inner S t).card ≤ f) :
    ∃ (a : Fin i → Fin (6 * d)) (b : Fin j → Fin (6 * e)) (c : Fin k → Fin (6 * f))
      (V : Finset (Cell i j k)), V ⊆ U ∧ U.card ≤ 2 * V.card ∧
      (∀ t ∈ V, ∀ x ∈ rows S t, a x = a t.1 → x = t.1) ∧
      (∀ t ∈ V, ∀ y ∈ cols S t, b y = b t.2.1 → y = t.2.1) ∧
      (∀ t ∈ V, ∀ z ∈ inner S t, c z = c t.2.2 → z = t.2.2) := by
  obtain ⟨a, X, hX, hx, ha⟩ := one_label U (·.1) (rows S) hd hr
  obtain ⟨b, Y, hY, hy, hb⟩ := one_label X (·.2.1) (cols S) he fun t ht => hc t (hX ht)
  obtain ⟨c, V, hV, hv, hc⟩ := one_label Y (·.2.2) (inner S) hf fun t ht => hi t (hX (hY ht))
  exact ⟨a, b, c, V, hV.trans (hY.trans hX), by omega,
    fun t ht => ha t (hY (hV ht)), fun t ht => hb t (hV ht), hc⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# 补全集有界时的有限秩比较

**英文原文**

A finite rank comparison for bounded completion sets
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse

-- 读法：`DegreeBound` 的结果类型为 `Prop`。
/-- 该常数计入三次独立着色的成本，以及所选三元组中至多半数的损失。取张量幂可消去该常数。

英文原文：The constant pays for three independent colorings and the
loss of at most half of the selected triples. Tensor powers remove it.
-/
def DegreeBound (F : Type*) [Field F] : Prop :=
  ∀ i j k I J K r : ℕ, 0 < I → 0 < J → 0 < K →
    ∀ (w : Fin i → Fin j → Fin k → F) (U : Finset (Cell i j k)), U ⊆ support w →
      (∀ t ∈ U, (rows (support w) t).card ≤ I) →
      (∀ t ∈ U, (cols (support w) t).card ≤ J) →
      (∀ t ∈ U, (inner (support w) t).card ≤ K) →
      WeightedRankLE w r →
        U.card * Real.exp (exponent F (Real.log I) (Real.log J) (Real.log K)) ≤
          432 * (I : ℝ) * J * K * r

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# 部分乘积各次幂的补全方案数

**英文原文**

Completion counts for powers of a partial product
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {F : Type*} [Field F] {i j k n : ℕ}

-- 读法：`pack` 的结果类型为 `Cell (i ^ n) (j ^ n) (k ^ n)`。
def pack (p : Fin n → Cell i j k) : Cell (i ^ n) (j ^ n) (k ^ n) :=
  (finFunctionFinEquiv (fun l => (p l).1), finFunctionFinEquiv (fun l => (p l).2.1),
    finFunctionFinEquiv (fun l => (p l).2.2))

-- 读法：`(@pack i j k n)` 是单射。这里调用 `Function.LeftInverse.injective`。
theorem pack_injective : Function.Injective (@pack i j k n) := by
  let unpack (t : Cell (i ^ n) (j ^ n) (k ^ n)) (l : Fin n) :=
    (finFunctionFinEquiv.symm t.1 l, finFunctionFinEquiv.symm t.2.1 l,
      finFunctionFinEquiv.symm t.2.2 l)
  apply Function.LeftInverse.injective (g := unpack)
  intro p
  funext l
  simp [unpack, pack]

variable (w : Fin i → Fin j → Fin k → F) (p : Fin n → Cell i j k)

-- 读法：`(support w).card` 等于 `supportSize w`。
theorem card_support : (support w).card = supportSize w := by
  classical
  rw [support, card_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ite_not]
  rw [sum_comm]
  rfl

-- 读法：`pack p ∈ support (WPower w n)` 与 `∀ l, p l ∈ support w` 等价。
theorem mem_pack : pack p ∈ support (WPower w n) ↔ ∀ l, p l ∈ support w := by
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

-- 读法：`A.card` 等于 `∏ l, (B l).card`。
/-- 补全的标签是相互独立的数位串。

英文原文：Completed labels are independent digit strings.
-/
private theorem count_digits {d : ℕ} (A : Finset (Fin (d ^ n))) (B : Fin n → Finset (Fin d))
    (h : ∀ x, x ∈ A ↔ ∀ l, finFunctionFinEquiv.symm x l ∈ B l) :
    A.card = ∏ l, (B l).card := by
  have he : A = (Fintype.piFinset B).map finFunctionFinEquiv.toEmbedding := by
    ext x
    rw [h, mem_map_equiv, Fintype.mem_piFinset]
  rw [he, card_map, Fintype.card_piFinset]

-- 读法：`(rows (support (WPower w n)) (pack p)).card` 等于 `∏ l, (rows (support w) (p l)).card`。这里调用 `count_digits`。
theorem rows_power :
    (rows (support (WPower w n)) (pack p)).card = ∏ l, (rows (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [rows, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

-- 读法：`(cols (support (WPower w n)) (pack p)).card` 等于 `∏ l, (cols (support w) (p l)).card`。这里调用 `count_digits`。
theorem cols_power :
    (cols (support (WPower w n)) (pack p)).card = ∏ l, (cols (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [cols, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

-- 读法：`(inner (support (WPower w n)) (pack p)).card` 等于 `∏ l, (inner (support w) (p l)).card`。这里调用 `count_digits`。
theorem inner_power :
    (inner (support (WPower w n)) (pack p)).card = ∏ l, (inner (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [inner, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# 给定支撑字类型时的补全方案数

**英文原文**

Completion counts on a fixed type of support words
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open OAI.LinearAlgebra.TensorSpectrum

-- 读法：这里调用 `mem_pack`。
/-- 固定独立选取的支撑三元组的频数类型。相应的张量幂中可得到与该类型的词数一样多的互异三元组，而且它们在三侧的补全数均分别相同。

英文原文：A type of independent supported triples gives as many distinct
triples in the power, all with the same three completion counts.
-/
theorem fiber {F : Type*} [Field F] {i j k m : ℕ}
    (w : Fin i → Fin j → Fin k → F) (e : Fin m ≃ support w) (n : ℕ) (t : TagWords.CountVector m n) :
    ∃ U : Finset (Cell (i ^ n) (j ^ n) (k ^ n)), U ⊆ support (WPower w n) ∧
      U.card = (TagWords.fiber t).card ∧ ∀ p ∈ U,
        (rows (support (WPower w n)) p).card = TagWords.countWeight (fun a => (rows (support w) (e a).val).card) t ∧
        (cols (support (WPower w n)) p).card = TagWords.countWeight (fun a => (cols (support w) (e a).val).card) t ∧
        (inner (support (WPower w n)) p).card = TagWords.countWeight (fun a => (inner (support w) (e a).val).card) t := by
  let f : TagWords.Word m n ↪ Cell (i ^ n) (j ^ n) (k ^ n) :=
    ⟨fun x => pack fun l => (e (x l)).val, fun _ _ he =>
      funext fun l => e.injective (Subtype.ext (congrFun (pack_injective he) l))⟩
  refine ⟨(TagWords.fiber t).map f, ?_, Finset.card_map _, ?_⟩
  · intro p hp
    -- 推导：从 `Finset.mem_map.mp hp` 中取出 `x, _, rfl`。
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hp
    exact (mem_pack w _).2 fun l => (e (x l)).property
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hp
    rw [show f x = pack (fun l => (e (x l)).val) from rfl, rows_power, cols_power, inner_power]
    have he (a : Fin m → ℕ) : ∏ l, a (x l) = TagWords.countWeight a t :=
      TagWords.wordWeight_eq_of_mem_fiber a hx
    exact ⟨he (fun a => (rows (support w) (e a).val).card),
      he (fun a => (cols (support w) (e a).val).card),
      he (fun a => (inner (support w) (e a).val).card)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# 对偶总相关量的非负性

先对第一个索引与其余两个索引组成的有序对使用熵的次可加性，再固定第一个索引，在每个切片内对其余两个索引使用同一性质。

**英文原文**

Nonnegative dual total correlation

Apply entropy subadditivity to the first index and the pair of
remaining indices, then to the two remaining indices within
each fixed first-index slice.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

-- 读法：`left` 的取值由 `univ.filter fun x => (x, y) ∈ S` 给出。
private def left (S : Finset (X × Y)) (y : Y) := univ.filter fun x => (x, y) ∈ S

-- 读法：`right` 的取值由 `univ.filter fun y => (x, y) ∈ S` 给出。
private def right (S : Finset (X × Y)) (x : X) := univ.filter fun y => (x, y) ∈ S

-- 读法：结论为 `∑ x, ∑ y ∈ right S x, f (x, y) = ∑ p ∈ S, f p`。
private theorem sum_right (S : Finset (X × Y)) (f : X × Y → ℝ) :
    ∑ x, ∑ y ∈ right S x, f (x, y) = ∑ p ∈ S, f p := by
  simp only [right, sum_filter]
  rw [← Fintype.sum_prod_type (fun p => if p ∈ S then f p else 0)]
  simp

-- 读法：结论为 `∑ x, ((right S x).card : ℝ) = S.card`。这里调用 `sum_right`。
private theorem count_right (S : Finset (X × Y)) : ∑ x, ((right S x).card : ℝ) = S.card := by
  simpa using sum_right S (fun _ => 1)

-- 读法：结论为 `∑ y, ((left S y).card : ℝ) = S.card`。
private theorem count_left (S : Finset (X × Y)) : ∑ y, ((left S y).card : ℝ) = S.card := by
  rw [← count_right S]
  simp only [left, right, card_filter, Nat.cast_sum]
  rw [sum_comm]

-- 读法：结论为 `∑ p ∈ S, (Real.log (right S p.1).card + Real.log (left S p.2).card) ≤ S.card * Real.log S.card`。
/-- 对关系上的均匀分布，两个条件熵之和不超过联合熵。

英文原文：For the uniform distribution on a relation, the sum of the
two conditional entropies is bounded by the joint entropy.
-/
private theorem pair_bound (S : Finset (X × Y)) :
    ∑ p ∈ S, (Real.log (right S p.1).card + Real.log (left S p.2).card) ≤
      S.card * Real.log S.card := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let a x := ((right S x).card : ℝ)
  let b y := ((left S y).card : ℝ)
  let m : ℝ := S.card
  have hm : 0 < m := Nat.cast_pos.mpr hS.card_pos
  have hsum : ∑ p ∈ S, a p.1 * b p.2 ≤ m * m := by
    calc
      _ ≤ ∑ p : X × Y, a p.1 * b p.2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intro p _ _
        unfold a b
        positivity)
      _ = m * m := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, ← sum_mul, a, b, count_left, count_right, m]
  calc
    _ ≤ ∑ p ∈ S, (a p.1 * b p.2 / m - 1 + Real.log m) := by
      apply sum_le_sum
      rintro ⟨x, y⟩ hxy
      -- 推导：记下中间结论 `ha`：`0 < a x`。
      have ha : 0 < a x := Nat.cast_pos.mpr (card_pos.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hxy⟩⟩)
      have hb : 0 < b y := Nat.cast_pos.mpr (card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hxy⟩⟩)
      have hh := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hb) hm)
      rw [Real.log_div (mul_pos ha hb).ne' hm.ne', Real.log_mul ha.ne' hb.ne'] at hh
      exact sub_le_iff_le_add.mp hh
    _ ≤ _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
      change _ / m - m + m * Real.log m ≤ m * Real.log m
      linarith only [(div_le_iff₀ hm).mpr hsum]

-- 读法：`0` 不超过 `premium S`。这里调用 `sum_le_sum`。
theorem premium_nonneg {i j k : ℕ} (S : Finset (Cell i j k)) (hS : S.Nonempty) :
    0 ≤ premium S := by
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have h₁ := pair_bound S
  have h₂ : ∑ p ∈ S, (Real.log (cols S p).card + Real.log (inner S p).card) ≤
      ∑ p ∈ S, Real.log (right S p.1).card := by
    rw [← sum_right S, ← sum_right S]
    apply sum_le_sum
    intro x _
    have he (t : Fin j × Fin k) : cols S (x, t) = left (right S x) t.2 := by
      ext y; simp [cols, left, right]
    have hf (t : Fin j × Fin k) : inner S (x, t) = right (right S x) t.1 := by
      ext z; simp [inner, right]
    simp only [he, hf, sum_const, nsmul_eq_mul]
    simpa only [add_comm] using pair_bound (right S x)
  unfold premium
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply sub_nonneg.mpr
  unfold conditional
  rw [div_le_iff₀ hm, mul_comm]
  have he (t : Cell i j k) : rows S t = left S t.2 := rfl
  simp only [he, sum_add_distrib] at *
  linarith only [h₁, h₂]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-!
# 由补全方案数构造乘法权重

**英文原文**

Multiplicative weights from completion counts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open OAI.LinearAlgebra.TensorSpectrum.TagWords

-- 读法：`unitWeight` 的取值由 `Real.exp (s * (Real.log x + Real.log y + Real.log z))` 给出。
def unitWeight (s : ℝ) (x y z : ℕ) := Real.exp (s * (Real.log x + Real.log y + Real.log z))

variable {m n : ℕ}

-- 读法：`Real.log (countWeight a t : ℕ)` 等于 `∑ i, (t i).val * Real.log (a i)`。
private theorem log_count (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) (t : CountVector m n) :
    Real.log (countWeight a t : ℕ) = ∑ i, (t i).val * Real.log (a i) := by
  simp only [countWeight, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (by exact_mod_cast (ha i).ne'))]
  simp only [Real.log_pow]

-- 读法：`countWeight (fun i => unitWeight s (a i) (b i) (c i)) t` 等于 `unitWeight s (countWeight a t) (countWeight b t) (countWeight c t)`。这里调用 `Finset.prod_congr`。
theorem unit_count (s : ℝ) (a b c : Fin m → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) (t : CountVector m n) :
    countWeight (fun i => unitWeight s (a i) (b i) (c i)) t =
      unitWeight s (countWeight a t) (countWeight b t) (countWeight c t) := by
  unfold unitWeight
  rw [log_count a ha t, log_count b hb t, log_count c hc t,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

-- 读法：`m * Real.exp ((∑ i, a i) / m)` 不超过 `∑ i, Real.exp (a i)`。
theorem sum_exp_lower (hm : 0 < m) (a : Fin m → ℝ) :
    m * Real.exp ((∑ i, a i) / m) ≤ ∑ i, Real.exp (a i) := by
  have hm' : 0 < (m : ℝ) := by positivity
  have hp : 0 < ∑ i, Real.exp (a i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let b := (m : ℝ)⁻¹ * ∑ i, Real.exp (a i)
  have he := TensorSpectrum.weighted_log_le_log_of_sum_le (fun _ => (m : ℝ)⁻¹)
    (fun i => Real.exp (a i)) b (fun _ => by positivity) (by simp [hm.ne'])
    (fun _ => Real.exp_pos _) (by unfold b; positivity) (by unfold b; rw [Finset.mul_sum])
  simp only [Real.log_exp, b, inv_mul_eq_div, ← Finset.sum_div] at he
  rw [mul_comm, ← le_div_iff₀ hm']
  exact (Real.le_log_iff_exp_le (by positivity)).mp he

variable {i j k : ℕ} (S : Finset (Cell i j k)) (e : Fin S.card ≃ S)

-- 读法：`rCount` 的取值由 `(rows S (e a).val).card` 给出。
def rCount (a : Fin S.card) := (rows S (e a).val).card
-- 读法：`cCount` 的取值由 `(cols S (e a).val).card` 给出。
def cCount (a : Fin S.card) := (cols S (e a).val).card
-- 读法：`kCount` 的取值由 `(inner S (e a).val).card` 给出。
def kCount (a : Fin S.card) := (inner S (e a).val).card

-- 读法：`0` 严格小于 `rCount S e a`。
theorem rCount_pos (a) : 0 < rCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

-- 读法：`0` 严格小于 `cCount S e a`。
theorem cCount_pos (a) : 0 < cCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

-- 读法：`0` 严格小于 `kCount S e a`。
theorem kCount_pos (a) : 0 < kCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

-- 读法：`weight` 的取值由 `unitWeight s (rCount S e a) (cCount S e a) (kCount S e a)` 给出。
def weight (s : ℝ) (a : Fin S.card) := unitWeight s (rCount S e a) (cCount S e a) (kCount S e a)

-- 读法：`S.card * Real.exp (s * conditional S)` 不超过 `∑ a, weight S e s a`。
theorem exp_conditional (h : S.Nonempty) (s : ℝ) :
    S.card * Real.exp (s * conditional S) ≤ ∑ a, weight S e s a := by
  let f (t : Cell i j k) := Real.log (rows S t).card + Real.log (cols S t).card +
    Real.log (inner S t).card
  have he : ∑ a, s * f (e a).val = s * ∑ t ∈ S, f t := by
    rw [← Finset.mul_sum, e.sum_comp (fun t => f t.val), Finset.sum_coe_sort]
  have hp := sum_exp_lower h.card_pos (fun a => s * f (e a).val)
  rw [he, mul_div_assoc] at hp
  exact hp

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-!
# 以一组输出单元为支撑的权重及其各次幂

**英文原文**

Powers of a weighting supported on a set of output cells
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}
  {w : Fin i → Fin j → Fin k → F} {u : Finset (Pos i j)}

-- 读法：`supportSize w` 等于 `u.card * k`。按 `(x, y) ∈ u` 成立与否分情况。
private theorem size_cells (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) :
    supportSize w = u.card * k := by
  classical
  have he x y z : (if w x y z = 0 then 0 else 1) = (if (x, y) ∈ u then 1 else 0 : ℕ) := by
    by_cases h : (x, y) ∈ u
    · simp [h, (hw x y z).mpr h]
    · simp [h, not_ne_iff.mp (mt (hw x y z).mp h)]
  unfold supportSize
  simp_rw [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : Pos i j => k * if p ∈ u then 1 else 0)]
  simp [mul_ite]

-- 读法：存在 `v : Finset (Pos (i ^ n) (j ^ n))`，`v.card = u.card ^ n ∧ ∀ x y z, WPower w n x y z ≠ 0` 与 `(x, y) ∈ v` 等价。
theorem power_cells (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) (hk : 0 < k) (n : ℕ) :
    ∃ v : Finset (Pos (i ^ n) (j ^ n)), v.card = u.card ^ n ∧
      ∀ x y z, WPower w n x y z ≠ 0 ↔ (x, y) ∈ v := by
  classical
  let v : Finset (Pos (i ^ n) (j ^ n)) := Finset.univ.filter fun p =>
    ∀ l : Fin n, (finFunctionFinEquiv.symm p.1 l, finFunctionFinEquiv.symm p.2 l) ∈ u
  have hv x y z : WPower w n x y z ≠ 0 ↔ (x, y) ∈ v := by
    simp [WPower, v, Finset.prod_ne_zero_iff, hw]
  refine ⟨v, ?_, hv⟩
  have he := supportSize_power w n
  rw [size_cells hv, size_cells hw, mul_pow] at he
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hk n) he

-- 读法：`short (i ^ n) (j ^ n) (q ^ n)` 等于 `n * short i j q`。
theorem short_pow (i j q n : ℕ) : short (i ^ n) (j ^ n) (q ^ n) = n * short i j q := by
  unfold short
  simp only [Nat.cast_pow, Real.log_pow, mul_div_assoc, mul_min_of_nonneg _ _ (Nat.cast_nonneg n)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
