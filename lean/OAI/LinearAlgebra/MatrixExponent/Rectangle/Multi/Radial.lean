-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi.Count
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Root
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth

/-!
# 在次数单纯形中装入独立立方体

以分量非负且分量和至多为 `q` 的平移向量为各立方体编号。把各坐标的一元分级相加，只保留所有输入和输出的平移向量均相同的项。

**英文原文**

Packing independent cubes into a degree simplex

Index the cubes by nonnegative translation vectors with sum at most
`q`. Summing the one-variable grading over the coordinates keeps
only terms whose input and output translation vectors all agree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {ι : Type} [Fintype ι] (F : Type) [Field F] (m q : ℕ) (L : ι → ℕ)

-- 读法：在后续公式中，`blockFromCubes` 是 `Deg m q × (Fin m → Profile.leg L s)` 的缩写。
private abbrev blockFromCubes (s : Option ι) := Deg m q × (Fin m → Profile.leg L s)

-- 读法：`join` 的结果类型为 `leg m (fun i => (q + m) * L i) s`。
private def join (s : Option ι) (x : blockFromCubes m q L s) : leg m (fun i => (q + m) * L i) s := by
  refine ⟨fun l => x.1.val l * Profile.length L s + (x.2 l).val, ?_⟩
  have he : Profile.length (fun i => (q + m) * L i) s = (q + m) * Profile.length L s := by
    cases s <;> simp [Profile.length, mul_sum]
  rw [he, sum_add_distrib, ← sum_mul, add_mul]
  apply Nat.add_le_add (Nat.mul_le_mul_right _ x.1.property)
  simpa using sum_le_sum (s := univ) (fun l _ => (x.2 l).isLt.le)

-- 读法：`bigFromCubes` 的取值由 `entry F m (fun i => (q + m) * L i) (fun s => join m q L s (x s))` 给出。
private def bigFromCubes (x : ∀ s, blockFromCubes m q L s) :=
  entry F m (fun i => (q + m) * L i) (fun s => join m q L s (x s))

-- 读法：`score` 的结果类型为 `ℤ`。
private def score (l : Fin m) (s : Option ι) (p : blockFromCubes m q L s) : ℤ :=
  if s.isNone then -Profile.weight (p.1.val l) (Profile.length L s) (p.2 l).val (Fintype.card ι)
  else Profile.weight (p.1.val l) (Profile.length L s) (p.2 l).val 1

-- 读法：`gradingFromCubes` 的取值由 `∑ l, score m q L l s p` 给出。
private def gradingFromCubes (s : Option ι) (p : blockFromCubes m q L s) : ℤ := ∑ l, score m q L l s p

-- 读法：结论为 `0 ≤ ∑ s, gradingFromCubes m q L s (x s) ∧ ((∑ s, gradingFromCubes m q L s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1)`。
private theorem grading_ruleFromCubes (x : ∀ s, blockFromCubes m q L s) (hx : bigFromCubes F m q L x ≠ 0) :
    0 ≤ ∑ s, gradingFromCubes m q L s (x s) ∧
      ((∑ s, gradingFromCubes m q L s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1) := by
  have he : ∑ i, (join m q L (some i) (x (some i))).val = (join m q L none (x none)).val := by
    simpa [bigFromCubes, entry] using hx
  have hs (l : Fin m) : 0 ≤ ∑ s, score m q L l s (x s) ∧
      ((∑ s, score m q L l s (x s)) = 0 ↔ ∀ i, (x (some i)).1.val l = (x none).1.val l) := by
    have hh : ∑ i, ((x (some i)).1.val l * L i + ((x (some i)).2 l).val) =
        (x none).1.val l * (∑ i, L i) + ((x none).2 l).val := by
      simpa only [Finset.sum_apply, join, Profile.length] using congrFun he l
    have hw := Profile.weights (fun i => ((x (some i)).1.val l : ℤ)) (fun i => (L i : ℤ))
      (fun i => (((x (some i)).2 l).val : ℤ)) ((x none).1.val l) ((x none).2 l).val
      (fun _ => by positivity) (fun i => by exact_mod_cast ((x (some i)).2 l).isLt)
      (by exact_mod_cast hh)
    simpa [Fintype.sum_option, score, Profile.length] using hw
  unfold gradingFromCubes
  rw [sum_comm]
  refine ⟨sum_nonneg (fun l _ => (hs l).1), ?_⟩
  simp only [sum_eq_zero_iff_of_nonneg (fun l _ => (hs l).1), mem_univ, forall_true_left, (hs _).2]
  exact ⟨fun h i => Subtype.ext (funext fun l => h l i), fun h l i => by rw [h i]⟩

open Classical in
-- 读法：`bigFromCubes F m q L x` 等于 `copyTable (Profile.entry F L) m (fun s => (x s).2)`。
private theorem aligned (x : ∀ s, blockFromCubes m q L s)
    (h : ∀ i, (x (some i)).1 = (x none).1) :
    bigFromCubes F m q L x = copyTable (Profile.entry F L) m (fun s => (x s).2) := by
  unfold bigFromCubes entry copyTable Profile.entry
  rw [Fintype.prod_ite_zero, prod_const_one]
  congr 1
  apply propext
  rw [funext_iff]
  simp only [Finset.sum_apply, join, Profile.length, h, sum_add_distrib, ← mul_sum, add_right_inj]

-- 读法：`Profile.array (Profile.grade (gradingFromCubes m q L) (bigFromCubes F m q L))` 等于 `(Fintype.card (Deg m q) : Tensor F (Option ι)) * Profile.polynomial F L ^ m`。这里调用 `Profile.grade_labels`。
private theorem table_cubes :
    Profile.array (Profile.grade (gradingFromCubes m q L) (bigFromCubes F m q L)) =
      (Fintype.card (Deg m q) : Tensor F (Option ι)) * Profile.polynomial F L ^ m := by
  rw [Profile.polynomial, ← table_pow]
  exact Profile.grade_labels (gradingFromCubes m q L) (bigFromCubes F m q L) (copyTable (Profile.entry F L) m)
    (fun x hx => (grading_ruleFromCubes F m q L x hx).2) (aligned F m q L)

-- 读法：`((q : ℝ) * f (Profile.polynomial F L)) ^ m` 不超过 `m.factorial * (f (simplex F m (fun i => (q + m) * L i)) : ℝ)`。这里调用 `Raw.coeff_ofTable`。
theorem cubes_le [Infinite F] [DecidableEq ι] (f : Tensor F (Option ι) →+* NNReal) (hf : Monotone f) :
    ((q : ℝ) * f (Profile.polynomial F L)) ^ m ≤
      m.factorial * (f (simplex F m (fun i => (q + m) * L i)) : ℝ) := by
  have hb : Profile.array (bigFromCubes F m q L) ≤ simplex F m (fun i => (q + m) * L i) := by
    refine Raw.Restricts.pullback (join m q L) fun x => ?_
    change (∀ s, blockFromCubes m q L s) at x
    exact (Raw.coeff_ofTable _ _ x).trans
      (Raw.coeff_ofTable _ (entry F m (fun i => (q + m) * L i)) (fun s => join m q L s (x s))).symm
  have h := Profile.grade_price f hf (bigFromCubes F m q L) (gradingFromCubes m q L)
    (fun x hx => (grading_ruleFromCubes F m q L x hx).1)
  rw [table_cubes, map_mul, map_natCast, map_pow] at h
  have he := NNReal.coe_le_coe.mpr (h.trans (hf hb))
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow] at he
  have hc : (q : ℝ) ^ m ≤ m.factorial * (Fintype.card (Deg m q) : ℝ) := by exact_mod_cast count_lower m q
  rw [mul_pow]
  refine (mul_le_mul_of_nonneg_right hc (by positivity)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left he (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# 在立方体中装入有序单纯形

为累积次数加上严格递增的偏移后，每种坐标次序各对应一个副本。按变差分级可除去次序混合的项。

**英文原文**

Packing ordered simplices into a cube

Cumulative degrees with strictly increasing offsets give one copy for
each coordinate ordering. The variation grading removes mixed orders.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {m : ℕ} {ι : Type} [Fintype ι]

-- 读法：`cum` 的取值由 `∑ u ∈ Iic t, x u` 给出。
private def cum (x : Fin m → ℕ) (t : Fin m) := ∑ u ∈ Iic t, x u

-- 读法：`(cum (m := m))` 是单射。用函数外延性比较等号两侧在 `t` 处的取值。
private theorem cum_inj : Function.Injective (cum (m := m)) := by
  intro x y h
  funext t
  induction t using WellFoundedLT.induction with
  | ind t ih =>
    have he := congrFun h t
    have h' : ∑ u ∈ Iio t, x u = ∑ u ∈ Iio t, y u := sum_congr rfl fun u hu => ih u (mem_Iio.mp hu)
    simpa [cum, ← Iio_insert, h'] using he

-- 读法：`cum (∑ i, x i) t` 等于 `∑ i, cum (x i) t`。这里调用 `sum_comm`。
private theorem cum_sum (x : ι → Fin m → ℕ) (t : Fin m) :
    cum (∑ i, x i) t = ∑ i, cum (x i) t := by
  simp only [cum, Finset.sum_apply]
  exact sum_comm

-- 读法：`shifted` 的取值由 `cum x t + d * t.val` 给出。
private def shifted (x : Fin m → ℕ) (d : ℕ) (t : Fin m) := cum x t + d * t.val

-- 读法：`(shifted x d)` 是严格单调递增的。这里调用 `add_lt_add_of_le_of_lt`。
private theorem shifted_mono (x : Fin m → ℕ) {d : ℕ} (hd : 0 < d) : StrictMono (shifted x d) := by
  intro u v huv
  exact add_lt_add_of_le_of_lt (sum_le_sum_of_subset (Iic_subset_Iic.mpr huv.le))
    (Nat.mul_lt_mul_of_pos_left huv hd)

variable (m) (L : ι → ℕ)

-- 读法：在后续公式中，`blockFromOrdered` 是 `Equiv.Perm (Fin m) × leg m L s` 的缩写。
private abbrev blockFromOrdered (s : Option ι) := Equiv.Perm (Fin m) × leg m L s

-- 读法：逐一匹配以下输入模式：`none`、`some _`。
private def offset : Option ι → ℕ
  | none => Fintype.card ι
  | some _ => 1

-- 读法：`0` 严格小于 `offset s`。
private theorem offset_pos [Nonempty ι] (s : Option ι) : 0 < offset s := by
  cases s <;> simp [offset, Fintype.card_pos]

-- 读法：`degreeFromOrdered` 的取值由 `shifted x.2.val (offset s) (x.1 t)` 给出。
private def degreeFromOrdered (s : Option ι) (x : blockFromOrdered m L s) (t : Fin m) :=
  shifted x.2.val (offset s) (x.1 t)

-- 读法：`embed` 的结果类型为 `Profile.leg (fun i => L i + m) s`。
private def embed [Nonempty ι] (s : Option ι) (x : blockFromOrdered m L s) (t : Fin m) :
    Profile.leg (fun i => L i + m) s := by
  refine ⟨degreeFromOrdered m L s x t, ?_⟩
  rw [show Profile.length (fun i => L i + m) s = Profile.length L s + offset s * m by
    cases s <;> simp [Profile.length, offset, sum_add_distrib]]
  exact add_lt_add_of_le_of_lt ((sum_le_sum_of_subset (subset_univ _)).trans x.2.property)
    (Nat.mul_lt_mul_of_pos_left (x.1 t).isLt (offset_pos s))

-- 读法：这里调用 `cum_inj`。
private theorem agree (x : ∀ s, blockFromOrdered m L s) (hp : ∀ i, (x (some i)).1 = (x none).1) :
    (∀ t, ∑ i, degreeFromOrdered m L (some i) (x (some i)) t = degreeFromOrdered m L none (x none) t) ↔
      ∑ i, (x (some i)).2.val = (x none).2.val := by
  simp only [degreeFromOrdered, shifted, hp, offset, one_mul, sum_add_distrib, sum_const, card_univ,
    smul_eq_mul, add_left_inj, ← cum_sum]
  constructor
  · intro h
    apply cum_inj
    funext t
    simpa using h ((x none).1.symm t)
  · intro h t
    rw [h]

variable (F : Type) [Field F] [Nonempty ι]

-- 读法：`bigFromOrdered` 的取值由 `if ∀ t, ∑ i, degreeFromOrdered m L (some i) (x (some i)) t = degreeFromOrdered m L none (x none) t then (1 : F) else 0` 给出。
private def bigFromOrdered (x : ∀ s, blockFromOrdered m L s) :=
  if ∀ t, ∑ i, degreeFromOrdered m L (some i) (x (some i)) t = degreeFromOrdered m L none (x none) t
    then (1 : F) else 0

-- 读法：`gradingFromOrdered` 的取值由 `let w := variation (fun t => degreeFromOrdered m L s x t) if s.isNone then -w else w` 给出。
private def gradingFromOrdered (s : Option ι) (x : blockFromOrdered m L s) :=
  let w := variation (fun t => degreeFromOrdered m L s x t)
  if s.isNone then -w else w

-- 读法：结论为 `0 ≤ ∑ s, gradingFromOrdered m L s (x s) ∧ ((∑ s, gradingFromOrdered m L s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1)`。
private theorem grading_ruleFromOrdered (x : ∀ s, blockFromOrdered m L s) (hx : bigFromOrdered m L F x ≠ 0) :
    0 ≤ ∑ s, gradingFromOrdered m L s (x s) ∧
      ((∑ s, gradingFromOrdered m L s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1) := by
  have he : ∀ t, ∑ i, degreeFromOrdered m L (some i) (x (some i)) t = degreeFromOrdered m L none (x none) t := by
    simpa [bigFromOrdered] using hx
  let d (s) (t) : ℤ := degreeFromOrdered m L s (x s) t
  have hd s u v : d s u < d s v ↔ (x s).1 u < (x s).1 v := by
    simp only [d, Nat.cast_lt, degreeFromOrdered, (shifted_mono _ (offset_pos s)).lt_iff_lt]
  have hw := variation_rule (fun s => (x s).1) d hd (fun t => by
    unfold d; exact_mod_cast he t)
  simpa [Fintype.sum_option, gradingFromOrdered, d, neg_add_eq_zero, le_add_iff_nonneg_left] using hw

-- 读法：`Profile.array (bigFromOrdered m L F)` 不超过 `(Profile.polynomial F (fun i => L i + m)) ^ m`。
private theorem big_le : Profile.array (bigFromOrdered m L F) ≤ (Profile.polynomial F (fun i => L i + m)) ^ m := by
  rw [Profile.polynomial, ← table_pow]
  refine Raw.Restricts.pullback (embed m L) fun x => ?_
  change (∀ s, blockFromOrdered m L s) at x
  erw [Raw.coeff_ofTable, Raw.coeff_ofTable]
  unfold copyTable Profile.entry
  rw [Fintype.prod_ite_zero, prod_const_one]
  unfold bigFromOrdered
  congr

-- 读法：`Profile.array (Profile.grade (gradingFromOrdered m L) (bigFromOrdered m L F))` 等于 `(m.factorial : Tensor F (Option ι)) * simplex F m L`。
private theorem graded_simplex :
    Profile.array (Profile.grade (gradingFromOrdered m L) (bigFromOrdered m L F)) =
      (m.factorial : Tensor F (Option ι)) * simplex F m L := by
  have he := Profile.grade_labels (gradingFromOrdered m L) (bigFromOrdered m L F) (entry F m L)
    (fun x hx => (grading_ruleFromOrdered m L F x hx).2) (by
      intro x hp
      simp only [bigFromOrdered, entry, agree m L x hp])
  rw [Fintype.card_perm, Fintype.card_fin] at he
  exact he

variable {F m}

-- 读法：`m.factorial * f (simplex F m L)` 不超过 `f (Profile.polynomial F (fun i => L i + m)) ^ m`。这里调用 `h.trans`。
/-- `m!` 种排序各自在零次分量上贡献一个单纯形，各个单纯形互不相交。

英文原文：Each of the `m!` orderings contributes a disjoint simplex at grade zero.
-/
theorem simplex_le [Infinite F] [DecidableEq ι] (L : ι → ℕ)
    (f : Tensor F (Option ι) →+* NNReal) (hf : Monotone f) :
    m.factorial * f (simplex F m L) ≤ f (Profile.polynomial F (fun i => L i + m)) ^ m := by
  have h := Profile.grade_price f hf (bigFromOrdered m L F) (gradingFromOrdered m L)
    (fun x hx => (grading_ruleFromOrdered m L F x hx).1)
  rw [graded_simplex, map_mul, map_natCast] at h
  rw [← map_pow]
  exact h.trans (hf (big_le m L F))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# 独立的多项式变量组

**英文原文**

Independent groups of polynomial variables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Finset

variable {ι : Type} [Fintype ι] (K : Type) [Field K]

-- 读法：`simplex K m L` 不等于 `0`。
theorem simplex_ne_zero (m : ℕ) (L : ι → ℕ) : simplex K m L ≠ 0 := by
  intro h
  let x (s : Option ι) : leg m L s := ⟨0, by simp⟩
  have he := (Tensor.ofRaw_eq_zero _).mp h x
  rw [Raw.coeff_ofTable] at he
  simp [entry, x] at he

-- 读法：`0` 严格小于 `(f (simplex K m L) : ℝ)`。
theorem simplex_pos (m : ℕ) (L : ι → ℕ) (f : Tensor K (Option ι) →+* NNReal) (hf : Monotone f) :
    0 < (f (simplex K m L) : ℝ) := by
  have hh := hf (Tensor.one_le _ (simplex_ne_zero K m L))
  rw [map_one] at hh
  exact_mod_cast zero_lt_one.trans_le hh

-- 读法：`concat` 的结果类型为 `leg (n * m) (fun i => n * L i) s`。
private def concat (n m : ℕ) (L : ι → ℕ) (s : Option ι) (x : Fin n → leg m L s) :
    leg (n * m) (fun i => n * L i) s := by
  refine ⟨fun i => (x (finProdFinEquiv.symm i).1).val (finProdFinEquiv.symm i).2, ?_⟩
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  have h := sum_le_sum (s := univ) (fun i _ => (x i).property)
  have he : Profile.length (fun i => n * L i) s = n * Profile.length L s := by
    cases s <;> simp [Profile.length, mul_sum]
  simpa [he] using h

-- 读法：`(simplex K m L) ^ n` 不超过 `simplex K (n * m) (fun i => n * L i)`。
theorem simplex_pow (m n : ℕ) (L : ι → ℕ) :
    (simplex K m L) ^ n ≤ simplex K (n * m) (fun i => n * L i) := by
  classical
  unfold simplex
  rw [← table_pow]
  refine Raw.Restricts.pullback (concat n m L) fun x => ?_
  change (∀ s, Fin n → leg m L s) at x
  erw [Raw.coeff_ofTable, Raw.coeff_ofTable]
  unfold copyTable entry
  rw [Fintype.prod_ite_zero, prod_const_one]
  congr 1
  apply propext
  simp only [funext_iff, Finset.sum_apply, concat]
  constructor
  · intro h i; exact h _ _
  · intro h i j
    simpa only [Equiv.symm_apply_apply] using h (finProdFinEquiv (i, j))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# 次数能量及其在小开销下的上界

对 `m` 个变量使用总次数预算。通过一个公共松弛变量将各个输入和输出齐次化，同时保持张量不变。按次序作退化可直接给出上界，而且该界对变量数一致。

**英文原文**

Degree energy and its upper bound at small costs

Use total-degree budgets in `m` variables. A common slack variable
homogenizes each input and the output without changing the tensor.
The ordering degeneration gives the upper bound directly, uniformly
in the number of variables.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Energy Set Finset
open scoped Topology

variable {ι K : Type} [Fintype ι] [Field K]

-- 读法：`penalty` 的取值由 `∑ i, s i * L i` 给出。
def penalty (s : ι → ℝ) (L : ι → ℕ) := ∑ i, s i * L i

-- 读法：`scores` 的取值由 `{a | ∃ m : ℕ, 0 < m ∧ ∃ L, a = (H m L - penalty s L) / m}` 给出。
def scores (H : ℕ → (ι → ℕ) → ℝ) (s : ι → ℝ) : Set ℝ :=
  {a | ∃ m : ℕ, 0 < m ∧ ∃ L, a = (H m L - penalty s L) / m}

-- 读法：`degree` 的取值由 `sSup (scores H s)` 给出。
def degree (H : ℕ → (ι → ℕ) → ℝ) (s : ι → ℝ) := sSup (scores H s)

-- 读法：要证明的命题是 `(scores H s).Nonempty`。
theorem scores_nonempty (H : ℕ → (ι → ℕ) → ℝ) (s : ι → ℝ) : (scores H s).Nonempty :=
  ⟨_, 1, by decide, 0, rfl⟩

variable [Nonempty ι] [DecidableEq ι] [Infinite K]

-- 读法：`degrees` 的取值由 `d * Real.log (f (simplex K m L))` 给出。
def degrees (f : Tensor K (Option ι) →+* NNReal) (d : ℝ) (m : ℕ) (L : ι → ℕ) :=
  d * Real.log (f (simplex K m L))

-- 读法：`widths` 的取值由 `d * Real.log (Profile.profile f x)` 给出。
def widths (f : Tensor K (Option ι) →+* NNReal) (d : ℝ) (x : ι → ℝ) :=
  d * Real.log (Profile.profile f x)

variable {f : Tensor K (Option ι) →+* NNReal} (hf : Monotone f) {d N : ℝ}
    (hd : 0 < d) {s : ι → ℝ} (hs : ∀ i, 0 < s i)
include hf hd hs

-- 读法：`d + widths f d x - cost s x` 不超过 `variational (widths f d) d s`。这里调用 `sum_le_sum`。
theorem widths_le {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    d + widths f d x - cost s x ≤ variational (widths f d) d s := by
  refine le_csSup ?_ ⟨x, hx, rfl⟩
  obtain ⟨j, _, hm⟩ := Finset.exists_min_image univ s univ_nonempty
  refine ⟨d * Real.log (d / s j), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hc : s j * ∑ i, y i ≤ cost s y := by
    rw [cost, Finset.mul_sum]
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hm _ (mem_univ i)) (hy i).le)
  have hp : 0 < ∑ i, y i := sum_pos (fun i _ => hy i) univ_nonempty
  have hh := Real.log_le_log (Profile.profile_pos hf hy) ((Profile.scaling_polynomial f hf).scale_bound hy)
  change d + d * Real.log (Profile.profile f y) - _ ≤ _
  linarith only [hc, mul_le_mul_of_nonneg_left hh hd.le, log_max hd (hs j) hp]

-- 读法：`d * Real.log N + variational (widths f d) d s + 2 * (∑ i, s i) / N` 属于 `upperBounds (scores (degrees f d) (fun i => s i / N))`。
theorem scores_upper (hN : 0 < N) :
    d * Real.log N + variational (widths f d) d s + 2 * (∑ i, s i) / N ∈
      upperBounds (scores (degrees f d) (fun i => s i / N)) := by
  rintro _ ⟨m, hm, L, rfl⟩
  have hm' : 0 < (m : ℝ) := by positivity
  let M := fun i => L i + m
  let x := fun i => ((L i : ℝ) + 2 * m) / (m * N)
  have hx (i) : 0 < x i := by unfold x; positivity
  let y := Profile.profile f x
  have hy : 0 < y := Profile.profile_pos hf hx
  -- 推导：记下中间结论 `hscale`：`(f (Profile.polynomial K M) : ℝ) ≤ (m * N) * y`。
  have hscale : (f (Profile.polynomial K M) : ℝ) ≤ (m * N) * y := by
    apply (inv_mul_le_iff₀ (mul_pos hm' hN)).mp
    apply (Profile.scaling_polynomial f hf).le_scale (by positivity)
    intro i
    unfold x M
    rw [inv_mul_eq_div, Nat.cast_add, div_lt_div_iff_of_pos_right (mul_pos hm' hN)]
    linarith
  have ht := simplex_le (m := m) L f hf
  have hfac : 0 < (m.factorial : ℝ) := by positivity
  have hp := simplex_pos K m L f hf
  -- 推导：记下中间结论 `hh`：`(m.factorial : ℝ) * f (simplex K m L) ≤ ((m * N) * y) ^ m`。
  have hh : (m.factorial : ℝ) * f (simplex K m L) ≤ ((m * N) * y) ^ m := by
    refine le_trans ?_ (pow_le_pow_left₀ (by positivity) hscale _)
    exact_mod_cast ht
  have he := Real.log_le_log (mul_pos hfac hp) hh
  rw [Real.log_mul hfac.ne' hp.ne', Real.log_pow, Real.log_mul (by positivity) hy.ne',
    Real.log_mul hm'.ne' hN.ne'] at he
  have hc : Real.log m - Real.log m.factorial / m ≤ 1 := correction_le m
  have hv : degrees f d m L / m ≤ d * (Real.log N + Real.log y + 1) := by
    unfold degrees
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hd.le
    have hh := (div_le_iff₀ hm').mpr (he.trans_eq (mul_comm _ _))
    rw [add_div] at hh
    linarith only [hh, hc]
  -- 推导：记下中间结论 `hpen`：`penalty (fun i => s i / N) L / m + 2 * (∑ i, s i) / N = cost s x`。
  have hpen : penalty (fun i => s i / N) L / m + 2 * (∑ i, s i) / N = cost s x := by
    unfold penalty cost x
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hu := widths_le hf hd hs hx
  change d + d * Real.log y - cost s x ≤ _ at hu
  rw [sub_div]
  linarith only [hu, hpen, hv]

-- 读法：要证明的命题是 `BddAbove (scores (degrees f d) s)`。
theorem bounded_scores : BddAbove (scores (degrees f d) s) := by
  have hh := scores_upper hf hd hs zero_lt_one
  simp only [div_one] at hh
  exact ⟨_, hh⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-!
# 次数能量的连续极限

在一元上确界的定义中固定一种立方体形状，再将其平移副本装入一个多元单纯形。各宽度中留出的严格余量足以支付对平移副本数取整的代价。

**英文原文**

The continuum limit of degree energy

Fix a cube shape in the univariate supremum, then pack translated
copies inside a multivariate simplex. The strict slack in each
width pays for rounding the number of translates.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Energy Filter Set
open scoped Topology

variable {ι K : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field K] [Infinite K]
    {f : Tensor K (Option ι) →+* NNReal} (hf : Monotone f)
    {d : ℝ} (hd : 0 < d) {s : ι → ℝ} (hs : ∀ i, 0 < s i)

include hf hd hs in
-- 读法：对每个 `ᶠ N : ℝ in atTop`，`d * (Real.log (c * f (Profile.polynomial K L)) + correction m) - cost s x` 不超过 `degree (degrees f d) (fun i => s i / N) - d * Real.log N`。这里调用 `eventually_all.mpr`。
private theorem lower_cube {x : ι → ℝ} {c : ℝ} {L : ι → ℕ}
    (hc : 0 < c) (hc' : 0 < c * f (Profile.polynomial K L))
    (hx : ∀ i, c * L i < x i) {m : ℕ} (hm : 0 < m) :
    ∀ᶠ N : ℝ in atTop,
      d * (Real.log (c * f (Profile.polynomial K L)) + correction m) - cost s x ≤
        degree (degrees f d) (fun i => s i / N) - d * Real.log N := by
  have hm' : 0 < (m : ℝ) := by positivity
  let q (N : ℝ) := ⌈m * N * c⌉₊
  have hlarge : ∀ᶠ N : ℝ in atTop, ∀ i, ((q N : ℝ) + m) * L i ≤ (m * N) * x i := by
    apply eventually_all.mpr
    intro i
    have hi := sub_pos.mpr (hx i)
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (((1 + m) * L i) / (m * (x i - c * L i)))]
      with N hN hN'
    -- 推导：记下中间结论 `hq`：`(q N : ℝ) ≤ m * N * c + 1`。
    have hq : (q N : ℝ) ≤ m * N * c + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    linarith only [mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (L i)),
      (div_le_iff₀ (mul_pos hm' hi)).mp hN']
  filter_upwards [eventually_gt_atTop 0, hlarge] with N hN hsize
  let A := fun i => (q N + m) * L i
  let y := c * (f (Profile.polynomial K L) : ℝ)
  have hy : 0 < y := hc'
  have hw : ((m * N) * y) ^ m ≤ m.factorial * (f (simplex K m A) : ℝ) := by
    refine le_trans ?_ (cubes_le K m (q N) L f hf)
    apply pow_le_pow_left₀ (by positivity)
    unfold y
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have hv := Real.log_le_log (by positivity) hw
  rw [Real.log_pow, Real.log_mul (by positivity) hy.ne', Real.log_mul hm'.ne' hN.ne',
    Real.log_mul (by positivity) (simplex_pos K m A f hf).ne'] at hv
  -- 推导：记下中间结论 `he`：`d * (Real.log N + Real.log y + correction m) ≤ degrees f d m A / m`。
  have he : d * (Real.log N + Real.log y + correction m) ≤ degrees f d m A / m := by
    rw [degrees, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hd.le
    have he := (le_div_iff₀ hm').mpr ((mul_comm _ _).trans_le hv)
    rw [add_div] at he
    unfold correction
    linarith only [he]
  have hcost : penalty (fun i => s i / N) A / m ≤ cost s x := by
    unfold penalty cost
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    change s i / N * ((q N + m) * L i : ℕ) / m ≤ _
    rw [Nat.cast_mul, Nat.cast_add, div_mul_eq_mul_div, div_div, div_le_iff₀ (mul_pos hN hm')]
    linarith only [mul_le_mul_of_nonneg_left (hsize i) (hs i).le]
  -- 推导：记下中间结论 `hb`：`= bounded_scores hf hd (s`。
  have hb := bounded_scores hf hd (s := fun i => s i / N) (fun i => div_pos (hs i) hN)
  have hh : (degrees f d m A - penalty (fun i => s i / N) A) / m ≤
      degree (degrees f d) (fun i => s i / N) := le_csSup hb ⟨m, hm, A, rfl⟩
  rw [sub_div] at hh
  change d * (Real.log y + correction m) - _ ≤ _
  linarith only [he, hcost, hh]

include hf hd hs in
-- 读法：`(fun N : ℝ => degree (degrees f d) (fun i => s i / N) - d * Real.log N)` 沿滤子 `atTop` 收敛到 `(variational (widths f d) d s)`。这里调用 `tendsto_order.mpr`。
theorem degree_limit :
    Tendsto (fun N : ℝ => degree (degrees f d) (fun i => s i / N) - d * Real.log N) atTop
      (𝓝 (variational (widths f d) d s)) := by
  apply tendsto_order.mpr
  constructor
  · intro t ht
    obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := exists_lt_of_lt_csSup
      (show ((fun x => d + widths f d x - cost s x) '' {x | ∀ i, 0 < x i}).Nonempty from
        ⟨_, fun _ => 1, fun _ => zero_lt_one, rfl⟩) ht
    have hc : Tendsto (fun m => d * (Real.log (Profile.profile f x) + correction m) - cost s x)
        atTop (𝓝 (d + widths f d x - cost s x)) := by
      convert ((correction_limit.const_add _).const_mul d).sub_const (cost s x) using 1
      unfold widths
      ring_nf
    -- 推导：从 `((eventually_gt_atTop 0).and (hc.eventually_const_lt hx')).exists` 中取出 `m, hm, hval`。
    obtain ⟨m, hm, hval⟩ := ((eventually_gt_atTop 0).and (hc.eventually_const_lt hx')).exists
    let y := (t + cost s x) / d - correction m
    have hy : Real.exp y < Profile.profile f x := by
      apply (Real.lt_log_iff_exp_lt (Profile.profile_pos hf hx)).mp
      unfold y
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]
      linarith only [hval]
    unfold Profile.profile Profile.scale at hy
    obtain ⟨_, ⟨L, c, hc', hL, rfl⟩, hhigh⟩ :=
      exists_lt_of_lt_csSup (by exact ⟨_, 0, 1, zero_lt_one, by simpa using hx, rfl⟩) hy
    have h' := (Real.exp_pos _).trans hhigh
    have hh := (Real.lt_log_iff_exp_lt h').mpr hhigh
    unfold y at hh
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd] at hh
    filter_upwards [lower_cube hf hd hs hc' h' hL hm] with N hN
    linarith only [hh, hN]
  · intro t ht
    -- 推导：记下中间结论 `hc`：`Tendsto (fun N : ℝ => 2 * (∑ i, s i) / N) atTop (𝓝 0)`。
    have hc : Tendsto (fun N : ℝ => 2 * (∑ i, s i) / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [eventually_gt_atTop 0, hc.eventually_lt_const (sub_pos.mpr ht)] with N hN hN'
    have he := csSup_le (scores_nonempty _ _) (scores_upper hf hd hs hN)
    unfold degree
    linarith only [he, hN']

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# 固定有限配置中的次数能量与宽度能量

**英文原文**

Degree and width energy at a fixed finite placement
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral Filter
open scoped Topology

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X) (x : ι → X)

-- 读法：`H A o x` 等于 `degrees (Profile.point A (sites o x)) (A.price (sites o x) 2)`。用函数外延性比较等号两侧在 `m L` 处的取值。
theorem H_eq : H A o x = degrees (Profile.point A (sites o x)) (A.price (sites o x) 2) := by
  funext m L
  exact Profile.price_eq A _ _

-- 读法：`n * H A o x m L` 不超过 `H A o x (n * m) (fun i => n * L i)`。
theorem H_pow (n m : ℕ) (L : ι → ℕ) :
    n * H A o x m L ≤ H A o x (n * m) (fun i => n * L i) := by
  let f := Profile.point A (sites o x)
  have hf := Profile.point_mono A (sites o x)
  have h := hf (simplex_pow K m n L)
  rw [map_pow] at h
  have hp : (f (simplex K m L) : ℝ) ^ n ≤ f (simplex K (n * m) (fun i => n * L i)) := by
    exact_mod_cast h
  have h' := Real.log_le_log (pow_pos (simplex_pos K m L f hf) _) hp
  rw [Real.log_pow] at h'
  rw [H_eq, degrees, degrees, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h' (A.nonnegative _ _)

-- 读法：`Q` 的取值由 `let d := A.price (sites o x) 2 Energy.variational (widths (Profile.point A (sites o x)) d) d s` 给出。
def Q (s : ι → ℝ) :=
  let d := A.price (sites o x) 2
  Energy.variational (widths (Profile.point A (sites o x)) d) d s

-- 读法：要证明的命题是 `Tendsto (fun N : ℝ => degree (H A o x) (fun i => s i / N) - A.price (sites o x) 2 * Real.log N) atTop (𝓝 (Q A o x s))`。这里调用 `degree_limit`。
theorem H_limit [Infinite K] (hd : 0 < A.price (sites o x) 2)
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) :
    Tendsto (fun N : ℝ => degree (H A o x) (fun i => s i / N) - A.price (sites o x) 2 * Real.log N)
      atTop (𝓝 (Q A o x s)) := by
  rw [H_eq]
  exact degree_limit (Profile.point_mono A _) hd hs

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-!
# 两组变量的代换具有递增收益

对两个测试乘积分别作张量积，使它们使用相同的变量数。扇区展开只损失对数成本，继续对二者共同取幂后，这项损失便消失。

**英文原文**

Increasing returns from substitution in two groups of variables

Tensor the two test products up to the same number of variables. The
sector expansion loses only a logarithmic cost, which disappears under
further joint powering.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Finset

variable {ι : Type} [Fintype ι] {H : ℕ → (ι → ℕ) → ℝ}
    {f : ι → ℝ} {s a b C : ℝ} {L R : ι → ℕ}

-- 读法：`penalty f (fun i => n * L i)` 等于 `n * penalty f L`。这里调用 `sum_congr`。
theorem penalty_mul (f : ι → ℝ) (L : ι → ℕ) (n : ℕ) :
    penalty f (fun i => n * L i) = n * penalty f L := by
  simp only [penalty, Nat.cast_mul, mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

-- 读法：`penalty f L + penalty (fun i => f i + s) R` 等于 `penalty f (L + R) + s * (∑ i, R i : ℕ)`。这里调用 `sum_congr`。
private theorem penalty_add (L R : ι → ℕ) (f : ι → ℝ) (s : ℝ) :
    penalty f L + penalty (fun i => f i + s) R = penalty f (L + R) + s * (∑ i, R i : ℕ) := by
  simp only [penalty, Pi.add_apply, Nat.cast_add, Nat.cast_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

-- 读法：`A` 不超过 `B`。这里调用 `Real.exp_le_exp.mp`。
private theorem absorb_log {A B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, 0 < n → n * A ≤ n * B + C * Real.log (1 + n * D)) : A ≤ B := by
  apply Real.exp_le_exp.mp
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ ((1 + D) ^ C) C
    (by positivity) (by positivity) (by positivity) hC
  intro n hn
  rw [← Real.mul_rpow (by positivity) (by positivity), Real.rpow_def_of_pos (by positivity),
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have he := Real.log_le_log (by positivity : 0 < 1 + (n : ℝ) * D)
    (show 1 + (n : ℝ) * D ≤ (1 + D) * (n + 1) by linarith)
  linarith only [h n hn, mul_le_mul_of_nonneg_left he hC]

-- 读法：`Sectors` 的结果类型为 `Prop`。
/-- 在次数扇区的数量为多项式级时比较对数价格。

英文原文：Log-price comparison with a polynomial number of degree sectors.
-/
def Sectors (H : ℕ → (ι → ℕ) → ℝ) (S : Finset ι) (C : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ L R : ι → ℕ, (∀ i ∈ S, L i = 0) →
    ∃ U V : ι → ℕ, U + V = L + R ∧ (∀ i ∈ S, V i = 0) ∧ (∑ i, V i) ≤ ∑ i, R i ∧
      H m L + H m R ≤ H m U + H m V + C * Real.log (1 + (∑ i, (L i + R i) : ℕ))

-- 读法：`(H m L - penalty f L) / m + (H n R - penalty (fun i => f i + s) R) / n` 不超过 `a + b`。这里调用 `absorb_log`。
theorem increase {S : Finset ι} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hpow : ∀ n m L, (n : ℕ) * H m L ≤ H (n * m) (fun i => n * L i))
    (hsec : Sectors H S C)
    (ha : ∀ m : ℕ, 0 < m → ∀ L, H m L - penalty f L ≤ m * a)
    (hb : ∀ m : ℕ, 0 < m → ∀ R, (∀ i ∈ S, R i = 0) → H m R - penalty (fun i => f i + s) R ≤ m * b)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hL : ∀ i ∈ S, L i = 0) :
    (H m L - penalty f L) / m + (H n R - penalty (fun i => f i + s) R) / n ≤ a + b := by
  let g i := f i + s
  have same (m : ℕ) (hm : 0 < m) (L R : ι → ℕ) (hL : ∀ i ∈ S, L i = 0) :
      H m L - penalty f L + (H m R - penalty g R) ≤ m * (a + b) := by
    apply absorb_log (D := (∑ i, (L i + R i) : ℕ)) hC (by positivity)
    intro t ht
    let U i := t * L i
    let V i := t * R i
    -- 推导：记下中间结论 `h₀`：`∀ i ∈ S, U i = 0`。
    have h₀ : ∀ i ∈ S, U i = 0 := by intro i hi; simp [U, hL i hi]
    obtain ⟨X, Y, he, hY, hv, hh⟩ := hsec (t * m) (Nat.mul_pos ht hm) U V h₀
    have hp : penalty f X + penalty g Y ≤ penalty f U + penalty g V := by
      unfold g
      rw [penalty_add, penalty_add, he]
      gcongr
    have hmass : ∑ i, (U i + V i) = t * ∑ i, (L i + R i) := by simp [U, V, mul_sum, mul_add]
    rw [hmass, Nat.cast_mul] at hh
    rw [show penalty f U = t * penalty f L from penalty_mul _ _ _,
      show penalty g V = t * penalty g R from penalty_mul _ _ _] at hp
    have ha' := ha (t * m) (Nat.mul_pos ht hm) X
    have hb' := hb (t * m) (Nat.mul_pos ht hm) Y hY
    rw [Nat.cast_mul] at ha' hb'
    -- 推导：记下中间结论 `hu`：`(t : ℝ) * H m L ≤ H (t * m) U`。
    have hu : (t : ℝ) * H m L ≤ H (t * m) U := hpow _ _ _
    have hv : (t : ℝ) * H m R ≤ H (t * m) V := hpow _ _ _
    change H (t * m) Y - penalty g Y ≤ _ at hb'
    linarith only [hh, hp, ha', hb', hu, hv]
  have he := same (n * m) (Nat.mul_pos hn hm) (fun i => n * L i) (fun i => m * R i)
    (by intro i hi; simp [hL i hi])
  have hr := hpow m n R
  rw [Nat.mul_comm m n] at hr
  rw [penalty_mul, penalty_mul, Nat.cast_mul] at he
  change _ + (H n R - penalty g R) / n ≤ a + b
  field_simp
  linarith only [he, hpow n m L, hr]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-!
# 处理多项式数量的双分次分区的开销

**英文原文**

The cost of a polynomial number of bidegree sectors
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Spectral

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X) (x : ι → X)

-- 读法：存在 `C : ℝ`，`0 ≤ C` 与 `Sectors (H A o x) S C` 同时成立。
theorem H_sectors (S : Finset ι) :
    ∃ C : ℝ, 0 ≤ C ∧ Sectors (H A o x) S C := by
  let d := A.price (sites o x) 2
  let f := Profile.point A (sites o x)
  have hf : Monotone f := Profile.point_mono A _
  have hd : 0 ≤ d := A.nonnegative _ _
  refine ⟨d * Fintype.card ι, by positivity, ?_⟩
  intro m _ L R hL
  obtain ⟨U, V, he, hv, ht, h⟩ := sector (m := m) L R S hL f hf
  refine ⟨U, V, he, hv, ht, ?_⟩
  let y (L : ι → ℕ) : ℝ := f (simplex K m L)
  let t : ℕ := 1 + ∑ i, (L i + R i)
  have hp L : 0 < y L := simplex_pos K m L f hf
  -- 推导：记下中间结论 `ht`：`0 < (t : ℝ)`。
  have ht : 0 < (t : ℝ) := by unfold t; positivity
  have he : y L * y R ≤ (t : ℝ) ^ Fintype.card ι * y U * y V := by
    exact_mod_cast h
  have hl := Real.log_le_log (mul_pos (hp _) (hp _)) he
  rw [Real.log_mul (hp _).ne' (hp _).ne', Real.log_mul (mul_pos (pow_pos ht _) (hp _)).ne'
    (hp _).ne', Real.log_mul (pow_pos ht _).ne' (hp _).ne', Real.log_pow] at hl
  rw [H_eq, ← Nat.cast_one (R := ℝ), ← Nat.cast_add]
  change d * Real.log (y L) + d * Real.log (y R) ≤ d * Real.log (y U) + d * Real.log (y V) +
    d * Fintype.card ι * Real.log t
  linarith only [mul_le_mul_of_nonneg_left hl hd]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

/-!
# 次数能量差的径向比较

在混合配置中，一项测试只用内侧输入，另一项只用外侧输入。由收益递增性质，可将它们与一项不受限制的测试及一项平移后的内侧测试比较。前者收缩到外侧站址，后者舍去次数为零的输入。

**英文原文**

Radial comparison of degree-energy differences

In the mixed placement one test uses only inner inputs and one uses
only outer inputs. Increasing returns compares these two tests to an
unrestricted test and a shifted inner test. The former contracts onto
the outer sites. The latter discards zero-degree inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Finset

variable {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X)

-- 读法：`H A o x m L - penalty f L` 不超过 `m * degree (H A o x) f`。这里调用 `bounded_scores`。
private theorem test_le_degree [Infinite K] (x : ι → X) (f : ι → ℝ)
    (hd : 0 < A.price (sites o x) 2) (hf : ∀ i, 0 < f i) (m : ℕ) (hm : 0 < m) (L : ι → ℕ) :
    H A o x m L - penalty f L ≤ m * degree (H A o x) f := by
  have hb : BddAbove (scores (H A o x) f) := by
    rw [H_eq]
    exact bounded_scores (Profile.point_mono _ _) hd hf
  rw [mul_comm, ← div_le_iff₀ (by positivity : (0 : ℝ) < m)]
  exact le_csSup hb ⟨m, hm, L, rfl⟩

-- 读法：`sSup s + sSup t` 不超过 `C`。这里调用 `csSup_le`。
private theorem add_sups {s t : Set ℝ} {C : ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (h : ∀ a ∈ s, ∀ b ∈ t, a + b ≤ C) : sSup s + sSup t ≤ C := by
  rw [← le_sub_iff_add_le]
  apply csSup_le hs
  intro a ha
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
  exact csSup_le ht (fun b hb => le_sub_iff_add_le'.mpr (h a ha b hb))

-- 读法：`degree (H A o y) g - degree (H A o y) (fun i => g i + s)` 不超过 `degree (H A o x) f - degree (H A o x) (fun i => f i + s)`。
theorem degree_contract [Infinite K] (x y : ι → X) (f g t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1)
    (h₁ : ∀ i, Dist.dist o (y i) = t i * Dist.dist o (x i))
    (h₂ : ∀ i, Dist.dist (y i) (x i) = (1 - t i) * Dist.dist o (x i))
    (hg : ∀ i, t i * f i ≤ g i) (hf₀ : ∀ i, 0 < f i) (hg₀ : ∀ i, 0 < g i)
    (hx : 0 < A.price (sites o x) 2) (hy : 0 < A.price (sites o y) 2) {s : ℝ} (hs : 0 ≤ s) :
    degree (H A o y) g - degree (H A o y) (fun i => g i + s) ≤
      degree (H A o x) f - degree (H A o x) (fun i => f i + s) := by
  let M := H A o (Sum.elim x y)
  let S : Finset (ι ⊕ ι) := univ.image Sum.inl
  -- 推导：从 `H_sectors A o (Sum.elim x y) S` 中取出 `C, hC, hsec`。
  obtain ⟨C, hC, hsec⟩ := H_sectors A o (Sum.elim x y) S
  have hpow := H_pow A o (Sum.elim x y)
  let c := Sum.elim f g
  let a := degree (H A o x) f
  let b := degree (H A o y) (fun i => g i + s)
  have ha (m : ℕ) (hm : 0 < m) (L : ι ⊕ ι → ℕ) : M m L - penalty c L ≤ m * a := by
    obtain ⟨R, hR⟩ := contract A o x y f g t ht ht' h₁ h₂ hg m L
    exact hR.trans (test_le_degree A o x f hx hf₀ m hm R)
  have hb (m : ℕ) (hm : 0 < m) (R : ι ⊕ ι → ℕ) (hR : ∀ i ∈ S, R i = 0) :
      M m R - penalty (fun i => c i + s) R ≤ m * b := by
    let V i := R (.inr i)
    -- 推导：记下中间结论 `he`：`R = Sum.elim (0 : ι → ℕ) V`。
    have he : R = Sum.elim (0 : ι → ℕ) V := by
      funext i
      rcases i with i | i
      · exact hR (.inl i) (by simp [S])
      · rfl
    rw [he, show M m (Sum.elim 0 V) = H A o y m V from right_H m V A o x y]
    have hh := test_le_degree A o y (fun i => g i + s) hy (fun i => add_pos_of_pos_of_nonneg (hg₀ i) hs) m hm V
    simpa [penalty, c, b, Fintype.sum_sum_type] using hh
  have he : degree (H A o y) g + degree (H A o x) (fun i => f i + s) ≤ a + b := by
    apply add_sups (scores_nonempty _ _) (scores_nonempty _ _)
    rintro _ ⟨m, hm, L, rfl⟩ _ ⟨n, hn, R, rfl⟩
    -- 推导：记下中间结论 `hL`：`∀ i ∈ S, Sum.elim (0 : ι → ℕ) L i = 0`。
    have hL : ∀ i ∈ S, Sum.elim (0 : ι → ℕ) L i = 0 := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      rfl
    have hh := increase hC hs hpow hsec ha hb (R := Sum.elim R 0) hm hn hL
    simpa [M, right_H, left_H, penalty, c, Fintype.sum_sum_type] using hh
  unfold a b at he
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end

section
/-!
# 有限配置中宽度能量的径向收缩

**英文原文**

Radial contraction of width energy at finite placements
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
open Filter
open scoped Topology

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K] [Infinite K]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (o : X)

-- 读法：`Q A o y g - Q A o y (fun i => g i + s)` 不超过 `Q A o x f - Q A o x (fun i => f i + s)`。
theorem Q_contract (x y : ι → X) (f g t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1)
    (h₁ : ∀ i, Dist.dist o (y i) = t i * Dist.dist o (x i))
    (h₂ : ∀ i, Dist.dist (y i) (x i) = (1 - t i) * Dist.dist o (x i))
    (hg : ∀ i, t i * f i ≤ g i) (hf₀ : ∀ i, 0 < f i) (hg₀ : ∀ i, 0 < g i)
    (hx : 0 < A.price (sites o x) 2) (hy : 0 < A.price (sites o y) 2) {s : ℝ} (hs : 0 ≤ s) :
    Q A o y g - Q A o y (fun i => g i + s) ≤ Q A o x f - Q A o x (fun i => f i + s) := by
  have hl := (H_limit A o y hy g hg₀).sub
    (H_limit A o y hy _ (fun i => add_pos_of_pos_of_nonneg (hg₀ i) hs))
  have hu := (H_limit A o x hx f hf₀).sub
    (H_limit A o x hx _ (fun i => add_pos_of_pos_of_nonneg (hf₀ i) hs))
  refine le_of_tendsto_of_tendsto hl hu ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hp (i) : t i * (f i / N) ≤ g i / N := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (hg i) hN.le
  have h := degree_contract A o x y _ _ t ht ht' h₁ h₂ hp (fun i => div_pos (hf₀ i) hN)
    (fun i => div_pos (hg₀ i) hN) hx hy (div_nonneg hs hN.le)
  simp only [← add_div] at h
  linarith only [h]

-- 读法：`Q A o x (fun i => r * f i)` 等于 `Q A o x f - A.price (sites o x) 2 * Real.log r`。
theorem Q_scale (x : ι → X) (f : ι → ℝ) (hf : ∀ i, 0 < f i)
    (hx : 0 < A.price (sites o x) 2) {r : ℝ} (hr : 0 < r) :
    Q A o x (fun i => r * f i) = Q A o x f - A.price (sites o x) 2 * Real.log r := by
  have he := H_limit A o x hx _ (fun i => mul_pos hr (hf i))
  have h := (H_limit A o x hx f hf).comp (tendsto_id.atTop_div_const hr)
  refine tendsto_nhds_unique he ((h.sub_const _).congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply, id_eq]
  rw [Real.log_div hN.ne' hr.ne', show (fun i => f i / (N / r)) = (fun i => r * f i / N) by
    ext i; field_simp]
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Multi
end
