-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import Mathlib.LinearAlgebra.Vandermonde
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Scale
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place

/-!
# 多种输入长度的多项式乘法

输出容量等于各输入长度之和。若还有额外坐标，则其系数为零。

**英文原文**

Polynomial multiplication with many input lengths

The output has the sum of the input lengths as its capacity. Extra
coordinates, if any, have zero coefficients.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {ι : Type} [Fintype ι]

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
def length (L : ι → ℕ) : Option ι → ℕ
  | none => ∑ i, L i
  | some i => L i

-- 读法：在后续公式中，`leg` 是 `Fin (length L s)` 的缩写。
abbrev leg (L : ι → ℕ) (s : Option ι) := Fin (length L s)

variable (K : Type) [Field K] (L : ι → ℕ)

-- 读法：当 `∑ i, (x (some i)).val = (x none).val` 成立时取 `1`，否则取 `0`。
def entry (x : ∀ s, leg L s) : K := if ∑ i, (x (some i)).val = (x none).val then 1 else 0

-- 读法：`polynomial` 的取值由 `Tensor.ofRaw (Raw.ofTable (leg L) (entry K L))` 给出。
def polynomial : Tensor K (Option ι) := Tensor.ofRaw (Raw.ofTable (leg L) (entry K L))

variable {L}

-- 读法：`(polynomial (ι := ι) K)` 是单调不减的。对 `s` 分类讨论。
theorem polynomial_mono : Monotone (polynomial (ι := ι) K) := by
  intro L L' h
  have he (s) : length L s ≤ length L' s := by
    cases s with
    | none => exact sum_le_sum (fun i _ => h i)
    | some i => exact h i
  refine Raw.Restricts.pullback (fun s x => Fin.castLE (he s) x) ?_
  intro x
  change (∀ s, leg L s) at x
  refine (Raw.coeff_ofTable _ _ x).trans ?_
  exact (Raw.coeff_ofTable (leg L') (entry K L') (fun s => Fin.castLE (he s) (x s))).symm

-- 读法：`polynomial K L` 不等于 `0`。对 `s` 分类讨论。
theorem polynomial_ne_zero [Nonempty ι] (hL : ∀ i, 0 < L i) : polynomial K L ≠ 0 := by
  have hp (s) : 0 < length L s := by
    cases s with
    | none => exact sum_pos (fun i _ => hL i) univ_nonempty
    | some i => exact hL i
  intro h
  let x (s) : leg L s := ⟨0, hp s⟩
  have h' := (Tensor.ofRaw_eq_zero _).mp h x
  rw [Raw.coeff_ofTable] at h'
  simp [entry, x] at h'

-- 读法：`polynomial K L` 不超过 `(∑ i, L i : ℕ)`。
/-- 范德蒙德求值和插值使每个可用的输出系数对应一个秩一项。

英文原文：Vandermonde evaluation and interpolation give one rank-one term
for each available output coefficient.
-/
theorem polynomial_rank [Infinite K] [Nonempty ι] (L : ι → ℕ) :
    polynomial K L ≤ (∑ i, L i : ℕ) := by
  classical
  let m := ∑ i, L i
  let v (i : Fin m) := Infinite.natEmbedding K i.val
  let M := Matrix.vandermonde v
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr ((Infinite.natEmbedding K).injective.comp Fin.val_injective))
  let f (l : Fin m) : (s : Option ι) → leg L s → K
    | none, u => M⁻¹ u l
    | some _, u => v l ^ u.val
  let A : Raw K (Option ι) := ⟨leg L, Fin m, f⟩
  -- 推导：记下中间结论 `he`：`polynomial K L = Tensor.ofRaw A`。
  have he : polynomial K L = Tensor.ofRaw A := by
    refine Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_)
    change (∀ s, leg L s) at x
    refine (Raw.coeff_ofTable _ _ x).trans ?_
    change entry K L x = ∑ l, ∏ s, f l s (x s)
    let b : Fin m := ⟨∑ i, (x (some i)).val,
      sum_lt_sum_of_nonempty univ_nonempty (fun i _ => (x (some i)).isLt)⟩
    simp only [Fintype.prod_option, f, prod_pow_eq_pow_sum]
    let a : Fin m := x none
    change entry K L x = (M⁻¹ * M) a b
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
    change (if b.val = a.val then (1 : K) else 0) = _
    simp only [Fin.ext_iff, eq_comm]
  rw [he]
  have h := Tensor.le_term_count A
  change _ ≤ (Fintype.card (Fin m) : Tensor K (Option ι)) at h
  rwa [Fintype.card_fin] at h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 对应两个输入和一个输出的三个带标签站点

**英文原文**

Three labelled sites with two inputs and one output
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

-- 读法：在后续公式中，`Site` 是 `Option Bool` 的缩写。
abbrev Site := Option Bool

-- 读法：在后续公式中，`sides` 是 `| some false => X | some true => Y | none => Z` 的缩写。
abbrev sides (X Y Z : Type) : Site → Type
  | some false => X
  | some true => Y
  | none => Z

variable {K X Y Z U V W : Type} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

-- 读法：逐一匹配以下输入模式：`some false`、`some true`、`none`。
instance instSides : (s : Site) → Fintype (sides X Y Z s)
  | some false => inferInstanceAs (Fintype X)
  | some true => inferInstanceAs (Fintype Y)
  | none => inferInstanceAs (Fintype Z)

-- 读法：逐一匹配以下输入模式：`some false`、`some true`、`none`。
def tuple {L : Site → Type} (x : L (some false)) (y : L (some true)) (z : L none) : ∀ s, L s
  | some false => x
  | some true => y
  | none => z

-- 读法：`tuple (x (some false)) (x (some true)) (x none)` 等于 `x`。用函数外延性比较等号两侧在 `s` 处的取值。
@[simp] theorem tuple_eta {L : Site → Type} (x : ∀ s, L s) :
    tuple (x (some false)) (x (some true)) (x none) = x := by
  funext s
  rcases s with _ | (_ | _) <;> rfl

-- 读法：`triple` 的取值由 `Raw.ofTable (sides X Y Z) (fun x => T (x (some false)) (x (some true)) (x none))` 给出。
def triple (T : X → Y → Z → K) : Raw K Site :=
  Raw.ofTable (sides X Y Z) (fun x => T (x (some false)) (x (some true)) (x none))

-- 读法：`read` 的取值由 `A.coeff (tuple x y z)` 给出。
def read (A : Raw K Site) (x : A.leg (some false)) (y : A.leg (some true)) (z : A.leg none) :=
  A.coeff (tuple x y z)

-- 读法：结论为 `∏ s, f s = f (some false) * f (some true) * f none`。
theorem prod_site (f : Site → K) : ∏ s, f s = f (some false) * f (some true) * f none := by
  rw [Fintype.prod_option, Fintype.prod_bool]
  ring

-- 读法：`read A x y z` 等于 `∑ i, A.factor i (some false) x * A.factor i (some true) y * A.factor i none z`。
theorem read_apply (A : Raw K Site) (x : A.leg (some false)) (y : A.leg (some true)) (z : A.leg none) :
    read A x y z = ∑ i, A.factor i (some false) x * A.factor i (some true) y * A.factor i none z := by
  simp only [read, Raw.coeff, prod_site, tuple]

-- 读法：`read (triple T)` 等于 `T`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem read_triple (T : X → Y → Z → K) : read (triple T) = T := by
  funext x y z
  exact Raw.coeff_ofTable _ _ _

-- 读法：`Tensor.ofRaw (triple (read A))` 等于 `Tensor.ofRaw A`。用函数外延性比较等号两侧在 `s` 处的取值。
theorem triple_read (A : Raw K Site) : Tensor.ofRaw (triple (read A)) = Tensor.ofRaw A := by
  let e (s : Site) : (triple (read A)).leg s ≃ A.leg s := match s with
    | none => Equiv.refl _
    | some false => Equiv.refl _
    | some true => Equiv.refl _
  refine Tensor.ofRaw_eq (Raw.equiv_coeff e fun x => ?_)
  refine (Raw.coeff_ofTable _ _ x).trans ?_
  apply congrArg A.coeff
  funext s
  rcases s with _ | (_ | _) <;> rfl

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `L (some false) × L (some true) × L none ≃ (∀ s, L s)`。
private def coordinates (L : Site → Type) :
    L (some false) × L (some true) × L none ≃ (∀ s, L s) where
  toFun p := tuple p.1 p.2.1 p.2.2
  invFun x := (x (some false), x (some true), x none)
  left_inv _ := rfl
  right_inv _ := tuple_eta _

-- 读法：要证明的命题是 `(triple A).Restricts (triple B)`。
theorem restricts_triple (A : X → Y → Z → K) (B : U → V → W → K)
    (f : U → X → K) (g : V → Y → K) (h : W → Z → K)
    (he : ∀ u v w, B u v w = ∑ x, ∑ y, ∑ z, f u x * g v y * h w z * A x y z) :
    (triple A).Restricts (triple B) := by
  let L (s : Site) : (triple B).leg s → (triple A).leg s → K := match s with
    | none => h
    | some false => f
    | some true => g
  refine (Raw.restricts_iff _ _).mpr ⟨L, fun x => ?_⟩
  rw [← (coordinates (triple A).leg).sum_comp]
  simp only [Fintype.sum_prod_type, prod_site]
  refine (Raw.coeff_ofTable _ _ x).trans ((he _ _ _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  exact congrArg _ (congrFun (congrFun (congrFun (read_triple A).symm i) j) k)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 有序多项式乘法的有限行不等式

**英文原文**

Finite row inequalities for ordered polynomial multiplication
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

variable (K : Type) [Field K]

-- 读法：当 `x.val + y.val = z.val` 成立时取 `1`，否则取 `0`。
def convolution (a b : ℕ) (x : Fin a) (y : Fin b) (z : Fin (a + b - 1)) : K :=
  if x.val + y.val = z.val then 1 else 0

-- 读法：`binary` 的取值由 `Tensor.ofRaw (triple (convolution K a b))` 给出。
def binary (a b : ℕ) := Tensor.ofRaw (triple (convolution K a b))

-- 读法：`reverseOutput` 的取值由 `Tensor.ofRaw (triple (fun x z y => convolution K a b x y z))` 给出。
def reverseOutput (a b : ℕ) := Tensor.ofRaw (triple (fun x z y => convolution K a b x y z))

-- 读法：`BinaryLaw` 的结果类型为 `Prop`。
/-- 以次数为索引表述的有限形式的行列式不等式与三倍化不等式。

英文原文：The finite determinant and tripling inequalities, in degree indices.
-/
def BinaryLaw : Prop :=
  ∀ (f : Tensor K Site →+* NNReal), Monotone f → ∀ p : ℝ, 0 < p →
    (f (Tensor.wire K (some true) none 2) : ℝ) = (2 : ℝ) ^ p → ∀ m : ℕ,
    Row (fun n => (f (binary K (m + 1) (n + 1)) : ℝ) ^ (1 / p))
      (fun n => (f (reverseOutput K (m + 1) (n + 1)) : ℝ) ^ (1 / p)) m

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 保留非负分次张量中权重为零的系数

**英文原文**

Keeping the weight-zero coefficients of a nonnegatively graded tensor
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {K S : Type} [Field K] [Fintype S] [Nonempty S] {X : S → Type} [∀ s, Fintype (X s)]

-- 读法：在后续公式中，`array` 是 `Tensor.ofRaw (Raw.ofTable X v)` 的缩写。
abbrev array (v : (∀ s, X s) → K) := Tensor.ofRaw (Raw.ofTable X v)

-- 读法：当 `∑ s, w s (x s) = 0` 成立时取 `v x`，否则取 `0`。
def grade (w : (s : S) → X s → ℤ) (v : (∀ s, X s) → K) (x : ∀ s, X s) : K :=
  if ∑ s, w s (x s) = 0 then v x else 0

-- 读法：`array (fun x => (∏ s, f s (x s)) * v x)` 不超过 `array v`。
private theorem rescale (v : (∀ s, X s) → K) (f : (s : S) → X s → K) :
    array (fun x => (∏ s, f s (x s)) * v x) ≤ array v := by
  classical
  let A := Raw.ofTable X v
  let B := Raw.ofTable X (fun x => (∏ s, f s (x s)) * v x)
  let L (s) (x y : X s) := if y = x then f s x else 0
  refine ⟨L, fun x => ?_⟩
  change (∀ s, X s) at x
  change B.coeff x = ∑ l : A.term, ∏ s, ∑ y : X s, L s (x s) y * A.factor l s y
  simp only [L, ite_mul, zero_mul, Fintype.sum_ite_eq', prod_mul_distrib, ← mul_sum]
  exact (Raw.coeff_ofTable _ _ x).trans (congrArg _ (Raw.coeff_ofTable X v x).symm)

-- 读法：`f (array (grade w v))` 不超过 `f (array v)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem grade_price [Infinite K] [DecidableEq S] (f : Tensor K S →+* NNReal) (hf : Monotone f)
    (v : (∀ s, X s) → K) (w : (s : S) → X s → ℤ)
    (hw : ∀ x, v x ≠ 0 → 0 ≤ ∑ s, w s (x s)) : f (array (grade w v)) ≤ f (array v) := by
  classical
  let P x := Polynomial.X ^ (∑ s, w s (x s)).toNat * Polynomial.C (v x)
  have he : (fun x => (P x).eval 0) = grade w v := by
    funext x
    by_cases hv : v x = 0
    · simp [P, grade, hv]
    by_cases hz : ∑ s, w s (x s) = 0
    · simp [P, grade, hz]
    have hn : (∑ s, w s (x s)).toNat ≠ 0 := by have := hw x hv; omega
    simp [P, grade, hz, hn]
  -- 推导：记下中间结论 `h`：`ZClosure {u | array u ≤ array v} (grade w v)`。
  have h : ZClosure {u | array u ≤ array v} (grade w v) := by
    rw [← he]
    apply Speedup.path_closure P Polynomial.X Polynomial.X_ne_zero
    intro t ht
    rw [Polynomial.eval_X] at ht
    let a s x := t ^ (w s x)
    have ha (x : ∀ s, X s) (l : Finset S) : ∏ s ∈ l, a s (x s) = t ^ (∑ s ∈ l, w s (x s)) := by
      induction l using Finset.induction_on with
      | empty => simp
      | insert i l hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ ht]
    -- 推导：记下中间结论 `hp`：`(fun x => (P x).eval t) = fun x => (∏ s, a s (x s)) * v x`。
    have hp : (fun x => (P x).eval t) = fun x => (∏ s, a s (x s)) * v x := by
      funext x
      by_cases hv : v x = 0
      · simp [P, hv]
      simp only [P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        ha, ← zpow_natCast, Int.toNat_of_nonneg (hw x hv)]
    rw [hp]
    exact rescale v a
  exact NNReal.coe_le_coe.mp (h.price f hf (by positivity) (fun _ ht => NNReal.coe_le_coe.mpr (hf ht)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
通过分级消去标签不同的项，剩下由相同副本组成的对角张量。

**英文原文**

Grading away unequal labels exposes a diagonal of identical copies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {F ι B : Type} [Field F] [Fintype ι] [Fintype B] [DecidableEq B]
  {X : Option ι → Type} [∀ s, Fintype (X s)]

-- 读法：`array (grade w v)` 等于 `(Fintype.card B : Tensor F (Option ι)) * array u`。
theorem grade_labels (w : ∀ s, B × X s → ℤ) (v : (∀ s, B × X s) → F) (u : (∀ s, X s) → F)
    (rule : ∀ x, v x ≠ 0 → ((∑ s, w s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1))
    (aligned : ∀ x, (∀ i, (x (some i)).1 = (x none).1) → v x = u (fun s => (x s).2)) :
    array (grade w v) = (Fintype.card B : Tensor F (Option ι)) * array u := by
  classical
  rw [← Tensor.diag_eq_natCast B]
  refine Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_)
  change (∀ s, B × X s) at x
  erw [Raw.coeff_ofTable, Raw.coeff_mul, Raw.coeff_ofTable]
  have hd : (Raw.diag F (Option ι) B).coeff (fun s => (x s).1) =
      if ∀ i, (x (some i)).1 = (x none).1 then 1 else 0 := by
    change ∑ p, ∏ s, (if (x s).1 = p then (1 : F) else 0) = _
    rw [Fintype.sum_eq_single (x none).1]
    · rw [Fintype.prod_option]
      simp [Fintype.prod_ite_zero]
    · intro p hp
      exact prod_eq_zero (mem_univ none) (ite_eq_right hp.symm)
  change grade w v x = (Raw.diag F (Option ι) B).coeff (fun s => (x s).1) * u (fun s => (x s).2)
  rw [hd, grade]
  by_cases h : ∀ i, (x (some i)).1 = (x none).1
  · rw [ite_eq_left h, one_mul, ← aligned x h]
    by_cases hv : v x = 0
    · simp [hv]
    · rw [ite_eq_left ((rule x hv).mpr h)]
  · rw [ite_eq_right h, zero_mul]
    by_cases hv : v x = 0
    · simp [hv]
    · rw [ite_eq_right (mt (rule x hv).mp h)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 等大分块退化

对块号 `a`、长度 `l` 和偏移 `d`，给输入赋予整数权重 `a(a-1)l + a(2d+1)`。除非 `a=b`，该权重都严格高于输出块 `b` 的支撑直线。由于次数可加，各支撑直线相加恰得到输出权重。

**英文原文**

Equal-block degeneration

For block number `a`, length `l` and offset `d`, assign the input the
integer weight `a(a-1)l + a(2d+1)`. Its excess above the supporting
line for the output block `b` is positive unless `a=b`. The supporting
lines add to the output weight because degrees add.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Finset Spectral

variable {ι : Type} [Fintype ι]

-- 读法：`weight` 的取值由 `a * (a - 1) * l + a * (2 * d + m)` 给出。
def weight (a l d m : ℤ) := a * (a - 1) * l + a * (2 * d + m)

-- 读法：`0` 严格小于 `(a - b) * ((a - b - 1) * l + 2 * d + 1)`。这里调用 `mul_pos_of_neg_of_neg`。
private theorem excess (a b l d : ℤ) (hd : 0 ≤ d) (hl : d < l) (hne : a ≠ b) :
    0 < (a - b) * ((a - b - 1) * l + 2 * d + 1) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have ht := mul_le_mul_of_nonneg_right (show a - b - 1 ≤ -2 by omega) (show 0 ≤ l by omega)
    exact mul_pos_of_neg_of_neg (by omega) (by omega)
  · have ht := mul_nonneg (show 0 ≤ a - b - 1 by omega) (show 0 ≤ l by omega)
    exact mul_pos (by omega) (by omega)

-- 读法：结论为 `let W := -weight b (∑ i, l i) u (Fintype.card ι) + ∑ i, weight (a i) (l i) (d i) 1 0 ≤ W ∧ (W = 0 ↔ ∀ i, a i = b)`。按 `a i = b` 成立与否分情况。
theorem weights (a l d : ι → ℤ) (b u : ℤ)
    (hd : ∀ i, 0 ≤ d i) (hl : ∀ i, d i < l i) (he : ∑ i, (a i * l i + d i) = b * (∑ i, l i) + u) :
    let W := -weight b (∑ i, l i) u (Fintype.card ι) + ∑ i, weight (a i) (l i) (d i) 1
    0 ≤ W ∧ (W = 0 ↔ ∀ i, a i = b) := by
  let v i := (a i - b) * ((a i - b - 1) * l i + 2 * d i + 1)
  have hv i : 0 ≤ v i ∧ (v i = 0 ↔ a i = b) := by
    by_cases h : a i = b
    · simp [v, h]
    · have hp : 0 < v i := excess _ _ _ _ (hd i) (hl i) h
      exact ⟨hp.le, iff_of_false hp.ne' h⟩
  have he' i : weight (a i) (l i) (d i) 1 =
      v i + (2 * b) * (a i * l i + d i) - b * (b + 1) * l i + b := by unfold v weight; ring
  have hW : -weight b (∑ i, l i) u (Fintype.card ι) + ∑ i, weight (a i) (l i) (d i) 1 =
      ∑ i, v i := by
    simp_rw [he']
    rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, he, ← mul_sum, sum_const]
    simp only [weight, card_univ, nsmul_eq_mul]
    ring
  dsimp only
  rw [hW]
  refine ⟨sum_nonneg (fun i _ => (hv i).1), ?_⟩
  simp only [sum_eq_zero_iff_of_nonneg (fun i _ => (hv i).1), mem_univ, forall_true_left, (hv _).2]

variable (K : Type) [Field K] (L : ι → ℕ) (k : ℕ)

-- 读法：在后续公式中，`block` 是 `Fin k × leg L s` 的缩写。
private abbrev block (s : Option ι) := Fin k × leg L s

-- 读法：`join` 的取值由 `Fin.cast (by cases s <;> simp [length, mul_sum]) (finProdFinEquiv p)` 给出。
private def join (s : Option ι) (p : block L k s) : leg (fun i => k * L i) s :=
  Fin.cast (by cases s <;> simp [length, mul_sum]) (finProdFinEquiv p)

-- 读法：`(join L k s p).val` 等于 `p.1.val * length L s + p.2.val`。
private theorem join_val (s : Option ι) (p : block L k s) :
    (join L k s p).val = p.1.val * length L s + p.2.val := by
  simp [join, finProdFinEquiv, add_comm, mul_comm]

-- 读法：`big` 的取值由 `entry K (fun i => k * L i) (fun s => join L k s (x s))` 给出。
private def big (x : ∀ s, block L k s) := entry K (fun i => k * L i) (fun s => join L k s (x s))

-- 读法：当 `s.isNone` 成立时取 `-weight p.1.val (length L s) p.2.val (Fintype.card ι)`，否则取 `weight p.1.val (length L s) p.2.val 1`。
private def grading (s : Option ι) (p : block L k s) : ℤ :=
  if s.isNone then -weight p.1.val (length L s) p.2.val (Fintype.card ι)
  else weight p.1.val (length L s) p.2.val 1

-- 读法：`0` 不超过 `∑ s, grading L k s (x s) ∧ ((∑ s, grading L k s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1)`。
private theorem grading_rule (x : ∀ s, block L k s) (hx : big K L k x ≠ 0) :
    0 ≤ ∑ s, grading L k s (x s) ∧
      ((∑ s, grading L k s (x s)) = 0 ↔ ∀ i, (x (some i)).1 = (x none).1) := by
  have he : ∑ i, ((x (some i)).1.val * L i + (x (some i)).2.val) =
      (x none).1.val * (∑ i, L i) + (x none).2.val := by
    simpa [big, entry, join_val, length] using hx
  have hw := weights (fun i => ((x (some i)).1.val : ℤ)) (fun i => (L i : ℤ))
    (fun i => ((x (some i)).2.val : ℤ)) (x none).1.val (x none).2.val
    (fun _ => by positivity) (fun i => by exact_mod_cast (x (some i)).2.isLt) (by exact_mod_cast he)
  simpa [Fintype.sum_option, grading, length, Fin.ext_iff] using hw

-- 读法：`array (grade (grading L k) (big K L k))` 等于 `(k : Tensor K (Option ι)) * polynomial K L`。
private theorem table_blocks :
    array (grade (grading L k) (big K L k)) = (k : Tensor K (Option ι)) * polynomial K L := by
  have he := grade_labels (grading L k) (big K L k) (entry K L)
    (fun x hx => (grading_rule K L k x hx).2) (by
      intro x h
      simp only [big, entry, join_val, length, h, sum_add_distrib, ← mul_sum, add_right_inj])
  rw [Fintype.card_fin] at he
  exact he

-- 读法：`k * f (polynomial K L)` 不超过 `f (polynomial K (fun i => k * L i))`。这里调用 `Raw.coeff_ofTable`。
theorem polynomial_dilate [Infinite K] [DecidableEq ι] (f : Tensor K (Option ι) →+* NNReal)
    (hf : Monotone f) : k * f (polynomial K L) ≤ f (polynomial K (fun i => k * L i)) := by
  have hb : array (big K L k) ≤ polynomial K (fun i => k * L i) := by
    refine Raw.Restricts.pullback (join L k) fun x => ?_
    change (∀ s, block L k s) at x
    refine (Raw.coeff_ofTable _ _ x).trans ?_
    exact (Raw.coeff_ofTable _ (entry K (fun i => k * L i)) (fun s => join L k s (x s))).symm
  have h := grade_price f hf (big K L k) (grading L k) (fun x hx => (grading_rule K L k x hx).1)
  rw [table_blocks, map_mul, map_natCast] at h
  exact h.trans (hf hb)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 一元多项式乘法的连续剖面

**英文原文**

Continuum profile for univariate polynomial multiplication
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Filter
open scoped Topology

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K] [Infinite K]

-- 读法：要证明的命题是 `Scaling (fun L => (f (polynomial K L) : ℝ))`。
theorem scaling_polynomial (f : Tensor K (Option ι) →+* NNReal) (hf : Monotone f) :
    Scaling (fun L => (f (polynomial K L) : ℝ)) := by
  refine ⟨fun _ => by positivity, fun _ _ h => NNReal.coe_le_coe.mpr (hf (polynomial_mono K h)), ?_, ?_⟩
  · intro L
    have h := hf (polynomial_rank K L)
    rw [map_natCast] at h
    exact_mod_cast h
  · intro k L
    exact_mod_cast polynomial_dilate K L k f hf

-- 读法：`profile` 的取值由 `scale (fun L => (f (polynomial K L) : ℝ)) t` 给出。
def profile (f : Tensor K (Option ι) →+* NNReal) (t : ι → ℝ) :=
  scale (fun L => (f (polynomial K L) : ℝ)) t

variable {f : Tensor K (Option ι) →+* NNReal} (hf : Monotone f) {t : ι → ℝ} (ht : ∀ i, 0 < t i)
include hf ht

-- 读法：`0` 严格小于 `profile f t`。这里调用 `scaling_polynomial`。
theorem profile_pos : 0 < profile f t := by
  apply (scaling_polynomial f hf).scale_pos ht (L := fun _ => 1)
  have h := hf (Tensor.one_le _ (polynomial_ne_zero K (L := fun _ => 1) (fun _ => zero_lt_one)))
  rw [map_one] at h
  exact_mod_cast zero_lt_one.trans_le h

-- 读法：`(fun n => Real.log (f (polynomial K (L n))) - Real.log (N n))` 沿滤子 `l` 收敛到 `(Real.log (profile f t))`。这里调用 `h.log`。
theorem log_profile_limit {α : Type*} {l : Filter α} {N : α → ℝ}
    (hN : Tendsto N l atTop) {L : α → ι → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (t i))) :
    Tendsto (fun n => Real.log (f (polynomial K (L n))) - Real.log (N n))
      l (𝓝 (Real.log (profile f t))) := by
  have h := (scaling_polynomial f hf).limit ht hN hL
  have hp := profile_pos hf ht
  apply (h.log hp.ne').congr'
  filter_upwards [hN.eventually_gt_atTop 0, h.eventually_const_lt hp] with n hn hn'
  exact Real.log_div ((div_pos_iff_of_pos_right hn).mp hn').ne' hn.ne'

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 从以二为底的普通价格到自然对数剖面

**英文原文**

From ordinary base-two prices to natural-log profiles
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

-- 读法：逐一匹配以下输入模式：`false`、`true`。
def two {α : Type*} (x y : α) : Bool → α
  | false => x
  | true => y

-- 读法：逐一匹配以下输入模式：`none`、`some false`、`some true`。
def pairSite (i j : Fin 3) : Site → Fin 3
  | none => -i - j
  | some false => i
  | some true => j

-- 读法：`placement` 的取值由 `v ∘ pairSite i j` 给出。
def placement {X : Type*} (v : Fin 3 → X) (i j : Fin 3) := v ∘ pairSite i j

-- 读法：`(pairSite i j)` 是双射。使用 `fin_cases` 给出的结论。
theorem pairSite_bijective {i j : Fin 3} (hij : i ≠ j) : Function.Bijective (pairSite i j) := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

variable {K S : Type} [Field K] [Fintype S] [Nontrivial S] [DecidableEq S]
    {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X) (v : S → X)

-- 读法：存在 `f : Tensor K S →+* NNReal`，`Monotone f` 与 `∀ B, Real.log 2 * A.price v B = A.price v 2 * Real.log (f B)` 同时成立。
private theorem exists_point :
    ∃ f : Tensor K S →+* NNReal, Monotone f ∧
      ∀ B, Real.log 2 * A.price v B = A.price v 2 * Real.log (f B) := by
  obtain ⟨_, d, _, f, hf, he⟩ := A.valid v
  have hn (B : Tensor K S) : 0 ≤ f B := by simpa using hf (Tensor.zero_le B)
  let g : Tensor K S →+* NNReal :=
    { toFun := fun B => ⟨f B, hn B⟩
      map_zero' := Subtype.ext (map_zero f)
      map_one' := Subtype.ext (map_one f)
      map_add' := fun a b => Subtype.ext (f.map_add a b)
      map_mul' := fun a b => Subtype.ext (f.map_mul a b) }
  refine ⟨g, hf, fun B => ?_⟩
  change Real.log 2 * A.price v B = A.price v 2 * Real.log (f B)
  rw [he, Tensor.values, Tensor.values, map_ofNat]
  ring

-- 读法：`point` 的取值由 `(exists_point A v).choose` 给出。
def point : Tensor K S →+* NNReal := (exists_point A v).choose

-- 读法：`(point A v)` 是单调不减的。使用 `exists_point` 给出的结论。
theorem point_mono : Monotone (point A v) := (exists_point A v).choose_spec.1

-- 读法：`Real.log 2 * A.price v B` 等于 `A.price v 2 * Real.log (point A v B)`。使用 `exists_point` 给出的结论。
theorem price_eq (B : Tensor K S) :
    Real.log 2 * A.price v B = A.price v 2 * Real.log (point A v B) :=
  (exists_point A v).choose_spec.2 B

-- 读法：`A.price (placement v i j) 2` 等于 `A.price v 2`。
theorem placement_two (v : Fin 3 → X) {i j : Fin 3} (hij : i ≠ j) :
    A.price (placement v i j) 2 = A.price v 2 := by
  unfold placement
  rw [A.place, Function.comp_apply, Tensor.place_eq_group _ (pairSite_bijective hij).2, map_ofNat]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 对双输入多项式张量重新编号

**英文原文**

Reindexing the two-input polynomial tensor
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral

variable {K X Y Z : Type} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：逐一匹配以下输入模式：`none`、`some false`、`some true`。
def flip : Site → Site
  | none => none
  | some false => some true
  | some true => some false

-- 读法：逐一匹配以下输入模式：`none`、`some false`、`some true`。
def turn : Site → Site
  | none => some true
  | some false => some false
  | some true => none

-- 读法：`Tensor.place turn (Tensor.ofRaw (triple T))` 不超过 `Tensor.ofRaw (triple (fun x z y => T x y z))`。
private theorem turn_le (T : X → Y → Z → K) :
    Tensor.place turn (Tensor.ofRaw (triple T)) ≤ Tensor.ofRaw (triple (fun x z y => T x y z)) := by
  let A := (triple T).group turn
  let L (s : Site) : A.leg s → sides X Z Y s := match s with
    | none => fun x => x ⟨some true, rfl⟩
    | some false => fun x => x ⟨some false, rfl⟩
    | some true => fun x => x ⟨none, rfl⟩
  refine Raw.Restricts.pullback L fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

-- 读法：`Tensor.place turn (binary K a b)` 等于 `reverseOutput K a b`。这里调用 `le_antisymm`。
theorem place_turn (a b : ℕ) : Tensor.place turn (binary K a b) = reverseOutput K a b := by
  apply le_antisymm (turn_le _)
  have h := Tensor.place_mono turn (turn_le (fun x z y => convolution K a b x y z))
  rw [← Tensor.place_comp, show turn ∘ turn = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id] at h
  exact h

-- 读法：`Tensor.place flip (binary K a b)` 不超过 `binary K b a`。
private theorem flip_le (a b : ℕ) : Tensor.place flip (binary K a b) ≤ binary K b a := by
  let A := (triple (convolution K a b)).group flip
  let L (s : Site) : A.leg s → sides (Fin b) (Fin a) (Fin (b + a - 1)) s := match s with
    | none => fun x => Fin.cast (show a + b - 1 = b + a - 1 by omega) (x ⟨none, rfl⟩)
    | some false => fun x => x ⟨some true, rfl⟩
    | some true => fun x => x ⟨some false, rfl⟩
  refine Raw.Restricts.pullback L fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]
  unfold convolution
  rw [Nat.add_comm]
  rfl

-- 读法：`Tensor.place flip (binary K a b)` 等于 `binary K b a`。这里调用 `le_antisymm`。
theorem place_flip (a b : ℕ) : Tensor.place flip (binary K a b) = binary K b a := by
  apply le_antisymm (flip_le _ _)
  have h := Tensor.place_mono flip (flip_le (K := K) b a)
  rw [← Tensor.place_comp, show flip ∘ flip = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id] at h
  exact h

-- 读法：`binary K a b` 等于 `polynomial K (two a b)`。用函数外延性比较等号两侧在 `x y z` 处的取值。
theorem binary_eq (a b : ℕ) : binary K a b = polynomial K (two a b) := by
  classical
  let d := length (two a b) none
  have hd : d = a + b := by simp [d, length, two, add_comm]
  let W (x : Fin a) (y : Fin b) (z : Fin d) : K := if x.val + y.val = z.val then 1 else 0
  let A := Raw.ofTable (leg (two a b)) (entry K (two a b))
  have he : read A = W := by
    funext x y z
    refine (Raw.coeff_ofTable _ _ _).trans ?_
    simp [entry, W, tuple, Nat.add_comm]
  change Tensor.ofRaw (triple _) = Tensor.ofRaw A
  rw [← triple_read A, he]
  change Tensor.ofRaw (triple (convolution K a b)) = Tensor.ofRaw (triple W)
  let e := Fin.castLE (show a + b - 1 ≤ d by omega)
  let δ {α : Type} (x y : α) : K := if x = y then 1 else 0
  apply Tensor.ofRaw_eq
  constructor
  · refine restricts_triple _ _ δ δ (fun z z' => δ z (e z')) fun x y z => ?_
    simp only [δ, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Fintype.sum_ite_eq]
    let l : Fin (a + b - 1) := ⟨x.val + y.val, by have := x.isLt; have := y.isLt; omega⟩
    rw [Fintype.sum_eq_single l]
    · simp [convolution, l, W, e, Fin.ext_iff, eq_comm]
    · intro j hj
      have h' : x.val + y.val ≠ j.val := fun h' => hj (Fin.ext h'.symm)
      simp [convolution, h']
  · refine restricts_triple _ _ δ δ (fun z z' => δ (e z) z') fun x y z => ?_
    simp only [δ, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Fintype.sum_ite_eq]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 三点配置上的宽度剖面

**英文原文**

Width profiles on a three-point placement
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter
open scoped Topology

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X)
    (v : Fin 3 → X)

-- 读法：`pairs` 的取值由 `if i ≠ j ∧ 0 < x ∧ 0 < y then A.price v 2 * Real.log (profile (point A (placement v i j)) (two x y)) else 0` 给出。
def pairs (i j : Fin 3) (x y : ℝ) : ℝ :=
  if i ≠ j ∧ 0 < x ∧ 0 < y then
    A.price v 2 * Real.log (profile (point A (placement v i j)) (two x y))
  else 0

variable [Infinite K] {i j : Fin 3} {x y : ℝ}

-- 读法：要证明的命题是 `Tendsto (fun n => Real.log 2 * A.price (placement v i j) (polynomial K (L n)) - A.price v 2 * Real.log (N n)) l (𝓝 (pairs A v i j x y))`。这里调用 `h.congr'`。
theorem pairs_limit (hij : i ≠ j) (hx : 0 < x) (hy : 0 < y)
    {α : Type*} {l : Filter α} {N : α → ℝ} (hN : Tendsto N l atTop) {L : α → Bool → ℕ}
    (hL : ∀ i, Tendsto (fun n => (L n i : ℝ) / N n) l (𝓝 (two x y i))) :
    Tendsto (fun n => Real.log 2 * A.price (placement v i j) (polynomial K (L n)) -
      A.price v 2 * Real.log (N n)) l (𝓝 (pairs A v i j x y)) := by
  have ht : ∀ b, 0 < two x y b := by rintro (_ | _) <;> assumption
  have h := (log_profile_limit (point_mono A (placement v i j)) ht hN hL).const_mul (A.price v 2)
  rw [pairs, ite_eq_left ⟨hij, hx, hy⟩]
  apply h.congr'
  filter_upwards [] with n
  rw [price_eq A (placement v i j), placement_two A v hij, mul_sub]

-- 读法：`pairs A v i j (s * x) (s * y)` 等于 `pairs A v i j x y + A.price v 2 * Real.log s`。这里调用 `scaling_polynomial`。
theorem pairs_scale (hij : i ≠ j) {s : ℝ} (hs : 0 < s) (hx : 0 < x) (hy : 0 < y) :
    pairs A v i j (s * x) (s * y) = pairs A v i j x y + A.price v 2 * Real.log s := by
  have ht : ∀ b, 0 < two x y b := by rintro (_ | _) <;> assumption
  let f := point A (placement v i j)
  have hf : Monotone f := point_mono _ _
  have he : profile f (two (s * x) (s * y)) = s * profile f (two x y) := by
    rw [show two (s * x) (s * y) = s • two x y by funext b; cases b <;> rfl]
    exact (scaling_polynomial f hf).scale_smul ht hs
  rw [pairs, pairs, ite_eq_left ⟨hij, mul_pos hs hx, mul_pos hs hy⟩, ite_eq_left ⟨hij, hx, hy⟩,
    he, Real.log_mul hs.ne' (profile_pos hf ht).ne']
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
通过将最后一个输入吸收到输出站址，或抽取固定总次数的分量，得到相应的限制。

**英文原文**

Restrictions by absorbing the last input at the output site or extracting a fixed total degree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Spectral Finset

variable {K : Type} [Field K]

-- 读法：`Tensor.place f (polynomial K L)` 不超过 `Tensor.place g (polynomial K M)`。用函数外延性比较等号两侧在 `t` 处的取值。
private theorem placed_le {S T U : Type} [Fintype S] [Fintype T] [Fintype U]
    [DecidableEq S] [DecidableEq T] [DecidableEq U] {L : S → ℕ} {M : T → ℕ}
    (f : Option S → U) (g : Option T → U)
    (v : ∀ t, (∀ s, f s = g t → leg L s) → leg M t)
    (he : ∀ x, entry K L x = entry K M (fun t => v t (fun s _ => x s))) :
    Tensor.place f (polynomial K L) ≤ Tensor.place g (polynomial K M) := by
  let A := Raw.ofTable (leg L) (entry K L)
  let B := Raw.ofTable (leg M) (entry K M)
  let V (u : U) (x : (A.group f).leg u) : (B.group g).leg u :=
    fun t => v t (fun s h => x ⟨s, h.trans t.property⟩)
  refine Raw.Restricts.pullback V fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable, he]
  congr 1
  funext t
  unfold V
  congr 1
  funext s h
  have aux (u : U) (h : f s = u) : x (f s) ⟨s, rfl⟩ = x u ⟨s, h⟩ := by cases h; rfl
  exact aux _ h

-- 读法：逐一匹配以下输入模式：`none`、`some false`、`some true`。
private def pins (i j k : Fin 3) : Site → Fin 3
  | none => k
  | some false => i
  | some true => j

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
def terminal (k : Fin 3) : Option (Fin 3) → Fin 3
  | none => k
  | some i => i

variable {i j k : Fin 3} {L : Fin 3 → ℕ}

-- 读法：`pairSite i j` 等于 `pins i j k`。用函数外延性比较等号两侧在 `t` 处的取值。
private theorem pairSite_eq (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairSite i j = pins i j k := by
  funext t
  rcases t with _ | (_ | _) <;> simp [pairSite, pins]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | decide

-- 读法：结论为 `∑ t, v t = v i + v j + v k`。这里调用 `Finset.eq_univ_of_card`。
private theorem sum_three (v : Fin 3 → ℕ) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, v t = v i + v j + v k := by
  have he : {i, j, k} = (univ : Finset (Fin 3)) := by
    apply Finset.eq_univ_of_card
    simp [hij, hik, hjk]
  simp [← he, hij, hik, hjk, add_assoc]

-- 读法：`length (two a b) none` 等于 `a + b`。
private theorem pair_length (a b : ℕ) : length (two a b) none = a + b := by
  simp [length, two, add_comm]

-- 读法：当 `w ≤ z ∧ z - w < d` 成立时取 `z - w`，否则取 `d - 1`。
/-- 若差值超出范围，则使用该对的备用输出坐标。

英文原文：An out-of-range difference uses the spare output coordinate of the pair.
-/
private def shift (d z w : ℕ) : ℕ :=
  if w ≤ z ∧ z - w < d then z - w else d - 1

-- 读法：`Tensor.place (terminal k) (polynomial K L)` 不超过 `Tensor.place (pairSite i j) (polynomial K (two (L i) (L j)))`。
theorem absorb (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : 0 < L i) :
    Tensor.place (terminal k) (polynomial K L) ≤
      Tensor.place (pairSite i j) (polynomial K (two (L i) (L j))) := by
  rw [pairSite_eq hij hik hjk]
  let M := two (L i) (L j)
  let D := L i + L j
  have hd : length M none = D := pair_length _ _
  have hshift (z w : ℕ) : shift D z w < length M none := by
    rw [hd]
    unfold shift D
    split <;> omega
  let v : ∀ t, (∀ s, terminal k s = pins i j k t → leg L s) → leg M t
    | some false, x => x (some i) rfl
    | some true, x => x (some j) rfl
    | none, x => ⟨shift D (x none rfl).val (x (some k) rfl).val, hshift _ _⟩
  refine placed_le _ _ v fun x => ?_
  -- 推导：记下中间结论 `h₁`：`(x (some i)).val < L i`。
  have h₁ : (x (some i)).val < L i := (x (some i)).isLt
  have h₂ : (x (some j)).val < L j := (x (some j)).isLt
  simp only [entry, sum_three _ hij hik hjk, Fintype.sum_bool, v]
  congr 1
  apply propext
  unfold shift D
  split <;> omega

-- 读法：`Tensor.place (some ∘ pairSite i j) (polynomial K (two (L i) (L j)))` 不超过 `polynomial K L`。
/-- 将输出固定在次数 `L i + L j - 1` 上，并反转输入 `k` 的次数，从而显出一个以 `k` 为输出的双输入多项式。

英文原文：Pin the output at degree `L i + L j - 1` and reverse the degree
on input `k` to expose a two-input polynomial with output at `k`.
-/
theorem extract_pair (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : 0 < L i)
    (hk : L i + L j ≤ L k) :
    Tensor.place (some ∘ pairSite i j) (polynomial K (two (L i) (L j))) ≤ polynomial K L := by
  rw [pairSite_eq hij hik hjk]
  let M := two (L i) (L j)
  let D := L i + L j
  have hd : length M none = D := pair_length _ _
  have hout : D - 1 < length L none := by
    rw [length, sum_three _ hij hik hjk]
    unfold D
    omega
  let v : ∀ t, (∀ s, some (pins i j k s) = t → leg M s) → leg L t
    | none, _ => ⟨D - 1, hout⟩
    | some l, x =>
      if hi' : i = l then Fin.cast (congrArg L hi') (x (some false) (congrArg some hi'))
      else if hj' : j = l then Fin.cast (congrArg L hj') (x (some true) (congrArg some hj'))
      else
        have eq : k = l := by omega
        have hD : D - 1 < L l := by rw [← eq]; unfold D; omega
        ⟨D - 1 - (x none (congrArg some eq)).val, (Nat.sub_le _ _).trans_lt hD⟩
  rw [← Tensor.place_id (polynomial K L)]
  refine placed_le _ _ v fun x => ?_
  -- 推导：记下中间结论 `h₁`：`(x none).val < D`。
  have h₁ : (x none).val < D := hd ▸ (x none).isLt
  simp only [entry, sum_three _ hij hik hjk, Fintype.sum_bool, v, hij, hik, hjk,
    dite_eq_right, dite_eq_left, eq_self, not_false_eq_true]
  congr 1
  apply propext
  change (x (some true)).val + (x (some false)).val = (x none).val ↔
    (x (some false)).val + (x (some true)).val + (D - 1 - (x none).val) = D - 1
  omega

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-!
# 宽度剖面与站点置换的相容性

**英文原文**

Compatibility of the width profiles with site permutations
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Filter Spectral
open scoped Topology

variable {K : Type} [Field K] {X : Type*} [PseudoMetricSpace X] (A : MatrixExponent.Prices.Atlas K X)
    (v : Fin 3 → X) {i j k : Fin 3} {x y : ℝ}

-- 读法：`-i - j` 等于 `k`。使用 `fin_cases` 给出的结论。
theorem remaining (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : -i - j = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | decide

-- 读法：`A.price (placement v i j) (binary K a b)` 等于 `A.price (placement v j i) (binary K b a)`。用函数外延性比较等号两侧在 `s` 处的取值。
theorem price_flip (i j : Fin 3) (a b : ℕ) :
    A.price (placement v i j) (binary K a b) = A.price (placement v j i) (binary K b a) := by
  have he : placement v i j = placement v j i ∘ flip := by
    funext s
    rcases s with _ | (_ | _) <;> simp [placement, pairSite, flip, sub_eq_add_neg, add_comm]
  rw [he, A.place, Function.comp_apply, place_flip]

-- 读法：`A.price (placement v i k) (binary K a b)` 等于 `A.price (placement v i j) (reverseOutput K a b)`。用函数外延性比较等号两侧在 `s` 处的取值。
theorem price_turn (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : ℕ) :
    A.price (placement v i k) (binary K a b) = A.price (placement v i j) (reverseOutput K a b) := by
  have he : placement v i k = placement v i j ∘ turn := by
    funext s
    rcases s with _ | (_ | _) <;>
      simp [placement, pairSite, turn, remaining hij hik hjk, remaining hik hij hjk.symm]
  rw [he, A.place, Function.comp_apply, place_turn]

-- 读法：`binary K (a + 1) (b + 1)` 不等于 `0`。这里调用 `polynomial_ne_zero`。
theorem binary_ne_zero (a b : ℕ) : binary K (a + 1) (b + 1) ≠ 0 := by
  rw [binary_eq]
  exact polynomial_ne_zero K (by rintro (_|_) <;> exact Nat.succ_pos _)

-- 读法：`reverseOutput K (a + 1) (b + 1)` 不等于 `0`。这里调用 `binary_ne_zero`。
theorem reverse_ne_zero (a b : ℕ) : reverseOutput K (a + 1) (b + 1) ≠ 0 := by
  rw [← place_turn]
  intro hz
  have he := congrArg (Tensor.place turn) hz
  rw [← Tensor.place_comp, show turn ∘ turn = id by funext s; rcases s with _ | (_ | _) <;> rfl,
    Tensor.place_id, Tensor.place_zero] at he
  exact binary_ne_zero a b he

-- 读法：`0` 严格小于 `(f T : ℝ)`。
theorem point_pos {f : Tensor K Site →+* NNReal} (hf : Monotone f)
    {T : Tensor K Site} (hT : T ≠ 0) : 0 < (f T : ℝ) := by
  have h := hf (Tensor.one_le _ hT)
  rw [map_one] at h
  exact_mod_cast zero_lt_one.trans_le h

-- 读法：`0 < A.price v 2` 与 `(point A (placement v i j) (Tensor.wire K (some true) none 2) : ℝ) = (2 : ℝ) ^ (d / A.price v 2)` 同时成立。
theorem scaled_wire (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {d : ℝ} (hd : 0 < d) (he : Dist.dist (v j) (v k) = d) :
    0 < A.price v 2 ∧
      (point A (placement v i j) (Tensor.wire K (some true) none 2) : ℝ) = (2 : ℝ) ^ (d / A.price v 2) := by
  let w := placement v i j
  let B := Tensor.wire K (some true) none 2
  have he' : A.price w B = d := by
    rw [show A.price w B = Dist.dist (w (some true)) (w none) from A.wire _ _ _]
    simpa [w, placement, pairSite, remaining hij hik hjk] using he
  have hD := price_eq A w B
  rw [he', placement_two A v hij] at hD
  -- 推导：记下中间结论 `hlog`：`0 < Real.log 2`。
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hone : (1 : ℝ) ≤ point A w B := by
    have h := point_mono A w (Tensor.one_le_wire K (some true) none (n := 2) (by decide))
    rw [map_one] at h
    exact_mod_cast h
  have hpos : 0 < A.price v 2 := pos_of_mul_pos_left (hD ▸ mul_pos hlog hd) (Real.log_nonneg hone)
  refine ⟨hpos, ?_⟩
  rw [Real.rpow_def_of_pos (by norm_num), ← mul_div_assoc, hD, mul_div_cancel_left₀ _ hpos.ne',
    Real.exp_log (zero_lt_one.trans_le hone)]

variable [Infinite K]

-- 读法：这里调用 `pairs_limit`。
theorem binary_limit (hij : i ≠ j) (hx : 0 < x) (hy : 0 < y) {a b : ℝ → ℕ}
    (ha : Tendsto (fun n => (a n : ℝ) / n) atTop (𝓝 x))
    (hb : Tendsto (fun n => (b n : ℝ) / n) atTop (𝓝 y)) :
    Tendsto (fun n => Real.log 2 * A.price (placement v i j) (binary K (a n + 1) (b n + 1)) -
      A.price v 2 * Real.log n) atTop (𝓝 (pairs A v i j x y)) := by
  have h₁ : Tendsto (fun n : ℝ => 1 / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  simp_rw [binary_eq]
  apply pairs_limit A v hij hx hy tendsto_id
  rintro (_ | _)
  · simpa only [two, Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using ha.add h₁
  · simpa only [two, Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using hb.add h₁

-- 读法：`pairs A v i j x y` 等于 `pairs A v j i y x`。按 `i ≠ j ∧ 0 < x ∧ 0 < y` 成立与否分情况。
theorem pairs_symm (i j : Fin 3) (x y : ℝ) : pairs A v i j x y = pairs A v j i y x := by
  by_cases h : i ≠ j ∧ 0 < x ∧ 0 < y
  swap; · have : ¬(j ≠ i ∧ 0 < y ∧ 0 < x) := by tauto
          simp only [pairs, ite_eq_right h, ite_eq_right this]
  obtain ⟨hij, hx, hy⟩ := h
  have ha := tendsto_nat_floor_mul_div_atTop hx.le
  have hb := tendsto_nat_floor_mul_div_atTop hy.le
  have h := binary_limit A v hij hx hy ha hb
  simp_rw [price_flip A v i j] at h
  exact tendsto_nhds_unique h (binary_limit A v hij.symm hy hx hb ha)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end
