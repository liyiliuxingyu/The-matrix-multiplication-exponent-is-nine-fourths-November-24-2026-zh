-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.FourArms
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model
import OAI.LinearAlgebra.MatrixExponent.Prices.Space

/-!
# 将叶节点距离实现为平移后各点间距离的极限

**英文原文**

Realizing the leaf distances as limits of translated points
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0

open Filter
open scoped Topology

-- 读法：结构的字段包括 `e`、`origin`、`r`、`factor`、`pos`。
structure Dilation where
  e : ℕ → ℚ
  origin : ℕ → ℚ
  r : ℝ
  factor : ℕ → ℝ
  pos : ∀ n, 0 < e n
  pos_r : 0 < r
  pos_factor : ∀ n, 0 < factor n
  he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)
  ht : Tendsto (fun n => (origin n : ℝ)) atTop (𝓝 r)

variable {E X : Type*} [Field E]

-- 读法：`Dilation.index` 的取值由 `zoom (D.e n) (D.origin n) (D.pos n) z` 给出。
def Dilation.index (D : Dilation) (n : ℕ) (z : K0 E) : K0 E :=
  zoom (D.e n) (D.origin n) (D.pos n) z

-- 读法：`D.index n (z - w)` 等于 `D.index n z - D.index n w`。
@[simp] theorem Dilation.index_sub (D : Dilation) (n : ℕ) (z w : K0 E) :
    D.index n (z - w) = D.index n z - D.index n w := by simp [index, zoom, mul_sub]

-- 读法：对每个 `ᶠ n in atTop`，`0` 严格小于 `val E (D.index n z)`。使用 `zoom_pos` 给出的结论。
theorem Dilation.positive (D : Dilation) (z : K0 E) :
    ∀ᶠ n in atTop, 0 < val E (D.index n z) := zoom_pos D.pos_r D.pos D.he D.ht z

variable [MetricSpace X] [MulAction (G E) X] [IsIsometricSMul (G E) X]

-- 读法：`Dilation.point` 的取值由 `shift (D.index n z) • A` 给出。
def Dilation.point (D : Dilation) (A : X) (n : ℕ) (z : K0 E) : X := shift (D.index n z) • A

-- 读法：按 `z = w` 成立与否分情况。
theorem RadialStars.leaves [CompleteSpace X] (h : RadialStars E X) (C : Routing.Comparison X)
    {M : ℝ} (hM : ∀ x y : X, dist x y ≤ M) (o : X)
    (hm : ∃ a : ℝ, 0 < a ∧ o ∉ fixed (level E a))
    (hs : ∀ ε : ℝ, 0 < ε → ∃ b, 0 < b ∧ profile E o b < ε) :
    ∃ (A : X) (D : Dilation),
      (∀ φ : X → X, Isometry φ → φ o = o →
        Set.MapsTo φ (fixed (level E D.r)) (fixed (level E D.r)) → φ A = A) ∧
      ∀ z w : K0 E, Tendsto (fun n => D.factor n * dist (D.point A n z) (D.point A n w))
        atTop (𝓝 (diskDist (leaf z) (leaf w) : ℝ)) := by
  obtain ⟨r, A, k, hr, hk, _, hfix, hh⟩ :=
    motion_scale C (level E) (level_anti.antitoneOn _) hM (h.secants hM) o hm hs
  -- 推导：从 `hh.zoom hk` 中取出 `e, t₀, he, he0, ht, hlim`。
  obtain ⟨e, t₀, he, he0, ht, hlim⟩ := hh.zoom hk
  let D : Dilation := ⟨e, t₀, r, fun n => 2 / (k * e n), he, hr,
    fun n => div_pos (by norm_num) (mul_pos hk (Rat.cast_pos.mpr (he n))), he0, ht⟩
  refine ⟨A, D, hfix, fun z w => ?_⟩
  by_cases hz : z = w
  · subst w
    simp
  obtain ⟨s, hv⟩ := WithTop.ne_top_iff_exists.mp ((val E).ne_top_iff.mpr (sub_ne_zero.mpr hz))
  rw [leaf_dist hv.symm, Rat.cast_mul, Rat.cast_max, Rat.cast_sub, Rat.cast_zero,
    Rat.cast_one, Rat.cast_ofNat]
  refine zoom_leaf (R := profile E A) hr (fun n => (D.pos_factor n).le) he he0 ht hlim s _ ?_
  filter_upwards [D.positive z, D.positive w, D.positive (z - w)] with n hn hm hd
  -- 推导：记下中间结论 `hval`：`val E (D.index n (z - w)) = ↑(t₀ n + e n * s)`。
  have hval : val E (D.index n (z - w)) = ↑(t₀ n + e n * s) := val_zoom _ _ _ hv.symm
  have hq : 0 < t₀ n + e n * s := WithTop.coe_pos.mp (hval ▸ hd)
  have hshift : shift (D.index n z) = shift (D.index n w) * shift (D.index n (z - w)) := by
    rw [← shift_add hm hd, D.index_sub, add_sub_cancel]
  unfold Dilation.point
  rw [hshift, mul_smul, dist_smul, dist_comm]
  exact ⟨dist_nonneg, cost_le hq hval.ge hM, fun _ ha hb => h.star hM A ha hb hval⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0
end

/-!
# 具有共同误差空间的稀疏乘积

矩形乘法的每个输出都使用若干专用的简单乘积，以及公共双线性型的一个线性组合。

**英文原文**

Sparse products with a common error space

Each output of a rectangular multiplication uses private simple
products and a linear combination of common bilinear forms.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Spectral Finset
open scoped Classical

-- 读法：在后续公式中，`Out` 是 `Fin s × Fin s` 的缩写。
abbrev Out (s : ℕ) := Fin s × Fin s
-- 读法：在后续公式中，`Leg` 是 `Fin s × Fin j` 的缩写。
abbrev Leg (s j : ℕ) := Fin s × Fin j

variable {s j r p : ℕ}

-- 读法：当 `(x.1, y.1) = e ∧ x.2 = y.2` 成立时取 `1`，否则取 `0`。
def entry (F : Type) [Field F] (e : Out s) (x y : Leg s j) : F :=
  if (x.1, y.1) = e ∧ x.2 = y.2 then 1 else 0

-- 读法：`short` 的取值由 `∑ t, u e t x * v e t y` 给出。
def short (F : Type) [Field F] (u v : Out s → Fin p → Leg s j → F) (e : Out s) (x y : Leg s j) :=
  ∑ t, u e t x * v e t y

-- 读法：`Decodes` 的结果类型为 `Prop`。
def Decodes (F : Type) [Field F] (s j r p : ℕ) : Prop :=
  ∃ (u v : Out s → Fin p → Leg s j → F) (c : Out s → Fin r → F)
    (b : Fin r → Leg s j → Leg s j → F),
    ∀ e x y, entry F e x y = short F u v e x y + ∑ t, c e t * b t x y

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

-- 读法：`SparseApprox` 的结果类型为 `Prop`。
/-- 由有限秩公式得到稀疏的输出专用乘积与共享的误差坐标。

英文原文：Sparse private products and shared error coordinates from a finite rank formula.
-/
def SparseApprox (F : Type) [Field F] : Prop :=
  ∀ n : ℕ, ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 ≤ C ∧ ∀ s j r b : ℕ,
    r ≤ 2 ^ b → s * s ≤ 2 ^ b → Rectangle.RankLE F s s j r →
    ∃ t : ℕ, 0 < t ∧ (t : ℝ) ≤ C * (2 : ℝ) ^ (((n : ℝ) + 1 - c) * b) ∧
      Decodes F (s ^ (n + 1)) (j ^ (n + 1)) t (2 ^ (2 * b))

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 矩形张量幂的二进制填充

将公共因子矩阵所有未使用的列置零。每个寄存器都使用同一矩阵，使它在各矩阵乘积索引的每一个数位上独立作用。

**英文原文**

Binary padding of rectangular tensor powers

Use zero for every unused column of the common factor matrix. The same
matrix on each register acts independently on each digit of every
matrix-product index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Finset Classical

variable {F : Type} [Field F] {s j r m : ℕ}

-- 读法：结论为 `∃ (M : Matrix (Bits m) (Bits m) F) (row : Out s → Bits m) (u v : Bits m → Leg s j → F), ∀ e x y, entry F e x y = ∑ t, M (row e) t * (u t x * v t y)`。
private theorem padded (hr : r ≤ 2 ^ m) (hs : s * s ≤ 2 ^ m) (h : Rectangle.RankLE F s s j r) :
    ∃ (M : Matrix (Bits m) (Bits m) F) (row : Out s → Bits m)
      (u v : Bits m → Leg s j → F), ∀ e x y,
      entry F e x y = ∑ t, M (row e) t * (u t x * v t y) := by
  obtain ⟨a, b, c, h⟩ := h
  let row : Out s ↪ Bits m := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [Out, Bits] using hs))
  let col : Fin r ↪ Bits m := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [Bits] using hr))
  let pad (z : Fin r → F) := Function.extend col z (fun _ => 0)
  let M := Function.extend row (fun e => pad (fun t => c t e)) (fun _ _ => 0)
  refine ⟨M, row, fun t x => pad (fun i => a i x) t, fun t y => pad (fun i => b i y.swap) t,
    fun e x y => ?_⟩
  unfold M
  rw [row.injective.extend_apply]
  let f (t : Bits m) := pad (fun i => c i e) t *
    (pad (fun i => a i x) t * pad (fun i => b i y.swap) t)
  change entry F e x y = ∑ t, f t
  calc
    _ = ∑ i, a i x * b i y.swap * c i e := by
      rw [h]
      simp [entry, Prod.ext_iff, and_assoc, and_comm]
    _ = ∑ t ∈ univ.image col, f t := by
      rw [sum_image col.injective.injOn]
      simp only [f, pad, col.injective.extend_apply, mul_comm]
    _ = _ := by
      apply sum_subset (subset_univ _)
      intro t _ ht
      -- 推导：记下中间结论 `hn`：`¬ ∃ i, col i = t`。
      have hn : ¬ ∃ i, col i = t := by simpa using ht
      simp [f, pad, Function.extend, hn]

-- 读法：`digit` 的取值由 `Fintype.equivOfCardEq (by simp)` 给出。
private def digit (s k : ℕ) : Fin (s ^ k) ≃ (Fin k → Fin s) :=
  Fintype.equivOfCardEq (by simp)

-- 读法：`split` 的取值由 `(digit s k x.1 i, digit j k x.2 i)` 给出。
private def split {k : ℕ} (x : Leg (s ^ k) (j ^ k)) (i : Fin k) : Leg s j :=
  (digit s k x.1 i, digit j k x.2 i)

-- 读法：`entry F e x y` 等于 `∏ i, entry F (split e i) (split x i) (split y i)`。按 `(x.1, y.1) = e ∧ x.2 = y.2` 成立与否分情况。
private theorem entry_prod {k : ℕ} (e : Out (s ^ k)) (x y : Leg (s ^ k) (j ^ k)) :
    entry F e x y = ∏ i, entry F (split e i) (split x i) (split y i) := by
  unfold entry
  by_cases h : (x.1, y.1) = e ∧ x.2 = y.2
  · obtain ⟨rfl, he⟩ := h
    simp [split, he]
  · rw [ite_eq_right h]
    have hn : ∃ i, ¬ (((split x i).1, (split y i).1) = split e i ∧
        (split x i).2 = (split y i).2) := by
      by_contra! h'
      apply h
      refine ⟨Prod.ext ?_ ?_, (digit j k).injective (funext fun i => (h' i).2)⟩
      · exact (digit s k).injective (funext fun i => congrArg Prod.fst (h' i).1)
      · exact (digit s k).injective (funext fun i => congrArg Prod.snd (h' i).1)
    obtain ⟨i, hi⟩ := hn
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

-- 读法：结论为 `∃ (M : Matrix (Bits m) (Bits m) F) (row : Out (s ^ (n + 1)) → Registers n m) (u v : Registers n m → Leg (s ^ (n + 1)) (j ^ (n + 1)) → F), ∀ e x y, entry F e x y = ∑ t, (matPower (fun _ : Fin (n + 1) => M)) (row e) t * (u t x * v t y)`。
theorem padded_power (n : ℕ) (hr : r ≤ 2 ^ m) (hs : s * s ≤ 2 ^ m)
    (h : Rectangle.RankLE F s s j r) :
    ∃ (M : Matrix (Bits m) (Bits m) F) (row : Out (s ^ (n + 1)) → Registers n m)
      (u v : Registers n m → Leg (s ^ (n + 1)) (j ^ (n + 1)) → F), ∀ e x y,
      entry F e x y = ∑ t, (matPower (fun _ : Fin (n + 1) => M)) (row e) t * (u t x * v t y) := by
  obtain ⟨M, row, u, v, he⟩ := padded hr hs h
  refine ⟨M, fun e i => row (split e i), fun t x => ∏ i, u (t i) (split x i),
    fun t y => ∏ i, v (t i) (split y i), fun e x y => ?_⟩
  rw [entry_prod]
  simp only [he, Fintype.prod_sum, prod_mul_distrib, matPower]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# 输出短和的单侧形式

在站点 0 和 1 复制输出，两个输入置于站点 2 和 3。所得张量含有两个彼此重叠的三站点标签以及一条内部连线。误差空间只需跨越切口传输一次。

**英文原文**

One-sided short output sums

Duplicate the output at sites 0 and 1 while the inputs are on 2 and 3.
The resulting tensor contains two overlapping three-site labels and
an inner wire. The error space is transmitted only once across the cut.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Spectral Finset
open scoped Classical

variable {F : Type} [Field F] {s j r p : ℕ}

-- 读法：在后续公式中，`Both` 是 `Out s × Fin j` 的缩写。
abbrev Both (s j : ℕ) := Out s × Fin j

-- 读法：`left` 的取值由 `(x.1.1, x.2)` 给出。
private def left (x : Both s j) : Leg s j := (x.1.1, x.2)
-- 读法：`right` 的取值由 `(x.1.2, x.2)` 给出。
private def right (x : Both s j) : Leg s j := (x.1.2, x.2)

-- 读法：当 `(x 0).1 = (x 1).1` 成立时取 `A (x 0).1 (left (x 2)) (right (x 3))`，否则取 `0`。
private def oneSide (A : Out s → Leg s j → Leg s j → F) (x : Fin 4 → Both s j) :=
  if (x 0).1 = (x 1).1 then A (x 0).1 (left (x 2)) (right (x 3)) else 0

-- 读法：`label` 的取值由 `Tensor.shared F {i, 0, 1} n` 给出。
def label (F : Type) [Field F] (i : Fin 4) (n : ℕ) : Tensor F (Fin 4) :=
  Tensor.shared F {i, 0, 1} n
local notation "wire" => Tensor.wire (S := Fin 4) F

-- 读法：`label F 2 s * label F 3 s * wire 2 3 j` 不超过 `Tensor.array (oneSide (s := s) (j := j) (entry F))`。
private theorem oneSide_lower [NeZero s] [NeZero j] :
    label F 2 s * label F 3 s * wire 2 3 j ≤
      Tensor.array (oneSide (s := s) (j := j) (entry F)) := by
  let a := Raw.port (n := s) ({2, 0, 1} : Finset (Fin 4))
  let b := Raw.port (n := s) ({3, 0, 1} : Finset (Fin 4))
  let c := Raw.port (n := j) ({2, 3} : Finset (Fin 4))
  let g (i : Fin 4) (t : Both s j) : Both s j := ((a i t.1.1, b i t.1.2), c i t.2)
  have hg : Tensor.signals F g = label F 2 s * label F 3 s * wire 2 3 j := by
    rw [show Tensor.signals F g = _ from
      Tensor.signals_mul (fun i (t : Out s) => (a i t.1, b i t.2)) c, Tensor.signals_mul a b]
    rfl
  rw [← hg]
  let P := Raw.ofTable (fun _ : Fin 4 => Both s j) (oneSide (entry F))
  let v (i : Fin 4) (t : Both s j) : F := if t = g i t then 1 else 0
  let L (i : Fin 4) (x y : Both s j) := if y = x then v i x else 0
  refine ⟨L, fun x => ?_⟩
  change Fin 4 → Both s j at x
  change (∑ t : Both s j, ∏ i, if x i = g i t then (1 : F) else 0) =
    ∑ t : P.term, ∏ i, ∑ y : Both s j, (if y = x i then v i (x i) else 0) * P.factor t i y
  have hv (t : P.term) (i : Fin 4) :
      (∑ y : Both s j, (if y = x i then v i (x i) else 0) * P.factor t i y) =
        v i (x i) * P.factor t i (x i) := by
    rw [Fintype.sum_eq_single (x i)]
    · simp
    · intro y h; simp [h]
  simp only [hv, prod_mul_distrib, ← mul_sum]
  rw [show (∑ t : P.term, ∏ i, P.factor t i (x i)) = _ from Raw.coeff_ofTable _ _ x]
  rw [Fintype.sum_eq_single ((x 0).1, (x 2).2)]
  · simp [oneSide, entry, left, right, v, g, a, b, c, Raw.port, Fin.prod_univ_four, Prod.ext_iff]
    grind
  · intro t ht
    by_cases he : x 0 = g 0 t
    · apply prod_eq_zero (mem_univ 2)
      refine ite_eq_right fun h => ht (Prod.ext ?_ ?_)
      · simpa [g, a, b, Raw.port] using (congrArg Prod.fst he).symm
      · simpa [g, c, Raw.port] using (congrArg Prod.snd h).symm
    · exact prod_eq_zero (mem_univ 0) (ite_eq_right he)

-- 读法：`Tensor.array (oneSide (short F u v))` 不超过 `((s * s : ℕ) : Tensor F (Fin 4)) * wire 2 3 p`。
private theorem short_le (u v : Out s → Fin p → Leg s j → F) :
    Tensor.array (oneSide (short F u v)) ≤ ((s * s : ℕ) : Tensor F (Fin 4)) * wire 2 3 p := by
  let g (i : Fin 4) (y : Both s p) : Both s p := (y.1, Raw.port {2, 3} i y.2)
  have hg : Tensor.signals F g = ((s * s : ℕ) : Tensor F (Fin 4)) * wire 2 3 p := by
    rw [show Tensor.signals F g = _ from
      Tensor.signals_mul (fun (_ : Fin 4) (e : Out s) => e) (Raw.port (n := p) {2, 3})]
    change Tensor.ofRaw (Raw.diag F (Fin 4) (Out s)) * _ = _
    rw [Tensor.diag_eq_natCast, Fintype.card_prod, Fintype.card_fin]
    rfl
  rw [← hg]
  let M (i : Fin 4) (x : Both s j) (y : Both s p) : F :=
    ![if x.1 = y.1 then 1 else 0, if x.1 = y.1 then 1 else 0,
      u y.1 y.2 (left x), v y.1 y.2 (right x)] i
  refine ⟨M, fun x => ?_⟩
  change Fin 4 → Both s j at x
  rw [Raw.coeff_ofTable]
  change oneSide _ _ = ∑ t : Both s p, ∏ i, ∑ y : Both s p,
    M i (x i) y * if y = g i t then 1 else 0
  have delta (i) (t : Both s p) :
      (∑ y : Both s p, M i (x i) y * if y = g i t then 1 else 0) = M i (x i) (g i t) := by
    rw [Fintype.sum_eq_single (g i t)]
    · simp
    · intro y hy; simp [hy]
  simp_rw [delta, Fin.prod_univ_four]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (x 0).1]
  · by_cases h : (x 1).1 = (x 0).1
    · simp [oneSide, short, g, Raw.port, M, h]
    · simp [oneSide, g, M, h, Ne.symm h]
  · intro e he
    simp [g, M, Ne.symm he]

-- 读法：`label F 2 s * label F 3 s * wire 2 3 j` 不超过 `((s * s : ℕ) : Tensor F (Fin 4)) * wire 2 3 p + wire 0 2 r * wire 0 1 (s * s * j) * wire 2 3 (s * s * j)`。
theorem Decodes.one_side (h : Decodes F s j r p) (hs : 0 < s) (hj : 0 < j) :
    label F 2 s * label F 3 s * wire 2 3 j ≤
      ((s * s : ℕ) : Tensor F (Fin 4)) * wire 2 3 p +
        wire 0 2 r * wire 0 1 (s * s * j) * wire 2 3 (s * s * j) := by
  have : NeZero s := ⟨hs.ne'⟩
  have : NeZero j := ⟨hj.ne'⟩
  obtain ⟨u, v, c, b, he⟩ := h
  let L t (x : Fin 4 → Both s j) := if (x 0).1 = (x 1).1 then c (x 0).1 t else 0
  let R t (x : Fin 4 → Both s j) := b t (left (x 2)) (right (x 3))
  let err x := ∑ t, L t x * R t x
  let g (i : Fin 4) : Fin 4 := if i.val < 2 then 0 else 2
  let E := Raw.ofTable (fun _ => Both s j) err
  -- 推导：记下中间结论 `hcut`：`Tensor.place g (Tensor.ofRaw E) ≤ wire 0 2 r`。
  have hcut : Tensor.place g (Tensor.ofRaw E) ≤ wire 0 2 r := by
    have h := Tensor.separated_le (fun _ => Both s j) err (fun i => i.val < 2) L R
      (fun _ => rfl) (fun t x y h => by unfold L; rw [h 0 (by decide), h 1 (by decide)])
      (fun t x y h => by unfold R; rw [h 2 (by decide), h 3 (by decide)]) (0 : Fin 4) 2
    rwa [Fintype.card_fin] at h
  have hg := Tensor.transport E g id
  rw [Tensor.place_id, Fin.prod_univ_four] at hg
  have hc (i : Fin 4) : Fintype.card (E.leg i) = s * s * j := by change Fintype.card (Both s j) = _; simp
  simp [hc, show g 0 = 0 from rfl, show g 1 = 0 from rfl, show g 2 = 2 from rfl, show g 3 = 2 from rfl,
    Tensor.wire_self F _ (by positivity : 0 < s * s * j)] at hg
  -- 推导：记下中间结论 `herr`：`Tensor.array err ≤ wire 0 2 r * wire 0 1 (s * s * j) * wire 2 3 (s * s * j)`。
  have herr : Tensor.array err ≤ wire 0 2 r * wire 0 1 (s * s * j) * wire 2 3 (s * s * j) := by
    rw [mul_assoc]
    apply hg.trans
    rw [mul_comm (Tensor.place _ _), mul_comm (wire 0 2 r)]
    exact Tensor.mul_le_mul_left _ _ _ hcut
  refine oneSide_lower.trans ?_
  rw [show oneSide (entry F) = fun x => oneSide (short F u v) x + err x by
    funext x
    by_cases h : (x 0).1 = (x 1).1 <;> simp [oneSide, L, R, err, h, he]]
  refine (Tensor.array_sum _ _).trans ((Tensor.add_le_add_right _ _ _ (short_le u v)).trans ?_)
  rw [add_comm _ (Tensor.array err), add_comm _ (wire 0 2 r * wire 0 1 (s * s * j) * wire 2 3 (s * s * j))]
  exact Tensor.add_le_add_right _ _ _ herr

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
单侧检验给出两个三终端标签速率之和的上界。

**英文原文**

The one-sided test bounds the sum of two three-terminal label rates.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Spectral
variable {F : Type} [Field F] {a h ε δ : ℝ}
local notation "wire" => Tensor.wire (S := Fin 4) F

-- 读法：`f (label F i n)` 等于 `(n : ℝ) ^ Tensor.values 1 f (label F i 2)`。
private theorem label_rate (f : Tensor F (Fin 4) →+* ℝ) (hf : Monotone f) (i : Fin 4)
    {n : ℕ} (hn : 0 < n) :
    f (label F i n) = (n : ℝ) ^ Tensor.values 1 f (label F i 2) := by
  have hm : Monotone (label F i) := fun _ _ h => Tensor.shared_mono F {i, 0, 1} (by simp) h
  have hu (s : ℕ) (hs : 0 < s) : 1 ≤ f (label F i s) ∧ f (label F i s) ≤ (s : ℝ) := by
    constructor
    · simpa [label, Tensor.shared_one] using hf (hm hs)
    · have he := Tensor.shared_subset F (Finset.subset_univ ({i, 0, 1} : Finset (Fin 4))) s
      rw [Tensor.shared_all] at he
      simpa [label] using hf he
  obtain ⟨p, _, _, he⟩ := TensorSpectrum.exists_power_of_monotone_multiplicative (fun n => f (label F i n))
    (fun _ _ _ _ => (congrArg f (Tensor.shared_mul F _ _ _)).trans (f.map_mul _ _))
    (fun _ _ _ h => hf (hm h)) hu
  have hp : Tensor.values 1 f (label F i 2) = p := by
    rw [Tensor.values, one_mul, he 2 (by decide), Nat.cast_ofNat, Real.log_rpow (by norm_num),
      mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hp, he n hn]

-- 读法：`Real.log L ≤ Real.log 2 + Real.log R`、`Real.log L ≤ Real.log 2 + Real.log E` 至少有一项成立。这里调用 `Real.log_le_log`。
private theorem logs {L R E : ℝ} (hl : 0 < L) (hr : 0 < R) (he : 0 < E) (h : L ≤ R + E) :
    Real.log L ≤ Real.log 2 + Real.log R ∨ Real.log L ≤ Real.log 2 + Real.log E := by
  rcases le_total E R with h' | h'
  · left
    rw [← Real.log_mul (by norm_num) hr.ne']
    exact Real.log_le_log hl (by linarith)
  · right
    rw [← Real.log_mul (by norm_num) he.ne']
    exact Real.log_le_log hl (by linarith)

-- 读法：结论为 `let L := (P (label F 2 2) + P (label F 3 2)) * Real.log s + h * Real.log j L ≤ P 2 * (Real.log 2 + 2 * Real.log s) + h * Real.log p ∨ L ≤ P 2 * Real.log 2 + a * Real.log r + 2 * h * (2 * Real.log s + Real.log j)`。
private theorem finite_cost {s j r p : ℕ} (hs : 0 < s) (hj : 0 < j) (hr : 0 < r) (hp : 0 < p)
    (H : Decodes F s j r p) {D : ℝ} {P : Tensor F (Fin 4) → ℝ}
    (hP : P ∈ Tensor.ordinary F (Fin 4) D) (ha : P (wire 0 2 2) = a)
    (hh : P (wire 0 1 2) = h) (hh' : P (wire 2 3 2) = h) :
    let L := (P (label F 2 2) + P (label F 3 2)) * Real.log s + h * Real.log j
    L ≤ P 2 * (Real.log 2 + 2 * Real.log s) + h * Real.log p ∨
      L ≤ P 2 * Real.log 2 + a * Real.log r + 2 * h * (2 * Real.log s + Real.log j) := by
  obtain ⟨d, hd, f, hf, rfl⟩ := hP
  have ht := hf (H.one_side hs hj)
  rw [f.map_add, f.map_mul, f.map_mul, f.map_mul, f.map_mul, f.map_mul, map_natCast f] at ht
  simp only [label_rate f hf _ hs, Tensor.price_wire f hf _ _ hj,
    Tensor.price_wire f hf _ _ hp, Tensor.price_wire f hf _ _ hr,
    Tensor.price_wire f hf _ _ (by positivity : 0 < s * s * j), Nat.cast_mul] at ht
  have he := logs (by positivity) (by positivity) (by positivity) ht
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow] at he
  -- 推导：记下中间结论 `htwo`：`Tensor.values d f 2 = d`。
  have htwo : Tensor.values d f 2 = d := by
    rw [Tensor.values, map_ofNat, div_self (Real.log_pos (by norm_num)).ne', mul_one]
  change d * Tensor.dist f 0 2 = a at ha
  change d * Tensor.dist f 0 1 = h at hh
  change d * Tensor.dist f 2 3 = h at hh'
  have hm (i : Fin 4) : d * Tensor.values 1 f (label F i 2) = Tensor.values d f (label F i 2) := by
    simp [Tensor.values]
  dsimp only
  rw [htwo]
  rcases he with he | he
  all_goals
    have he' := mul_le_mul_of_nonneg_left he hd.1
    simp only [mul_add, ← mul_assoc, hm, ha, hh, hh'] at he'
  · exact .inl (by linarith only [he'])
  · exact .inr (by linarith only [he'])

-- 读法：`P (label F 2 2) + P (label F 3 2) + (1 / 2 - ε) * h` 不超过 `2 * P 2`。
theorem one_rate
    (H : ∀ n : ℕ, ∃ s j r p : ℕ, n ≤ s ∧ 0 < r ∧ 0 < p ∧ (s : ℝ) ^ (1 / 2 - ε) * p ≤ j ∧
      (r : ℝ) ≤ (s : ℝ) ^ (2 - δ) ∧ j ≤ s ^ 3 ∧ Decodes F s j r p)
    {D : ℝ} {P : Tensor F (Fin 4) → ℝ} (hP : P ∈ Tensor.ordinary F (Fin 4) D)
    (ha : P (wire 0 2 2) = a) (hh : P (wire 0 1 2) = h) (hh' : P (wire 2 3 2) = h)
    (ha' : 0 ≤ a) (hh₀ : 0 ≤ h) (hgap : 7 * h < a * δ)
    (hlo : 2 * a ≤ P (label F 2 2) + P (label F 3 2)) :
    P (label F 2 2) + P (label F 3 2) + (1 / 2 - ε) * h ≤ 2 * P 2 := by
  by_contra! bad
  let L := P (label F 2 2) + P (label F 3 2) + (1 / 2 - ε) * h - 2 * P 2
  -- 推导：记下中间结论 `h₁`：`0 < L`。
  have h₁ : 0 < L := sub_pos.mpr bad
  have h₂ := sub_pos.mpr hgap
  let B := P 2 * Real.log 2
  let M := max (B / L) (B / (a * δ - 7 * h))
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp M)
  obtain ⟨s, j, r, p, hs, hr, hp, hj, hr', hc, hd⟩ := H n
  have hm := hn.trans_le (Nat.cast_le.mpr hs : (n : ℝ) ≤ s)
  have hs' := (Real.exp_pos M).trans hm
  have he : 0 < (s : ℝ) ^ (1 / 2 - ε) * p := by positivity
  have hj' := he.trans_le hj
  have hl := (Real.lt_log_iff_exp_lt hs').mpr hm
  have hL := (div_lt_iff₀ h₁).mp ((le_max_left _ _).trans_lt hl)
  have hR := (div_lt_iff₀ h₂).mp ((le_max_right _ _).trans_lt hl)
  rcases finite_cost (Nat.cast_pos.mp hs') (Nat.cast_pos.mp hj') hr hp hd hP ha hh hh' with h | h
  · have hv := Real.log_le_log he hj
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hs'] at hv
    unfold L B at hL
    linarith only [h, hL, mul_le_mul_of_nonneg_left hv hh₀]
  · have ht := Real.log_le_log (Nat.cast_pos.mpr hr) hr'
    have hu := Real.log_le_log hj' (show (j : ℝ) ≤ (s : ℝ) ^ 3 by exact_mod_cast hc)
    rw [Real.log_pow, Nat.cast_ofNat] at hu
    rw [Real.log_rpow hs'] at ht
    unfold B at hR
    linarith only [h, hR, mul_le_mul_of_nonneg_left hu hh₀, mul_le_mul_of_nonneg_left ht ha',
      mul_le_mul_of_nonneg_right hlo (show 0 ≤ Real.log (s : ℝ) by positivity)]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end
