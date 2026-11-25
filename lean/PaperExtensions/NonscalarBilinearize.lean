import PaperExtensions.NonscalarModel
import OAI.LinearAlgebra.MatrixExponent.Derivatives
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# 只按非标量乘除门计数的双线性化

在输入变量的有理函数域中，跟踪每条线的「先对右输入、再对左输入求导」矩阵。
维持一个供所有线共用的秩一矩阵族。加减、乘域常数和除以非零域常数都
保持原有张成空间。遇到一个计费门时，向矩阵族添入至多两个外积。
除法使用商乘以除数等于被除数这一恒等式，所以任意特征均适用。

这里沿用上游 `MatrixExponent.Bilinearize` 对泛点形式偏导的处理，并把它的归纳
不变量改为按非标量门计数。输出的秩分解定义在有理函数扩域上。
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type*} [Field F] {n : ℕ}

-- 每个外积由左输入和右输入上的两组系数给出。
private abbrev Factors (F : Type*) [Field F] (n : ℕ) :=
  (Pos n → Rat F n) × (Pos n → Rat F n)

private def outer (v : Factors F n) (i j : Pos n) : Rat F n := v.1 i * v.2 j

private def cross (x y : Rat F n) : Factors F n :=
  (fun i => partialD (.inl i) x, fun j => partialD (.inr j) y)

private def mixed (x : Rat F n) (i j : Pos n) : Rat F n :=
  partialD (.inl i) (partialD (.inr j) x)

-- 两次运用莱布尼茨法则。两项是旧矩阵的标量倍，另外两项各是一个外积。
private theorem mixed_mul (x y : Rat F n) :
    mixed (x * y) = y • mixed x + (x • mixed y + (outer (cross x y) + outer (cross y x))) := by
  funext i j
  simp only [mixed, Derivation.leibniz, smul_eq_mul, map_add, Pi.add_apply,
    Pi.smul_apply, outer, cross]
  ring

-- 基域常数在各输入方向的偏导都为零，所以标量乘法不需要新的外积。
private theorem mixed_scalar_mul (c : F) (x : Rat F n) :
    mixed (algebraMap F (Rat F n) c * x) = algebraMap F (Rat F n) c • mixed x := by
  funext i j
  simp [mixed, Derivation.leibniz, smul_eq_mul]

-- 输出项的混合偏导恰好读出矩阵乘法张量的一项 0–1 系数。
private theorem mixed_output (i j p : Pos n) :
    mixed (output F p) i j =
      if i.1 = p.1 ∧ i.2 = j.1 ∧ j.2 = p.2 then 1 else 0 := by
  have hy : partialD (.inr j) (output F p) =
      if j.2 = p.2 then input F (.inl (p.1, j.1)) else 0 := by
    by_cases h : j.2 = p.2 <;>
      simp [output, map_sum, Derivation.leibniz, smul_eq_mul, input, partialD_X,
        Prod.ext_iff, h, mul_ite]
  rw [mixed, hy]
  by_cases h : j.2 = p.2 <;> simp [h, input, partialD_X, Prod.ext_iff]

/-- 所有已获得的线，其混合偏导均落在同一族 `d` 个外积张成的空间中。 -/
private def Covered (T : Set (Rat F n)) (d : ℕ) : Prop :=
  ∃ v : Fin d → Factors F n, ∀ x ∈ T,
    mixed x ∈ Submodule.span (Rat F n) (Set.range fun i => outer (v i))

-- 新线已在原空间中时，原有的同一族外积可直接保留。
private theorem Covered.free {T : Set (Rat F n)} {d : ℕ} (h : Covered T d) {z : Rat F n}
    (hz : ∀ U : Submodule (Rat F n) (Pos n → Pos n → Rat F n),
      (∀ x ∈ T, mixed x ∈ U) → mixed z ∈ U) : Covered (insert z T) d := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, ?_⟩
  rintro x (rfl | hx)
  · exact hz _ hv
  · exact hv x hx

-- 一个计费门采用两个新的外积，旧的 `d` 个外积仍可用于所有旧线。
private theorem Covered.step {T : Set (Rat F n)} {d : ℕ} (h : Covered T d)
    {z : Rat F n} (a b : Rat F n)
    (hz : ∀ U : Submodule (Rat F n) (Pos n → Pos n → Rat F n),
      (∀ x ∈ T, mixed x ∈ U) → outer (cross a b) ∈ U → outer (cross b a) ∈ U → mixed z ∈ U) :
    Covered (insert z T) (d + 2) := by
  obtain ⟨v, hv⟩ := h
  let w : Fin (d + 2) → Factors F n := Fin.cons (cross a b) (Fin.cons (cross b a) v)
  let U := Submodule.span (Rat F n) (Set.range fun i => outer (w i))
  have hw (i) : outer (w i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
  have hold : Submodule.span (Rat F n) (Set.range fun i => outer (v i)) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simpa [w] using hw i.succ.succ
  refine ⟨w, ?_⟩
  rintro x (rfl | hx)
  · exact hz U (fun x hx => hold (hv x hx)) (hw 0) (hw (Fin.succ 0))
  · exact hold (hv x hx)

private theorem covered_nonscalar_build {m q : ℕ} {T : Set (Rat F n)}
    (h : NonscalarBuild F (initial F n) m q T) : Covered T (2 * q) := by
  induction h with
  | nil =>
    refine ⟨Fin.elim0, fun x hx => ?_⟩
    have hz : mixed x = 0 := by
      funext i j
      rcases hx with ⟨c, rfl⟩ | ⟨k, rfl⟩
      · simp [mixed]
      · simp only [mixed, input, partialD_X]
        split_ifs <;> simp
    rw [hz]
    exact Submodule.zero_mem _
  | @add m q T x y _ hx hy ih =>
    apply ih.free
    intro U hu
    have he : mixed (x + y) = mixed x + mixed y := by funext i j; simp [mixed]
    rw [he]
    exact U.add_mem (hu x hx) (hu y hy)
  | @sub m q T x y _ hx hy ih =>
    apply ih.free
    intro U hu
    have he : mixed (x - y) = mixed x - mixed y := by funext i j; simp [mixed]
    rw [he]
    exact U.sub_mem (hu x hx) (hu y hy)
  | @mulScalarLeft m q T x y _ hx hy hs ih =>
    obtain ⟨c, rfl⟩ := hs
    apply ih.free
    intro U hu
    rw [mixed_scalar_mul]
    exact U.smul_mem _ (hu y hy)
  | @mulScalarRight m q T x y _ hx hy hs ih =>
    obtain ⟨c, rfl⟩ := hs
    apply ih.free
    intro U hu
    rw [mul_comm x, mixed_scalar_mul]
    exact U.smul_mem _ (hu x hx)
  | @divScalar m q T x y _ hx hy hne hs ih =>
    obtain ⟨c, rfl⟩ := hs
    apply ih.free
    intro U hu
    have he : x / algebraMap F (Rat F n) c = algebraMap F (Rat F n) c⁻¹ * x := by
      simp [div_eq_mul_inv, mul_comm]
    rw [he, mixed_scalar_mul]
    exact U.smul_mem _ (hu x hx)
  | @mul m q T x y _ hx hy _ _ ih =>
    apply ih.step x y
    intro U hu ha hb
    rw [mixed_mul]
    exact U.add_mem (U.smul_mem y (hu x hx)) (U.add_mem (U.smul_mem x (hu y hy)) (U.add_mem ha hb))
  | @div m q T x y _ hx hy hne _ ih =>
    -- 令 f = x/y，将 x = f*y 代入乘积公式，再乘以非零除数的逆元。
    apply ih.step (x / y) y
    intro U hu ha hb
    have hm : mixed ((x / y) * y) ∈ U := by rw [div_mul_cancel₀ _ hne]; exact hu x hx
    rw [mixed_mul] at hm
    have hr := U.sub_mem hm (U.add_mem (U.smul_mem (x / y) (hu y hy)) (U.add_mem ha hb))
    rw [add_sub_cancel_right] at hr
    simpa [smul_smul, hne] using U.smul_mem y⁻¹ hr

/-- 若一个具体计算序列使用 `q` 个非标量乘除门，并输出所有矩阵乘积项，
则泛点上的矩阵乘法张量具有至多 `2q` 项的精确分解。 -/
theorem rank_of_nonscalar_build {m q : ℕ} {T : Set (Rat F n)}
    (h : NonscalarBuild F (initial F n) m q T) (hout : ∀ p : Pos n, output F p ∈ T) :
    RankLE (Rat F n) n (2 * q) := by
  obtain ⟨v, hv⟩ := covered_nonscalar_build h
  have hc (p : Pos n) := (Submodule.mem_span_range_iff_exists_fun _).mp (hv _ (hout p))
  choose c he using hc
  refine ⟨fun l => (v l).1, fun l => (v l).2, fun l p => c p l, ?_⟩
  intro i j p
  rw [← mixed_output i j p, ← he p]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, outer]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- 论文引理 2.4 的有理函数域版本。`q` 仅计数非标量乘法和除法。 -/
theorem bilinearize_nonscalar {F : Type*} [Field F] {n q : ℕ} (h : ComputesNonscalar F n q) :
    RankLE (Rat F n) n (2 * q) := by
  obtain ⟨m, T, hT, hout⟩ := h
  exact rank_of_nonscalar_build hT hout

end OAI.LinearAlgebra.MatrixExponent
