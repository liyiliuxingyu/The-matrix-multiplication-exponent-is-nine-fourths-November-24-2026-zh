-- 本文件所属证明环节：在有理函数域中对一般算术电路作双线性化，从计算矩阵乘积的程序提取秩分解并界定长度。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model
import OAI.LinearAlgebra.MatrixExponent.Derivatives
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# 在有理函数域中作双线性化

追踪每条可用连线相对于左右两类变量的混合偏导矩阵。每个门至多为公共张成族增加两个外积。在泛点处工作，除法就无须从基域选择取值有定义的点，也无须在特征二下进行极化。

**英文原文**

Bilinearization in the rational function field

Track the matrix of mixed left/right partials of each available wire. A gate
enlarges a common spanning family by at most two outer products. Work at the
generic point, so division never requires choosing a regular point in the
ground field. This also avoids polarization in characteristic two.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {I J K : ℕ}

-- 读法：在后续公式中，`Factors` 是 `(Pos I K → Rat F I J K) × (Pos K J → Rat F I J K)` 的缩写。
private abbrev Factors (F : Type*) [Field F] (I J K : ℕ) :=
  (Pos I K → Rat F I J K) × (Pos K J → Rat F I J K)

-- 读法：`outer` 的取值由 `v.1 i * v.2 j` 给出。
private def outer (v : Factors F I J K) (i : Pos I K) (j : Pos K J) : Rat F I J K := v.1 i * v.2 j

-- 读法：`cross` 的取值由 `(fun i => partialD (.inl i) x, fun j => partialD (.inr j) y)` 给出。
private def cross (x y : Rat F I J K) : Factors F I J K :=
  (fun i => partialD (.inl i) x, fun j => partialD (.inr j) y)

-- 读法：`mixed` 的取值由 `partialD (.inl i) (partialD (.inr j) x)` 给出。
private def mixed (x : Rat F I J K) (i : Pos I K) (j : Pos K J) : Rat F I J K :=
  partialD (.inl i) (partialD (.inr j) x)

-- 读法：`mixed (x * y)` 等于 `y • mixed x + (x • mixed y + (outer (cross x y) + outer (cross y x)))`。用函数外延性比较等号两侧在 `i j` 处的取值。
private theorem mixed_mul (x y : Rat F I J K) :
    mixed (x * y) = y • mixed x + (x • mixed y + (outer (cross x y) + outer (cross y x))) := by
  funext i j
  simp only [mixed, Derivation.leibniz, smul_eq_mul, map_add, Pi.add_apply,
    Pi.smul_apply, outer, cross]
  ring

-- 读法：`mixed (output F p) i j` 等于 `if i.1 = p.1 ∧ i.2 = j.1 ∧ j.2 = p.2 then 1 else 0`。按 `j.2 = p.2 <;>` 成立与否分情况。
private theorem mixed_output (i : Pos I K) (j : Pos K J) (p : Pos I J) :
    mixed (output F p) i j =
      if i.1 = p.1 ∧ i.2 = j.1 ∧ j.2 = p.2 then 1 else 0 := by
  have hy : partialD (.inr j) (output F p) =
      if j.2 = p.2 then input F (.inl (p.1, j.1)) else 0 := by
    by_cases h : j.2 = p.2 <;>
      simp [output, map_sum, Derivation.leibniz, smul_eq_mul, input, partialD_X,
        Prod.ext_iff, h, mul_ite]
  rw [mixed, hy]
  by_cases h : j.2 = p.2 <;> simp [h, input, partialD_X, Prod.ext_iff]

-- 读法：`Covered` 表示以下条件：存在 `v : Fin d → Factors F I J K`，对每个 `x ∈ T`，`mixed x` 属于 `Submodule.span (Rat F I J K) (Set.range fun i => outer (v i))`。
private def Covered (T : Set (Rat F I J K)) (d : ℕ) : Prop :=
  ∃ v : Fin d → Factors F I J K, ∀ x ∈ T,
    mixed x ∈ Submodule.span (Rat F I J K) (Set.range fun i => outer (v i))

-- 读法：要证明的命题是 `Covered (insert z T) (d + 2)`。这里调用 `Submodule.span_le.mpr`。
private theorem Covered.step {T : Set (Rat F I J K)} {d : ℕ} (h : Covered T d)
    {z : Rat F I J K} (a b : Rat F I J K)
    (hz : ∀ U : Submodule (Rat F I J K) (Pos I K → Pos K J → Rat F I J K),
      (∀ x ∈ T, mixed x ∈ U) → outer (cross a b) ∈ U → outer (cross b a) ∈ U → mixed z ∈ U) :
    Covered (insert z T) (d + 2) := by
  obtain ⟨v, hv⟩ := h
  let w : Fin (d + 2) → Factors F I J K := Fin.cons (cross a b) (Fin.cons (cross b a) v)
  let U := Submodule.span (Rat F I J K) (Set.range fun i => outer (w i))
  have hw (i) : outer (w i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
  have hold : Submodule.span (Rat F I J K) (Set.range fun i => outer (v i)) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simpa [w] using hw i.succ.succ
  refine ⟨w, ?_⟩
  rintro x (rfl | hx)
  · exact hz U (fun x hx => hold (hv x hx)) (hw 0) (hw (Fin.succ 0))
  · exact hold (hv x hx)

-- 读法：要证明的命题是 `Covered T (2 * m)`。对 `h` 作归纳。
private theorem covered_build {m : ℕ} {T : Set (Rat F I J K)}
    (h : Build (initial F I J K) m T) : Covered T (2 * m) := by
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
  | @add m T x y _ hx hy ih =>
    apply ih.step x y
    intro U hu _ _
    -- 推导：记下中间结论 `he`：`mixed (x + y) = mixed x + mixed y`。
    have he : mixed (x + y) = mixed x + mixed y := by funext i j; simp [mixed]
    rw [he]
    exact U.add_mem (hu x hx) (hu y hy)
  | @sub m T x y _ hx hy ih =>
    apply ih.step x y
    intro U hu _ _
    have he : mixed (x - y) = mixed x - mixed y := by funext i j; simp [mixed]
    rw [he]
    exact U.sub_mem (hu x hx) (hu y hy)
  | @mul m T x y _ hx hy ih =>
    apply ih.step x y
    intro U hu ha hb
    rw [mixed_mul]
    exact U.add_mem (U.smul_mem y (hu x hx)) (U.add_mem (U.smul_mem x (hu y hy)) (U.add_mem ha hb))
  | @div m T x y _ hx hy hne ih =>
    apply ih.step (x / y) y
    intro U hu ha hb
    -- 推导：记下中间结论 `hm`：`mixed ((x / y) * y) ∈ U`。
    have hm : mixed ((x / y) * y) ∈ U := by rw [div_mul_cancel₀ _ hne]; exact hu x hx
    rw [mixed_mul] at hm
    have hr := U.sub_mem hm (U.add_mem (U.smul_mem (x / y) (hu y hy)) (U.add_mem ha hb))
    rw [add_sub_cancel_right] at hr
    simpa [smul_smul, hne] using U.smul_mem y⁻¹ hr

-- 读法：在 `(Rat F I J K)` 上，三个尺寸为 `I`、`J`、`K` 的矩阵乘法张量的秩至多为 `(2 * m)`。
/-- 在由输入生成的有理函数域上，乘法张量的秩至多为算术成本的两倍。

英文原文：The multiplication tensor has rank at most twice the arithmetic cost over
the rational function field of the inputs.
-/
theorem bilinearize {m : ℕ} (h : Computes F I J K m) : RankLE (Rat F I J K) I J K (2 * m) := by
  obtain ⟨T, hT, hout⟩ := h
  obtain ⟨v, hv⟩ := covered_build hT
  have hc (p : Pos I J) := (Submodule.mem_span_range_iff_exists_fun _).mp (hv _ (hout p))
  choose c he using hc
  refine ⟨fun l => (v l).1, fun l => (v l).2, fun l p => c p l, ?_⟩
  intro i j p
  rw [← mixed_output i j p, ← he p]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, outer]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：在 `(Rat F n)` 上，边长为 `n` 的矩阵乘法张量的秩至多为 `(2 * m)`。使用 `Rectangle.bilinearize` 给出的结论。
theorem bilinearize {F : Type*} [Field F] {n m : ℕ} (h : Computes F n m) :
    RankLE (Rat F n) n (2 * m) :=
  Rectangle.bilinearize h

end OAI.LinearAlgebra.MatrixExponent
