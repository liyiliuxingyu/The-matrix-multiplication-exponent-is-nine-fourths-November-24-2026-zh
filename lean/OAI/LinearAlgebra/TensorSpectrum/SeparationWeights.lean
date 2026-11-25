-- 本文件所属证明环节：以 5M 为相位模数，证明有限标签投影时不会回绕成额外的零项。把保留的 Laurent 权重写成平方，说明其恰在两个标签相等时为零并给出上界。
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 辅助分离所用的整数相位与权重

标签区间内不存在相位模数 `5M` 的非零倍数。投影后，洛朗权重为一个平方，且恰在猜测的扇区与辅助标签一致时为零。这些都是局部恒等式；张量分离及其标签不等式有待进一步证明。

**英文原文**

Integer phases and weights for auxiliary separation

The phase modulus `5M` has no nonzero multiple on the label interval. After
projection, the Laurent weight is a square and vanishes exactly when the
sector guess and the auxiliary labels agree. These are local identities;
they do not assert the tensor separation or its tag inequality.
-/

namespace OAI.LinearAlgebra.TensorSpectrum.Separation

-- 读法：要证明的命题是 `(N ∣ x ↔ x = 0)`。按 `k = 0` 成立与否分情况。
theorem dvd_iff_eq_zero_of_bounds (N x : ℤ) (hN : 0 < N)
    (hlo : -N < x) (hhi : x < N) : (N ∣ x ↔ x = 0) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hzero : k = 0
    · simp [hzero] at hk
      exact hk
    · rcases lt_or_gt_of_ne hzero with hneg | hpos
      · have hmul := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hN.le
        nlinarith
      · have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) hN.le
        nlinarith
  · rintro rfl
    exact dvd_zero N

-- 读法：要证明的命题是 `((5 * M ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0)`。这里调用 `dvd_iff_eq_zero_of_bounds`。
/-- 论文使用的从一开始编号的标签约定。

英文原文：The paper's one-based label convention.
-/
theorem projection_does_not_wrap
    (M h g u v : ℤ)
    (hM : 1 ≤ M) (hh0 : 1 ≤ h) (hhM : h ≤ M)
    (hg0 : 1 ≤ g) (hgM : g ≤ M)
    (hu0 : 1 ≤ u) (huM : u ≤ M)
    (hv0 : 1 ≤ v) (hvM : v ≤ M) :
    ((5 * M ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0) := by
  exact dvd_iff_eq_zero_of_bounds (5 * M) (u - v + 2 * (g - h))
    (by omega) (by omega) (by omega)

-- 读法：要证明的命题是 `((5 * (M : ℤ) ∣ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)) ↔ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val) = 0)`。这里调用 `dvd_iff_eq_zero_of_bounds`。
/-- 对从零编号的有限标签给出相同的无回绕性质。

英文原文：The same no-wrap property for finite labels numbered from zero.
-/
theorem projection_does_not_wrap_fin {M : ℕ} (h g u v : Fin M) :
    ((5 * (M : ℤ) ∣ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)) ↔
      (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val) = 0) := by
  have hh := h.isLt
  have hg := g.isLt
  have hu := u.isLt
  have hv := v.isLt
  exact dvd_iff_eq_zero_of_bounds (5 * (M : ℤ))
    ((u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val))
    (by omega) (by omega) (by omega)

-- 读法：`g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2` 与 `0 ≤ g ^ 2 + h * u - h ^ 2 - h * v ∧ (g ^ 2 + h * u - h ^ 2 - h * v = 0 ↔ g = h ∧ u = v)` 同时成立。这里调用 `sq_nonneg`。
/-- 权重恒等式与标签从零还是从一开始编号无关。

英文原文：The weight identity is independent of the choice of zero- or one-based
labels.
-/
theorem projected_square_weight
    (h g u v : ℤ) (hphase : u - v + 2 * (g - h) = 0) :
    g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2 ∧
    0 ≤ g ^ 2 + h * u - h ^ 2 - h * v ∧
    (g ^ 2 + h * u - h ^ 2 - h * v = 0 ↔ g = h ∧ u = v) := by
  have hweight : g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2 := by
    calc
      g ^ 2 + h * u - h ^ 2 - h * v =
          (g - h) ^ 2 + h * (u - v + 2 * (g - h)) := by ring
      _ = (g - h) ^ 2 := by rw [hphase]; ring
  refine ⟨hweight, ?_, ?_⟩
  · rw [hweight]
    exact sq_nonneg _
  · rw [hweight]
    constructor
    · intro hz
      -- 推导：记下中间结论 `hdiff`：`g - h = 0`。
      have hdiff : g - h = 0 := sq_eq_zero_iff.mp hz
      constructor <;> omega
    · rintro ⟨rfl, rfl⟩
      simp

-- 读法：`squareExponent` 的取值由 `Int.toNat (((g.val : ℤ) - h.val) ^ 2)` 给出。
/-- 傅里叶投影后使用的非负指数。

英文原文：The nonnegative exponent used after the Fourier projection.
-/
def squareExponent {M : ℕ} (g h : Fin M) : ℕ :=
  Int.toNat (((g.val : ℤ) - h.val) ^ 2)

-- 读法：`squareExponent g h = 0` 与 `g = h` 等价。按 `Fin.ext` 的外延性准则比较各分量。
theorem squareExponent_eq_zero_iff {M : ℕ} (g h : Fin M) :
    squareExponent g h = 0 ↔ g = h := by
  constructor
  · intro he
    have hnonneg : 0 ≤ ((g.val : ℤ) - h.val) ^ 2 := sq_nonneg _
    have hz : ((g.val : ℤ) - h.val) ^ 2 = 0 := by
      unfold squareExponent at he
      omega
    have hdiff : (g.val : ℤ) - h.val = 0 := sq_eq_zero_iff.mp hz
    apply Fin.ext
    omega
  · rintro rfl
    simp [squareExponent]

-- 读法：`squareExponent g h` 不超过 `(M - 1) ^ 2`。
theorem squareExponent_le {M : ℕ} (g h : Fin M) :
    squareExponent g h ≤ (M - 1) ^ 2 := by
  have hg := g.isLt
  have hh := h.isLt
  have hlow : -((M - 1 : ℕ) : ℤ) ≤ (g.val : ℤ) - h.val := by omega
  have hhigh : (g.val : ℤ) - h.val ≤ ((M - 1 : ℕ) : ℤ) := by omega
  have hprod :
      0 ≤ (((M - 1 : ℕ) : ℤ) - ((g.val : ℤ) - h.val)) *
        (((M - 1 : ℕ) : ℤ) + ((g.val : ℤ) - h.val)) :=
    mul_nonneg (by omega) (by omega)
  have hsq : ((g.val : ℤ) - h.val) ^ 2 ≤ (((M - 1 : ℕ) : ℤ)) ^ 2 := by
    nlinarith
  have hcast : ((g.val : ℤ) - h.val) ^ 2 ≤ (((M - 1) ^ 2 : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow] using hsq
  unfold squareExponent
  omega

end OAI.LinearAlgebra.TensorSpectrum.Separation
