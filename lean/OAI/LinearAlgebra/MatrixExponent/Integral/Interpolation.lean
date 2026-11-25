-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Nodes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# 代数整数上的多项式插值

**英文原文**

Polynomial interpolation over algebraic integers
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Finset Polynomial Matrix
open scoped Classical

-- 读法：存在 `v : Fin n → O`，`IsUnit (vandermonde v).det` 与 `∀ i, IsUnit (v i)` 同时成立。
theorem unit_nodes (n : ℕ) : ∃ v : Fin n → O,
    IsUnit (vandermonde v).det ∧ ∀ i, IsUnit (v i) := by
  obtain ⟨x, hx, h⟩ := nodes n
  exact ⟨_, h, fun i => hx.pow i.val⟩

-- 读法：当 `h : d < n` 成立时取 `(vandermonde v)⁻¹ ⟨d, h⟩ i`，否则取 `0`。
def weight {n : ℕ} (v : Fin n → O) (i : Fin n) (d : ℕ) :=
  if h : d < n then (vandermonde v)⁻¹ ⟨d, h⟩ i else 0

-- 读法：`p.coeff d` 等于 `∑ i, p.eval (v i) * weight v i d`。按 `d < n` 成立与否分情况。
theorem interpolate {n : ℕ} (v : Fin n → O) (h : IsUnit (vandermonde v).det)
    (p : Polynomial O) (d : ℕ) (hd : p.degree < Fintype.card (Fin n)) :
    p.coeff d = ∑ i, p.eval (v i) * weight v i d := by
  rw [Fintype.card_fin] at hd
  by_cases hd' : d < n
  · by_cases hp : p = 0
    · simp [hp]
    let a (i : Fin n) := p.coeff i.val
    let b (i : Fin n) := p.eval (v i)
    have he : (vandermonde v).mulVec a = b := by
      funext i
      unfold b
      rw [eval_eq_sum_range' ((natDegree_lt_iff_degree_lt hp).mpr hd), ← Fin.sum_univ_eq_sum_range]
      change (∑ j : Fin n, v i ^ j.val * a j) = ∑ j : Fin n, a j * v i ^ j.val
      exact sum_congr rfl (fun j _ => mul_comm (v i ^ j.val) (a j))
    -- 推导：记下中间结论 `hh`：`(vandermonde v)⁻¹.mulVec b = a`。
    have hh : (vandermonde v)⁻¹.mulVec b = a := by
      rw [← he, mulVec_mulVec, nonsing_inv_mul _ h, one_mulVec]
    have heq := congrFun hh ⟨d, hd'⟩
    simpa only [a, b, weight, dite_eq_left hd', Matrix.mulVec, dotProduct, mul_comm] using heq.symm
  · simp only [weight, dite_eq_right hd', mul_zero, sum_const_zero]
    exact coeff_eq_zero_of_degree_lt (hd.trans_le (by exact_mod_cast Nat.le_of_not_gt hd'))

/-- 指数非负时可直接取幂；负整次幂只用于可逆元。

英文原文：These integer powers are used only on units, apart from
nonnegative exponents.
-/
scoped instance : Pow O ℤ := ⟨fun x i => if h : IsUnit x then ((h.unit ^ i : Oˣ) : O) else x ^ i.toNat⟩

-- 读法：`x ^ (i + j)` 等于 `x ^ i * x ^ j`。
theorem upow_add {x : O} (h : IsUnit x) (i j : ℤ) : x ^ (i + j) = x ^ i * x ^ j := by
  change (if h : IsUnit x then ((h.unit ^ (i + j) : Oˣ) : O) else _) =
    (if h : IsUnit x then ((h.unit ^ i : Oˣ) : O) else _) * (if h : IsUnit x then ((h.unit ^ j : Oˣ) : O) else _)
  simp only [dite_eq_left h, zpow_add, Units.val_mul]

-- 读法：`x ^ (i : ℤ)` 等于 `x ^ i`。
theorem upow_nat (x : O) (i : ℕ) : x ^ (i : ℤ) = x ^ i := by
  change (if h : IsUnit x then ↑(h.unit ^ (i : ℤ)) else x ^ _) = _
  split <;> simp

-- 读法：存在 `(ζ : O) (w : Fin (6 * M) → O)`，使 `IsUnit ζ ∧ ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) → (∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0` 成立。
/-- 平移带符号指数，使其落入长度为分支数六倍的区间，再通过插值提取中央系数。

英文原文：Shift signed exponents into a range of length six times the
branch count. Interpolation extracts the central coefficient.
-/
theorem phases {M : ℕ} (_hM : 0 < M) :
    ∃ (ζ : O) (w : Fin (6 * M) → O), IsUnit ζ ∧
      ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
        (∑ r : Fin (6 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0 := by
  obtain ⟨ζ, hζ, h⟩ := nodes (6 * M)
  let v := fun i : Fin (6 * M) => ζ ^ i.val
  refine ⟨ζ, fun i => weight v i (3 * M) * ζ ^ ((i : ℤ) * (3 * M)), hζ, fun e hlo hhi => ?_⟩
  let n := (3 * (M : ℤ) + e).toNat
  have hn : (n : ℤ) = 3 * M + e := by unfold n; omega
  have hc := interpolate v h (X ^ n) (3 * M) (by
    rw [degree_X_pow, Fintype.card_fin]
    exact_mod_cast (show n < 6 * M by omega))
  rw [coeff_X_pow] at hc
  simp only [eval_pow, eval_X] at hc
  calc
    _ = ∑ i, v i ^ n * weight v i (3 * M) := by
      apply sum_congr rfl
      intro i _
      rw [mul_assoc, ← upow_add hζ, ← mul_add, ← hn, ← Nat.cast_mul, upow_nat, pow_mul, mul_comm]
    _ = _ := by rw [← hc]; congr 1; exact propext (by omega)

end OAI.LinearAlgebra.MatrixExponent.Integral
