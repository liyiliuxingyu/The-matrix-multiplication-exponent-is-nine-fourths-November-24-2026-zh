-- 本文件所属证明环节：逐条刻画无除法矩阵程序的正确性，验证计算一个标量乘积的程序，并控制矩形输入内维 innerSize 的单调性、正性和实数幂上界。
import OAI.LinearAlgebra.MatrixMultiplication.Model
import OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-!
域上的无除法算术程序及其运算次数。

**英文原文**

Division-free arithmetic programs over a field and their operation counts.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {F Input Register : Type*}

end Gate

namespace Program

variable {F Input : Type*}

-- 读法：`(p.step g).eval inputs 0` 等于 `g.eval inputs (p.eval inputs)`。两端由定义化简为同一项。
@[simp] theorem eval_step_zero [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

-- 读法：`(p.step g).eval inputs i.succ` 等于 `p.eval inputs i`。两端由定义化简为同一项。
@[simp] theorem eval_step_succ [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

-- 读法：`(p.step g).cost` 等于 `p.cost + g.cost`。两端由定义化简为同一项。
@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

-- 读法：用函数外延性比较等号两侧在 `i k` 处的取值。
theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

-- 读法：用字段 `registers`、`program`、`output` 构造 `MatrixAlgorithm F 1 1 1`。
def scalarAlgorithm (F : Type*) [Field F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

-- 读法：要证明的命题是 `(scalarAlgorithm F).Correct`。用函数外延性比较等号两侧在 `i k` 处的取值。
theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

-- 读法：`1` 不超过 `innerSize n k`。这里调用 `Nat.one_le_ceil_iff.mpr`。
-- 读法：`(scalarAlgorithm F).cost` 等于 `1`。两端由定义化简为同一项。
@[simp] theorem scalarAlgorithm_cost (F : Type*) [Field F] : (scalarAlgorithm F).cost = 1 := rfl

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

-- 读法：`innerSize n 0` 等于 `1`。
@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

-- 读法：`innerSize n 1` 等于 `n`。
@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

-- 读法：`innerSize n k` 不超过 `innerSize n l`。这里调用 `Nat.ceil_mono`。
theorem innerSize_mono {n : ℕ} (hn : 1 ≤ n) {k l : ℝ} (hkl : k ≤ l) :
    innerSize n k ≤ innerSize n l := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hkl)

-- 读法：`innerSize n k` 不超过 `b ^ t`。这里调用 `Nat.ceil_le.mpr`。
theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

-- 读法：`(innerSize n k : ℝ)` 不超过 `2 * (n : ℝ) ^ k`。
theorem innerSize_cast_le {n : ℕ} (hn : 1 ≤ n) {k : ℝ} (hk : 0 ≤ k) :
    (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  have hpow : 1 ≤ (n : ℝ) ^ k := Real.one_le_rpow (by exact_mod_cast hn) hk
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) k)).le
  change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
  linarith

end MatrixMultiplication.Arithmetic

end

end OAI
