-- 本文件所属证明环节：以矩阵变量的有理函数为线值，定义每一步加减乘除、输出计算、可容许指数与方阵指数，同时写出精确秩分解的系数等式。
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# 方阵乘法的形式算术复杂度

直线计算记录当前可用的连线值。初始时所有输入和域常数均可用。每步加入一个二元门的值，以前的值可不限次数复用。除法规则在有理函数域中检验分母，即使在正特征下也是如此。

**英文原文**

Formal arithmetic complexity of square matrix multiplication

A straight-line computation records the set of available wire values. All
inputs and field constants are initially available. One step adds the value
of one binary gate, with unrestricted reuse. The division rule tests the
denominator in the rational function field, even in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：在后续公式中，`Pos` 是 `Fin n × Fin n` 的缩写。
abbrev Pos (n : ℕ) := Fin n × Fin n
-- 读法：在后续公式中，`Var` 是 `Pos n ⊕ Pos n` 的缩写。
abbrev Var (n : ℕ) := Pos n ⊕ Pos n
-- 读法：在后续公式中，`Rat` 是 `FractionRing (MvPolynomial (Var n) F)` 的缩写。
abbrev Rat (F : Type*) [Field F] (n : ℕ) := FractionRing (MvPolynomial (Var n) F)

-- 读法：`input` 的取值由 `algebraMap (MvPolynomial (Var n) F) (Rat F n) (MvPolynomial.X i)` 给出。
def input (F : Type*) [Field F] {n : ℕ} (i : Var n) : Rat F n :=
  algebraMap (MvPolynomial (Var n) F) (Rat F n) (MvPolynomial.X i)

-- 读法：`initial` 的取值由 `Set.range (algebraMap F (Rat F n)) ∪ Set.range (input F)` 给出。
def initial (F : Type*) [Field F] (n : ℕ) : Set (Rat F n) :=
  Set.range (algebraMap F (Rat F n)) ∪ Set.range (input F)

-- 读法：`output` 的取值由 `∑ k : Fin n, input F (.inl (p.1, k)) * input F (.inr (k, p.2))` 给出。
def output (F : Type*) [Field F] {n : ℕ} (p : Pos n) : Rat F n :=
  ∑ k : Fin n, input F (.inl (p.1, k)) * input F (.inr (k, p.2))

-- 读法：归纳构造子包括 `nil`、`add`、`sub`、`mul`、`div`。
inductive Build {K : Type*} [Field K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)
  | div {m T x y} : Build S m T → x ∈ T → y ∈ T → y ≠ 0 → Build S (m + 1) (insert (x / y) T)

-- 读法：`Computes` 表示以下条件：存在 `T`，`Build (initial F n) m T` 与 `∀ p : Pos n, output F p ∈ T` 同时成立。
def Computes (F : Type*) [Field F] (n m : ℕ) : Prop :=
  ∃ T, Build (initial F n) m T ∧ ∀ p : Pos n, output F p ∈ T

-- 读法：`Admissible` 表示以下条件：对每个 `ε : ℝ`，由 `0 < ε` 推出 `∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ m : ℕ, Computes F n m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)`。
def Admissible (F : Type*) [Field F] (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F n m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

-- 读法：`omega` 的取值由 `sInf {s | Admissible F s}` 给出。
def omega (F : Type*) [Field F] : ℝ := sInf {s | Admissible F s}

-- 读法：`RankLE` 表示以下条件：存在 `a b c : Fin r → Pos n → F`，对每个 `x y z : Pos n`，结论为 `∑ i : Fin r, a i x * b i y * c i z = if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0`。
/-- 秩分解的系数方程。最后一个索引是输出位置，由左输入的行与右输入的列确定。

英文原文：Coefficient equations for a rank decomposition. The last index is an
output position (row of the left input, column of the right input).
-/
def RankLE (F : Type*) [Field F] (n r : ℕ) : Prop :=
  ∃ a b c : Fin r → Pos n → F, ∀ x y z : Pos n,
    ∑ i : Fin r, a i x * b i y * c i z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

end OAI.LinearAlgebra.MatrixExponent
