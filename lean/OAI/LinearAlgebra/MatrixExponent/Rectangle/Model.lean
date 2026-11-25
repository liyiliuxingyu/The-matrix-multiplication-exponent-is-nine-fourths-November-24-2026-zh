-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.RationalCircuits

/-!
# 矩形矩阵乘积的算术指数

三条边长依次是行数、列数、内侧维数。这里与正方形模型使用相同的直线电路规则。

**英文原文**

The arithmetic exponent for rectangular products

The side lengths are ordered as rows, columns, inner dimension. The
straight-line circuit rules are shared with the square model.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

-- 读法：在后续公式中，`Pos` 是 `Fin i × Fin j` 的缩写。
abbrev Pos (i j : ℕ) := Fin i × Fin j
-- 读法：在后续公式中，`Var` 是 `Pos i k ⊕ Pos k j` 的缩写。
abbrev Var (i j k : ℕ) := Pos i k ⊕ Pos k j
-- 读法：在后续公式中，`Rat` 是 `FractionRing (MvPolynomial (Var i j k) F)` 的缩写。
abbrev Rat (F : Type*) [Field F] (i j k : ℕ) := FractionRing (MvPolynomial (Var i j k) F)

-- 读法：`input` 的取值由 `algebraMap (MvPolynomial (Var i j k) F) (Rat F i j k) (MvPolynomial.X x)` 给出。
def input (F : Type*) [Field F] {i j k : ℕ} (x : Var i j k) : Rat F i j k :=
  algebraMap (MvPolynomial (Var i j k) F) (Rat F i j k) (MvPolynomial.X x)

-- 读法：`initial` 的取值由 `Set.range (algebraMap F (Rat F i j k)) ∪ Set.range (input F)` 给出。
def initial (F : Type*) [Field F] (i j k : ℕ) : Set (Rat F i j k) :=
  Set.range (algebraMap F (Rat F i j k)) ∪ Set.range (input F)

-- 读法：`output` 的取值由 `∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))` 给出。
def output (F : Type*) [Field F] {i j k : ℕ} (p : Pos i j) : Rat F i j k :=
  ∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))

-- 读法：`Computes` 表示以下条件：存在 `T`，`Build (initial F i j k) m T` 与 `∀ p : Pos i j, output F p ∈ T` 同时成立。
def Computes (F : Type*) [Field F] (i j k m : ℕ) : Prop :=
  ∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T

-- 读法：`side` 的取值由 `⌈(n : ℝ) ^ a⌉₊` 给出。
def side (n : ℕ) (a : ℝ) : ℕ := ⌈(n : ℝ) ^ a⌉₊

-- 读法：`Admissible` 表示以下条件：对每个 `ε : ℝ`，要证明的命题是 `0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)`。
def Admissible (F : Type*) [Field F] (a b c s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

-- 读法：`exponent` 的取值由 `sInf {s | Admissible F a b c s}` 给出。
def exponent (F : Type*) [Field F] (a b c : ℝ) : ℝ := sInf {s | Admissible F a b c s}

-- 读法：`dual` 的取值由 `sSup {c ∈ Set.Icc 0 (min a b) | exponent F a b c = a + b}` 给出。
def dual (F : Type*) [Field F] (a b : ℝ) : ℝ :=
  sSup {c ∈ Set.Icc 0 (min a b) | exponent F a b c = a + b}

-- 读法：`RankLE` 表示以下条件：结论为 `∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F), ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z = if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0`。
def RankLE (F : Type*) [Field F] (i j k r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

-- 读法：`benchmark` 的取值由 `a + b + (max ((a + b) * c - a * b) 0) ^ 2 / (4 * a * b * c)` 给出。
/-- 最后一个坐标最小的锥上的基准函数。

英文原文：The benchmark on the cone where the last coordinate is smallest.
-/
def benchmark (a b c : ℝ) : ℝ :=
  a + b + (max ((a + b) * c - a * b) 0) ^ 2 / (4 * a * b * c)

-- 读法：`U` 的取值由 `if c ≤ min a b then benchmark a b c else if a ≤ b then benchmark b c a else benchmark c a b` 给出。
/-- 将一条最短边置于最后，再计算基准函数值。实值公式在坐标平面上出现的除以零按返回零处理。

英文原文：Evaluate the benchmark with a smallest side placed last. Division by
zero in the real-valued formula returns zero on a coordinate plane.
-/
def U (a b c : ℝ) : ℝ :=
  if c ≤ min a b then benchmark a b c
  else if a ≤ b then benchmark b c a
  else benchmark c a b

-- 读法：`Rigidity` 表示以下条件：`(∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → exponent F a b c = U a b c)`、`(∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → max (a + b) (max (a + c) (b + c)) < U a b c → exponent F a b c < U a b c)` 至少有一项成立。
/-- 推论 1.2 所用的矩形刚性二择一结论。若基准函数值严格大于每两个坐标之和，则称该形状为活动形状。

英文原文：The part of the rectangular rigidity dichotomy used in Corollary 1.2.
An active shape is one where the benchmark exceeds every pair sum.
-/
def Rigidity (F : Type*) [Field F] : Prop :=
  (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → exponent F a b c = U a b c) ∨
  (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
    max (a + b) (max (a + c) (b + c)) < U a b c → exponent F a b c < U a b c)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
