-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# 公共随机种子与无除法算术验证

每个种子选定一个直线程序，在其后进行若干标量相等性检验。成本计入每条二元算术指令和每次检验。这些程序是第 8 节相等性检验树的一个子类。

**英文原文**

Public seeds and division-free arithmetic verification

Each seed chooses a straight-line program followed by scalar equality
tests. Its cost counts all binary arithmetic instructions and all tests.
This is a subclass of the equality-test trees in Section 8.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter Finset
open scoped Classical

-- 读法：在后续公式中，`Index` 是 `Fin 3 × Rectangle.Pos n n` 的缩写。
abbrev Index (n : ℕ) := Fin 3 × Rectangle.Pos n n
-- 读法：在后续公式中，`Poly` 是 `MvPolynomial (Index n) F` 的缩写。
abbrev Poly (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Index n) F

-- 读法：`inputs` 的取值由 `Set.range MvPolynomial.C ∪ Set.range MvPolynomial.X` 给出。
def inputs (F : Type*) [Field F] (n : ℕ) : Set (Poly F n) :=
  Set.range MvPolynomial.C ∪ Set.range MvPolynomial.X

variable {F : Type*} [Field F] {n : ℕ}

-- 读法：`Correct` 表示以下条件：对每个 `i j : Fin n`，结论为 `∑ k, x (0, i, k) * x (1, k, j) = x (2, i, j)`。
def Correct (x : Index n → F) : Prop :=
  ∀ i j : Fin n, ∑ k, x (0, i, k) * x (1, k, j) = x (2, i, j)

-- 读法：结构的字段包括 `count`、`left`、`right`。
structure Test (F : Type*) [Field F] (n : ℕ) where
  count : ℕ
  left : Fin count → Poly F n
  right : Fin count → Poly F n

-- 读法：`Test.accept` 表示以下条件：对每个 `i`，`MvPolynomial.eval x (T.left i)` 等于 `MvPolynomial.eval x (T.right i)`。
def Test.accept (T : Test F n) (x : Index n → F) : Prop :=
  ∀ i, MvPolynomial.eval x (T.left i) = MvPolynomial.eval x (T.right i)

-- 读法：`Test.cost` 表示以下条件：存在 `(m : ℕ) (V : Set (Poly F n))`，`Integral.Build (inputs F n) m V` 与 `(∀ i, T.left i ∈ V ∧ T.right i ∈ V) ∧ (m : ℝ) + T.count ≤ c` 同时成立。
def Test.cost (T : Test F n) (c : ℝ) : Prop :=
  ∃ (m : ℕ) (V : Set (Poly F n)), Integral.Build (inputs F n) m V ∧
    (∀ i, T.left i ∈ V ∧ T.right i ∈ V) ∧ (m : ℝ) + T.count ≤ c

-- 读法：`Uniform` 的结果类型为 `Prop`。
def Uniform (F : Type*) [Field F] (n : ℕ) (s c p : ℝ) : Prop :=
  ∃ (L : ℕ) (A : Fin L → Test F n), 0 < L ∧ (L : ℝ) ≤ s ∧ (∀ i, (A i).cost c) ∧
    (∀ x, Correct x → ∀ i, (A i).accept x) ∧
    ∀ x, ¬ Correct x → (#{i | (A i).accept x} : ℝ) ≤ p * L

-- 读法：`Support` 表示以下条件：对每个 `ε > (0 : ℝ)`，对每个 `p > (0 : ℝ)`，对每个 `ᶠ n : ℕ in atTop`，要证明的命题是 `Uniform F n ((n : ℝ) ^ (ρ + ε)) ((n : ℝ) ^ (v + ε)) p`。
def Support (F : Type*) [Field F] (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Uniform F n ((n : ℝ) ^ (ρ + ε)) ((n : ℝ) ^ (v + ε)) p

-- 读法：`Entropy` 的结果类型为 `Prop`。
def Entropy (F : Type*) [Field F] (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (L : ℕ) (A : Fin L → Test F n) (w : Fin L → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ -(∑ i, w i * Real.log (w i)) ≤ (η + ε) * Real.log n ∧
      (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧
      ∀ x, (∑ i, if (A i).accept x ↔ Correct x then w i else 0) ≥ 2 / 3

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
