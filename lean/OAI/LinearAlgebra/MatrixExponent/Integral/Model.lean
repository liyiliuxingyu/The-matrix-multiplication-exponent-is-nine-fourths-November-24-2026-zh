-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-!
在环上计算形式多项式恒等式的无除法电路。

**英文原文**

Division-free circuits computing formal polynomial identities over a ring.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral

-- 读法：在后续公式中，`Pos` 是 `Rectangle.Pos` 的缩写。
abbrev Pos := Rectangle.Pos
-- 读法：在后续公式中，`Var` 是 `Rectangle.Var` 的缩写。
abbrev Var := Rectangle.Var
-- 读法：在后续公式中，`Poly` 是 `MvPolynomial (Var i j k) F` 的缩写。
abbrev Poly (F : Type*) [CommRing F] (i j k : ℕ) := MvPolynomial (Var i j k) F
-- 读法：在后续公式中，`side` 是 `Rectangle.side` 的缩写。
abbrev side := Rectangle.side

-- 读法：在后续公式中，`input` 是 `MvPolynomial.X x` 的缩写。
abbrev input (F : Type*) [CommRing F] {i j k : ℕ} (x : Var i j k) : Poly F i j k :=
  MvPolynomial.X x

-- 读法：归纳构造子包括 `nil`、`add`、`sub`、`mul`。
inductive Build {K : Type*} [CommRing K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)

-- 读法：`initial` 的取值由 `Set.range (algebraMap F (Poly F i j k)) ∪ Set.range (input F)` 给出。
def initial (F : Type*) [CommRing F] (i j k : ℕ) : Set (Poly F i j k) :=
  Set.range (algebraMap F (Poly F i j k)) ∪ Set.range (input F)

-- 读法：`output` 的取值由 `∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))` 给出。
def output (F : Type*) [CommRing F] {i j k : ℕ} (p : Pos i j) : Poly F i j k :=
  ∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))

-- 读法：`Computes` 表示以下条件：存在 `T`，`Build (initial F i j k) m T` 与 `∀ p : Pos i j, output F p ∈ T` 同时成立。
def Computes (F : Type*) [CommRing F] (i j k m : ℕ) : Prop :=
  ∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T

-- 读法：`Admissible` 表示以下条件：对每个 `ε : ℝ`，要证明的命题是 `0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)`。
def Admissible (F : Type*) [CommRing F] (a b c s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

-- 读法：`exponent` 的取值由 `sInf {s | Admissible F a b c s}` 给出。
def exponent (F : Type*) [CommRing F] (a b c : ℝ) : ℝ := sInf {s | Admissible F a b c s}

-- 读法：`Rank` 表示以下条件：结论为 `∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F), ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z = if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0`。
def Rank (F : Type*) [CommRing F] (i j k r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

end OAI.LinearAlgebra.MatrixExponent.Integral
