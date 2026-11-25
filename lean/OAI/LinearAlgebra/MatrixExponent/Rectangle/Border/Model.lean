-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# 全系数空间中秩轨迹的几何闭包

**英文原文**

Geometric closure of the rank locus in the full coefficient space
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}

-- 读法：`ZClosure` 表示以下条件：对每个 `p : MvPolynomial ι F`，由 `(∀ y ∈ s, MvPolynomial.eval y p = 0)` 推出 `MvPolynomial.eval x p = 0`。
def ZClosure {ι : Type} (s : Set (ι → F)) (x : ι → F) : Prop :=
  ∀ p : MvPolynomial ι F,
    (∀ y ∈ s, MvPolynomial.eval y p = 0) → MvPolynomial.eval x p = 0

-- 读法：在后续公式中，`Coordinates` 是 `Pos i k × Pos k j × Pos i j` 的缩写。
abbrev Coordinates (i j k : ℕ) := Pos i k × Pos k j × Pos i j

-- 读法：当 `x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2` 成立时取 `w x.1 y.2 x.2`，否则取 `0`。
def coefficients (w : Fin i → Fin j → Fin k → F) : Coordinates i j k → F :=
  fun (x, y, z) => if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

-- 读法：`rankSet` 的结果类型为 `Set (Coordinates i j k → F)`。
def rankSet (F : Type*) [Field F] (i j k r : ℕ) : Set (Coordinates i j k → F) :=
  {v | ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z = v (x, y, z)}

-- 读法：`BorderRankLE` 表示以下条件：`ZClosure (rankSet (AlgebraicClosure F) i j k r) (coefficients (fun x y z => algebraMap F (AlgebraicClosure F) (w x y z)))`。
def BorderRankLE (w : Fin i → Fin j → Fin k → F) (r : ℕ) : Prop :=
  ZClosure (rankSet (AlgebraicClosure F) i j k r)
    (coefficients (fun x y z => algebraMap F (AlgebraicClosure F) (w x y z)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
