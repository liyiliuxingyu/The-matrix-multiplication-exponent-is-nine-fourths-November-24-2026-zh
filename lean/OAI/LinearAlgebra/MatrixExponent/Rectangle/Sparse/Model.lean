-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights

/-!
# 均匀支撑上的补全方案数与条件熵

**英文原文**

Completion counts and conditional entropies on the uniform support
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse

-- 读法：在后续公式中，`Cell` 是 `Fin i × Fin j × Fin k` 的缩写。
abbrev Cell (i j k : ℕ) := Fin i × Fin j × Fin k
variable {F : Type*} [Field F] {i j k : ℕ}

open Classical in
-- 读法：`support` 的取值由 `Finset.univ.filter fun t => w t.1 t.2.1 t.2.2 ≠ 0` 给出。
def support (w : Fin i → Fin j → Fin k → F) : Finset (Cell i j k) :=
  Finset.univ.filter fun t => w t.1 t.2.1 t.2.2 ≠ 0

-- 读法：`rows` 的取值由 `Finset.univ.filter fun x : Fin i => (x, t.2.1, t.2.2) ∈ S` 给出。
def rows (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun x : Fin i => (x, t.2.1, t.2.2) ∈ S

-- 读法：`cols` 的取值由 `Finset.univ.filter fun y : Fin j => (t.1, y, t.2.2) ∈ S` 给出。
def cols (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun y : Fin j => (t.1, y, t.2.2) ∈ S

-- 读法：`inner` 的取值由 `Finset.univ.filter fun z : Fin k => (t.1, t.2.1, z) ∈ S` 给出。
def inner (S : Finset (Cell i j k)) (t : Cell i j k) :=
  Finset.univ.filter fun z : Fin k => (t.1, t.2.1, z) ∈ S

-- 读法：`conditional` 的取值由 `(∑ t ∈ S, (Real.log (rows S t).card + Real.log (cols S t).card + Real.log (inner S t).card)) / S.card` 给出。
/-- 给定另两个标签时，缺失标签的条件分布在所有可补全的取值上均匀。此处的熵取自然对数。

英文原文：The conditional law of each missing label given the other two
is uniform on its completion set. Entropy here uses natural logs.
-/
def conditional (S : Finset (Cell i j k)) : ℝ :=
  (∑ t ∈ S, (Real.log (rows S t).card + Real.log (cols S t).card +
    Real.log (inner S t).card)) / S.card

-- 读法：`premium` 的取值由 `(Real.log S.card - conditional S) / Real.log 2` 给出。
/-- 以比特计的对偶总相关量。

英文原文：Dual total correlation in bits.
-/
def premium (S : Finset (Cell i j k)) : ℝ :=
  (Real.log S.card - conditional S) / Real.log 2

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
