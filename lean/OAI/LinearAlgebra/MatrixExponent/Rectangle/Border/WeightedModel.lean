-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Model
import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring


/-!
# 加权乘积的三个张量腿

**英文原文**

The three tensor legs of a weighted product
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

variable {F : Type} [Field F] {i j k : ℕ}

-- 读法：`tripleLeg` 的取值由 `Fin.cases a (Fin.cases b (Fin.cases c fun t => Fin.elim0 t))` 给出。
def tripleLeg {α : Fin 3 → Sort*} (a : α 0) (b : α 1) (c : α 2) : ∀ t, α t :=
  Fin.cases a (Fin.cases b (Fin.cases c fun t => Fin.elim0 t))

-- 读法：在后续公式中，`legs` 是 `![Pos i j, Pos i k, Pos k j]` 的缩写。
abbrev legs (i j k : ℕ) : Fin 3 → Type := ![Pos i j, Pos i k, Pos k j]

-- 读法：为 `∀ s, Fintype (legs i j k s)` 构造类型类实例。
instance legFintype (i j k : ℕ) : ∀ s, Fintype (legs i j k s) :=
  tripleLeg (inferInstanceAs (Fintype (Pos i j))) (inferInstanceAs (Fintype (Pos i k)))
    (inferInstanceAs (Fintype (Pos k j)))

-- 读法：`ungroup` 的取值由 `(x 1, x 2, x 0)` 给出。
def ungroup (x : ∀ s, legs i j k s) : Coordinates i j k := (x 1, x 2, x 0)

-- 读法：`wtensor` 的取值由 `Tensor.ofRaw (Raw.ofTable (legs i j k) (T ∘ ungroup))` 给出。
def wtensor (T : Coordinates i j k → F) : Tensor F (Fin 3) :=
  Tensor.ofRaw (Raw.ofTable (legs i j k) (T ∘ ungroup))

-- 读法：`weightedTensor` 的取值由 `wtensor (coefficients w)` 给出。
def weightedTensor (w : Fin i → Fin j → Fin k → F) := wtensor (coefficients w)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
