-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-!
# 每个输出均有专用乘积的双线性公式

**英文原文**

Bilinear formulas with a private product for each output
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior

-- 读法：结构的字段包括 `left`、`right`。
/-- 可分解双线性型的系数。

英文原文：Coefficients of a decomposable bilinear form.
-/
structure Product (F : Type*) (X Y : Type) where
  left : X → F
  right : Y → F

-- 读法：`Product.apply` 的取值由 `p.left x * p.right y` 给出。
def Product.apply {F : Type*} [Mul F] {X Y : Type} (p : Product F X Y) (x : X) (y : Y) :=
  p.left x * p.right y

-- 读法：`Private` 的结果类型为 `Prop`。
/-- 每个输出只读取自己的乘积和公共乘积的一个线性组合。其他输出均不读取该专用乘积。

英文原文：Each output reads its own product and a linear combination of
common products. No other output reads the private product.
-/
def Private {F : Type*} [Field F] {X Y Z : Type} (M : Z → X → Y → F) (r : ℕ) : Prop :=
  ∃ (a : Z → Product F X Y) (b : Fin r → Product F X Y) (c : Z → Fin r → F),
    ∀ z x y, M z x y = (a z).apply x y + ∑ l, c z l * (b l).apply x y

-- 读法：`PrivateProducts` 表示以下条件：`Private (fun (z : Pos i j) (x : Pos i k) (y : Pos k j) => if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : F) else 0) r`。
def PrivateProducts (F : Type*) [Field F] (i j k r : ℕ) : Prop :=
  Private (fun (z : Pos i j) (x : Pos i k) (y : Pos k j) =>
    if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : F) else 0) r

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
