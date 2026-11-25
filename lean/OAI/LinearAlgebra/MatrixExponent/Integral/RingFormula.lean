-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
-- FieldFormula 给出任意域的指数，UpperBound 提供可用于非零交换环的转换。
import OAI.LinearAlgebra.MatrixExponent.FieldFormula
import OAI.LinearAlgebra.MatrixExponent.Integral.UpperBound

/-! # 非零交换环上的无除法指数 -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral

-- 读法：`exponent A a b c` 等于 `Rectangle.U a b c`。使用 `of_fields` 给出的结论。
-- 在非平凡交换环 A 上，对每组三个非负权重，计算无除法电路的指数。
theorem exponent_eq (A : Type*) [CommRing A] [Nontrivial A] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent A a b c = Rectangle.U a b c :=
  -- of_fields 将目标归约到各域的同一等式。把目标权重的非负性和域上已知的 Rectangle.exponent_eq 传入。
  of_fields A ha hb hc (fun F _ => Rectangle.exponent_eq F ha hb hc)

-- 读法：`exponent A 1 1 1` 等于 `9 / 4`。
-- 方阵对应三个权重全为 1。将它们代入刚得到的公式，展开基准函数，计算得到 2+1/4。
theorem square_exponent (A : Type*) [CommRing A] [Nontrivial A] : exponent A 1 1 1 = 9 / 4 := by
  rw [exponent_eq A zero_le_one zero_le_one zero_le_one]
  norm_num [Rectangle.U, Rectangle.benchmark]

end OAI.LinearAlgebra.MatrixExponent.Integral
