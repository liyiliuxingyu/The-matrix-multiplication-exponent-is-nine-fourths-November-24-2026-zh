-- 本文件所属证明环节：汇总三条最终定理。方阵情形将无除法形式电路与有理函数电路的指数等式同 ω＝9/4 相接；对偶指数利用矩形刚性得到 1/2；一般矩形先把负权重截为零，再排序代入统一闭式。
-- 本文件综合四个模块：整数型电路的精确公式、对偶指数的定义、矩形电路模型间的对应，以及方阵秩模型间的对应。
import OAI.LinearAlgebra.MatrixExponent.Integral.RingFormula
import OAI.LinearAlgebra.SpectralBooks.DualExponent
import OAI.LinearAlgebra.SpectralBooks.RectangularCircuitModel
import OAI.LinearAlgebra.SpectralBooks.SquareRankModel

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

-- 读法：`formalOmega F 1 1 1` 等于 `(9 : ℝ) / 4`。通过传递性衔接 `formalOmega_square_eq_omega` 与 `MatrixExponent.omega_eq`。
/-- 任意域上的方阵乘法指数等于 9/4。 -/
theorem square_exponent (F : Type*) [Field F] : formalOmega F 1 1 1 = (9 : ℝ) / 4 :=
  -- 第一条等式把无除法形式电路的指数化为有理函数电路的指数，第二条把后者算成 9/4；用等式的传递性连接它们。
  (formalOmega_square_eq_omega F).trans (MatrixExponent.omega_eq F)

-- 读法：`formalAlpha F` 等于 `(1 : ℝ) / 2`。这里调用 `and_congr_right`。
/-- 任意域上的对偶矩阵乘法指数等于 1/2。 -/
theorem dual_exponent (F : Type*) [Field F] : formalAlpha F = (1 : ℝ) / 2 := by
  -- 同时取出方阵指数等式 hs 和矩形刚性 hr，最后一步会同时用到这两个结论。
  obtain ⟨hs, hr⟩ := MatrixExponent.omega_eq_and_rigidity F
  calc
    formalAlpha F = MatrixExponent.Rectangle.dual F 1 1 := by
      -- 两个对偶指数都定义为实数集合的上确界。用集合外延把目标化成逐个 t 的成员资格等价。
      unfold formalAlpha dualExponent MatrixExponent.Rectangle.dual
      congr 1
      ext t
      simp only [Set.mem_ofPred_eq, min_self, one_add_one_eq_two]
      apply and_congr_right
      -- 此处 ht 给出 0 ≤ t ≤ 1。先转为 Integral 模型，再用非负权重下的模型一致性和三条边的循环对称性改写。
      intro ht
      rw [formalOmega_eq_integral, MatrixExponent.Integral.agreement F ht.1 zero_le_one zero_le_one,
        MatrixExponent.Rectangle.cycle F ht.1 zero_le_one zero_le_one]
    -- 将方阵指数 9/4 和矩形刚性代入 dual_square，得到边界权重 1/2。
    _ = (1 : ℝ) / 2 := MatrixExponent.Rectangle.dual_square hr hs

-- 读法：结论为 `MatrixExponent.Rectangle.U c b a = let x := max a (max b c) let z := min a (min b c) let y := a + b + c - x - z x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z)`。
-- 整理矩形公式：x 是最大权重，z 是最小权重，扣除这两项便得到中间权重 y。这里先处理对称基准函数本身。
private theorem benchmark_sorted (a b c : ℝ) :
    MatrixExponent.Rectangle.U c b a =
      let x := max a (max b c)
      let z := min a (min b c)
      let y := a + b + c - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  let x := max a (max b c)
  let z := min a (min b c)
  let y := a + b + c - x - z
  change MatrixExponent.Rectangle.U c b a = MatrixExponent.Rectangle.benchmark x y z
  -- 如果第三个参数已经是最小值 z，前两个参数互换也不改变修正项：分子、分母关于它们对称。
  have sorted (u v w : ℝ) (hw : w = z)
      (huv : (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
      MatrixExponent.Rectangle.benchmark u v w = MatrixExponent.Rectangle.benchmark x y z := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rw [hu, hv, hw]
    simp only [MatrixExponent.Rectangle.benchmark, add_comm y x, mul_comm y x,
      show 4 * y * x = 4 * x * y by ring]
  -- 展开 U 中按最小权重分类的分支；逐支确认前两个参数的顺序，再调用上面的对称性。
  unfold MatrixExponent.Rectangle.U
  split_ifs <;> apply sorted <;> dsimp only [x, y, z] <;> grind

-- 读法：这里调用 `benchmark_sorted`。
/-- 矩形乘法指数的精确值。先把每个权重截断到非负半轴，再按降序排列。在坐标平面上，修正项为零。 -/
theorem rectangular_exponent (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c =
      let A := max a 0
      let B := max b 0
      let C := max c 0
      let x := max A (max B C)
      let z := min A (min B C)
      let y := A + B + C - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  -- 截断负权重后，形式指数等于 Integral.exponent；非负性使精确指数公式适用，最后将式子改写为有序权重的形式。
  rw [formalOmega_max_zero F a b c, formalOmega_eq_integral,
    MatrixExponent.Integral.exponent_eq F (le_max_right ..) (le_max_right ..) (le_max_right ..)]
  exact benchmark_sorted _ _ _

end SpectralBooks
end LinearAlgebra
end OAI
