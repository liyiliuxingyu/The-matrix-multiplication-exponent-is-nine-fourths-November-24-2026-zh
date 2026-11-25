-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Bounds
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower

/-!
# 从特征标估计得到矩形矩阵乘法算法

每一配对作用于其命名所指的那条腿以外的两条腿。将前两条腿视作输入、第三条腿视作输出，即得到形式乘积的秩界。每个配对向上取整的代价至多为因子二。

**英文原文**

From the character estimate to rectangular algorithms

Each pairing belongs to the two legs other than its named leg. Reading
the first two legs as inputs and the third as output gives a rank bound
on the formal product. Ceiling costs at most a factor of two per pairing.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Rectangle
open Upper Upper.TensorClass

-- 读法：`dots` 的取值由 `dotX j * dotY i * dotZ k` 给出。
def dots (i j k : ℕ) : TensorClass := dotX j * dotY i * dotZ k

-- 读法：`dots (i ^ t) (j ^ t) (k ^ t)` 等于 `(dots i j k) ^ t`。对 `t` 作归纳。
theorem dots_power (i j k t : ℕ) : dots (i ^ t) (j ^ t) (k ^ t) = (dots i j k) ^ t := by
  induction t with
  | zero => simp [dots]
  | succ t ih =>
    rw [pow_succ, pow_succ, pow_succ, pow_succ, ← ih]
    simp only [dots, ← dotX_mul, ← dotY_mul, ← dotZ_mul]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)

open OAI.MatrixMultiplication.Foundation Upper.CoefficientTensor in
-- 读法：要证明的命题是 `Rank O i j k r`。这里调用 `CoefficientTensor.rank_le_iff`。
theorem rank_of_dots {i j k r : ℕ} (h : dots i j k ≤ (r : TensorClass)) :
    Rank O i j k r := by
  have hr := (TensorClass.rank_mono h).trans (show TensorClass.rank (r : TensorClass) ≤ r by
    rw [natCast_eq_ofTensor_natTensor, rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr (CoefficientTensor.rankAtMost_natTensor r))
  rw [ dots, dotX, dotY, dotZ, ofTensor_mul, ofTensor_mul, rank_ofTensor] at hr
  obtain ⟨a, b, c, he⟩ := (CoefficientTensor.rank_le_iff _ _).mp hr
  refine ⟨fun l x => a l (((), x.1), x.2), fun l y => b l ((y.2, ()), y.1),
    fun l z => c l ((z.2, z.1), ()), ?_⟩
  intro x y z
  have hh := congrFun (congrFun (congrFun he (((), x.1), x.2)) ((y.2, ()), y.1)) ((z.2, z.1), ())
  refine hh.symm.trans ?_
  simp [Tensor.product, dotXCoeff, dotYCoeff, dotZCoeff, ite_and]
  grind

-- 读法：`(side n a : ℝ) ^ p` 不超过 `2 * (n : ℝ) ^ (a * p)`。这里调用 `mul_le_mul_of_nonneg_right`。
theorem rounded_dot {n : ℕ} (hn : 0 < n) {a p : ℝ} (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (side n a : ℝ) ^ p ≤ 2 * (n : ℝ) ^ (a * p) := by
  calc
    _ ≤ (2 * (n : ℝ) ^ a) ^ p :=
      Real.rpow_le_rpow (by positivity) (side_le hn ha) hp
    _ = (2 : ℝ) ^ p * (n : ℝ) ^ (a * p) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp'

-- 读法：`(f (dots (side n a) (side n b) (side n c)) : ℝ)` 不超过 `8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ)`。
theorem price_dots (f : Character) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (f (dots (side n a) (side n b) (side n c)) : ℝ) ≤
      8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) := by
  simp only [dots, Character.map_mul, NNReal.coe_mul]
  change f.dotXValue _ * f.dotYValue _ * f.dotZValue _ ≤ _
  rw [f.dotXValue_eq_rpow _ (side_pos hn b), f.dotYValue_eq_rpow _ (side_pos hn a),
    f.dotZValue_eq_rpow _ (side_pos hn c)]
  have hn₀ : 0 < (n : ℝ) := by positivity
  calc
    _ ≤ (2 * (n : ℝ) ^ (b * f.pX)) * (2 * (n : ℝ) ^ (a * f.pY)) *
        (2 * (n : ℝ) ^ (c * f.pZ)) := by
      gcongr
      · exact rounded_dot hn hb f.pX_nonneg f.pX_le_one
      · exact rounded_dot hn ha f.pY_nonneg f.pY_le_one
      · exact rounded_dot hn hc f.pZ_nonneg f.pZ_le_one
    _ = _ := by rw [Real.rpow_add hn₀, Real.rpow_add hn₀]; ring

end OAI.LinearAlgebra.MatrixExponent.Integral
