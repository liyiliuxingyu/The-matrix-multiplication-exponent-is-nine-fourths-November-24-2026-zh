-- 本文件所属证明环节：交换输出的行、列坐标，使电路的输出下标与循环三张量记号的第三个因子相配，识别两种方阵秩条件。再用各阶乘法张量的渐近秩，把无除法形式程序的方阵指数同有理函数电路的方阵指数联系起来。
-- 把有理函数电路一侧的秩界与无除法电路一侧的渐近秩公式合在一起。
import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.SpectralBooks.SquareExponent

/-! # 方阵乘法张量的秩与两种电路模型 -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication.Foundation

-- 读法：`MatrixExponent.RankLE F n r` 与 `Tensor.RankAtMost (matrixTensor F n n n) r` 等价。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 电路输出按（行，列）编号，循环张量则按（列，行）编号。交换最后一对指标，即可对应两种秩分解。 -/
private theorem square_rank_iff {F : Type*} [Field F] {n r : ℕ} :
    MatrixExponent.RankLE F n r ↔ Tensor.RankAtMost (matrixTensor F n n n) r := by
  constructor
  -- 从电路分解中取出三个线性因子。只把第三个因子的下标 z 改成 z.swap，随后对三个输入逐点验证系数。
  · rintro ⟨a, b, c, h⟩
    refine ⟨a, b, fun i z => c i z.swap, ?_⟩
    funext x y z
    simpa [matrixTensor, Tensor.matrixCoefficients, Tensor.rankOne, and_comm, and_left_comm,
      eq_comm] using (h x y z.swap).symm
  -- 反方向采用相同的交换，因为交换两次回到原指标。congrFun 连续三次从函数等式取出指定坐标的等式。
  · rintro ⟨a, b, c, h⟩
    refine ⟨a, b, fun i z => c i z.swap, ?_⟩
    intro x y z
    simpa [matrixTensor, Tensor.matrixCoefficients, Tensor.rankOne, and_comm, and_left_comm,
      eq_comm] using (congrFun (congrFun (congrFun h x) y) z.swap).symm

-- 读法：`(n : ℝ) ^ MatrixExponent.omega F` 不超过 `asymptoticRank (matrixTensor F n n n)`。这里调用 `le_ciInf`。
-- 证明有理函数电路指数给出渐近秩的下界。渐近秩是各正次张量幂的秩开相应次方根所得数值的下确界。
private theorem rpow_omega_le_asymptoticRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ MatrixExponent.omega F ≤ asymptoticRank (matrixTensor F n n n) := by
  -- 要证明某数不超过下确界，只需逐一证明它不超过每一项。第 k 项取的是 k+1 次幂。
  apply le_ciInf
  intro k
  rw [tensorRank_matrixTensor_power]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (show 0 < (k : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast, Real.rpow_pow_comm (Nat.cast_nonneg n), ← Nat.cast_pow]
  -- 反设某一项太小。将 Tₙ 的 k+1 次张量幂视为 m 阶矩阵乘法，其中 m = n^(k+1)。
  by_contra! h
  let m := n ^ (k + 1)
  have hr := square_rank_iff.mpr (rankAtMost_tensorRank (matrixTensor F m m m))
  -- 若 m 阶的秩严格低于 m^ω，则有限秩改进给出 ω < ω，矛盾。
  exact (lt_irrefl (MatrixExponent.omega F)) (MatrixExponent.omega_lt_of_rank
    (hn.trans (le_self_pow (by omega) (by omega))) hr h)

-- 读法：`formalOmega F 1 1 1` 等于 `MatrixExponent.omega F`。这里调用 `le_antisymm`。
/-- 各有限阶方阵的张量秩在两种电路模型中确定同一个指数。 -/
theorem formalOmega_square_eq_omega (F : Type*) [Field F] :
    formalOmega F 1 1 1 = MatrixExponent.omega F := by
  apply le_antisymm
  -- 第一方向：若形式指数更大，有理函数电路一侧给出一对有限规模的 n、r，满足 r 小于 n 的形式指数次幂。
  · by_contra! h
    obtain ⟨n, r, hn, rank, small⟩ := MatrixExponent.omega_lt_iff_rank.mp h
    -- 把该秩分解转换为张量秩上界，再和形式模型给出的相反方向的秩下界相连，排除严格不等式。
    have le := tensorRank_le_of_rankAtMost (square_rank_iff.mp rank)
    exact (not_lt_of_ge ((rpow_formalOmega_le_tensorRank F hn).trans (Nat.cast_le.mpr le))) small
  -- 反方向只需看二阶：把渐近秩代成 2 的形式指数次幂，并利用底数 2 大于 1 消去同底幂。
  · have h := rpow_omega_le_asymptoticRank F (n := 2) (by decide)
    rw [square_asymptoticRank_eq_rpow_formalOmega F (by decide)] at h
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < (2 : ℕ))).mp h

end SpectralBooks
end LinearAlgebra
end OAI
