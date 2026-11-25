import PaperExtensions.NonscalarBilinearize
import OAI.LinearAlgebra.MatrixExponent.FieldFormula
import OAI.LinearAlgebra.MatrixExponent.RankCriterion
import OAI.LinearAlgebra.MatrixExponent.RankPower
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# 固定阶数的秩下界与整数门数

任一固定阶数上的秩分解都能递归用于更大规模的乘法。上游的
`omega_lt_of_rank` 精确表达了这一点：一旦某个有限阶数严格节省，就会把同一域上的
渐近指数压到相应阈值以下。因此可以从方阵指数的等式推出逐阶的秩下界。
-/

namespace OAI.LinearAlgebra.MatrixExponent

/-- 在任意域上，每个阶数至少为二的方阵乘法张量，其任意长度为 `r` 的
精确秩分解都满足 `n^(9/4) ≤ r`。域参数也可以取为电路输入的有理函数域。 -/
theorem fixed_order_rpow_le_of_rank {F : Type*} [Field F] {n r : ℕ}
    (hn : 2 ≤ n) (hr : RankLE F n r) :
    (n : ℝ) ^ ((9 : ℝ) / 4) ≤ (r : ℝ) := by
  -- 如果分解比此下界更短，上游的有限秩判据就会给出 omega F < 9/4。
  by_contra h
  exact (not_lt_of_ge (omega_eq F).ge) (omega_lt_of_rank hn hr (lt_of_not_ge h))

/-- 若每个计费门至多贡献两个秩一项，从门数 `m` 得到的秩证书就推出
逐阶的整数下界。这里先除以二再向上取整，保留论文中的精确常数。 -/
theorem nonscalar_count_ge_of_rank {F : Type*} [Field F] {n m : ℕ}
    (hn : 2 ≤ n) (hr : RankLE F n (2 * m)) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ m := by
  apply Nat.ceil_le.mpr
  have h := fixed_order_rpow_le_of_rank hn hr
  push_cast at h
  linarith

/-- 论文引理 2.4。若一个形式电路以 `q` 个非标量乘除门计算矩阵乘积，
则乘法张量在常数域的代数闭包上有长度为 `2*q` 的精确分解。
先将有理函数域上的分解特化到有限扩域，再将该域嵌入代数闭包。 -/
theorem rank_le_twice_nonscalar_over_algebraicClosure {F : Type*} [Field F] {n q : ℕ}
    (h : ComputesNonscalar F n q) :
    RankLE (AlgebraicClosure F) n (2 * q) := by
  obtain ⟨L, _, _, _, hL⟩ := finiteExtensionRank (F := F) (bilinearize_nonscalar h)
  exact rank_map (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F).toRingHom hL

/-- 论文推论 1.2 的逐电路陈述。`h` 给出从输入和域常数出发的一条实际计算：
总门数为 `m`，其中非标量乘除门数为 `q`。`hout` 表示在电路终止时，
乘积矩阵每个位置的形式有理函数都已获得。 -/
theorem nonscalar_gate_lower_bound_of_build {F : Type*} [Field F] {n m q : ℕ}
    {T : Set (Rat F n)} (hn : 2 ≤ n)
    (h : NonscalarBuild F (initial F n) m q T)
    (hout : ∀ p : Pos n, output F p ∈ T) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ q :=
  nonscalar_count_ge_of_rank hn
    (rank_le_twice_nonscalar_over_algebraicClosure (F := F) (n := n) ⟨m, T, h, hout⟩)

/-- 存在某个计算方阵乘积的形式电路、且其中恰有 `q` 个非标量乘除门时，
其门数亦满足同一界。计数规则也覆盖有限域，因为正确性是形式有理函数恒等式。 -/
theorem nonscalar_gate_lower_bound {F : Type*} [Field F] {n q : ℕ}
    (hn : 2 ≤ n) (h : ComputesNonscalar F n q) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ q :=
  nonscalar_count_ge_of_rank hn (rank_le_twice_nonscalar_over_algebraicClosure h)

end OAI.LinearAlgebra.MatrixExponent
