-- 本文件所属证明环节：调用素数域上的网络安装及排除共享价格的论证，同时得到方阵指数等式与矩形刚性，再推出任意域上的加权矩形指数公式。
import OAI.LinearAlgebra.MatrixExponent.Realization
import OAI.LinearAlgebra.MatrixExponent.Rounds.Installation

/-! # 任意域上的方阵乘法指数和矩形刚性 -/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：`omega F = 9 / 4` 与 `Rectangle.Rigidity F` 同时成立。使用 `contact_of_installations` 给出的结论。
-- 同时证明方阵指数等式和矩形刚性。Realization 将任意域上的这两个目标归约到各个素域上的压缩构造；Installation 提供所需的构造。
theorem omega_eq_and_rigidity (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F :=
  -- 对于素数 p，使用域 ZMod p 上的 installable 结果，随后由 contact_of_installations 得到目标域 F 上的结论。
  contact_of_installations (fun p _ => Rounds.installable (ZMod p)) F

-- 读法：`omega F` 等于 `9 / 4`。使用 `omega_eq_and_rigidity` 给出的结论。
/-- 任意域上由有理函数电路计算的方阵乘法指数。 -/
theorem omega_eq (F : Type*) [Field F] : omega F = 9 / 4 :=
  -- 合取的第一个分量就是方阵指数等式；矩形刚性仍可从 omega_eq_and_rigidity 单独取得。
  (omega_eq_and_rigidity F).1

-- 读法：`9 / 4` 不超过 `omega F`。使用 `omega_eq` 给出的结论。
-- 仅需要指数下界时，可以直接把已证等式取成相应方向的不等式。
theorem nine_fourths_le_omega (F : Type*) [Field F] : 9 / 4 ≤ omega F :=
  (omega_eq F).ge

-- 读法：`exponent F a b c` 等于 `U a b c`。这里调用 `all_shapes`。
/-- 矩形乘法指数等于对称基准函数；该结论也包括至少一个权重为零的坐标平面。 -/
theorem Rectangle.exponent_eq (F : Type*) [Field F] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : exponent F a b c = U a b c := by
  -- 矩形情形既使用刚性，也使用方阵指数。all_shapes 将二者应用于给定的三个非负权重。
  obtain ⟨square, rigid⟩ := omega_eq_and_rigidity F
  exact all_shapes rigid square ha hb hc

end OAI.LinearAlgebra.MatrixExponent
