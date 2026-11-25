-- 本文件所属证明环节：把需要的两个素数域估计分别交给多列表困难性和分轮压缩安装，从这些实例推出所有域的方阵指数与矩形刚性。
-- Obstruction 提供比较两类网络估计的定理，BatchDescent.Hard 提供列表问题的困难性，Rounds.Install 将构造转为压缩估计。
import OAI.LinearAlgebra.MatrixExponent.Obstruction
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
import OAI.LinearAlgebra.MatrixExponent.Rounds.Install

/-! # 归约到压缩构造

多列表问题的精确计算下界在所有有限域上都成立。因此，要得到算术指数的等式以及矩形刚性，只需在共享价格假设下完成素域上的压缩构造。 -/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：`omega F = 9 / 4` 与 `Rectangle.Rigidity F` 同时成立。
-- 假设 rounds 对每个素数 p 都可用：若 ZMod p 的代数闭包满足共享价格条件，就给出该素域上的 Installable 对象。
theorem contact_of_installations
    (rounds : ∀ (p : ℕ) [Fact p.Prime], Prices.SharedPrice (AlgebraicClosure (ZMod p)) →
      Rounds.Installable (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F :=
  -- 向网络比较定理输入两个独立的估计。第一个由多列表问题在 ZMod p 上的困难性得到。
  contact_of_network_estimates (fun p _ => BatchDescent.hard (ZMod p))
    -- 第二个取自 rounds 构造的 reduction 分量。比较定理将两项估计转成任意域 F 上的指数等式与刚性。
    (fun p _ h => (rounds p h).reduction) F

end OAI.LinearAlgebra.MatrixExponent
