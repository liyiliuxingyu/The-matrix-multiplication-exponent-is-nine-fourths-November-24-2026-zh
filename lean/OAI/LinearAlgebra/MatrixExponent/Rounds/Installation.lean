-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
-- Construct 说明怎样从球面尺度控制构造压缩轮次；Sphere.Price.Run 给出所需的控制估计。
import OAI.LinearAlgebra.MatrixExponent.Rounds.Construct
import OAI.LinearAlgebra.MatrixExponent.Sphere.Price.Run
import OAI.LinearAlgebra.MatrixExponent.Shaving.Network
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

/-! # 有限域上的张量幂压缩 -/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：要证明的命题是 `Rounds.Installable F`。这里调用 `Rounds.installable_of_controller`。
-- 在有限域 F 上，假设 F 的代数闭包满足共享价格。目标是取得一个可实行全部压缩轮次的 Installable 对象。
theorem Rounds.installable (F : Type) [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Rounds.Installable F := by
  -- 利用 installable_of_controller 把目标化为逐个尺度方案的控制要求；SphereScale.controlled 为任意给定参数提供所需的界。
  apply Rounds.installable_of_controller F h
  intro K _ _ s hs p l b
  exact Rounds.SphereScale.controlled K s hs p l b

-- 读法：要证明的命题是 `Compresses F`。这里调用 `compresses_of_stages`。
-- 将轮次的可实施性转成网络压缩性质。这里仍以共享价格为假设。
theorem compresses_of_shared_price {F : Type} [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Compresses F := by
  -- 先取得指数 q∈(1,2) 的排序网络，再从 Installable 中取 reduction 分量作为阶段性元数缩减，与排序一起应用 compresses_of_stages。
  obtain ⟨q, hq, hq₂, sort⟩ := Routing.sorting_of_shared_price h
  exact compresses_of_stages hq hq₂ sort (Rounds.installable F h).reduction

-- 读法：要证明的命题是 `Compression (Realizes F)`。使用 `compresses_of_shared_price` 给出的结论。
-- 若方阵指数严格小于 9/4，共享价格条件由 shared_of_saving 得到。把上一步的网络压缩结论专门用于列表，即得所需的 Compression。
theorem compression_of_square_saving {F : Type} [Field F] [Finite F]
    (h : omega F < 9 / 4) : Compression (Realizes F) :=
  (compresses_of_shared_price (shared_of_saving h)).lists

end OAI.LinearAlgebra.MatrixExponent
