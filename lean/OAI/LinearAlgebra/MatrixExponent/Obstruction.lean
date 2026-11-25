-- 本文件所属证明环节：把素数域上的带标签置换难度与元数缩减两条估计合并，利用多列表下界和反复压缩互相矛盾，进而得到所有域上的结论。
-- 证明结合矩形指数、排序、带标记问题的归约、反复压缩，以及网络规模的缩减估计。
import OAI.LinearAlgebra.MatrixExponent.Rectangle
import OAI.LinearAlgebra.MatrixExponent.Routing.Square
import OAI.LinearAlgebra.MatrixExponent.Routing.Dual
import OAI.LinearAlgebra.MatrixExponent.Tagged.Reduction
import OAI.LinearAlgebra.MatrixExponent.Iteration
import OAI.LinearAlgebra.MatrixExponent.Shaving.Network

/-! # 谱空间上的两种情形

若共享价格条件不成立，则三脚架上必有接触。若共享价格条件成立，就能得到两种排序构造以及局部集中。素域上的两个网络估计将排除后一种情形。 -/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：`omega F = 9 / 4` 与 `Rectangle.Rigidity F` 同时成立。这里调用 `Rectangle.of_prime_fields`。
/-- 方阵指数的等式与矩形刚性可以同时推出。 -/
theorem contact_of_network_estimates
    (hard : ∀ (p : ℕ) [Fact p.Prime], Tagged.Hard (ZMod p))
    (stage : ∀ (p : ℕ) [Fact p.Prime], Prices.SharedPrice (AlgebraicClosure (ZMod p)) →
      ArityReduction (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  -- 先调用素域归约。只需对每个素数 p 证明 ZMod p 上的指数等式及刚性，结论就能转至目标域 F。
  apply Rectangle.of_prime_fields _ F
  intro p _
  -- 通过 contact_of_not_shared，只需排除共享价格条件。令 sync 表示假定存在的共享价格。
  apply contact_of_not_shared
  intro sync
  -- 由共享价格选出满足 1<q<2 的排序指数 q 及排序构造 sort；共享价格还允许使用假设 stage p sync。
  obtain ⟨q, hq, hq', sort⟩ := Routing.sorting_of_shared_price sync
  -- 把排序与阶段性的元数缩减合并，得到足以反复压缩网络的 shrink。
  have shrink := compresses_of_stages hq hq' sort (stage p sync)
  -- 从单个列表的初始网络 seed 出发，压缩给出的多列表成本与 Tagged.Hard 推出的成本下界不相容。这就排除了 sync。
  exact incompatible (seed _) (Tagged.manyList_of_tag (hard p)) shrink.lists

end OAI.LinearAlgebra.MatrixExponent
