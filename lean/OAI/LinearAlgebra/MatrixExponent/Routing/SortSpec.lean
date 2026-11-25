-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags
import OAI.LinearAlgebra.MatrixExponent.Radix.Defs
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute

/-!
# 定理 3.1 的带标签置换张量与稳定排序张量

**英文原文**

The tagged-permutation and stable-sort tensors of Theorem 3.1
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

-- 读法：`key` 的取值由 `(bits (word k)).symm (fun i => bits (word w) x (e i))` 给出。
/-- 选取由互异比特位置组成的任意有序子序列，次序从最高有效位到最低有效位。

英文原文：Select any ordered subsequence of distinct bit positions, in order
from most to least significant.
-/
def key {w k : ℕ} (e : slots (word k) ↪ slots (word w)) (x : Val (word w)) : Val (word k) :=
  (bits (word k)).symm (fun i => bits (word w) x (e i))

open Classical in
-- 读法：当 `Radix.Stable (key e) (flatten h x) (flatten h y)` 成立时取 `1`，否则取 `0`。
noncomputable def stableTensor (F : Type) [Field F] (h w k : ℕ)
    (e : slots (word k) ↪ slots (word w))
    (x y : Val (tree h (word w))) : F :=
  if Radix.Stable (key e) (flatten h x) (flatten h y) then 1 else 0

-- 读法：`SortingBound` 的结果类型为 `Prop`。
/-- 在标签谓词中，无标签的行是候选输出，有标签的行是附有目标地址的输入。两个上界均将顶点数与全部外部位置数相加。

英文原文：In the tag predicate the untagged rows are the proposed outputs,
and the tagged rows are inputs bearing their destination addresses.
Both bounds count vertices plus all exterior positions.
-/
def SortingBound (F : Type) [Field F] (h w : ℕ) (M : ℝ) : Prop :=
  (∃ v, Net F (Tagged.inputs h (word w)) .unit (Tagged.tag F h (word w)) v ∧
    (v + 2 ^ h * (h + 2 * w) : ℕ) ≤ M) ∧
  ∀ k (e : slots (word k) ↪ slots (word w)),
    ∃ v, Net F (tree h (word w)) (tree h (word w)) (stableTensor F h w k e) v ∧
      (v + 2 ^ h * (2 * w) : ℕ) ≤ M

end OAI.LinearAlgebra.MatrixExponent.Routing
