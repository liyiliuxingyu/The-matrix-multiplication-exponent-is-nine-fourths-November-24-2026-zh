-- 本文件所属证明环节：为置换网络中配对的边作匹配和均衡着色，并把图论分配步骤编码成可计算的有限地址和置换。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector

/-!
# 用不动点延拓以列表给出的函数

**英文原文**

Extending a listed function by fixed points
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Coloring

-- 读法：`lowerHalf` 的取值由 `Fin.castLEEmb (by rw [pow_succ]; omega)` 给出。
def lowerHalf (h : ℕ) : B h ↪ B (h + 1) := Fin.castLEEmb (by rw [pow_succ]; omega)

-- 读法：当 `ha : a.val < 2 ^ h` 成立时取 `lowerHalf h (x ⟨a, ha⟩)`，否则取 `a`。
def inflate (h : ℕ) (x : (Perm h).obj) (a : B (h + 1)) : B (h + 1) :=
  if ha : a.val < 2 ^ h then lowerHalf h (x ⟨a, ha⟩) else a

end OAI.LinearAlgebra.MatrixExponent.Routing
