-- 本文件所属证明环节：在有限域上把具有短标签的调用编成批量下降过程；结合带标签置换的难度和对角抵抗性，导出多份独立列表同时判重的规模下界。
-- Compilation 与 Encoded 把假定存在的低成本计算变为可执行的下降过程；Resistance 给出它与目标族之间的矛盾。
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Compilation
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoded
import OAI.LinearAlgebra.MatrixExponent.Processor.Resistance
import OAI.LinearAlgebra.MatrixExponent.Tagged.Reduction

/-! # 有限域上多列表问题的精确计算下界

若带标记置换问题的困难性不成立，就可以编译出所需的下降过程。将其应用于能够抵抗这种下降的族，便得到矛盾。归约到列表互异性时，完整的批量大小范围得以保留。 -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

-- 读法：要证明的命题是 `Tagged.Hard F`。使用 `Processor.hard_of_descent` 给出的结论。
-- 对任意有限域 F，证明带标记置换的困难性。参数 bad 表示假设困难性失效时得到的见证。
theorem hard (F : Type) [Field F] [Finite F] : Tagged.Hard F :=
  -- 先将 bad 编码，再从编码构造编译结果，随后用它执行下降，并交给 Processor.hard_of_descent 得出结论。
  Processor.hard_of_descent (descent fun bad => compilation_of_encoded (encoded bad))

-- 读法：存在 `η : ℝ`，由 `0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ, 1 ≤ t` 推出 `(t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m → (t : ℝ) * listBits w * (w : ℝ) ^ η < m`。使用 `Tagged.manyList_full` 给出的结论。
-- 完整形式的下界允许批量 t 大到 2^(w^(1+η))。同一个 η>0 对所有充分大的 w 和所有允许的 t 同时有效。
theorem manyList_full (F : Type) [Field F] [Finite F] :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
      (t : ℝ) * listBits w * (w : ℝ) ^ η < m :=
  Tagged.manyList_full (hard F)

-- 读法：要证明的命题是 `ManyList (Realizes F)`。使用 `Tagged.manyList_of_tag` 给出的结论。
-- 这里取多列表下界的标准接口 ManyList；迭代压缩的矛盾证明使用这一版本。
theorem manyList (F : Type) [Field F] [Finite F] : ManyList (Realizes F) :=
  Tagged.manyList_of_tag (hard F)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
