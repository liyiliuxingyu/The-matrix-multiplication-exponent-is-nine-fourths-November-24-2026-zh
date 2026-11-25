import PaperExtensions.NonscalarLowerBound
import OAI.LinearAlgebra.SpectralBooks.ExactExponent
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# 指数定理与非标量门数下界的公理核对

先显示原有定理及补充定理的实际公理依赖，再逐个检查传递依赖是否包含上游 Comparator
许可列表之外的公理。若某一条证明引用了 `sorry`，收集到的 `sorryAx` 会使检查失败。
-/

#print axioms OAI.LinearAlgebra.SpectralBooks.square_exponent
#print axioms OAI.LinearAlgebra.SpectralBooks.dual_exponent
#print axioms OAI.LinearAlgebra.SpectralBooks.rectangular_exponent

#print axioms OAI.LinearAlgebra.MatrixExponent.computes_iff_exists_nonscalarBuild
#print axioms OAI.LinearAlgebra.MatrixExponent.bilinearize_nonscalar
#print axioms OAI.LinearAlgebra.MatrixExponent.rank_le_twice_nonscalar_over_algebraicClosure
#print axioms OAI.LinearAlgebra.MatrixExponent.nonscalar_gate_lower_bound_of_build
#print axioms OAI.LinearAlgebra.MatrixExponent.nonscalar_gate_lower_bound

open Lean

-- 双反引号引述已存在的声明。入口若改名或缺失，此处在 elaboration 时即失败。
run_cmd
  let targets := [``OAI.LinearAlgebra.SpectralBooks.square_exponent,
    ``OAI.LinearAlgebra.SpectralBooks.dual_exponent,
    ``OAI.LinearAlgebra.SpectralBooks.rectangular_exponent,
    ``OAI.LinearAlgebra.MatrixExponent.computes_iff_exists_nonscalarBuild,
    ``OAI.LinearAlgebra.MatrixExponent.bilinearize_nonscalar,
    ``OAI.LinearAlgebra.MatrixExponent.rank_le_twice_nonscalar_over_algebraicClosure,
    ``OAI.LinearAlgebra.MatrixExponent.nonscalar_gate_lower_bound_of_build,
    ``OAI.LinearAlgebra.MatrixExponent.nonscalar_gate_lower_bound]
  -- 这三个公理名与原 ComparatorChallenges/MatrixExponent.json 的配置逐项一致。
  let permitted : List Name := [`propext, `Quot.sound, `Classical.choice]
  for target in targets do
    -- collectAxioms 会沿定理的依赖传递收集公理，包括从已编译模块导入的依赖。
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless permitted.contains ax do
        throwError "定理 {target} 依赖许可清单之外的公理 {ax}"
