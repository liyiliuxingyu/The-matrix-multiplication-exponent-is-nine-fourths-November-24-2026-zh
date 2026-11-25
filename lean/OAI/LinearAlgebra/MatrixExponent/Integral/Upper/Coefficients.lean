-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Interpolation
import OAI.LinearAlgebra.TensorSpectrum.Additive.RankAnalysis
import OAI.LinearAlgebra.MatrixExponent.LocalTensor
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper
open OAI.MatrixMultiplication.Foundation

-- 读法：`matrixTensor` 的取值由 `Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)` 给出。
def matrixTensor (a b c : ℕ) :
    Tensor O (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
