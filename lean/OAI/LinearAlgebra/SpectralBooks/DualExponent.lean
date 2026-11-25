-- 本文件所属证明环节：把 formalAlpha 定义为 t∈[0,1] 且 formalOmega(F,1,1,t)＝2 的权重的上确界。先由零权重的情形保证可行集非空，再证明任何逐点控制这些 t 的上界也控制其上确界。
import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
import OAI.LinearAlgebra.SpectralBooks.Elongated

/-! # 形式算术矩阵乘法的对偶指数 -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

-- 读法：`formalAlpha` 的取值由 `dualExponent (formalOmega F 1 1)` 给出。
/-- 对 t ∈ [0,1]，取使矩形权重 (1,1,t) 的形式算术指数等于 2 的所有 t 的上确界。 -/
noncomputable def formalAlpha (F : Type*) [Field F] : ℝ := dualExponent (formalOmega F 1 1)

-- 读法：`formalOmega F 1 1 0` 等于 `2`。
-- 先证明矩形族的端点 t=0 确实达到指数 2，以便后面对非空集合取上确界。
theorem formalOmega_one_one_zero (F : Type*) [Field F] : formalOmega F 1 1 0 = 2 := by
  let S := {τ : ℝ | FormalAdmissibleExponent F 1 1 0 τ}
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  have h1 : (0 : ℝ) ≤ 1 := zero_le_one
  -- 朴素算法说明 2 是一个容许指数，因而容许指数集合的下确界至多为 2。
  have hmem := formalAdmissibleExponent_naive F h1 h1 h0
  norm_num at hmem
  -- 反过来，端口负载的下界对每个容许指数 τ 都有效；代入权重并化简，得到 2 ≤ τ。
  have hbound : ∀ τ ∈ S, (2 : ℝ) ≤ τ := by
    intro τ hτ
    have h := FormalAdmissibleExponent.load_le (F := F) (w12 := 1) (w23 := 1) (w31 := 0) hτ 1
    norm_num [loads] at h
    exact h
  -- 使用下确界的两条次序性质合并上下界。hmem 还同时提供集合非空的见证。
  exact le_antisymm (csInf_le (s := S) ⟨2, hbound⟩ hmem) (le_csInf ⟨2, hmem⟩ hbound)

-- 读法：`formalAlpha F` 不超过 `b`。这里调用 `csSup_le`。
/-- 使矩形乘法指数等于 2 的权重集合包含 0。因此，若每个可取权重都有同一上界，该上界也控制它们的上确界。 -/
theorem formalAlpha_le {F : Type*} [Field F] {b : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, formalOmega F 1 1 t = 2 → t ≤ b) :
    formalAlpha F ≤ b := by
  -- 以 t=0 为集合的一个元素；对任意另一元素拆出其区间条件与指数等式，直接应用给定的上界 h。
  apply csSup_le (s := {t : ℝ | t ∈ Set.Icc 0 1 ∧ formalOmega F 1 1 t = 2})
    ⟨0, ⟨le_rfl, zero_le_one⟩, formalOmega_one_one_zero F⟩
  rintro t ⟨ht, hω⟩
  exact h t ht hω

end SpectralBooks
end LinearAlgebra
end OAI
