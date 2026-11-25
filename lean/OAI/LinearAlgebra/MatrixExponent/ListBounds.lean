-- 本文件所属证明环节：为列表的输入位数、单实例初始上界、多实例规模下界及一次压缩的节省和复制因子给出量词完整的定义。
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# 独立列表的界

这里，`P w t m` 表示宽度为 `w` 的张量取 `t` 次张量幂后有一个大小为 `m` 的精确实现。三个前提都只涉及这一族命题。

**英文原文**

Bounds on independent lists

Here `P w t m` means that the `t`-fold tensor power at width `w` admits
an exact realization of size `m`. The three premises only use this family.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

-- 读法：`listBits` 的取值由 `2 * w * 2 ^ w` 给出。
/-- 一个列表含有 `2^w` 条记录，每条有 `2*w` 个比特。

英文原文：A list contains `2^w` records, each with `2*w` bits.
-/
def listBits (w : ℕ) : ℕ := 2 * w * 2 ^ w

-- 读法：`Seed` 表示以下条件：存在 `C : ℝ`，对每个 `ᶠ w : ℕ in atTop`，存在 `m : ℕ`，`P w 1 m` 与 `(m : ℝ) ≤ C * listBits w * (w : ℝ) ^ 2` 同时成立。
def Seed (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ C : ℝ, ∀ᶠ w : ℕ in atTop, ∃ m : ℕ,
    P w 1 m ∧ (m : ℝ) ≤ C * listBits w * (w : ℝ) ^ 2

-- 读法：`ManyList` 表示以下条件：存在 `σ : ℝ`，由 `0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ, 1 ≤ t` 推出 `t ≤ listBits w → P w t m → (t : ℝ) * listBits w * (w : ℝ) ^ σ < 3 * m`。
def ManyList (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
    1 ≤ t → t ≤ listBits w → P w t m →
    (t : ℝ) * listBits w * (w : ℝ) ^ σ < 3 * m

-- 读法：`Compression` 的结果类型为 `Prop`。
def Compression (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ γ : ℝ, 0 < γ ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ, 1 ≤ t → P w t m →
    (m : ℝ) ≤ (listBits w : ℝ) ^ (21 / 20 : ℝ) →
    ∃ d m' : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (listBits w : ℝ) ^ δ ∧
      P w (t * d) m' ∧
      let h : ℝ := Nat.clog 2 (listBits w)
      (m' : ℝ) ≤ d * ((m : ℝ) * h ^ (-γ) + t * (listBits w : ℝ) * h ^ η)

end OAI.LinearAlgebra.MatrixExponent
