-- 本文件所属证明环节：合并分轮元数缩减、批量查表和排序成本，给出带独立外部比特的张量幂网络的对数幂次节省。
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs

/-!
# 两种压缩尺度

宽网络的规模计入站点及其全部端口。三价网络的规模计入站点与暴露端口。元数超过三的表必须来自有限字典。各阶段可采用不同的字典限制，但工作域必须相同。

**英文原文**

The two compression scales

A wide network counts stations and all their ports. A trivalent network
counts stations and exposed ports. Tables of arity above three must come
from a finite dictionary. The stages may use different dictionary limits
but must all work over the same field.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

-- 读法：`PowerSize` 表示以下条件：存在 `v`，`Net F (copies a d) (copies b d) (power k d) v` 与 `m = v + d * (wd a + wd b)` 同时成立。
/-- 外部比特彼此独立时，一个精确张量幂的三价实现大小。

英文原文：Trivalent size of an exact tensor power with independent exterior bits.
-/
def PowerSize {F : Type} [Field F] {a b : Wire} (k : Val a → Val b → F) (d m : ℕ) : Prop :=
  ∃ v, Net F (copies a d) (copies b d) (power k d) v ∧ m = v + d * (wd a + wd b)

-- 读法：`Compresses` 的结果类型为 `Prop`。
/-- 定理 2.1 的结论，对所有初始网络一致。

英文原文：The conclusion of Theorem 2.1, uniformly in the starting network.
-/
def Compresses (F : Type) [Field F] : Prop :=
  ∀ η : ℝ, 0 < η → ∃ γ : ℝ, 0 < γ ∧ ∀ κ : ℝ, 0 < κ →
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Wire) (k : Val a → Val b → F) (v : ℕ),
      Net F a b k v →
      let e := wd a + wd b
      let m := v + e
      let h : ℝ := Nat.clog 2 n
      n ≤ e → (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ) →
      ∃ d m' : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ κ ∧ PowerSize k d m' ∧
        (m' : ℝ) ≤ d * ((m : ℝ) * h ^ (-γ) + (e : ℝ) * h ^ η)

-- 读法：`Labeled` 表示以下条件：存在 `L : Finset (Table K)`，`L.card ≤ B` 与 `Wide K u (↑L) a b k s` 同时成立。
/-- 站点及端口的计数，其中不同的高元数标签至多有 `B` 个。

英文原文：A station and port count with at most `B` distinct high-arity labels.
-/
def Labeled {K : Type} [Field K] {a b : Wire} (k : Val a → Val b → K)
    (B s u : ℕ) : Prop :=
  ∃ L : Finset (Table K), L.card ≤ B ∧ Wide K u (↑L) a b k s

-- 读法：`ArityStep` 的结果类型为 `Prop`。
/-- 第 5 节的表网络引理的一次应用。

英文原文：One application of the table-network lemma in Section 5.
-/
def ArityStep (K : Type) [Field K] (n B B' : ℕ) (b δ a ξ : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  ∀ (x y : Wire) (k : Val x → Val y → K) (s u M : ℕ),
    Labeled k B s u → (u : ℝ) ≤ h ^ b →
    s ≤ M → n ≤ M → (M : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) →
    ((wd x + wd y : ℕ) : ℝ) ≤ M * h ^ (-(2 * a)) →
    ∃ r s' u' : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ (n : ℝ) ^ ξ ∧
      Labeled (power k r) B' s' u' ∧
      (s' : ℝ) ≤ (M : ℝ) * r * h ^ (-((1 - δ) * a)) ∧
      (u' : ℝ) ≤ h ^ (b + (1 + δ) * a)

-- 读法：`ArityReduction` 的结果类型为 `Prop`。
/-- 对固定的节省额，只需有限多个元数指数。先选定域和标签的上限，再指定初始网络。

英文原文：Only finitely many arity exponents are needed for a fixed saving. The
field and label limits are chosen before the starting network.
-/
def ArityReduction (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ α : ℝ, 0 < α ∧ ∀ (a : ℝ) (J : ℕ), 0 < a → a < α → 0 < J →
      β + (1 + δ) * a * J ≤ 1 / 2 → ∀ ξ : ℝ, 0 < ξ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop, ∃ (K : Type) (_ : Field K) (_ : Algebra F K)
          (_ : Module.Finite F K) (B : ℕ → ℕ),
          (Module.finrank F K : ℝ) ≤ C * Real.log (Nat.clog 2 n) ∧
          ∀ j : ℕ, j < J → ArityStep K n (B j) (B (j + 1)) (β + (1 + δ) * a * j) δ a ξ

end OAI.LinearAlgebra.MatrixExponent
