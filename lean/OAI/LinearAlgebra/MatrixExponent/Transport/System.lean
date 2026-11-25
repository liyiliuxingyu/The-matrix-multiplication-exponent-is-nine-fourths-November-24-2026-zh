-- 本文件所属证明环节：以有限的局部核及端口表实现带标记记录的运输，使局部选择组合成指定置换并控制扩展规模。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Pad
import OAI.LinearAlgebra.MatrixExponent.Install.Weight

/-!
# 置换的局部实现

依赖于输入的控制器读取一个置换和一个外层选择器，在各个位置选择局部核及与该位置关联的核心槽位配置。每个启用的槽位指明对应的另一端。局部核还接收外部的输入、输出记录。

**英文原文**

Local realization of a permutation

An input-dependent controller reads a permutation and an outer
selector. At each site it chooses a local kernel and a configuration
of the incident core slots. Every enabled slot names its opposite end.
A kernel also receives the incoming and outgoing exterior records.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring

-- 读法：在后续公式中，`Site` 是 `B (h + 1)` 的缩写。
abbrev Site (h : ℕ) := B (h + 1)
-- 读法：在后续公式中，`Port` 是 `Site h × B p` 的缩写。
abbrev Port (h p : ℕ) := Site h × B p
-- 读法：在后续公式中，`Data` 是 `Fin W × Fin z → Bool` 的缩写。
abbrev Data (W z : ℕ) := Fin W × Fin z → Bool
-- 读法：在后续公式中，`Channels` 是 `B p × Fin z → Bool` 的缩写。
abbrev Channels (p z : ℕ) := B p × Fin z → Bool

-- 读法：在后续公式中，`Command` 是 `Format.pair .bit (.pair .bit (.pair (.addr (h + 1)) (.addr p)))` 的缩写。
/-- 启用标志、方向比特、远端位点和远端槽位。

英文原文：Enable flag, orientation bit, remote site and remote slot.
-/
abbrev Command (h p : ℕ) := Format.pair .bit (.pair .bit (.pair (.addr (h + 1)) (.addr p)))
-- 读法：在后续公式中，`Controls` 是 `Format.vec (h + 1) (.pair A (.vec p (Command h p)))` 的缩写。
abbrev Controls (h p : ℕ) (A : Format) := Format.vec (h + 1) (.pair A (.vec p (Command h p)))
-- 读法：在后续公式中，`Orders` 是 `Port h p → (Command h p).obj` 的缩写。
abbrev Orders (h p : ℕ) := Port h p → (Command h p).obj

variable {h p W z : ℕ}

-- 读法：输入 `i` 时返回 `(c i.1).2 i.2`。
def commands {A : Format} (c : (Controls h p A).obj) : Orders h p := fun i => (c i.1).2 i.2

-- 读法：`Enabled` 的取值由 `Finset.univ.filter (fun i => (a i).1)` 给出。
def Enabled (a : Orders h p) : Finset (Port h p) := Finset.univ.filter (fun i => (a i).1)

-- 读法：`Valid` 表示以下条件：对每个 `i ∈ Enabled a`，结论为 `let j := (a i).2.2 j ∈ Enabled a ∧ (a j).2.2 = i ∧ (a j).2.1 = !(a i).2.1 ∧ group j = group i`。
def Valid (group : Port h p → ℕ) (a : Orders h p) : Prop :=
  ∀ i ∈ Enabled a, let j := (a i).2.2
    j ∈ Enabled a ∧ (a j).2.2 = i ∧ (a j).2.1 = !(a i).2.1 ∧ group j = group i

-- 读法：`Joins` 表示以下条件：对每个 `i ∈ Enabled a`，结论为 `let j := (a i).2.2 ∀ t, c i.1 (i.2, t) = c j.1 (j.2, t)`。
def Joins (a : Orders h p) (c : Site h → Channels p z) : Prop :=
  ∀ i ∈ Enabled a, let j := (a i).2.2
    ∀ t, c i.1 (i.2, t) = c j.1 (j.2, t)

-- 读法：在后续公式中，`KernelPins` 是 `A.pins ⊕ (Fin W × Fin z) ⊕ (Fin W × Fin z) ⊕ (B p × Fin z)` 的缩写。
abbrev KernelPins (A : Format) (p W z : ℕ) :=
  A.pins ⊕ (Fin W × Fin z) ⊕ (Fin W × Fin z) ⊕ (B p × Fin z)

-- 读法：结构的字段包括 `selector`、`config`、`dispatch`、`group`、`kernel`。
structure System (F : Type) (h p W z : ℕ) where
  selector : Format
  config : Format
  dispatch : ((Perm h).pair selector).obj → (Controls h p config).obj
  group : Port h p → ℕ
  kernel : config.obj → Data W z → Data W z → Channels p z → F

namespace System

variable {F : Type} [Field F] (S : System F h p W z)

-- 读法：`localWeight` 的结果类型为 `F`。
def localWeight (x : KernelPins S.config p W z → Bool) : F :=
  S.kernel (S.config.code.symm (x ∘ Sum.inl)) (fun i => x (.inr (.inl i)))
    (fun i => x (.inr (.inr (.inl i)))) (fun i => x (.inr (.inr (.inr i))))

-- 读法：`value` 的取值由 `∏ i, S.kernel (v i).1 (x i) (y i) (c i)` 给出。
def value (v : (Controls h p S.config).obj) (x y : Site h → Data W z)
    (c : Site h → Channels p z) : F :=
  ∏ i, S.kernel (v i).1 (x i) (y i) (c i)

open Classical in
-- 读法：`Correct` 的结果类型为 `Prop`。
def Correct (C : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (B h)) (x y : Site h → Data W z),
    (∀ t c, let v := S.dispatch (σ, t)
      S.value v x y c ≠ 0 → Valid S.group (commands v) ∧ (Enabled (commands v)).card ≤ C * W * 2 ^ h) ∧
    (if ∀ i, x i = y (Routing.inflate h σ i) then (1 : F) else 0) =
      ∑ t : S.selector.pins → Bool, ∑ c : Site h → Channels p z,
        let v := S.dispatch (σ, S.selector.code.symm t)
        S.value v x y c * (if Joins (commands v) c then 1 else 0)

end System

-- 读法：`LocalProtocol` 的结果类型为 `Prop`。
/-- 传送宽度有一致上界。各项控制开销与局部核开销都允许依赖于所选的高度比。

英文原文：Uniform bound on transported width; all control and local kernel
costs may depend on the chosen height ratio.
-/
def LocalProtocol (F : Type) [Field F] : Prop :=
  ∃ C : ℕ, ∀ τ : ℝ, 0 < τ → ∃ p W D : ℕ, 4 ≤ W ∧ ∀ᶠ h : ℕ in Filter.atTop,
    ∃ b : ℕ, p + 22 ≤ b ∧ b ≤ h ∧ (b : ℝ) ≤ τ * h ∧ ∀ j : ℕ, j ≤ h →
      ∃ S : System F h p W (2 ^ j), S.Correct C ∧
        (∀ i, (Finset.univ.filter (fun k => S.group k = i)).card ≤ 2 ^ (b - 1)) ∧
        Cheap F (h + 1) (h + 1) ((Perm h).pair S.selector) (Controls h p S.config) S.dispatch D ∧
        Install.Weight F S.localWeight (2 ^ j * (100 + j) ^ D)

end OAI.LinearAlgebra.MatrixExponent.Transport
