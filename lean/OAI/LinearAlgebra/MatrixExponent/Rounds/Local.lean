-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame

/-!
# 局部集中的图接口

`Cell h` 中的每个索引指明一个独立块。宿主位置为单元命名，每个站点都属于某一块的某一单元。输入站点的元数为正，每个包都由完整的宽度 `R` 单位组成。输出为各站点预留独立的宿主槽位，并在各次节拍开始前填充到以宽度 `u` 为单位。

**英文原文**

The graph interface to local concentration

Each index in `Cell h` identifies an independent block. Host positions
name cells and each station belongs to one cell of one block. The input
has positive arities and integral packets of width `R`. The output
reserves individual host slots for the stations and is padded to units
of width `u` before the beats.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

-- 读法：结构的字段包括 `V`、`diagram`、`place`、`adj`、`sym`。
structure Input (F : Type) (x y : Wire) (h D T R g : ℕ) (W : ℝ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  place : diagram.V → V × Cell h
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  degree : ∀ v, (adj v).card ≤ g
  edge : ∀ e, let q := place (diagram.source e)
    let p := place (diagram.target e)
    p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ adj q.1)
  loopless : ∀ e, diagram.source e ≠ diagram.target e
  positive : ∀ v, 0 < diagram.arity v
  width : ∀ v w, R ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  mobile : diagram.V → Prop
  ext : ∀ q, ¬mobile (portEnd diagram q)
  occupied : (univ.image place).card * D * T ≤ W
  immobile : Fintype.card {v // ¬mobile v} * D * T ≤ W
  count : ∀ p, Fintype.card {v // place v = p} ≤ 100 * D
  mass : ∀ p, push place (fun v => (diagram.arity v : ℝ)) p ≤ 100 * (D : ℝ) * T
  squares : (∑ v, (diagram.arity v : ℝ) ^ 2) ≤ W * T
  /-- 用于确定性编号的可选局部站点键和宿主键。

英文原文：Optional local station and host keys for deterministic numbering.
-/
  ranks : Option ((diagram.V → ℕ) × (V → ℕ)) := none

attribute [instance] Input.fv

-- 读法：结构的字段包括 `V`、`diagram`、`freeze`、`frame`、`one`。
structure LocalTerm (F : Type) (x y : Wire) (h u : ℕ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  freeze : Freeze diagram
  frame : freeze.Frame V h
  one : Function.Injective frame.place
  width : ∀ v w, u ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  charge : diagram.V → ℝ
  cover : ∀ v, diagram.arity v ≤ charge v
  floor : ∀ v, u ≤ charge v

attribute [instance] LocalTerm.fv

variable {F : Type} {x y : Wire} {h D T R g u : ℕ} {W : ℝ}

-- 读法：结构的字段包括 `cells`、`coreDegree`、`fullDegree`、`frozenCount`、`frozenMax`。
/-- 每个加数所需的图与元数估计。应用中 `D=2^d`，所有隐含常数均不超过 `C`。

英文原文：The graph and arity estimates needed from one summand. Here `D=2^d`
in applications. All implicit constants are bounded by `C`.
-/
structure Concentrated (P : Input F x y h D T R g W) (Q : LocalTerm F x y h u)
    (C d ℓ : ℕ) : Prop where
  cells : Fintype.card Q.V ≤ D ^ C * Fintype.card P.V
  coreDegree : ∀ v, (Q.frame.C v).card ≤ C
  fullDegree : ∀ v, (Q.frame.N v).card ≤ D ^ C
  frozenCount : Fintype.card Q.freeze.Fixed * D * T ≤ C * W
  frozenMax : ∀ v : Q.freeze.Fixed, Q.charge v.val ≤ (C : ℝ) * D * T
  frozenSquare : (∑ v : Q.freeze.Fixed, Q.charge v.val ^ 2) ≤ C * W * T
  coreMax : ∀ v : Q.freeze.Core, Q.charge v.val * (D : ℝ) ^ ℓ ≤ T
  coreSum : (∑ v : Q.freeze.Core, Q.charge v.val) ≤ C * W * (1 + (d : ℝ)) ^ 2

-- 读法：`LocalExpansion` 的结果类型为 `Prop`。
/-- 精确展开与控制指标的数量。要具体实现该和，还需所选各项满足算法上的局部性条件。

英文原文：The exact expansion and control-index count. Algorithmic locality
of the chosen terms is an additional requirement for realizing the sum.
-/
def LocalExpansion [Field F] (P : Input F x y h D T R g W) (u C d ℓ A : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y h u) (c : I → F),
    Fintype.card I ≤ 2 ^ (A * (1 + Nat.clog 2 (T + 1)) * (univ.image P.place).card) ∧
    (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = P.diagram.eval x y) ∧
    ∀ i, Concentrated P (Q i) C d ℓ

end OAI.LinearAlgebra.MatrixExponent.Rounds

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter

-- 读法：`LocalLaw` 的结果类型为 `Prop`。
/-- 一致的局部集中使用一个固定有限扩域来布置初始数据，并为各次移动使用多项式数量的域中点。

英文原文：Uniform local concentration uses a fixed finite extension for
planting and polynomially many field points for the motions.
-/
def LocalLaw (k : Type) [Field k] (ℓ : ℕ) : Prop :=
  ∀ g : ℕ, 0 < g → ∃ C : ℕ, ∀ᶠ d : ℕ in atTop,
    let D := 2 ^ d
    ∃ (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      ∀ᶠ T : ℕ in atTop, ∃ R : ℕ, 0 < R ∧ R * D ^ 2 ≤ T ∧
        ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
          A * (1 + T) ^ A ≤ Fintype.card K → ∀ u : ℕ, 0 < u → u * D ^ C ≤ T →
          ∀ (x y : Wire) (h : ℕ) (W : ℝ) (P : Input K x y h D T R g W), LocalExpansion P u C d ℓ A

end OAI.LinearAlgebra.MatrixExponent.Rounds
