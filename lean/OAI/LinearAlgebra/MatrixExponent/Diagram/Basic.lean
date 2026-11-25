-- 本文件所属证明环节：用有限有向多重图表示带端口的比特张量网络，证明细分、重编号、替换及取幂对张量收缩和规模的影响。
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide

/-!
# 将比特网络表示为有限有向多重图

每个实参槽位要么属于某个有名称的外部位置，要么属于某条内部边的一端。两个双射确定这些关联，无须指定拓扑序，因此也允许自环。

**英文原文**

Bit networks as finite directed multigraphs

Every argument slot belongs either to a named exterior position or to
one end of an internal edge. The two bijections specify this incidence
without requiring a topological order. In particular, loops are allowed.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：结构的字段包括 `V`、`E`、`table`、`src`、`dst`。
structure Diagram (F : Type) (a b : Wire) where
  V : Type
  [fv : Fintype V]
  E : Type
  [fe : Fintype E]
  table : V → Table F
  src : (Σ v, slots (table v).1) ≃ slots a ⊕ E
  dst : (Σ v, slots (table v).2.1) ≃ slots b ⊕ E

attribute [instance] Diagram.fv Diagram.fe

namespace Diagram
variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：`arity` 的取值由 `wd (G.table v).1 + wd (G.table v).2.1` 给出。
def arity (v : G.V) : ℕ := wd (G.table v).1 + wd (G.table v).2.1
-- 读法：`cost` 的取值由 `∑ v, (1 + G.arity v)` 给出。
def cost : ℕ := ∑ v, (1 + G.arity v)

-- 读法：`Trivalent` 表示以下条件：对每个 `v`，`G.arity v` 不超过 `3`。
def Trivalent : Prop := ∀ v, G.arity v ≤ 3
-- 读法：`Admits` 表示以下条件：对每个 `v`，`G.arity v ≤ u` 与 `(G.arity v ≤ 3 ∨ G.table v ∈ L)` 同时成立。
def Admits (u : ℕ) (L : Set (Table F)) : Prop :=
  ∀ v, G.arity v ≤ u ∧ (G.arity v ≤ 3 ∨ G.table v ∈ L)

-- 读法：`source` 的取值由 `(G.src.symm (.inr e)).1` 给出。
def source (e : G.E) : G.V := (G.src.symm (.inr e)).1
-- 读法：`target` 的取值由 `(G.dst.symm (.inr e)).1` 给出。
def target (e : G.E) : G.V := (G.dst.symm (.inr e)).1

-- 读法：`vertex` 的结果类型为 `F`。
/-- 对内部边的比特求和前，一个站点的权重。

英文原文：Weight of one station before the internal edge bits are summed.
-/
def vertex (x : Val a) (y : Val b) (z : G.E → Bool) (v : G.V) : F :=
  (G.table v).2.2
    ((bits (G.table v).1).symm (fun i => Sum.elim (bits a x) z (G.src ⟨v, i⟩)))
    ((bits (G.table v).2.1).symm (fun i => Sum.elim (bits b y) z (G.dst ⟨v, i⟩)))

-- 读法：`eval` 的结果类型为 `F`。
noncomputable def eval [Field F] (x : Val a) (y : Val b) : F := by
  classical
  exact ∑ z : G.E → Bool, ∏ v, G.vertex x y z v

end Diagram
end OAI.LinearAlgebra.MatrixExponent
