-- 本文件所属证明环节：用有限有向多重图表示带端口的比特张量网络，证明细分、重编号、替换及取幂对张量收缩和规模的影响。
import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule

section
/-!
# 比较规模与体积的计量约定

**英文原文**

Comparing size and volume conventions
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：结论为 `∑ v, G.arity v = wd a + wd b + 2 * Fintype.card G.E`。
/-- 每条内部边贡献两个实参位置，每个外部比特贡献一个。

英文原文：Each internal edge contributes two argument positions and each
exterior bit contributes one.
-/
theorem sum_arity : ∑ v, G.arity v = wd a + wd b + 2 * Fintype.card G.E := by
  have hi := Fintype.card_congr G.src
  have ho := Fintype.card_congr G.dst
  simp only [Fintype.card_sigma, Fintype.card_sum, card_slots] at hi ho
  simp only [arity, Finset.sum_add_distrib]
  omega

-- 读法：`G.cost` 等于 `Fintype.card G.V + wd a + wd b + 2 * Fintype.card G.E`。
theorem cost_eq : G.cost = Fintype.card G.V + wd a + wd b + 2 * Fintype.card G.E := by
  simp [cost, Finset.sum_add_distrib, G.sum_arity, add_assoc]

-- 读法：`G.cost` 不超过 `4 * Fintype.card G.V`。
theorem cost_trivalent (h : G.Trivalent) : G.cost ≤ 4 * Fintype.card G.V := by
  calc
    _ ≤ ∑ _ : G.V, 4 := Finset.sum_le_sum (fun v _ => Nat.add_le_add_left (h v) 1)
    _ = _ := by simp [mul_comm]

-- 读法：`Fintype.card G.V + Fintype.card G.E + wd a + wd b` 不超过 `3 * (Fintype.card G.V + wd a + wd b)`。
/-- 计入连线的体积至多为顶点数与外部比特数之和的三倍。

英文原文：Wire-inclusive volume is at most three times vertices plus exterior bits.
-/
theorem volume_trivalent (h : G.Trivalent) :
    Fintype.card G.V + Fintype.card G.E + wd a + wd b ≤
      3 * (Fintype.card G.V + wd a + wd b) := by
  have := G.cost_trivalent h
  rw [cost_eq] at this
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-!
# 二分图表示

在每条内部和外部连线上各插入一张二元相等性表。现在每个原实参位置都独占一条边，每条这样的边连接一个原顶点与一个接点。每个外部位置有独立的相等性叶节点，原有的自环也被细分。

**英文原文**

A bipartite presentation

Insert one binary equality table on each internal and external wire.
Each of the original argument positions now has its own edge. All
these edges join an original vertex and a junction. Exterior positions
have distinct equality leaves and even an old loop is subdivided.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：在后续公式中，`Joint` 是 `slots a ⊕ slots b ⊕ G.E` 的缩写。
abbrev Joint := slots a ⊕ slots b ⊕ G.E
-- 读法：在后续公式中，`End` 是 `(slots a ⊕ G.E) ⊕ slots b ⊕ G.E` 的缩写。
abbrev End := (slots a ⊕ G.E) ⊕ slots b ⊕ G.E

-- 读法：逐一匹配以下输入模式：`.inl (.inl i)`、`.inl (.inr e)`、`.inr (.inl j)`、`.inr (.inr e)`。
def junction : G.End → G.Joint
  | .inl (.inl i) => .inl i
  | .inl (.inr e) => .inr (.inr e)
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr e) => .inr (.inr e)

-- 读法：`station` 的取值由 `Sum.elim (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1)` 给出。
def station : G.End → G.V :=
  Sum.elim (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1)

-- 读法：用字段 `left_inv`、`right_inv` 构造 `(slots a ⊕ G.E) ⊕ G.Joint ≃ slots a ⊕ G.End`。
private def srcNorm : (slots a ⊕ G.E) ⊕ G.Joint ≃ slots a ⊕ G.End where
  toFun
    | .inl i => .inr (.inl i)
    | .inr (.inl i) => .inl i
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl i => .inr (.inl i)
    | .inr (.inl i) => .inl i
    | .inr (.inr j) => .inr (.inr j)
  left_inv := by rintro (i | i | j) <;> rfl
  right_inv := by rintro (i | i | j) <;> rfl

-- 读法：用字段 `left_inv`、`right_inv` 构造 `(slots b ⊕ G.E) ⊕ G.Joint ≃ slots b ⊕ G.End`。
private def dstNorm : (slots b ⊕ G.E) ⊕ G.Joint ≃ slots b ⊕ G.End where
  toFun
    | .inl j => .inr (.inr j)
    | .inr (.inl i) => .inr (.inl (.inl i))
    | .inr (.inr (.inl j)) => .inl j
    | .inr (.inr (.inr e)) => .inr (.inl (.inr e))
  invFun
    | .inl j => .inr (.inr (.inl j))
    | .inr (.inl (.inl i)) => .inr (.inl i)
    | .inr (.inl (.inr e)) => .inr (.inr (.inr e))
    | .inr (.inr j) => .inl j
  left_inv := by rintro (j | i | j | e) <;> rfl
  right_inv := by rintro (j | (i | e) | j) <;> rfl

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F a b`。
abbrev normalized [Field F] : Diagram F a b where
  V := G.V ⊕ G.Joint
  E := G.End
  table := Sum.elim G.table (fun _ => ⟨.bit, .bit, fun i j => if i = j then 1 else 0⟩)
  src := (Equiv.sumSigmaDistrib _).trans
    ((G.src.sumCongr (Equiv.sigmaUnique G.Joint (fun _ => Unit))).trans G.srcNorm)
  dst := (Equiv.sumSigmaDistrib _).trans
    ((G.dst.sumCongr (Equiv.sigmaUnique G.Joint (fun _ => Unit))).trans G.dstNorm)

-- 读法：`Fintype.card G.End` 等于 `wd a + wd b + 2 * Fintype.card G.E`。
theorem card_end : Fintype.card G.End = wd a + wd b + 2 * Fintype.card G.E := by
  simp only [End, Fintype.card_sum, card_slots]
  omega

-- 读法：`Fintype.card G.Joint` 等于 `wd a + wd b + Fintype.card G.E`。
theorem card_joint : Fintype.card G.Joint = wd a + wd b + Fintype.card G.E := by
  simp only [Joint, Fintype.card_sum, card_slots, add_assoc]

variable [Field F]

-- 读法：`G.normalized.cost` 不超过 `4 * G.cost`。
theorem cost_normalized : G.normalized.cost ≤ 4 * G.cost := by
  rw [cost_eq, cost_eq, Fintype.card_sum, card_joint, card_end]
  omega

-- 读法：要证明的命题是 `G.normalized.Admits u L`。
theorem admits_normalized {u : ℕ} {L : Set (Table F)} (hu : 2 ≤ u) (h : G.Admits u L) :
    G.normalized.Admits u L := by
  rintro (v|v)
  · exact h v
  · exact ⟨hu, Or.inl (by change 2 ≤ 3; decide)⟩

-- 读法：要证明的命题是 `G.normalized.Trivalent`。
theorem trivalent_normalized (h : G.Trivalent) : G.normalized.Trivalent := by
  rintro (v|v)
  · exact h v
  · change 2 ≤ 3
    decide

-- 读法：结论为 `G.normalized.source e = Sum.inl (G.station e) ∧ G.normalized.target e = Sum.inr (G.junction e) ∨ G.normalized.target e = Sum.inl (G.station e) ∧ G.normalized.source e = Sum.inr (G.junction e)`。
theorem bipartite (e : G.End) :
    G.normalized.source e = Sum.inl (G.station e) ∧
      G.normalized.target e = Sum.inr (G.junction e) ∨
    G.normalized.target e = Sum.inl (G.station e) ∧
      G.normalized.source e = Sum.inr (G.junction e) := by
  rcases e with (i | e) | (j | e)
  · exact .inl ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

-- 读法：`G.normalized.source e` 不等于 `G.normalized.target e`。
theorem normalized_loopless (e : G.End) : G.normalized.source e ≠ G.normalized.target e := by
  rcases G.bipartite e with ⟨h, g⟩ | ⟨g, h⟩ <;> rw [h, g] <;> simp

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-!
# 细分网络中原始站点的度数

**英文原文**

The degree of an original station in the subdivided network
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：在后续公式中，`Port` 是 `slots (G.table v).1 ⊕ slots (G.table v).2.1` 的缩写。
abbrev Port (v : G.V) := slots (G.table v).1 ⊕ slots (G.table v).2.1

-- 读法：`portEquiv` 的取值由 `(Equiv.sigmaSumDistrib _ _).trans (G.src.sumCongr G.dst)` 给出。
def portEquiv : (Σ v, G.Port v) ≃ G.End :=
  (Equiv.sigmaSumDistrib _ _).trans (G.src.sumCongr G.dst)

-- 读法：`G.station (G.portEquiv p)` 等于 `p.1`。
theorem station_port (p : Σ v, G.Port v) : G.station (G.portEquiv p) = p.1 := by
  rcases p with ⟨v, i|j⟩
  · exact congrArg Sigma.fst (G.src.symm_apply_apply ⟨v, i⟩)
  · exact congrArg Sigma.fst (G.dst.symm_apply_apply ⟨v, j⟩)

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `G.Port v ≃ {p : Σ x, G.Port x // p.1 = v}`。
private def atStation (v : G.V) : G.Port v ≃ {p : Σ x, G.Port x // p.1 = v} where
  toFun i := ⟨⟨v, i⟩, rfl⟩
  invFun p := p.2 ▸ p.1.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨x, i⟩, rfl⟩; rfl

-- 读法：`incident` 的结果类型为 `G.Port v ≃ {e : G.End // G.station e = v}`。
def incident (v : G.V) : G.Port v ≃ {e : G.End // G.station e = v} :=
  (G.atStation v).trans (G.portEquiv.subtypeEquiv (fun p => by rw [station_port]))

-- 读法：`Fintype.card {e : G.End // G.station e = v}` 等于 `G.arity v`。
theorem degree [DecidableEq G.V] (v : G.V) :
    Fintype.card {e : G.End // G.station e = v} = G.arity v := by
  rw [← Fintype.card_congr (G.incident v)]
  simp only [Port, Fintype.card_sum, card_slots, arity]

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# 带无向局部函数的网络

每个端口只指定一个所属站点，无须指定局部端口次序。对某站点求值只需它自己的端口值。选定枚举后，即可将该描述转换为具有相同边与相同权重的图式。

**英文原文**

Networks with unoriented local functions

Use one owner per port rather than specifying a local port order. Evaluating
a station only needs the values on its own ports. Choosing an enumeration
converts such a description into a diagram with the same edges and weights.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {V E I F : Type} [Fintype V] [Fintype E] {a b : Wire}

-- 读法：在后续公式中，`bundle` 是 `word (Fintype.card {i // f i = v})` 的缩写。
private abbrev bundle [Fintype I] (f : I → V) (v : V) :=
  word (Fintype.card {i // f i = v})

-- 读法：`port` 的取值由 `Fintype.equivOfCardEq (by rw [card_slots, wd_word])` 给出。
private def port [Fintype I] (f : I → V) (v : V) :
    slots (bundle f v) ≃ {i // f i = v} :=
  Fintype.equivOfCardEq (by rw [card_slots, wd_word])

-- 读法：`connect` 的取值由 `(Equiv.sigmaCongrRight (port f)).trans (Equiv.sigmaFiberEquiv f)` 给出。
private def connect [Fintype I] (f : I → V) : (Σ v, slots (bundle f v)) ≃ I :=
  (Equiv.sigmaCongrRight (port f)).trans (Equiv.sigmaFiberEquiv f)

-- 读法：当 `h : f i = v` 成立时取 `bits (bundle f v) x ((port f v).symm ⟨i, h⟩)`，否则取 `false`。
private def fill [Fintype I] (f : I → V) (v : V) (x : Val (bundle f v)) (i : I) :=
  if h : f i = v then bits (bundle f v) x ((port f v).symm ⟨i, h⟩) else false

omit [Fintype V] in
-- 读法：`fill f v ((bits (bundle f v)).symm (fun j => x (connect f ⟨v, j⟩))) i` 等于 `x i`。
private theorem fill_read [Fintype I] (f : I → V) (v : V) (x : I → Bool)
    (i : I) (hi : f i = v) :
    fill f v ((bits (bundle f v)).symm (fun j => x (connect f ⟨v, j⟩))) i = x i := by
  rw [fill, dite_eq_left hi, Equiv.apply_symm_apply]
  change x ((port f v) ((port f v).symm ⟨i, hi⟩)).val = _
  rw [Equiv.apply_symm_apply]

variable (src : slots a ⊕ E → V) (dst : slots b ⊕ E → V)
variable (k : V → (slots a ⊕ E → Bool) → (slots b ⊕ E → Bool) → F)

-- 读法：`Local` 表示以下条件：对每个 `v x y x' y'`，由 `(∀ i, src i = v → x i = x' i)` 推出 `(∀ i, dst i = v → y i = y' i) → k v x y = k v x' y'`。
def Local : Prop :=
  ∀ v x y x' y', (∀ i, src i = v → x i = x' i) → (∀ i, dst i = v → y i = y' i) →
    k v x y = k v x' y'

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F a b`。
abbrev ofLocal : Diagram F a b where
  V := V
  E := E
  table v := ⟨bundle src v, bundle dst v, fun x y => k v (fill src v x) (fill dst v y)⟩
  src := connect src
  dst := connect dst

-- 读法：`(ofLocal src dst k).arity v` 等于 `Fintype.card {i // src i = v} + Fintype.card {i // dst i = v}`。
theorem arity_ofLocal (v : V) :
    (ofLocal src dst k).arity v =
      Fintype.card {i // src i = v} + Fintype.card {i // dst i = v} := by
  simp only [arity, wd_word]

-- 读法：`(ofLocal src dst k).source e` 等于 `src (.inr e)`。两端由定义化简为同一项。
theorem source_ofLocal (e : E) : (ofLocal src dst k).source e = src (.inr e) := rfl

-- 读法：`(ofLocal src dst k).target e` 等于 `dst (.inr e)`。两端由定义化简为同一项。
theorem target_ofLocal (e : E) : (ofLocal src dst k).target e = dst (.inr e) := rfl

-- 读法：`(ofLocal src dst k).vertex x y z v` 等于 `k v (Sum.elim (bits a x) z) (Sum.elim (bits b y) z)`。
theorem vertex_ofLocal (hk : Local src dst k)
    (x : Val a) (y : Val b) (z : E → Bool) (v : V) :
    (ofLocal src dst k).vertex x y z v =
      k v (Sum.elim (bits a x) z) (Sum.elim (bits b y) z) :=
  hk _ _ _ _ _ (fill_read src _ _) (fill_read dst _ _)

variable (G : Diagram F a b)

-- 读法：`weight` 的结果类型为 `F`。
/-- 在收缩之前，允许同一条边的两个端点取不同值。

英文原文：Allow the two ends of an edge to carry different values until contraction.
-/
def weight (v : G.V) (x : slots a ⊕ G.E → Bool) (y : slots b ⊕ G.E → Bool) : F :=
  (G.table v).2.2
    ((bits (G.table v).1).symm (fun i => x (G.src ⟨v, i⟩)))
    ((bits (G.table v).2.1).symm (fun j => y (G.dst ⟨v, j⟩)))

-- 读法：要证明的命题是 `Local (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1) G.weight`。用函数外延性比较等号两侧在 `i; exact hx _ (by simp)` 处的取值。
theorem local_weight :
    Local (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1) G.weight := by
  intro v x y x' y' hx hy
  unfold weight
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg
  · funext i; exact hx _ (by simp)
  · funext i; exact hy _ (by simp)

-- 读法：`(ofLocal src dst k).weight v x y` 等于 `k v x y`。
/-- 局部权重与所选的端口枚举次序无关。

英文原文：Local weights are independent of the chosen enumeration of ports.
-/
theorem weight_ofLocal (hk : Local src dst k) (v : V) (x : slots a ⊕ E → Bool)
    (y : slots b ⊕ E → Bool) : (ofLocal src dst k).weight v x y = k v x y :=
  hk _ _ _ _ _ (fill_read src _ _) (fill_read dst _ _)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# 收缩簇

将原边分为可见边和各簇内部的边，各簇的内部边彼此不交。在每个新表内对该簇的内部边求和。这一恒等式允许自环、空簇和标量顶点。

**英文原文**

Contracting clusters

Split the old edges into the visible edges and a disjoint family of
edges internal to the clusters. Sum the latter inside each new table.
This identity allows loops, empty clusters and scalar vertices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b) (V E : Type)

-- 读法：结构的字段包括 `owner`、`hidden`、`edges`、`src_hidden`、`dst_hidden`。
structure Clustering where
  owner : G.V → V
  hidden : V → Type
  [finite : ∀ v, Fintype (hidden v)]
  edges : E ⊕ (Σ v, hidden v) ≃ G.E
  src_hidden : ∀ v e, owner (G.source (edges (.inr ⟨v, e⟩))) = v
  dst_hidden : ∀ v e, owner (G.target (edges (.inr ⟨v, e⟩))) = v

attribute [instance] Clustering.finite

namespace Clustering

variable {G V E} (C : Clustering G V E)

-- 读法：`src` 的取值由 `C.owner (G.src.symm (i.map id (fun e => C.edges (.inl e)))).1` 给出。
def src (i : slots a ⊕ E) : V :=
  C.owner (G.src.symm (i.map id (fun e => C.edges (.inl e)))).1

-- 读法：`dst` 的取值由 `C.owner (G.dst.symm (i.map id (fun e => C.edges (.inl e)))).1` 给出。
def dst (i : slots b ⊕ E) : V :=
  C.owner (G.dst.symm (i.map id (fun e => C.edges (.inl e)))).1

-- 读法：在后续公式中，`Inside` 是 `∀ v, C.hidden v → Bool` 的缩写。
abbrev Inside := ∀ v, C.hidden v → Bool

-- 读法：`assignments` 的结果类型为 `(E → Bool) × C.Inside ≃ (G.E → Bool)`。
private def assignments : (E → Bool) × C.Inside ≃ (G.E → Bool) :=
  ((Equiv.refl _).prodCongr (Equiv.piCurry (fun v (_ : C.hidden v) => Bool)).symm).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans (C.edges.arrowCongr (Equiv.refl _)))

-- 读法：`lift` 的取值由 `Sum.elim (x ∘ Sum.inl) (C.assignments (x ∘ Sum.inr, w))` 给出。
def lift {X : Type} (x : X ⊕ E → Bool) (w : C.Inside) : X ⊕ G.E → Bool :=
  Sum.elim (x ∘ Sum.inl) (C.assignments (x ∘ Sum.inr, w))

-- 读法：`C.lift x w i` 等于 `C.lift x' w' i`。
private theorem lift_local {X : Type} (o : X ⊕ G.E → V)
    (ho : ∀ v e, o (.inr (C.edges (.inr ⟨v, e⟩))) = v)
    {v : V} {x x' : X ⊕ E → Bool} {w w' : C.Inside}
    (hx : ∀ i, o (i.map id (fun e => C.edges (.inl e))) = v → x i = x' i)
    (hw : w v = w' v) (i : X ⊕ G.E) (hi : o i = v) : C.lift x w i = C.lift x' w' i := by
  rcases i with i|e
  · exact hx (.inl i) hi
  obtain ⟨j, rfl⟩ := C.edges.surjective e
  change Sum.elim (x ∘ Sum.inr) _ (C.edges.symm (C.edges j)) =
    Sum.elim (x' ∘ Sum.inr) _ (C.edges.symm (C.edges j))
  rw [Equiv.symm_apply_apply]
  rcases j with j|⟨u, t⟩
  · exact hx (.inr j) hi
  · rw [ho] at hi
    subst u
    exact congrFun hw t

variable [Field F]

-- 读法：`term` 的取值由 `∏ t : {t // C.owner t = v}, G.weight t (C.lift x w) (C.lift y w)` 给出。
private def term (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool)
    (w : C.Inside) : F :=
  ∏ t : {t // C.owner t = v}, G.weight t (C.lift x w) (C.lift y w)

-- 读法：`C.term v x y w` 等于 `C.term v x' y' w'`。这里调用 `Finset.prod_congr`。
private theorem term_local {v : V} {x x' y y'} {w w' : C.Inside}
    (hx : ∀ i, C.src i = v → x i = x' i) (hy : ∀ i, C.dst i = v → y i = y' i)
    (hw : w v = w' v) : C.term v x y w = C.term v x' y' w' := by
  apply Finset.prod_congr rfl
  intro t _
  apply G.local_weight
  · intro i hi
    exact C.lift_local (fun i => C.owner (G.src.symm i).1) C.src_hidden hx hw i
      ((congrArg C.owner hi).trans t.property)
  · intro i hi
    exact C.lift_local (fun i => C.owner (G.dst.symm i).1) C.dst_hidden hy hw i
      ((congrArg C.owner hi).trans t.property)

-- 读法：`total` 的取值由 `∑ w : C.hidden v → Bool, C.term v x y (Function.update (fun _ _ => false) v w)` 给出。
private def total (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool) : F :=
  ∑ w : C.hidden v → Bool, C.term v x y (Function.update (fun _ _ => false) v w)

-- 读法：要证明的命题是 `Local C.src C.dst C.total`。这里调用 `Finset.sum_congr`。
private theorem total_local : Local C.src C.dst C.total := by
  intro v x y x' y' hx hy
  exact Finset.sum_congr rfl fun _ _ => C.term_local hx hy rfl

variable [Fintype V] [Fintype E]

-- 读法：在后续公式中，`collapse` 是 `ofLocal C.src C.dst C.total` 的缩写。
abbrev collapse : Diagram F a b := ofLocal C.src C.dst C.total

-- 读法：使用 `weight_ofLocal` 给出的结论。
/-- 每个簇的局部核仅使用自身的隐藏比特，可按任意端口顺序读取。

英文原文：The local kernel at one cluster uses only its own hidden bits.
It can be read in any port order.
-/
theorem weight_collapse (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool) :
    C.collapse.weight v x y =
      ∑ z : C.hidden v → Bool, ∏ t : {t // C.owner t = v},
        G.weight t (C.lift x (Function.update (fun _ _ => false) v z))
          (C.lift y (Function.update (fun _ _ => false) v z)) :=
  weight_ofLocal _ _ _ C.total_local _ _ _

-- 读法：`C.collapse.eval` 等于 `G.eval`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval_collapse : C.collapse.eval = G.eval := by
  funext x y
  have prod_eq (z : E → Bool) :
      (∏ v, C.collapse.vertex x y z v) =
        ∑ w : C.Inside, ∏ v, G.vertex x y (C.assignments (z, w)) v := by
    simp only [collapse, vertex_ofLocal _ _ _ C.total_local, total, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Fintype.prod_fiberwise C.owner]
    apply Finset.prod_congr rfl
    intro v _
    change C.term v _ _ _ = C.term v (Sum.elim (bits a x) z) (Sum.elim (bits b y) z) w
    exact C.term_local (fun _ _ => rfl) (fun _ _ => rfl) (Function.update_self _ _ _)
  unfold eval
  simp_rw [prod_eq]
  rw [← Equiv.sum_comp C.assignments, Fintype.sum_prod_type]

end Clustering

variable {V} (o : G.V → V)

-- 读法：在后续公式中，`Between` 是 `{e : G.E // o (G.source e) ≠ o (G.target e)}` 的缩写。
/-- 仅保留跨越划分边界的连线。

英文原文：Keep only wires that cross the partition.
-/
abbrev Between := {e : G.E // o (G.source e) ≠ o (G.target e)}

-- 读法：用字段 `owner`、`hidden`、`edges`、`src_hidden` 构造 `Clustering G V (G.Between o)`。
def partition : Clustering G V (G.Between o) where
  owner := o
  hidden v := {e : {e : G.E // o (G.source e) = o (G.target e)} // o (G.source e) = v}
  edges :=
    ((Equiv.refl _).sumCongr (Equiv.sigmaFiberEquiv _)).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun e => o (G.source e) = o (G.target e))))
  src_hidden _ e := e.property
  dst_hidden _ e := e.val.property.symm.trans e.property

variable [Field F] [Fintype V]

-- 读法：在后续公式中，`coarsen` 是 `(G.partition o).collapse` 的缩写。
abbrev coarsen := (G.partition o).collapse

-- 读法：`(G.coarsen o).eval` 等于 `G.eval`。使用 `G.partition` 给出的结论。
theorem eval_coarsen : (G.coarsen o).eval = G.eval := (G.partition o).eval_collapse

-- 读法：`(G.coarsen o).source e` 等于 `o (G.source e)`。两端由定义化简为同一项。
theorem source_coarsen (e : G.Between o) : (G.coarsen o).source e = o (G.source e) := rfl

-- 读法：`(G.coarsen o).target e` 等于 `o (G.target e)`。两端由定义化简为同一项。
theorem target_coarsen (e : G.Between o) : (G.coarsen o).target e = o (G.target e) := rfl

-- 读法：`(G.coarsen o).cost` 等于 `Fintype.card V + wd a + wd b + 2 * Fintype.card (G.Between o)`。使用 `G.coarsen` 给出的结论。
theorem cost_coarsen : (G.coarsen o).cost =
    Fintype.card V + wd a + wd b + 2 * Fintype.card (G.Between o) :=
  (G.coarsen o).cost_eq

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# 用同时成立的连线恒等式展开网络

将每条边切成两条半边，把边上比特的两个副本放入数据包的需求端口。新站点与原站点互不相交，即使多项需求共用端点也是如此。

**英文原文**

Expanding a network by a simultaneous wire identity

Cut each edge into two half-edges. Insert the two copies of its bit
into the demand ports of the packet. The new sites and the old stations
are disjoint, even when several demands have a common endpoint.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b)
variable {S I : Type} {J : I → Type} [Fintype S] [Fintype I] [∀ i, Fintype (J i)]
variable {D : G.E → S × S} {W : (i : I) → J i → S × S}

namespace Expansion

-- 读法：在后续公式中，`Edge` 是 `G.E ⊕ G.E ⊕ T` 的缩写。
abbrev Edge (T : Type) := G.E ⊕ G.E ⊕ T

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr (.inl e)`、`.inr (.inr (.inl e))`、`.inr (.inr (.inr j))`。
def src {T : Type} (D : G.E → S × S) (w : T → S × S) : slots a ⊕ Edge G T → G.V ⊕ S
  | .inl i => .inl (G.src.symm (.inl i)).1
  | .inr (.inl e) => .inl (G.source e)
  | .inr (.inr (.inl e)) => .inr (D e).2
  | .inr (.inr (.inr j)) => .inr (w j).1

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr (.inl e)`、`.inr (.inr (.inl e))`、`.inr (.inr (.inr j))`。
def dst {T : Type} (D : G.E → S × S) (w : T → S × S) : slots b ⊕ Edge G T → G.V ⊕ S
  | .inl i => .inl (G.dst.symm (.inl i)).1
  | .inr (.inl e) => .inr (D e).1
  | .inr (.inr (.inl e)) => .inl (G.target e)
  | .inr (.inr (.inr j)) => .inr (w j).2

-- 读法：`entry` 的结果类型为 `F`。
def entry (P : Spectral.Packet.Rule F D W) (i : I) (v : G.V ⊕ S)
    (x : slots a ⊕ Edge G (J i) → Bool) (y : slots b ⊕ Edge G (J i) → Bool) : F :=
  match v with
  | .inl t => G.weight t (Sum.elim (x ∘ Sum.inl) (fun e => x (.inr (.inl e))))
      (Sum.elim (y ∘ Sum.inl) (fun e => y (.inr (.inr (.inl e)))))
  | .inr s => P.entry i s (fun e => y (.inr (.inl e))) (fun e => x (.inr (.inr (.inl e))))
      (fun j => if (W i j).1 = s then x (.inr (.inr (.inr j))) else y (.inr (.inr (.inr j))))

-- 读法：要证明的命题是 `Local (src G D (W i)) (dst G D (W i)) (entry G P i)`。这里调用 `G.local_weight`。
theorem entry_local (P : Spectral.Packet.Rule F D W) (i : I) :
    Local (src G D (W i)) (dst G D (W i)) (entry G P i) := by
  rintro (v|s) x y x' y' hx hy
  · apply G.local_weight
    · rintro (t|e) he
      · exact hx (.inl t) (congrArg Sum.inl he)
      · exact hx (.inr (.inl e)) (congrArg Sum.inl he)
    · rintro (t|e) he
      · exact hy (.inl t) (congrArg Sum.inl he)
      · exact hy (.inr (.inr (.inl e))) (congrArg Sum.inl he)
  · apply P.local'
    · exact fun e he => hy (.inr (.inl e)) (congrArg Sum.inr he)
    · exact fun e he => hx (.inr (.inr (.inl e))) (congrArg Sum.inr he)
    · intro j hj
      by_cases h : (W i j).1 = s
      · simpa only [ite_eq_left h] using hx (.inr (.inr (.inr j))) (congrArg Sum.inr h)
      · simpa only [ite_eq_right h] using hy (.inr (.inr (.inr j))) (congrArg Sum.inr (hj.resolve_left h))

end Expansion

-- 读法：在后续公式中，`expanded` 是 `ofLocal (Expansion.src G D (W i)) (Expansion.dst G D (W i)) (Expansion.entry G P i)` 的缩写。
abbrev expanded (P : Spectral.Packet.Rule F D W) (i : I) :=
  ofLocal (Expansion.src G D (W i)) (Expansion.dst G D (W i)) (Expansion.entry G P i)


-- 读法：`(G.expanded P i).weight v x y` 等于 `Expansion.entry G P i v x y`。使用 `weight_ofLocal` 给出的结论。
theorem weight_expanded (P : Spectral.Packet.Rule F D W) (i : I) (v : G.V ⊕ S)
    (x : slots a ⊕ Expansion.Edge G (J i) → Bool)
    (y : slots b ⊕ Expansion.Edge G (J i) → Bool) :
    (G.expanded P i).weight v x y = Expansion.entry G P i v x y :=
  weight_ofLocal _ _ _ (Expansion.entry_local G P i) v x y

-- 读法：`G.eval x y` 等于 `∑ l : U → Bool, ∑ r : V → Bool, ∑ z : T → Bool, ∏ v, G.vertex x y (Sum.elim l (Sum.elim r z) ∘ g) v`。
private theorem eval_split {U V T : Type} [Fintype U] [Fintype V] [Fintype T]
    (g : G.E ≃ U ⊕ V ⊕ T) (x : Val a) (y : Val b) :
    G.eval x y = ∑ l : U → Bool, ∑ r : V → Bool, ∑ z : T → Bool,
      ∏ v, G.vertex x y (Sum.elim l (Sum.elim r z) ∘ g) v := by
  let e : (G.E → Bool) ≃ (U → Bool) × (V → Bool) × (T → Bool) :=
    ((g.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))
  unfold eval
  rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type]
  rfl

-- 读法：结论为 `∑ i, (G.expanded P i).eval x y = G.eval x y`。
theorem eval_expanded (P : Spectral.Packet.Rule F D W) (x : Val a) (y : Val b) :
    ∑ i, (G.expanded P i).eval x y = G.eval x y := by
  let H (l r : G.E → Bool) := ∏ v, G.weight v (Sum.elim (bits a x) l) (Sum.elim (bits b y) r)
  have each (i : I) : (G.expanded P i).eval x y =
      ∑ l, ∑ r, H l r * ∑ z, ∏ s, P.entry i s l r z := by
    rw [eval_split (G.expanded P i) (U := G.E) (V := G.E) (T := J i) (Equiv.refl _)]
    simp_rw [expanded, vertex_ofLocal _ _ _ (Expansion.entry_local G P i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.prod_sum_type]
    simp only [Expansion.entry, Function.comp_apply, Equiv.refl_apply, Sum.elim_inl, Sum.elim_inr, ite_self]
    rfl
  simp_rw [each]
  rw [Finset.sum_comm]
  unfold eval
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← P.eval]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# 收缩同时连线恒等式中的一个加项

划分可以依赖所选的选择器。把每个切口端与分配给它的数据包站点接合后，图中只留下跨界的供给边。

**英文原文**

Contracting a summand of the simultaneous wire identity

The partition may depend on the selector. When each cut end meets its
assigned packet site, the surviving graph has just the crossing supplies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b)
variable {S I : Type} {J : I → Type} [Fintype S] [Fintype I] [∀ i, Fintype (J i)]
variable {D : G.E → S × S} {W : (i : I) → J i → S × S} (P : Spectral.Packet.Rule F D W)
variable {V : Type} [Fintype V] (o : I → G.V → V) (q : I → S → V)

-- 读法：在后续公式中，`replaced` 是 `(G.expanded P i).coarsen (Sum.elim (o i) (q i))` 的缩写。
abbrev replaced (i : I) := (G.expanded P i).coarsen (Sum.elim (o i) (q i))

-- 读法：结论为 `∑ i, (G.replaced P o q i).eval x y = G.eval x y`。
theorem eval_replaced (x : Val a) (y : Val b) :
    ∑ i, (G.replaced P o q i).eval x y = G.eval x y := by
  simp only [replaced, eval_coarsen, eval_expanded]

-- 读法：`Aligned` 表示以下条件：对每个 `i e`，`o i (G.source e) = q i (D e).1` 与 `o i (G.target e) = q i (D e).2` 同时成立。
def Aligned (D : G.E → S × S) : Prop :=
  ∀ i e, o i (G.source e) = q i (D e).1 ∧ o i (G.target e) = q i (D e).2

-- 读法：在后续公式中，`Cut` 是 `{e : J i // q i (W i e).1 ≠ q i (W i e).2}` 的缩写。
abbrev Cut (i : I) := {e : J i // q i (W i e).1 ≠ q i (W i e).2}

-- 读法：`cutEdges` 的结果类型为 `Cut (W := W) q i ≃ (G.replaced P o q i).E`。
def cutEdges (h : G.Aligned o q D) (i : I) :
    Cut (W := W) q i ≃ (G.replaced P o q i).E := by
  let f : Cut (W := W) q i → (G.replaced P o q i).E :=
    fun e => ⟨.inr (.inr e.val), e.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e t he
    exact Subtype.ext (Sum.inr.inj (Sum.inr.inj (congrArg Subtype.val he)))
  · rintro ⟨e | e | j, he⟩
    · exact (he (h i e).1).elim
    · exact (he (h i e).2.symm).elim
    · exact ⟨⟨j, he⟩, rfl⟩

-- 读法：`(G.replaced P o q i).source (G.cutEdges P o q h i e)` 等于 `q i (W i e).1`。两端由定义化简为同一项。
theorem source_cut (h : G.Aligned o q D) (i : I) (e : Cut (W := W) q i) :
    (G.replaced P o q i).source (G.cutEdges P o q h i e) = q i (W i e).1 := rfl

-- 读法：`(G.replaced P o q i).target (G.cutEdges P o q h i e)` 等于 `q i (W i e).2`。两端由定义化简为同一项。
theorem target_cut (h : G.Aligned o q D) (i : I) (e : Cut (W := W) q i) :
    (G.replaced P o q i).target (G.cutEdges P o q h i e) = q i (W i e).2 := rfl

-- 读法：`(G.replaced P o q i).cost` 等于 `Fintype.card V + wd a + wd b + 2 * Fintype.card (Cut (W := W) q i)`。
theorem cost_replaced (h : G.Aligned o q D) (i : I) :
    (G.replaced P o q i).cost =
      Fintype.card V + wd a + wd b + 2 * Fintype.card (Cut (W := W) q i) := by
  rw [cost_eq, Fintype.card_congr (G.cutEdges P o q h i)]

-- 读法：`((G.replaced P o q i).src.symm (.inl t)).1` 等于 `o i (G.src.symm (.inl t)).1`。两端由定义化简为同一项。
theorem source_exterior (i : I) (t : slots a) :
    ((G.replaced P o q i).src.symm (.inl t)).1 = o i (G.src.symm (.inl t)).1 := rfl

-- 读法：`((G.replaced P o q i).dst.symm (.inl t)).1` 等于 `o i (G.dst.symm (.inl t)).1`。两端由定义化简为同一项。
theorem target_exterior (i : I) (t : slots b) :
    ((G.replaced P o q i).dst.symm (.inl t)).1 = o i (G.dst.symm (.inl t)).1 := rfl

omit [Fintype V] in
-- 读法：`Fintype.card {t // u t = v}` 不超过 `Fintype.card {t // f t = v} + Fintype.card {t // g t = v}`。这里调用 `Fintype.card_le_of_injective`。
private theorem ends_le {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (u : X ⊕ Y → V) (f : X → V) (g : Z → V) (m : Y ↪ Z)
    (he : ∀ x, u (.inl x) = f x) (hi : ∀ y, u (.inr y) = g (m y)) (v : V) :
    Fintype.card {t // u t = v} ≤ Fintype.card {t // f t = v} + Fintype.card {t // g t = v} := by
  let p : {t // u t = v} → {t // f t = v} ⊕ {t // g t = v}
    | ⟨.inl x, h⟩ => .inl ⟨x, (he x).symm.trans h⟩
    | ⟨.inr y, h⟩ => .inr ⟨m y, (hi y).symm.trans h⟩
  rw [← Fintype.card_sum]
  apply Fintype.card_le_of_injective p
  rintro ⟨x|y, h⟩ ⟨x'|y', h'⟩ eq
  · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val (Sum.inl.inj eq)))
  · cases eq
  · cases eq
  · exact Subtype.ext (congrArg Sum.inr (m.injective (congrArg Subtype.val (Sum.inr.inj eq))))

-- 读法：`arity_replaced` 的证明用到 `G.expanded`、`Sum.elim`、`G.cutEdges`。
/-- 将所有局部供给计入时，簇元数的上界只会增大。

英文原文：Including all local supplies only increases the bound on a cluster's arity.
-/
theorem arity_replaced (h : G.Aligned o q D) (i : I) (v : V) :
    (G.replaced P o q i).arity v ≤
      (Fintype.card {t : slots a // o i (G.src.symm (.inl t)).1 = v} +
       Fintype.card {t : slots b // o i (G.dst.symm (.inl t)).1 = v}) +
      (Fintype.card {e : J i // q i (W i e).1 = v} +
       Fintype.card {e : J i // q i (W i e).2 = v}) := by
  let c := (G.expanded P i).partition (Sum.elim (o i) (q i))
  let inj := (G.cutEdges P o q h i).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun j : J i => q i (W i j).1 ≠ q i (W i j).2))
  have h₁ := ends_le c.src (fun t => o i (G.src.symm (.inl t)).1) (fun e => q i (W i e).1) inj
    (fun _ => rfl) (fun e => by
      -- 推导：从 `(G.cutEdges P o q h i).surjective e` 中取出 `t, rfl`。
      obtain ⟨t, rfl⟩ := (G.cutEdges P o q h i).surjective e
      simp only [inj, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
        Function.Embedding.subtype_apply]
      rfl) v
  have h₂ := ends_le c.dst (fun t => o i (G.dst.symm (.inl t)).1) (fun e => q i (W i e).2) inj
    (fun _ => rfl) (fun e => by
      obtain ⟨t, rfl⟩ := (G.cutEdges P o q h i).surjective e
      simp only [inj, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
        Function.Embedding.subtype_apply]
      rfl) v
  change (ofLocal c.src c.dst _).arity v ≤ _
  rw [arity_ofLocal]
  exact (Nat.add_le_add h₁ h₂).trans_eq (add_add_add_comm _ _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end
