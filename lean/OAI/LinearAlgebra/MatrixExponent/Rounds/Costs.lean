-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import OAI.LinearAlgebra.MatrixExponent.Packing.FieldLift
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Rounds.Downstream
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present
import OAI.LinearAlgebra.MatrixExponent.Shaving.Design

/-!
# 把各位置实例装入球面单元

先把组号视为一个宿主坐标。在同时选好平衡分划后，再将这个坐标分离出来。所有组共用同一个候选宿主，但各组实际占据的单元可以不同。

**英文原文**

Packing the occurrences into sphere cells

First treat the group number as a host coordinate. Split it off again
after choosing simultaneous balanced partitions. The candidate host
is common to all groups, while the occupied cells can vary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h a g D T : ℕ} {L θ : ℝ}
variable (P : Board F x y h)

-- 读法：结构的字段包括 `V`、`seats`、`A`、`size`、`site`。
structure Cells (a g D T : ℕ) (L : ℝ) where
  V : Type
  [fv : Fintype V]
  seats : Fintype.card V * 2 ^ a ≤ 2 * P.seats
  A : Type
  [fa : Fintype A]
  size : (Fintype.card A : ℝ) * D * T ≤ 17 * L
  site : A ↪ V × Cell a
  cell : P.diagram.V → A
  mass : ∀ c, push cell P.charge c ≤ (D : ℝ) * T
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  degree : ∀ v, (adj v).card ≤ g
  edge : ∀ e, let q := site (cell (P.diagram.source e))
    let p := site (cell (P.diagram.target e))
    p.2 = q.2 ∧ p.1 ∈ adj q.1

attribute [instance] Cells.fv Cells.fa

-- 读法：`0` 不超过 `P.charge v`。通过传递性衔接 `Nat.cast_nonneg` 与 `P.cover`。
theorem Board.charge_nonneg (v : P.diagram.V) : 0 ≤ P.charge v :=
  (Nat.cast_nonneg _).trans (P.cover v)

-- 读法：在后续公式中，`Board.groupLoad` 是 `push (splitAddr P.V a ha ∘ P.place) P.charge (v, i)` 的缩写。
abbrev Board.groupLoad (a : ℕ) (ha : a ≤ h) (v : P.V × Cell a) (i : Cell (h - a)) :=
  push (splitAddr P.V a ha ∘ P.place) P.charge (v, i)

-- 读法：在后续公式中，`Board.Plan` 是 `Grouping (inGroup a P.adj) (inGroup a P.adj) g g 1 ((D : ℝ) * T / 2) (P.groupLoad a ha)` 的缩写。
abbrev Board.Plan (a : ℕ) (ha : a ≤ h) (g D T : ℕ) :=
  Grouping (inGroup a P.adj) (inGroup a P.adj) g g 1 ((D : ℝ) * T / 2) (P.groupLoad a ha)

-- 读法：`0 ≤ P.groupLoad a ha v i` 与 `P.groupLoad a ha v i ≤ (D : ℝ) * T / 2` 同时成立。这里调用 `push_max`。
theorem Board.groupBound (ha : a ≤ h) (ok : P.Ready g D T L θ) (v : P.V × Cell a) (i : Cell (h - a)) :
    0 ≤ P.groupLoad a ha v i ∧ P.groupLoad a ha v i ≤ (D : ℝ) * T / 2 := by
  refine ⟨push_nonneg _ _ P.charge_nonneg _, ?_⟩
  exact push_max _ (fun _ => True) P.charge _ (by positivity) (fun v => (ok.2.2.2 v).1)
    (by simp) ((splitAddr _ a ha).injective.comp P.one).injOn _

-- 读法：`v` 属于 `inGroup a P.adj z`。这里调用 `mem_inGroup`。
private theorem inGroup_sym (v z : P.V × Cell a) (hz : z ∈ inGroup a P.adj v) :
    v ∈ inGroup a P.adj z := by
  obtain ⟨he, hb⟩ := (mem_inGroup _ _ _ _).mp hz
  exact (mem_inGroup _ _ _ _).mpr ⟨P.sym _ _ he, hb.symm⟩

-- 读法：`Board.withCells` 的结果类型为 `Cells P a ((4 * g) ^ 300) D T L`。
def Board.withCells (hg : 0 < g) (hD : 0 < D) (hT : 0 < T) (ha : a < h) (ok : P.Ready g D T L θ)
    (slack : (P.seats : ℝ) * D * T ≤ L * (2 : ℝ) ^ (h - a))
    (G : P.Plan a ha.le g D T) : Cells P a ((4 * g) ^ 300) D T L := by
  let f := splitAddr P.V a ha.le ∘ P.place
  let w v i := push f P.charge (v, i)
  let N := inGroup a P.adj
  let B := (D : ℝ) * T / 2
  have hb : 0 < B := by unfold B; positivity
  let loc (p : (P.V × Cell a) × Cell (h - a)) := G.loc p.1 p.2
  let place : G.Colony ↪ Site P.V (h - a) × Cell a :=
    ⟨splitSite ∘ G.site, splitSite.injective.comp G.site_injective⟩
  have eq : (2 : ℝ) ^ 1 * B = (D : ℝ) * T := by unfold B; ring
  have count : (Fintype.card G.Colony : ℝ) * D * T ≤ 17 * L := by
    have total : (∑ v, ∑ i, w v i) ≤ L := by
      rw [← Fintype.sum_prod_type (push f P.charge), sum_push]
      exact ok.2.1
    have hs : (Fintype.card (P.V × Cell a) : ℝ) * ((D : ℝ) * T) ≤ L := by
      apply le_of_mul_le_mul_right _ (by positivity : (0 : ℝ) < 2 ^ (h - a))
      refine le_trans ?_ slack
      simp only [Board.seats, Fintype.card_prod, card_cell, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have he : (2 : ℝ) ^ a * 2 ^ (h - a) = 2 ^ h := by rw [← pow_add, Nat.add_sub_of_le ha.le]
      rw [← he]
      exact le_of_eq (by ring)
    have hm := G.card_bound
    change (Fintype.card G.Colony : ℝ) ≤ Fintype.card (P.V × Cell a) + 16 * (∑ v, ∑ i, w v i) / ((2 : ℝ) ^ 1 * B) at hm
    rw [eq] at hm
    have ht := mul_le_mul_of_nonneg_right hm (show 0 ≤ (D : ℝ) * T by positivity)
    rw [add_mul, div_mul_cancel₀ _ (by positivity)] at ht
    linarith
  refine {
    V := Site P.V (h - a)
    seats := ?_
    A := G.Colony
    size := count
    site := place
    cell := loc ∘ f
    mass := ?_
    adj := near P.adj g
    sym := near_symm P.sym g
    degree := near_card P.adj g hg ok.1
    edge := ?_ }
  · refine (Nat.mul_le_mul_right _ (Site.card P.V (h - a))).trans_eq ?_
    unfold Board.seats
    have he : (2 : ℕ) ^ (h - a) * 2 ^ a = 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel ha.le]
    rw [← he]
    ring
  · intro c
    rw [← push_comp]
    refine le_trans ?_ eq.le
    have hm := G.here_load hb.le (G.site c)
    simp only [Grouping.here, G.site_injective.eq_iff] at hm
    refine le_trans ?_ hm
    exact sum_le_sum (fun p _ => by unfold loc; split_ifs <;> rfl)
  · intro e
    let v := P.place (P.diagram.source e)
    let z := P.place (P.diagram.target e)
    obtain ⟨he, hz⟩ := P.edge e
    change z.2 = v.2 at he
    have h' : (z.1, ancestor ha.le z.2) ∈ N (v.1, ancestor ha.le v.2) :=
      (mem_inGroup _ _ _ _).mpr ⟨hz, congrArg (ancestor ha.le) he⟩
    have hd := G.here_full (inGroup_sym P) le_rfl h' (suffix a v.2)
    have hm := split_near P.adj g hd
    change (splitSite (G.here (z.1, ancestor ha.le z.2) (suffix a z.2))).2 = _ ∧
      (splitSite (G.here (z.1, ancestor ha.le z.2) (suffix a z.2))).1 ∈ _
    rw [congrArg (suffix a) he]
    exact ⟨hm.1.symm, hm.2⟩

-- 读法：`(Cells P a ((4 * g) ^ 300) D T L)` 有元素。
theorem cells (hg : 0 < g) (hD : 0 < D) (hT : 0 < T) (ha : a < h) (ok : P.Ready g D T L θ)
    (slack : (P.seats : ℝ) * D * T ≤ L * (2 : ℝ) ^ (h - a)) :
    Nonempty (Cells P a ((4 * g) ^ 300) D T L) := by
  let N := inGroup a P.adj
  have hd v : (N v).card ≤ g := by simpa [N, inGroup] using ok.1 v.1
  obtain ⟨G⟩ := pack_group N N g g hg hg (inGroup_sym P) (inGroup_sym P) (fun _ => subset_rfl) hd hd
    (le_refl 1) (by omega : 1 ≤ h - a) _ (by positivity) _ (P.groupBound ha.le ok)
  exact ⟨P.withCells hg hD hT ha ok slack G⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 将外部比特移至恒等站点

为每个外部比特引入一个恒等映射。按单元将它们合并后，每个具有外部端口的单元各有一个固定不动的站点。

**英文原文**

Moving exterior bits to identity stations

Introduce one identity per exterior bit. Coarsening these by cell gives
one immobile station in each cell that has exterior ports.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

variable {F V : Type} [Field F] {x y : Wire}

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Σ _ : T, Unit) ≃ T`。
private def forget (T : Type) : (Σ _ : T, Unit) ≃ T where
  toFun := Sigma.fst
  invFun t := ⟨t, ()⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- 读法：用字段 `table`、`src`、`dst` 构造 `Border F (slots x ⊕ slots y) x y x y`。
def ident (F : Type) [Field F] (x y : Wire) : Border F (slots x ⊕ slots y) x y x y where
  table _ := ⟨.bit, .bit, fun i j => if i = j then 1 else 0⟩
  src := forget _
  dst := (forget _).trans (Equiv.sumComm _ _)

-- 读法：`(ident F x y).tensor t` 等于 `t`。
theorem ident_tensor (t : slots x ⊕ slots y) : (ident F x y).tensor t = t := by
  cases t <;> rfl

-- 读法：`(ident F x y).weight s t u v` 等于 `if s = u ∧ t = v then 1 else 0`。按 `b = c` 成立与否分情况。
private theorem weight_ident (s u : Val x) (t v : Val y) :
    (ident F x y).weight s t u v = if s = u ∧ t = v then 1 else 0 := by
  unfold Border.weight
  rw [Fintype.prod_sum_type]
  change (∏ i, if bits x s i = bits x u i then (1 : F) else 0) *
    (∏ j, if bits y v j = bits y t j then 1 else 0) = _
  have delta (a : Wire) (b c : Val a) :
      (∏ i, if bits a b i = bits a c i then (1 : F) else 0) = if b = c then 1 else 0 := by
    by_cases h : b = c
    · simp [h]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp ((bits a).injective.ne h)
      rw [ite_eq_right h]
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp only [delta, eq_comm (a := v), ite_mul, one_mul, zero_mul, ite_and]

variable (G : Diagram F x y)

-- 读法：`((ident F x y).attach G).eval` 等于 `G.eval`。用函数外延性比较等号两侧在 `s t` 处的取值。
theorem eval_ident : ((ident F x y).attach G).eval = G.eval := by
  funext s t
  rw [Border.eval_attach]
  simp [weight_ident, ite_and, mul_ite]

-- 读法：`portEnd ((ident F x y).attach G) i` 等于 `Sum.inr i`。
theorem port_ident (i : slots x ⊕ slots y) : portEnd ((ident F x y).attach G) i = Sum.inr i := by
  cases i <;> rfl

variable [Fintype V] (o : G.V → V)

-- 读法：`portEnd (G.coarsen o) i` 等于 `o (portEnd G i)`。
theorem port_coarsen (i : slots x ⊕ slots y) :
    portEnd (G.coarsen o) i = o (portEnd G i) := by cases i <;> rfl

-- 读法：`(G.coarsen o).arity v` 不超过 `push o (fun i => (G.arity i : ℝ)) v`。这里调用 `add_le_add`。
theorem arity_coarsen (v : V) : (G.coarsen o).arity v ≤ push o (fun i => (G.arity i : ℝ)) v := by
  let f := fun i => (o (G.source i), o (G.target i))
  let e : (G.coarsen o).E ↪ G.E := Function.Embedding.subtype _
  have ha := site_arity (G.coarsen o) id v
  have h₁ : push id (fun i : (G.coarsen o).V => ((G.coarsen o).arity i : ℝ)) v =
      (G.coarsen o).arity v := by simp [push]
  rw [h₁] at ha
  rw [ha, site_arity]
  apply add_le_add
  · simp only [port_load, Function.id_comp]
    rw [show portEnd (G.coarsen o) = o ∘ portEnd G from funext (port_coarsen _ _)]
  · exact Nat.cast_le.mpr (degree_select f e v)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 单元中可移动及不可移动的站点

为可移动站点预留 `D` 个槽位，并为外部恒等映射留一个槽位。先保留各标量的乘积，再舍弃标量槽位。

**英文原文**

The mobile and immobile stations in a cell

Use `D` slots for mobile stations and one for the exterior identity.
Discard the scalar slots only after retaining their product.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Cells

open Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g D T : ℕ} {L : ℝ}
variable {P : Board F x y h} (C : Cells P a g D T L) (bin : P.diagram.V → Fin D)

-- 读法：在后续公式中，`Slot` 是 `C.A × Option (Fin D)` 的缩写。
abbrev Slot := C.A × Option (Fin D)
-- 读法：在后续公式中，`before` 是 `(ident F x y).attach P.diagram` 的缩写。
abbrev before (P : Board F x y h) := (ident F x y).attach P.diagram

-- 读法：`pack` 的取值由 `(C.cell v, bin v)` 给出。
def pack (v : P.diagram.V) : C.A × Fin D := (C.cell v, bin v)

-- 读法：逐一匹配以下输入模式：`.inl v`、`.inr q`。
def seat : (before P).V → C.Slot
  | .inl v => (C.cell v, some (bin v))
  | .inr q => (C.cell (portEnd P.diagram q), none)

-- 读法：在后续公式中，`grouped` 是 `(before P).coarsen (C.seat bin)` 的缩写。
abbrev grouped := (before P).coarsen (C.seat bin)
-- 读法：在后续公式中，`stations` 是 `(C.grouped bin).prune` 的缩写。
abbrev stations := (C.grouped bin).prune

-- 读法：`place` 的取值由 `C.site v.val.1` 给出。
def place (v : (C.stations bin).V) := C.site v.val.1

-- 读法：存在 `c : F`，对每个 `x y`，`c * (C.stations bin).eval x y` 等于 `P.diagram.eval x y`。
theorem evaluation : ∃ c : F, ∀ x y,
    c * (C.stations bin).eval x y = P.diagram.eval x y := by
  obtain ⟨c, hc⟩ := (C.grouped bin).eval_prune
  refine ⟨c, fun x y => (hc _ _).trans ?_⟩
  rw [Diagram.eval_coarsen, eval_ident]

-- 读法：`(portEnd (C.stations bin) q).val` 等于 `(C.cell (portEnd P.diagram q), none)`。
theorem port (q : slots x ⊕ slots y) :
    (portEnd (C.stations bin) q).val = (C.cell (portEnd P.diagram q), none) := by
  cases q <;> rfl

-- 读法：`(C.stations bin).source e` 不等于 `(C.stations bin).target e`。
theorem loopless (e : (C.stations bin).E) :
    (C.stations bin).source e ≠ (C.stations bin).target e :=
  fun h => e.property (congrArg Subtype.val h)

-- 读法：结论为 `let p := C.place bin ((C.stations bin).source e) let q := C.place bin ((C.stations bin).target e) q.2 = p.2 ∧ (q.1 = p.1 ∨ q.1 ∈ C.adj p.1)`。
theorem contact (e : (C.stations bin).E) :
    let p := C.place bin ((C.stations bin).source e)
    let q := C.place bin ((C.stations bin).target e)
    q.2 = p.2 ∧ (q.1 = p.1 ∨ q.1 ∈ C.adj p.1) := by
  rcases e with ⟨i|j|k, _⟩
  · exact ⟨(C.edge i).1, .inr (C.edge i).2⟩
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩

-- 读法：`estimate` 的取值由 `q.2.elim (2 * exterior P.diagram C.cell q.1) (fun i => push (C.pack bin) P.charge (q.1, i))` 给出。
def estimate (q : C.Slot) : ℝ :=
  q.2.elim (2 * exterior P.diagram C.cell q.1)
    (fun i => push (C.pack bin) P.charge (q.1, i))

omit [Field F] in
-- 读法：`0` 不超过 `C.estimate bin q`。这里调用 `mul_nonneg`。
theorem estimate_nonneg (q : C.Slot) : 0 ≤ C.estimate bin q := by
  obtain ⟨c, _|i⟩ := q
  · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  · exact push_nonneg _ _ P.charge_nonneg _

-- 读法：`(C.stations bin).arity v` 不超过 `C.estimate bin v.1`。
theorem arity (v : (C.stations bin).V) : (C.stations bin).arity v ≤ C.estimate bin v.1 := by
  refine (arity_coarsen (before P) (C.seat bin) v.val).trans ?_
  unfold push
  rw [Fintype.sum_sum_type]
  obtain ⟨⟨c, _|i⟩, hv⟩ := v
  · simp only [seat, Prod.mk.injEq, reduceCtorEq, and_false, ite_false, sum_const_zero, zero_add,
      and_true]
    change _ ≤ 2 * (exterior P.diagram C.cell c : ℝ)
    rw [port_load, push, mul_sum]
    apply sum_le_sum
    intro q _
    change (if C.cell (portEnd P.diagram q) = c then (2 : ℝ) else 0) ≤ _
    simp [Function.comp_apply, mul_ite]
  · simp only [seat, Prod.mk.injEq, reduceCtorEq, and_false, ite_false, sum_const_zero, add_zero,
      Option.some.injEq]
    apply sum_le_sum
    intro v _
    simp only [pack, Prod.mk.injEq]
    split_ifs
    · exact P.cover v
    · exact le_rfl

omit [Field F] in
-- 读法：`(exterior P.diagram C.cell c : ℝ)` 不超过 `(D : ℝ) * T`。这里调用 `le_add_of_nonneg_right`。
theorem exterior_le (c : C.A) : (exterior P.diagram C.cell c : ℝ) ≤ (D : ℝ) * T := calc
  _ ≤ push C.cell (fun v => (P.diagram.arity v : ℝ)) c := by
    rw [site_arity]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  _ ≤ push C.cell P.charge c := push_le_push _ P.cover _
  _ ≤ _ := C.mass c

omit [Field F] in
-- 读法：`(∑ i, C.estimate bin (c, i))` 不超过 `3 * (D : ℝ) * T`。
theorem cell_estimate (c : C.A) : (∑ i, C.estimate bin (c, i)) ≤ 3 * (D : ℝ) * T := by
  rw [Fintype.sum_option]
  change 2 * (exterior P.diagram C.cell c : ℝ) + (∑ i, push (C.pack bin) P.charge (c, i)) ≤ _
  rw [← push_fst, push_comp, show Prod.fst ∘ C.pack bin = C.cell from rfl]
  linarith [C.exterior_le c, C.mass c]

omit [Field F] in
-- 读法：`(∑ z, (C.estimate bin z) ^ 2)` 不超过 `7 * L * T`。这里调用 `sum_le_sum`。
theorem estimate_squares
    (bound : ∑ z, (push (C.pack bin) P.charge z) ^ 2 ≤ 3 * L * T)
    (exposed : ((wd x + wd y : ℕ) : ℝ) * D ≤ L) :
    (∑ z, (C.estimate bin z) ^ 2) ≤ 7 * L * T := by
  have he : (∑ c, (exterior P.diagram C.cell c : ℝ)) = wd x + wd y := by
    simp only [port_load, sum_push, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_sum, card_slots, Nat.cast_add]
  have he' : (∑ c, (2 * (exterior P.diagram C.cell c : ℝ)) ^ 2) ≤ 4 * L * T := calc
    _ ≤ ∑ c, 4 * ((D : ℝ) * T) * exterior P.diagram C.cell c := by
      apply sum_le_sum
      intro c _
      nlinarith only [mul_le_mul_of_nonneg_right (C.exterior_le c)
        (Nat.cast_nonneg (α := ℝ) (exterior P.diagram C.cell c))]
    _ ≤ _ := by
      rw [← mul_sum, he]
      rw [Nat.cast_add] at exposed
      linarith only [mul_le_mul_of_nonneg_right exposed (Nat.cast_nonneg (α := ℝ) T)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_option]
  rw [sum_add_distrib]
  rw [Fintype.sum_prod_type] at bound
  exact (add_le_add he' bound).trans_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Cells
end

/-!
# 局部输入的统一宽度

每个站点至多涉及 `g+1` 个单元，并且在每个单元中至多接触 `D+1` 个槽位。因此当 `g < D` 且 `R D² ≤ T` 时，对两个定向均作填充至多使该站点的元数增加 `4T`。

**英文原文**

Uniform width for the local input

A station can touch at most `D+1` slots in each of at most `g+1`
cells. Padding both orientations therefore adds at most `4T` to
its arity when `g < D` and `R D² ≤ T`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Cells

open Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g D T R : ℕ} {L : ℝ}
variable {P : Board F x y h} (C : Cells P a g D T L) (bin : P.diagram.V → Fin D)

-- 读法：`Fintype.card {v // p v}` 不超过 `s.card * (D + 1)`。这里调用 `Subtype.ext`。
theorem count_slots (s : Finset C.V) (i : Cell a) (p : (C.stations bin).V → Prop)
    [DecidablePred p]
    (hp : ∀ v, p v → (C.place bin v).1 ∈ s ∧ (C.place bin v).2 = i) :
    Fintype.card {v // p v} ≤ s.card * (D + 1) := by
  let f (v : {v // p v}) : s × Option (Fin D) :=
    (⟨(C.place bin v.1).1, (hp _ v.2).1⟩, v.1.val.2)
  have inj : Function.Injective f := by
    intro v w he
    have ha := congrArg (fun t : s × Option (Fin D) => t.1.val) he
    have hz := (hp _ v.2).2.trans (hp _ w.2).2.symm
    have hb := congrArg Prod.snd he
    exact Subtype.ext (Subtype.ext (Prod.ext (C.site.injective (Prod.ext ha hz)) hb))
  simpa [Fintype.card_prod] using Fintype.card_le_of_injective f inj

omit [Field F] in
-- 读法：存在 `e`，`G.source e = v` 与 `G.target e = w` 同时成立。
private theorem width_pos {G : Diagram F x y} {v w : G.V} (h : 0 < G.width v w) :
    ∃ e, G.source e = v ∧ G.target e = w := by
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp h
  exact ⟨e.1, e.2⟩

-- 读法：`Fintype.card {w // 0 < (C.stations bin).width v w ∨ 0 < (C.stations bin).width w v}` 不超过 `(g + 1) * (D + 1)`。
private theorem contacts (v : (C.stations bin).V) :
    Fintype.card {w // 0 < (C.stations bin).width v w ∨ 0 < (C.stations bin).width w v} ≤
      (g + 1) * (D + 1) := by
  let p := C.place bin v
  let s := insert p.1 (C.adj p.1)
  have hs : s.card ≤ g + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right (C.degree p.1) _)
  refine le_trans (C.count_slots bin s p.2 _ ?_) (Nat.mul_le_mul_right _ hs)
  intro w hw
  rw [show s = insert p.1 (C.adj p.1) from rfl, mem_insert]
  rcases hw with hw | hw
  · obtain ⟨e, hs, ht⟩ := width_pos hw
    have he := C.contact bin e
    rw [hs, ht] at he
    exact ⟨he.2, he.1⟩
  · obtain ⟨e, hs, ht⟩ := width_pos hw
    have he := C.contact bin e
    rw [hs, ht] at he
    exact ⟨he.2.imp Eq.symm (C.sym _ _), he.1.symm⟩

-- 读法：在后续公式中，`padded` 是 `(C.stations bin).pad R` 的缩写。
abbrev padded (R : ℕ) := (C.stations bin).pad R

-- 读法：`((C.padded bin R).arity v : ℝ)` 不超过 `C.estimate bin v.1 + 4 * T`。这里调用 `Nat.cast_le.mpr`。
theorem arity_padded (hg : g < D) (hR : R * D ^ 2 ≤ T) (v : (C.stations bin).V) :
    ((C.padded bin R).arity v : ℝ) ≤ C.estimate bin v.1 + 4 * T := by
  have hm : 2 * R * ((g + 1) * (D + 1)) ≤ 4 * T := calc
    _ ≤ 2 * R * (D * (2 * D)) := by gcongr <;> omega
    _ = 4 * (R * D ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hR
  have hx : (C.padded bin R).arity v ≤ (C.stations bin).arity v + 4 * T :=
    ((C.stations bin).arity_pad R v).trans (Nat.add_le_add_left
      ((Nat.mul_le_mul_left (2 * R) (C.contacts bin v)).trans hm) _)
  exact (Nat.cast_le.mpr hx).trans (by push_cast; exact add_le_add_left (C.arity bin v) _)

-- 读法：`(∑ v : (C.stations bin).V, f v.1)` 不超过 `∑ z, f z`。这里调用 `sum_le_sum_of_subset_of_nonneg`。
private theorem sum_slots (f : C.Slot → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∑ v : (C.stations bin).V, f v.1) ≤ ∑ z, f z := by
  let e : (C.stations bin).V ↪ C.Slot := Function.Embedding.subtype _
  change (∑ v : (C.stations bin).V, f (e v)) ≤ _
  rw [← sum_map]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => hf z

-- 读法：`push (C.place bin) (fun v => ((C.padded bin R).arity v : ℝ)) p` 不超过 `100 * (D : ℝ) * T`。这里调用 `sum_le_sum`。
theorem padded_mass (hg : g < D) (hR : R * D ^ 2 ≤ T) (p : C.V × Cell a) :
    push (C.place bin) (fun v => ((C.padded bin R).arity v : ℝ)) p ≤ 100 * (D : ℝ) * T := by
  let f (z : C.Slot) := if C.site z.1 = p then C.estimate bin z + 4 * T else 0
  have hf z : 0 ≤ f z := by
    have := C.estimate_nonneg bin z
    unfold f
    positivity
  refine le_trans ?_ ((C.sum_slots bin f hf).trans ?_)
  · apply sum_le_sum
    intro v _
    by_cases h : C.site v.1.1 = p
    · simpa only [f, place, h, ite_true] using C.arity_padded bin hg hR v
    · simp only [f, place, h, ite_false, le_refl]
  rw [Fintype.sum_prod_type]
  by_cases hp : ∃ c, C.site c = p
  -- 推导：从 `hp` 中取出 `c, rfl`。
  · obtain ⟨c, rfl⟩ := hp
    rw [Fintype.sum_eq_single c]
    swap
    · intro b hb
      simp [f, hb]
    simp only [f, ite_true, sum_add_distrib, sum_const, card_univ, Fintype.card_option, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have ht : (T : ℝ) ≤ D * T := le_mul_of_one_le_left (by positivity)
      (by exact_mod_cast (show 1 ≤ D by omega))
    nlinarith only [ht, C.cell_estimate bin c, Nat.cast_nonneg (α := ℝ) T]
  · have hn c : C.site c ≠ p := fun he => hp ⟨c, he⟩
    simp only [f, hn, ite_false, sum_const_zero]
    positivity

-- 读法：`(∑ v, ((C.padded bin R).arity v : ℝ) ^ 2)` 不超过 `10000 * L * T`。这里调用 `sum_le_sum`。
theorem padded_squares (hg : g < D) (hR : R * D ^ 2 ≤ T)
    (budget : ∑ z, (C.estimate bin z) ^ 2 ≤ 7 * L * T) :
    (∑ v, ((C.padded bin R).arity v : ℝ) ^ 2) ≤ 10000 * L * T := by
  let f (z : C.Slot) := 2 * (C.estimate bin z) ^ 2 + 32 * (T : ℝ) ^ 2
  have hf z : 0 ≤ f z := by unfold f; positivity
  refine le_trans ?_ ((C.sum_slots bin f hf).trans ?_)
  · apply sum_le_sum
    intro v _
    have he := C.arity_padded bin hg hR v
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) he 2
    unfold f
    nlinarith only [this, sq_nonneg (C.estimate bin v.1 - 4 * T)]
  -- 推导：记下中间结论 `hL`：`0 ≤ L`。
  have hL : 0 ≤ L := by
    have hn : (0 : ℝ) ≤ (Fintype.card C.A : ℝ) * D * T := by positivity
    linarith [C.size]
  have count : Fintype.card C.Slot ≤ 2 * Fintype.card C.A * D := by
    simp only [Slot, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    rw [mul_comm 2, mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have hcount : (Fintype.card C.Slot : ℝ) * T ≤ 34 * L := by
    have hx := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr count) (Nat.cast_nonneg (α := ℝ) T)
    push_cast at hx
    linarith only [hx, C.size]
  -- 推导：记下中间结论 `ht`：`= mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg (α`。
  have ht := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg (α := ℝ) T)
  simp only [f, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  nlinarith only [budget, ht, mul_nonneg hL (Nat.cast_nonneg (α := ℝ) T)]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Cells
end

/-!
# 局部集中之前的分组步骤

**英文原文**

The grouping step before local concentration
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Packing Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g D T R : ℕ} {L θ : ℝ}

-- 读法：`Cells.input` 的结果类型为 `Input F x y a D T R g (10000 * L)`。
def Cells.input {P : Board F x y h} (C : Cells P a g D T L)
    (hg : g < D) (hR : 0 < R) (hr : R * D ^ 2 ≤ T)
    (hL : 0 ≤ L) (ext : ((wd x + wd y : ℕ) : ℝ) * D ≤ L) (b : P.diagram.V → Fin D)
    (hb' : ∑ z, (push (C.pack b) P.charge z) ^ 2 ≤ 3 * L * T) :
    Input F x y a D T R g (10000 * L) := by
  let G := C.stations b
  let p := C.place b
  let mobile (v : G.V) := v.val.2 ≠ none
  have present : (univ.image p).card ≤ Fintype.card C.A := by
    refine (card_le_card (t := univ.image C.site) ?_).trans card_image_le
    rintro z hz
    obtain ⟨v, _, rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem _ (mem_univ v.val.1)
  have fixed : Fintype.card {v : G.V // ¬mobile v} ≤ Fintype.card C.A := by
    apply Fintype.card_le_of_injective (fun v : {v : G.V // ¬mobile v} => v.val.val.1)
    intro v w he
    exact Subtype.ext (Subtype.ext (Prod.ext he ((not_ne_iff.mp v.2).trans (not_ne_iff.mp w.2).symm)))
  have hsize (m : ℕ) (hm : m ≤ Fintype.card C.A) : (m : ℝ) * D * T ≤ 10000 * L := calc
    _ ≤ (Fintype.card C.A : ℝ) * D * T := by gcongr
    _ ≤ _ := C.size.trans (by linarith)
  exact {
    V := C.V
    diagram := G.pad R
    place := p
    adj := C.adj
    sym := C.sym
    degree := C.degree
    edge e := by
      obtain ⟨i, h₁, h₂⟩ := G.contact_pad R e
      rw [← h₁, ← h₂]
      exact C.contact b i
    loopless e := by
      obtain ⟨i, h₁, h₂⟩ := G.contact_pad R e
      rw [← h₁, ← h₂]
      exact C.loopless b i
    positive v := v.property.trans_le (G.arity_le_pad R v)
    width := G.divisible_pad hR
    mobile := mobile
    ext t := by
      have hv : portEnd (G.pad R) t = portEnd G t := by cases t <;> rfl
      unfold mobile
      rw [hv, C.port b]
      exact not_not.mpr rfl
    occupied := by exact_mod_cast hsize _ present
    immobile := by
      have hh := hsize _ fixed
      simp only [Fintype.card_eq_nat_card] at hh ⊢
      exact_mod_cast hh
    count m := by
      have hx := C.count_slots b {m.1} m.2 (fun v => C.place b v = m)
        (fun _ he => by rw [he]; simp)
      rw [card_singleton, one_mul] at hx
      exact hx.trans (by omega)
    mass := C.padded_mass b hg hr
    squares := C.padded_squares b hg hr (C.estimate_squares b hb' ext) }

-- 读法：存在 `(Q : Input F x y a D T R g (10000 * L)) (c : F)`，`(∀ i j, c * Q.diagram.eval i j = P.diagram.eval i j)` 与 `Fintype.card Q.V * 2 ^ a ≤ 2 * P.seats` 同时成立。
private theorem Cells.prepare {P : Board F x y h} (C : Cells P a g D T L)
    (hg : g < D) (hR : 0 < R) (hr : R * D ^ 2 ≤ T)
    (sum : ∑ v, P.charge v ≤ L) (sq : ∑ v, P.charge v ^ 2 ≤ L * T)
    (ext : ((wd x + wd y : ℕ) : ℝ) * D ≤ L) :
    ∃ (Q : Input F x y a D T R g (10000 * L)) (c : F),
      (∀ i j, c * Q.diagram.eval i j = P.diagram.eval i j) ∧
      Fintype.card Q.V * 2 ^ a ≤ 2 * P.seats := by
  obtain ⟨b, hb⟩ := bins C.cell P.charge D T (by omega) P.charge_nonneg C.mass
  have hb' : ∑ z, (push (C.pack b) P.charge z) ^ 2 ≤ 3 * L * T := by
    refine hb.trans ?_
    linarith only [sq, mul_le_mul_of_nonneg_left sum (Nat.cast_nonneg (α := ℝ) T)]
  let G := C.stations b
  let Q := C.input hg hR hr ((sum_nonneg fun v _ => P.charge_nonneg v).trans sum) ext b hb'
  -- 推导：从 `C.evaluation b` 中取出 `c, hc`。
  obtain ⟨c, hc⟩ := C.evaluation b
  refine ⟨Q, c, fun i j => ?_, C.seats⟩
  change c * (G.pad R).eval i j = _
  rw [G.eval_pad]
  exact hc i j

-- 读法：存在 `(Q : Input F x y a D T R ((4 * g) ^ 300) (10000 * L)) (c : F)`，`(∀ i j, c * Q.diagram.eval i j = P.diagram.eval i j)` 与 `Fintype.card Q.V * 2 ^ a ≤ 2 * P.seats` 同时成立。这里调用 `C.prepare`。
/-- 首次分组为局部集中提供输入，总预算只发生一个具有绝对界的变化。

英文原文：The first grouping step supplies the input to local concentration with
an absolute change in the total budget.
-/
theorem prepare (P : Board F x y h) (hg : 0 < g) (hd : (4 * g) ^ 300 < D) (ht : 0 < T)
    (hR : 0 < R) (hr : R * D ^ 2 ≤ T) (ha : a < h) (ok : P.Ready g D T L θ)
    (slack : (P.seats : ℝ) * D * T ≤ L * (2 : ℝ) ^ (h - a)) (ext : ((wd x + wd y : ℕ) : ℝ) * D ≤ L) :
    ∃ (Q : Input F x y a D T R ((4 * g) ^ 300) (10000 * L)) (c : F),
      (∀ i j, c * Q.diagram.eval i j = P.diagram.eval i j) ∧
      Fintype.card Q.V * 2 ^ a ≤ 2 * P.seats := by
  obtain ⟨C⟩ := cells P hg (by omega) ht ha ok slack
  exact C.prepare hd hR hr ok.2.1 ok.2.2.1 ext

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 将球面分组并入后续轮次

**英文原文**

Adding the sphere grouping to the downstream round
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Finset

-- 读法：`localDegree` 的取值由 `(4 * 5 : ℕ) ^ 300` 给出。
def localDegree := (4 * 5 : ℕ) ^ 300

-- 读法：`8` 不超过 `localDegree`。
theorem localDegree_large : 8 ≤ localDegree := by
  unfold localDegree
  generalize he : 300 = n
  exact (by decide : 8 ≤ 4 * 5).trans (Nat.le_self_pow (by omega : n ≠ 0) _)

variable {F : Type} [Field F] {δ : ℝ}

-- 读法：要证明的命题是 `p.Works F T`。
theorem Design.step (p : Design δ) (T R H n : ℕ) (θ : ℝ)
    (hD : localDegree < p.D) (ht : 0 < T) (hR : 0 < R) (hr' : R * p.D ^ 2 ≤ T)
    (hH : 2 * H ≤ p.overhead) (hd : p.D ≤ p.overhead) (hs : p.steps = n + 1) (hf : p.floor ≤ θ)
    (next : ∀ (x y : Wire) (h a r : ℕ) (L : ℝ)
      (Q : Input F x y h p.D T R localDegree (10000 * L)),
      a + n * r ≤ h → H ≤ 2 ^ r → (H : ℝ) * T * (Fintype.card Q.V * 2 ^ h : ℕ) ≤ L * (2 : ℝ) ^ r →
      Expansion Q.diagram.eval (H * (1 + Nat.clog 2 (T + 1))*⌈L / (T : ℝ)⌉₊) (fun S : Board F x y a =>
        S.Ready 4 p.D (2 ^ p.growth * T) (L / 2 ^ p.gain) θ ∧ S.seats ≤ H * (Fintype.card Q.V * 2 ^ h))) :
    p.Works F T := by
  intro x y h P r a L ok ha hsize ext slack
  -- 推导：记下中间结论 `hr`：`0 < r`。
  have hr : 0 < r := by
    by_contra! h
    have := p.overhead_large
    rw [show r = 0 by omega, pow_zero] at hsize
    omega
  have hL : 0 ≤ L := (by positivity : 0 ≤ ((wd x + wd y : ℕ) : ℝ) * p.D).trans ext
  let b := a + n * r
  have hb : b + r ≤ h := by
    rw [hs, add_mul, one_mul] at ha
    unfold b
    omega
  -- 推导：记下中间结论 `budget`：`(P.seats : ℝ) * p.D * T ≤ L * (2 : ℝ) ^ (h - b)`。
  have budget : (P.seats : ℝ) * p.D * T ≤ L * (2 : ℝ) ^ (h - b) := calc
    _ = (p.D : ℝ) * T * P.seats := by ring
    _ ≤ (p.overhead : ℝ) * T * P.seats := by gcongr
    _ ≤ L * (2 : ℝ) ^ r := slack
    _ ≤ _ := by gcongr <;> solve | norm_num | omega
  obtain ⟨Q, c, he, hq⟩ := prepare P (by decide : 0 < 5) hD ht hR hr' (by omega : b < h) ok budget ext
  have cap : H * (Fintype.card Q.V * 2 ^ b) ≤ p.overhead * P.seats := calc
    _ ≤ H * (2 * P.seats) := Nat.mul_le_mul_left _ hq
    _ = 2 * H * P.seats := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hH
  -- 推导：记下中间结论 `hsl`：`(H : ℝ) * T * (Fintype.card Q.V * 2 ^ b : ℕ) ≤ L * (2 : ℝ) ^ r`。
  have hsl : (H : ℝ) * T * (Fintype.card Q.V * 2 ^ b : ℕ) ≤ L * (2 : ℝ) ^ r := by
    have ht' := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr cap) (Nat.cast_nonneg (α := ℝ) T)
    simp only [Nat.cast_mul] at ht' ⊢
    linarith
  obtain ⟨I, _, Q', coeff, hI, he', out⟩ := next x y b a r L Q le_rfl (by omega) hsl
  refine ⟨I, inferInstance, Q', fun i => c * coeff i, hI.trans ?_, ?_, ?_⟩
  · unfold bits
    gcongr; omega
  · intro x y
    simp only [mul_assoc, ← mul_sum, he', he]
  · exact fun i => ⟨(out i).1.relax (by decide) le_rfl hf, (out i).2.trans cap⟩

-- 读法：结论为 `∃ (p : Design δ) (A T₀ : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra F M), ∀ T ≥ T₀, ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra M K), A * (1 + T) ^ A ≤ Fintype.card K → p.Works K T`。
/-- 同一工作扩域可用于任意多个宽度尺度。

英文原文：One working extension can serve arbitrarily many width scales.
-/
theorem design (tag : Radix.WideTag F) (law : LocalLaw F 10) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ (p : Design δ) (A T₀ : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra F M),
      ∀ T ≥ T₀, ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra M K),
        A * (1 + T) ^ A ≤ Fintype.card K → p.Works K T := by
  obtain ⟨D, n, v, b, H, θ, hD, hn, hv, hb, hvb, hθ, A, M, _, _, _, hm⟩ :=
    downstream tag law hδ hδ' localDegree (by have := localDegree_large; omega)
  let p : Design δ :=
    ⟨D, n + 1, v, b, 2 * H + D, min θ 4, localDegree_large.trans hD.le, by omega, hv, hb,
      by have := localDegree_large; omega, lt_min hθ (by norm_num), min_le_right _ _, hvb⟩
  obtain ⟨T₀, hcut⟩ := Filter.eventually_atTop.mp hm
  refine ⟨p, A, T₀ + 1, M, inferInstance, inferInstance, inferInstance, ?_⟩
  intro T hT K _ _ _ large
  obtain ⟨R, hR, hr, ok⟩ := hcut T (by omega)
  exact p.step T R H n θ hD (by omega) hR hr (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    rfl (min_le_left _ _) (ok K inferInstance inferInstance inferInstance large)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 一个阶段的终端族

加权和精确表示整个张量幂。这是将该和的执行记录实现为单个网络之前的展开式。

**英文原文**

Terminal family of a stage

The weighted sum represents the whole tensor power exactly. This is
the expansion before the realization of its transcript as one network.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Filter

variable {δ : ℝ} {p : Design δ} {M n T₀ : ℕ} {a b ξ : ℝ}

-- 读法：`Levels.Terminal` 的结果类型为 `Prop`。
def Levels.Terminal {K : Type} [Field K] {x y : Wire} (v : Levels p M)
    (k : Val x → Val y → K) (m : ℕ) : Prop :=
  Expansion (power k v.batch) (v.selector m)
    (fun Q : Board K _ _ v.remaining =>
      Q.Ready 5 p.D v.finalWidth (v.finalBudget m) p.floor ∧
        Q.seats ≤ p.overhead ^ v.j * v.allocation m)

-- 读法：`v.finalBudget m` 不超过 `32 * (m : ℝ) * (v.stack + 1) * v.batch * (Nat.clog 2 n : ℝ) ^ (-a)`。
theorem Levels.Suits.mass {v : Levels p M} (h : v.Suits n T₀ a b ξ) (m : ℕ) :
    v.finalBudget m ≤ 32 * (m : ℝ) * (v.stack + 1) * v.batch * (Nat.clog 2 n : ℝ) ^ (-a) := by
  obtain ⟨_, hh, _, _, _, _, _, hb, _⟩ := h
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  unfold Levels.finalBudget
  have eq : (v.allocation m : ℝ) * 2 ^ v.stack = 32 * (m : ℝ) * (v.stack + 1) * v.batch := by
    unfold Levels.allocation Levels.batch
    push_cast
    ring
  rw [eq]
  gcongr

-- 读法：`e * D * 2 ^ j` 不超过 `m`。这里调用 `le_div_iff₀`。
private theorem exterior_limit {e D m j : ℕ} {H a : ℝ} (hh : 1 < H)
    (he : (e : ℝ) ≤ m * H ^ (-(2 * a))) (hsize : (D : ℝ) * (2 : ℝ) ^ j ≤ H ^ (2 * a)) :
    e * D * 2 ^ j ≤ m := by
  have bound : (e : ℝ) * D * 2 ^ j ≤ m := by
    rw [mul_assoc]
    refine le_trans (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)) ?_
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv] at he
    exact (le_div_iff₀ (by positivity)).mp he
  exact_mod_cast bound

-- 读法：要证明的命题是 `v.Terminal G.eval m`。这里调用 `p.run`。
theorem Levels.Suits.run {v : Levels p M} (h : v.Suits n T₀ a b ξ)
    {K : Type} [Field K] (works : ∀ T, T₀ ≤ T → T ≤ (Nat.clog 2 n) ^ 4 → p.Works K T)
    {x y : Wire} (G : Diagram K x y) (m : ℕ) (hm : G.cost ≤ m)
    (arity : ∀ i, (G.arity i : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ b)
    (ext : ((wd x + wd y : ℕ) : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a))) :
    v.Terminal G.eval m := by
  obtain ⟨_, hh, _, _, hw, _, hcut, _, hsize, _, hT, _⟩ := h
  apply p.run G v.stack v.j v.remaining v.group m hm _ _
    (exterior_limit hh ext hsize) v.room
  · intro i
    exact_mod_cast (arity i).trans hw
  · intro i hi
    apply works
    · exact hcut.trans (Nat.le_mul_of_pos_left _ (by positivity))
    · refine le_trans ?_ hT
      unfold Design.width Levels.finalWidth
      rw [mul_comm, ← pow_add]
      gcongr

-- 读法：`terminal` 的证明用到 `p.levels`、`net.diagram`、`hv.run`。
/-- 第 4、5 节直到末端展开为止的结论。工作域的大小与复制上界对所有输入一致。

英文原文：Sections 4 and 5 up to the terminal expansion. The size of the
working field and the replication bound are uniform in the input.
-/
theorem terminal {F : Type} [Field F] (tag : Radix.WideTag F) (law : LocalLaw F 10)
    (hδ : 0 < δ) (hd : δ ≤ 1) :
    ∃ (p : Design δ) (A T₀ : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra F L),
      ∀ (M : ℕ) (a b ξ : ℝ), 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → 0 < ξ →
      ∀ᶠ n : ℕ in atTop, ∃ v : Levels p M, v.Suits n T₀ a b ξ ∧
        ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
          A * (1 + (Nat.clog 2 n) ^ 4) ^ A ≤ Fintype.card K →
          ∀ (x y : Wire) (k : Val x → Val y → K) (m s u : ℕ) (labels : Set (Table K)),
            Wide K u labels x y k s → s ≤ m → (u : ℝ) ≤ (Nat.clog 2 n : ℝ) ^ b →
            ((wd x + wd y : ℕ) : ℝ) ≤ m * (Nat.clog 2 n : ℝ) ^ (-(2 * a)) → v.Terminal k m := by
  -- 推导：从 `design tag law hδ hd` 中取出 `p, A, T₀, L, _, _, _, ok`。
  obtain ⟨p, A, T₀, L, _, _, _, ok⟩ := design tag law hδ hd
  refine ⟨p, A, T₀, L, inferInstance, inferInstance, inferInstance, ?_⟩
  intro M a b ξ ha ha' hb hb' hx
  filter_upwards [p.levels hd T₀ M ha ha' hb hb' hx] with n hn
  obtain ⟨v, hv⟩ := hn
  refine ⟨v, hv, ?_⟩
  intro K _ _ _ size x y k m s u labels net hm hu he
  obtain ⟨G, rfl, hs, hc⟩ := net.diagram
  refine hv.run ?_ G m (hc.le.trans hm) (fun i => (Nat.cast_le.mpr (hs i).1).trans hu) he
  intro T ht hmax
  apply ok T ht K inferInstance inferInstance inferInstance
  refine le_trans ?_ size
  gcongr

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 终端规模估计

用任意正余量吸收高度的对数的各个固定次幂。槽位数估计中的指数与末端预留的块数无关。

**英文原文**

Terminal size estimates

Absorb powers of the logarithm of the height using arbitrary positive
slack. The exponent in the seat estimate does not depend on how many
blocks are reserved at the end.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter

variable {δ : ℝ} {p : Design δ} {M n T₀ : ℕ} {a b ξ : ℝ}

-- 读法：`C₀` 的取值由 `2 / Real.log 2 + 3` 给出。
private def C₀ := 2 / Real.log 2 + 3

-- 读法：`0` 严格小于 `C₀`。
private theorem c_pos : 0 < C₀ := by unfold C₀; positivity

-- 读法：`(t : ℝ) + 2` 不超过 `C₀ * Real.log h`。
private theorem log_bound {t : ℕ} {h : ℝ} (hh : 1 ≤ Real.log h)
    (ht : (2 : ℝ) ^ t ≤ h ^ 2) : (t : ℝ) + 2 ≤ C₀ * Real.log h := by
  have hb := Real.log_le_log (by positivity) ht
  rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hb
  have := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hb
  unfold C₀
  rw [add_mul, div_mul_eq_mul_div]
  linarith

-- 读法：结论为 `let c := C₀ * Real.log (Nat.clog 2 n) (v.stack : ℝ) + 2 ≤ c ∧ (v.j : ℝ) ≤ c`。这里调用 `log_bound`。
private theorem indices {v : Levels p M} (hv : v.Suits n T₀ a b ξ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hh : 2 ≤ (Nat.clog 2 n : ℝ)) (hl : 1 ≤ Real.log (Nat.clog 2 n)) :
    let c := C₀ * Real.log (Nat.clog 2 n)
    (v.stack : ℝ) + 2 ≤ c ∧ (v.j : ℝ) ≤ c := by
  let h : ℝ := Nat.clog 2 n
  have hh' : 1 ≤ h := by linarith
  obtain ⟨_, _, _, _, _, ht, _, _, hj, _⟩ := hv
  constructor
  · apply log_bound hl
    calc
      _ ≤ _ := ht
      _ ≤ h * h := mul_le_mul hh (by simpa using Real.rpow_le_rpow_of_exponent_le hh' hb)
        (by positivity) (by positivity)
      _ = _ := (pow_two h).symm
  -- 推导：记下中间结论 `he`：`(2 : ℝ) ^ v.j ≤ h ^ 2`。
  · have he : (2 : ℝ) ^ v.j ≤ h ^ 2 := calc
      _ ≤ (2 : ℝ) ^ (p.gain * v.j) := pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left _ p.gain_pos)
      _ ≤ (p.D : ℝ) * (2 : ℝ) ^ (p.gain * v.j) := le_mul_of_one_le_left (by positivity)
        (by exact_mod_cast (show 1 ≤ p.D by have := p.large; omega))
      _ ≤ h ^ (2 * a) := hj
      _ ≤ h ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh' (by linarith)
      _ = _ := Real.rpow_two h
    exact (le_add_of_nonneg_right (by norm_num)).trans (log_bound hl he)

-- 读法：`Levels.Costs` 的结果类型为 `Prop`。
def Levels.Costs (v : Levels p M) (n m : ℕ) (a b τ : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  let S := (2 : ℝ) ^ v.blocks
  (v.selector m : ℝ) ≤ m * S * h ^ τ ∧
  ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) ≤ m * S * h ^ (p.groupRate * a + τ) ∧
  v.finalBudget m ≤ m * v.batch * h ^ (-a + τ) ∧
  (p.D : ℝ) * v.finalWidth ≤ h ^ (b + (1 + δ / 3) * a + τ)

-- 读法：对每个 `ᶠ n : ℕ in atTop`，对每个 `(v : Levels p M)`，由 `v.Suits n T₀ a b ξ` 推出 `∀ m, v.Costs n m a b τ`。
theorem Design.costs (p : Design δ) {τ : ℝ} (hτ : 0 < τ) (ha : a ≤ 1) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M), v.Suits n T₀ a b ξ →
      ∀ m, v.Costs n m a b τ := by
  let A : ℝ := 32 * p.overhead * (1 + p.growth) * C₀ ^ 3
  let B : ℝ := 32 * (2 : ℝ) ^ (2 * p.groupRate) * C₀
  have ht := Shaving.tendsto_height
  filter_upwards [ht.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    ht.eventually (Shaving.polylog_le A 3 hτ),
    ht.eventually (Shaving.polylog_le B 1 hτ),
    ht.eventually (Shaving.polylog_le (32 * C₀) 1 hτ),
    ((tendsto_rpow_atTop hτ).comp ht).eventually_ge_atTop ((p.D : ℝ) * (2 : ℝ) ^ (p.growth + 1))]
    with n hh hl hA hB hC hD v hv m
  let h : ℝ := Nat.clog 2 n
  -- 推导：记下中间结论 `hpos`：`0 < h`。
  have hpos : 0 < h := by linarith
  let S := (2 : ℝ) ^ v.blocks
  let c := C₀ * Real.log h
  have hc : 0 ≤ c := mul_nonneg c_pos.le (zero_le_one.trans hl)
  obtain ⟨hs, hj⟩ := indices hv ha hb hh hl
  have hs' : (v.stack : ℝ) + 1 ≤ c := by linarith
  have hi : 2 + (v.stack : ℝ) + p.growth * v.j ≤ (1 + p.growth) * c := by
    linarith only [hs, mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg (α := ℝ) p.growth)]
  have mass := hv.mass m
  obtain ⟨_, _, _, _, _, _, _, _, _, hw, _, hr, _⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ c * (p.overhead * ((1 + p.growth) * c) * (32 * m * c * S)) := by
        unfold Levels.selector Levels.allocation
        push_cast
        gcongr
      _ = m * S * (A * (Real.log h) ^ 3) := by unfold A c; ring
      _ ≤ m * S * h ^ τ := mul_le_mul_of_nonneg_left hA (by unfold S; positivity)
  -- 推导：记下中间结论 `hp`：`p.overhead ^ v.j ≤ 2 ^ v.group`。
  · have hp : p.overhead ^ v.j ≤ 2 ^ v.group := calc
      _ ≤ p.overhead ^ (v.j + 1) := Nat.pow_le_pow_right (by have := p.overhead_large; omega) (by omega)
      _ ≤ _ := (Nat.le_mul_of_pos_right _ (by positivity)).trans v.room
    have hp' : (p.overhead : ℝ) ^ v.j ≤ (2 : ℝ) ^ (2 * p.groupRate) * h ^ (p.groupRate * a) :=
      le_trans (by exact_mod_cast hp) hr
    calc
      _ ≤ ((2 : ℝ) ^ (2 * p.groupRate) * h ^ (p.groupRate * a)) * (32 * m * c * S) := by
        unfold Levels.allocation
        push_cast
        gcongr
      _ = m * S * h ^ (p.groupRate * a) * (B * (Real.log h) ^ 1) := by unfold B c; ring
      _ ≤ m * S * h ^ (p.groupRate * a) * h ^ τ := mul_le_mul_of_nonneg_left hB (by unfold S; positivity)
      _ = _ := by rw [Real.rpow_add hpos, mul_assoc]
  · calc
      _ ≤ _ := mass
      _ ≤ 32 * (m : ℝ) * c * v.batch * h ^ (-a) := by gcongr
      _ = (m : ℝ) * v.batch * h ^ (-a) * (32 * C₀ * (Real.log h) ^ 1) := by unfold c; ring
      _ ≤ (m : ℝ) * v.batch * h ^ (-a) * h ^ τ := mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by rw [Real.rpow_add hpos, mul_assoc]
  · calc
      _ ≤ (p.D : ℝ) * ((2 : ℝ) ^ (p.growth + 1) * h ^ (b + (1 + δ / 3) * a)) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ h ^ τ * h ^ (b + (1 + δ / 3) * a) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by rw [mul_comm, ← Real.rpow_add hpos]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end
