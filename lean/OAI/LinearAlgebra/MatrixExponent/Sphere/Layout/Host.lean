-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Load
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing

/-!
# 将比特编码的已降度网络放置到分块宿主图上

**英文原文**

Placing a bit-encoded, degree-reduced network on a block host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Finset Classical Packing

variable {F V : Type} [Field F] [Fintype V] {a b : Wire} {d h u : ℕ}
  {G : Bundled F a b} {T : Trie V d} (H : Fanout G T (Cell h))

-- 读法：`fixed` 的取值由 `T.frozen (H.site v).1` 给出。
def fixed (v : G.V) := T.frozen (H.site v).1

-- 读法：`exterior` 的取值由 `(∀ i, H.fixed (G.left i)) ∧ (∀ i, H.fixed (G.right i))` 给出。
def exterior := (∀ i, H.fixed (G.left i)) ∧ (∀ i, H.fixed (G.right i))

-- 读法：用字段 `frozen`、`exterior`、`separate` 构造 `Freeze H.route.net.diagram`。
abbrev freeze (he : H.exterior) : Freeze H.route.net.diagram where
  frozen j := T.fixed (H.place j).1
  exterior := by
    rintro (q|q)
    · exact he.1 q
    · exact he.2 q
  separate i := T.separate (H.edges i.1).2

-- 读法：用字段 `place`、`frozen`、`keep`、`N` 构造 `(H.freeze he).Frame (Node V d) h`。
abbrev frame (he : H.exterior) : (H.freeze he).Frame (Node V d) h where
  place := H.place
  frozen := T.fixed
  keep _ := Iff.rfl
  N := T.adj
  C := T.core
  ns _ _ := T.adj_symm
  cs _ _ := T.core_symm
  sub _ := filter_subset _ _
  group i := (H.edges i.1).1
  edge i := mem_filter.mpr ⟨(H.edges i.val.1).2, i.property⟩
  full i := (H.edges i.1).2

-- 读法：用字段 `V`、`diagram`、`freeze`、`frame` 构造 `Rounds.LocalTerm F a b h u`。
/-- 即使中继位置未被使用，也要支付一次基本费用。

英文原文：The floor charge is paid once even for unused relay positions.
-/
abbrev term (he : H.exterior) (hw : ∀ e, u ∣ G.width e) : Rounds.LocalTerm F a b h u where
  V := Node V d
  diagram := H.route.net.diagram
  freeze := H.freeze he
  frame := H.frame he
  one := H.injective
  width v w := H.route.net.divisible v w u (fun e _ _ => hw e.1)
  charge v := H.route.net.arity v + (u : ℝ)
  cover v := by rw [Bundled.arity_diagram]; exact le_add_of_nonneg_right (by positivity)
  floor v := le_add_of_nonneg_left (by positivity)

variable (he : H.exterior) (hw : ∀ e, u ∣ G.width e)

-- 读法：`(H.term he hw).diagram.eval` 等于 `G.eval`。
theorem eval_term : (H.term he hw).diagram.eval = G.eval := by
  rw [Bundled.eval_diagram, Routes.eval_net]

-- 读法：在后续公式中，`Frozen` 是 `{v // H.fixed v}` 的缩写。
abbrev Frozen := {v // H.fixed v}
-- 读法：在后续公式中，`Mobile` 是 `{v // ¬ H.fixed v}` 的缩写。
abbrev Mobile := {v // ¬ H.fixed v}

-- 读法：用字段 `toFun`、`left_inv`、`right_inv` 构造 `H.Frozen ≃ (H.freeze he).Fixed`。
def fixedEquiv : H.Frozen ≃ (H.freeze he).Fixed where
  toFun v := ⟨.inl v.val, v.property⟩
  invFun
    | ⟨.inl v, hv⟩ => ⟨v, hv⟩
    | ⟨.inr _, hv⟩ => False.elim hv
  left_inv _ := rfl
  right_inv := by rintro ⟨v|v, hv⟩; rfl; exact False.elim hv

-- 读法：用字段 `left_inv`、`right_inv` 构造 `H.Mobile ⊕ Relay G.V d ≃ (H.freeze he).Core`。
def coreEquiv : H.Mobile ⊕ Relay G.V d ≃ (H.freeze he).Core where
  toFun
    | .inl v => ⟨.inl v.val, v.property⟩
    | .inr v => ⟨.inr v, fun h => h⟩
  invFun
    | ⟨.inl v, hv⟩ => .inl ⟨v, hv⟩
    | ⟨.inr v, _⟩ => .inr v
  left_inv := by rintro (v | v) <;> rfl
  right_inv := by rintro ⟨v | v, _⟩ <;> rfl

-- 读法：`(H.term he hw).charge (.inl v)` 等于 `G.arity v + (u : ℝ)`。
theorem old_charge (v : G.V) : (H.term he hw).charge (.inl v) = G.arity v + (u : ℝ) := by
  change (H.route.net.arity (.inl v) : ℝ) + u = _
  rw [Routes.old_arity]

-- 读法：`(H.term he hw).charge v.val` 不超过 `2 * B + u`。按 `H.fixed v.1` 成立与否分情况。
theorem core_max {B : ℝ} (hB : 0 ≤ B) (hcore : ∀ v : H.Mobile, G.arity v.val ≤ B)
    (hties : ∀ v w : H.Frozen, G.ties v.val w.val ≤ B) (v : (H.freeze he).Core) :
    (H.term he hw).charge v.val ≤ 2 * B + u := by
  obtain ⟨v|v, hv⟩ := v
  · rw [old_charge]
    have := hcore ⟨v, hv⟩
    change (G.arity v : ℝ) ≤ B at this
    linarith
  · have hh : (H.route.net.arity (.inr v) : ℝ) ≤ 2 * B := by
      by_cases h : H.fixed v.1
      -- 推导：从 `H.frozen_relay v h` 中取出 `w, hw`。
      · obtain ⟨w, hw⟩ := H.frozen_relay v h
        have hb : (G.ties v.1 w : ℝ) ≤ B := by
          by_cases ht : H.fixed w
          · exact hties ⟨v.1, h⟩ ⟨w, ht⟩
          · exact (Nat.cast_le.mpr (G.ties_le _ w)).trans (hcore ⟨w, ht⟩)
        exact (show (H.route.net.arity (.inr v) : ℝ) ≤ 2 * (G.ties v.1 w : ℝ) by exact_mod_cast hw).trans
          (by gcongr)
      · exact (show (H.route.net.arity (.inr v) : ℝ) ≤ 2 * (G.arity v.1 : ℝ) by
          exact_mod_cast H.relay_le v).trans (mul_le_mul_of_nonneg_left (hcore ⟨v.1, h⟩) (by norm_num))
    exact add_le_add_left hh _

-- 读法：结论为 `(∑ v : (H.freeze he).Core, (H.term he hw).charge v.val) = (∑ v : H.Mobile, ((G.arity v.val : ℝ) + u)) + 4 * (d + 1) * (∑ e, (G.width e : ℝ)) + Fintype.card (Relay G.V d) * (u : ℝ)`。
theorem core_sum :
    (∑ v : (H.freeze he).Core, (H.term he hw).charge v.val) =
      (∑ v : H.Mobile, ((G.arity v.val : ℝ) + u)) +
        4 * (d + 1) * (∑ e, (G.width e : ℝ)) + Fintype.card (Relay G.V d) * (u : ℝ) := by
  rw [← (H.coreEquiv he).sum_comp, Fintype.sum_sum_type]
  change (∑ v : H.Mobile, (H.term he hw).charge (.inl v.val)) +
    (∑ v : Relay G.V d, ((H.route.net.arity (.inr v) : ℝ) + u)) = _
  have ht : (∑ v, (H.route.net.arity (.inr v) : ℝ)) = 4 * (d + 1) * (∑ e, (G.width e : ℝ)) := by
    exact_mod_cast H.total
  simp only [Routes.old_arity, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ht, add_assoc]

-- 读法：`(∑ v : (H.freeze he).Fixed, f ((H.term he hw).charge v.val))` 等于 `∑ v : H.Frozen, f (G.arity v.val + (u : ℝ))`。这里调用 `sum_congr`。
theorem frozen_sum (f : ℝ → ℝ) :
    (∑ v : (H.freeze he).Fixed, f ((H.term he hw).charge v.val)) =
      ∑ v : H.Frozen, f (G.arity v.val + (u : ℝ)) := by
  rw [← (H.fixedEquiv he).sum_comp]
  exact sum_congr rfl (fun v _ => congrArg f (old_charge H he hw v.val))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-!
# 路由前的填充

对每条线束只取整一次。随后作路由仍保持整除性，即使多条线束共用同一条树边也如此。取整开销可由关联线束的条数加以约束。

**英文原文**

Padding before routing

Round each bundle once. Routing afterwards preserves divisibility,
including when several bundles share a tree edge. The rounding cost is
bounded in terms of the number of incident bundles.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset

variable {F V I : Type} {a b : Wire}

namespace Bundled
variable (G : Bundled F a b) (u : ℕ)

-- 读法：用字段 `toFun`、`inj'` 构造 `G.state e ↪ (Fin (Diagram.padWidth u (G.width e)) → Bool)`。
private def paddedCode (e : G.E) : G.state e ↪ (Fin (Diagram.padWidth u (G.width e)) → Bool) where
  toFun s i := if h : i.val < G.width e then G.code e s ⟨i.val, h⟩ else false
  inj' x y h := by
    apply (G.code e).injective
    funext i
    simpa using congrFun h (Fin.castLE (Diagram.le_padWidth u (G.width e)) i)

-- 读法：在后续公式中，`pad` 是 `{ G with width := fun e => Diagram.padWidth u (G.width e), code := G.paddedCode u }` 的缩写。
abbrev pad : Bundled F a b :=
  { G with width := fun e => Diagram.padWidth u (G.width e), code := G.paddedCode u }

-- 读法：`(G.pad u).eval` 等于 `G.eval`。两端由定义化简为同一项。
theorem eval_pad [Field F] : (G.pad u).eval = G.eval := rfl

-- 读法：`u` 整除 `(G.pad u).width e`。使用 `Diagram.dvd_padWidth` 给出的结论。
theorem divisible_pad (hu : 0 < u) (e : G.E) : u ∣ (G.pad u).width e :=
  Diagram.dvd_padWidth hu _

-- 读法：`degree` 的取值由 `(∑ e, if G.src e = v then 1 else 0) + (∑ e, if G.dst e = v then 1 else 0)` 给出。
def degree (v : G.V) :=
  (∑ e, if G.src e = v then 1 else 0) + (∑ e, if G.dst e = v then 1 else 0)

-- 读法：`(∑ e, if p e then Diagram.padWidth u (G.width e) else 0)` 不超过 `(∑ e, if p e then G.width e else 0) + u * ∑ e, if q e then 1 else 0`。这里调用 `sum_le_sum`。
private theorem round_le (p q : G.E → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ e, p e → q e) :
    (∑ e, if p e then Diagram.padWidth u (G.width e) else 0) ≤
      (∑ e, if p e then G.width e else 0) + u * ∑ e, if q e then 1 else 0 := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases he : p e
  · simpa [he, h e he] using Diagram.padWidth_le u (G.width e)
  · simp [he]

-- 读法：`(G.pad u).arity v` 不超过 `G.arity v + u * G.degree v`。
theorem arity_pad (v : G.V) : (G.pad u).arity v ≤ G.arity v + u * G.degree v := by
  have hs := G.round_le u (fun e => G.src e = v) _ (fun _ h => h)
  have ht := G.round_le u (fun e => G.dst e = v) _ (fun _ h => h)
  simp only [arity, pad, degree, mul_add]
  omega

-- 读法：`(G.pad u).ties v w` 不超过 `G.ties v w + u * G.degree v`。
theorem ties_pad (v w : G.V) : (G.pad u).ties v w ≤ G.ties v w + u * G.degree v := by
  have hs := G.round_le u (fun e => G.src e = v ∧ G.dst e = w) (fun e => G.src e = v)
    (fun _ h => h.1)
  have ht := G.round_le u (fun e => G.dst e = v ∧ G.src e = w) (fun e => G.dst e = v)
    (fun _ h => h.1)
  simp only [ties, pad, degree, mul_add]
  omega

-- 读法：结论为 `∑ e, (G.pad u).width e ≤ (∑ e, G.width e) + Fintype.card G.E * u`。这里调用 `sum_le_sum`。
theorem total_pad : ∑ e, (G.pad u).width e ≤ (∑ e, G.width e) + Fintype.card G.E * u := by
  simpa [sum_add_distrib] using sum_le_sum (fun e (_ : e ∈ univ) => Diagram.padWidth_le u (G.width e))

end Bundled

namespace Fanout
variable {G : Bundled F a b} {d : ℕ} {T : Trie V d}

-- 读法：在后续公式中，`pad` 是 `⟨H.site, H.one, H.near, H.group⟩` 的缩写。
abbrev pad (H : Fanout G T I) (u : ℕ) : Fanout (G.pad u) T I :=
  ⟨H.site, H.one, H.near, H.group⟩

variable [Field F] [Fintype V] {h u : ℕ} (H : Fanout G T (Packing.Cell h))

-- 读法：在后续公式中，`finish` 是 `(H.pad u).term he (G.divisible_pad u hu)` 的缩写。
abbrev finish (he : H.exterior) (hu : 0 < u) : Rounds.LocalTerm F a b h u :=
  (H.pad u).term he (G.divisible_pad u hu)

-- 读法：`(H.finish he hu).diagram.eval` 等于 `G.eval`。
theorem eval_finish (he : H.exterior) (hu : 0 < u) : (H.finish he hu).diagram.eval = G.eval :=
  ((H.pad u).eval_term he _).trans (G.eval_pad u)

end Fanout
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
路由前的估计，以及最后统一采用的尺度幂次。

**英文原文**

Pre-routing estimates and the final common power of the scale.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Classical Finset Rounds Packing

variable {F V : Type} [Field F] [Fintype V] {a b : Wire} {c d h D T R g : ℕ} {W : ℝ}
  {G : Bundled F a b} {S : Trie V (c * d)} (H : Fanout G S (Cell h))

-- 读法：`exponent` 的取值由 `64 * (c + ℓ + 1) ^ 2` 给出。
def exponent (c ℓ : ℕ) := 64 * (c + ℓ + 1) ^ 2

-- 读法：结构的字段包括 `cells`、`size`、`degree`、`frozenCount`、`frozenMax`。
/-- 列出路由与取整之前的全部费用。除各核心元数外，只有冻结站点间的直接邻接还需额外的界。

英文原文：All charges before routing and rounding. Only direct contacts between
frozen stations need a bound beyond the individual core arities.
-/
structure Caps (P : Input F a b h D T R g W) (ℓ : ℕ) : Prop where
  cells : Fintype.card V ≤ D ^ c * Fintype.card P.V
  size : ((Fintype.card G.V : ℝ) + Fintype.card G.E) * T ≤ (D : ℝ) ^ c * W
  degree : ∀ v, G.degree v ≤ D ^ c
  frozenCount : (Fintype.card H.Frozen : ℝ) * D * T ≤ c * W
  frozenMax : ∀ v : H.Frozen, (G.arity v.val : ℝ) ≤ c * (D : ℝ) * T
  frozenSquare : (∑ v : H.Frozen, (G.arity v.val : ℝ) ^ 2) ≤ c * W * T
  coreMax : ∀ v : H.Mobile, (G.arity v.val : ℝ) ≤ T / (D : ℝ) ^ (ℓ + 2)
  ties : ∀ v w : H.Frozen, (G.ties v.val w.val : ℝ) ≤ T / (D : ℝ) ^ (ℓ + 2)
  coreSum : (∑ v : H.Mobile, (G.arity v.val : ℝ)) ≤ c * W * (1 + (d : ℝ))
  edges : (∑ e, (G.width e : ℝ)) ≤ c * W * (1 + (d : ℝ))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-!
# 统计关联次数及线束宽度

**英文原文**

Counting incidences and bundle widths
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Bundled
open Classical Finset

variable {F V E : Type} {a b : Wire}

-- 读法：`(∑ v, ∑ e, if f e = v then w e else 0)` 等于 `∑ e, w e`。
private theorem push_total [Fintype V] [Fintype E] (f : E → V) (w : E → ℕ) :
    (∑ v, ∑ e, if f e = v then w e else 0) = ∑ e, w e := by
  rw [sum_comm]
  simp

variable (G : Bundled F a b)

-- 读法：结论为 `∑ v, G.degree v = 2 * Fintype.card G.E`。
theorem degree_total : ∑ v, G.degree v = 2 * Fintype.card G.E := by
  unfold degree
  rw [sum_add_distrib, push_total, push_total]
  simp [two_mul]

-- 读法：结论为 `∑ v, G.arity v = wd a + wd b + 2 * ∑ e, G.width e`。
theorem arity_total : ∑ v, G.arity v = wd a + wd b + 2 * ∑ e, G.width e := by
  unfold arity
  simp only [Fintype.card_subtype, card_filter, sum_add_distrib, push_total, sum_const, card_univ,
    card_slots, smul_eq_mul, mul_one]
  ring

-- 读法：结论为 `∑ e, G.width e ≤ ∑ v, G.arity (f v)`。这里调用 `sum_le_sum`。
/-- 只统计源枢纽的元数就能覆盖所有连线。

英文原文：Counting the arities just at source hubs covers all wires.
-/
theorem width_le_source [Fintype V] (f : V → G.V) (h : ∀ e, G.src e ∈ Set.range f) :
    ∑ e, G.width e ≤ ∑ v, G.arity (f v) := by
  choose j hj using h
  rw [← push_total j G.width]
  apply sum_le_sum
  intro v _
  calc
    _ ≤ ∑ e, if G.src e = f v then G.width e else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : j e = v
      · rw [← hj e, he, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right he]; exact Nat.zero_le _
    _ ≤ G.arity (f v) := by unfold arity; omega

-- 读法：`Fintype.card G.E` 不超过 `∑ v, G.degree (f v)`。这里调用 `sum_le_sum`。
theorem count_le_source [Fintype V] (f : V → G.V) (h : ∀ e, G.src e ∈ Set.range f) :
    Fintype.card G.E ≤ ∑ v, G.degree (f v) := by
  choose j hj using h
  rw [show Fintype.card G.E = ∑ _ : G.E, 1 by simp, ← push_total j (fun _ => 1)]
  apply sum_le_sum
  intro v _
  calc
    _ ≤ ∑ e, if G.src e = f v then 1 else 0 := by
      apply sum_le_sum
      intro e _
      by_cases he : j e = v
      · rw [← hj e, he, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right he]; exact Nat.zero_le _
    _ ≤ G.degree (f v) := Nat.le_add_right _ _

-- 读法：结论为 `∑ v : {v // p v}, G.arity v.val ≤ 2 * ∑ e, G.width e`。
theorem sum_mobile (p : G.V → Prop) [DecidablePred p] (hl : ∀ i, ¬ p (G.left i))
    (hr : ∀ i, ¬ p (G.right i)) : ∑ v : {v // p v}, G.arity v.val ≤ 2 * ∑ e, G.width e := by
  let cost (v : G.V) := (∑ e, if G.src e = v then G.width e else 0) +
    (∑ e, if G.dst e = v then G.width e else 0)
  have he (v : {v // p v}) : G.arity v.val = cost v.val := by
    have h₁ (i) : G.left i ≠ v.val := fun h => hl i (h.symm ▸ v.property)
    have h₂ (i) : G.right i ≠ v.val := fun h => hr i (h.symm ▸ v.property)
    simp [arity, cost, h₁, h₂]
  simp_rw [he]
  calc
    _ = ∑ v ∈ univ.filter p, cost v := (sum_subtype _ (by simp) cost).symm
    _ ≤ ∑ v, cost v := sum_le_sum_of_subset (subset_univ _)
    _ = _ := by rw [show (∑ v, cost v) = _ from sum_add_distrib, push_total, push_total, two_mul]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Bundled
end

/-!
# 拆为分块后的站点腿与接缝负载

**英文原文**

Loads of station legs and seams after splitting into chunks
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical Packing Real

-- 读法：`proxy` 的取值由 `4 * sqrt ((M : ℝ) * r * e) + M` 给出。
def proxy (M r e : ℕ) := 4 * sqrt ((M : ℝ) * r * e) + M

-- 读法：`0` 不超过 `proxy M r e`。
theorem proxy_nonneg (M r e : ℕ) : 0 ≤ proxy M r e := by unfold proxy; positivity

-- 读法：`Chunk.width r (s.val j).val * sqrt M` 不超过 `proxy M r e`。
theorem chunk_le {M e : ℕ} (r : ℕ) (s : Chunk.Shape M e) (j : Fin M) :
    Chunk.width r (s.val j).val * sqrt M ≤ proxy M r e := by
  have h : (s.val j).val ≤ e := Nat.le_of_lt_succ (s.val j).isLt
  have hM : 1 ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by have := j.isLt; omega)
  have hm : sqrt (M : ℝ) ≤ M := sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  calc
    _ ≤ (4 * sqrt ((r : ℝ) * e) + 1) * sqrt M := by
      gcongr
      refine (Chunk.width_le _ _).trans ?_
      gcongr
    _ ≤ _ := by
      unfold proxy
      rw [mul_assoc (M : ℝ), sqrt_mul (by positivity : (0 : ℝ) ≤ M)]
      linarith

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  (C : V → Surface.Cell F (M * r) (M * t) T E X) (d : E → ℕ) {a b : Wire}

-- 读法：`seamWidth` 的取值由 `proxy M r (d e)` 给出。
def seamWidth (_ : V → Surface.Cell F (M * r) (M * t) T E X) (d : E → ℕ) (e : E) :=
  proxy M r (d e)

-- 读法：`legWidth` 的取值由 `proxy M r (item C i).a + proxy M t (item C i).b` 给出。
def legWidth (i : Place C) := proxy M r (item C i).a + proxy M t (item C i).b

omit [Field F] [Fintype E] [Fintype V] in
-- 读法：`0` 不超过 `legWidth C i`。使用 `add_nonneg` 给出的结论。
theorem legWidth_nonneg (i : Place C) : 0 ≤ legWidth C i :=
  add_nonneg (proxy_nonneg ..) (proxy_nonneg ..)

namespace Backdrop

variable {C d} (B : Backdrop C a b) (p : Profile C d) (P : ℕ)

-- 读法：在后续公式中，`emitted` 是 `(B.emit p P p.widths).net` 的缩写。
abbrev emitted := (B.emit p P p.widths).net

-- 读法：`chamberLoad` 的取值由 `push B.src (seamWidth C d) v + push B.dst (seamWidth C d) v + push Sigma.fst (legWidth C) v` 给出。
def chamberLoad (d : E → ℕ) (v : V) :=
  push B.src (seamWidth C d) v + push B.dst (seamWidth C d) v +
    push Sigma.fst (legWidth C) v

-- 读法：结论为 `(B.emitted p P).arity (.inr (.inl (v, j))) = (∑ e, if B.src e = v then p.widths.seam (e, j) else 0) + (∑ e, if B.dst e = v then p.widths.seam (e, j) else 0) + ∑ i, if i.1 = v then p.widths.leg (.inl (i, j)) else 0`。
theorem chamberA (v : V) (j : Fin M) :
    (B.emitted p P).arity (.inr (.inl (v, j))) =
      (∑ e, if B.src e = v then p.widths.seam (e, j) else 0) +
      (∑ e, if B.dst e = v then p.widths.seam (e, j) else 0) +
      ∑ i, if i.1 = v then p.widths.leg (.inl (i, j)) else 0 := by
  rw [Attach.right_arity]
  simp [Bundled.arity, chambers, seamEnd, socket, Grid.map, Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and]

-- 读法：`(B.emitted p P).arity (.inr (.inr (v, j)))` 等于 `∑ i, if i.1 = v then p.widths.leg (.inr (i, j)) else 0`。
theorem chamberB (v : V) (j : Fin M) :
    (B.emitted p P).arity (.inr (.inr (v, j))) =
      ∑ i, if i.1 = v then p.widths.leg (.inr (i, j)) else 0 := by
  rw [Attach.right_arity]
  simp [Bundled.arity, chambers, seamEnd, socket, Grid.map, Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and]

-- 读法：这里调用 `sum_congr`。
theorem station (v : B.base.V) :
    (B.emitted p P).arity (.inl v) = B.base.arity v +
      ∑ i, if B.owner i = v then
        (∑ j, p.widths.leg (.inl (i, j))) + (∑ j, p.widths.leg (.inr (i, j))) else 0 := by
  rw [Attach.left_arity]
  simp only [arm, Grid.point, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
  rw [← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases h : B.owner i = v <;> simp [h]

-- 读法：`(∑ i, if loc i = v then w i else 0 : ℕ) * x` 不超过 `push loc cost v`。这里调用 `sum_le_sum`。
private theorem push_est {Y Z : Type} [Fintype Y] (loc : Y → Z) (v : Z) (w : Y → ℕ)
    (cost : Y → ℝ) (x : ℝ) (hw : ∀ i, w i * x ≤ cost i) :
    (∑ i, if loc i = v then w i else 0 : ℕ) * x ≤ push loc cost v := by
  rw [Nat.cast_sum, sum_mul]
  apply sum_le_sum
  intro i _
  by_cases h : loc i = v <;> simp [h, hw i]

-- 读法：`((B.emitted p P).arity (.inl v) : ℝ)` 不超过 `B.base.arity v + push B.owner (legWidth C) v`。这里调用 `push_est`。
theorem station_le (v : B.base.V) : ((B.emitted p P).arity (.inl v) : ℝ) ≤
    B.base.arity v + push B.owner (legWidth C) v := by
  rw [station, Nat.cast_add]
  gcongr
  rw [← mul_one (↑(∑ i, if B.owner i = v then
    (∑ j, p.widths.leg (.inl (i, j))) + (∑ j, p.widths.leg (.inr (i, j))) else 0) : ℝ)]
  apply push_est
  intro i
  rw [mul_one, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  exact add_le_add (Chunk.total_width r (p.1 (.inr i))) (Chunk.total_width t (p.2 i))

-- 读法：`(B.emitted p P).arity (.inr s) * sqrt M` 不超过 `B.chamberLoad d (Grid.point s)`。这里调用 `push_est`。
theorem chamber_le (s : Grid M V) :
    (B.emitted p P).arity (.inr s) * sqrt M ≤ B.chamberLoad d (Grid.point s) := by
  have h (v : V) (j : Fin M) (f : E → V) :=
    push_est f v (fun e => p.widths.seam (e, j)) (seamWidth C d) (sqrt M)
      (fun e => chunk_le r (p.1 (.inl e)) j)
  rcases s with ⟨v, j⟩ | ⟨v, j⟩
  · rw [chamberA, Nat.cast_add, Nat.cast_add, add_mul, add_mul]
    refine add_le_add (add_le_add (h v j B.src) (h v j B.dst)) ?_
    apply push_est
    intro i
    exact (chunk_le r (p.1 (.inr i)) j).trans (le_add_of_nonneg_right (proxy_nonneg ..))
  · rw [chamberB]
    have hn (f : E → V) := push_nonneg f (seamWidth C d) (fun _ => proxy_nonneg ..) v
    refine le_trans ?_ (le_add_of_nonneg_left (add_nonneg (hn B.src) (hn B.dst)))
    apply push_est
    intro i
    exact (chunk_le t (p.2 i) j).trans (le_add_of_nonneg_left (proxy_nonneg ..))

-- 读法：`(∑ e, ((B.emitted p P).width e : ℝ))` 不超过 `(∑ e, (B.base.width e : ℝ)) + (∑ e, seamWidth C d e) + ∑ i, legWidth C i`。
theorem emitted_width :
    (∑ e, ((B.emitted p P).width e : ℝ)) ≤
      (∑ e, (B.base.width e : ℝ)) + (∑ e, seamWidth C d e) + ∑ i, legWidth C i := by
  simp only [emitted, Attach.net, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_prod_type]
  rw [← sum_add_distrib, ← add_assoc]
  refine add_le_add (add_le_add le_rfl (sum_le_sum ?_)) (sum_le_sum ?_)
  · exact fun e _ => Chunk.total_width r (p.1 (.inl e))
  · exact fun i _ => add_le_add (Chunk.total_width r (p.1 (.inr i))) (Chunk.total_width t (p.2 i))

-- 读法：`(∑ v, ((B.emitted p P).arity v : ℝ))` 不超过 `(∑ v, (B.base.arity v : ℝ)) + 2 * ((∑ e, seamWidth C d e) + ∑ i, legWidth C i)`。
theorem emitted_total : (∑ v, ((B.emitted p P).arity v : ℝ)) ≤
    (∑ v, (B.base.arity v : ℝ)) + 2 * ((∑ e, seamWidth C d e) + ∑ i, legWidth C i) := by
  rw [← Nat.cast_sum, ← Nat.cast_sum, Bundled.arity_total, Bundled.arity_total]
  push_cast
  linarith only [B.emitted_width p P]

end Backdrop
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# 球面展开所用的宿主槽位

在每个非空单元中，为两种状态的站点、两个普通枢纽以及每个分块上的两个形式预留槽位。较大的宿主图与具体配置及活动站点列表均无关。

**英文原文**

Host slots for a sphere expansion

Within each occupied cell reserve slots for stations of either status,
two ordinary hubs, and the two forms in each chunk. The larger host is
independent of the profile or the active station list.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y) {h D T R g : ℕ} {W : ℝ} (P : Input F a b h D T R g W)

-- 读法：结构的字段包括 `rank`、`inject`。
/-- 由同一宿主上各个独立的块实例共享。

英文原文：Shared across the independent block occurrences of a host.
-/
structure Steering {V : Type} (adj : V → Finset V) (n : ℕ) where
  rank : V → V → Fin (n + 1)
  inject : ∀ v, Set.InjOn (rank v) (insert v (adj v) : Finset V)

-- 读法：`Steering.any` 的结果类型为 `Steering adj n`。
def Steering.any {V : Type} (adj : V → Finset V) (n : ℕ) (h : ∀ v, (adj v).card ≤ n) :
    Steering adj n := by
  let f (v : V) : ↥(insert v (adj v)) ↪ Fin (n + 1) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact (card_insert_le ..).trans (Nat.add_le_add_right (h v) 1)))
  refine ⟨fun v w => if h : w ∈ insert v (adj v) then f v ⟨w, h⟩ else 0, ?_⟩
  intro v x hx y hy he
  change x ∈ insert v (adj v) at hx
  change y ∈ insert v (adj v) at hy
  simp only [dite_eq_left hx, dite_eq_left hy] at he
  exact congrArg Subtype.val ((f v).injective he)

-- 读法：结构的字段包括 `site`、`near`、`count`、`chunks`、`degree`。
/-- 接缝邻接关系与输入分块相容。

英文原文：The seam contacts respect the input blocks.
-/
structure Geo (k : ℕ) where
  site : V ↪ P.V × Cell h
  near : ∀ e, let p := site (S.src e); let q := site (S.dst e)
    p.2 = q.2 ∧ (q.1 = p.1 ∨ q.1 ∈ P.adj p.1)
  count : ∀ v, (C v).stations.length ≤ D ^ k
  chunks : M ≤ D ^ k
  degree : g ≤ D ^ k
  frozen : Place C → Prop
  left : ∀ i, frozen (S.left i)
  right : ∀ i, frozen (S.right i)
  steer : Steering P.adj (D ^ k) := Steering.any _ _ (fun i => (P.degree i).trans degree)

-- 读法：在后续公式中，`Position` 是 `S.Vertex ⊕ Grid M V` 的缩写。
abbrev Position := S.Vertex ⊕ Grid M V

-- 读法：逐一匹配以下输入模式：`.inl (.inl i)`、`.inl (.inr (.inl v)) | .inl (.inr (.inr v))`、`.inr s`。
def home : S.Position → V
  | .inl (.inl i) => i.1
  | .inl (.inr (.inl v)) | .inl (.inr (.inr v)) => v
  | .inr s => Grid.point s

-- 读法：在后续公式中，`Slot` 是 `(Bool × Fin (D ^ k)) ⊕ (Bool ⊕ (Fin M ⊕ Fin M))` 的缩写。
abbrev Slot (M D k : ℕ) := (Bool × Fin (D ^ k)) ⊕ (Bool ⊕ (Fin M ⊕ Fin M))

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr _`。
def frozenSlot {M D k : ℕ} : Slot M D k → Prop
  | .inl i => i.1 = true
  | .inr _ => False

-- 读法：`radius` 的取值由 `8 * (k + 1)` 给出。
def radius (k : ℕ) := 8 * (k + 1)

namespace Geo

variable {S P} {k : ℕ} (G : S.Geo P k)

-- 读法：逐一匹配输入模式，例如 `.inl (.inl i)`、`.inl (.inr (.inl _))`、`.inl (.inr (.inr _))`、`.inr (.inl p)`。
def slot : S.Position → Slot M D k
  | .inl (.inl i) => .inl (decide (G.frozen i), Fin.castLE (G.count i.1) i.2)
  | .inl (.inr (.inl _)) => .inr (.inl false)
  | .inl (.inr (.inr _)) => .inr (.inl true)
  | .inr (.inl p) => .inr (.inr (.inl p.2))
  | .inr (.inr p) => .inr (.inr (.inr p.2))

-- 读法：`place` 的取值由 `(((G.site (S.home x)).1, G.slot x), (G.site (S.home x)).2)` 给出。
def place (x : S.Position) : (P.V × Slot M D k) × Cell h :=
  (((G.site (S.home x)).1, G.slot x), (G.site (S.home x)).2)

-- 读法：`G.place` 是单射。
theorem one : Function.Injective G.place := by
  intro x y h
  have he : S.home x = S.home y := G.site.injective (congrArg (fun p => (p.1.1, p.2)) h)
  have hf : G.slot x = G.slot y := congrArg (fun p => p.1.2) h
  rcases x with ((⟨v, i⟩ | v | v) | (⟨v, i⟩ | ⟨v, i⟩)) <;>
    rcases y with ((⟨u, j⟩ | u | u) | (⟨u, j⟩ | ⟨u, j⟩))
  all_goals simp only [slot, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hf
  all_goals change v = u at he
  all_goals subst u
  · have : i = j := Fin.ext (congrArg (fun x : Fin (D ^ k) => x.val) hf.2)
    rw [this]
  · rfl
  · rfl
  · rw [hf]
  · rw [hf]

-- 读法：`neighbors` 的取值由 `insert p.1 (P.adj p.1) ×ˢ (univ : Finset (Slot M D k))` 给出。
def neighbors (_ : S.Geo P k) (p : P.V × Slot M D k) :=
  insert p.1 (P.adj p.1) ×ˢ (univ : Finset (Slot M D k))

-- 读法：`y` 属于 `G.neighbors x`。这里调用 `h.imp`。
theorem symmetric (x y : P.V × Slot M D k) (h : x ∈ G.neighbors y) : y ∈ G.neighbors x := by
  simp only [neighbors, mem_product, mem_univ, and_true, mem_insert] at h ⊢
  exact h.imp Eq.symm (P.sym _ _)

include G in
-- 读法：`Fintype.card (Slot M D k)` 不超过 `6 * D ^ k`。
theorem slot_count (hD : 4 ≤ D) : Fintype.card (Slot M D k) ≤ 6 * D ^ k := by
  simp only [Slot, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  have := G.chunks
  have : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  omega

-- 读法：`64 * (D ^ k) ^ 3` 不超过 `D ^ radius k`。
theorem polynomial (hD : 4 ≤ D) (k : ℕ) : 64 * (D ^ k) ^ 3 ≤ D ^ radius k := by
  calc
    _ ≤ D ^ 3 * (D ^ k) ^ 3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hD 3)
    _ = D ^ (3 + k * 3) := by rw [pow_add, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold radius; omega)

include G in
-- 读法：`Fintype.card (P.V × Slot M D k)` 不超过 `D ^ radius k * Fintype.card P.V`。这里调用 `Nat.mul_le_mul_right`。
theorem host_count (hD : 4 ≤ D) :
    Fintype.card (P.V × Slot M D k) ≤ D ^ radius k * Fintype.card P.V := by
  rw [Fintype.card_prod, mul_comm]
  apply Nat.mul_le_mul_right
  exact ((G.slot_count hD).trans (Nat.mul_le_mul (by decide : 6 ≤ 64) (Nat.le_self_pow (by decide : 3 ≠ 0) _))).trans
    (polynomial hD k)

-- 读法：`(G.neighbors v).card` 不超过 `D ^ radius k`。
theorem neighbor_count (hD : 4 ≤ D) (v : P.V × Slot M D k) :
    (G.neighbors v).card ≤ D ^ radius k := by
  rw [neighbors, card_product, card_univ]
  have h₁ := (card_insert_le v.1 (P.adj v.1)).trans (Nat.add_le_add_right ((P.degree _).trans G.degree) 1)
  have hp : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ (D ^ k + 1) * (6 * D ^ k) := Nat.mul_le_mul h₁ (G.slot_count hD)
    _ ≤ 64 * (D ^ k) ^ 3 := by nlinarith [Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)]
    _ ≤ _ := polynomial hD k

variable {d : ℕ} (hD : D = 2 ^ d) (hD' : 4 ≤ D)

-- 读法：`steeringCode` 的结果类型为 `Fin (D ^ k + 1) × Slot M D k ↪ Address (radius k * d)`。
def steeringCode (hc : M ≤ D ^ k) : Fin (D ^ k + 1) × Slot M D k ↪ Address (radius k * d) := by
  apply binaryCode
  simp only [Slot, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
  rw [mul_comm (radius k), pow_mul, ←hD]
  have hp : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ (D ^ k + 1) * (6 * D ^ k) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 64 * (D ^ k) ^ 3 := by nlinarith [Nat.pow_le_pow_right hp (by decide : 2 ≤ 3)]
    _ ≤ _ := polynomial hD' k

-- 读法：用字段 `near`、`symm`、`frozen`、`code` 构造 `Trie (P.V × Slot M D k) (radius k * d)`。
abbrev tree : Trie (P.V × Slot M D k) (radius k * d) where
  near := G.neighbors
  symm := G.symmetric
  frozen v := frozenSlot v.2
  code v w := steeringCode hD hD' G.chunks (G.steer.rank v.1 w.1, w.2)
  inject v x hx y hy he := by
    obtain ⟨he, hs⟩ := Prod.mk.inj ((steeringCode hD hD' G.chunks).injective he)
    exact Prod.ext (G.steer.inject _ (mem_product.mp hx).1 (mem_product.mp hy).1 he) hs

variable [Field F] [Fintype E] [Fintype V] [Fintype K] {e : E → ℕ} (p : Profile C e) (L : ℕ)

-- 读法：结论为 `let s := G.place ((S.backdrop.emitted p L).src i) let t := G.place ((S.backdrop.emitted p L).dst i) s.2 = t.2 ∧ (t.1.1 = s.1.1 ∨ t.1.1 ∈ P.adj s.1.1)`。这里调用 `G.near`。
private theorem contacts (i : (S.backdrop.emitted p L).E) :
    let s := G.place ((S.backdrop.emitted p L).src i)
    let t := G.place ((S.backdrop.emitted p L).dst i)
    s.2 = t.2 ∧ (t.1.1 = s.1.1 ∨ t.1.1 ∈ P.adj s.1.1) := by
  rcases i with ⟨i, j|j|j⟩ | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact ⟨rfl, .inl rfl⟩
  · exact G.near j.val
  · exact ⟨rfl, .inl rfl⟩
  · exact G.near i
  · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩

-- 读法：用字段 `site`、`one`、`group`、`near` 构造 `Fanout (S.backdrop.emitted p L) (G.tree hD hD') (Cell h)`。
abbrev layout : Fanout (S.backdrop.emitted p L) (G.tree hD hD') (Cell h) where
  site := G.place
  one := G.one
  group i := (G.contacts p L i).1
  near i := mem_product.mpr ⟨mem_insert.mpr (G.contacts p L i).2, mem_univ _⟩

-- 读法：`(G.layout hD hD' p L).fixed (.inl (.inl i))` 与 `G.frozen i` 等价。
theorem fixed_item (i : Place C) :
    (G.layout hD hD' p L).fixed (.inl (.inl i)) ↔ G.frozen i := by
  change decide (G.frozen i) = true ↔ _
  simp

-- 读法：要证明的命题是 `(G.layout hD hD' p L).exterior`。
theorem external : (G.layout hD hD' p L).exterior :=
  ⟨fun i => (G.fixed_item hD hD' p L _).mpr (G.left i),
    fun i => (G.fixed_item hD hD' p L _).mpr (G.right i)⟩

-- 读法：用字段 `toFun`、`left_inv`、`right_inv` 构造 `{i // G.frozen i} ≃ (G.layout hD hD' p L).Frozen`。
def frozenEquiv : {i // G.frozen i} ≃ (G.layout hD hD' p L).Frozen where
  toFun i := ⟨.inl (.inl i.val), (G.fixed_item hD hD' p L _).mpr i.property⟩
  invFun
    | ⟨.inl (.inl i), hi⟩ => ⟨i, (G.fixed_item hD hD' p L _).mp hi⟩
    | ⟨.inl (.inr (.inl _)), hi⟩ | ⟨.inl (.inr (.inr _)), hi⟩
    | ⟨.inr (.inl _), hi⟩ | ⟨.inr (.inr _), hi⟩ => False.elim hi
  left_inv _ := rfl
  right_inv := by
    rintro ⟨((i | v | v) | (v|v)), hi⟩
    · rfl
    all_goals exact False.elim hi

end Geo
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

section
/-!
# 公共路由宿主图的尺度不等式

**英文原文**

Scale inequalities for the common routing host
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Finset

variable {c d D T u ℓ C : ℕ}

-- 读法：`3 * c + ℓ + 2 ≤ C` 与 `8 * (c + 1) ^ 2 ≤ C` 同时成立。
theorem exponent_bounds (hC : exponent c ℓ ≤ C) :
    3 * c + ℓ + 2 ≤ C ∧ 8 * (c + 1) ^ 2 ≤ C := by
  unfold exponent at hC
  constructor <;> nlinarith [Nat.zero_le (c * ℓ)]

-- 读法：`(1 + (c * d + 1) * 2 ^ (c * d)) * D ^ c ≤ D ^ C` 与 `(c * d + 1) * 2 ^ (c * d) ≤ (D ^ c) ^ 2 ∧ max 3 (2 ^ (c * d)) ≤ D ^ C` 同时成立。
theorem host_bound (hD : D = 2 ^ d) (hD' : 4 ≤ D) (hC : exponent c ℓ ≤ C) :
    (1 + (c * d + 1) * 2 ^ (c * d)) * D ^ c ≤ D ^ C ∧ (c * d + 1) * 2 ^ (c * d) ≤ (D ^ c) ^ 2 ∧
      max 3 (2 ^ (c * d)) ≤ D ^ C := by
  have hc := (exponent_bounds hC).1
  have he : 2 ^ (c * d) = D ^ c := by rw [hD, ← pow_mul, mul_comm c]
  have hp : 1 ≤ D ^ c := Nat.one_le_pow _ _ (by omega)
  have hq : c * d + 1 ≤ D ^ c := by rw [← he]; exact Nat.lt_two_pow_self
  have hr : (c * d + 1) * 2 ^ (c * d) ≤ (D ^ c) ^ 2 := by rw [he, pow_two]; gcongr
  have h := Nat.pow_le_pow_right (by omega : 0 < D) (show 3 * c + 1 ≤ C by omega)
  refine ⟨?_, hr, max_le ?_ ?_⟩
  · refine le_trans ?_ h
    rw [pow_succ, mul_comm 3 c, pow_mul D c 3]
    calc
      _ ≤ (1 + (D ^ c) ^ 2) * D ^ c := by gcongr
      _ ≤ (D ^ c) ^ 3 * 2 := by nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) (D ^ c)]
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · exact (show 3 ≤ D by omega).trans (Nat.le_self_pow (by omega) _)
  · rw [he]
    exact Nat.pow_le_pow_right (by omega) (by omega)

-- 读法：`(u : ℝ) * ((D : ℝ) ^ c) ^ 3 ≤ T` 与 `((u : ℝ) * ((D : ℝ) ^ c + 1)) * (4 * (D : ℝ) ^ ℓ) ≤ T` 同时成立。
theorem padding_budget (hD : 4 ≤ D) (hC : exponent c ℓ ≤ C) (hs : u * D ^ C ≤ T) :
    (u : ℝ) * ((D : ℝ) ^ c) ^ 3 ≤ T ∧
      ((u : ℝ) * ((D : ℝ) ^ c + 1)) * (4 * (D : ℝ) ^ ℓ) ≤ T := by
  have hc := (exponent_bounds hC).1
  have hp : 1 ≤ D ^ c := Nat.one_le_pow _ _ (by omega)
  have hb (n) (hn : n ≤ C) : u * D ^ n ≤ T :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hn)).trans hs
  have h₁ := hb (c * 3) (by omega)
  rw [pow_mul] at h₁
  have h₂ : u * (D ^ c + 1) * (4 * D ^ ℓ) ≤ T := calc
    _ ≤ u * (D ^ c * 2) * (4 * D ^ ℓ) := by gcongr; omega
    _ = u * D ^ c * D ^ ℓ * 8 := by ring
    _ ≤ u * D ^ c * D ^ ℓ * D ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    _ = u * D ^ (c + ℓ + 2) := by simp [pow_add, mul_assoc]
    _ ≤ T := hb _ (by omega)
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-!
# 二进制路由后的集中

平方预算用于支付冻结费用。总核心宽度会乘上一个对数级的路由深度；为每条线束取整及为空置槽位计费所消耗的开销，均落在允许的多项式填充余量内。

**英文原文**

Concentration after binary routing

The square budget covers frozen charges. A logarithmic routing depth
multiplies the total core width; rounding every bundle and charging
unused slots consume only the allowed polynomial padding margin.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Classical Finset Rounds Packing

variable {F V : Type} [Field F] [Fintype V] {a b : Wire} {c d h D T R g u C ℓ : ℕ} {W : ℝ}
  {G : Bundled F a b} {S : Trie V (c * d)} (H : Fanout G S (Cell h))
  (P : Input F a b h D T R g W)

omit [Field F] in
-- 读法：`((G.pad u).arity v : ℝ) + u` 不超过 `G.arity v + (u : ℝ) * ((D : ℝ) ^ c + 1)`。
private theorem charge_pad (h : H.Caps P ℓ) (u : ℕ) (v : G.V) :
    ((G.pad u).arity v : ℝ) + u ≤ G.arity v + (u : ℝ) * ((D : ℝ) ^ c + 1) := by
  have hh : (G.pad u).arity v ≤ G.arity v + u * D ^ c :=
    (G.arity_pad u v).trans (by gcongr; exact h.degree v)
  have ht : ((G.pad u).arity v : ℝ) ≤ G.arity v + u * (D : ℝ) ^ c := by exact_mod_cast hh
  linarith

omit [Field F] in
-- 读法：`((Fintype.card G.V : ℝ) + Fintype.card G.E) * u * ((D : ℝ) ^ c) ^ 2` 不超过 `W`。这里调用 `mul_le_mul_iff_left₀`。
private theorem size_pad (h : H.Caps P ℓ) (hD : 4 ≤ D) (hC : exponent c ℓ ≤ C)
    (hs : u * D ^ C ≤ T) :
    ((Fintype.card G.V : ℝ) + Fintype.card G.E) * u * ((D : ℝ) ^ c) ^ 2 ≤ W := by
  have hp : 0 < (D : ℝ) ^ c := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    _ = ((Fintype.card G.V : ℝ) + Fintype.card G.E) * (u * ((D : ℝ) ^ c) ^ 3) := by ring
    _ ≤ ((Fintype.card G.V : ℝ) + Fintype.card G.E) * T := by
      gcongr
      exact (padding_budget hD hC hs).1
    _ ≤ _ := h.size.trans_eq (mul_comm _ _)

-- 读法：`(∑ v : (H.finish he hu).freeze.Core, (H.finish he hu).charge v.val)` 不超过 `C * W * (1 + (d : ℝ)) ^ 2`。
private theorem sum_finish (hcap : H.Caps P ℓ) (hD : D = 2 ^ d) (hD' : 4 ≤ D) (hc : 1 ≤ c)
    (hC : exponent c ℓ ≤ C) (hu : 0 < u) (hs : u * D ^ C ≤ T) (he : H.exterior) :
    (∑ v : (H.finish he hu).freeze.Core, (H.finish he hu).charge v.val) ≤ C * W * (1 + (d : ℝ)) ^ 2 := by
  let p := (D : ℝ) ^ c
  have hp : 1 ≤ p := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D by omega))
  have ht := H.size_pad P hcap hD' hC hs
  have hW : 0 ≤ W := le_trans (by positivity) ht
  have hv : (Fintype.card G.V : ℝ) * u * p ^ 2 ≤ W := le_trans (by gcongr; simp) ht
  have hj : (Fintype.card G.E : ℝ) * u ≤ W := calc
    _ ≤ (Fintype.card G.E : ℝ) * u * p ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hp)
    _ ≤ _ := le_trans (by gcongr; simp) ht
  -- 推导：记下中间结论 `hrelay`：`(Fintype.card (Relay G.V (c * d)) : ℝ) * u ≤ W`。
  have hrelay : (Fintype.card (Relay G.V (c * d)) : ℝ) * u ≤ W := by
    have hh : Fintype.card (Relay G.V (c * d)) ≤ Fintype.card G.V * (D ^ c) ^ 2 := by
      simp only [Relay, Address, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool]
      exact Nat.mul_le_mul_left _ (host_bound hD hD' hC).2.1
    calc
      _ ≤ (Fintype.card G.V : ℝ) * p ^ 2 * u := by gcongr; unfold p; exact_mod_cast hh
      _ = (Fintype.card G.V : ℝ) * u * p ^ 2 := by ring
      _ ≤ _ := hv
  have hold : (∑ v : H.Mobile, (((G.pad u).arity v.val : ℝ) + u)) ≤
      c * W * (1 + (d : ℝ)) + 2 * W := by
    -- 推导：记下中间结论 `hb`：`(Fintype.card H.Mobile : ℝ) ≤ Fintype.card G.V`。
    have hb : (Fintype.card H.Mobile : ℝ) ≤ Fintype.card G.V :=
      Nat.cast_le.mpr (Fintype.card_subtype_le _)
    calc
      _ ≤ ∑ v : H.Mobile, ((G.arity v.val : ℝ) + u * (p + 1)) :=
        sum_le_sum fun v _ => H.charge_pad P hcap u v.val
      _ = (∑ v : H.Mobile, (G.arity v.val : ℝ)) + Fintype.card H.Mobile * (u * (p + 1)) := by
        simp [sum_add_distrib]
      _ ≤ c * W * (1 + (d : ℝ)) + Fintype.card G.V * (u * (2 * p ^ 2)) := by
        gcongr
        · exact hcap.coreSum
        · nlinarith only [hp]
      _ ≤ _ := by linarith only [hv]
  -- 推导：记下中间结论 `hsum`：`(∑ e, ((G.pad u).width e : ℝ)) ≤ c * W * (1 + (d : ℝ)) + W`。
  have hsum : (∑ e, ((G.pad u).width e : ℝ)) ≤ c * W * (1 + (d : ℝ)) + W := by
    have hb := G.total_pad u
    have hh : (∑ e, ((G.pad u).width e : ℝ)) ≤ (∑ e, (G.width e : ℝ)) + Fintype.card G.E * (u : ℝ) := by
      exact_mod_cast hb
    exact hh.trans (add_le_add hcap.edges hj)
  have hh := (H.pad u).core_sum he (G.divisible_pad u hu)
  refine hh.trans_le ?_
  push_cast
  calc
    _ ≤ (c * W * (1 + (d : ℝ)) + 2 * W) + 4 * (c * d + 1) * (c * W * (1 + d) + W) + W := by
      exact add_le_add (add_le_add hold (mul_le_mul_of_nonneg_left hsum (by positivity))) hrelay
    _ ≤ 8 * ((c : ℝ) + 1) ^ 2 * W * (1 + d) ^ 2 := by
      apply sub_nonneg.mp
      ring_nf
      positivity
    _ ≤ _ := by gcongr; exact_mod_cast (exponent_bounds hC).2

-- 读法：`(H.finish he hu).charge v.val * (D : ℝ) ^ ℓ` 不超过 `T`。
private theorem max_finish (hcap : H.Caps P ℓ) (hD : 4 ≤ D)
    (hC : exponent c ℓ ≤ C) (hu : 0 < u) (hs : u * D ^ C ≤ T) (he : H.exterior)
    (v : (H.finish he hu).freeze.Core) :
    (H.finish he hu).charge v.val * (D : ℝ) ^ ℓ ≤ T := by
  let B := (T : ℝ) / (D : ℝ) ^ (ℓ + 2)
  let p := (D : ℝ) ^ c
  have hh := (H.pad u).core_max he (G.divisible_pad u hu) (B := B + u * p)
    (by unfold B p; positivity) (by
      intro w
      exact (show ((G.pad u).arity w.val : ℝ) ≤ G.arity w.val + (u : ℝ) * p by
        have := H.charge_pad P hcap u w.val
        unfold p; linarith).trans (add_le_add_left (hcap.coreMax w) _)) (by
      intro w w'
      have h₁ := (G.ties_pad u w.val w'.val).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left u (hcap.degree w.val)) _)
      exact (show ((G.pad u).ties w.val w'.val : ℝ) ≤ G.ties w.val w'.val + (u : ℝ) * p by
        unfold p; exact_mod_cast h₁).trans (add_le_add_left (hcap.ties w w') _)) v
  -- 推导：记下中间结论 `hD'`：`4 ≤ (D : ℝ)`。
  have hD' : 4 ≤ (D : ℝ) := by exact_mod_cast hD
  have h₁ : B * (D : ℝ) ^ ℓ ≤ T / 4 := by
    have h : B * (D : ℝ) ^ ℓ = T / (D : ℝ) ^ 2 := by
      unfold B
      rw [pow_add]
      field_simp
    rw [h]
    gcongr
    nlinarith
  have h₂ : (u : ℝ) * (p + 1) * (4 * (D : ℝ) ^ ℓ) ≤ T := (padding_budget hD hC hs).2
  refine (mul_le_mul_of_nonneg_right hh (by positivity)).trans ?_
  linarith only [h₁, h₂, show 0 ≤ (u : ℝ) * (D : ℝ) ^ ℓ by positivity]

-- 读法：要证明的命题是 `Concentrated P (H.finish he hu) C d ℓ`。
theorem concentrated (hD : D = 2 ^ d) (hD' : 4 ≤ D) (hc : 1 ≤ c) (hC : exponent c ℓ ≤ C)
    (hu : 0 < u) (hs : u * D ^ C ≤ T) (he : H.exterior) (hcap : H.Caps P ℓ) :
    Concentrated P (H.finish he hu) C d ℓ := by
  have hC₄ : 4 * c ≤ C := by have := (exponent_bounds hC).2; nlinarith
  have hCc : c ≤ C := by omega
  have hW : 0 ≤ W := le_trans (by positivity) (H.size_pad P hcap hD' hC hs)
  have hscale : 1 ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hp : (u : ℝ) * ((D : ℝ) ^ c + 1) ≤ T := by
    refine (le_mul_of_one_le_right (by positivity) ?_).trans (padding_budget hD' hC hs).2
    have : 1 ≤ (D : ℝ) ^ ℓ := one_le_pow₀ hscale
    linarith
  have charge (v : G.V) : ((G.pad u).arity v : ℝ) + u ≤ G.arity v + (T : ℝ) :=
    (H.charge_pad P hcap u v).trans (add_le_add_right hp _)
  have host := host_bound hD hD' hC
  let H' := H.pad u
  have hw := G.divisible_pad u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, H.max_finish P hcap hD' hC hu hs he,
    H.sum_finish P hcap hD hD' hc hC hu hs he⟩
  · change Fintype.card (Node V (c * d)) ≤ _
    rw [node_count]
    calc
      _ ≤ (1 + (c * d + 1) * 2 ^ (c * d)) * (D ^ c * Fintype.card P.V) := Nat.mul_le_mul_left _ hcap.cells
      _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ host.1
  · intro v
    exact (S.core_degree v).trans (by omega)
  · intro v
    exact (S.degree v).trans host.2.2
  · rw [← Fintype.card_congr (H'.fixedEquiv he)]
    exact hcap.frozenCount.trans (by gcongr)
  · intro v
    -- 推导：从 `(H'.fixedEquiv he).surjective v` 中取出 `w, rfl`。
    obtain ⟨w, rfl⟩ := (H'.fixedEquiv he).surjective v
    change (H'.term he hw).charge (.inl w.val) ≤ _
    rw [H'.old_charge he hw]
    calc
      _ ≤ G.arity w.val + (T : ℝ) := charge w.val
      _ ≤ (c : ℝ) * D * T + D * T := add_le_add (hcap.frozenMax w)
        (le_mul_of_one_le_left (by positivity) hscale)
      _ = ((c : ℝ) + 1) * D * T := by ring
      _ ≤ _ := by gcongr; exact_mod_cast (show c + 1 ≤ C by omega)
  · refine (H'.frozen_sum he hw (fun t => t ^ 2)).trans_le ?_
    -- 推导：记下中间结论 `hsum`：`(Fintype.card H.Frozen : ℝ) * T ≤ c * W`。
    have hsum : (Fintype.card H.Frozen : ℝ) * T ≤ c * W := calc
      _ ≤ Fintype.card H.Frozen * (D : ℝ) * T := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hscale
      _ ≤ _ := hcap.frozenCount
    calc
      _ ≤ ∑ v : H.Frozen, (2 * (G.arity v.val : ℝ) ^ 2 + 2 * (T : ℝ) ^ 2) := by
        apply sum_le_sum
        intro v _
        have hb := pow_le_pow_left₀ (by positivity) (charge v.val) 2
        nlinarith only [hb, sq_nonneg ((G.arity v.val : ℝ) - T)]
      _ = 2 * (∑ v : H.Frozen, (G.arity v.val : ℝ) ^ 2) + 2 * (Fintype.card H.Frozen * T) * T := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
        ring
      _ ≤ 4 * (c : ℝ) * W * T := by
        linarith only [hcap.frozenSquare, mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg T)]
      _ ≤ _ := by gcongr; exact_mod_cast hC₄

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end
