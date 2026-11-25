-- 本文件所属证明环节：用有限有向多重图表示带端口的比特张量网络，证明细分、重编号、替换及取幂对张量收缩和规模的影响。
import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Input
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Tagged.ColumnNetwork
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode

section
/-!
# 从图式中移除标量站点

**英文原文**

Removing scalar stations from a diagram
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：`0` 严格小于 `wd d`。使用 `card_slots` 给出的结论。
private theorem slot_pos {d : Wire} (i : slots d) : 0 < wd d :=
  (card_slots d) ▸ Fintype.card_pos_iff.mpr ⟨i⟩

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Σ v : {v // 0 < G.arity v}, slots (d v.val)) ≃ Σ v, slots (d v)`。
private def keepSlots (d : G.V → Wire) (h : ∀ v, wd (d v) ≤ G.arity v) :
    (Σ v : {v // 0 < G.arity v}, slots (d v.val)) ≃ Σ v, slots (d v) where
  toFun i := ⟨i.1.val, i.2⟩
  invFun i := ⟨⟨i.1, (slot_pos i.2).trans_le (h i.1)⟩, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F a b`。
/-- 每个线端本来就属于一个正元数站点。

英文原文：Every wire end already belongs to a station of positive arity.
-/
abbrev prune : Diagram F a b where
  V := {v : G.V // 0 < G.arity v}
  E := G.E
  table v := G.table v.val
  src := (G.keepSlots (fun v => (G.table v).1) (fun _ => Nat.le_add_right _ _)).trans G.src
  dst := (G.keepSlots (fun v => (G.table v).2.1) (fun _ => Nat.le_add_left _ _)).trans G.dst

-- 读法：`G.prune.arity v` 等于 `G.arity v.val`。两端由定义化简为同一项。
theorem arity_prune (v : G.prune.V) : G.prune.arity v = G.arity v.val := rfl

-- 读法：`(G.prune.source e).val` 等于 `G.source e`。两端由定义化简为同一项。
theorem source_prune (e : G.E) : (G.prune.source e).val = G.source e := rfl

-- 读法：`(G.prune.target e).val` 等于 `G.target e`。两端由定义化简为同一项。
theorem target_prune (e : G.E) : (G.prune.target e).val = G.target e := rfl

-- 读法：`G.vertex x y z v` 等于 `G.vertex x' y' z' v`。
private theorem scalar_vertex (v : G.V) (hv : ¬0 < G.arity v)
    (x x' : Val a) (y y' : Val b) (z z' : G.E → Bool) :
    G.vertex x y z v = G.vertex x' y' z' v := by
  unfold vertex
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext i
  · exact (hv ((slot_pos i).trans_le (Nat.le_add_right _ _))).elim
  · exact (hv ((slot_pos i).trans_le (Nat.le_add_left _ _))).elim

-- 读法：存在 `c : F`，对每个 `x y`，`c * G.prune.eval x y` 等于 `G.eval x y`。这里调用 `Finset.sum_congr`。
/-- 被移除的各表的乘积与一切比特赋值无关。这个乘积可能为零，故直接将它提为因子，不对它作除法。

英文原文：The product of the removed tables is independent of all bit assignments.
It may vanish, so we factor it out without dividing by it.
-/
theorem eval_prune [Field F] : ∃ c : F, ∀ x y, c * G.prune.eval x y = G.eval x y := by
  classical
  let x₀ := (bits a).symm (fun _ => false)
  let y₀ := (bits b).symm (fun _ => false)
  refine ⟨∏ v : {v // ¬0 < G.arity v}, G.vertex x₀ y₀ (fun _ => false) v.val, ?_⟩
  intro x y
  rw [eval, eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [mul_comm, ← Fintype.prod_subtype_mul_prod_subtype (fun v => 0 < G.arity v)
    (G.vertex x y z)]
  apply congrArg
  exact Finset.prod_congr rfl fun v _ => G.scalar_vertex v.val v.property _ _ _ _ _ _

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# 有向网络的独立副本

**英文原文**

Independent copies of a directed network
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical Diagonal

variable {F I : Type} {n : ℕ} {a b : Wire} (G : Diagram F a b) (c : I ≃ Fin n)

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Σ q : I × G.V, Z q.2) ≃ I × (Σ v, Z v)`。
private def collect (Z : G.V → Type) : (Σ q : I × G.V, Z q.2) ≃ I × (Σ v, Z v) where
  toFun q := (q.1.1, ⟨q.1.2, q.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- 读法：`io` 的结果类型为 `(Σ q : I × G.V, Z q.2) ≃ slots (copies d n) ⊕ (I × G.E)`。
private def io (d : Wire) (Z : G.V → Type) (p : (Σ v, Z v) ≃ slots d ⊕ G.E) :
    (Σ q : I × G.V, Z q.2) ≃ slots (copies d n) ⊕ (I × G.E) :=
  (G.collect Z).trans <| ((Equiv.refl I).prodCongr p).trans <|
    (Equiv.prodSumDistrib _ _ _).trans <|
      (((c.prodCongr (.refl _)).trans (port d n).symm).sumCongr (.refl _))

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F (copies a n) (copies b n)`。
abbrev replicate [Fintype I] : Diagram F (copies a n) (copies b n) where
  V := I × G.V
  E := I × G.E
  table v := G.table v.2
  src := G.io c a (fun v => slots (G.table v).1) G.src
  dst := G.io c b (fun v => slots (G.table v).2.1) G.dst

-- 读法：`Sum.elim (bits (copies d n) (bundle d n x)) (Function.uncurry z) (G.io c d Z p ⟨(i, v), t⟩)` 等于 `Sum.elim (bits d (x (c i))) (z i) (p ⟨v, t⟩)`。
private theorem read_io (d : Wire) (Z : G.V → Type) (p : (Σ v, Z v) ≃ slots d ⊕ G.E)
    (x : Fin n → Val d) (z : I → G.E → Bool) (i : I) (v : G.V) (t : Z v) :
    Sum.elim (bits (copies d n) (bundle d n x)) (Function.uncurry z)
      (G.io c d Z p ⟨(i, v), t⟩) = Sum.elim (bits d (x (c i))) (z i) (p ⟨v, t⟩) := by
  change Sum.elim _ _ (Sum.map _ _ (Equiv.prodSumDistrib I _ _ (i, p ⟨v, t⟩))) = _
  cases p ⟨v, t⟩ with
  | inl s =>
    change bits (copies d n) (bundle d n x) ((port d n).symm (c i, s)) = _
    simp [bits_bundle]
  | inr e => rfl

-- 读法：`(bundle d n)` 是满射。
private theorem bundle_surj (d : Wire) (n : ℕ) : Function.Surjective (bundle d n) := by
  intro x
  let v := fun i => (bits d).symm (fun s => bits (copies d n) x ((port d n).symm (i, s)))
  refine ⟨v, (bits _).injective (funext fun s => ?_)⟩
  simp only [bits_bundle, v, Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]

variable [Fintype I]

-- 读法：`(G.replicate c).source (i, e)` 等于 `(i, G.source e)`。两端由定义化简为同一项。
@[simp] theorem source_replicate (i : I) (e : G.E) :
    (G.replicate c).source (i, e) = (i, G.source e) := rfl

-- 读法：`(G.replicate c).target (i, e)` 等于 `(i, G.target e)`。两端由定义化简为同一项。
@[simp] theorem target_replicate (i : I) (e : G.E) :
    (G.replicate c).target (i, e) = (i, G.target e) := rfl

-- 读法：`(G.replicate c).vertex (bundle a n x) (bundle b n y) (Function.uncurry z) (i, v)` 等于 `G.vertex (x (c i)) (y (c i)) (z i) v`。这里调用 `G.read_io`。
theorem vertex_replicate (x : Fin n → Val a) (y : Fin n → Val b) (z : I → G.E → Bool)
    (i : I) (v : G.V) :
    (G.replicate c).vertex (bundle a n x) (bundle b n y) (Function.uncurry z) (i, v) =
      G.vertex (x (c i)) (y (c i)) (z i) v := by
  unfold vertex
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext t
  · exact G.read_io c a _ G.src x z i v t
  · exact G.read_io c b _ G.dst y z i v t

-- 读法：`G.eval x y` 等于 `∑ z : I → E → Bool, ∏ v, G.vertex x y (Function.uncurry z ∘ e) v`。
private theorem eval_curry [Field F] {E : Type} [Fintype E] (e : G.E ≃ I × E) (x : Val a) (y : Val b) :
    G.eval x y = ∑ z : I → E → Bool, ∏ v, G.vertex x y (Function.uncurry z ∘ e) v := by
  let q := (e.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry I E Bool)
  unfold eval
  rw [← q.symm.sum_comp]
  rfl

-- 读法：`(G.replicate c).eval` 等于 `power G.eval n`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval_replicate [Field F] : (G.replicate c).eval = power G.eval n := by
  funext x y
  obtain ⟨X, rfl⟩ := bundle_surj _ _ x
  obtain ⟨Y, rfl⟩ := bundle_surj _ _ y
  rw [power_bundle, ← c.prod_comp]
  rw [eval_curry (G.replicate c) (I := I) (E := G.E) (Equiv.refl _)]
  unfold eval
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl
    (fun v _ => G.vertex_replicate c X Y z i v))

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-!
# 配有一组指定附加表的确定性电路

**英文原文**

Deterministic circuits with a specified set of additional tables
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type} [Field F]

-- 读法：`DWide` 表示以下条件：存在 `s ≤ m`，要证明的命题是 `Wide F u L a b (fun x y => if f x = y then 1 else 0) s`。
def DWide (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (a b : Wire) (f : Val a → Val b) (m : ℕ) : Prop :=
  ∃ s ≤ m, Wide F u L a b (fun x y => if f x = y then 1 else 0) s

namespace DWide
variable {u m n : ℕ} {L : Set (Table F)} {a b c d : Wire}
variable {f : Val a → Val b}

-- 读法：要证明的命题是 `DWide F u L a b f n`。
theorem mono (h : DWide F u L a b f m) (hv : m ≤ n) : DWide F u L a b f n :=
  let ⟨s, hs, hw⟩ := h
  ⟨s, hs.trans hv, hw⟩

-- 读法：要证明的命题是 `DWide F u L a c (fun x => g (f x)) m`。
theorem pre {g : Val b → Val c} (h : DWide F u L b c g m) (k : Rewire a b f) :
    DWide F u L a c (fun x => g (f x)) m :=
  let ⟨s, hs, hw⟩ := h
  ⟨s, hs, hw.pre k⟩

-- 读法：要证明的命题是 `DWide F u L a c (fun x => g (f x)) m`。
theorem post {g : Val b → Val c} (h : DWide F u L a b f m) (k : Rewire b c g) :
    DWide F u L a c (fun x => g (f x)) m := by
  obtain ⟨s, hs, hw⟩ := h
  obtain ⟨_, hk, he⟩ := k.inverse
  exact ⟨s, hs, by simpa only [he] using hw.post hk⟩

-- 读法：要证明的命题是 `DWide F u L a c (fun x => g (f x)) (m + n)`。
theorem comp {g : Val b → Val c} (h : DWide F u L a b f m) (k : DWide F u L b c g n) :
    DWide F u L a c (fun x => g (f x)) (m + n) := by
  obtain ⟨s, hs, hw⟩ := h
  obtain ⟨t, ht, hv⟩ := k
  refine ⟨s + t, Nat.add_le_add hs ht, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using hw.comp hv

-- 读法：要证明的命题是 `DWide F u L (.pair a c) (.pair b d) (fun x => (f x.1, g x.2)) (m + n)`。这里调用 `hw.par`。
theorem par {g : Val c → Val d} (h : DWide F u L a b f m) (k : DWide F u L c d g n) :
    DWide F u L (.pair a c) (.pair b d) (fun x => (f x.1, g x.2)) (m + n) := by
  obtain ⟨s, hs, hw⟩ := h
  obtain ⟨t, ht, hv⟩ := k
  refine ⟨s + t, Nat.add_le_add hs ht, ?_⟩
  simpa only [Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using hw.par hv

-- 读法：要证明的命题是 `DWide F u L a b f (4 * m)`。
theorem of_dnet (hu : 3 ≤ u) (h : DNet F a b f m) : DWide F u L a b f (4 * m) := by
  obtain ⟨s, hs, hw⟩ := h
  obtain ⟨v, hv, hv'⟩ := hw.includeWide (L := L) hu
  exact ⟨v, hv.trans (Nat.mul_le_mul_left _ hs), hv'⟩

-- 读法：要证明的命题是 `DWide F u L (copies a t) (copies b t) (mapCopies f t) (t * m)`。对 `t` 作归纳。
theorem many (h : DWide F u L a b f m) (t : ℕ) :
    DWide F u L (copies a t) (copies b t) (mapCopies f t) (t * m) := by
  induction t with
  | zero => exact ⟨0, Nat.zero_le _, Wide.empty⟩
  | succ t ih => rw [Nat.succ_mul, Nat.add_comm (t * m)]; exact h.par ih

-- 读法：`columnModel` 的取值由 `⟨DWide F u L, pre, post, comp, mono⟩` 给出。
def columnModel (F : Type) [Field F] (u : ℕ) (L : Set (Table F)) : Columns.Model :=
  ⟨DWide F u L, pre, post, comp, mono⟩

end DWide
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# 填充有序的平行线束

收集每对有序站点之间的比特，再将其二进制字用零延长。空线束仍为空。

**英文原文**

Padding ordered bundles of parallel wires

Collect the bits between each ordered pair of stations, then extend
their binary word by zeros. Empty bundles remain empty.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram

open Finset Sphere.Layout
open scoped Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b)

-- 读法：`width` 的取值由 `Fintype.card {e // G.source e = v ∧ G.target e = w}` 给出。
def width (v w : G.V) : ℕ := Fintype.card {e // G.source e = v ∧ G.target e = w}

-- 读法：`padWidth` 的取值由 `n + if R ∣ n then 0 else R - n % R` 给出。
def padWidth (R n : ℕ) : ℕ := n + if R ∣ n then 0 else R - n % R

-- 读法：`n` 不超过 `padWidth R n`。使用 `Nat.le_add_right` 给出的结论。
-- 读法：`padWidth R 0` 等于 `0`。
@[simp] theorem padWidth_zero (R : ℕ) : padWidth R 0 = 0 := by simp [padWidth]

theorem le_padWidth (R n : ℕ) : n ≤ padWidth R n := Nat.le_add_right _ _

-- 读法：`padWidth R n` 不超过 `n + R`。
theorem padWidth_le (R n : ℕ) : padWidth R n ≤ n + R := by
  unfold padWidth
  split_ifs <;> omega

-- 读法：`R` 整除 `padWidth R n`。
theorem dvd_padWidth {R : ℕ} (hR : 0 < R) (n : ℕ) : R ∣ padWidth R n := by
  unfold padWidth
  split_ifs with hd
  · simpa using hd
  · refine ⟨n / R + 1, ?_⟩
    rw [mul_add, mul_one]
    have := Nat.mod_add_div n R
    have := Nat.mod_lt n hR
    omega

-- 读法：在后续公式中，`Bundle` 是 `{e // G.source e = p.1 ∧ G.target e = p.2}` 的缩写。
private abbrev Bundle (p : G.V × G.V) := {e // G.source e = p.1 ∧ G.target e = p.2}

-- 读法：用字段 `toFun`、`inj'`、`let`、`have` 构造 `(G.Bundle p → Bool) ↪ (Fin (padWidth R (G.width p.1 p.2)) → Bool)`。
private def padCode (R : ℕ) (p : G.V × G.V) :
    (G.Bundle p → Bool) ↪ (Fin (padWidth R (G.width p.1 p.2)) → Bool) where
  toFun z i := if hi : i.val < G.width p.1 p.2 then
    z ((Fintype.equivFin (G.Bundle p)).symm ⟨i.val, hi⟩) else false
  inj' x y he := by
    funext e
    let i := Fintype.equivFin (G.Bundle p) e
    have hi : i.val < G.width p.1 p.2 := i.isLt
    have h := congrFun he ⟨i.val, hi.trans_le (le_padWidth R _)⟩
    simp only [dite_eq_left hi] at h
    change x ((Fintype.equivFin _).symm i) = y ((Fintype.equivFin _).symm i) at h
    simpa only [i, Equiv.symm_apply_apply] using h

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`rfl` 构造 `(∀ p, G.Bundle p → Bool) ≃ (G.E → Bool)`。
private def bundleBits : (∀ p, G.Bundle p → Bool) ≃ (G.E → Bool) where
  toFun z e := z (G.source e, G.target e) ⟨e, rfl, rfl⟩
  invFun z _ e := z e.val
  left_inv z := by
    funext p e
    rcases p with ⟨v, w⟩
    rcases e with ⟨e, hv, hw⟩
    cases hv
    cases hw
    rfl
  right_inv _ := rfl

-- 读法：用字段 `V`、`E`、`state`、`width` 构造 `Bundled F a b`。
private abbrev padded (R : ℕ) : Bundled F a b where
  V := G.V
  E := G.V × G.V
  state p := G.Bundle p → Bool
  width p := padWidth R (G.width p.1 p.2)
  code := G.padCode R
  src := Prod.fst
  dst := Prod.snd
  left i := (G.src.symm (.inl i)).1
  right i := (G.dst.symm (.inl i)).1
  station v x y z := G.vertex x y (G.bundleBits z) v
  locality v x y z x' y' z' hx hy hz := by
    apply G.local_weight
    · rintro (i | e) hi
      · exact hx i hi
      · exact congrFun (hz (G.source e, G.target e) (.inl hi)) ⟨e, rfl, rfl⟩
    · rintro (i | e) hi
      · exact hy i hi
      · exact congrFun (hz (G.source e, G.target e) (.inr hi)) ⟨e, rfl, rfl⟩

variable [Field F]

-- 读法：在后续公式中，`pad` 是 `(G.padded R).diagram` 的缩写。
abbrev pad (R : ℕ) : Diagram F a b := (G.padded R).diagram

-- 读法：`(G.pad R).eval` 等于 `G.eval`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval_pad (R : ℕ) : (G.pad R).eval = G.eval := by
  refine (G.padded R).eval_diagram.trans ?_
  let : DecidableEq (G.V × G.V) := Classical.typeDecidableEq _
  funext x y
  unfold Bundled.eval eval
  apply Fintype.sum_equiv G.bundleBits
  exact fun _ => rfl

-- 读法：`(G.pad R).width v w` 等于 `padWidth R (G.width v w)`。这里调用 `G.padded`。
theorem width_pad (R : ℕ) (v w : G.V) :
    (G.pad R).width v w = padWidth R (G.width v w) := by
  trans ∑ p : G.V × G.V, if p.1 = v ∧ p.2 = w then padWidth R (G.width p.1 p.2) else 0
  · exact (G.padded R).card_bits (fun p => p.1 = v ∧ p.2 = w)
  · rw [Fintype.sum_prod_type]
    simp [ite_and]

-- 读法：`R` 整除 `(G.pad R).width v w`。这里调用 `dvd_padWidth`。
theorem divisible_pad {R : ℕ} (hR : 0 < R) (v w : G.V) : R ∣ (G.pad R).width v w := by
  rw [width_pad]
  exact dvd_padWidth hR _

-- 读法：存在 `t : G.E`，`G.source t = (G.pad R).source e` 与 `G.target t = (G.pad R).target e` 同时成立。这里调用 `he.false`。
theorem contact_pad (R : ℕ) (e : (G.pad R).E) :
    ∃ t : G.E, G.source t = (G.pad R).source e ∧ G.target t = (G.pad R).target e := by
  have hp : 0 < G.width e.1.1 e.1.2 := by
    have he : 0 < padWidth R (G.width e.1.1 e.1.2) := Nat.zero_lt_of_lt e.2.isLt
    by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, padWidth_zero] at he
    exact he.false
  obtain ⟨t⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨t.val, t.property⟩

-- 读法：`outerArity` 的取值由 `Fintype.card {i // (G.src.symm (.inl i)).1 = v} + Fintype.card {i // (G.dst.symm (.inl i)).1 = v}` 给出。
private def outerArity (v : G.V) :=
  Fintype.card {i // (G.src.symm (.inl i)).1 = v} +
  Fintype.card {i // (G.dst.symm (.inl i)).1 = v}

omit [Field F] in
-- 读法：`G.arity v` 等于 `G.outerArity v + ∑ w, (G.width v w + G.width w v)`。
private theorem arity_width (v : G.V) :
    G.arity v = G.outerArity v + ∑ w, (G.width v w + G.width w v) := by
  have row : (∑ w, G.width v w) = ∑ e, if G.source e = v then 1 else 0 := by
    simp only [width, Fintype.card_subtype, card_filter]
    rw [sum_comm]
    simp [and_comm (a := G.source _ = v), ite_and]
  have col : (∑ w, G.width w v) = ∑ e, if G.target e = v then 1 else 0 := by
    simp only [width, Fintype.card_subtype, card_filter]
    rw [sum_comm]
    simp [ite_and]
  rw [sum_add_distrib, row, col, ← G.degree, Fintype.card_subtype, card_filter, Fintype.sum_sum_type]
  simp only [outerArity, Fintype.card_subtype, card_filter, Fintype.sum_sum_type, station,
    Sum.elim_inl, Sum.elim_inr, source, target]
  ac_rfl

-- 读法：`(G.pad R).arity v` 等于 `G.outerArity v + ∑ w, (padWidth R (G.width v w) + padWidth R (G.width w v))`。这里调用 `sum_congr`。
private theorem arity_pad_eq (R : ℕ) (v : G.V) :
    (G.pad R).arity v = G.outerArity v +
      ∑ w, (padWidth R (G.width v w) + padWidth R (G.width w v)) := by
  rw [arity_width]
  congr 1
  apply sum_congr rfl
  intro w _
  rw [width_pad, width_pad]

-- 读法：`G.arity v` 不超过 `(G.pad R).arity v`。这里调用 `Nat.add_le_add_left`。
theorem arity_le_pad (R : ℕ) (v : G.V) : G.arity v ≤ (G.pad R).arity v := by
  rw [arity_pad_eq, arity_width]
  exact Nat.add_le_add_left (sum_le_sum fun w _ =>
    Nat.add_le_add (le_padWidth R (G.width v w)) (le_padWidth R (G.width w v))) _

-- 读法：`(G.pad R).arity v` 不超过 `G.arity v + 2 * R * Fintype.card {w // 0 < G.width v w ∨ 0 < G.width w v}`。这里调用 `Nat.add_le_add_left`。
theorem arity_pad (R : ℕ) (v : G.V) :
    (G.pad R).arity v ≤ G.arity v + 2 * R * Fintype.card {w // 0 < G.width v w ∨ 0 < G.width w v} := by
  rw [arity_pad_eq, arity_width, Fintype.card_subtype, card_filter, mul_sum, add_assoc,
    ← sum_add_distrib]
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro w _
  split_ifs with hw
  · have := padWidth_le R (G.width v w)
    have := padWidth_le R (G.width w v)
    omega
  · have h₁ : G.width v w = 0 := by omega
    have h₂ : G.width w v = 0 := by omega
    simp [h₁, h₂]

-- 读法：`(G.pad R).arity v` 不超过 `2 * G.arity v`。按 `G.width v w = 0` 成立与否分情况。
theorem arity_pad_le_twice (R : ℕ) (h : ∀ v w, 0 < G.width v w → R ≤ G.width v w) (v : G.V) :
    (G.pad R).arity v ≤ 2 * G.arity v := by
  have hw (v w : G.V) : padWidth R (G.width v w) ≤ 2 * G.width v w := by
    by_cases hz : G.width v w = 0
    · simp [hz]
    · have := h v w (Nat.pos_of_ne_zero hz)
      have := padWidth_le R (G.width v w)
      omega
  rw [arity_pad_eq, arity_width, mul_add, mul_sum]
  apply Nat.add_le_add (by omega)
  exact sum_le_sum fun w _ => by rw [mul_add]; exact Nat.add_le_add (hw v w) (hw w v)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end
