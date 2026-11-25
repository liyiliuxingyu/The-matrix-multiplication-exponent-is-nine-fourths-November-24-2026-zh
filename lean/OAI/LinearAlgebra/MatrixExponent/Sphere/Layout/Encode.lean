-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement

/-!
# 编码有限的内部状态

每条线束都有自己的有限字母表和单射的二进制编码。局部表在无效编码上取零。因此，即使字母表为空或线束宽度为零，也能保持收缩值。

**英文原文**

Encoding finite internal states

A bundle has its own finite alphabet and an injective binary code.
The local table gives zero to invalid codes. This preserves the
contraction even when an alphabet is empty or a bundle has width zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset

-- 读法：`binaryCode` 的取值由 `Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))` 给出。
def binaryCode (X : Type) [Fintype X] (n : ℕ) (h : Fintype.card X ≤ 2 ^ n) :
    X ↪ (Fin n → Bool) := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

-- 读法：结构的字段包括 `V`、`E`、`state`、`width`、`code`。
structure Bundled (F : Type) (a b : Wire) where
  V : Type
  E : Type
  [fv : Fintype V]
  [fe : Fintype E]
  state : E → Type
  [fs : ∀ e, Fintype (state e)]
  width : E → ℕ
  code : ∀ e, state e ↪ (Fin (width e) → Bool)
  src : E → V
  dst : E → V
  left : slots a → V
  right : slots b → V
  station : V → Val a → Val b → (∀ e, state e) → F
  locality : ∀ v x y z x' y' z',
    (∀ i, left i = v → bits a x i = bits a x' i) →
    (∀ i, right i = v → bits b y i = bits b y' i) →
    (∀ e, src e = v ∨ dst e = v → z e = z' e) →
    station v x y z = station v x' y' z'

attribute [instance] Bundled.fv Bundled.fe Bundled.fs

namespace Bundled
variable {F : Type} {a b : Wire} (G : Bundled F a b)

-- 读法：在后续公式中，`Bit` 是 `Σ e, Fin (G.width e)` 的缩写。
abbrev Bit := Σ e, Fin (G.width e)
-- 读法：在后续公式中，`State` 是 `∀ e, G.state e` 的缩写。
abbrev State := ∀ e, G.state e

-- 读法：`pack` 的取值由 `G.code i.1 (s i.1) i.2` 给出。
def pack (s : G.State) (i : G.Bit) : Bool := G.code i.1 (s i.1) i.2

-- 读法：`G.pack` 是单射。用函数外延性比较等号两侧在 `e` 处的取值。
theorem pack_injective : Function.Injective G.pack := by
  intro x y h
  funext e
  exact (G.code e).injective (funext fun k => congrFun h ⟨e, k⟩)

-- 读法：`eval` 的取值由 `∑ s : G.State, ∏ v, G.station v x y s` 给出。
def eval [Field F] (x : Val a) (y : Val b) := ∑ s : G.State, ∏ v, G.station v x y s

-- 读法：`incoming` 的取值由 `Sum.elim G.left (fun i => G.src i.1)` 给出。
def incoming : slots a ⊕ G.Bit → G.V := Sum.elim G.left (fun i => G.src i.1)
-- 读法：`outgoing` 的取值由 `Sum.elim G.right (fun i => G.dst i.1)` 给出。
def outgoing : slots b ⊕ G.Bit → G.V := Sum.elim G.right (fun i => G.dst i.1)

-- 读法：`Valid` 表示以下条件：`(∀ i, G.src i.1 = v → G.pack s i = x (.inr i))` 与 `(∀ i, G.dst i.1 = v → G.pack s i = y (.inr i))` 同时成立。
private def Valid (v : G.V) (x : slots a ⊕ G.Bit → Bool) (y : slots b ⊕ G.Bit → Bool)
    (s : G.State) : Prop :=
  (∀ i, G.src i.1 = v → G.pack s i = x (.inr i)) ∧
  (∀ i, G.dst i.1 = v → G.pack s i = y (.inr i))

variable [Field F]

-- 读法：`weight` 的取值由 `if h : ∃ s, G.Valid v x y s then G.station v ((bits a).symm (x ∘ .inl)) ((bits b).symm (y ∘ .inl)) h.choose else 0` 给出。
def weight (v : G.V) (x : slots a ⊕ G.Bit → Bool) (y : slots b ⊕ G.Bit → Bool) : F :=
  if h : ∃ s, G.Valid v x y s then
    G.station v ((bits a).symm (x ∘ .inl)) ((bits b).symm (y ∘ .inl)) h.choose
  else 0

-- 读法：`G.weight v x y` 等于 `G.station v ((bits a).symm (x ∘ .inl)) ((bits b).symm (y ∘ .inl)) s`。这里调用 `G.locality`。
private theorem weight_read (v : G.V) {x y} {s : G.State} (h : G.Valid v x y s) :
    G.weight v x y = G.station v ((bits a).symm (x ∘ .inl)) ((bits b).symm (y ∘ .inl)) s := by
  have hs : ∃ s, G.Valid v x y s := ⟨s, h⟩
  rw [weight, dite_eq_left hs]
  apply G.locality _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  intro e he
  apply (G.code e).injective
  funext i
  rcases he with he | he
  · exact (hs.choose_spec.1 ⟨e, i⟩ he).trans (h.1 ⟨e, i⟩ he).symm
  · exact (hs.choose_spec.2 ⟨e, i⟩ he).trans (h.2 ⟨e, i⟩ he).symm

-- 读法：要证明的命题是 `Diagram.Local G.incoming G.outgoing G.weight`。按 `∃ s, G.Valid v x y s` 成立与否分情况。
theorem local_weight : Diagram.Local G.incoming G.outgoing G.weight := by
  intro v x y x' y' hx hy
  have he (s : G.State) : G.Valid v x y s ↔ G.Valid v x' y' s := by
    constructor
    · exact fun h => ⟨fun i hi => (h.1 i hi).trans (hx (.inr i) hi),
        fun i hi => (h.2 i hi).trans (hy (.inr i) hi)⟩
    · exact fun h => ⟨fun i hi => (h.1 i hi).trans (hx (.inr i) hi).symm,
        fun i hi => (h.2 i hi).trans (hy (.inr i) hi).symm⟩
  by_cases h : ∃ s, G.Valid v x y s
  · obtain ⟨s, hs⟩ := h
    rw [G.weight_read v hs, G.weight_read v ((he s).mp hs)]
    apply G.locality
    · simpa [incoming] using fun i hi => hx (.inl i) hi
    · simpa [outgoing] using fun i hi => hy (.inl i) hi
    · exact fun _ _ => rfl
  · simp only [weight, ← he, dite_eq_right h]

-- 读法：在后续公式中，`diagram` 是 `Diagram.ofLocal G.incoming G.outgoing G.weight` 的缩写。
abbrev diagram := Diagram.ofLocal G.incoming G.outgoing G.weight

-- 读法：`G.diagram.source e` 等于 `G.src e.1`。两端由定义化简为同一项。
theorem source (e : G.Bit) : G.diagram.source e = G.src e.1 := rfl

-- 读法：`G.diagram.target e` 等于 `G.dst e.1`。两端由定义化简为同一项。
theorem target (e : G.Bit) : G.diagram.target e = G.dst e.1 := rfl

-- 读法：`G.diagram.vertex x y (G.pack s) v` 等于 `G.station v x y s`。
theorem vertex (x : Val a) (y : Val b) (s : G.State) (v : G.V) :
    G.diagram.vertex x y (G.pack s) v = G.station v x y s := by
  rw [Diagram.vertex_ofLocal _ _ _ G.local_weight, G.weight_read v (s := s)]
  · simp [Function.comp_def]
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

-- 读法：结论为 `∏ v : G.V, G.diagram.vertex x y z v = 0`。
theorem invalid (x : Val a) (y : Val b) (z : G.Bit → Bool) (h : z ∉ Set.range G.pack) :
    ∏ v : G.V, G.diagram.vertex x y z v = 0 := by
  by_contra! hn
  have he (e : G.E) : ∃ t, ∀ k, G.code e t k = z ⟨e, k⟩ := by
    have hv := prod_ne_zero_iff.mp hn (G.src e) (mem_univ _)
    rw [Diagram.vertex_ofLocal _ _ _ G.local_weight, weight] at hv
    split_ifs at hv with hs
    · exact ⟨hs.choose e, fun k => hs.choose_spec.1 ⟨e, k⟩ rfl⟩
    · contradiction
  choose s hs using he
  exact h ⟨s, funext fun i => hs i.1 i.2⟩

-- 读法：`G.diagram.eval` 等于 `G.eval`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval_diagram : G.diagram.eval = G.eval := by
  funext x y
  unfold Diagram.eval
  symm
  calc
    G.eval x y = ∑ z ∈ univ.image G.pack, ∏ v : G.V, G.diagram.vertex x y z v := by
      rw [sum_image G.pack_injective.injOn]
      simp only [vertex, eval]
    _ = _ := sum_subset (subset_univ _) (fun z _ hz => G.invalid x y z (by simpa using hz))
    _ = _ := by congr!

omit [Field F] in
-- 读法：`Fintype.card {i : G.Bit // p i.1}` 等于 `∑ e, if p e then G.width e else 0`。这里调用 `sum_congr`。
theorem card_bits (p : G.E → Prop) [DecidablePred p] :
    Fintype.card {i : G.Bit // p i.1} = ∑ e, if p e then G.width e else 0 := by
  rw [Fintype.card_subtype, card_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro e _
  by_cases he : p e <;> simp [he]

omit [Field F] in
-- 读法：`Fintype.card {i : I ⊕ G.Bit // Sum.elim p (fun j => q j.1) i = v}` 等于 `Fintype.card {i // p i = v} + ∑ e, if q e = v then G.width e else 0`。
private theorem card_end {I : Type} [Fintype I] (p : I → G.V) (q : G.E → G.V) (v : G.V) :
    Fintype.card {i : I ⊕ G.Bit // Sum.elim p (fun j => q j.1) i = v} =
      Fintype.card {i // p i = v} + ∑ e, if q e = v then G.width e else 0 := by
  rw [← G.card_bits (fun e => q e = v)]
  simp only [Fintype.card_subtype, card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr!

-- 读法：`arity` 的结果类型为 `ℕ`。
def arity (v : G.V) : ℕ :=
  Fintype.card {i // G.left i = v} + Fintype.card {i // G.right i = v} +
    (∑ e, if G.src e = v then G.width e else 0) + (∑ e, if G.dst e = v then G.width e else 0)

-- 读法：`G.diagram.arity v` 等于 `G.arity v`。
theorem arity_diagram (v : G.V) : G.diagram.arity v = G.arity v := by
  rw [Diagram.arity_ofLocal]
  unfold incoming outgoing arity
  rw [G.card_end, G.card_end]
  omega

-- 读法：`u` 整除 `Fintype.card {i : G.diagram.E // G.diagram.source i = v ∧ G.diagram.target i = w}`。这里调用 `dvd_sum`。
theorem divisible (v w : G.V) (u : ℕ) (h : ∀ e, G.src e = v → G.dst e = w → u ∣ G.width e) :
    u ∣ Fintype.card {i : G.diagram.E // G.diagram.source i = v ∧ G.diagram.target i = w} := by
  rw [show Fintype.card {i : G.diagram.E // G.diagram.source i = v ∧ G.diagram.target i = w} =
    ∑ e, if G.src e = v ∧ G.dst e = w then G.width e else 0 from
      G.card_bits (fun e => G.src e = v ∧ G.dst e = w)]
  apply dvd_sum
  intro e _
  split_ifs with he
  · exact h e he.1 he.2
  · exact dvd_zero _

end Bundled
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
