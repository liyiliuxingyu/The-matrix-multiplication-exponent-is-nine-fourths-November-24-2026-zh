-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Pruned
import Mathlib.Data.List.NodupEquivFin
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing

/-!
# 布线后的线束关联次数

**英文原文**

Number of bundle incidences after routing
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset
variable {F V I : Type} [Field F] {a b : Wire} {d : ℕ}

-- 读法：用字段 `V`、`E`、`state`、`width` 构造 `Bundled F .unit .unit`。
/-- 令每条线束的宽度均为一，元数估计即化为度数估计。

英文原文：A unit width on every bundle specializes the arity estimates to degree.
-/
private abbrev thin (G : Bundled F a b) : Bundled F .unit .unit where
  V := G.V
  E := G.E
  state _ := Unit
  width _ := 1
  code _ := binaryCode _ _ (by simp)
  src := G.src
  dst := G.dst
  left := Empty.elim
  right := Empty.elim
  station _ _ _ _ := 1
  locality _ _ _ _ _ _ _ _ _ _ := rfl

-- 读法：`(thin G).arity v` 等于 `G.degree v`。
private theorem thin_arity (G : Bundled F a b) (v : G.V) : (thin G).arity v = G.degree v := by
  simp [Bundled.arity, Bundled.degree, thin]

namespace Fanout
variable {G : Bundled F a b} {T : Trie V d} (H : Fanout G T I)

-- 读法：在后续公式中，`unitFan` 是 `⟨H.site, H.one, H.near, H.group⟩` 的缩写。
private abbrev unitFan : Fanout (thin G) T I :=
  ⟨H.site, H.one, H.near, H.group⟩

-- 读法：`H.route.net.degree v` 等于 `H.unitFan.route.net.arity v`。
private theorem fan_arity (v : Node G.V d) : H.route.net.degree v = H.unitFan.route.net.arity v := by
  rw [← thin_arity]
  unfold Bundled.arity
  rfl

-- 读法：`H.route.net.degree v` 不超过 `2 * k`。对 `v` 分类讨论。
theorem fan_degree {k : ℕ} (hk : ∀ v, G.degree v ≤ k) (v : Node G.V d) :
    H.route.net.degree v ≤ 2 * k := by
  rw [fan_arity]
  cases v with
  | inl v => rw [Routes.old_arity, thin_arity]; have := hk v; omega
  | inr v =>
    refine (H.unitFan.relay_le v).trans ?_
    rw [thin_arity]
    exact Nat.mul_le_mul_left 2 (hk _)

end Fanout
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# 具有指定有序站点表的图式

局部计算规则只能读取两个外部比特串和两组线束字列表。关联双射在两端都保持线束偏移量。

**英文原文**

Diagrams with prescribed ordered station tables

Local recipes see only the two exterior strings and two lists of bundle
words. The incidence bijections preserve bundle offsets at both ends.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Transcript Finset Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

variable {F : Type} {a b : Wire}

-- 读法：结构的字段包括 `left`、`right`、`recipe`。
structure Drawing (G : Bundled F a b) where
  left : Side G.left G.src
  right : Side G.right G.dst
  recipe : G.V → Recipe F

namespace Drawing
variable {G : Bundled F a b} (D : Drawing G)

-- 读法：在后续公式中，`front` 是 `D.left.panel G.width v` 的缩写。
abbrev front (v : G.V) := D.left.panel G.width v
-- 读法：在后续公式中，`back` 是 `D.right.panel G.width v` 的缩写。
abbrev back (v : G.V) := D.right.panel G.width v

-- 读法：用字段 `V`、`E`、`table`、`src` 构造 `Diagram F a b`。
abbrev diagram : Diagram F a b where
  V := G.V
  E := G.Bit
  table v := (D.front v).table (D.back v) (D.recipe v)
  src := D.left.ports G.width
  dst := D.right.ports G.width

-- 读法：`D.diagram.source e` 等于 `G.src e.1`。使用 `D.left.owner` 给出的结论。
theorem source (e : G.Bit) : D.diagram.source e = G.src e.1 := D.left.owner G.width (.inr e)
-- 读法：`D.diagram.target e` 等于 `G.dst e.1`。使用 `D.right.owner` 给出的结论。
theorem target (e : G.Bit) : D.diagram.target e = G.dst e.1 := D.right.owner G.width (.inr e)

-- 读法：`Packing.portEnd D.diagram q` 等于 `Sum.elim G.left G.right q`。对 `q` 分类讨论。
theorem exterior (q : slots a ⊕ slots b) :
    Packing.portEnd D.diagram q = Sum.elim G.left G.right q := by
  cases q with
  | inl i => exact D.left.owner G.width (.inl i)
  | inr i => exact D.right.owner G.width (.inl i)

-- 读法：`D.diagram.arity v` 等于 `G.arity v`。
theorem arity (v : G.V) : D.diagram.arity v = G.arity v := by
  change wd (D.left.panel G.width v).wire + wd (D.right.panel G.width v).wire = _
  rw [Side.wd_panel, Side.wd_panel, Bundled.arity]
  omega

-- 读法：`(D.front v).count + (D.back v).count` 等于 `G.degree v`。
theorem count (v : G.V) : (D.front v).count + (D.back v).count = G.degree v := by
  change D.left.inner.count v + D.right.inner.count v = _
  simp only [Enum.count_eq, Fintype.card_subtype, card_filter, Bundled.degree]

-- 读法：`D.diagram.vertex x y z v` 等于 `D.recipe v (D.left.view G.width v (bits a x) z) (D.right.view G.width v (bits b y) z)`。
theorem vertex (x : Val a) (y : Val b) (z : G.Bit → Bool) (v : G.V) :
    D.diagram.vertex x y z v =
      D.recipe v (D.left.view G.width v (bits a x) z) (D.right.view G.width v (bits b y) z) :=
  congrArg₂ (D.recipe v) (D.left.read G.width v (bits a x) z) (D.right.read G.width v (bits b y) z)

variable [Field F]

-- 读法：`D.diagram.eval` 等于 `G.eval`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval
    (valid : ∀ x y s v, D.diagram.vertex x y (G.pack s) v = G.station v x y s)
    (invalid : ∀ x y z, z ∉ Set.range G.pack → ∃ v, D.diagram.vertex x y z v = 0) :
    D.diagram.eval = G.eval := by
  rw [← Bundled.eval_diagram]
  funext x y
  apply sum_congr rfl
  intro z _
  by_cases h : z ∈ Set.range G.pack
  · obtain ⟨s, rfl⟩ := h
    exact prod_congr rfl fun v _ => (valid x y s v).trans (G.vertex x y s v).symm
  · obtain ⟨v, hv⟩ := invalid x y z h
    exact (prod_eq_zero (mem_univ v) hv).trans (G.invalid x y z h).symm

end Drawing
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 各物理站点两侧的连续块

**英文原文**

Consecutive blocks on both sides of each physical station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Transcript Finset Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

namespace Side
variable {X Y V E : Type} {f : X → V} {g : Y → V} {u v : E → V}
  (P : Side f u) (Q : Side g v) (w : E → ℕ) (a : V) (b : Bool)

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr ⟨i, j⟩`。
def remote : (P.panel w a).Port → Bool × Option (V × ℕ)
  | .inl _ => (b, none)
  | .inr ⟨i, j⟩ => (b, some (Q.peer w ⟨P.inner.get a i, j⟩))

-- 读法：`P.remote Q w a b j` 等于 `Diagram.advance (P.remote Q w a b i)`。
theorem adjacent (i j : (P.panel w a).Port)
    (h : (P.panel w a).number i + 1 = (P.panel w a).number j)
    (he : (P.panel w a).block i = (P.panel w a).block j) :
    P.remote Q w a b j = Diagram.advance (P.remote Q w a b i) := by
  rcases i with i | ⟨i, k⟩ <;> rcases j with j | ⟨j, l⟩
  · rfl
  · simp [Panel.block] at he
  · simp [Panel.block] at he
  · have hij : i = j := Fin.ext (Nat.succ.inj he)
    subst j
    rw [Panel.number_inner, Panel.number_inner] at h
    have hl : k.val + 1 = l.val := by dsimp only at h; omega
    obtain ⟨s, hs⟩ := Q.peer_offset w (P.inner.get a i)
    unfold remote
    simp only [hs, Diagram.advance, Option.map_some, Nat.add_assoc, hl]

end Side

namespace Drawing
variable {F : Type} {a b : Wire} {G : Bundled F a b} (D : Drawing G) (v : G.V)

-- 读法：在后续公式中，`Both` 是 `(D.front v).Port ⊕ (D.back v).Port` 的缩写。
private abbrev Both := (D.front v).Port ⊕ (D.back v).Port

-- 读法：`place` 的取值由 `((D.front v).port.symm.sumCongr (D.back v).port.symm).trans (positions (.pair (D.front v).wire (D.back v).wire))` 给出。
private def place : D.Both v ≃ Fin (D.diagram.arity v) :=
  ((D.front v).port.symm.sumCongr (D.back v).port.symm).trans
    (positions (.pair (D.front v).wire (D.back v).wire))

-- 读法：`(D.place v (.inl i)).val` 等于 `(D.front v).number i`。两端由定义化简为同一项。
private theorem left_val (i : (D.front v).Port) :
    (D.place v (.inl i)).val = (D.front v).number i := rfl

-- 读法：`(D.place v (.inr i)).val` 等于 `wd (D.front v).wire + (D.back v).number i`。两端由定义化简为同一项。
private theorem right_val (i : (D.back v).Port) :
    (D.place v (.inr i)).val = wd (D.front v).wire + (D.back v).number i := rfl

-- 读法：`D.diagram.peer v (D.place v (.inl i))` 等于 `D.left.remote D.right G.width v false i`。
private theorem left_peer (i : (D.front v).Port) :
    D.diagram.peer v (D.place v (.inl i)) = D.left.remote D.right G.width v false i := by
  let e := positions (.pair (D.front v).wire (D.back v).wire)
  change D.diagram.portPeer v (e.symm (e (.inl ((D.front v).port.symm i)))) = _
  rw [Equiv.symm_apply_apply]
  change (false, (D.left.ports G.width ⟨v, (D.front v).port.symm i⟩).elim (fun _ => none)
    (fun j => some (D.right.peer G.width j))) = _
  rcases i with i | ⟨i, k⟩
  · rw [D.left.ports_ext G.width v i]; rfl
  · rw [D.left.ports_inner G.width v i k]; rfl

-- 读法：`D.diagram.peer v (D.place v (.inr i))` 等于 `D.right.remote D.left G.width v true i`。
private theorem right_peer (i : (D.back v).Port) :
    D.diagram.peer v (D.place v (.inr i)) = D.right.remote D.left G.width v true i := by
  let e := positions (.pair (D.front v).wire (D.back v).wire)
  change D.diagram.portPeer v (e.symm (e (.inr ((D.back v).port.symm i)))) = _
  rw [Equiv.symm_apply_apply]
  change (true, (D.right.ports G.width ⟨v, (D.back v).port.symm i⟩).elim (fun _ => none)
    (fun j => some (D.left.peer G.width j))) = _
  rcases i with i | ⟨i, k⟩
  · rw [D.right.ports_ext G.width v i]; rfl
  · rw [D.right.ports_inner G.width v i k]; rfl

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr i`。
private def block : D.Both v → ℕ
  | .inl i => (D.front v).block i
  | .inr i => (D.front v).count + 1 + (D.back v).block i

-- 读法：`D.block v i` 严格小于 `G.degree v + 2`。对 `i` 分类讨论。
private theorem block_lt (i : D.Both v) : D.block v i < G.degree v + 2 := by
  have hc := D.count v
  have ef : (D.front v).count = D.left.inner.count v := rfl
  cases i with
  | inl i => have := (D.front v).block_le i; unfold block; dsimp only; omega
  | inr i => have := (D.back v).block_le i; unfold block; dsimp only; omega

-- 读法：`D.block v i` 不超过 `D.block v j`。这里调用 `D.front`。
private theorem block_mono (i j : D.Both v) (h : (D.place v i).val ≤ (D.place v j).val) :
    D.block v i ≤ D.block v j := by
  have ef : (D.front v).count = D.left.inner.count v := rfl
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [left_val, right_val] at h
  all_goals simp only [block]
  · exact (D.front v).monotone i j h
  · have := (D.front v).block_le i; omega
  · have : (D.front v).number j < wd (D.front v).wire := Fin.isLt _
    omega
  · exact Nat.add_le_add_left ((D.back v).monotone i j (by omega)) _

-- 读法：`D.diagram.peer v (D.place v j)` 等于 `Diagram.advance (D.diagram.peer v (D.place v i))`。这里调用 `D.left.adjacent`。
private theorem block_next (i j : D.Both v)
    (h : (D.place v i).val + 1 = (D.place v j).val) (he : D.block v i = D.block v j) :
    D.diagram.peer v (D.place v j) = Diagram.advance (D.diagram.peer v (D.place v i)) := by
  have ef : (D.front v).count = D.left.inner.count v := rfl
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [block] at he
  · rw [left_peer, left_peer]
    exact D.left.adjacent D.right _ _ _ i j h he
  · have := (D.front v).block_le i; omega
  · have := (D.front v).block_le j; omega
  · rw [right_peer, right_peer]
    rw [right_val, right_val] at h
    apply D.right.adjacent D.left
    · exact Nat.add_left_cancel (by rwa [Nat.add_assoc] at h)
    · exact Nat.add_left_cancel he

-- 读法：要证明的命题是 `D.diagram.PortOrder R`。这里调用 `D.block_mono`。
theorem order {R : ℕ} (hR : ∀ v, G.degree v + 2 ≤ R) : D.diagram.PortOrder R := by
  intro v
  let block (i : Fin (D.diagram.arity v)) : Fin R :=
    ⟨D.block v ((D.place v).symm i), (D.block_lt v _).trans_le (hR v)⟩
  refine ⟨block, ?_, ?_⟩
  · intro i j h
    apply D.block_mono
    simpa only [Equiv.apply_symm_apply] using (show i.val ≤ j.val from h)
  · intro i j h he
    obtain ⟨i, rfl⟩ := (D.place v).surjective i
    obtain ⟨j, rfl⟩ := (D.place v).surjective j
    exact D.block_next v i j h (by simpa [block] using congrArg Fin.val he)

end Drawing
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 用线束自身的有限字母表解码

**英文原文**

Decoding a bundle with its own finite alphabet
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

-- 读法：在后续公式中，`Decoder` 是 `List Bool → Option α` 的缩写。
abbrev Decoder (α : Type) := List Bool → Option α

variable {α β : Type}

-- 读法：`decode` 的取值由 `Function.extend (fun x => List.ofFn (c x)) (fun x => some (tag x)) (fun _ => none)` 给出。
def decode (X : Type) (n : ℕ) (c : X ↪ (Fin n → Bool)) (tag : X → α) : Decoder α :=
  Function.extend (fun x => List.ofFn (c x)) (fun x => some (tag x)) (fun _ => none)

variable {X : Type} {n : ℕ} (c : X ↪ (Fin n → Bool)) (tag : X → α)

-- 读法：`decode X n c tag (List.ofFn (c x))` 等于 `some (tag x)`。
theorem decode_good (x : X) : decode X n c tag (List.ofFn (c x)) = some (tag x) :=
  Function.Injective.extend_apply
    (show Function.Injective (fun x => List.ofFn (c x)) from List.ofFn_injective.comp c.injective) _ _ x

-- 读法：`decode X n c tag x` 等于 `none`。
theorem decode_none (x : List Bool) (h : ¬ ∃ j, List.ofFn (c j) = x) :
    decode X n c tag x = none := by simp [decode, Function.extend, h]

-- 读法：输入 `x` 时返回 `(D x).map f`。
def Decoder.map (f : α → β) (D : Decoder α) : Decoder β := fun x => (D x).map f

-- 读法：`decode X n c (f ∘ tag)` 等于 `(decode X n c tag).map f`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem decode_comp (f : α → β) : decode X n c (f ∘ tag) = (decode X n c tag).map f := by
  funext x
  by_cases h : ∃ j, List.ofFn (c j) = x
  · obtain ⟨j, rfl⟩ := h
    simp [Decoder.map, decode_good]
  · simp [Decoder.map, decode_none _ _ _ h]

-- 读法：当 `h : i.val < n` 成立时取 `x ⟨i.val, h⟩`，否则取 `false`。
def padBits (u n : ℕ) (x : Fin n → Bool) : Fin (Diagram.padWidth u n) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

-- 读法：`(padBits u n)` 是单射。用函数外延性比较等号两侧在 `i` 处的取值。
theorem padBits_injective (u n : ℕ) : Function.Injective (padBits u n) := by
  intro x y h
  funext i
  simpa [padBits] using congrFun h (Fin.castLE (Diagram.le_padWidth u n) i)

-- 读法：`Decoder.pad` 的取值由 `Function.extend (fun x => List.ofFn (padBits u n x)) (fun x => D (List.ofFn x)) (fun _ => none)` 给出。
def Decoder.pad (u n : ℕ) (D : Decoder α) : Decoder α :=
  Function.extend (fun x => List.ofFn (padBits u n x)) (fun x => D (List.ofFn x)) (fun _ => none)

-- 读法：`decode _ _ ((G.pad u).code e) tag` 等于 `Decoder.pad u (G.width e) (decode _ _ (G.code e) tag)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem decode_pad {F : Type} {a b : Wire} (G : Bundled F a b) (e : G.E) (u : ℕ)
    (tag : G.state e → α) :
    decode _ _ ((G.pad u).code e) tag = Decoder.pad u (G.width e) (decode _ _ (G.code e) tag) := by
  let w := G.width e
  have hp (s : G.state e) : (G.pad u).code e s = padBits u w (G.code e s) := rfl
  have hi : Function.Injective (fun z => List.ofFn (padBits u w z)) :=
    List.ofFn_injective.comp (padBits_injective u w)
  funext x
  by_cases h : ∃ z, List.ofFn (padBits u w z) = x
  · obtain ⟨z, rfl⟩ := h
    rw [Decoder.pad, hi.extend_apply]
    by_cases hz : ∃ s, G.code e s = z
    -- 推导：从 `hz` 中取出 `s, rfl`。
    · obtain ⟨s, rfl⟩ := hz
      rw [← hp, decode_good, decode_good]
    · rw [decode_none, decode_none]
      · rintro ⟨s, hs⟩; exact hz ⟨s, List.ofFn_injective hs⟩
      · rintro ⟨s, hs⟩; exact hz ⟨s, hi hs⟩
  · rw [decode_none _ _ _ (fun ⟨s, hs⟩ => h ⟨G.code e s, hs⟩)]
    simp [Decoder.pad, Function.extend, show ¬ ∃ z, List.ofFn (padBits u (G.width e) z) = x from h]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 局部指令序列

脚本提供外部顺序、关联操作数列表以及作用在解码后符号上的运算。实际生成的计算规则只以局部线束偏移量来标识操作数。每个源端都会检查自身的全部线束字，包括该运算未使用的字。

**英文原文**

Local scripts

A script supplies the exterior order, a list of incident operands and
an operation on their decoded symbols. The rendered recipe names
operands by local bundle offsets only. Every source checks its own
bundle words, including those omitted by the operation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Classical Finset OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

-- 读法：在后续公式中，`Program` 是 `List Bool → List Bool → List α → F` 的缩写。
abbrev Program (F α : Type) := List Bool → List Bool → List α → F
-- 读法：在后续公式中，`Call` 是 `Bool × ℕ × Decoder α` 的缩写。
abbrev Call (α : Type) := Bool × ℕ × Decoder α

variable {F α V X : Type} {a b : Wire} {G : Bundled F a b}

-- 读法：结构的字段包括 `ports`、`nodup`、`mem`。
structure Exterior (f : X → V) where
  ports : V → List X
  nodup : ∀ v, (ports v).Nodup
  mem : ∀ v i, i ∈ ports v ↔ f i = v

variable {f : X → V}

-- 读法：用字段 `count`、`elem` 构造 `Enum f`。
def Exterior.enum (B : Exterior f) : Enum f where
  count v := (B.ports v).length
  elem v := (List.Nodup.getEquiv _ (B.nodup v)).trans (Equiv.subtypeEquivRight (B.mem v))

-- 读法：`List.ofFn (fun i => x (B.enum.get v i))` 等于 `(B.ports v).map x`。
theorem Exterior.values (B : Exterior f) (v : V) (x : X → Bool) :
    List.ofFn (fun i => x (B.enum.get v i)) = (B.ports v).map x := by
  change List.ofFn (x ∘ (B.ports v).get) = _
  rw [← List.map_ofFn, List.ofFn_get]

-- 读法：结构的字段包括 `left`、`right`、`tag`、`program`、`reads`。
structure Script (G : Bundled F a b) (α : Type) where
  left : Exterior G.left
  right : Exterior G.right
  tag : ∀ e, G.state e ↪ α
  program : G.V → Program F α
  reads : G.V → List G.E
  incident : ∀ v e, e ∈ reads v → G.src e = v ∨ G.dst e = v
  run : ∀ v x y z, G.station v x y z =
    program v ((left.ports v).map (bits a x)) ((right.ports v).map (bits b y))
      ((reads v).map fun e => tag e (z e))

-- 读法：`Call.read` 的取值由 `t.2.2 (((if t.1 then y else x).2[t.2.1]?).getD [])` 给出。
def Call.read (t : Call α) (x y : View) : Option α :=
  t.2.2 (((if t.1 then y else x).2[t.2.1]?).getD [])

-- 读法：当 `∀ c ∈ checks ++ reads, c.read x y ≠ none` 成立时取 `f x.1 y.1 (reads.filterMap (fun c => c.read x y))`，否则取 `0`。
def render [Zero F] (f : Program F α) (reads checks : List (Call α)) : Recipe F :=
  fun x y => if ∀ c ∈ checks ++ reads, c.read x y ≠ none then
    f x.1 y.1 (reads.filterMap (fun c => c.read x y)) else 0

namespace Script
variable (p : Script G α)

-- 读法：在后续公式中，`source` 是 `⟨p.left.enum, Enum.any G.src⟩` 的缩写。
abbrev source : Side G.left G.src := ⟨p.left.enum, Enum.any G.src⟩
-- 读法：在后续公式中，`target` 是 `⟨p.right.enum, Enum.any G.dst⟩` 的缩写。
abbrev target : Side G.right G.dst := ⟨p.right.enum, Enum.any G.dst⟩

-- 读法：`signal` 的取值由 `decode _ _ (G.code e) (p.tag e)` 给出。
def signal (e : G.E) := decode _ _ (G.code e) (p.tag e)

-- 读法：当 `G.src e = v` 成立时取 `(false, (p.source.inner.index e).val, p.signal e)`，否则取 `(true, (p.target.inner.index e).val, p.signal e)`。
def call (v : G.V) (e : G.E) : Call α :=
  if G.src e = v then (false, (p.source.inner.index e).val, p.signal e)
  else (true, (p.target.inner.index e).val, p.signal e)

-- 读法：`checks` 的取值由 `(univ.filter fun e => G.src e = v).toList` 给出。
def checks (v : G.V) := (univ.filter fun e => G.src e = v).toList

-- 读法：用字段 `left`、`right`、`recipe` 构造 `Drawing G`。
abbrev drawing [Field F] : Drawing G where
  left := p.source
  right := p.target
  recipe v := render (p.program v) ((p.reads v).map (p.call v))
    ((checks (G := G) v).map (p.call v))

-- 读法：`(((S.view w (f e) x s).2[(S.inner.index e).val]?).getD [])` 等于 `List.ofFn (fun i => s ⟨e, i⟩)`。
theorem read_side {X E V : Type} {l : X → V} {f : E → V} (S : Side l f)
    (w : E → ℕ) (x : X → Bool) (s : Side.Bit w → Bool) (e : E) :
    (((S.view w (f e) x s).2[(S.inner.index e).val]?).getD []) =
      List.ofFn (fun i => s ⟨e, i⟩) := by
  let q (e : E) := List.ofFn (fun i => s ⟨e, i⟩)
  change ((List.ofFn (fun j => q (S.inner.get (f e) j)))[(S.inner.index e).val]?).getD [] = q e
  simp

-- 读法：按 `G.src e = v` 成立与否分情况。
theorem read_call (v : G.V) (e : G.E) (h : G.src e = v ∨ G.dst e = v)
    (x : Val a) (y : Val b) (z : G.Bit → Bool) :
    (p.call v e).read (p.source.view G.width v (bits a x) z) (p.target.view G.width v (bits b y) z) =
      p.signal e (List.ofFn fun i => z ⟨e, i⟩) := by
  by_cases hs : G.src e = v
  · subst v
    simp only [call, ite_true, Call.read, Bool.false_eq_true, ite_false]
    rw [read_side]
  · have he := h.resolve_left hs
    subst v
    simp only [call, ite_eq_right hs, Call.read, ite_true]
    rw [read_side]

variable [Field F]

-- 读法：`p.drawing.diagram.vertex x y (G.pack s) v` 等于 `G.station v x y s`。
private theorem valid (x : Val a) (y : Val b) (s : G.State) (v : G.V) :
    p.drawing.diagram.vertex x y (G.pack s) v = G.station v x y s := by
  rw [Drawing.vertex, p.run]
  let l := p.source.view G.width v (bits a x) (G.pack s)
  let r := p.target.view G.width v (bits b y) (G.pack s)
  have h (e : G.E) (he : G.src e = v ∨ G.dst e = v) :
      (p.call v e).read l r = some (p.tag e (s e)) :=
    (p.read_call v e he _ _ _).trans (decode_good (G.code e) (p.tag e) (s e))
  have hv : ∀ c ∈ (checks (G := G) v).map (p.call v), c.read l r ≠ none := by
    simp only [List.forall_mem_map, checks, mem_toList, mem_filter, mem_univ, true_and]
    intro e he
    rw [h e (.inl he)]
    exact Option.some_ne_none _
  have hr (es : List G.E) (hs : es ⊆ p.reads v) :
      (es.map (p.call v)).filterMap (fun c => c.read l r) = es.map (fun e => p.tag e (s e)) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      rw [List.map_cons, List.filterMap_cons, h e (p.incident _ _ (hs (by simp)))]
      exact congrArg _ (ih (fun _ ht => hs (List.mem_cons_of_mem _ ht)))
  change render _ _ _ l r = _
  -- 推导：记下中间结论 `ha`：`∀ c ∈ (p.reads v).map (p.call v), c.read l r ≠ none`。
  have ha : ∀ c ∈ (p.reads v).map (p.call v), c.read l r ≠ none := by
    rw [List.forall_mem_map]
    intro e he
    rw [h e (p.incident _ _ he)]
    exact Option.some_ne_none _
  rw [render, ite_eq_left (List.forall_mem_append.mpr ⟨hv, ha⟩), hr _ (fun _ he => he)]
  exact congrArg₂ (fun a b => p.program v a b _) (p.left.values _ _) (p.right.values _ _)

-- 读法：存在 `v`，`p.drawing.diagram.vertex x y z v` 等于 `0`。这里调用 `ite_eq_right`。
private theorem invalid (x : Val a) (y : Val b) (z : G.Bit → Bool) (h : z ∉ Set.range G.pack) :
    ∃ v, p.drawing.diagram.vertex x y z v = 0 := by
  have he : ∃ e, ¬ ∃ t, List.ofFn (G.code e t) = List.ofFn (fun i => z ⟨e, i⟩) := by
    by_contra! hh
    choose s hs using hh
    exact h ⟨s, funext fun j => congrFun (List.ofFn_injective (hs j.1)) j.2⟩
  obtain ⟨e, he⟩ := he
  refine ⟨G.src e, ?_⟩
  rw [Drawing.vertex]
  apply ite_eq_right
  intro h'
  have hx := h' (p.call (G.src e) e) (List.mem_append_left _ (List.mem_map_of_mem (by simp [checks])))
  exact hx ((p.read_call (G.src e) e (.inl rfl) _ _ _).trans (decode_none _ _ _ he))

-- 读法：`p.drawing.diagram.eval` 等于 `G.eval`。使用 `p.drawing.eval` 给出的结论。
theorem eval : p.drawing.diagram.eval = G.eval := p.drawing.eval p.valid p.invalid

end Script
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 物理表名称的计数

从有限字典中选择有界数量的完整记录。指数依赖于读取的线束条数，与其比特宽度无关。该界对所有全局站点名及边名统一成立。

**英文原文**

Counting physical table names

Boundedly many whole records are selected from finite dictionaries.
The exponent depends on the number of bundles read, never on their bit
width. The bound is uniform over all global station and edge names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Finset Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

variable {α F : Type}

-- 读法：逐一匹配以下输入模式：`0`、`n + 1`。
def strings (s : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] ((s ×ˢ strings s n).image fun p => p.1 :: p.2)

-- 读法：`l` 属于 `strings s n`。对 `n` 作归纳，并把 `l` 保持为任意参数。
theorem mem_strings (s : Finset α) (n : ℕ) (l : List α)
    (hl : l.length ≤ n) (h : ∀ x ∈ l, x ∈ s) : l ∈ strings s n := by
  induction n generalizing l with
  | zero => simp [strings, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
  | succ n ih =>
    cases l with
    | nil => exact mem_insert_self _ _
    | cons x l =>
      apply mem_insert_of_mem
      refine mem_image.mpr ⟨(x, l), mem_product.mpr ⟨h x (by simp), ?_⟩, rfl⟩
      exact ih _ (Nat.succ_le_succ_iff.mp hl) (fun y hy => h _ (List.mem_cons_of_mem _ hy))

-- 读法：`(strings s n).card` 不超过 `(s.card + 1) ^ n`。对 `n` 作归纳。
theorem card_strings (s : Finset α) (n : ℕ) : (strings s n).card ≤ (s.card + 1) ^ n := by
  induction n with
  | zero => simp [strings]
  | succ n ih =>
    refine (card_insert_le _ _).trans ((Nat.add_le_add_right card_image_le _).trans ?_)
    rw [card_product, pow_succ', add_mul, one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.one_le_pow _ _ (by omega))

-- 读法：`Panel.ofList` 的取值由 `⟨e, xs.length, xs.get⟩` 给出。
def Panel.ofList (e : ℕ) (xs : List ℕ) : Panel := ⟨e, xs.length, xs.get⟩

-- 读法：`Panel.ofList p.ext (List.ofFn p.width)` 等于 `p`。对 `p` 分类讨论。
private theorem panel_roundtrip (p : Panel) : Panel.ofList p.ext (List.ofFn p.width) = p := by
  cases p with
  | mk e n f =>
    simp only [Panel.ofList, Panel.mk.injEq, true_and, List.length_ofFn]
    exact Function.hfunext (by simp) (fun i j h => by simp [Fin.val_eq_val_of_heq h])

-- 读法：`panels` 的取值由 `((range (u + 1)) ×ˢ strings (range (u + 1)) k).image fun p => Panel.ofList p.1 p.2` 给出。
def panels (k u : ℕ) : Finset Panel :=
  ((range (u + 1)) ×ˢ strings (range (u + 1)) k).image fun p => Panel.ofList p.1 p.2

-- 读法：`p` 属于 `panels k u`。这里调用 `mem_range.mpr`。
theorem panel_mem (p : Panel) {k u : ℕ} (hk : p.count ≤ k) (hu : wd p.wire ≤ u) :
    p ∈ panels k u := by
  rw [Panel.wd_wire] at hu
  refine mem_image.mpr ⟨(p.ext, List.ofFn p.width), mem_product.mpr ⟨mem_range.mpr (by omega),
    mem_strings _ _ _ (by simpa using hk) ?_⟩, panel_roundtrip p⟩
  rintro _ hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have h : p.width i ≤ p.size := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  exact mem_range.mpr (by omega)

-- 读法：`(panels k u).card` 不超过 `(u + 1) * (u + 2) ^ k`。这里调用 `Nat.mul_le_mul_left`。
theorem panel_count (k u : ℕ) : (panels k u).card ≤ (u + 1) * (u + 2) ^ k := by
  refine card_image_le.trans ?_
  rw [card_product, card_range]
  exact Nat.mul_le_mul_left _ (by simpa only [card_range] using card_strings (range (u + 1)) k)

-- 读法：`calls` 的取值由 `univ ×ˢ (range k ×ˢ d)` 给出。
def calls (d : Finset (Decoder α)) (k : ℕ) : Finset (Call α) :=
  univ ×ˢ (range k ×ˢ d)

-- 读法：`menu` 的结果类型为 `Finset (Table F)`。
def menu [Zero F] (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ) : Finset (Table F) :=
  let side := panels k u
  let args := strings (calls dec k) k
  ((side ×ˢ side) ×ˢ (ops ×ˢ (args ×ˢ args))).image fun s =>
    s.1.1.table s.1.2 (render s.2.1 s.2.2.1 s.2.2.2)

-- 读法：`(menu ops dec k u).card` 不超过 `((u + 1) * (u + 2) ^ k) ^ 2 * ops.card * ((2 * k * dec.card + 1) ^ k) ^ 2`。这里调用 `card_strings`。
theorem menu_count [Zero F] (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ) :
    (menu ops dec k u).card ≤ ((u + 1) * (u + 2) ^ k) ^ 2 * ops.card * ((2 * k * dec.card + 1) ^ k) ^ 2 := by
  have ha : (strings (calls dec k) k).card ≤ (2 * k * dec.card + 1) ^ k := by
    simpa [calls, mul_assoc] using card_strings (calls dec k) k
  refine card_image_le.trans ?_
  rw [card_product, card_product, card_product, card_product, ← pow_two, ← pow_two, ← mul_assoc]
  gcongr
  exact panel_count _ _

namespace Script
variable [Field F] {a b : Wire} {G : Bundled F a b} (s : Script G α)
  (ops : Finset (Program F α)) (dec : Finset (Decoder α)) (k u : ℕ)

-- 读法：`s.drawing.diagram.table v` 属于 `menu ops dec k u`。
theorem menu_mem (ho : ∀ v, s.program v ∈ ops) (hc : ∀ e, s.signal e ∈ dec)
    (hw : ∀ v, G.arity v ≤ u) (hv : ∀ v, G.degree v ≤ k) (hr : ∀ v, (s.reads v).length ≤ k)
    (v : G.V) : s.drawing.diagram.table v ∈ menu ops dec k u := by
  let L := s.drawing.front v
  let R := s.drawing.back v
  have hdeg : L.count + R.count ≤ k := (s.drawing.count v).trans_le (hv v)
  have hwidth : wd L.wire + wd R.wire ≤ u := (s.drawing.arity v).trans_le (hw v)
  have hm (e : G.E) (he : G.src e = v ∨ G.dst e = v) : s.call v e ∈ calls dec k := by
    unfold call calls
    split_ifs with h
    -- 推导：记下中间结论 `h'`：`(s.source.inner.index e).val < L.count`。
    · have h' : (s.source.inner.index e).val < L.count := by
        change _ < s.source.inner.count v
        rw [← h]
        exact Fin.isLt _
      exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_range.mpr (h'.trans_le (show L.count ≤ k by omega)), hc e⟩⟩
    · have h' : (s.target.inner.index e).val < R.count := by
        change _ < s.target.inner.count v
        rw [← he.resolve_left h]
        exact Fin.isLt _
      exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_range.mpr (h'.trans_le (show R.count ≤ k by omega)), hc e⟩⟩
  have hl (l : List G.E) (hn : l.length ≤ k) (hi : ∀ e ∈ l, G.src e = v ∨ G.dst e = v) :
      l.map (s.call v) ∈ strings (calls dec k) k := by
    refine mem_strings _ _ _ (by simpa using hn) ?_
    rintro _ h
    -- 推导：从 `List.mem_map.mp h` 中取出 `e, he, rfl`。
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact hm e (hi e he)
  let c := checks (G := G) v
  have hn : c.length ≤ k := by
    have : c.length = L.count := by
      change (univ.filter fun e => G.src e = v).toList.length = s.source.inner.count v
      rw [Enum.count_eq, Fintype.card_subtype, length_toList]
    omega
  refine mem_image.mpr ⟨((L, R), s.program v, (s.reads v).map (s.call v), c.map (s.call v)), ?_, rfl⟩
  simp only [mem_product]
  refine ⟨⟨panel_mem _ (by omega) (by omega), panel_mem _ (by omega) (by omega)⟩,
    ho v, hl _ (hr v) (s.incident v), hl _ hn ?_⟩
  simp only [c, checks, mem_toList, mem_filter, mem_univ, true_and]
  exact fun _ h => .inl h

end Script
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 全部中继表和枢纽表共用一个相等性程序

**英文原文**

One equality program suffices for all relay and hub tables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Finset

variable {F α V E X Y : Type} {a b : Wire} {G : Bundled F a b}

-- 读法：用字段 `ports`、`nodup`、`mem` 构造 `Exterior (Sum.inl ∘ f : X → V ⊕ Y)`。
def Exterior.lift {f : X → V} (P : Exterior f) (Y : Type) :
    Exterior (Sum.inl ∘ f : X → V ⊕ Y) where
  ports := Sum.elim P.ports (fun _ => [])
  nodup := by rintro (v|v); exact P.nodup v; simp
  mem := by rintro (v|v) i <;> simp [P.mem]

-- 读法：`pairs` 的取值由 `l.flatMap (fun p => [p.1, p.2])` 给出。
def pairs (l : List (E × E)) : List E := l.flatMap (fun p => [p.1, p.2])

-- 读法：`(pairs l).length` 等于 `2 * l.length`。对 `l` 作归纳。
theorem length_pairs (l : List (E × E)) : (pairs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => change (p.1 :: p.2 :: pairs l).length = _; simp [ih]; omega

-- 读法：`(∀ e ∈ pairs l, p e)` 与 `∀ t ∈ l, p t.1 ∧ p t.2` 等价。
theorem pairs_forall (l : List (E × E)) (p : E → Prop) :
    (∀ e ∈ pairs l, p e) ↔ ∀ t ∈ l, p t.1 ∧ p t.2 := by
  simp [pairs]
  grind

-- 读法：逐一匹配以下输入模式：`[]`、`[_]`、`x :: y :: l`。
def equalPairs : List α → Prop
  | [] => True
  | [_] => False
  | x :: y :: l => x = y ∧ equalPairs l

-- 读法：当 `equalPairs l` 成立时取 `1`，否则取 `0`。
def checkPairs [Field F] : Program F α := fun _ _ l => if equalPairs l then 1 else 0

-- 读法：`checkPairs x y ((pairs l).map f)` 等于 `if ∀ p ∈ l, f p.1 = f p.2 then (1 : F) else 0`。对 `l` 作归纳。
theorem checkPairs_eq [Field F] (f : E → α) (l : List (E × E)) (x y : List Bool) :
    checkPairs x y ((pairs l).map f) = if ∀ p ∈ l, f p.1 = f p.2 then (1 : F) else 0 := by
  have h : equalPairs ((pairs l).map f) ↔ ∀ p ∈ l, f p.1 = f p.2 := by
    induction l with
    | nil => simp [pairs, equalPairs]
    | cons p l ih =>
      change (f p.1 = f p.2 ∧ equalPairs ((pairs l).map f)) ↔ _
      rw [List.forall_mem_cons, ih]
  simp only [checkPairs, h]

namespace Script
variable (p : Script G α)

-- 读法：在后续公式中，`pad` 是 `⟨p.left, p.right, p.tag, p.program, p.reads, p.incident, p.run⟩` 的缩写。
abbrev pad (u : ℕ) : Script (G.pad u) α :=
  ⟨p.left, p.right, p.tag, p.program, p.reads, p.incident, p.run⟩

-- 读法：`(p.pad u).signal e` 等于 `Decoder.pad u (G.width e) (p.signal e)`。使用 `decode_pad` 给出的结论。
theorem signal_pad (u : ℕ) (e : G.E) :
    (p.pad u).signal e = Decoder.pad u (G.width e) (p.signal e) := decode_pad _ _ _ _

variable (R : Routes G Y)

-- 读法：当 `G.src e = v` 成立时取 `⟨e, 0⟩`，否则取 `⟨e, Fin.last _⟩`。
def endpoint (v : G.V) (e : G.E) : R.Hop :=
  if G.src e = v then ⟨e, 0⟩ else ⟨e, Fin.last _⟩

-- 读法：`R.src (endpoint R v e) = .inl v`、`R.dst (endpoint R v e) = .inl v` 至少有一项成立。
private theorem endpoint_incident (v : G.V) (e : G.E) (he : G.src e = v ∨ G.dst e = v) :
    R.src (endpoint R v e) = .inl v ∨ R.dst (endpoint R v e) = .inl v := by
  unfold endpoint
  split_ifs with h
  · exact .inl (by simp [Routes.src, h])
  · exact .inr (by simp [Routes.dst, he.resolve_left h])

-- 读法：`routeTag` 的取值由 `p.tag i.1` 给出。
private def routeTag (i : R.Hop) := p.tag i.1

-- 读法：`p.routeTag R (endpoint R v e) (s (endpoint R v e))` 等于 `p.tag e (R.read v s e)`。按 `G.src e = v` 成立与否分情况。
private theorem endpoint_tag (v : G.V) (s : R.Data) (e : G.E) :
    p.routeTag R (endpoint R v e) (s (endpoint R v e)) = p.tag e (R.read v s e) := by
  unfold Routes.read
  by_cases h : G.src e = v
  · rw [ite_eq_left h, show endpoint R v e = ⟨e, 0⟩ from ite_eq_left h]
    rfl
  · rw [ite_eq_right h, show endpoint R v e = ⟨e, Fin.last _⟩ from ite_eq_right h]
    rfl

-- 读法：在后续公式中，`Visit` 是 `Σ e, Fin (R.length e)` 的缩写。
abbrev Visit := Σ e, Fin (R.length e)
-- 读法：`visits` 的取值由 `univ.filter (fun i : Visit R => R.via i.1 i.2 = v)` 给出。
def visits (v : Y) := univ.filter (fun i : Visit R => R.via i.1 i.2 = v)
-- 读法：`ends` 的取值由 `(⟨i.1, i.2.castSucc⟩, ⟨i.1, i.2.succ⟩)` 给出。
def ends (i : Visit R) : R.Hop × R.Hop := (⟨i.1, i.2.castSucc⟩, ⟨i.1, i.2.succ⟩)
-- 读法：`matched` 的取值由 `(visits R v).toList.map (ends R)` 给出。
def matched (v : Y) := (visits R v).toList.map (ends R)

variable [Field F] [Fintype Y]

-- 读法：用字段 `left`、`right`、`tag`、`program` 构造 `Script R.net α`。
abbrev route : Script R.net α where
  left := p.left.lift Y
  right := p.right.lift Y
  tag := p.routeTag R
  program := Sum.elim p.program (fun _ => checkPairs)
  reads := Sum.elim (fun v => (p.reads v).map (endpoint R v)) (fun v => pairs (matched R v))
  incident := by
    rintro (v|v) e he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact endpoint_incident R v i (p.incident v i hi)
    · have h : ∀ e ∈ pairs (matched R v), R.src e = .inr v ∨ R.dst e = .inr v := by
        rw [pairs_forall]
        rintro _ hs
        obtain ⟨⟨i, j⟩, hi, rfl⟩ := List.mem_map.mp hs
        have hj := (mem_filter.mp (mem_toList.mp hi)).2
        exact ⟨.inr (by simp [ends, Routes.dst, hj]), .inl (by simp [ends, Routes.src, hj])⟩
      exact h e he
  run := by
    rintro (v|v) x y z
    · change G.station v x y (R.read v z) =
        p.program v _ _ (((p.reads v).map (endpoint R v)).map (fun e => p.routeTag R e (z e)))
      rw [p.run, List.map_map]
      simp only [Function.comp_def, endpoint_tag]
      rfl
    · change (if R.Valid v z then 1 else 0) =
        checkPairs [] [] ((pairs (matched R v)).map (fun e => p.routeTag R e (z e)))
      rw [checkPairs_eq]
      have he : (∀ i ∈ matched R v,
          p.routeTag R i.1 (z i.1) = p.routeTag R i.2 (z i.2)) ↔ R.Valid v z := by
        simp only [matched, List.forall_mem_map, mem_toList, visits, mem_filter, mem_univ, true_and,
          ends, routeTag, Routes.Valid, Sigma.forall]
        constructor
        · exact fun h e j hj => (p.tag e).injective (h e j hj)
        · exact fun h e j hj => congrArg (p.tag e) (h e j hj)
      simp only [he]

-- 读法：`(visits R v).card` 不超过 `R.net.degree (.inr v)`。这里调用 `sum_le_sum`。
private theorem visit_count (v : Y) : (visits R v).card ≤ R.net.degree (.inr v) := by
  unfold visits Bundled.degree
  refine le_trans ?_ (Nat.le_add_right _ _)
  rw [card_filter, Fintype.sum_sigma, Fintype.sum_sigma]
  apply sum_le_sum
  intro e _
  rw [Fin.sum_univ_succ]
  simp [Routes.src]

-- 读法：`((p.route R).reads (.inr v)).length` 不超过 `2 * R.net.degree (.inr v)`。这里调用 `Nat.mul_le_mul_left`。
theorem length_route (v : Y) : ((p.route R).reads (.inr v)).length ≤ 2 * R.net.degree (.inr v) := by
  change (pairs (matched R v)).length ≤ _
  rw [length_pairs, matched, List.length_map, length_toList]
  exact Nat.mul_le_mul_left _ (visit_count R v)

end Script
end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
一个站点读取一列普通键，其中同一个键可以多次读取。

**英文原文**

A station reads a list of ordinary keys; repeated reads are allowed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Surface.Stage

variable {F U X E V K : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}

-- 读法：结构的字段包括 `left`、`right`、`tag`、`label`、`reads`。
structure Rules (S : Sharing C a b Y) where
  left : Exterior S.left
  right : Exterior S.right
  tag : ∀ k, Y.state k ↪ Symbol (M * t)
  label : Place C → Label F (M * r) (M * t)
  reads : Place C → List K
  seen : ∀ i k, k ∈ reads i → k ∈ S.reads i
  run : ∀ i x y s a' b', (item C i).table (S.param x y s) a' b' =
    label i ((left.ports i).map (bits a x)) ((right.ports i).map (bits b y))
      ((reads i).map fun k => tag k (s k)) a'.val b'.val

namespace Rules
variable {S : Sharing C a b Y} (L : Rules S)
-- 读法：`signal` 的取值由 `decode _ _ (Y.code k) (L.tag k)` 给出。
def signal (k : K) := decode _ _ (Y.code k) (L.tag k)
end Rules

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
每个普通枢纽将每个可见键与对应的局部存储副本比较。

**英文原文**

An ordinary hub compares each visible key with its local storage copy.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Finset Classical

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y) (v : V)

-- 读法：`contacts` 的取值由 `univ.filter fun e => e.1 ∈ S.seen v ∧ (S.source e = .inr (.inl v) ∨ S.target e = .inr (.inl v))` 给出。
def contacts : Finset S.Edge :=
  univ.filter fun e => e.1 ∈ S.seen v ∧ (S.source e = .inr (.inl v) ∨ S.target e = .inr (.inl v))

-- 读法：`mates` 的取值由 `(i.val, ⟨i.val.1, .inl ⟨v, (mem_filter.mp i.property).2.1⟩⟩)` 给出。
def mates (i : ↥(contacts S v)) : S.Edge × S.Edge :=
  (i.val, ⟨i.val.1, .inl ⟨v, (mem_filter.mp i.property).2.1⟩⟩)

-- 读法：`hubReads` 的取值由 `pairs ((contacts S v).attach.toList.map (mates S v))` 给出。
def hubReads : List S.Edge := pairs ((contacts S v).attach.toList.map (mates S v))

omit [Field F] in
-- 读法：对每个 `e ∈ hubReads S v`，`S.source e = .inr (.inl v)`、`S.target e = .inr (.inl v)` 至少有一项成立。
theorem hub_meets : ∀ e ∈ hubReads S v, S.source e = .inr (.inl v) ∨ S.target e = .inr (.inl v) := by
  unfold hubReads
  rw [pairs_forall]
  rintro _ he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(mem_filter.mp i.property).2.2, .inl rfl⟩

-- 读法：`checkPairs x y ((hubReads S v).map (fun e => tag e.1 (z e)))` 等于 `if S.checks (.inr (.inl v)) z then (1 : F) else 0`。
theorem hub_eval {α : Type} (tag : ∀ k, Y.state k ↪ α) (z : S.State) (x y : List Bool) :
    checkPairs x y ((hubReads S v).map (fun e => tag e.1 (z e))) =
      if S.checks (.inr (.inl v)) z then (1 : F) else 0 := by
  rw [hubReads, checkPairs_eq]
  simp only [List.forall_mem_map, mem_toList, mem_attach, true_implies]
  congr 1
  apply propext
  constructor
  · intro h k j hj e he
    have hj' : v = j.val := Sum.inl.inj (Sum.inr.inj hj)
    subst v
    let i : ↥(contacts S j.val) := ⟨⟨k, e⟩, mem_filter.mpr ⟨mem_univ _, j.property, he⟩⟩
    exact (tag k).injective (h i)
  · intro h i
    obtain ⟨_, hs, he⟩ := mem_filter.mp i.property
    exact congrArg (tag i.val.1) (h _ ⟨v, hs⟩ rfl i.val.2 he)

-- 读法：`(hubReads S v).length` 不超过 `2 * S.base.degree (.inr (.inl v))`。这里调用 `Nat.mul_le_mul_left`。
theorem length_hubReads : (hubReads S v).length ≤ 2 * S.base.degree (.inr (.inl v)) := by
  rw [hubReads, length_pairs, List.length_map, length_toList, card_attach]
  apply Nat.mul_le_mul_left
  simp only [contacts, card_filter, Bundled.degree, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  split_ifs <;> grind

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
用于重新组装分块状态并对球面形式求值的局部操作。

**英文原文**

Local operations for reassembling chunk states and evaluating sphere forms.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Surface.Stage Classical

-- 读法：归纳构造子包括 `key`、`front`、`back`。
inductive Signal (M r t : ℕ) where
  | key : Symbol (M * t) → Signal M r t
  | front : Wedge r → Signal M r t
  | back : Wedge t → Signal M r t

variable {M r t : ℕ}

-- 读法：在后续公式中，`Args` 是 `List (Symbol (M * t)) × (Fin M → Wedge r) × (Fin M → Wedge t)` 的缩写。
abbrev Args (M r t : ℕ) := List (Symbol (M * t)) × (Fin M → Wedge r) × (Fin M → Wedge t)

-- 读法：`symbols` 的取值由 `u.1.map .key ++ List.ofFn (fun j => .front (u.2.1 j)) ++ List.ofFn (fun j => .back (u.2.2 j))` 给出。
def symbols (u : Args M r t) : List (Signal M r t) :=
  u.1.map .key ++ List.ofFn (fun j => .front (u.2.1 j)) ++ List.ofFn (fun j => .back (u.2.2 j))

-- 读法：`(symbols (M := M) (r := r) (t := t))` 是单射。
private theorem symbols_injective : Function.Injective (symbols (M := M) (r := r) (t := t)) := by
  rintro ⟨x, a, b⟩ ⟨x', a', b'⟩ h
  unfold symbols at h
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_ofFn, List.length_map] at hl
  obtain ⟨h, hb⟩ := List.append_inj h (by simp only [List.length_append, List.length_ofFn, List.length_map]; omega)
  obtain ⟨hx, ha⟩ := List.append_inj h (by simp only [List.length_map]; omega)
  have hx' := Function.Injective.list_map (fun _ _ he => Signal.key.inj he) hx
  have ha' : a = a' := funext fun i => Signal.front.inj (congrFun (List.ofFn_injective ha) i)
  have hb' : b = b' := funext fun i => Signal.back.inj (congrFun (List.ofFn_injective hb) i)
  exact Prod.ext hx' (Prod.ext ha' hb')

variable {F : Type} [Field F]

-- 读法：输入 `x y` 时返回 `Function.extend symbols (fun u => f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2)) (fun _ => 0)`。
def load (f : Label F (M * r) (M * t)) : Program F (Signal M r t) :=
  fun x y => Function.extend symbols
    (fun u => f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2)) (fun _ => 0)

-- 读法：`load f x y (symbols u)` 等于 `f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2)`。使用 `symbols_injective.extend_apply` 给出的结论。
theorem load_symbols (f : Label F (M * r) (M * t)) (x y : List Bool) (u : Args M r t) :
    load f x y (symbols u) = f x y u.1 (Chunk.join u.2.1) (Chunk.join u.2.2) :=
  symbols_injective.extend_apply _ _ u

-- 读法：`Signal.first` 的结果类型为 `Signal M r t → Wedge r`。
def Signal.first : Signal M r t → Wedge r
  | .front a => a
  | _ => ⟨[], by simp⟩

-- 读法：`Signal.second` 的结果类型为 `Signal M r t → Wedge t`。
def Signal.second : Signal M r t → Wedge t
  | .back a => a
  | _ => ⟨[], by simp⟩

-- 读法：输入 `_ _ u` 时返回 `wick fieldKernel (z.zipWith (fun v s => Surface.modes v (g s)) u).flatten`。
def chamber {α : Type} (g : α → Wedge r) (z : List F) : Program F α :=
  fun _ _ u => wick fieldKernel (z.zipWith (fun v s => Surface.modes v (g s)) u).flatten

-- 读法：`chamber g (l.map z) x y (l.map h)` 等于 `Layout.read z (g ∘ h) l`。对 `l` 作归纳。
theorem chamber_eval {α I : Type} (g : α → Wedge r) (h : I → α) (z : I → F)
    (l : List I) (x y : List Bool) :
    chamber g (l.map z) x y (l.map h) = Layout.read z (g ∘ h) l := by
  unfold chamber Layout.read
  congr 1
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.flatten_cons, List.flatMap_cons, ih,
      Function.comp_apply]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end
