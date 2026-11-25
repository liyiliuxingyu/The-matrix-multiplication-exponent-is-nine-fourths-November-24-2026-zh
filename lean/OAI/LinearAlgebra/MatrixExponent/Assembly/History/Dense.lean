-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Runs

/-!
# 解码收缩后站点的权重

原子参数或指向新站点的外露参数，或指向在站点内部求和消去的连线。无论是解码器还是原子的取值，都无须知道任何外部或内部连线的绝对名称。

**英文原文**

Decoding the weight of a contracted station

Atom arguments refer either to exposed arguments of the new station
or to wires summed out inside it. Neither the decoder nor the atom
values need the absolute names of any exterior or internal wires.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Classical

-- 读法：结构的字段包括 `A`、`E`、`I`、`value`、`read`。
structure History (F X : Type) where
  A : Type
  E : Type
  [atoms : Fintype A]
  [internal : Fintype E]
  I : A → Type
  value : ∀ a, (I a → Bool) → F
  read : ∀ a, I a → X ⊕ E

attribute [instance] History.atoms History.internal

namespace History
variable {F X V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}

-- 读法：`eval` 的取值由 `∑ z : H.E → Bool, ∏ t, H.value t (Sum.elim x z ∘ H.read t)` 给出。
def eval (H : History F X) (x : X → Bool) :=
  ∑ z : H.E → Bool, ∏ t, H.value t (Sum.elim x z ∘ H.read t)

variable {G : Diagram F a b} (C : G.Clustering V E)

-- 读法：逐一匹配以下输入模式：`.inl (.inl x)`、`.inr (.inl y)`、`.inl (.inr e)`、`.inr (.inr e)`。
/-- 沿整个簇追踪一个端口。隐藏连线的两个端点给出同一个地址。

英文原文：Track a port all the way through a cluster. Both ends of a hidden
wire give the very same address.
-/
def address : G.End → C.collapse.End ⊕ (Σ v, C.hidden v)
  | .inl (.inl x) => .inl (.inl (.inl x))
  | .inr (.inl y) => .inl (.inr (.inl y))
  | .inl (.inr e) => (C.edges.symm e).map (fun i => .inl (.inr i)) id
  | .inr (.inr e) => (C.edges.symm e).map (fun i => .inr (.inr i)) id

-- 读法：用字段 `toFun`、`inj'` 构造 `G.Port v ↪ G.End`。
def named (G : Diagram F a b) (v : G.V) : G.Port v ↪ G.End where
  toFun i := G.portEquiv ⟨v, i⟩
  inj' _ _ h := eq_of_heq (Sigma.mk.inj_iff.mp (G.portEquiv.injective h)).2

omit [Field F] in
-- 读法：`Transcript.sample (G.table v) (Sum.elim x y ∘ named G v)` 等于 `G.weight v x y`。两端由定义化简为同一项。
private theorem sample (G : Diagram F a b) (v : G.V) (x y) :
    Transcript.sample (G.table v) (Sum.elim x y ∘ named G v) = G.weight v x y := rfl

-- 读法：`Sum.elim w (fun e => z e.1 e.2) (address C p)` 等于 `Sum.elim (C.lift (w ∘ Sum.inl) z) (C.lift (w ∘ Sum.inr) z) p`。
private theorem read_address (w : C.collapse.End → Bool) (z : C.Inside) (p : G.End) :
    Sum.elim w (fun e => z e.1 e.2) (address C p) =
      Sum.elim (C.lift (w ∘ Sum.inl) z) (C.lift (w ∘ Sum.inr) z) p := by
  rcases p with (i|e)|(j|e)
  · rfl
  · change Sum.elim _ _ ((C.edges.symm e).map _ _) = Sum.elim _ _ (C.edges.symm e)
    cases C.edges.symm e <;> rfl
  · rfl
  · change Sum.elim _ _ ((C.edges.symm e).map _ _) = Sum.elim _ _ (C.edges.symm e)
    cases C.edges.symm e <;> rfl

variable (H : History F X) (v : V) (out : C.collapse.Port v ≃ X)

-- 读法：结构的字段包括 `atom`、`hidden`、`arg`、`localValue`、`links`。
/-- 可逐一检查各原子名称和比特名称的证书。

英文原文：A certificate checked pointwise on the atom and bit names.
-/
structure Presents where
  atom : H.A ≃ {t // C.owner t = v}
  hidden : H.E ≃ C.hidden v
  arg : ∀ i, G.Port (atom i).val → H.I i
  localValue : ∀ i w, H.value i w = Transcript.sample (G.table (atom i).val) (w ∘ arg i)
  links : ∀ i j, address C (named G (atom i).val j) =
    (H.read i (arg i j)).map (fun p => named C.collapse v (out.symm p)) (fun e => ⟨v, hidden e⟩)

-- 读法：在后续公式中，`Bit` 是 `C.collapse.End ⊕ (Σ u, C.hidden u)` 的缩写。
abbrev Bit := C.collapse.End ⊕ (Σ u, C.hidden u)

-- 读法：`embed` 的取值由 `Sum.map (fun p => named C.collapse v (out.symm p)) (fun e => ⟨v, hidden e⟩)` 给出。
def embed (hidden : H.E ≃ C.hidden v) : X ⊕ H.E → Bit C :=
  Sum.map (fun p => named C.collapse v (out.symm p)) (fun e => ⟨v, hidden e⟩)

-- 读法：`factor` 的取值由 `G.weight t (w ∘ address C ∘ Sum.inl) (w ∘ address C ∘ Sum.inr)` 给出。
def factor (t : G.V) (w : Bit C → Bool) : F :=
  G.weight t (w ∘ address C ∘ Sum.inl) (w ∘ address C ∘ Sum.inr)

-- 读法：结构的字段包括 `atom`、`hidden`、`entry`、`idle`。
/-- 局部对应可以略去空闲因子。进行检验时无须为原有原子的参数指定次序。

英文原文：A local correspondence may omit idle factors. Its tests need no
choice of an ordering of the old atom arguments.
-/
structure Traces where
  atom : H.A ↪ {t // C.owner t = v}
  hidden : H.E ≃ C.hidden v
  entry : ∀ i w, H.value i (w ∘ embed C H v out hidden ∘ H.read i) = factor C (atom i) w
  idle : ∀ t ∉ Set.range atom, ∀ w, factor C t.val w = 1

variable {C H v out}

-- 读法：用字段 `atom`、`hidden`、`idle`、`entry` 构造 `Traces C H v out`。
def Presents.traces (p : Presents C H v out) : Traces C H v out where
  atom := p.atom.toEmbedding
  hidden := p.hidden
  idle j hj := (hj (p.atom.surjective j)).elim
  entry i w := by
    rw [p.localValue, factor, ← sample]
    apply congrArg
    funext t
    change w (embed C H v out p.hidden (H.read i (p.arg i t))) = _
    unfold embed
    rw [← p.links]
    simp only [Function.comp_apply]
    cases named G (p.atom i).val t <;> rfl

-- 读法：`H.eval x` 等于 `Transcript.sample (C.collapse.table v) (x ∘ out)`。用函数外延性比较等号两侧在 `t; rw [Function.comp_apply, ← hw]` 处的取值。
theorem Traces.correct (p : Traces C H v out) (x : X → Bool) :
    H.eval x = Transcript.sample (C.collapse.table v) (x ∘ out) := by
  let f := named C.collapse v
  let w := Function.extend f (x ∘ out) (fun _ => false)
  have hw (t : C.collapse.Port v) : w (named C.collapse v t) = x (out t) :=
    f.injective.extend_apply _ _ _
  have eqn : x ∘ out = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ∘ f := by
    funext t; rw [Function.comp_apply, ← hw]
    change w (f t) = Sum.elim _ _ (f t)
    cases f t <;> rfl
  rw [eqn, sample, C.weight_collapse]
  unfold eval
  refine Fintype.sum_equiv (p.hidden.arrowCongr (Equiv.refl Bool)) _ _ ?_
  intro z
  let Z : C.Inside := Function.update (fun _ _ => false) v (z ∘ p.hidden.symm)
  -- 推导：记下中间结论 `tape`：`Bit C → Bool`。
  let tape : Bit C → Bool := Sum.elim w (fun e => Z e.1 e.2)
  have hread : Sum.elim x z = tape ∘ embed C H v out p.hidden := by
    funext t
    cases t with
    | inl t => simp [tape, embed, hw]
    | inr e => simp [tape, embed, Z]
  have ha : tape ∘ address C = Sum.elim (C.lift (w ∘ Sum.inl) Z) (C.lift (w ∘ Sum.inr) Z) :=
    funext (read_address C w Z)
  have hf (i : G.V) :
      G.weight i (C.lift (w ∘ Sum.inl) Z) (C.lift (w ∘ Sum.inr) Z) = factor C i tape := by
    unfold factor
    simp only [← Function.comp_assoc, ha]
    rfl
  change _ = ∏ t : {t // C.owner t = v}, G.weight t (C.lift _ Z) (C.lift _ Z)
  simp only [hf, hread, Function.comp_assoc, p.entry]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image p.atom))]
  · rw [Finset.prod_image p.atom.injective.injOn]
  · intro j _ hj
    exact p.idle j (by simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hj) tape

-- 读法：`H.eval x` 等于 `Transcript.sample (C.collapse.table v) (x ∘ out)`。使用 `p.traces.correct` 给出的结论。
theorem Presents.correct (p : Presents C H v out) (x : X → Bool) :
    H.eval x = Transcript.sample (C.collapse.table v) (x ∘ out) :=
  p.traces.correct x

end History
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 局部收缩编码

每个端口引用描述一整段连续的片段。线束的比特宽度可以大于编码的长度。例如，可用一张公共长度表，以线束为单位给出长度和偏移量。

**英文原文**

Local contraction codes

A port reference describes an entire contiguous fragment. The bit
width of a bundle may exceed the size of the code. A common length
table can, for example, give lengths and offsets in bundle units.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring Classical

-- 读法：在后续公式中，`Positions` 是 `Σ i, Fin (w i)` 的缩写。
abbrev Positions {e : ℕ} (w : B e → ℕ) := Σ i, Fin (w i)

-- 读法：结构的字段包括 `width`、`value`、`length`。
/-- 所有位点均使用固定的字典与长度尺度。

英文原文：The dictionary and the length scale are fixed across all sites.
-/
structure Menu (F : Type) (l s d : ℕ) where
  width : B l → B s → ℕ
  value : (i : B l) → (Positions (width i) → Bool) → F
  length : B d → ℕ

-- 读法：在后续公式中，`pointer` 是 `.pair .bit (.pair (.addr e) (.addr d))` 的缩写。
/-- 若区段隐藏，则设置此标志。

英文原文：The flag is set for a hidden span.
-/
abbrev pointer (e d : ℕ) : Format := .pair .bit (.pair (.addr e) (.addr d))

-- 读法：在后续公式中，`code` 是 `.pair (.vec e (.addr d)) (.vec m (.pair .bit (.pair (.addr l) (.vec s (pointer e d)))))` 的缩写。
abbrev code (m e l s d : ℕ) : Format :=
  .pair (.vec e (.addr d)) (.vec m (.pair .bit (.pair (.addr l) (.vec s (pointer e d)))))

-- 读法：`(code m e l s d).width` 等于 `2 ^ e * d + 2 ^ m * (1 + (l + 2 ^ s * (1 + (e + d))))`。
theorem width_code (m e l s d : ℕ) :
    (code m e l s d).width = 2 ^ e * d + 2 ^ m * (1 + (l + 2 ^ s * (1 + (e + d)))) := by
  simp [code, pointer]

namespace Menu
variable {F : Type} {m e l s d : ℕ} (M : Menu F l s d)
variable (w : B e → ℕ) (c : (code m e l s d).obj)

-- 读法：在后续公式中，`Atom` 是 `{i : B m // (c.2 i).1 = true}` 的缩写。
abbrev Atom := {i : B m // (c.2 i).1 = true}
-- 读法：在后续公式中，`label` 是 `(c.2 i).2.1` 的缩写。
abbrev label (i : Atom c) := (c.2 i).2.1
-- 读法：在后续公式中，`ref` 是 `(c.2 i).2.2 j` 的缩写。
abbrev ref (i : Atom c) (j : B s) := (c.2 i).2.2 j
-- 读法：在后续公式中，`hidden` 是 `M.length (c.1 j)` 的缩写。
abbrev hidden (j : B e) := M.length (c.1 j)

-- 读法：当 `p.1` 成立时取 `M.hidden c p.2.1`，否则取 `w p.2.1`。
def capacity (p : (pointer e d).obj) :=
  if p.1 then M.hidden c p.2.1 else w p.2.1

-- 读法：`Fits` 表示以下条件：对每个 `(i : Atom c) (j : B s) (t : Fin (M.width (label c i) j))`，`M.length (ref c i j).2.2 + t.val` 严格小于 `M.capacity w c (ref c i j)`。
def Fits : Prop :=
  ∀ (i : Atom c) (j : B s) (t : Fin (M.width (label c i) j)),
    M.length (ref c i j).2.2 + t.val < M.capacity w c (ref c i j)

-- 读法：`resolve` 的结果类型为 `Positions w ⊕ Positions (M.hidden c)`。
def resolve (p : (pointer e d).obj) (t : Fin (M.capacity w c p)) :
    Positions w ⊕ Positions (M.hidden c) :=
  if h : p.1 then .inr ⟨p.2.1, ⟨t.val, by simpa [capacity, h] using t.isLt⟩⟩
  else .inl ⟨p.2.1, ⟨t.val, by simpa [capacity, h] using t.isLt⟩⟩

-- 读法：用字段 `A`、`E`、`I`、`value` 构造 `History F (Positions w)`。
def history (h : M.Fits w c) : History F (Positions w) where
  A := Atom c
  E := Positions (M.hidden c)
  I i := Positions (M.width (label c i))
  value i := M.value (label c i)
  read i p := M.resolve w c (ref c i p.1) ⟨_, h i p.1 p.2⟩

-- 读法：当 `h : M.Fits w c` 成立时取 `(M.history w c h).eval x`，否则取 `0`。
/-- 无需读取表的全局站点编号即可解码。

英文原文：A table is decoded without access to its global station number.
-/
def decode [Field F] (x : Positions w → Bool) : F :=
  if h : M.Fits w c then (M.history w c h).eval x else 0

-- 读法：`M.decode w c x` 等于 `Transcript.sample (C.collapse.table v) (x ∘ p)`。这里调用 `trace.correct`。
theorem decode_eq [Field F] {V E : Type} [Fintype V] [Fintype E] {a b : Wire}
    {G : Diagram F a b} (C : G.Clustering V E) (v : V)
    (p : C.collapse.Port v ≃ Positions w) (h : M.Fits w c)
    (trace : Traces C (M.history w c h) v p) (x : Positions w → Bool) :
    M.decode w c x = Transcript.sample (C.collapse.table v) (x ∘ p) := by
  rw [decode, dite_eq_left h]
  exact trace.correct x

end Menu
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 按各自的实际宽度打包局部历史

每个标签均为非负整数，其长度为表示它所需的比特数，零占零位。在每个槽位存储一个较短的长度值，并在相应的乘积空间中枚举截短后的标签。新标签中较长的部分以上述已占用长度的*总和*为界，系数恰为一。

**英文原文**

Packing local histories at their actual widths

Every tag is a nonnegative integer. Its length is the number of bits
needed to represent it, with zero using no bits. Store a short length
at every slot and enumerate the truncated tags in the corresponding
product space. The long part of the new tag is bounded by the *sum*
of the occupied lengths, with coefficient one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
open Coloring
open scoped Classical

-- 读法：`used` 的取值由 `Nat.clog 2 (n + 1)` 给出。
def used (n : ℕ) := Nat.clog 2 (n + 1)

-- 读法：`used n ≤ d` 与 `n < 2 ^ d` 等价。这里调用 `Nat.clog_le_iff_le_pow`。
theorem used_le {n d : ℕ} : used n ≤ d ↔ n < 2 ^ d := by
  exact Nat.clog_le_iff_le_pow (by decide)

-- 读法：`used 0` 等于 `0`。
@[simp] theorem used_zero : used 0 = 0 := by simp [used]

variable {I : Type} [Fintype I] [DecidableEq I] {l k : ℕ}

-- 读法：`cost` 的取值由 `∑ i, used (x i).val` 给出。
def cost (x : I → B l) := ∑ i, used (x i).val

-- 读法：`widths` 的取值由 `⟨used (x i).val, (used_le.mpr (x i).isLt).trans_lt (used_le.mp le_rfl)⟩` 给出。
def widths (x : I → B l) (i : I) : B (used l) :=
  ⟨used (x i).val, (used_le.mpr (x i).isLt).trans_lt (used_le.mp le_rfl)⟩

-- 读法：在后续公式中，`values` 是 `(i : I) → B (b i).val` 的缩写。
abbrev values (b : I → B (used l)) := (i : I) → B (b i).val

-- 读法：输入 `i` 时返回 `⟨(x i).val, used_le.mp le_rfl⟩`。
def trim (x : I → B l) : values (widths x) :=
  fun i => ⟨(x i).val, used_le.mp le_rfl⟩

-- 读法：`header` 的取值由 `k + Fintype.card I * used l` 给出。
def header (I : Type) [Fintype I] (k l : ℕ) := k + Fintype.card I * used l

-- 读法：`heads` 的取值由 `Fintype.equivOfCardEq (by simp [B, ← pow_mul, mul_comm]; rw [header, pow_add])` 给出。
private def heads : B k × (I → B (used l)) ≃ B (header I k l) :=
  Fintype.equivOfCardEq (by simp [B, ← pow_mul, mul_comm]; rw [header, pow_add])

-- 读法：`number` 的取值由 `(Fintype.equivFin (values b) v).val` 给出。
private def number {b : I → B (used l)} (v : values b) : ℕ :=
  (Fintype.equivFin (values b) v).val

-- 读法：`pack` 的取值由 `(heads (z.1, widths z.2)).val + 2 ^ (header I k l) * number (trim z.2)` 给出。
def pack (z : B k × (I → B l)) : ℕ :=
  (heads (z.1, widths z.2)).val + 2 ^ (header I k l) * number (trim z.2)

-- 读法：`used (pack z)` 不超过 `header I k l + cost z.2`。
theorem length (z : B k × (I → B l)) : used (pack z) ≤ header I k l + cost z.2 := by
  have hn : number (trim z.2) < 2 ^ cost z.2 := by
    have h := (Fintype.equivFin (values (widths z.2)) (trim z.2)).isLt
    change number (trim z.2) < Fintype.card (values (widths z.2)) at h
    change number (trim z.2) < Fintype.card ((i : I) → B ((widths z.2) i).val) at h
    rw [Fintype.card_pi] at h
    simp only [B, Fintype.card_fin, Finset.prod_pow_eq_pow_sum] at h
    exact h
  rw [used_le, pow_add]
  unfold pack
  calc
    _ < 2 ^ (header I k l) + 2 ^ (header I k l) * number (trim z.2) :=
      Nat.add_lt_add_right (heads (z.1, widths z.2)).isLt _
    _ = 2 ^ (header I k l) * (number (trim z.2) + 1) := by rw [mul_add, mul_one, add_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ hn

-- 读法：对每个 `i`，`(v i).val` 等于 `(w i).val`。
private theorem number_eq {a b : I → B (used l)} {v : values a} {w : values b}
    (h : a = b) (e : number v = number w) : ∀ i, (v i).val = (w i).val := by
  subst b
  have hh : v = w := (Fintype.equivFin _).injective (Fin.ext e)
  simp only [hh, implies_true]

-- 读法：`(pack (I := I) (k := k) (l := l))` 是单射。
theorem injective : Function.Injective (pack (I := I) (k := k) (l := l)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have he := congrArg (· % 2 ^ (header I k l)) h
  simp only [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fin.isLt _)] at he
  have hh := heads.injective (Fin.ext he)
  obtain ⟨rfl, hw⟩ := Prod.mk.inj hh
  have he' : number (trim x) = number (trim y) := by
    unfold pack at h
    rw [he] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel h)
  have hxy : x = y := funext fun i => Fin.ext (number_eq hw he' i)
  rw [hxy]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
end

/-!
# 解读局部半边数组

群落标签仅在所属宿主内部唯一。邻居索引相对于源宿主给出。这两个字段都不需要全局地址比特。

**英文原文**

Interpreting the local stub arrays

A colony label is unique only inside its host. A neighbor index is
local to the source host. Neither field needs global address bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring Packing

variable {V E P : Type} {r d h e k ℓ : ℕ}

-- 读法：结构的字段包括 `block`、`tag`、`separate`、`stub`、`unique`。
/-- 对所有局部数组统一编制索引。源端与目的端采用同一群落标签约定。

英文原文：Common indexing of all local arrays. Source and destination use
the same convention for colony labels.
-/
structure Stubs (src dst : E → P) (ix : E → Cell r) (owner : P → V) (d h e ℓ : ℕ) where
  block : Cell r ↪ B h
  tag : P → B ℓ
  separate : ∀ p q, owner p = owner q → tag p = tag q → p = q
  stub : E → B e
  unique : ∀ i j, src i = src j → ix i = ix j → stub i = stub j → i = j
  near : E → B d
  neighbor : ∀ i j, src i = src j → (near i = near j ↔ owner (dst i) = owner (dst j))

namespace Stubs
variable {src dst : E → P} {ix : E → Cell r} {owner : P → V}
  (f : Stubs src dst ix owner d h e ℓ)

-- 读法：`pos` 的取值由 `(rowIndex h e).symm (f.block (ix i), f.stub i)` 给出。
def pos (i : E) := (rowIndex h e).symm (f.block (ix i), f.stub i)
-- 读法：`key` 的取值由 `(Labels h ℓ d).serial (0, f.tag p, 0)` 给出。
def key (p : P) := (Labels h ℓ d).serial (0, f.tag p, 0)

variable (x : V → (Input d h e k ℓ).obj) (c : Color r)

-- 读法：结构的字段包括 `active`、`color`、`label`、`slot`、`remote`。
/-- 活跃记录恰好枚举所有传出单位。只要求这些单位上的本地和远端群落键正确。

英文原文：The active records enumerate exactly the outgoing units. Only the
local and remote colony keys on those units must be correct.
-/
structure Records : Prop where
  active : ∀ v b j, (((x v).2.1 b).2 j).1 = true ↔
    ∃ i, owner (src i) = v ∧ f.block (ix i) = b ∧ f.stub i = j
  color : ∀ i, (x (owner (src i))).1 (f.block (ix i)) = true ↔ thick c (ix i)
  label : ∀ i, ((x (owner (src i))).2.1 (f.block (ix i))).1 = f.tag (src i)
  slot : ∀ i, (((x (owner (src i))).2.1 (f.block (ix i))).2 (f.stub i)).2.1 = f.near i
  remote : ∀ i, (x (owner (src i))).2.2 (f.block (ix i)) (f.near i) = f.tag (dst i)

-- 读法：要证明的命题是 `(rows (x (owner p))).Represents src dst ix c p f.pos (f.key p)`。
theorem represents (rec : f.Records x c) (p : P) :
    (rows (x (owner p))).Represents src dst ix c p f.pos (f.key p) := by
  have addr (i : E) : rowIndex h e (f.pos i) = (f.block (ix i), f.stub i) :=
    (rowIndex h e).apply_symm_apply _
  have source (i : E) : (rows (x (owner (src i)))).src (f.pos i) = f.key (src i) := by
    simp only [Rows.src, rows, addr, rec.label, key]
  have dest (i : E) : (rows (x (owner (src i)))).dest (f.pos i) =
      (Labels h ℓ d).serial (0, f.tag (dst i), f.near i) := by
    simp only [Rows.dest, rows, addr, rec.slot, rec.remote]
  constructor
  · intro i j hi hj eq
    have hr := congrArg (rowIndex h e) eq
    rw [addr, addr] at hr
    exact f.unique i j (hi.trans hj.symm) (f.block.injective (Prod.mk.inj hr).1) (Prod.mk.inj hr).2
  · intro i hi
    simp only [Rows.active, rows, addr]
    exact (rec.active _ _ _).mpr ⟨i, congrArg owner hi, rfl, rfl⟩
  · intro j hj ht
    -- 推导：从 `(rec.active (owner p) _ _).mp hj` 中取出 `i, ho, hb, hs`。
    obtain ⟨i, ho, hb, hs⟩ := (rec.active (owner p) _ _).mp hj
    have hp : f.pos i = j := (rowIndex h e).injective ((addr i).trans (Prod.ext hb hs))
    rw [← ho, ← hp, source] at ht
    have he := (Labels h ℓ d).serial.injective ht
    exact ⟨i, f.separate _ _ ho (congrArg (fun z => z.2.1) he), hp⟩
  · intro i hi
    simpa only [hi] using source i
  · intro i hi
    subst p
    simpa only [Rows.thick, rows, addr] using rec.color i
  · intro i j hi hj
    have ht := dest i
    have hu := dest j
    rw [hi] at ht
    rw [hj] at hu
    rw [ht, hu, Equiv.apply_eq_iff_eq]
    have hn := f.neighbor i j (hi.trans hj.symm)
    constructor
    · intro eq
      exact f.separate _ _ (hn.mp (congrArg (fun z => z.2.2) eq)) (congrArg (fun z => z.2.1) eq)
    · intro eq
      rw [eq, hn.mpr (congrArg owner eq)]
  · intro i j _ _
    simp only [Rows.item, rows, addr, Equiv.apply_eq_iff_eq, Prod.mk.injEq, and_true,
      f.block.injective.eq_iff]

end Stubs
end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end
