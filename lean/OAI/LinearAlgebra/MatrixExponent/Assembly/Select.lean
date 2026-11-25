-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import OAI.LinearAlgebra.MatrixExponent.Shaving.Defs
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats

section
/-!
# 宿主的长名称与块的短记录

同一宿主的各块共用一份邻居名称列表。每个出现位置只能看到此列表中的索引与远端端口的索引，因此无须在每个出现位置重复计入全局地址。

**英文原文**

Long host names and short block records

A host's list of neighbor names is shared between blocks. An
occurrence sees only indices in this list and indices of remote
ports. This avoids charging a global address at every occurrence.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Fmt

open Coloring

-- 读法：在后续公式中，`rows` 是 `.vec m (.pair (.vec d (.addr m)) (.vec h A))` 的缩写。
abbrev rows (m d h : ℕ) (A : Format) : Format :=
  .vec m (.pair (.vec d (.addr m)) (.vec h A))

-- 读法：在后续公式中，`occ` 是 `.pair (.addr ℓ) (.vec e (.pair .bit (.pair (.addr d) (.addr k))))` 的缩写。
/-- 单个出现位置的候选传出半边。附加字段可携带群落键，所属块则由外层行隐式指定。

英文原文：Candidate outgoing stubs at one occurrence. The extra field can
carry a colony key. The block is implicit in the enclosing row.
-/
abbrev occ (d _h e k ℓ : ℕ) : Format :=
  .pair (.addr ℓ) (.vec e (.pair .bit (.pair (.addr d) (.addr k))))

-- 读法：`(rows m d h A).width` 等于 `2 ^ m * (2 ^ d * m + 2 ^ h * A.width)`。
theorem width_rows (m d h : ℕ) (A : Format) :
    (rows m d h A).width = 2 ^ m * (2 ^ d * m + 2 ^ h * A.width) := by
  simp [rows]

-- 读法：`(occ d h e k ℓ).width` 等于 `ℓ + 2 ^ e * (1 + (d + k))`。
theorem width_occ (d h e k ℓ : ℕ) :
    (occ d h e k ℓ).width = ℓ + 2 ^ e * (1 + (d + k)) := by
  simp [occ]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Fmt
end

/-!
# 有类型的记录之间的网络

顺序复合会对*整条*中间记录作收缩。其两种布局之间可以有任意的比特位置重命名。门数预算可相加。

**英文原文**

Networks between typed records

Sequential composition contracts the *entire* intermediate record.
Its two layouts may differ by arbitrary renaming of bit positions.
The gate budget is additive.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

variable {F : Type} [Field F] {A B C D : Format} {u m n : ℕ} {L : Set (Table F)}

-- 读法：`finiteObj` 的取值由 `Finite.of_injective A.code A.code.injective` 给出。
instance finiteObj (A : Format) : Finite A.obj := Finite.of_injective A.code A.code.injective

-- 读法：`names` 的取值由 `Fintype.equivOfCardEq (by simp [Format.width])` 给出。
def names (A : Format) : A.pins ≃ slots (word A.width) := Fintype.equivOfCardEq (by simp [Format.width])

-- 读法：`view` 的取值由 `(bits a).trans ((i.symm.arrowCongr (.refl Bool)).trans A.code.symm)` 给出。
def view (A : Format) {a : Wire} (i : A.pins ≃ slots a) : Val a ≃ A.obj :=
  (bits a).trans ((i.symm.arrowCongr (.refl Bool)).trans A.code.symm)

-- 读法：`view A i x` 等于 `A.code.symm (bits a x ∘ i)`。两端由定义化简为同一项。
theorem view_apply (A : Format) {a : Wire} (i : A.pins ≃ slots a) (x : Val a) :
    view A i x = A.code.symm (bits a x ∘ i) := rfl

-- 读法：`Kernel` 表示以下条件：对每个 `(a b : Wire) (i : A.pins ≃ slots a) (j : B.pins ≃ slots b)`，存在 `s ≤ m`，要证明的命题是 `Wide F u L a b (fun x y => f (view A i x) (view B j y)) s`。
def Kernel (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (f : A.obj → B.obj → F) (m : ℕ) : Prop :=
  ∀ (a b : Wire) (i : A.pins ≃ slots a) (j : B.pins ≃ slots b),
    ∃ s ≤ m, Wide F u L a b (fun x y => f (view A i x) (view B j y)) s

-- 读法：`Map` 表示以下条件：`Kernel F u L A B (fun x y => if f x = y then 1 else 0) m`。
def Map (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (f : A.obj → B.obj) (m : ℕ) : Prop :=
  Kernel F u L A B (fun x y => if f x = y then 1 else 0) m

namespace Kernel
variable {f : A.obj → B.obj → F}

-- 读法：要证明的命题是 `Kernel F u L A B f n`。
theorem mono (h : Kernel F u L A B f m) (hm : m ≤ n) : Kernel F u L A B f n := by
  intro a b i j
  obtain ⟨s, hs, h⟩ := h a b i j
  exact ⟨s, hs.trans hm, h⟩

-- 读法：要证明的命题是 `Kernel F v L' A B f m`。
theorem widen {v : ℕ} {L' : Set (Table F)} (h : Kernel F u L A B f m)
    (hu : u ≤ v) (hl : L ⊆ L') : Kernel F v L' A B f m := by
  intro a b i j
  obtain ⟨s, hs, h⟩ := h a b i j
  exact ⟨s, hs, h.mono hu hl⟩

-- 读法：要证明的命题是 `Kernel F u L A B f m`。
theorem of_layout {a b : Wire} (i : A.pins ≃ slots a) (j : B.pins ≃ slots b)
    (h : ∃ s ≤ m, Wide F u L a b (fun x y => f (view A i x) (view B j y)) s) :
    Kernel F u L A B f m := by
  intro c d k l
  obtain ⟨s, hs, hw⟩ := h
  refine ⟨s, hs, ?_⟩
  have hp := (hw.pre (rewire_reindex (i.symm.trans k))).post (rewire_reindex (j.symm.trans l))
  simpa [view_apply, reindex, Function.comp_def] using hp

-- 读法：要证明的命题是 `Kernel F u L A C (fun x z => ∑ y, f x y * g y z) (m + n)`。这里调用 `h.comp`。
theorem comp [Fintype B.obj] {g : B.obj → C.obj → F}
    (h : Kernel F u L A B f m) (k : Kernel F u L B C g n) :
    Kernel F u L A C (fun x z => ∑ y, f x y * g y z) (m + n) := by
  intro a c i l
  obtain ⟨s, hs, h⟩ := h a _ i (names B)
  obtain ⟨t, ht, k⟩ := k _ c (names B) l
  refine ⟨s + t, Nat.add_le_add hs ht, ?_⟩
  have he (x : Val a) (z : Val c) :=
    (view B (names B)).sum_comp (fun y => f (view A i x) y * g y (view C l z))
  simpa only [he] using h.comp k

-- 读法：要证明的命题是 `Kernel F u L (.pair A C) (.pair B D) (fun x y => f x.1 y.1 * g x.2 y.2) (m + n)`。这里调用 `of_layout`。
theorem par {g : C.obj → D.obj → F} (h : Kernel F u L A B f m) (k : Kernel F u L C D g n) :
    Kernel F u L (.pair A C) (.pair B D) (fun x y => f x.1 y.1 * g x.2 y.2) (m + n) := by
  obtain ⟨s, hs, h⟩ := h _ _ (names A) (names B)
  obtain ⟨t, ht, k⟩ := k _ _ (names C) (names D)
  exact of_layout (a := .pair _ _) (b := .pair _ _)
    ((names A).sumCongr (names C)) ((names B).sumCongr (names D))
    ⟨_, Nat.add_le_add hs ht, h.par k⟩

end Kernel

namespace Map
variable {f : A.obj → B.obj}

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `B` 实现映射 `f` 的开销至多为 `n`。使用 `Kernel.mono` 给出的结论。
theorem mono (h : Map F u L A B f m) (hm : m ≤ n) : Map F u L A B f n := Kernel.mono h hm

-- 读法：要证明的命题是 `Kernel F u L A C (fun x y => g (f x) y) (m + n)`。
theorem then_kernel {g : B.obj → C.obj → F} (h : Map F u L A B f m)
    (k : Kernel F u L B C g n) : Kernel F u L A C (fun x y => g (f x) y) (m + n) := by
  let _ := Fintype.ofFinite B.obj
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using Kernel.comp h k

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `C` 实现映射 `(g ∘ f)` 的开销至多为 `(m + n)`。使用 `h.then_kernel` 给出的结论。
theorem comp {g : B.obj → C.obj} (h : Map F u L A B f m) (k : Map F u L B C g n) :
    Map F u L A C (g ∘ f) (m + n) := h.then_kernel k

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `(.pair A C)` 到 `(.pair B D)` 实现映射 `(Prod.map f g)` 的开销至多为 `(m + n)`。
theorem par {g : C.obj → D.obj} (h : Map F u L A B f m) (k : Map F u L C D g n) :
    Map F u L (.pair A C) (.pair B D) (Prod.map f g) (m + n) := by
  unfold Map
  simpa only [Prod.ext_iff, Prod.map_fst, Prod.map_snd, ite_and, ite_mul, one_mul, zero_mul]
    using Kernel.par h k

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `B` 实现映射 `f` 的开销至多为 `m`。这里调用 `Kernel.of_layout`。
theorem of_layout {a b : Wire} (i : A.pins ≃ slots a) (j : B.pins ≃ slots b)
    {g : Val a → Val b} (h : DWide F u L a b g m) (he : ∀ x, view B j (g x) = f (view A i x)) :
    Map F u L A B f m := by
  apply Kernel.of_layout i j
  obtain ⟨s, hs, hw⟩ := h
  refine ⟨s, hs, ?_⟩
  simpa only [← he, Equiv.apply_eq_iff_eq] using hw

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `A` 到 `B` 实现映射 `f` 的开销至多为 `(4 * m)`。这里调用 `of_layout`。
theorem circuit (hu : 3 ≤ u) (h : Circuit F A B f m) : Map F u L A B f (4 * m) := by
  apply of_layout (names A) (names B) (DWide.of_dnet hu (h _ _ (names A) (names B)))
  intro x
  exact (view B (names B)).apply_symm_apply _

end Map
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 编码后的展开式的复合

状态可包含其宿主、分配方案及不变量的证明。跨越阶段边界时只传递比特记录，其中可以按本阶段自身的次序排列有效载荷。即使记录相同，不同项在系数域中的重数仍然保留。

**英文原文**

Composing encoded expansions

A state can carry its host, allocation and proof invariants. Only
the bit record crosses a stage boundary. It may contain payloads
in the stage's own ordering. Distinct terms with the same record
retain their field multiplicities.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

universe v

-- 读法：结构的字段包括 `state`、`eval`、`port`、`encode`。
structure Snapshot (F : Type) (x y : Wire) where
  state : Type v
  eval : state → Val x → Val y → F
  port : Format
  encode : state → Val x → Val y → port.obj

variable {F : Type} [Field F] {x y : Wire} {u m n : ℕ} {L : Set (Table F)}
  {X Y Z : Snapshot.{v} F x y}

-- 读法：`Expands` 的结果类型为 `Prop`。
def Expands (X Y : Snapshot.{v} F x y) (f : X.port.obj → Y.port.obj → F) : Prop :=
  ∀ s : X.state, ∃ (I : Type) (_ : Fintype I) (q : I → Y.state) (c : I → F),
    (∀ a b, X.eval s a b = ∑ i, c i * Y.eval (q i) a b) ∧
    ∀ a b r, f (X.encode s a b) r = ∑ i, if Y.encode (q i) a b = r then c i else 0

-- 读法：`Transforms` 表示以下条件：存在 `f`，`Kernel F u L X.port Y.port f m` 与 `Expands X Y f` 同时成立。
def Transforms (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (X Y : Snapshot.{v} F x y) (m : ℕ) : Prop :=
  ∃ f, Kernel F u L X.port Y.port f m ∧ Expands X Y f

-- 读法：`(∑ r, (∑ i, if q i = r then c i else 0) * f r)` 等于 `∑ i, c i * f (q i)`。
/-- 对快照进行收缩时，按实际分支求和，即使有不同分支的编码相同亦然。

英文原文：Contracting against a snapshot sums over actual branches, including
when encodings collide.
-/
private theorem contract {I R : Type} [Fintype I] [Fintype R] (q : I → R) (c : I → F) (f : R → F) :
    (∑ r, (∑ i, if q i = r then c i else 0) * f r) = ∑ i, c i * f (q i) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

-- 读法：要证明的命题是 `Expands X Z (fun a b => ∑ y, f a y * g y b)`。
theorem Expands.comp [Fintype Y.port.obj] {f g} (h : Expands X Y f) (k : Expands Y Z g) :
    Expands X Z (fun a b => ∑ y, f a y * g y b) := by
  intro s
  obtain ⟨I, _, q, c, hq, he⟩ := h s
  choose J fJ r d hr hd using fun i => k (q i)
  let _ : ∀ i, Fintype (J i) := fJ
  refine ⟨Σ i, J i, inferInstance, fun v => r v.1 v.2, fun v => c v.1 * d v.1 v.2, ?_, ?_⟩
  · intro a b
    simp only [hq, hr, Finset.mul_sum, Fintype.sum_sigma, mul_assoc]
  · intro a b t
    simp only [he]
    rw [contract, Fintype.sum_sigma]
    simp only [hd, Finset.mul_sum, mul_ite, mul_zero]

namespace Transforms

-- 读法：要证明的命题是 `Transforms F u L X Y n`。
theorem mono (h : Transforms F u L X Y m) (hm : m ≤ n) : Transforms F u L X Y n :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.mono hm, he⟩

-- 读法：要证明的命题是 `Transforms F v L' X Y m`。
theorem widen {v : ℕ} {L' : Set (Table F)} (h : Transforms F u L X Y m) (hu : u ≤ v)
    (hs : L ⊆ L') : Transforms F v L' X Y m :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.widen hu hs, he⟩

-- 读法：要证明的命题是 `Transforms F u L X Z (m + n)`。
theorem comp (h : Transforms F u L X Y m) (k : Transforms F u L Y Z n) :
    Transforms F u L X Z (m + n) := by
  let _ := Fintype.ofFinite Y.port.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  exact ⟨_, hf.comp hg, he.comp hg'⟩

-- 读法：要证明的命题是 `Transforms F u L X Y m`。
theorem of_map (f : X.port.obj → Y.port.obj) (q : X.state → Y.state)
    (hm : Map F u L X.port Y.port f m)
    (he : ∀ s, X.eval s = Y.eval (q s))
    (hc : ∀ s a b, f (X.encode s a b) = Y.encode (q s) a b) :
    Transforms F u L X Y m := by
  refine ⟨_, hm, fun s => ⟨Unit, inferInstance, fun _ => q s, fun _ => 1, ?_, ?_⟩⟩
  · intro a b
    simp only [he, Fintype.sum_unique, one_mul]
  · intro a b r
    simp only [hc, Fintype.sum_unique]

-- 读法：要证明的命题是 `Transforms F u L X X (4 * X.port.width)`。使用 `of_map` 给出的结论。
theorem refl (hu : 3 ≤ u) (X : Snapshot.{v} F x y) :
    Transforms F u L X X (4 * X.port.width) :=
  of_map id id (Map.circuit hu (Circuit.id F _)) (fun _ => rfl) (fun _ _ _ => rfl)

end Transforms

-- 读法：`Finishes` 表示以下条件：存在 `k : X.port.obj → F`，`Kernel F u L X.port (.wire .unit) (fun a _ => k a) m` 与 `∀ s a b, k (X.encode s a b) = X.eval s a b` 同时成立。
def Finishes (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (X : Snapshot.{v} F x y) (m : ℕ) : Prop :=
  ∃ k : X.port.obj → F, Kernel F u L X.port (.wire .unit) (fun a _ => k a) m ∧
    ∀ s a b, k (X.encode s a b) = X.eval s a b

-- 读法：要证明的命题是 `Finishes F u L X (m + n)`。
theorem Transforms.finish (h : Transforms F u L X Y m) (k : Finishes F u L Y n) :
    Finishes F u L X (m + n) := by
  let _ := Fintype.ofFinite Y.port.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  refine ⟨fun x => ∑ y, f x y * g y, hf.comp hg, fun s a b => ?_⟩
  obtain ⟨I, _, q, c, hq, hh⟩ := he s
  simp only [hh, contract, hg', hq]

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 在共用记录带上实现局部因子

复制数据带时，只按实际读取次数计费；即使整条数据带远大于任一单个因子，也照此计算。

**英文原文**

Realizing local factors on shared tapes

Copying a tape is paid once per actual read, even if the tape is
much larger than any individual factor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel

open Coloring Transcript
open scoped Classical

variable {F : Type} [Field F] {A B C : Format} {u m : ℕ} {L : Set (Table F)}

-- 读法：要证明的命题是 `Kernel F u L A B (fun x y => f (Sum.elim (A.code x) (B.code y))) (m + 4 * B.width)`。
theorem of_weight (hu : 3 ≤ u) {f : ((A.pins ⊕ B.pins) → Bool) → F}
    (h : WideWeight F u L f m) :
    Kernel F u L A B (fun x y => f (Sum.elim (A.code x) (B.code y))) (m + 4 * B.width) := by
  intro a b i j
  obtain ⟨s, hs, k⟩ := h (.pair a b) (i.sumCongr j)
  obtain ⟨t, ht, hc⟩ := (Net.cup F b).includeWide (L := L) hu
  have hw := (((k.par hc).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))).trace
  have hb := (Fintype.card_congr j).trans (card_slots b)
  refine ⟨s + t, Nat.add_le_add hs (by rw [Format.width, hb]; exact ht), ?_⟩
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hw
  convert hw using 1
  funext x y
  simp only [view_apply, Equiv.apply_symm_apply]
  apply congrArg f
  funext p
  cases p <;> rfl

-- 读法：这里调用 `of_weight`。
theorem factors {I Y : Type} [Fintype I] [Fintype Y] {Z : I → Type} [∀ i, Fintype (Z i)]
    (k : (i : I) → (Z i → Bool) → F) (r : (i : I) → Z i → (A.pins ⊕ B.pins) ⊕ Y)
    (cost : I → ℕ) (hu : 3 ≤ u) (h : ∀ i, WideWeight F u L (k i) (cost i)) :
    Kernel F u L A B (fun x y => weightedSum k r (Sum.elim (A.code x) (B.code y)))
      (8 * (A.width + B.width + Fintype.card Y) + 9 * (∑ i, cost i) + 4 * B.width) := by
  simpa only [Fintype.card_sum] using of_weight hu (wide_sum k r cost hu h)

-- 读法：存在从 `.unit` 到 `a` 的网络，核为 `(fun _ _ => 1)`，顶点数为 `(wd a)`，系数取自 `F`。对 `a` 作归纳。
private theorem free (a : Wire) : Net F .unit a (fun _ _ => 1) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact .empty
  | pair a b h k => simpa only [wd, one_mul] using (h.par k).pre (.unit' _)

-- 读法：要证明的命题是 `Kernel F u L A B (fun a b => ∑ c, f (a, c) b) (m + 4 * C.width)`。
theorem sum_hidden [Fintype C.obj] {f : (A.obj × C.obj) → B.obj → F}
    (hu : 3 ≤ u) (h : Kernel F u L (.pair A C) B f m) :
    Kernel F u L A B (fun a b => ∑ c, f (a, c) b) (m + 4 * C.width) := by
  intro a b i j
  let c := word C.width
  obtain ⟨s, hs, hk⟩ := h (.pair a c) b (i.sumCongr (names C)) j
  obtain ⟨t, ht, hf⟩ := (free (F := F) c).includeWide (L := L) hu
  have hw := ((hk.par hf).pre (.unit' _)).trace
  refine ⟨s + t, Nat.add_le_add hs (by simpa [c] using ht), ?_⟩
  simp only [mul_one] at hw
  convert hw using 1
  funext x y
  exact ((view C (names C)).sum_comp (fun z => f (view A i x, z) (view B j y))).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Kernel
end

/-!
# 精确展开式的每个分支使用一个选择字

备选菜单可以依赖于完整的前序状态。只有对外提供的选择器格式必须在所有可能的前序状态间保持一致。

**英文原文**

One selector word per branch of an exact expansion

The menu can depend on the entire preceding state. Only the exposed
selector format must stay fixed across the possible preceding states.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Transcript
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire} {u m n : ℕ} {L : Set (Table F)}
  {X Y : Snapshot.{v} F x y} {C : Format}

-- 读法：结构的字段包括 `choice`、`index`、`next`、`scalar`、`expands`。
structure Selected (X Y : Snapshot.{v} F x y) (C : Format) where
  choice : X.state → Type
  [finite : ∀ s, Fintype (choice s)]
  index : ∀ s, Selector (choice s) C.obj
  next : ∀ s, choice s → Y.state
  scalar : ∀ s, choice s → F
  expands : ∀ s a b, X.eval s a b = ∑ i, scalar s i * Y.eval (next s i) a b

attribute [instance] Selected.finite

-- 读法：要证明的命题是 `Transforms F u L X Y (m + 4 * C.width)`。
theorem Transforms.of_selector (hu : 3 ≤ u) (R : Selected X Y C)
    {k : X.port.obj × C.obj → Y.port.obj → F}
    (hk : Kernel F u L (.pair X.port C) Y.port k m)
    (he : ∀ s a b c t, k (X.encode s a b, c) t = ((R.index s).read c).elim 0
      (fun i => if Y.encode (R.next s i) a b = t then R.scalar s i else 0)) :
    Transforms F u L X Y (m + 4 * C.width) := by
  let _ := Fintype.ofFinite C.obj
  refine ⟨_, Kernel.sum_hidden hu hk, fun s =>
    ⟨R.choice s, inferInstance, R.next s, R.scalar s, R.expands s, fun a b t => ?_⟩⟩
  simp only [he, Selector.sum]

-- 读法：要证明的命题是 `Transforms F u L X Y (m + 4 * C.width)`。
/-- 计算可令无效字的权重为零，从而拒绝它。

英文原文：The computation can reject invalid words by zero weight.
-/
theorem Transforms.of_guard (hu : 3 ≤ u) (R : Selected X Y C)
    (out : X.port.obj × C.obj → Y.port.obj) (weight : X.port.obj × C.obj → F)
    (hk : Kernel F u L (.pair X.port C) Y.port (fun v t => if out v = t then weight v else 0) m)
    (hw : ∀ s a b c, weight (X.encode s a b, c) = ((R.index s).read c).elim 0 (R.scalar s))
    (ho : ∀ s a b i, out (X.encode s a b, (R.index s).write i) = Y.encode (R.next s i) a b) :
    Transforms F u L X Y (m + 4 * C.width) := by
  refine Transforms.of_selector hu R hk fun s a b c t => ?_
  rw [hw]
  cases h : (R.index s).read c with
  | none => simp
  | some i =>
    rw [(R.index s).valid _ _ |>.mp h, ho]
    rfl

-- 读法：存在 `v ≤ m + n + 4 * wd y`，要证明的命题是 `Wide F u L x y (X.eval s) v`。
theorem Finishes.start (hu : 3 ≤ u) (s : X.state)
    (h : Map F u L (.wire (.pair x y)) X.port (fun p => X.encode s p.1 p.2) m)
    (hf : Finishes F u L X n) :
    ∃ v ≤ m + n + 4 * wd y, Wide F u L x y (X.eval s) v := by
  obtain ⟨k, hk, he⟩ := hf
  obtain ⟨v, hv, hv'⟩ := h.then_kernel hk (.pair x y) .unit (.refl _) (.refl _)
  have viewId (z : Val (.pair x y)) : view (.wire (.pair x y)) (.refl _) z = z :=
    (bits _).symm_apply_apply z
  simp only [viewId, he] at hv'
  obtain ⟨w, hw, hcup⟩ := (Net.cup F y).includeWide (L := L) hu
  have hfin := (((hv'.par hcup).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))).trace
  refine ⟨v + w, Nat.add_le_add hv hw, ?_⟩
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hfin

-- 读法：要证明的命题是 `Finishes F u L (X 0) ((∑ i ∈ Finset.range j, cost i) + m)`。对 `j` 作归纳，并把 `m` 保持为任意参数。
/-- 即使每轮的端口、布局与可达状态有所变化，各阶段的预算仍可相加。

英文原文：Stage budgets add even when ports, layouts and reachable states
change from round to round.
-/
theorem Finishes.stages (X : ℕ → Snapshot.{v} F x y) (cost : ℕ → ℕ) (j : ℕ)
    (steps : ∀ i < j, Transforms F u L (X i) (X (i + 1)) (cost i))
    (stop : Finishes F u L (X j) m) :
    Finishes F u L (X 0) ((∑ i ∈ Finset.range j, cost i) + m) := by
  induction j generalizing m with
  | zero => simpa using stop
  | succ j ih =>
    rw [Finset.sum_range_succ, add_assoc]
    exact ih (fun i hi => steps i (Nat.lt_succ_of_lt hi)) ((steps j (by omega)).finish stop)

end OAI.LinearAlgebra.MatrixExponent.Assembly
end
