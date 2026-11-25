-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
import OAI.LinearAlgebra.MatrixExponent.Sphere.Footprint.Load
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Hub
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Angular
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares

/-!
# 运动历史的有限键

每个单元的私有选择器保留原名。每条新增的普通剩余态连线都用创建前的栈长编号。

**英文原文**

Finite keys for the motion history

A cell's private selector has its original name. Each new ordinary
residue wire is numbered by the previous stack length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
open Finset Surface

-- 读法：在后续公式中，`Key` 是 `V ⊕ Fin ns.length` 的缩写。
abbrev Key (V : Type) (ns : List ℕ) := V ⊕ Fin ns.length

namespace Key
variable {V : Type}

-- 读法：`name` 的取值由 `(Function.Embedding.refl _).sumMap ⟨Fin.val, Fin.val_injective⟩` 给出。
def name (ns : List ℕ) : Key V ns ↪ V ⊕ ℕ :=
  (Function.Embedding.refl _).sumMap ⟨Fin.val, Fin.val_injective⟩

-- 读法：要证明的命题是 `Surface.available ns.length (name ns i)`。对 `i` 分类讨论。
theorem available (ns : List ℕ) (i : Key V ns) : Surface.available ns.length (name ns i) := by
  cases i with
  | inl _ => exact trivial
  | inr i => exact i.isLt

-- 读法：存在 `j`，`name ns j` 等于 `i`。对 `i` 分类讨论。
theorem exists_name (ns : List ℕ) (i : V ⊕ ℕ) (hi : Surface.available ns.length i) :
    ∃ j, name ns j = i := by
  cases i with
  | inl i => exact ⟨.inl i, rfl⟩
  | inr i => exact ⟨.inr ⟨i, hi⟩, rfl⟩

-- 读法：`filter` 的取值由 `univ.filter fun i => name ns i ∈ s` 给出。
def filter [Fintype V] (ns : List ℕ) (s : Finset (V ⊕ ℕ)) : Finset (Key V ns) :=
  univ.filter fun i => name ns i ∈ s

-- 读法：`i ∈ filter ns s` 与 `name ns i ∈ s` 等价。
@[simp] theorem mem_filter [Fintype V] {ns : List ℕ} {s : Finset (V ⊕ ℕ)} {i : Key V ns} :
    i ∈ filter ns s ↔ name ns i ∈ s := by simp [filter]

-- 读法：`(filter ns s).card` 不超过 `s.card`。这里调用 `card_le_card`。
theorem card_filter [Fintype V] (ns : List ℕ) (s : Finset (V ⊕ ℕ)) :
    (filter ns s).card ≤ s.card := by
  rw [← card_map (name ns)]
  apply card_le_card
  rintro _ he
  obtain ⟨i, hi, rfl⟩ := mem_map.mp he
  exact mem_filter.mp hi

-- 读法：逐一匹配以下输入模式：`[]`、`n :: ns`。
def order : (ns : List ℕ) → Fin ns.length → ℕ
  | [] => Fin.elim0
  | n :: ns => Fin.snoc (order ns) n

-- 读法：`order ns i` 属于 `ns`。对 `ns` 作归纳。
theorem order_mem (ns : List ℕ) (i : Fin ns.length) : order ns i ∈ ns := by
  induction ns with
  | nil => exact i.elim0
  | cons n ns ih =>
    induction i using Fin.lastCases with
    | last => simp [order]
    | cast i => simp [order, ih i]

-- 读法：用字段 `state`、`fs`、`width`、`code` 构造 `Alphabet (Key V ns)`。
def alphabet (Y : Alphabet V) (t : ℕ) (ns : List ℕ) : Alphabet (Key V ns) where
  state := Sum.elim Y.state fun j => Level t (order ns j)
  fs := Sum.rec Y.fs (fun j => inferInstanceAs (Fintype (Level t (order ns j))))
  width := Sum.elim Y.width fun j => Chunk.width t (order ns j)
  code := Sum.rec Y.code (fun j => binaryCode (Level t (order ns j)) _ (Chunk.card_le t (order ns j)))

-- 读法：`(alphabet Y t ns).width (.inl v)` 等于 `Y.width v`。两端由定义化简为同一项。
@[simp] theorem width_inl (Y : Alphabet V) (t : ℕ) (ns : List ℕ) (v : V) :
    (alphabet Y t ns).width (.inl v) = Y.width v := rfl

-- 读法：`(alphabet Y t ns).width (.inr j)` 等于 `Chunk.width t (order ns j)`。两端由定义化简为同一项。
@[simp] theorem width_inr (Y : Alphabet V) (t : ℕ) (ns : List ℕ) (j : Fin ns.length) :
    (alphabet Y t ns).width (.inr j) = Chunk.width t (order ns j) := rfl

-- 读法：`((alphabet Y t ns).width i : ℝ)` 不超过 `J`。对 `i` 分类讨论。
theorem width_le (Y : Alphabet V) (t : ℕ) (ns : List ℕ) (J : ℝ)
    (original : ∀ v, (Y.width v : ℝ) ≤ J)
    (residue : ∀ b ∈ ns, (Chunk.width t b : ℝ) ≤ J) (i : Key V ns) :
    ((alphabet Y t ns).width i : ℝ) ≤ J := by
  cases i with
  | inl v => exact original v
  | inr j => exact residue _ (order_mem ns j)

end Key
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# 将运动栈与各自独立命名的普通连线对应起来

**英文原文**

Identifying the motion stack with independently named ordinary wires
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
open Surface
open scoped Classical

variable {V X F : Type} {t : ℕ}

-- 读法：在后续公式中，`Values` 是 `∀ i : Fin ns.length, Level t (order ns i)` 的缩写。
abbrev Values (t : ℕ) (ns : List ℕ) := ∀ i : Fin ns.length, Level t (order ns i)

-- 读法：`cut` 的结果类型为 `Values t (n::ns) ≃ Values t ns × Level t n`。
def cut (n : ℕ) (ns : List ℕ) : Values t (n::ns) ≃ Values t ns × Level t n :=
  (Fin.snocEquiv (fun i => Level t (order (n::ns) i))).symm.trans
    ((Equiv.prodComm _ _).trans ((Equiv.piCongrRight fun i => Equiv.cast (by simp [order])).prodCongr
      (Equiv.cast (by simp [order]))))

-- 读法：逐一匹配以下输入模式：`[], _`、`n::ns, z`。
def nest (x : X) : (ns : List ℕ) → Values t ns → Stack X t ns
  | [], _ => x
  | n::ns, z => (nest x ns (cut n ns z).1, (cut n ns z).2)

-- 读法：`traceStack t x ns f` 等于 `∑ z, f (nest x ns z)`。对 `ns` 作归纳。
private theorem trace_nest [Field F] (x : X) (ns : List ℕ) (f : Stack X t ns → F) :
    traceStack t x ns f = ∑ z, f (nest x ns z) := by
  induction ns with
  | nil => simp [traceStack, nest, Values]
  | cons n ns ih =>
    rw [traceStack, ih, ← (cut (t := t) n ns).symm.sum_comp, Fintype.sum_prod_type]
    simp only [nest, Equiv.apply_symm_apply]

-- 读法：要证明的命题是 `Stage.Observe keys ns u (nest x ns z) (nest y ns z')`。对 `ns` 作归纳。
private theorem observe_nest (keys : V → X → X → Prop) (x y : X) (ns : List ℕ)
    (u : V ⊕ ℕ) (z z' : Values t ns)
    (orig : ∀ i, u = .inl i → keys i x y)
    (fresh : ∀ i : Fin ns.length, u = .inr i.val → z i = z' i) :
    Stage.Observe keys ns u (nest x ns z) (nest y ns z') := by
  induction ns with
  | nil => cases u with
    | inl i => exact orig i rfl
    | inr _ => exact trivial
  | cons n ns ih =>
    refine ⟨ih _ _ ?_, ?_⟩
    · intro i hi
      exact congrArg (Equiv.cast (by simp [order]) : Level t (order (n::ns) i.castSucc) ≃ _)
        (fresh i.castSucc hi)
    · intro hi
      exact congrArg (Equiv.cast (by simp [order]) : Level t (order (n::ns) (Fin.last ns.length)) ≃ _)
        (fresh (Fin.last ns.length) hi)

-- 读法：`Stage.base ns (nest x ns z)` 等于 `x`。对 `ns` 作归纳。
private theorem base_nest (x : X) (ns : List ℕ) (z : Values t ns) :
    Stage.base ns (nest x ns z) = x := by
  induction ns with
  | nil => rfl
  | cons n ns ih => exact ih _

variable (Y : Alphabet V) (t : ℕ) (ns : List ℕ)

-- 读法：输入 `i` 时返回 `z (.inl i)`。
def old (z : (alphabet Y t ns).State) : Y.State := fun i => z (.inl i)

-- 读法：`stack` 的取值由 `nest (init (old Y t ns z)) ns (fun i => z (.inr i))` 给出。
/-- 填入原始参数，并将编号后的剩余态还原为运动过程生成它们时的顺序。

英文原文：Fill the original parameters and unwind the numbered residue states
into the order in which the motion procedure produced them.
-/
def stack (init : Y.State → X) (z : (alphabet Y t ns).State) : Stack X t ns :=
  nest (init (old Y t ns z)) ns (fun i => z (.inr i))

-- 读法：`Stage.base ns (stack Y t ns init z)` 等于 `init (old Y t ns z)`。使用 `base_nest` 给出的结论。
@[simp] theorem base_stack (init : Y.State → X) (z : (alphabet Y t ns).State) :
    Stage.base ns (stack Y t ns init z) = init (old Y t ns z) := base_nest _ _ _

-- 读法：要证明的命题是 `Stage.Observe keys ns (name ns k) (stack Y t ns init z) (stack Y t ns init' z')`。这里调用 `old_keys`。
theorem observe_stack (keys : V → X → X → Prop) (init init' : Y.State → X)
    (old_keys : ∀ v x y, x v = y v → keys v (init x) (init' y))
    (z z' : (alphabet Y t ns).State) (k : Key V ns) (hz : z k = z' k) :
    Stage.Observe keys ns (name ns k) (stack Y t ns init z) (stack Y t ns init' z') := by
  refine observe_nest _ _ _ _ _ _ _ ?_ ?_
  · intro i hi
    have he : k = .inl i := (name ns).injective hi
    subst k
    exact old_keys i _ _ hz
  · intro i hi
    have he : k = .inr i := (name ns).injective hi
    subst k
    exact hz

-- 读法：`(∑ z, f (stack Y t ns init z))` 等于 `∑ x : Y.State, traceStack t (init x) ns f`。
theorem sum_stack [Field F] [Fintype V] (init : Y.State → X) (f : Stack X t ns → F) :
    (∑ z, f (stack Y t ns init z)) = ∑ x : Y.State, traceStack t (init x) ns f := by
  let e : (alphabet Y t ns).State ≃ Y.State × Values t ns :=
    Equiv.sumPiEquivProdPi (alphabet Y t ns).state
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [trace_nest]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
end

/-!
# 从终止阶段到普通共享值

**英文原文**

From terminal stages to ordinary shared values
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
open Surface Finset
open scoped Classical

variable {V E T F X : Type} {r t M : ℕ}

-- 读法：结构的字段包括 `src`、`dst`、`meets`、`tracks`、`left`。
/-- 选择分块布局之前，普通网络所需的输入数据。

英文原文：Input data for the ordinary network before choosing a chunk layout.
-/
structure Source (Y : Alphabet V) (a b : Wire) (S : Stage F r t T V E X) where
  src : E → V
  dst : E → V
  meets : ∀ v j, j ∈ (S.scene.cell v).ports → src j.1 = v ∨ dst j.1 = v
  tracks : Tracks src dst S.footprint S.hidden.length
  left : slots a → Place S.scene.cell
  right : slots b → Place S.scene.cell
  init : Val a → Val b → Y.State → X
  keys : V → X → X → Prop
  ext : T → X → X → Prop
  controls : S.Controls keys ext
  original : ∀ i x y z x' y' z', z i = z' i → keys i (init x y z) (init x' y' z')
  exterior : ∀ i j, (item S.scene.cell i).label.name = some j → ∀ x y z x' y' z',
    (∀ k, left k = i → bits a x k = bits a x' k) →
    (∀ k, right k = i → bits b y k = bits b y' k) → ext j (init x y z) (init x' y' z')

variable {Y : Alphabet V} {a b : Wire} [Fintype V]
  (S : Stage F (M * r) (M * t) T V E X) (A : Source Y a b S)

-- 读法：用字段 `src`、`dst`、`meets`、`seen` 构造 `Sharing S.scene.cell a b (alphabet Y (M * t) S.hidden)`。
/-- 仅读取属于该站点足迹的普通连线。

英文原文：Read only ordinary wires belonging to the station's footprint.
-/
def share : Sharing S.scene.cell a b (alphabet Y (M * t) S.hidden) where
  src := A.src
  dst := A.dst
  meets := A.meets
  seen v := filter S.hidden (S.footprint v)
  reads i := filter S.hidden (item S.scene.cell i).label.reads
  within i _ h := mem_filter.mpr
    ((A.controls i.1 _ (List.get_mem _ i.2)).within (mem_filter.mp h))
  present k := by
    obtain ⟨v, hv⟩ := (A.tracks.present _).mpr (available S.hidden k)
    exact ⟨v, mem_filter.mpr hv⟩
  connected k v w hv hw := by
    simp only [mem_filter]
    exact A.tracks.connected _ _ _ (mem_filter.mp hv) (mem_filter.mp hw)
  left := A.left
  right := A.right
  param x y := stack Y (M * t) S.hidden (A.init x y)
  locality i x y z x' y' z' hx hy hz := by
    have ctrl := A.controls i.1 _ (List.get_mem _ i.2)
    apply ctrl.respects
    · intro j hj
      have hav := (A.tracks.present j).mp ⟨_, ctrl.within hj⟩
      obtain ⟨k, rfl⟩ := exists_name S.hidden j hav
      exact observe_stack Y (M * t) S.hidden A.keys _ _
        (fun v a b => A.original v x y a x' y' b) z z' k (hz k (mem_filter.mpr hj))
    · intro j hj
      rw [base_stack, base_stack]
      exact A.exterior i j hj _ _ _ _ _ _ hx hy

-- 读法：结论为 `let B := (share S A).backdrop (∑ z : (share S A).State, (∏ v, B.base.station v x y z) * S.scene.value P (B.param x y z)) = ∑ i : Y.State, S.value P (A.init x y i)`。这里调用 `sum_congr`。
/-- 普通网络的收缩对全部私有键与剩余连线求和，每项的重数均为一。

英文原文：Contracting the ordinary network sums all private keys and
residual wires, each with multiplicity one.
-/
theorem eval_share [Field F] [Fintype E] (P : ℕ) (x : Val a) (y : Val b) :
    let B := (share S A).backdrop
    (∑ z : (share S A).State, (∏ v, B.base.station v x y z) * S.scene.value P (B.param x y z)) =
      ∑ i : Y.State, S.value P (A.init x y i) := by
  refine ((share S A).eval x y (S.scene.value P)).trans ?_
  refine Eq.trans ?_ (sum_stack Y (M * t) S.hidden (A.init x y) (S.scene.value P))
  exact sum_congr (by ext; simp) (fun _ _ => rfl)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
end

/-!
# 输出表的局部操作数

**英文原文**

Local operands of the emitted tables
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Rules
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Finset Classical

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (L : Rules S) {d : E → ℕ} (p : Profile C d) (P : ℕ)

-- 读法：在后续公式中，`Line` 是 `S.Edge ⊕ (E × Fin M) ⊕ Layout.Grid M (Place C)` 的缩写。
abbrev Line (S : Sharing C a b Y) := S.Edge ⊕ (E × Fin M) ⊕ Layout.Grid M (Place C)
-- 读法：在后续公式中，`Vertex` 是 `S.Vertex ⊕ Layout.Grid M V` 的缩写。
abbrev Vertex (S : Sharing C a b Y) := S.Vertex ⊕ Layout.Grid M V

-- 读法：`keyTag` 的取值由 `(L.tag k).trans ⟨.key, fun _ _ h => Signal.key.inj h⟩` 给出。
def keyTag (k : K) : Y.state k ↪ Signal M r t :=
  (L.tag k).trans ⟨.key, fun _ _ h => Signal.key.inj h⟩

-- 读法：`frontTag` 的取值由 `⟨fun x => .front x.val, fun _ _ h => Subtype.ext (Signal.front.inj h)⟩` 给出。
def frontTag (e : ℕ) : Level r e ↪ Signal M r t :=
  ⟨fun x => .front x.val, fun _ _ h => Subtype.ext (Signal.front.inj h)⟩

-- 读法：`backTag` 的取值由 `⟨fun x => .back x.val, fun _ _ h => Subtype.ext (Signal.back.inj h)⟩` 给出。
def backTag (e : ℕ) : Level t e ↪ Signal M r t :=
  ⟨fun x => .back x.val, fun _ _ h => Subtype.ext (Signal.back.inj h)⟩

-- 读法：逐一匹配以下输入模式：`.inl e`、`.inr (.inl _) | .inr (.inr (.inl _))`、`.inr (.inr (.inr _))`。
def tagAt : (i : Line S) → (S.backdrop.emitted p P).state i ↪ Signal M r t
  | .inl e => L.keyTag e.1
  | .inr (.inl _) | .inr (.inr (.inl _)) => frontTag _
  | .inr (.inr (.inr _)) => backTag _

-- 读法：逐一匹配输入模式，例如 `.inl (.inl i)`、`.inl (.inr (.inl _))`、`.inl (.inr (.inr _))`、`.inr (.inl (v, _))`。
def program : Vertex S → Program F (Signal M r t)
  | .inl (.inl i) => load (L.label i)
  | .inl (.inr (.inl _)) => checkPairs
  | .inl (.inr (.inr _)) => fun _ _ _ => 1
  | .inr (.inl (v, _)) => chamber Signal.first ((firstList C v).map (firstPoint C P))
  | .inr (.inr (v, _)) => chamber Signal.second ((secondList C v).map (secondPoint C))

-- 读法：`reader` 的取值由 `.inl ⟨j.val, .inr (.inr ⟨i, L.seen i j.val j.property⟩)⟩` 给出。
def reader (i : Place C) (j : {k // k ∈ L.reads i}) : Line S :=
  .inl ⟨j.val, .inr (.inr ⟨i, L.seen i j.val j.property⟩)⟩

-- 读法：`front` 的取值由 `.inr (.inr (.inl (i, j)))` 给出。
def front (i : Place C) (j : Fin M) : Line S := .inr (.inr (.inl (i, j)))
-- 读法：`back` 的取值由 `.inr (.inr (.inr (i, j)))` 给出。
def back (i : Place C) (j : Fin M) : Line S := .inr (.inr (.inr (i, j)))

-- 读法：逐一匹配以下输入模式：`.inl i`、`.inr i`。
def first (j : Fin M) : Marked C → Line S
  | .inl i => .inr (.inl (i.1, j))
  | .inr i => front i j

-- 读法：逐一匹配输入模式，例如 `.inl (.inl i)`、`.inl (.inr (.inl v))`、`.inl (.inr (.inr _))`、`.inr (.inl (v, j))`。
def operands : Vertex S → List (Line S)
  | .inl (.inl i) => (L.reads i).attach.map (L.reader i) ++ List.ofFn (front i) ++ List.ofFn (back i)
  | .inl (.inr (.inl v)) => (hubReads S v).map .inl
  | .inl (.inr (.inr _)) => []
  | .inr (.inl (v, j)) => (firstList C v).map (first j)
  | .inr (.inr (v, j)) => (secondList C v).map (fun i => back i j)

-- 读法：对每个 `i ∈ L.operands v`，`(S.backdrop.emitted p P).src i = v`、`(S.backdrop.emitted p P).dst i = v` 至少有一项成立。
theorem incident (v : Vertex S) : ∀ i ∈ L.operands v,
    (S.backdrop.emitted p P).src i = v ∨ (S.backdrop.emitted p P).dst i = v := by
  rcases v with ((i|v|v) | (⟨v, j⟩|⟨v, j⟩))
  · simp only [operands, List.forall_mem_append, List.forall_mem_map, List.forall_mem_ofFn_iff]
    exact ⟨⟨fun _ _ => .inr rfl, fun _ => .inl rfl⟩, fun _ => .inl rfl⟩
  · simp only [operands, List.forall_mem_map]
    exact fun i hi => (hub_meets S v i hi).imp (congrArg Sum.inl) (congrArg Sum.inl)
  · simp [operands]
  · simp only [operands, firstList, secondList, List.forall_mem_map, List.forall_mem_append]
    refine ⟨fun _ _ => .inr rfl, fun k hk => ?_⟩
    let f (v : V) : Vertex S := .inr (.inl (v, j))
    exact (S.meets v k hk).imp (congrArg f) (congrArg f)
  · simp only [operands, secondList, List.forall_mem_map]
    exact fun _ _ => .inr rfl

variable (z : (S.backdrop.emitted p P).State)

-- 读法：`value` 的取值由 `L.tagAt p P j (z j)` 给出。
private def value (j : Line S) := L.tagAt p P j (z j)

-- 读法：输入 `i` 时返回 `z (.inl i)`。
private def ordinary : S.State := fun i => z (.inl i)

-- 读法：输入 `i` 时返回 `z (.inr (.inr i))`。
private def links : p.Legs := fun i => z (.inr (.inr i))

-- 读法：输入 `i` 时返回 `z (.inr (.inl i))`。
private def seam : p.Seams := fun i => z (.inr (.inl i))

-- 读法：`args` 的结果类型为 `Args M r t`。
private def args (i : Place C) : Args M r t :=
  ((L.reads i).map (fun k => L.tag k (S.localState i (ordinary p P z) k)),
    fun j => ((links p P z) (.inl (i, j))).val, fun j => ((links p P z) (.inr (i, j))).val)

-- 读法：`(L.operands (.inl (.inl i))).map (L.value p P z)` 等于 `symbols (L.args p P z i)`。这里调用 `List.map_congr_left`。
private theorem operands_item (i : Place C) :
    (L.operands (.inl (.inl i))).map (L.value p P z) = symbols (L.args p P z i) := by
  simp only [operands, symbols, args, List.map_append, List.map_map, List.map_ofFn]
  congr 2
  rw [← List.attach_map_val (l := L.reads i)]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, Sharing.localState, dite_eq_left (L.seen i k.val k.property)]
  rfl

-- 读法：`p.insertion (links p P z) (S.param x y (S.localState i (ordinary p P z))) i` 等于 `load (L.label i) ((L.left.ports i).map (bits a x)) ((L.right.ports i).map (bits b y)) (symbols (L.args p P z i))`。这里调用 `L.run`。
private theorem insert_eq (i : Place C) (x : Val a) (y : Val b) :
    p.insertion (links p P z) (S.param x y (S.localState i (ordinary p P z))) i =
      load (L.label i) ((L.left.ports i).map (bits a x)) ((L.right.ports i).map (bits b y))
        (symbols (L.args p P z i)) := by
  rw [load_symbols]
  exact L.run i x y (S.localState i (ordinary p P z))
    (p.joinA (p.first (seam p P z) (links p P z)) (.inr i)) (p.joinB (p.second (links p P z)) i)

-- 读法：用字段 `left`、`right`、`tag`、`program` 构造 `Script (S.backdrop.emitted p P) (Signal M r t)`。
abbrev script : Script (S.backdrop.emitted p P) (Signal M r t) where
  left := (L.left.lift (V ⊕ V)).lift (Layout.Grid M V)
  right := (L.right.lift (V ⊕ V)).lift (Layout.Grid M V)
  tag := L.tagAt p P
  program := L.program P
  reads := L.operands
  incident := L.incident p P
  run := by
    rintro ((i|v|v)|(⟨v, j⟩|⟨v, j⟩)) x y z
    · have he : (S.backdrop.emitted p P).station (.inl (.inl i)) x y z =
          p.insertion (links p P z) (S.param x y (S.localState i (ordinary p P z))) i := by
        simp [Sharing.checks]
        rfl
      rw [he, L.insert_eq]
      exact congrArg (load (L.label i) _ _) (L.operands_item p P z i).symm
    · have he : (S.backdrop.emitted p P).station (.inl (.inr (.inl v))) x y z =
          if S.checks (.inr (.inl v)) (ordinary p P z) then 1 else 0 := by
        simp
        rfl
      rw [he]
      change _ = checkPairs [] [] (((hubReads S v).map Sum.inl).map (L.value p P z))
      rw [List.map_map]
      exact (hub_eval S v L.keyTag (ordinary p P z) [] []).symm
    · change (S.backdrop.emitted p P).station (.inl (.inr (.inr v))) x y z = 1
      simp [Sharing.checks]
    · change p.form P (seam p P z) (links p P z) (.inl (v, j)) =
        chamber Signal.first ((firstList C v).map (firstPoint C P)) [] []
          (((firstList C v).map (first j)).map (L.value p P z))
      rw [List.map_map, chamber_eval]
      simp only [Profile.form]
      congr 1
      funext h
      cases h <;> rfl
    · change p.form P (seam p P z) (links p P z) (.inr (v, j)) =
        chamber Signal.second ((secondList C v).map (secondPoint C)) [] []
          (((secondList C v).map (fun i => back i j)).map (L.value p P z))
      rw [List.map_map, chamber_eval]
      rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Rules
end

/-!
# 所有输出配置共用的物理字典

运算使用输入所给的表册、两族带标记球面形式以及相等关系。解码器只依赖于所给的普通字母表或一个分块的能量，以及未填充时的宽度。

**英文原文**

One physical dictionary for all emitted configurations

The operations use the input book, the two families of marked sphere
forms, and equality. The decoders depend only on the supplied ordinary
alphabet or one chunk energy, and on the unpadded width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order
open Finset Classical Surface.Stage OAI.LinearAlgebra.MatrixExponent.Sphere.Layout OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage.Layout

variable {F : Type} [Field F] [Fintype F] {M r t : ℕ}

-- 读法：`operations` 的结果类型为 `Finset (Program F (Signal M r t))`。
def operations (book : Finset (Label F (M * r) (M * t))) (k : ℕ) :
    Finset (Program F (Signal M r t)) :=
  (book.image load) ∪ {checkPairs, fun _ _ _ => 1} ∪
    ((strings univ k).image (chamber Signal.first)) ∪
      ((strings univ k).image (chamber Signal.second))

-- 读法：`frontDecode` 的取值由 `decode _ _ (binaryCode _ _ (Chunk.card_le r e)) (Rules.frontTag e)` 给出。
def frontDecode (M r t e : ℕ) : Decoder (Signal M r t) :=
  decode _ _ (binaryCode _ _ (Chunk.card_le r e)) (Rules.frontTag e)

-- 读法：`backDecode` 的取值由 `decode _ _ (binaryCode _ _ (Chunk.card_le t e)) (Rules.backTag e)` 给出。
def backDecode (M r t e : ℕ) : Decoder (Signal M r t) :=
  decode _ _ (binaryCode _ _ (Chunk.card_le t e)) (Rules.backTag e)

-- 读法：`signals` 的结果类型为 `Finset (Decoder (Signal M r t))`。
def signals (r : ℕ) (codes : Finset (Decoder (Symbol (M * t)))) (N : ℕ) :
    Finset (Decoder (Signal M r t)) :=
  (codes.image (Decoder.map Signal.key)) ∪ ((range (N + 1)).image (frontDecode M r t)) ∪
    ((range (N + 1)).image (backDecode M r t))

-- 读法：`paddedSignals` 的取值由 `((range (N + 1)) ×ˢ signals r codes N).image fun i => Decoder.pad u i.1 i.2` 给出。
def paddedSignals (r : ℕ) (codes : Finset (Decoder (Symbol (M * t)))) (N u : ℕ) :=
  ((range (N + 1)) ×ˢ signals r codes N).image fun i => Decoder.pad u i.1 i.2

-- 读法：`dictionary` 的取值由 `menu (operations book k) (paddedSignals r codes N u) k N` 给出。
def dictionary (book : Finset (Label F (M * r) (M * t))) (codes : Finset (Decoder (Symbol (M * t))))
    (k N u : ℕ) : Finset (Table F) :=
  menu (operations book k) (paddedSignals r codes N u) k N

-- 读法：`(operations book k).card` 不超过 `book.card + 2 + 2 * (Fintype.card F + 1) ^ k`。这里调用 `card_insert_le`。
theorem count_operations (book : Finset (Label F (M * r) (M * t))) (k : ℕ) :
    (operations book k).card ≤ book.card + 2 + 2 * (Fintype.card F + 1) ^ k := by
  unfold operations
  have hh := card_strings (univ : Finset F) k
  simp only [card_univ] at hh
  rw [two_mul, ← add_assoc]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ (card_image_le.trans hh))
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ (card_image_le.trans hh))
  refine (card_union_le _ _).trans (Nat.add_le_add card_image_le ?_)
  exact (card_insert_le _ _).trans_eq (by rw [card_singleton])

-- 读法：`(paddedSignals r codes N u).card` 不超过 `(N + 1) * (codes.card + 2 * (N + 1))`。这里调用 `Nat.mul_le_mul_left`。
theorem count_signals (r : ℕ) (codes : Finset (Decoder (Symbol (M * t)))) (N u : ℕ) :
    (paddedSignals r codes N u).card ≤ (N + 1) * (codes.card + 2 * (N + 1)) := by
  refine card_image_le.trans ?_
  rw [card_product, card_range]
  apply Nat.mul_le_mul_left
  unfold signals
  rw [two_mul, ← add_assoc]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ (card_image_le.trans_eq (card_range _)))
  exact (card_union_le _ _).trans (Nat.add_le_add card_image_le (card_image_le.trans_eq (card_range _)))

-- 读法：要证明的命题是 `((N + 1) * (N + 2) ^ k) ^ 2 * (A + 2 + 2 * (H + 1) ^ k) * ((2 * k * ((N + 1) * (S + 2 * (N + 1))) + 1) ^ k) ^ 2 ≤ B ^ ((k + 12) ^ 3)`。
private theorem polynomial (B N k A S H : ℕ) (hB : 4 ≤ B)
    (hN : N + 2 ≤ B) (hA : A ≤ B) (hS : S ≤ B) (hH : H + 1 ≤ B) :
    ((N + 1) * (N + 2) ^ k) ^ 2 * (A + 2 + 2 * (H + 1) ^ k) * ((2 * k * ((N + 1) * (S + 2 * (N + 1))) + 1) ^ k) ^ 2 ≤
      B ^ ((k + 12) ^ 3) := by
  have hb : 0 < B := by omega
  have he : 1 ≤ B ^ k := Nat.one_le_pow _ _ hb
  have hk : k ≤ B ^ k := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)
  have h₁ : (N + 1) * (N + 2) ^ k ≤ B ^ (k + 1) := by rw [pow_succ']; gcongr; omega
  have h₂ : A + 2 + 2 * (H + 1) ^ k ≤ B ^ (k + 2) := by
    have := Nat.pow_le_pow_left hH k
    rw [pow_add]
    nlinarith [Nat.mul_le_mul_left (B ^ k) (show 4 * B ≤ B ^ 2 by nlinarith)]
  -- 推导：记下中间结论 `h₃`：`(N + 1) * (S + 2 * (N + 1)) ≤ B ^ 3`。
  have h₃ : (N + 1) * (S + 2 * (N + 1)) ≤ B ^ 3 := calc
    _ ≤ B * (B + 2 * B) := by gcongr <;> omega
    _ ≤ B ^ 3 := by nlinarith [Nat.mul_le_mul_right (B ^ 2) hB]
  have h₄ : 2 * k * ((N + 1) * (S + 2 * (N + 1))) + 1 ≤ B ^ (k + 4) := calc
    _ ≤ 2 * B ^ k * B ^ 3 + 1 := by gcongr
    _ ≤ B ^ (k + 4) := by
      rw [pow_add]
      nlinarith [Nat.mul_le_mul_right (B ^ k * B ^ 3) hB, Nat.one_le_pow 3 B hb]
  calc
    _ ≤ (B ^ (k + 1)) ^ 2 * B ^ (k + 2) * ((B ^ (k + 4)) ^ k) ^ 2 := by gcongr
    _ = B ^ ((k + 1) * 2 + (k + 2) + (k + 4) * (k * 2)) := by rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hb (by nlinarith [Nat.zero_le (k ^ 3)])

-- 读法：`(dictionary book codes k N u).card` 不超过 `(N + 2 + Fintype.card F + book.card + codes.card) ^ ((k + 12) ^ 3)`。这里调用 `count_operations`。
theorem dictionary_count (book : Finset (Label F (M * r) (M * t)))
    (codes : Finset (Decoder (Symbol (M * t)))) (k N u : ℕ) :
    (dictionary book codes k N u).card ≤
      (N + 2 + Fintype.card F + book.card + codes.card) ^ ((k + 12) ^ 3) := by
  have hf : 1 < Fintype.card F := Fintype.one_lt_card
  refine (menu_count _ _ _ _).trans (le_trans ?_ (polynomial _ N k book.card codes.card
    (Fintype.card F) (by omega) (by omega) (by omega) (by omega) (by omega)))
  gcongr
  · exact count_operations _ _
  · exact count_signals _ _ _ _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order
end

/-!
# 有序表保留全部宿主图、放置及计费信息

**英文原文**

Ordered tables preserve all host, placement and charge information
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order Finset Classical Packing Rounds

variable {F V α : Type} [Field F] [Fintype V] {a b : Wire} {d h u : ℕ}
  {G : Bundled F a b} {T : Trie V d} (H : Fanout G T (Cell h))
  (he : H.exterior) (hw : ∀ e, u ∣ G.width e) (D : Drawing H.route.net)

-- 读法：用字段 `frozen`、`exterior`、`separate` 构造 `Freeze D.diagram`。
private abbrev drawnFreeze : Freeze D.diagram where
  frozen v := T.fixed (H.place v).1
  exterior i := by rw [D.exterior]; cases i with
    | inl i => exact he.1 i
    | inr i => exact he.2 i
  separate i := by rw [D.source, D.target]; exact T.separate (H.edges i.1).2

-- 读法：用字段 `place`、`frozen`、`keep`、`N` 构造 `(drawnFreeze H he D).Frame (Node V d) h`。
private abbrev drawnFrame : (drawnFreeze H he D).Frame (Node V d) h where
  place := H.place
  frozen := T.fixed
  keep _ := Iff.rfl
  N := T.adj
  C := T.core
  ns _ _ := T.adj_symm
  cs _ _ := T.core_symm
  sub _ := filter_subset _ _
  group i := by rw [D.source, D.target]; exact (H.edges i.1).1
  edge i := mem_filter.mpr ⟨by rw [D.source, D.target]; exact (H.edges i.val.1).2, i.property⟩
  full i := by rw [D.source, D.target]; exact (H.edges i.1).2

-- 读法：用字段 `V`、`diagram`、`freeze`、`frame` 构造 `LocalTerm F a b h u`。
abbrev drawn : LocalTerm F a b h u where
  V := Node V d
  diagram := D.diagram
  freeze := drawnFreeze H he D
  frame := drawnFrame H he D
  one := H.injective
  width v w := by
    have h := H.route.net.divisible v w u (fun e _ _ => hw e.1)
    convert h using 1
    refine @Fintype.card_congr _ _ ?_ ?_ ?_
    exact Equiv.subtypeEquivRight fun i => by rw [D.source, D.target]; rfl
  charge := (H.term he hw).charge
  cover v := by rw [D.arity]; exact le_add_of_nonneg_right (by positivity)
  floor := (H.term he hw).floor

-- 读法：要证明的命题是 `Concentrated P (H.drawn he hw D) K c ℓ`。
theorem drawn_concentrated {n c K A R g ℓ : ℕ} {W : ℝ} (P : Input F a b h n A R g W)
    (hP : Concentrated P (H.term he hw) K c ℓ) : Concentrated P (H.drawn he hw D) K c ℓ :=
  ⟨hP.cells, hP.coreDegree, hP.fullDegree, hP.frozenCount, hP.frozenMax, hP.frozenSquare,
    hP.coreMax, hP.coreSum⟩

-- 读法：在后续公式中，`routed` 是 `(s.pad u).route (H.pad u).route` 的缩写。
abbrev routed (s : Script G α) (u : ℕ) := (s.pad u).route (H.pad u).route

-- 读法：在后续公式中，`ordered` 是 `(H.pad u).drawn he (G.divisible_pad u hu) (H.routed s u).drawing` 的缩写。
abbrev ordered (hu : 0 < u) (s : Script G α) : LocalTerm F a b h u :=
  (H.pad u).drawn he (G.divisible_pad u hu) (H.routed s u).drawing

-- 读法：`(H.ordered he hu s).diagram.eval` 等于 `G.eval`。通过传递性衔接 `H.routed` 与 `G.eval_pad`。
theorem eval_ordered (hu : 0 < u) (s : Script G α) : (H.ordered he hu s).diagram.eval = G.eval :=
  (H.routed s u).eval.trans ((H.pad u).route.eval_net.trans (G.eval_pad u))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-!
# 输出终止配置所需的数值假设

**英文原文**

Numerical hypotheses for emitting a terminal configuration
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
open Classical Finset Rounds
open SphereScale (Scales size budget q)

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k ℓ L B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}
  (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D)
  (hk : allocation g ℓ ≤ k)

include s hk in
-- 读法：`SphereScale.probes ℓ D + D ^ 5 ≤ D ^ k` 与 `SphereScale.chunks ℓ D ≤ D ^ k ∧ g ≤ D ^ k` 同时成立。这里调用 `Nat.mul_le_mul_right`。
theorem slots_fit : SphereScale.probes ℓ D + D ^ 5 ≤ D ^ k ∧
    SphereScale.chunks ℓ D ≤ D ^ k ∧ g ≤ D ^ k := by
  have h := s.bound
  have hpos := s.Dpos
  have he : 8 * (ℓ + 32) + 10 ≤ k :=
    (Nat.add_le_add_right (Nat.le_add_left _ _) 10).trans hk
  have hx : 1600 * D ≤ D ^ 2 := by nlinarith
  have hn : SphereScale.probes ℓ D ≤ D ^ (2 + (ℓ + 32) * 8) := by
    rw [SphereScale.probes, size, q, pow_add D 2, pow_mul]
    exact Nat.mul_le_mul_right _ hx
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 2 * D ^ (2 + (ℓ + 32) * 8) := by
        rw [two_mul]
        exact Nat.add_le_add hn (Nat.pow_le_pow_right hpos (by omega))
      _ ≤ D ^ (2 + (ℓ + 32) * 8 + 1) := by rw [pow_succ']; gcongr; omega
      _ ≤ _ := Nat.pow_le_pow_right hpos (by omega)
  · rw [SphereScale.chunks, q, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (by omega)
  · exact (show g ≤ D by have := s.degree; omega).trans (Nat.le_self_pow (by omega) _)

include hr s hM in
omit [Field F] [Fintype K] in
-- 读法：这里调用 `Nat.mul_le_mul_right`。
theorem term_count (hroom : ∀ v, (C v).stations.length ≤ SphereScale.room ℓ D g) :
    Fintype.card (Profile C e) ≤ (SphereScale.depth ℓ D g L (m * B) + 1) ^
      (SphereScale.chunks ℓ D * (Fintype.card E + 2 * SphereScale.room ℓ D g * Fintype.card V)) := by
  let N := SphereScale.depth ℓ D g L (m * B)
  have he (i : E) : e i ≤ N := (hr.seamEnergy i).trans (by
    unfold N SphereScale.depth
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ s.pos))
  have h₁ (i : Place C) : (item C i).a ≤ N :=
    ((Nat.le_mul_of_pos_left _ s.pos).trans (Nat.le_add_right _ _)).trans (hr.energy i)
  have h₂ (i : Place C) : (item C i).b ≤ N := (Nat.le_add_left _ _).trans (hr.energy i)
  refine (card_profile C e N he h₁ h₂).trans (Nat.pow_le_pow_right (Nat.zero_lt_succ _) ?_)
  have hc : Fintype.card (Place C) ≤ SphereScale.room ℓ D g * Fintype.card V := by
    rw [Fintype.card_sigma, mul_comm (SphereScale.room ℓ D g)]
    simpa using sum_le_card_nsmul univ (fun v => (C v).stations.length) _ (fun v _ => hroom v)
  rw [← hM, mul_assoc]
  gcongr

include hr s ha hb hM hk

-- 读法：要证明的命题是 `G.Budgets d ℓ e`。
theorem budgets (d : ℕ) : G.Budgets d ℓ e := by
  have hW : 0 ≤ W := le_trans (by positivity) hr.occupied
  have hD := s.Dpos
  have hbig : 122 * budget g ≤ k ∧ 17 * (budget g) ^ 2 ≤ k ∧ 14 ≤ k := by
    unfold allocation at hk
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [hk]
  have hk' : budget g ≤ k := by omega
  refine ⟨?_, ?_, ?_, hr.ordinary_small s, ?_, ?_, ?_, ?_, hr.chamber_load s ha hb hM, ?_⟩
  · refine le_trans ?_ hr.occupied
    gcongr
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hD)
  · exact fun v => (hr.keys v).trans (Nat.pow_le_pow_right s.Dpos hbig.2.2)
  · exact fun v => ((hr.seams v).trans (show budget g ≤ D by have := s.large; omega)).trans
      (Nat.le_self_pow (by omega) _)
  · exact hr.collectors.trans (by gcongr)
  · intro i hi
    -- 推导：记下中间结论 `hx`：`(S.exteriorLoad i : ℝ) ≤ budget g * (D : ℝ) * T`。
    have hx : (S.exteriorLoad i : ℝ) ≤ budget g * (D : ℝ) * T := by exact_mod_cast hr.exterior i hi
    calc
      _ ≤ 11 * (budget g : ℝ) * D * T := by unfold stationLoad; linarith only [hx, hr.leg_le s ha hb hM i]
      _ ≤ _ := by gcongr; exact_mod_cast (show 11 * budget g ≤ k by omega)
  · refine (hr.frozen_square s ha hb hM).trans ?_
    gcongr
    exact_mod_cast hbig.1
  · exact fun i hi => (hr.residue_le s ha hb hM i hi).trans (room hD (by decide))
  · refine (hr.total_load s ha hb hM).trans ?_
    calc
      _ ≤ (k : ℝ) * W := by gcongr; exact_mod_cast hbig.2.1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by simp)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
end

/-!
# 用同一组字典覆盖所有顶点和解码器

**英文原文**

Coverage of all vertices and decoders by the same dictionaries
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Rules
open Finset Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Surface.Stage

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (L : Rules S) {d : E → ℕ} (p : Profile C d) (P : ℕ)
  (book : Finset (Label F (M * r) (M * t))) (codes : Finset (Decoder (Symbol (M * t)))) (k N : ℕ)

-- 读法：`(L.script p P).signal e` 属于 `signals r codes N`。这里调用 `mem_union_left`。
theorem signal_mem (h : ∀ i, L.signal i ∈ codes)
    (hd : ∀ i, d i ≤ N) (ha : ∀ i, (item C i).a ≤ N) (hb : ∀ i, (item C i).b ≤ N)
    (e : Line S) : (L.script p P).signal e ∈ signals r codes N := by
  have ma (j : ℕ) (hj : j ≤ N) : frontDecode M r t j ∈ signals r codes N :=
    mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le hj))))
  have mb (j : ℕ) (hj : j ≤ N) : backDecode M r t j ∈ signals r codes N :=
    mem_union_right _ (mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le hj)))
  rcases e with e | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · change decode _ _ (Y.code e.1) (Signal.key ∘ L.tag e.1) ∈ _
    rw [decode_comp]
    exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (h e.1)))
  · exact ma _ ((Nat.le_of_lt_succ ((p.1 (.inl i)).val j).isLt).trans (hd i))
  · exact ma _ ((Nat.le_of_lt_succ ((p.1 (.inr i)).val j).isLt).trans (ha i))
  · exact mb _ ((Nat.le_of_lt_succ ((p.2 i).val j).isLt).trans (hb i))

variable (hl : ∀ v, (C v).stations.length + (C v).ports.length ≤ k)
include hl

-- 读法：`(L.script p P).program v` 属于 `operations book k`。这里调用 `mem_union_left`。
theorem program_mem [Fintype F] (h : ∀ i, L.label i ∈ book) (v : Vertex S) :
    (L.script p P).program v ∈ operations book k := by
  have hm (l : List F) (hn : l.length ≤ k) : l ∈ strings univ k :=
    mem_strings _ _ _ hn (fun _ _ => mem_univ _)
  rcases v with ((i|v|v)|(⟨v, j⟩|⟨v, j⟩))
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (h i))))
  · simp [operations, program]
  · simp [operations, program]
  · apply mem_union_left
    apply mem_union_right
    apply mem_image_of_mem
    apply hm
    simpa [firstList, secondList] using hl v
  · apply mem_union_right
    apply mem_image_of_mem
    apply hm
    simpa [secondList] using (Nat.le_add_right _ _).trans (hl v)

-- 读法：`((L.script p P).reads v).length` 不超过 `k`。这里调用 `length_hubReads`。
theorem reads_bound (h : ∀ i, (L.reads i).length + 2 * M ≤ k)
    (hg : ∀ v, 2 * (S.backdrop.emitted p P).degree v ≤ k) (v : Vertex S) :
    ((L.script p P).reads v).length ≤ k := by
  rcases v with ((i|v|v)|(⟨v, j⟩|⟨v, j⟩))
  · simpa [operands, two_mul, add_assoc] using h i
  · have hh := hg (.inl (.inr (.inl v)))
    rw [Backdrop.base_degree] at hh
    have hle : 2 * S.base.degree (.inr (.inl v)) ≤ k := (Nat.mul_le_mul_left _ (Nat.le_add_right ..)).trans hh
    simpa [operands] using (length_hubReads S v).trans hle
  · simp [operands]
  · simpa [operands, firstList, secondList] using hl v
  · simpa [operands, secondList] using (Nat.le_add_right _ _).trans (hl v)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Rules
end

/-!
# 布线和填充后字典与端口顺序的界仍然成立

**英文原文**

The dictionary and port-order bounds survive routing and padding
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order Packing Rounds Classical Finset

variable {F V α : Type} [Field F] [Fintype V] {a b : Wire} {d h u : ℕ}
  {G : Bundled F a b} {T : Trie V d} (H : Fanout G T (Cell h))
  (he : H.exterior) (hu : 0 < u)

omit [Fintype V] [Field F] in
-- 读法：`G.width e` 不超过 `G.arity (G.src e)`。
theorem source_arity (G : Bundled F a b) (e : G.E) : G.width e ≤ G.arity (G.src e) := by
  have h := single_le_sum (f := fun j => if G.src j = G.src e then G.width j else 0)
    (fun _ (_ : _ ∈ univ) => Nat.zero_le _) (mem_univ e)
  rw [ite_eq_left rfl] at h
  unfold Bundled.arity
  omega

variable {D W₀ R g C z ℓ : ℕ} {W : ℝ} {P : Input F a b h D W₀ R g W}
  (hc : Concentrated P (H.finish he hu) C z ℓ) (hD : 1 ≤ D) (hC : 1 ≤ C)

include hc hD hC in
-- 读法：`(H.pad u).route.net.arity v` 不超过 `C * D * W₀`。这里调用 `Nat.cast_le`。
theorem arity_max (v : Node G.V d) : (H.pad u).route.net.arity v ≤ C * D * W₀ := by
  have hl : ((H.pad u).route.net.arity v : ℝ) ≤ (H.finish he hu).charge v :=
    le_add_of_nonneg_right (by positivity)
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  refine hl.trans ?_
  by_cases hv : (H.finish he hu).freeze.frozen v
  · exact hc.frozenMax ⟨v, hv⟩
  · calc
      _ ≤ (H.finish he hu).charge v * (D : ℝ) ^ ℓ := le_mul_of_one_le_right
        ((Nat.cast_nonneg _).trans hl) (one_le_pow₀ (by exact_mod_cast hD))
      _ ≤ W₀ := hc.coreMax ⟨v, hv⟩
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.mul_pos hC hD)

include hc hD hC in
-- 读法：这里调用 `q.menu_mem`。
theorem ordered_properties (s : Script G α) (k N K : ℕ)
    (ops : Finset (Program F α)) (signals : Finset (Decoder α))
    (h₀ : checkPairs ∈ ops) (hop : ∀ v, s.program v ∈ ops)
    (hs : ∀ e, s.signal e ∈ signals) (hr : ∀ v, (s.reads v).length ≤ k)
    (hk : ∀ v, G.degree v ≤ K) (hR : 4 * K ≤ k) (hN : C * D * W₀ ≤ N) :
    Concentrated P (H.ordered he hu s) C z ℓ ∧
      (H.ordered he hu s).diagram.PortOrder (k + 2) ∧
      ∀ v, (H.ordered he hu s).diagram.table v ∈ menu ops
        (((range (N + 1)) ×ˢ signals).image fun i => Decoder.pad u i.1 i.2) k N := by
  let q := H.routed s u
  have ha (v) := (H.arity_max he hu hc hD hC v).trans hN
  have hd (v) : (H.pad u).route.net.degree v ≤ 2 * K := (H.pad u).fan_degree hk v
  have hdeg (v) : (H.pad u).route.net.degree v ≤ k := (hd v).trans (by omega)
  refine ⟨(H.pad u).drawn_concentrated he _ _ P hc, q.drawing.order (fun v => Nat.add_le_add_right (hdeg v) 2), ?_⟩
  apply q.menu_mem _ _ _ _ _ _ ha hdeg
  · rintro (v|v)
    · simpa [q] using hr v
    · exact ((s.pad u).length_route (H.pad u).route v).trans (by have := hd (.inr v); omega)
  · rintro (v|v)
    · exact hop v
    · exact h₀
  · intro e
    -- 推导：记下中间结论 `hh`：`G.width e.1 ≤ N`。
    have hh : G.width e.1 ≤ N := calc
      _ ≤ (G.pad u).width e.1 := Diagram.le_padWidth _ _
      _ ≤ (G.pad u).arity (G.src e.1) := source_arity (G.pad u) _
      _ = (H.pad u).route.net.arity (.inl (G.src e.1)) := (Routes.old_arity _ _).symm
      _ ≤ N := ha _
    exact mem_image.mpr ⟨(G.width e.1, s.signal e.1), mem_product.mpr ⟨mem_range.mpr (by omega), hs e.1⟩,
      (s.signal_pad u e.1).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end
