-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Hub
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Seating

/-!
# 每个全局轮廓对应一个选择器字

每个独立形状只写入一次，各坐标之和等于指定能量。空席位的能量为零，因此只能用零填充。

**英文原文**

One selector word per global profile

Each independent shape is written once. Its coordinates sum to the
specified energy. Empty seats have energy zero, which forces zero padding.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Finset Transcript Coloring

-- 读法：在后续公式中，`Digits` 是 `Fin M → B z` 的缩写。
abbrev Digits (M z : ℕ) := Fin M → B z

-- 读法：`tally` 的取值由 `∑ i, (p i).val` 给出。
def tally {M z : ℕ} (p : Digits M z) := ∑ i, (p i).val

namespace Pick
variable {M z : ℕ} {J X : Type} (seat : J ↪ X) (cost : J → ℕ)

-- 读法：`target` 的取值由 `Function.extend seat cost (fun _ => 0)` 给出。
def target := Function.extend seat cost (fun _ => 0)

-- 读法：`accepts` 的取值由 `∀ x, tally (p x) = target seat cost x` 给出。
def accepts (p : X → Digits M z) := ∀ x, tally (p x) = target seat cost x

variable (h : ∀ i, cost i < 2 ^ z)

-- 读法：`write` 的结果类型为 `X → Digits M z`。
def write (w : Layout.Shapes M cost) : X → Digits M z :=
  Function.extend seat (fun i j => ⟨((w i).val j).val,
    (Nat.le_of_lt_succ ((w i).val j).isLt).trans_lt (h i)⟩) (fun _ _ => 0)

-- 读法：`(write seat cost h w (seat i) j).val` 等于 `((w i).val j).val`。
theorem write_at (w : Layout.Shapes M cost) (i : J) (j : Fin M) :
    (write seat cost h w (seat i) j).val = ((w i).val j).val := by
  unfold write
  rw [seat.injective.extend_apply]

-- 读法：要证明的命题是 `accepts seat cost (write seat cost h w)`。按 `∃ j, seat j = x` 成立与否分情况。
theorem accepts_write (w : Layout.Shapes M cost) : accepts seat cost (write seat cost h w) := by
  intro x
  by_cases hx : ∃ j, seat j = x
  · obtain ⟨j, rfl⟩ := hx
    unfold target tally
    rw [seat.injective.extend_apply]
    simp only [write_at]
    exact (w j).property
  · simp [write, target, Function.extend, hx, tally]

-- 读法：`read` 的结果类型为 `Layout.Shapes M cost`。
def read (p : X → Digits M z) (hp : accepts seat cost p) : Layout.Shapes M cost :=
  fun i =>
    have he : tally (p (seat i)) = cost i := (hp _).trans (seat.injective.extend_apply _ _ i)
    ⟨fun j => ⟨(p (seat i) j).val, Nat.lt_succ_of_le ((single_le_sum
      (fun k _ => Nat.zero_le (p (seat i) k).val) (mem_univ j)).trans_eq he)⟩, he⟩

-- 读法：`write seat cost h (read seat cost p hp)` 等于 `p`。用函数外延性比较等号两侧在 `x j` 处的取值。
theorem write_read (p : X → Digits M z) (hp : accepts seat cost p) :
    write seat cost h (read seat cost p hp) = p := by
  funext x j
  by_cases hx : ∃ k, seat k = x
  · obtain ⟨k, rfl⟩ := hx
    exact Fin.ext (write_at _ _ _ _ _ _)
  · have he : tally (p x) = 0 := (hp _).trans (Function.extend_apply' _ _ _ hx)
    have hj : (p x j).val ≤ tally (p x) := single_le_sum (fun i _ => Nat.zero_le (p x i).val) (mem_univ j)
    have hz : p x j = 0 := Fin.ext (by change (p x j).val = 0; omega)
    simp [write, Function.extend, hx, hz]

-- 读法：用字段 `write`、`read`、`valid` 构造 `Selector (Layout.Shapes M cost) (X → Digits M z)`。
def selector : Selector (Layout.Shapes M cost) (X → Digits M z) where
  write := write seat cost h
  read p := if hp : accepts seat cost p then some (read seat cost p hp) else none
  valid p w := by
    constructor
    · split_ifs with hp
      · intro e; rw [← Option.some.inj e, write_read]
      · simp
    · rintro rfl
      rw [dite_eq_left (accepts_write _ _ _ _), Option.some.injEq]
      funext i
      apply Subtype.ext
      funext j
      exact Fin.ext (write_at _ _ _ _ _ _)

end Pick
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 不借助外部连线名称读取站点数据

操作数的顺序决定原始参数列表。局部处理器无须读取图内的线束编号。

**英文原文**

Reading station data without ambient wire names

Operand order determines the raw argument list. The bundle numbering
internal to the diagram need not be observed by a local processor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Script
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Transcript Finset

variable {F α : Type} [Field F] {a b : Wire} {G : Bundled F a b}
  (p : Script G α) (v : G.V)

-- 读法：`localValue` 的取值由 `if (∀ e, G.src e = v → f e ≠ none) ∧ (∀ e ∈ p.reads v, f e ≠ none) then p.program v x y ((p.reads v).filterMap f) else 0` 给出。
def localValue (x y : List Bool) (f : G.E → Option α) : F :=
  if (∀ e, G.src e = v → f e ≠ none) ∧ (∀ e ∈ p.reads v, f e ≠ none) then
    p.program v x y ((p.reads v).filterMap f) else 0

-- 读法：`p.drawing.recipe v x y` 等于 `p.localValue v x.1 y.1 f`。这里调用 `forall₂_congr`。
theorem recipe_eq (x y : View) (f : G.E → Option α)
    (h : ∀ e, G.src e = v ∨ G.dst e = v → (p.call v e).read x y = f e) :
    p.drawing.recipe v x y = p.localValue v x.1 y.1 f := by
  let q := p.call v
  have ag (es : List G.E) (he : ∀ e ∈ es, G.src e = v ∨ G.dst e = v) :
      (∀ c ∈ es.map q, c.read x y ≠ none) ↔ ∀ e ∈ es, f e ≠ none := by
    rw [List.forall_mem_map]
    exact forall₂_congr fun e hi => by rw [h e (he _ hi)]
  have he : ((p.reads v).map q).filterMap (fun c => c.read x y) = (p.reads v).filterMap f := by
    rw [List.filterMap_map]
    exact List.filterMap_congr fun i hi => h i (p.incident _ _ hi)
  change render _ _ _ x y = _
  unfold render localValue
  have hc := ag (checks v) (fun i hi => .inl (mem_filter.mp (mem_toList.mp hi)).2)
  have hr := ag _ (p.incident v)
  unfold q at hc hr he
  simp only [List.forall_mem_append, hc, hr, he]
  simp only [checks, mem_toList, mem_filter, mem_univ, true_and]

-- 读法：`token` 的取值由 `p.signal e (List.ofFn (fun i => if G.src e = v then w (.inl (.inr ⟨e, i⟩)) else w (.inr (.inr ⟨e, i⟩))))` 给出。
def token (w : p.drawing.diagram.End → Bool) (e : G.E) :=
  p.signal e (List.ofFn (fun i => if G.src e = v then w (.inl (.inr ⟨e, i⟩))
    else w (.inr (.inr ⟨e, i⟩))))

-- 读法：结论为 `p.drawing.diagram.weight v (w ∘ .inl) (w ∘ .inr) = p.localValue v ((p.left.ports v).map fun i => w (.inl (.inl i))) ((p.right.ports v).map fun i => w (.inr (.inl i))) (p.token v w)`。
theorem weight_eq (w : p.drawing.diagram.End → Bool) :
    p.drawing.diagram.weight v (w ∘ .inl) (w ∘ .inr) =
      p.localValue v ((p.left.ports v).map fun i => w (.inl (.inl i)))
        ((p.right.ports v).map fun i => w (.inr (.inl i))) (p.token v w) := by
  let l₀ := fun i => w (.inl (.inl i))
  let r₀ := fun i => w (.inr (.inl i))
  let l₁ := fun i => w (.inl (.inr i))
  let r₁ := fun i => w (.inr (.inr i))
  let l := p.source.view G.width v l₀ l₁
  let r := p.target.view G.width v r₀ r₁
  -- 推导：记下中间结论 `hl`：`w ∘ Sum.inl = Sum.elim l₀ l₁`。
  have hl : w ∘ Sum.inl = Sum.elim l₀ l₁ := funext fun i => by cases i <;> rfl
  have hr : w ∘ Sum.inr = Sum.elim r₀ r₁ := funext fun i => by cases i <;> rfl
  have he (e : G.E) (he : G.src e = v ∨ G.dst e = v) :
      (p.call v e).read l r = p.token v w e := by
    unfold l r token
    by_cases h : G.src e = v
    · subst v
      simp only [call, ite_true, Call.read, Bool.false_eq_true, ite_false]
      rw [read_side]
    · have ht := he.resolve_left h
      subst v
      simp only [call, ite_eq_right h, Call.read, ite_true]
      rw [read_side]
  rw [hl, hr]
  calc
    _ = p.drawing.recipe v l r := congrArg₂ (p.drawing.recipe v)
      (p.source.read G.width v l₀ l₁) (p.target.read G.width v r₀ r₁)
    _ = p.localValue v l.1 r.1 (p.token v w) := p.recipe_eq v l r _ he
    _ = _ := congrArg₂ (fun a b => p.localValue v a b _) (p.left.values v l₀) (p.right.values v r₀)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Script
end

/-!
# 输出带标签网络的顶点星形邻域

**英文原文**

Printing the star of a labeled network
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring

variable {F α A : Type} {a b : Wire} {d : ℕ}

-- 读法：`side` 的取值由 `cond s G.dst G.src` 给出。
def side (G : Bundled F a b) (s : Bool) : G.E → G.V := cond s G.dst G.src

-- 读法：结构的字段包括 `lane`、`unique`、`near`。
structure Names (G : Bundled F a b) (A : Type) (d : ℕ) where
  lane : G.E → A
  unique : ∀ s i j, side G s i = side G s j → lane i = lane j → i = j
  near : G.V → G.V → B d

namespace Names
variable {G : Bundled F a b} (N : Names G A d)

-- 读法：当 `h : ∃ i, side G s i = v ∧ N.lane i = k` 成立时取 `some h.choose`，否则取 `none`。
def resident (v : G.V) (s : Bool) (k : A) : Option G.E :=
  if h : ∃ i, side G s i = v ∧ N.lane i = k then some h.choose else none

-- 读法：`N.resident (side G s i) s (N.lane i)` 等于 `some i`。
theorem resident_at (s : Bool) (i : G.E) :
    N.resident (side G s i) s (N.lane i) = some i := by
  have h : ∃ j, side G s j = side G s i ∧ N.lane j = N.lane i := ⟨i, rfl, rfl⟩
  rw [resident, dite_eq_left h, N.unique s _ _ h.choose_spec.1 h.choose_spec.2]

-- 读法：`side G s i = v` 与 `N.lane i = k` 同时成立。这里调用 `Option.some.inj`。
theorem resident_spec {v : G.V} {s : Bool} {k : A} {i : G.E}
    (he : N.resident v s k = some i) : side G s i = v ∧ N.lane i = k := by
  unfold resident at he
  split_ifs at he with h
  exact (Option.some.inj he) ▸ h.choose_spec

-- 读法：`target` 的取值由 `N.near (side G s i) (side G (!s) i)` 给出。
def target (s : Bool) (i : G.E) := N.near (side G s i) (side G (!s) i)

variable [Field F] (p : Order.Script G α)

-- 读法：`extSize` 的取值由 `cond s (p.right.ports v).length (p.left.ports v).length` 给出。
def extSize (v : G.V) (s : Bool) := cond s (p.right.ports v).length (p.left.ports v).length

-- 读法：用字段 `ext`、`link`、`value` 构造 `Star F A d`。
def star (v : G.V) : Star F A d where
  ext := extSize p v
  link s k := (N.resident v s k).map (fun i => (N.target s i, G.width i))
  value x y r := p.localValue v x y (fun e => p.signal e (r (decide (G.src e ≠ v)) (N.lane e)))

-- 读法：`(N.star p (side G s i)).link s (N.lane i)` 等于 `some (N.target s i, G.width i)`。
theorem link_at (s : Bool) (i : G.E) :
    (N.star p (side G s i)).link s (N.lane i) = some (N.target s i, G.width i) := by
  simp only [star, N.resident_at, Option.map_some]

-- 读法：存在 `i`，`side G s i = v` 与 `N.lane i = k ∧ N.target s i = w ∧ G.width i = n` 同时成立。
theorem link_spec {v s k w n} (h : (N.star p v).link s k = some (w, n)) :
    ∃ i, side G s i = v ∧ N.lane i = k ∧ N.target s i = w ∧ G.width i = n := by
  obtain ⟨i, hi, he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, (N.resident_spec hi).1, (N.resident_spec hi).2, Prod.mk.inj he⟩

end Names
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 输出位置实例记录中的等宽区段元数据

**英文原文**

Uniform-width span metadata of the printed occurrence records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Assembly

-- 读法：结构的字段包括 `m`、`d`、`h`、`e`、`ℓ`。
structure Engine (F A : Type) where
  m : ℕ
  d : ℕ
  h : ℕ
  e : ℕ
  ℓ : ℕ
  cap : ℕ
  ix : Band A cap ↪ B e
  decode : B ℓ → Pattern F d 0 e

variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}

-- 读法：在后续公式中，`Engine.scheme` 是 `⟨U.m, U.d, U.h, 0, U.e, U.ℓ, U.decode⟩` 的缩写。
abbrev Engine.scheme (U : Engine F A) : Scheme F :=
  ⟨U.m, U.d, U.h, 0, U.e, U.ℓ, U.decode⟩

-- 读法：结构的字段包括 `vertex`、`pos`、`width`、`bound`、`active`。
/-- 每个位置实例分配一个宿主槽位，并共用一张导航表。

英文原文：A single host slot per occurrence and a shared navigation table.
-/
structure Frame (U : Engine F A) (r : U.scheme.format.obj) (N : Names G A U.d)
    (p : Order.Script G α) (u : ℕ) where
  vertex : G.V ↪ U.scheme.Vtx
  pos : 0 < u
  width : ∀ i, u ∣ G.width i
  bound : ∀ i, G.width i / u ≤ U.cap
  active : ∀ v, U.scheme.pattern r (vertex v) = (N.star p v).pattern U.ix u
  inactive : ∀ v ∉ Set.range vertex, U.scheme.pattern r v = Star.vacant
  address : ∀ s i, let v := vertex (side G s i)
    ((r v.1).1 (N.target s i), v.2.1, (0 : B 0)) = vertex (side G (!s) i)

namespace Frame

variable {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

-- 读法：在后续公式中，`exterior` 是 `(H.vertex v, U.ix (s, none))` 的缩写。
abbrev exterior (v : G.V) (s : Bool) : U.scheme.Span := (H.vertex v, U.ix (s, none))
-- 读法：在后续公式中，`unit` 是 `(H.vertex (side G s i), U.ix (s, some (N.lane i, j)))` 的缩写。
abbrev unit (s : Bool) (i : G.E) (j : Fin U.cap) : U.scheme.Span :=
  (H.vertex (side G s i), U.ix (s, some (N.lane i, j)))

-- 读法：`U.scheme.width r (H.exterior v s) = Names.extSize p v s` 与 `U.scheme.direction r (H.exterior v s) = s ∧ U.scheme.peer r (H.exterior v s) = none` 同时成立。
theorem exterior_info (v : G.V) (s : Bool) :
    U.scheme.width r (H.exterior v s) = Names.extSize p v s ∧
      U.scheme.direction r (H.exterior v s) = s ∧ U.scheme.peer r (H.exterior v s) = none := by
  simp only [Scheme.width, Scheme.direction, Scheme.peer, H.active, Star.pattern, Star.desc_ext,
    Option.map_none, and_true]
  rfl

-- 读法：`U.scheme.width r (H.unit s i j) = u` 与 `U.scheme.direction r (H.unit s i j) = s ∧ U.scheme.peer r (H.unit s i j) = some (H.unit (!s) i j)` 同时成立。
theorem unit_info (s : Bool) (i : G.E) (j : Fin U.cap) (hj : j.val < G.width i / u) :
    U.scheme.width r (H.unit s i j) = u ∧ U.scheme.direction r (H.unit s i j) = s ∧
      U.scheme.peer r (H.unit s i j) = some (H.unit (!s) i j) := by
  have h := Star.desc_link _ U.ix u (N.link_at p s i) j hj
  simp only [Scheme.width, Scheme.direction, Scheme.peer, H.active, Star.pattern, h,
    true_and, Option.map_some, H.address]

-- 读法：`(U.scheme.pattern r (H.vertex (side G s i))).peer 0 (H.unit s i j).2` 等于 `some (N.target s i, 0, (H.unit (!s) i j).2)`。
theorem unit_local (s : Bool) (i : G.E) (j : Fin U.cap) (hj : j.val < G.width i / u) :
    (U.scheme.pattern r (H.vertex (side G s i))).peer 0 (H.unit s i j).2 =
      some (N.target s i, 0, (H.unit (!s) i j).2) := by
  rw [H.active]
  exact congrArg (fun a => a.2.2) (Star.desc_link _ U.ix u (N.link_at p s i) j hj)

-- 读法：`(∃ v s, q = H.exterior v s)`、`∃ s i j, j.val < G.width i / u ∧ q = H.unit s i j` 至少有一项成立。按 `v ∈ Set.range H.vertex` 成立与否分情况。
theorem classify (q : U.scheme.Span)
    (h : 0 < U.scheme.width r q ∨ U.scheme.peer r q ≠ none) :
    (∃ v s, q = H.exterior v s) ∨ ∃ s i j, j.val < G.width i / u ∧ q = H.unit s i j := by
  obtain ⟨v, q⟩ := q
  by_cases hv : v ∈ Set.range H.vertex
  swap
  · simp [Scheme.width, Scheme.peer, H.inactive v hv, Star.vacant] at h
  obtain ⟨v, rfl⟩ := hv
  have hh : 0 < ((N.star p v).desc U.ix u q).1 ∨ ((N.star p v).desc U.ix u q).2.2 ≠ none := by
    simpa only [Scheme.width, Scheme.peer, H.active, Star.pattern, ne_eq, Option.map_eq_none_iff] using h
  rcases Star.active _ _ _ hh with ⟨s, rfl⟩|⟨s, l, j, k, w, rfl, he, hj⟩
  · exact .inl ⟨v, s, rfl⟩
  · obtain ⟨i, rfl, rfl, _, rfl⟩ := N.link_spec p he
    exact .inr ⟨s, i, j, hj, rfl⟩

-- 读法：存在 `s i j`，`j.val < G.width i / u` 与 `a = H.unit s i j ∧ b = H.unit (!s) i j` 同时成立。
theorem peer_spec (a b : U.scheme.Span) (h : U.scheme.peer r a = some b) :
    ∃ s i j, j.val < G.width i / u ∧ a = H.unit s i j ∧ b = H.unit (!s) i j := by
  rcases H.classify a (.inr (by rw [h]; simp)) with ⟨v, s, rfl⟩ | ⟨s, i, j, hj, rfl⟩
  · rw [(H.exterior_info v s).2.2] at h; cases h
  · exact ⟨s, i, j, hj, rfl, Option.some.inj (h.symm.trans (H.unit_info s i j hj).2.2)⟩

include H in
-- 读法：要证明的命题是 `U.scheme.Proper r`。
theorem proper : U.scheme.Proper r := by
  intro a b h
  obtain ⟨s, i, j, hj, rfl, rfl⟩ := H.peer_spec a b h
  obtain ⟨h₁, h₂, _⟩ := H.unit_info s i j hj
  obtain ⟨h₃, h₄, h₅⟩ := H.unit_info (!s) i j hj
  refine ⟨by simpa using h₅, h₁.trans h₃.symm, ?_⟩
  rw [h₂, h₄]
  cases s <;> decide

end Frame
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 单位区段中的有序物理比特偏移量

**英文原文**

Ordered physical bit offsets in unit spans
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Assembly

variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}
  {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

-- 读法：在后续公式中，`SidePin` 是 `(Σ v, Fin (Names.extSize p v s)) ⊕ G.Bit` 的缩写。
abbrev SidePin (p : Order.Script G α) (s : Bool) := (Σ v, Fin (Names.extSize p v s)) ⊕ G.Bit
-- 读法：在后续公式中，`SourcePin` 是 `Σ s : Bool, SidePin p s` 的缩写。
abbrev SourcePin (p : Order.Script G α) := Σ s : Bool, SidePin p s

-- 读法：用字段 `left_inv`、`right_inv` 构造 `(Σ s, X s) ≃ X false ⊕ X true`。
private def boolIndex (X : Bool → Type) : (Σ s, X s) ≃ X false ⊕ X true where
  toFun
    | ⟨false, x⟩ => .inl x
    | ⟨true, x⟩ => .inr x
  invFun
    | .inl x => ⟨false, x⟩
    | .inr x => ⟨true, x⟩
  left_inv := by rintro ⟨_|_, _⟩ <;> rfl
  right_inv := by rintro (_|_) <;> rfl

-- 读法：`toEnds` 的取值由 `(boolIndex (SidePin p)).trans ((p.left.enum.full.sumCongr (.refl _)).sumCongr (p.right.enum.full.sumCongr (.refl _)))` 给出。
def toEnds (p : Order.Script G α) : SourcePin p ≃ p.drawing.diagram.End :=
  (boolIndex (SidePin p)).trans ((p.left.enum.full.sumCongr (.refl _)).sumCongr
    (p.right.enum.full.sumCongr (.refl _)))

include H in
-- 读法：`j.val / u` 严格小于 `G.width e / u`。这里调用 `Nat.div_lt_iff_lt_mul`。
theorem unit_lt (e : G.E) (j : Fin (G.width e)) : j.val / u < G.width e / u := by
  apply (Nat.div_lt_iff_lt_mul H.pos).mpr
  rw [Nat.div_mul_cancel (H.width e)]
  exact j.isLt

-- 读法：`unitIndex` 的取值由 `⟨j.val / u, (H.unit_lt e j).trans_le (H.bound e)⟩` 给出。
def unitIndex (e : G.E) (j : Fin (G.width e)) : Fin U.cap :=
  ⟨j.val / u, (H.unit_lt e j).trans_le (H.bound e)⟩

-- 读法：`outer` 的结果类型为 `U.scheme.Pin r`。
def outer (v : G.V) (s : Bool) (j : Fin (Names.extSize p v s)) : U.scheme.Pin r :=
  ⟨H.exterior v s, ⟨j.val, by rw [(H.exterior_info v s).1]; exact j.isLt⟩⟩

-- 读法：`inner` 的结果类型为 `U.scheme.Pin r`。
def inner (s : Bool) (e : G.E) (j : Fin (G.width e)) : U.scheme.Pin r :=
  ⟨H.unit s e (H.unitIndex e j), ⟨j.val % u, by
    rw [(H.unit_info s e (H.unitIndex e j) (H.unit_lt e j)).1]
    exact Nat.mod_lt _ H.pos⟩⟩

-- 读法：逐一匹配以下输入模式：`⟨s, .inl ⟨v, j⟩⟩`、`⟨s, .inr ⟨e, j⟩⟩`。
def put : SourcePin p → U.scheme.Pin r
  | ⟨s, .inl ⟨v, j⟩⟩ => H.outer v s j
  | ⟨s, .inr ⟨e, j⟩⟩ => H.inner s e j

-- 读法：`U.scheme.direction r (H.put q).1` 等于 `q.1`。这里调用 `H.exterior_info`。
theorem put_dir (q : SourcePin p) : U.scheme.direction r (H.put q).1 = q.1 := by
  rcases q with ⟨s, ⟨v, j⟩ | ⟨e, j⟩⟩
  · exact (H.exterior_info v s).2.1
  · exact (H.unit_info s e _ (H.unit_lt e j)).2.1

-- 读法：`H.put` 是单射。
private theorem injective : Function.Injective H.put := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have ht : s = t := (H.put_dir ⟨s, i⟩).symm.trans (h ▸ H.put_dir ⟨t, j⟩)
  subst t
  have hv := congrArg (fun p => p.1.1) h
  have hk := congrArg (fun p => p.1.2) h
  have ho := congrArg (fun p => p.2.val) h
  rcases i with ⟨v, i⟩|⟨e, i⟩ <;> rcases j with ⟨w, j⟩|⟨f, j⟩
  · have he : v = w := H.vertex.injective hv
    subst w
    -- 推导：记下中间结论 `hi`：`i = j`。
    have hi : i = j := Fin.ext ho
    rw [hi]
  · cases U.ix.injective hk
  · cases U.ix.injective hk
  · have hkey := Prod.mk.inj (Option.some.inj (Prod.mk.inj (U.ix.injective hk)).2)
    have he : e = f := N.unique s _ _ (H.vertex.injective hv) hkey.1
    subst f
    have hdiv : i.val / u = j.val / u := congrArg Fin.val hkey.2
    change i.val % u = j.val % u at ho
    have hij : i = j := Fin.ext (by
      rw [← Nat.mod_add_div i.val u, ho, hdiv, Nat.mod_add_div])
    rw [hij]

omit [Field F] in
-- 读法：`x` 等于 `y`。使用 `Sigma.ext` 给出的结论。
private theorem pin_ext {x y : U.scheme.Pin r} (h : x.1 = y.1) (hv : x.2.val = y.2.val) : x = y :=
  Sigma.ext h ((Fin.heq_ext_iff (congrArg (U.scheme.width r) h)).mpr hv)

-- 读法：`H.put` 是满射。
private theorem surjective : Function.Surjective H.put := by
  rintro ⟨q, j⟩
  rcases H.classify q (.inl (Nat.zero_lt_of_lt j.isLt)) with ⟨v, s, rfl⟩|⟨s, e, i, hi, rfl⟩
  · let k : Fin (Names.extSize p v s) := ⟨j.val, lt_of_lt_of_eq j.isLt (H.exterior_info v s).1⟩
    exact ⟨⟨s, .inl ⟨v, k⟩⟩, pin_ext rfl rfl⟩
  · have hj : j.val < u := lt_of_lt_of_eq j.isLt (H.unit_info s e i hi).1
    let k : Fin (G.width e) := ⟨u * i.val + j.val, by
      have h := Nat.mul_le_mul_right u hi
      rw [Nat.div_mul_cancel (H.width e), Nat.succ_mul, mul_comm i.val] at h
      omega⟩
    have hk : H.unitIndex e k = i := Fin.ext (by
      change (u * i.val + j.val) / u = i.val
      rw [Nat.mul_add_div H.pos, Nat.div_eq_of_lt hj, add_zero])
    refine ⟨⟨s, .inr ⟨e, k⟩⟩, pin_ext (congrArg (H.unit s e) hk) ?_⟩
    change (u * i.val + j.val) % u = j.val
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

-- 读法：`ends` 的取值由 `(toEnds p).symm.trans (Equiv.ofBijective _ ⟨H.injective, H.surjective⟩)` 给出。
def ends : p.drawing.diagram.End ≃ U.scheme.Pin r :=
  (toEnds p).symm.trans (Equiv.ofBijective _ ⟨H.injective, H.surjective⟩)

-- 读法：`H.ends (toEnds p q)` 等于 `H.put q`。
theorem at_end (q : SourcePin p) : H.ends (toEnds p q) = H.put q := by
  rw [ends, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

-- 读法：`U.scheme.direction r (H.ends q).1` 等于 `q.isRight`。
theorem directed_end (q : p.drawing.diagram.End) : U.scheme.direction r (H.ends q).1 = q.isRight := by
  obtain ⟨⟨s, v⟩, rfl⟩ := (toEnds p).surjective q
  rw [H.at_end, H.put_dir]
  cases s <;> rfl

-- 读法：`(H.ends q).1.1` 等于 `H.vertex (p.drawing.diagram.station q)`。对 `s` 分类讨论。
theorem owner (q : p.drawing.diagram.End) : (H.ends q).1.1 = H.vertex (p.drawing.diagram.station q) := by
  obtain ⟨⟨s, q⟩, rfl⟩ := (toEnds p).surjective q
  rw [H.at_end]
  rcases q with ⟨v, j⟩|⟨e, j⟩
  · cases s
    · exact congrArg H.vertex ((p.source.owner G.width (.inl (p.left.enum.get v j))).trans
        (p.left.enum.owner v j)).symm
    · exact congrArg H.vertex ((p.target.owner G.width (.inl (p.right.enum.get v j))).trans
        (p.right.enum.owner v j)).symm
  · cases s
    · exact congrArg H.vertex (p.drawing.source ⟨e, j⟩).symm
    · exact congrArg H.vertex (p.drawing.target ⟨e, j⟩).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
end

/-!
# 内在操作数程序

普通运算按顺序读取列表。相等性检验只依赖于被比较的数对组成的集合，即便编码无效也是如此。

**英文原文**

Intrinsic operand programs

Ordinary operations observe a list in order. Equality tests observe
only the set of compared pairs, even on invalid codes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

-- 读法：在后续公式中，`Policy` 是 `List Bool → List Bool → (A → Option α) → F` 的缩写。
abbrev Policy (F α A : Type) := List Bool → List Bool → (A → Option α) → F
variable {F α A B : Type} [Field F]

-- 读法：当 `∀ i ∈ xs, f i ≠ none` 成立时取 `p x y (xs.filterMap f)`，否则取 `0`。
def operation (p : Program F α) (xs : List A) : Policy F α A :=
  fun x y f => if ∀ i ∈ xs, f i ≠ none then p x y (xs.filterMap f) else 0

-- 读法：当 `∀ i ∈ s, f i.1 ≠ none ∧ f i.1 = f i.2` 成立时取 `1`，否则取 `0`。
def tests (s : Set (A × A)) : Policy F α A :=
  fun _ _ f => if ∀ i ∈ s, f i.1 ≠ none ∧ f i.1 = f i.2 then 1 else 0

-- 读法：`operation p (xs.map g) x y f` 等于 `operation p xs x y (f ∘ g)`。
theorem operation_reindex (p : Program F α) (xs : List A) (g : A → B) (f : B → Option α)
    (x y : List Bool) :
    operation p (xs.map g) x y f = operation p xs x y (f ∘ g) := by
  simp only [operation, List.forall_mem_map, List.filterMap_map, Function.comp_apply]

-- 读法：`operation p xs x y f` 等于 `operation p xs x y g`。
theorem operation_congr (p : Program F α) (xs : List A) (x y : List Bool)
    (f g : A → Option α) (h : ∀ i ∈ xs, f i = g i) :
    operation p xs x y f = operation p xs x y g := by
  have ht : (∀ i ∈ xs, f i ≠ none) ↔ ∀ i ∈ xs, g i ≠ none :=
    forall₂_congr fun i hi => by rw [h i hi]
  simp only [operation, ht, List.filterMap_congr h]

-- 读法：`checkPairs x y (a :: b :: l)` 等于 `if a = b then checkPairs (F := F) x y l else 0`。按 `a = b <;> simp [checkPairs, equalPairs, h]` 成立与否分情况。
private theorem test_cons (a b : α) (l : List α) (x y : List Bool) :
    checkPairs x y (a :: b :: l) = if a = b then checkPairs (F := F) x y l else 0 := by
  by_cases h : a = b <;> simp [checkPairs, equalPairs, h]

-- 读法：`operation checkPairs (a :: b :: l) x y f` 等于 `if f a ≠ none ∧ f a = f b then operation (F := F) checkPairs l x y f else 0`。
private theorem op_cons (a b : A) (l : List A) (x y : List Bool) (f : A → Option α) :
    operation checkPairs (a :: b :: l) x y f =
      if f a ≠ none ∧ f a = f b then operation (F := F) checkPairs l x y f else 0 := by
  unfold operation
  simp only [List.forall_mem_cons, List.filterMap_cons]
  cases f a <;> cases f b <;> simp [test_cons]
  split_ifs <;> simp_all

-- 读法：`operation (F := F) (α := α) checkPairs (pairs l)` 等于 `tests {i | i ∈ l}`。用函数外延性比较等号两侧在 `x y f` 处的取值。
theorem operation_pairs (l : List (A × A)) :
    operation (F := F) (α := α) checkPairs (pairs l) = tests {i | i ∈ l} := by
  funext x y f
  induction l with
  | nil => simp [pairs, operation, tests, checkPairs, equalPairs]
  | cons p l ih =>
    change operation checkPairs (p.1 :: p.2 :: pairs l) x y f = _
    rw [op_cons, ih]
    simp only [tests, Set.mem_ofPred_eq, List.forall_mem_cons, ite_and]
    congr!

-- 读法：`operation (F := F) (α := α) checkPairs ((pairs l).map id)` 等于 `tests {i | ∃ j ∈ l, Prod.map id id j = i}`。对 `l` 作归纳。
theorem reindex_pairs (l : List (A × A)) (id : A → B) :
    operation (F := F) (α := α) checkPairs ((pairs l).map id) =
      tests {i | ∃ j ∈ l, Prod.map id id j = i} := by
  have h : (pairs l).map id = pairs (l.map (Prod.map id id)) := by
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (fun xs => id a.1 :: id a.2 :: xs) ih
  rw [h, operation_pairs]
  simp only [List.mem_map]

-- 读法：`policy` 的取值由 `operation (p.program v) ((p.reads v).map lane)` 给出。
def policy {a b : Wire} {G : Bundled F a b} (p : Script G α) (lane : G.E → A) (v : G.V) :=
  operation (p.program v) ((p.reads v).map lane)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 所输出星形邻域的局部性

关联通道的集合、各通道端点的局部名称以及处理操作数的局部程序共同决定输出。`printStar` 的参数中没有顶点或通道的绝对编号。

**英文原文**

Locality of a printed star

The set of incident channels, their local endpoint names and the local
operand program determine the output. Absolute vertex and channel IDs
are absent from the arguments of `printStar`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

-- 读法：结构的字段包括 `key`、`side`、`width`、`decoder`。
structure Arc (α A X : Type) where
  key : A
  side : Bool → X
  width : ℕ
  decoder : Decoder α

variable {F α A X : Type} [Field F] {a b : Wire} {G : Bundled F a b} {d : ℕ}

-- 读法：`touches` 表示以下条件：`G.src e = v`、`G.dst e = v` 至少有一项成立。
def touches (G : Bundled F a b) (v : G.V) (e : G.E) : Prop := G.src e = v ∨ G.dst e = v

omit [Field F] in
-- 读法：要证明的命题是 `touches G (side G s e) e`。
theorem touches_side (G : Bundled F a b) (s : Bool) (e : G.E) : touches G (side G s e) e := by
  cases s <;> simp [touches, side]

-- 读法：`Unique` 的取值由 `∀ v e f, touches G v e → touches G v f → lane e = lane f → e = f` 给出。
def Unique (G : Bundled F a b) (lane : G.E → A) :=
  ∀ v e f, touches G v e → touches G v f → lane e = lane f → e = f

-- 读法：`Unique.names` 的取值由 `⟨lane, fun s i j he => h _ i j (touches_side _ s i) (he ▸ touches_side _ s j), near⟩` 给出。
def Unique.names (lane : G.E → A) (h : Unique G lane) (near : G.V → G.V → B d) : Names G A d :=
  ⟨lane, fun s i j he => h _ i j (touches_side _ s i) (he ▸ touches_side _ s j), near⟩

-- 读法：`arc` 的取值由 `⟨lane e, fun s => name (side G s e), G.width e, p.signal e⟩` 给出。
def arc (p : Script G α) (lane : G.E → A) (name : G.V → X) (e : G.E) : Arc α A X :=
  ⟨lane e, fun s => name (side G s e), G.width e, p.signal e⟩

-- 读法：`cloud` 的取值由 `arc p lane name '' {e | touches G v e}` 给出。
def cloud (p : Script G α) (lane : G.E → A) (name : G.V → X) (v : G.V) :=
  arc p lane name '' {e | touches G v e}

-- 读法：当 `h : ∃ c ∈ s, c.key = k` 成立时取 `some h.choose`，否则取 `none`。
def lookup (s : Set (Arc α A X)) (k : A) :=
  if h : ∃ c ∈ s, c.key = k then some h.choose else none

-- 读法：`lookup s c.key` 等于 `some c`。
theorem lookup_at {s : Set (Arc α A X)} (h : Set.InjOn Arc.key s) {c : Arc α A X} (hc : c ∈ s) :
    lookup s c.key = some c := by
  have he : ∃ a ∈ s, a.key = c.key := ⟨c, hc, rfl⟩
  rw [lookup, dite_eq_left he, h he.choose_spec.1 hc he.choose_spec.2]

-- 读法：`c ∈ s` 与 `c.key = k` 同时成立。这里调用 `Option.some.inj`。
theorem lookup_mem {s : Set (Arc α A X)} {c : Arc α A X} {k} (h : lookup s k = some c) :
    c ∈ s ∧ c.key = k := by
  unfold lookup at h
  split_ifs at h with he
  exact Option.some.inj h ▸ he.choose_spec

-- 读法：用字段 `ext`、`link`、`value` 构造 `Star F A d`。
def printStar (v : X) (s : Set (Arc α A X)) (near : X → X → B d)
    (ext : Bool → ℕ) (policy : Policy F α A) : Star F A d where
  ext := ext
  link b k := (lookup s k).bind fun c =>
    if c.side b = v then some (near v (c.side (!b)), c.width) else none
  value x y r :=
    let f k := (lookup s k).bind fun c => c.decoder (r (decide (c.side false ≠ v)) k)
    if ∀ c ∈ s, c.side false = v → f c.key ≠ none then policy x y f else 0

-- 读法：`N.star p v` 等于 `printStar (name v) (cloud p N.lane name v) near (Names.extSize p v) (policy p N.lane v)`。
theorem star_eq (N : Names G A d) (p : Script G α) (v : G.V) (name : G.V → X)
    (hu : Unique G N.lane)
    (hd : ∀ e, touches G v e → ∀ b, name (side G b e) = name v → side G b e = v)
    (near : X → X → B d)
    (hn : ∀ b e, side G b e = v → near (name v) (name (side G (!b) e)) = N.target b e) :
    N.star p v = printStar (name v) (cloud p N.lane name v) near
      (Names.extSize p v) (policy p N.lane v) := by
  let s := cloud p N.lane name v
  let t := arc p N.lane name
  have inj : Set.InjOn Arc.key s := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ h
    rw [hu v e f he hf h]
  have atKey (e) (he : touches G v e) : lookup s (N.lane e) = some (t e) :=
    lookup_at inj ⟨e, he, rfl⟩
  have side_eq (e) (he : touches G v e) (b) : (t e).side b = name v ↔ side G b e = v :=
    ⟨hd e he b, congrArg name⟩
  unfold Names.star printStar
  congr 1
  · funext b k
    change (N.resident v b k).map _ = (lookup s k).bind _
    cases he : N.resident v b k with
    | some e =>
      -- 推导：从 `N.resident_spec he` 中取出 `hq, rfl`。
      obtain ⟨hq, rfl⟩ := N.resident_spec he
      have hv : touches G v e := hq ▸ touches_side G b e
      rw [atKey _ hv, Option.bind_some, ite_eq_left ((side_eq _ hv b).mpr hq)]
      simp only [Option.map_some, t, arc, hn b e hq]
    | none =>
      cases hk : lookup s k with
      | none => rfl
      | some q =>
        obtain ⟨⟨e, hv, rfl⟩, rfl⟩ := lookup_mem hk
        have hx : (t e).side b ≠ name v := by
          intro h
          have hv' := (side_eq _ hv _).mp h
          have := N.resident_at b e
          change N.resident v b (N.lane e) = none at he
          rw [hv', he] at this
          contradiction
        exact (ite_eq_right hx).symm
  · funext x y r
    let f k := (lookup s k).bind fun c => c.decoder (r (decide (c.side false ≠ name v)) k)
    let g e := p.signal e (r (decide (G.src e ≠ v)) (N.lane e))
    have hf (e) (he : touches G v e) : f (N.lane e) = g e := by
      unfold f
      rw [atKey _ he, Option.bind_some]
      simp only [ne_eq, side_eq e he]
      rfl
    have hc : (∀ c ∈ s, c.side false = name v → f c.key ≠ none) ↔
        ∀ e, G.src e = v → g e ≠ none := by
      constructor
      · intro h e he
        rw [← hf e (.inl he)]
        exact h (t e) ⟨e, .inl he, rfl⟩ (congrArg name he)
      · rintro h _ ⟨e, he, rfl⟩ ht
        exact (hf e he).symm ▸ h e (hd e he _ ht)
    change p.localValue v x y g =
      if ∀ c ∈ s, c.side false = name v → f c.key ≠ none then policy p N.lane v x y f else 0
    have hv := operation_congr (p.program v) (p.reads v) x y (f ∘ N.lane) g
      (fun i hi => hf i (p.incident _ _ hi))
    simp only [hc, policy, operation_reindex, hv]
    simp only [Script.localValue, operation, ite_and]
    congr!

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 带类型的通道清单中的局部路径

一条路径依循原通道两端的宿主分支。其短名称包括原有名称和跳步索引。原宿主的分支映射中，只需读取与该通道关联的部分。

**英文原文**

Local paths in a typed channel inventory

A path follows the two host branches of the old channel. Its short
name contains the old name and a hop index. Only the incident part of
the old host's branch map is needed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

variable {F X Y A α I V : Type} {a b : Wire} {d : ℕ} {G : Bundled F a b} {T : Trie V d}

-- 读法：在后续公式中，`legs` 是 `(d + 1) + (d + 1)` 的缩写。
abbrev legs (d : ℕ) := (d + 1) + (d + 1)
-- 读法：在后续公式中，`Layer` 是 `A × Fin (legs d + 1)` 的缩写。
abbrev Layer (A : Type) (d : ℕ) := A × Fin (legs d + 1)
-- 读法：在后续公式中，`Branch` 是 `X → X → Fin (d + 1) → Address d` 的缩写。
abbrev Branch (X : Type) (d : ℕ) := X → X → Fin (d + 1) → Address d

-- 读法：`root` 的取值由 `Sum.elim id Prod.fst` 给出。
def root : Node X d → X := Sum.elim id Prod.fst

-- 读法：`lift` 的取值由 `Sum.map f (Prod.map f id)` 给出。
def lift (f : X → Y) : Node X d → Node Y d := Sum.map f (Prod.map f id)

-- 读法：`u` 等于 `v`。对 `he` 分类讨论。
theorem lift_eq {f : X → Y} {u v : Node X d} (h : f (root u) = f (root v) → root u = root v)
    (he : lift f u = lift f v) : u = v := by
  rcases u with u|⟨u, i⟩ <;> rcases v with v|⟨v, j⟩
  · exact congrArg Sum.inl (h (Sum.inl.inj he))
  · cases he
  · cases he
  · obtain ⟨hu, hi⟩ := Prod.mk.inj (Sum.inr.inj he)
    exact congrArg Sum.inr (Prod.ext (h hu) hi)

namespace Arc
variable (c : Arc α A X) (w : Branch X d)

-- 读法：`branch` 的取值由 `(c.side s, j, w (c.side s) (c.side (!s)) j)` 给出。
def branch (s : Bool) (j : Fin (d + 1)) : Relay X d :=
  (c.side s, j, w (c.side s) (c.side (!s)) j)

-- 读法：`via` 的取值由 `Fin.append (c.branch w false) (fun j => c.branch w true j.rev)` 给出。
def via := Fin.append (c.branch w false) (fun j => c.branch w true j.rev)

-- 读法：逐一匹配以下输入模式：`false`、`true`。
def endAt (i : Fin (legs d + 1)) : Bool → Node X d
  | false => Fin.cases (.inl (c.side false)) (fun j => .inr (c.via w j)) i
  | true => Fin.lastCases (.inl (c.side true)) (fun j => .inr (c.via w j)) i

-- 读法：`hop` 的取值由 `⟨(c.key, i), c.endAt w i, Diagram.padWidth u c.width, Order.Decoder.pad u c.width c.decoder⟩` 给出。
def hop (u : ℕ) (i : Fin (legs d + 1)) : Arc α (Layer A d) (Node X d) :=
  ⟨(c.key, i), c.endAt w i, Diagram.padWidth u c.width, Order.Decoder.pad u c.width c.decoder⟩

end Arc

variable (H : Fanout G T I) (u : ℕ) (lane : G.E → A)

-- 读法：`layer` 的取值由 `(lane i.1, i.2)` 给出。
def layer (i : (H.pad u).route.Hop) : Layer A d := (lane i.1, i.2)

-- 读法：要证明的命题是 `touches G ((H.pad u).route.via e i).1 e`。对 `i` 作归纳，采用 `Fin.addCases` 的归纳原则。
theorem via_root (e : G.E) (i : Fin (legs d)) :
    touches G ((H.pad u).route.via e i).1 e := by
  induction i using Fin.addCases
  · simp only [Fin.append_left]; exact .inl rfl
  · simp only [Fin.append_right]; exact .inr rfl

variable [Field F]

-- 读法：要证明的命题是 `touches G (root (side (H.pad u).route.net s i)) i.1`。对 `s` 分类讨论。
theorem end_root (s : Bool) (i : (H.pad u).route.Hop) :
    touches G (root (side (H.pad u).route.net s i)) i.1 := by
  obtain ⟨e, j⟩ := i
  cases s
  · induction j using Fin.cases with
    | zero => exact .inl rfl
    | succ j => exact via_root H u e j
  · change touches G (root ((H.pad u).route.dst ⟨e, j⟩)) e
    induction j using Fin.lastCases with
    | last => simp only [Routes.dst, Fin.lastCases_last]; exact .inr rfl
    | cast j => simp only [Routes.dst, Fin.lastCases_castSucc]; exact via_root H u e j

-- 读法：要证明的命题是 `touches G (root v) i.1`。这里调用 `end_root`。
theorem contact_root {v : Node G.V d} {i : (H.pad u).route.Hop}
    (h : touches (H.pad u).route.net v i) : touches G (root v) i.1 := by
  rcases h with rfl | rfl
  · exact end_root H u false i
  · exact end_root H u true i

-- 读法：要证明的命题是 `Unique (H.pad u).route.net (layer H u lane)`。
theorem unique_layer (hu : Unique G lane) : Unique (H.pad u).route.net (layer H u lane) := by
  rintro v ⟨e, i⟩ ⟨f, j⟩ he hf eq
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj eq
  have heq : e = f := hu _ _ _ (contact_root H u he) (contact_root H u hf) h₁
  subst f
  exact congrArg (Sigma.mk e) h₂

variable (p : Order.Script G α) (name : G.V → X) (w : Branch X d)

-- 读法：`Follows` 表示以下条件：对每个 `s`，`w (name (side G s e)) (name (side G (!s) e))` 等于 `T.address (H.site (side G s e)).1 (H.site (side G (!s) e)).1`。
def Follows (e : G.E) : Prop :=
  ∀ s, w (name (side G s e)) (name (side G (!s) e)) =
    T.address (H.site (side G s e)).1 (H.site (side G (!s) e)).1

omit [Field F] in
-- 读法：`Prod.map name id ((H.pad u).route.via e i)` 等于 `(arc p lane name e).via w i`。对 `i` 作归纳，采用 `Fin.addCases` 的归纳原则。
theorem map_via (e : G.E) (h : Follows H name w e) (i : Fin (legs d)) :
    Prod.map name id ((H.pad u).route.via e i) = (arc p lane name e).via w i := by
  unfold Follows at h
  induction i using Fin.addCases
  all_goals simp only [Arc.via, Fin.append_left, Fin.append_right, Arc.branch, arc, h]
  all_goals rfl

-- 读法：`lift name (side (H.pad u).route.net s ⟨e, i⟩)` 等于 `(arc p lane name e).endAt w i s`。对 `s` 分类讨论。
theorem map_end (e : G.E) (h : Follows H name w e) (i : Fin (legs d + 1)) (s : Bool) :
    lift name (side (H.pad u).route.net s ⟨e, i⟩) = (arc p lane name e).endAt w i s := by
  cases s
  · induction i using Fin.cases with
    | zero => rfl
    | succ j => exact congrArg Sum.inr (map_via H u lane p name w e h j)
  · change lift name ((H.pad u).route.dst ⟨e, i⟩) = _
    induction i using Fin.lastCases with
    | last => simp only [Routes.dst, Fin.lastCases_last, Arc.endAt]; rfl
    | cast j =>
      simp only [Routes.dst, Fin.lastCases_castSucc, Arc.endAt]
      exact congrArg Sum.inr (map_via H u lane p name w e h j)

-- 读法：`arc ((p.pad u).route (H.pad u).route) (layer H u lane) (lift name) ⟨e, i⟩` 等于 `(arc p lane name e).hop w u i`。这里调用 `p.signal_pad`。
theorem map_arc (e : G.E) (h : Follows H name w e) (i : Fin (legs d + 1)) :
    arc ((p.pad u).route (H.pad u).route) (layer H u lane) (lift name) ⟨e, i⟩ =
      (arc p lane name e).hop w u i := by
  apply congrArg₂ (fun side dec => Arc.mk (lane e, i) side (Diagram.padWidth u (G.width e)) dec)
  · exact funext (map_end H u lane p name w e h i)
  · exact p.signal_pad u e

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 原星形邻域决定布线后所关联的通道

**英文原文**

The incident routed channels are determined by the original star
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout

variable {F X A α I V : Type} [Field F] {a b : Wire} {d : ℕ} {G : Bundled F a b}
  {T : Trie V d}

-- 读法：`Same` 的取值由 `∀ e, touches G v e → ∀ s, name (side G s e) = name v → side G s e = v` 给出。
def Same (name : G.V → X) (v : G.V) :=
  ∀ e, touches G v e → ∀ s, name (side G s e) = name v → side G s e = v

omit [Field F] in
-- 读法：`q` 等于 `v`。
theorem Same.ends {name : G.V → X} {v q : G.V} (h : Same name v)
    (e : G.E) (hv : touches G v e) (hq : touches G q e) (he : name q = name v) : q = v := by
  rcases hq with rfl | rfl
  · exact h e hv false he
  · exact h e hv true he

-- 读法：`channels` 的取值由 `{c | ∃ a ∈ s, ∃ i, a.hop w u i = c ∧ (c.side false = z ∨ c.side true = z)}` 给出。
def channels (z : Node X d) (w : Branch X d) (u : ℕ) (s : Set (Arc α A X)) :=
  {c | ∃ a ∈ s, ∃ i, a.hop w u i = c ∧ (c.side false = z ∨ c.side true = z)}

variable (H : Fanout G T I) (u : ℕ) (lane : G.E → A)
  (p : Order.Script G α) (name : G.V → X) (w : Branch X d)

-- 读法：`side (H.pad u).route.net b ⟨e, i⟩` 等于 `v`。使用 `lift_eq` 给出的结论。
theorem reflect_end (v : Node G.V d) (hs : Same name (root v))
    (e : G.E) (he : touches G (root v) e) (i : Fin (legs d + 1)) (b : Bool)
    (hh : lift name (side (H.pad u).route.net b ⟨e, i⟩) = lift name v) :
    side (H.pad u).route.net b ⟨e, i⟩ = v :=
  lift_eq (hs.ends e he (end_root H u b ⟨e, i⟩)) hh

-- 读法：要证明的命题是 `Same (G := (H.pad u).route.net) (lift name) v`。这里调用 `reflect_end`。
theorem same_layer (v : Node G.V d) (hs : Same name (root v)) :
    Same (G := (H.pad u).route.net) (lift name) v := by
  rintro ⟨e, i⟩ he b hh
  exact reflect_end H u name v hs e (contact_root H u he) i b hh

-- 读法：`cloud ((p.pad u).route (H.pad u).route) (layer H u lane) (lift name) v` 等于 `channels (lift name v) w u (cloud p lane name (root v))`。这里调用 `he.imp`。
theorem routed_cloud (v : Node G.V d) (hs : Same name (root v))
    (hf : ∀ e, touches G (root v) e → Follows H name w e) :
    cloud ((p.pad u).route (H.pad u).route) (layer H u lane) (lift name) v =
      channels (lift name v) w u (cloud p lane name (root v)) := by
  ext c
  constructor
  · rintro ⟨⟨e, i⟩, he, rfl⟩
    have h := contact_root H u he
    refine ⟨_, ⟨e, h, rfl⟩, i, (map_arc H u lane p name w e (hf e h) i).symm, ?_⟩
    exact he.imp (congrArg (lift name)) (congrArg (lift name))
  · rintro ⟨_, ⟨e, he, rfl⟩, i, rfl, h⟩
    have heq := map_arc H u lane p name w e (hf e he) i
    refine ⟨⟨e, i⟩, ?_, heq⟩
    rw [← heq] at h
    exact h.imp (reflect_end H u name v hs e he i false) (reflect_end H u name v hs e he i true)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 读取原操作数或比较中继处的两次跳转

**英文原文**

Reading the original operands or comparing the two hops at a relay
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

variable {F X A α I V : Type} [Field F] {a b : Wire} {d : ℕ} {G : Bundled F a b}
  {T : Trie V d}

-- 读法：`endpoint` 的取值由 `(i, if ∃ c ∈ s, c.key = i ∧ c.side false = x then 0 else Fin.last _)` 给出。
def endpoint (x : X) (s : Set (Arc α A X)) (i : A) : Layer A d :=
  (i, if ∃ c ∈ s, c.key = i ∧ c.side false = x then 0 else Fin.last _)

-- 读法：`through` 的取值由 `{p | ∃ c ∈ s, ∃ i, c.via w i = x ∧ ((c.key, i.castSucc), (c.key, i.succ)) = p}` 给出。
def through (x : Relay X d) (w : Branch X d) (s : Set (Arc α A X)) :
    Set (Layer A d × Layer A d) :=
  {p | ∃ c ∈ s, ∃ i, c.via w i = x ∧ ((c.key, i.castSucc), (c.key, i.succ)) = p}

-- 读法：`routePolicy` 的取值由 `match x with | .inl v => fun l r f => p l r (f ∘ endpoint v s) | .inr v => tests (through v w s)` 给出。
def routePolicy (x : Node X d) (w : Branch X d) (s : Set (Arc α A X))
    (p : Policy F α A) : Policy F α (Layer A d) :=
  match x with
  | .inl v => fun l r f => p l r (f ∘ endpoint v s)
  | .inr v => tests (through v w s)

variable (H : Fanout G T I) (u : ℕ) (lane : G.E → A)
  (p : Order.Script G α) (name : G.V → X) (w : Branch X d)

omit [Field F] in
-- 读法：`layer H u lane (Script.endpoint (H.pad u).route v e)` 等于 `endpoint (name v) (cloud p lane name v) (lane e)`。
private theorem endpoint_eq (hu : Unique G lane) (v : G.V) (hs : Same name v)
    (e : G.E) (he : touches G v e) :
    layer H u lane (Script.endpoint (H.pad u).route v e) =
      endpoint (name v) (cloud p lane name v) (lane e) := by
  have eq : (∃ c ∈ cloud p lane name v, c.key = lane e ∧ c.side false = name v) ↔ G.src e = v := by
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, hk, hp⟩
      rw [hu _ _ _ hi he hk] at hp
      exact hs e he false hp
    · intro h
      exact ⟨_, ⟨e, he, rfl⟩, rfl, congrArg name h⟩
  unfold endpoint Script.endpoint
  simp only [eq]
  split_ifs <;> rfl

omit [Field F] in
-- 读法：结论为 `{i | ∃ j ∈ Script.matched (H.pad u).route v, Prod.map (layer H u lane) (layer H u lane) j = i} = through (Prod.map name id v) w (cloud p lane name v.1)`。
private theorem through_eq (v : Relay G.V d) (hs : Same name v.1)
    (hf : ∀ e, touches G v.1 e → Follows H name w e) :
    {i | ∃ j ∈ Script.matched (H.pad u).route v, Prod.map (layer H u lane) (layer H u lane) j = i} =
      through (Prod.map name id v) w (cloud p lane name v.1) := by
  ext i
  constructor
  · rintro ⟨_, hh, rfl⟩
    obtain ⟨⟨e, j⟩, hj, rfl⟩ := List.mem_map.mp hh
    have he : (H.pad u).route.via e j = v := by simpa only [Finset.mem_toList, Script.visits, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hv : touches G v.1 e := by rw [← he]; apply via_root
    exact ⟨_, ⟨e, hv, rfl⟩, j, (map_via H u lane p name w e (hf e hv) j).symm.trans
      (congrArg (Prod.map name id) he), rfl⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, j, hj, rfl⟩
    have e' := (map_via H u lane p name w e (hf e he) j).trans hj
    have eq : (H.pad u).route.via e j = v := Prod.ext
      (hs.ends e he (via_root H u e j) (congrArg Prod.fst e')) (congrArg (fun t : Relay X d => t.2) e')
    refine ⟨Script.ends (H.pad u).route ⟨e, j⟩, List.mem_map_of_mem ?_, rfl⟩
    simpa only [Finset.mem_toList, Script.visits, Finset.mem_filter, Finset.mem_univ, true_and] using eq

-- 读法：`policy ((p.pad u).route (H.pad u).route) (layer H u lane) v` 等于 `routePolicy (lift name v) w (cloud p lane name (root v)) (policy p lane (root v))`。对 `v` 分类讨论。
theorem policy_routed (hu : Unique G lane) (v : Node G.V d) (hs : Same name (root v))
    (hf : ∀ e, touches G (root v) e → Follows H name w e) :
    policy ((p.pad u).route (H.pad u).route) (layer H u lane) v =
      routePolicy (lift name v) w (cloud p lane name (root v)) (policy p lane (root v)) := by
  cases v with
  | inl v =>
    have eq : ((p.reads v).map (Script.endpoint (H.pad u).route v)).map (layer H u lane) =
        ((p.reads v).map lane).map (endpoint (name v) (cloud p lane name v)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left (fun i hi => endpoint_eq H u lane p name hu v hs i (p.incident _ _ hi))
    funext x y f
    change operation (p.program v) (((p.reads v).map (Script.endpoint (H.pad u).route v)).map _) x y f = _
    rw [eq, operation_reindex]
    rfl
  | inr v =>
    change operation checkPairs ((pairs (Script.matched (H.pad u).route v)).map (layer H u lane)) = _
    rw [reindex_pairs, through_eq H u lane p name w v hs hf]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end
