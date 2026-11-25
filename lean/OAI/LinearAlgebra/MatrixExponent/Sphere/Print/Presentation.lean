-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Traces
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Pins
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History

/-!
# 完整有序图式的有向单位宽度表示

**英文原文**

A directed, unit-width presentation of the full ordered diagram
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Assembly

variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}
  {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

-- 读法：用字段 `vertex`、`ends`、`station`、`value` 构造 `Seating U.scheme r p.drawing.diagram`。
def seating : Seating U.scheme r p.drawing.diagram where
  vertex := H.vertex
  ends := H.ends
  station := H.owner
  value := H.value
  empty v hv t := by
    have he (q : Pattern F U.d 0 U.e) (h : q = Star.vacant)
        (x : ∀ s, Fin (q.width v.2.2 s) → Bool) : q.value v.2.2 x = 1 := by subst q; rfl
    exact he _ (H.inactive v hv) _

-- 读法：用字段 `toSeating`、`proper`、`internal`、`input` 构造 `U.scheme.Presentation r p.drawing.diagram`。
def presentation : U.scheme.Presentation r p.drawing.diagram where
  toSeating := H.seating.seat
  proper := H.proper
  internal e := by
    rw [H.seating.ends_eq]
    change U.scheme.Joins r (H.ends (.inl (.inr e))) (H.ends (.inr (.inr e)))
    rw [H.lbit, H.rbit]
    exact ⟨(H.unit_info false e.1 _ (H.unit_lt _ e.2)).2.2, rfl⟩
  input i := by
    obtain ⟨⟨v, j⟩, rfl⟩ := p.left.enum.full.surjective i
    rw [H.seating.ends_eq]
    change U.scheme.peer r (H.ends (.inl (.inl (p.left.enum.get v j)))).1 = none
    rw [H.left v j]
    exact (H.exterior_info v false).2.2
  output i := by
    obtain ⟨⟨v, j⟩, rfl⟩ := p.right.enum.full.surjective i
    rw [H.seating.ends_eq]
    change U.scheme.peer r (H.ends (.inr (.inl (p.right.enum.get v j)))).1 = none
    rw [H.right v j]
    exact (H.exterior_info v true).2.2

-- 读法：`H.presentation.vertex` 等于 `H.vertex`。两端由定义化简为同一项。
theorem vertex_eq : H.presentation.vertex = H.vertex := rfl

-- 读法：`H.presentation.toSeating.ends` 等于 `H.ends`。使用 `H.seating.ends_eq` 给出的结论。
theorem ends_eq : H.presentation.toSeating.ends = H.ends := H.seating.ends_eq

-- 读法：要证明的命题是 `H.presentation.Directed`。这里调用 `H.directed_end`。
theorem directed : H.presentation.Directed := by
  intro q
  rw [H.ends_eq]
  exact H.directed_end q

include H in
-- 读法：`U.scheme.width r i` 等于 `u`。这里调用 `H.unit_info`。
theorem uniform (i : U.scheme.Span) (hi : (U.scheme.peer r i).isSome) : U.scheme.width r i = u := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hi
  obtain ⟨s, e, t, ht, rfl, _⟩ := H.peer_spec _ _ hj
  exact (H.unit_info s e t ht).1

-- 读法：`(U.scheme.pattern r (H.vertex v)).peer 0 i` 等于 `some (N.near v w, 0, j)`。这里调用 `H.unit_local`。
theorem neighbor (v w : G.V) (i j : B U.e)
    (h : U.scheme.peer r (H.vertex v, i) = some (H.vertex w, j)) :
    (U.scheme.pattern r (H.vertex v)).peer 0 i = some (N.near v w, 0, j) := by
  obtain ⟨s, e, l, hl, hi, hj⟩ := H.peer_spec _ _ h
  obtain ⟨hv, rfl⟩ := Prod.mk.inj hi
  obtain ⟨hw, rfl⟩ := Prod.mk.inj hj
  rw [H.vertex.injective hv, H.vertex.injective hw]
  exact H.unit_local s e l hl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
end

/-!
# 为一个站点的全部物理后代设置局部输出程序

**英文原文**

A local printer for all the physical descendants of a station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Classical

-- 读法：结构的字段包括 `ext`、`lines`、`command`。
structure Inventory (F α A X : Type) where
  ext : Bool → ℕ
  lines : Set (Arc α A X)
  command : Policy F α A

variable {F X A α I V : Type} [Field F] {a b : Wire} {d z : ℕ} {G : Bundled F a b}
  {T : Trie V d}

-- 读法：`describe` 的取值由 `⟨Names.extSize p v, cloud p lane name v, policy p lane v⟩` 给出。
def describe (p : Order.Script G α) (lane : G.E → A) (name : G.V → X) (v : G.V) :
    Inventory F α A X := ⟨Names.extSize p v, cloud p lane name v, policy p lane v⟩

-- 读法：`Inventory.star` 的取值由 `printStar x (channels x w u c.lines) near (if x.isLeft then c.ext else fun _ => 0) (routePolicy x w c.lines c.command)` 给出。
def Inventory.star (c : Inventory F α A X) (x : Node X d) (u : ℕ) (w : Branch X d)
    (near : Node X d → Node X d → B z) : Star F (Layer A d) z :=
  printStar x (channels x w u c.lines) near (if x.isLeft then c.ext else fun _ => 0)
    (routePolicy x w c.lines c.command)

variable (H : Fanout G T I) (u : ℕ) (lane : G.E → A) (hu : Unique G lane)
  (idx : Node G.V d → Node G.V d → B z)

-- 读法：在后续公式中，`routeNames` 是 `Unique.names (layer H u lane) (unique_layer H u lane hu) idx` 的缩写。
abbrev routeNames : Names (H.pad u).route.net (Layer A d) z := Unique.names (layer H u lane) (unique_layer H u lane hu) idx

-- 读法：`(routeNames H u lane hu idx).star ((p.pad u).route (H.pad u).route) v` 等于 `(describe p lane name (root v)).star (lift name v) u w near`。这里调用 `star_eq`。
/-- 给定清单、其端点上的分支赋值和邻点索引，即可在该站点的任一宿主槽位重建整个星形邻域。

英文原文：The inventory, branch assignments on its endpoints and neighbor
indices suffice for the whole star on any of the station's host slots.
-/
theorem printed (p : Order.Script G α) (name : G.V → X) (v : Node G.V d)
    (hs : Same name (root v)) (w : Branch X d)
    (hf : ∀ e, touches G (root v) e → Follows H name w e)
    (near : Node X d → Node X d → B z)
    (hn : ∀ b e, side (H.pad u).route.net b e = v →
      near (lift name v) (lift name (side (H.pad u).route.net (!b) e)) =
        idx v (side (H.pad u).route.net (!b) e)) :
    (routeNames H u lane hu idx).star ((p.pad u).route (H.pad u).route) v =
      (describe p lane name (root v)).star (lift name v) u w near := by
  let N := routeNames H u lane hu idx
  let q := (p.pad u).route (H.pad u).route
  -- 推导：记下中间结论 `h`：`Names.extSize q v = if (lift name v).isLeft then Names.extSize p (root v) else fun _ => 0`。
  have h : Names.extSize q v = if (lift name v).isLeft then Names.extSize p (root v) else fun _ => 0 := by
    cases v <;> funext s <;> cases s <;> rfl
  calc
    _ = printStar (lift name v) (cloud q (layer H u lane) (lift name) v) near
        (Names.extSize q v) (policy q (layer H u lane) v) := by
      apply star_eq N q v (lift name) (unique_layer H u lane hu) (same_layer H u name v hs)
      intro b e he
      change _ = idx (side _ b e) (side _ (!b) e)
      rw [he]
      exact hn b e he
    _ = _ := by
      rw [h]
      unfold q
      rw [routed_cloud H u lane p name w v hs hf, policy_routed H u lane p name w hu v hs hf]
      rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 静态局部导航

导航表不保存宿主的长名称。它保存一个单元及其相邻单元中各候选槽位之间的短分支地址和邻居索引。所有块共用这些函数。

**英文原文**

Static local navigation

A guide remembers no long host names. It stores the short branch
addresses and neighbor indices between the possible slots of a cell
and its neighbors. These functions are shared across all blocks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring

variable {F V X Y I α A : Type} {d z : ℕ}

-- 读法：结构的字段包括 `branch`、`next`。
structure Guide (X : Type) (d z : ℕ) where
  branch : Branch X d
  next : Node X d → Node X d → B z

-- 读法：用字段 `branch`、`next` 构造 `Guide X d z`。
def Guide.make (T : Trie V d) (index : Node V d → Node V d → B z) (find : X → V) :
    Guide X d z where
  branch x y := T.address (find x) (find y)
  next x y := index (lift find x) (lift find y)

-- 读法：`Guide.emit` 的取值由 `p.map (fun s => s.star v u W.branch W.next)` 给出。
def Guide.emit [Field F] (W : Guide X d z) (v : Node X d) (u : ℕ)
    (p : Option (Inventory F α A X)) : Option (Star F (Layer A d) z) :=
  p.map (fun s => s.star v u W.branch W.next)

variable {a b : Wire} {G : Bundled F a b} {T : Trie V d} (H : Fanout G T I)
  (idx : Node V d → Node V d → B z)

-- 读法：`pointer` 的取值由 `idx (H.place v).1 (H.place w).1` 给出。
def pointer (v w : Node G.V d) := idx (H.place v).1 (H.place w).1

-- 读法：`Locates` 的取值由 `∀ w, (w = v ∨ ∃ e, touches G v e ∧ touches G w e) → find (name w) = (H.site w).1` 给出。
def Locates (name : G.V → X) (find : X → V) (v : G.V) :=
  ∀ w, (w = v ∨ ∃ e, touches G v e ∧ touches G w e) → find (name w) = (H.site w).1

-- 读法：`lift find (lift name v)` 等于 `(H.place v).1`。对 `v` 分类讨论。
private theorem lift_name (name : G.V → X) (find : X → V) (v : Node G.V d)
    (h : find (name (root v)) = (H.site (root v)).1) :
    lift find (lift name v) = (H.place v).1 := by
  cases v with
  | inl v => exact congrArg Sum.inl h
  | inr v => exact congrArg (fun x => Sum.inr (x, v.2)) h

variable [Field F]

-- 读法：`(Guide.make T idx find).emit (lift name v) u (some (describe p lane name (root v)))` 等于 `some ((routeNames H u lane hu (pointer H idx)).star ((p.pad u).route (H.pad u).route) v)`。
theorem print_local (u : ℕ) (lane : G.E → A) (hu : Unique G lane) (p : Order.Script G α)
    (name : G.V → X) (v : Node G.V d) (hs : Same name (root v))
    (find : X → V) (hf : Locates H name find (root v)) :
    (Guide.make T idx find).emit (lift name v) u (some (describe p lane name (root v))) =
      some ((routeNames H u lane hu (pointer H idx)).star ((p.pad u).route (H.pad u).route) v) := by
  let W := Guide.make T idx find
  have follows (e : G.E) (he : touches G (root v) e) : Follows H name W.branch e := by
    intro s
    change T.address (find (name _)) (find (name _)) = _
    have ht (s : Bool) := hf _ (.inr ⟨e, he, touches_side _ s e⟩)
    rw [ht, ht]
  have step b i (h : side (H.pad u).route.net b i = v) :
      W.next (lift name v) (lift name (side (H.pad u).route.net (!b) i)) =
        pointer H idx v (side (H.pad u).route.net (!b) i) := by
    let w := side (H.pad u).route.net (!b) i
    have hv : touches G (root v) i.1 := h ▸ end_root H u b i
    change idx (lift find (lift name v)) (lift find (lift name w)) = _
    rw [lift_name H name find v (hf _ (.inl rfl)),
      lift_name H name find w (hf _ (.inr ⟨i.1, hv, end_root H u (!b) i⟩))]
    rfl
  exact congrArg some (printed H u lane hu (pointer H idx) p name v hs W.branch follows W.next step).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
局部程序指定了所有站点操作数和球面操作数的次序。

**英文原文**

Local programs, including the order of all station and sphere operands.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

-- 读法：当 `h : ∃ i ∈ c.rows, i.number = z` 成立时取 `some h.choose`，否则取 `none`。
def Sheet.get (c : Sheet F J Z A M r t) (z : Z) :=
  if h : ∃ i ∈ c.rows, i.number = z then some h.choose else none

-- 读法：`i ∈ c.rows` 与 `i.number = z` 同时成立。这里调用 `Option.some.inj`。
theorem Sheet.get_spec (c : Sheet F J Z A M r t) {z : Z} {i} (h : c.get z = some i) :
    i ∈ c.rows ∧ i.number = z := by
  unfold get at h
  split_ifs at h with he
  exact Option.some.inj h ▸ he.choose_spec

-- 读法：`Row.operands` 的取值由 `i.reads.map (fun k => .reader k v i.number) ++ List.ofFn (Lane.left v i.number) ++ List.ofFn (Lane.right v i.number)` 给出。
def Row.operands (i : Row F Z A M r t) (v : J) : List (Lane J Z A M) :=
  i.reads.map (fun k => .reader k v i.number) ++ List.ofFn (Lane.left v i.number) ++
    List.ofFn (Lane.right v i.number)

namespace Sheet
variable [Field F] (c : Sheet F J Z A M r t) (P : ℕ)

-- 读法：`first` 的结果类型为 `Policy F (Signal M r t) (Lane J Z A M)`。
def first (j : Fin M) : Policy F (Signal M r t) (Lane J Z A M) :=
  operation (chamber Signal.first
    (c.rows.map (fun i => i.point ^ P) ++ c.ports.map (fun i => i.point ^ P)))
    (c.rows.map (fun i => Lane.left c.mark i.number j) ++ c.ports.map (fun i => Lane.seam i.edge j))

-- 读法：`second` 的取值由 `operation (chamber Signal.second (c.rows.map Row.point)) (c.rows.map (fun i => Lane.right c.mark i.number j))` 给出。
def second (j : Fin M) : Policy F (Signal M r t) (Lane J Z A M) :=
  operation (chamber Signal.second (c.rows.map Row.point))
    (c.rows.map (fun i => Lane.right c.mark i.number j))

-- 读法：`job` 的结果类型为 `Option ((Bool → ℕ) × Policy F (Signal M r t) (Lane J Z A M))`。
def job (known : J → A → Prop) (z : Spot J Z M) :
    Option ((Bool → ℕ) × Policy F (Signal M r t) (Lane J Z A M)) :=
  match z.2 with
  | .inl i => (c.get i).map (fun j => (j.ext, operation (load j.label) (j.operands c.mark)))
  | .inr (.inl false) => some (fun _ => 0, tests (c.hub known))
  | .inr (.inl true) => some (fun _ => 0, operation (fun _ _ _ => 1) [])
  | .inr (.inr (.inl j)) => some (fun _ => 0, c.first P j)
  | .inr (.inr (.inr j)) => some (fun _ => 0, c.second j)

-- 读法：`inventory` 的取值由 `if z.1 = c.mark then (c.job P known z).map (fun x => ⟨x.1, c.lines known z, x.2⟩) else none` 给出。
def inventory (known : J → A → Prop) (z : Spot J Z M) :
    Option (Inventory F (Signal M r t) (Lane J Z A M) (Spot J Z M)) :=
  if z.1 = c.mark then (c.job P known z).map (fun x => ⟨x.1, c.lines known z, x.2⟩) else none

end Sheet

namespace Marking
variable (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e)

-- 读法：`(m.sheet L p i.1).get (m.number i)` 等于 `some (m.rowData L p i)`。
theorem get_eq (i : Place C) :
    (m.sheet L p i.1).get (m.number i) = some (m.rowData L p i) := by
  have h : ∃ j ∈ (m.sheet L p i.1).rows, j.number = m.number i :=
    ⟨_, m.row_mem L p i, rfl⟩
  rw [Sheet.get, dite_eq_left h]
  obtain ⟨j, hj, he⟩ := m.row_spec L p h.choose_spec.1
  have hn := h.choose_spec.2
  rw [← he] at hn ⊢
  rw [m.atCell j i hj hn]

variable [Field F] [Fintype E] [Fintype V] [Fintype K] (P : ℕ)

omit [Field F] in
-- 读法：`(L.operands (.inl (.inl i))).map m.lane` 等于 `(m.rowData L p i).operands (m.mark i.1)`。
private theorem row_operands (i : Place C) :
    (L.operands (.inl (.inl i))).map m.lane = (m.rowData L p i).operands (m.mark i.1) := by
  simp only [Rules.operands, Row.operands, rowData, List.map_append, List.map_map, List.map_ofFn]
  congr 2
  rw [← List.attach_map_val (l := L.reads i)]
  rfl

-- 读法：`policy (L.script p P) m.lane (.inr (.inl (v, j)))` 等于 `(m.sheet L p v).first P j`。
theorem first_eq (v : V) (j : Fin M) :
    policy (L.script p P) m.lane (.inr (.inl (v, j))) = (m.sheet L p v).first P j := by
  change operation (chamber Signal.first ((firstList C v).map (firstPoint C P)))
    (((firstList C v).map (Rules.first j)).map m.lane) = _
  unfold Sheet.first sheet
  simp only [firstList, secondList, List.map_append, List.map_map]
  rfl

-- 读法：`policy (L.script p P) m.lane (.inr (.inr (v, j)))` 等于 `(m.sheet L p v).second j`。
theorem second_eq (v : V) (j : Fin M) :
    policy (L.script p P) m.lane (.inr (.inr (v, j))) = (m.sheet L p v).second j := by
  change operation (chamber Signal.second ((secondList C v).map (secondPoint C)))
    (((secondList C v).map (fun i => Rules.back i j)).map m.lane) = _
  unfold Sheet.second sheet
  simp only [secondList, List.map_map]
  rfl

-- 读法：`(m.sheet L p (S.home s)).job P known (m.spot s)` 等于 `some (Names.extSize (L.script p P) s, policy (L.script p P) m.lane s)`。
private theorem job_eq (known : J → A → Prop) (s : S.Position) (h : m.Observes (S.home s) known) :
    (m.sheet L p (S.home s)).job P known (m.spot s) =
      some (Names.extSize (L.script p P) s, policy (L.script p P) m.lane s) := by
  rcases s with ((i|v|v)|(⟨v, j⟩|⟨v, j⟩))
  · change ((m.sheet L p i.1).get (m.number i)).map _ = _
    rw [m.get_eq, Option.map_some]
    change some ((m.rowData L p i).ext, operation (load (L.label i))
      ((m.rowData L p i).operands (m.mark i.1))) = _
    rw [← m.row_operands]
    rfl
  · rw [m.hub_eq L p v known h]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · rw [m.first_eq]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · rw [m.second_eq]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl

-- 读法：`(m.sheet L p (S.home s)).inventory P known (m.spot s)` 等于 `some (describe (L.script p P) m.lane m.spot s)`。
theorem inventory_eq (known : J → A → Prop) (s : S.Position) (h : m.Observes (S.home s) known) :
    (m.sheet L p (S.home s)).inventory P known (m.spot s) =
      some (describe (L.script p P) m.lane m.spot s) := by
  have he : (m.spot s).1 = (m.sheet L p (S.home s)).mark := m.home_mark s
  rw [Sheet.inventory, ite_eq_left he, m.job_eq L p P known s h, Option.map_some]
  rw [m.lines L p known P s h]
  rfl

omit [Fintype E] [Fintype V] [Fintype K] in
-- 读法：存在 `z`，`S.home z = v` 与 `m.spot z = s` 同时成立。
theorem inventory_live (known : J → A → Prop) (v : V) (s : Spot J Z M)
    (h : ((m.sheet L p v).inventory P known s).isSome) :
    ∃ z, S.home z = v ∧ m.spot z = s := by
  unfold Sheet.inventory at h
  split_ifs at h with he
  swap
  · contradiction
  obtain ⟨j, i | (_ | _) | i | i⟩ := s
  all_goals change j = m.mark v at he
  all_goals subst j
  · change ((m.sheet L p v).get i |>.map _ |>.map _).isSome at h
    obtain ⟨u, hu⟩ : ∃ u, (m.sheet L p v).get i = some u := by
      cases eq : (m.sheet L p v).get i
      · simp [eq] at h
      · exact ⟨_, rfl⟩
    -- 推导：从 `(m.sheet L p v).get_spec hu` 中取出 `hm, hn`。
    obtain ⟨hm, hn⟩ := (m.sheet L p v).get_spec hu
    obtain ⟨z, hz, rfl⟩ := m.row_spec L p hm
    exact ⟨.inl (.inl z), hz, Prod.ext (congrArg m.mark hz) (congrArg Sum.inl hn)⟩
  · exact ⟨.inl (.inr (.inl v)), rfl, rfl⟩
  · exact ⟨.inl (.inr (.inr v)), rfl, rfl⟩
  · exact ⟨.inr (.inl (v, i)), rfl, rfl⟩
  · exact ⟨.inr (.inr (v, i)), rfl, rfl⟩

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 对输出图样的局部请求

一个单元用一张表记录其全部后代。相邻单元的覆盖范围按颜色寻址，无须使用绝对位置。

**英文原文**

Local requests for printed patterns

A cell has one sheet for all its descendants. Footprints of neighbor
cells are addressed by color rather than by absolute position.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Assembly

-- 读法：结构的字段包括 `sheet`、`footprint`、`guide`、`seat`。
structure Request (F J Z A : Type) (M r t d z : ℕ) where
  sheet : Sheet F J Z A M r t
  footprint : Finset (J × A)
  guide : Guide (Spot J Z M) d z
  seat : Node (Spot J Z M) d

variable {F J Z A : Type} [Field F] {M r t d z c s : ℕ}

-- 读法：`Request.known` 的取值由 `(v, k) ∈ q.footprint` 给出。
def Request.known (q : Request F J Z A M r t d z) (v : J) (k : A) := (v, k) ∈ q.footprint

-- 读法：`Request.emit` 的取值由 `q.guide.emit q.seat u (q.sheet.inventory P q.known (root q.seat))` 给出。
def Request.emit (q : Request F J Z A M r t d z) (P u : ℕ) :=
  q.guide.emit q.seat u (q.sheet.inventory P q.known (root q.seat))

-- 读法：`pattern` 的取值由 `((x.bind fun q => q.emit P u).map fun b => b.pattern ix u).getD Star.vacant` 给出。
def pattern (x : Option (Request F J Z A M r t d z)) (P u : ℕ)
    (ix : Band (Layer (Lane J Z A M) d) c ↪ B s) :=
  ((x.bind fun q => q.emit P u).map fun b => b.pattern ix u).getD Star.vacant

-- 读法：`root (lift f v)` 等于 `f (root v)`。
theorem root_lift {V X : Type} (f : V → X) (v : Node V d) : root (lift f v) = f (root v) := by
  cases v <;> rfl

namespace Marking
variable {U X E V K : Type} [Fintype E] [Fintype V] [Fintype K]
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (m : Marking S J Z A) (L : Order.Rules S) {e : E → ℕ} (p : Profile C e)
  (P u : ℕ) {I V' : Type} {T : Trie V' d} (H : Fanout (S.backdrop.emitted p P) T I)
  (idx : Node V' d → Node V' d → B z)

-- 读法：在后续公式中，`names` 是 `routeNames H u m.lane (m.unique p P) (pointer H idx)` 的缩写。
abbrev names := routeNames H u m.lane (m.unique p P) (pointer H idx)

-- 读法：`x.emit P u` 等于 `some ((m.names p P u H idx).star (((L.script p P).pad u).route (H.pad u).route) v)`。这里调用 `print_local`。
theorem emit_eq (v : Node S.Position d) (x : Request F J Z A M r t d z)
    (h : x.sheet = m.sheet L p (S.home (root v)))
    (hobs : m.Observes (S.home (root v)) x.known) (hseat : x.seat = lift m.spot v)
    (find : Spot J Z M → V') (hloc : Locates H m.spot find (root v))
    (hg : x.guide = Guide.make T idx find) :
    x.emit P u = some ((m.names p P u H idx).star (((L.script p P).pad u).route (H.pad u).route) v) := by
  rw [Request.emit, hseat, hg, h, root_lift, m.inventory_eq L p P _ _ hobs]
  exact print_local H idx u m.lane (m.unique p P) (L.script p P) m.spot v (m.same p P _) find hloc

omit [Fintype E] [Fintype V] [Fintype K] in
-- 读法：存在 `w : Node S.Position d`，`S.home (root w) = v` 与 `lift m.spot w = x.seat` 同时成立。
theorem emit_live (v : V) (x : Request F J Z A M r t d z) (h : x.sheet = m.sheet L p v)
    (hx : (x.emit P u).isSome) :
    ∃ w : Node S.Position d, S.home (root w) = v ∧ lift m.spot w = x.seat := by
  have hr : ((m.sheet L p v).inventory P x.known (root x.seat)).isSome := by
    simpa [Request.emit, Guide.emit, h] using hx
  obtain ⟨w, hw, he⟩ := m.inventory_live L p P _ _ _ hr
  cases eq : x.seat with
  | inl s =>
    rw [eq] at he
    exact ⟨.inl w, hw, congrArg Sum.inl he⟩
  | inr s =>
    rw [eq] at he
    exact ⟨.inr (w, s.2), hw, congrArg (fun t => Sum.inr (t, s.2)) he⟩

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 一个已着色单元的静态宿主图信息

**英文原文**

Static host information for one colored cell
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Coloring Rounds
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet Node)

-- 读法：在后续公式中，`Number` 是 `Bool × Fin (D ^ k)` 的缩写。
abbrev Number (D k : ℕ) := Bool × Fin (D ^ k)
-- 读法：在后续公式中，`Bench` 是 `V × Sharing.Slot M D k` 的缩写。
abbrev Bench (V : Type) (M D k : ℕ) := V × Sharing.Slot M D k
-- 读法：在后续公式中，`Host` 是 `Node (Bench V M D k) (Sharing.radius k * d)` 的缩写。
abbrev Host (V : Type) (M D k d : ℕ) := Node (Bench V M D k) (Sharing.radius k * d)

variable {F U X E V K J A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k d z : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  (G : S.Geo P k) (m : Marking S J (Number D k) A)

-- 读法：结构的字段包括 `color`、`distinct`、`cell`、`row`。
structure Compass where
  color : P.V → J
  distinct : ∀ v, Set.InjOn color (insert v (P.adj v) : Finset P.V)
  cell : ∀ v, m.mark v = color (G.site v).1
  row : ∀ i, m.number i = (decide (G.frozen i), Fin.castLE (G.count i.1) i.2)

namespace Compass
variable {G m} (B : Compass G m)

-- 读法：当 `h : ∃ w ∈ insert v (P.adj v), B.color w = j` 成立时取 `h.choose`，否则取 `v`。
def find (v : P.V) (j : J) :=
  if h : ∃ w ∈ insert v (P.adj v), B.color w = j then h.choose else v

-- 读法：`B.find v (B.color w)` 等于 `w`。这里调用 `B.distinct`。
theorem location (v w : P.V) (hw : w ∈ insert v (P.adj v)) : B.find v (B.color w) = w := by
  have h : ∃ i ∈ insert v (P.adj v), B.color i = B.color w := ⟨w, hw, rfl⟩
  rw [find, dite_eq_left h]
  exact B.distinct v h.choose_spec.1 hw h.choose_spec.2

-- 读法：在后续公式中，`paint` 是 `Prod.map B.color id` 的缩写。
abbrev paint : Bench P.V M D k → Spot J (Number D k) M := Prod.map B.color id
-- 读法：在后续公式中，`resolve` 是 `Prod.map (B.find v) id` 的缩写。
abbrev resolve (v : P.V) : Spot J (Number D k) M → Bench P.V M D k := Prod.map (B.find v) id

-- 读法：`seat` 的取值由 `lift B.paint v` 给出。
def seat (v : Host P.V M D k d) := lift B.paint v

-- 读法：`m.spot i` 等于 `B.paint (G.place i).1`。
theorem spot (i : S.Position) : m.spot i = B.paint (G.place i).1 := by
  rcases i with ((i|v|v)|(⟨v, j⟩|⟨v, j⟩))
  all_goals simp [Marking.spot, paint, Sharing.Geo.place, Sharing.Geo.slot, Sharing.home,
    Layout.Grid.point, B.row, B.cell]

variable (hD : D = 2 ^ d) (hd : 4 ≤ D)
  (idx : Host P.V M D k d → Host P.V M D k d → Coloring.B z)

-- 读法：`guide` 的取值由 `Guide.make (G.tree hD hd) idx (B.resolve v)` 给出。
def guide (v : P.V) := Guide.make (G.tree hD hd) idx (B.resolve v)

variable [Field F] [Fintype E] [Fintype V] [Fintype K]
  {e : E → ℕ} (p : Profile C e) (L : ℕ)

-- 读法：`B.seat ((G.layout hD hd p L).place v).1` 等于 `lift m.spot v`。对 `v` 分类讨论。
theorem seat_eq (v : Node S.Position (Sharing.radius k * d)) :
    B.seat ((G.layout hD hd p L).place v).1 = lift m.spot v := by
  cases v with
  | inl v => exact congrArg Sum.inl (B.spot v).symm
  | inr v => exact congrArg (fun i => Sum.inr (i, v.2)) (B.spot v.1).symm

-- 读法：`((root ((G.layout hD hd p L).place v).1).1, ((G.layout hD hd p L).place v).2)` 等于 `G.site (S.home (root v))`。
theorem home_eq (v : Node S.Position (Sharing.radius k * d)) :
    ((root ((G.layout hD hd p L).place v).1).1, ((G.layout hD hd p L).place v).2) =
      G.site (S.home (root v)) := by cases v <;> rfl

-- 读法：要证明的命题是 `Locates (G.layout hD hd p L) m.spot (B.resolve (G.site (S.home v)).1) v`。这里调用 `Finset.mem_product.mp`。
theorem locates (v : S.Position) :
    Locates (G.layout hD hd p L) m.spot (B.resolve (G.site (S.home v)).1) v := by
  intro w hw
  have hnear {x y : S.Position} (i : (S.backdrop.emitted p L).E)
      (hx : (S.backdrop.emitted p L).src i = x) (hy : (S.backdrop.emitted p L).dst i = y) :
      (G.site (S.home y)).1 ∈ insert (G.site (S.home x)).1 (P.adj (G.site (S.home x)).1) := by
    have h := (G.layout hD hd p L).near i
    change (G.place _).1 ∈ G.neighbors (G.place _).1 at h
    rw [hx, hy] at h
    exact (Finset.mem_product.mp h).1
  -- 推导：记下中间结论 `hit`：`(G.site (S.home w)).1 ∈ insert (G.site (S.home v)).1 (P.adj (G.site (S.home v)).1)`。
  have hit : (G.site (S.home w)).1 ∈ insert (G.site (S.home v)).1 (P.adj (G.site (S.home v)).1) := by
    rcases hw with rfl | ⟨i, hv, hv'⟩
    · simp
    rcases hv with hv|hv <;> rcases hv' with hw|hw
    · rw [← hw, hv]; simp
    · exact hnear i hv hw
    · exact Finset.mem_insert.mpr ((Finset.mem_insert.mp (hnear i hw hv)).imp Eq.symm (P.sym _ _))
    · rw [← hw, hv]; simp
  rw [B.spot]
  exact Prod.ext (B.location _ _ hit) rfl

end Compass
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 局部输出中的活动槽位与空槽位

**英文原文**

Active and vacant slots in a local emission
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Rounds
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet Node)

-- 读法：在后续公式中，`Page` 是 `Sheet F J Z A M r t × Finset (J × A)` 的缩写。
abbrev Page (F J Z A : Type) (M r t : ℕ) := Sheet F J Z A M r t × Finset (J × A)

namespace Compass
variable {F U X E V K J A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k d z : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {m : Marking S J (Number D k) A}
  (B : Compass G m) (hD : D = 2 ^ d) (hd : 4 ≤ D)
  (idx : Host P.V M D k d → Host P.V M D k d → Coloring.B z)

-- 读法：`request` 的取值由 `⟨pg.1, pg.2, B.guide hD hd idx (root v).1, B.seat v⟩` 给出。
def request (v : Host P.V M D k d) (pg : Page F J (Number D k) A M r t) :
    Request F J (Number D k) A M r t (Sharing.radius k * d) z :=
  ⟨pg.1, pg.2, B.guide hD hd idx (root v).1, B.seat v⟩

-- 读法：`requestAt` 的取值由 `(pages ((root v.1).1, v.2)).map (B.request hD hd idx v.1)` 给出。
def requestAt (pages : P.V × Packing.Cell h → Option (Page F J (Number D k) A M r t))
    (v : Host P.V M D k d × Packing.Cell h) :=
  (pages ((root v.1).1, v.2)).map (B.request hD hd idx v.1)

-- 读法：`x` 等于 `y`。使用 `lift_eq` 给出的结论。
private theorem seat_inj {x y : Host P.V M D k d} (hh : (root x).1 = (root y).1)
    (he : B.seat x = B.seat y) : x = y :=
  lift_eq (fun h => Prod.ext hh (congrArg (fun i : Spot J (Number D k) M => i.2) h)) he

variable [Field F] [Fintype E] [Fintype V] [Fintype K]
  {e : E → ℕ} (p : Profile C e) (L u : ℕ) (q : Order.Rules S)
  (pages : P.V × Packing.Cell h → Option (Page F J (Number D k) A M r t))

-- 读法：结构的字段包括 `active`、`inactive`。
structure Ready : Prop where
  active : ∀ v, ∃ f, pages (G.site v) = some (m.sheet q p v, f) ∧
    m.Observes v (fun j a => (j, a) ∈ f)
  inactive : ∀ v ∉ Set.range G.site, pages v = none

local notation "H" => G.layout hD hd p L

-- 读法：`((B.requestAt hD hd idx pages ((H).place v)).bind fun a => a.emit L u)` 等于 `some ((m.names p L u H idx).star ((H).routed (q.script p L) u) v)`。这里调用 `m.emit_eq`。
theorem print_active (hs : Ready (G := G) (m := m) p q pages) (v : Node S.Position (Sharing.radius k * d)) :
    ((B.requestAt hD hd idx pages ((H).place v)).bind fun a => a.emit L u) =
      some ((m.names p L u H idx).star ((H).routed (q.script p L) u) v) := by
  obtain ⟨f, hf, ha⟩ := hs.active (S.home (root v))
  have hh := home_eq (G := G) hD hd p L v
  rw [requestAt, hh, hf, Option.map_some, Option.bind_some]
  apply m.emit_eq q p L u H idx v (B.request hD hd idx ((H).place v).1 (_, f)) rfl ha (B.seat_eq hD hd p L v)
    _ (B.locates hD hd p L (root v))
  exact congrArg (B.guide hD hd idx) (congrArg Prod.fst hh)

-- 读法：`((B.requestAt hD hd idx pages x).bind fun a => a.emit L u)` 等于 `none`。按 `((root x.1).1, x.2) ∈ Set.range G.site` 成立与否分情况。
theorem print_vacant (hs : Ready (G := G) (m := m) p q pages)
    (x : Host P.V M D k d × Packing.Cell h) (hx : x ∉ Set.range (H).place) :
    ((B.requestAt hD hd idx pages x).bind fun a => a.emit L u) = none := by
  by_cases hv : ((root x.1).1, x.2) ∈ Set.range G.site
  swap
  · simp [requestAt, hs.inactive _ hv]
  obtain ⟨v, he⟩ := hv
  obtain ⟨f, hf, _⟩ := hs.active v
  rw [requestAt, ← he, hf, Option.map_some, Option.bind_some]
  by_contra hne
  obtain ⟨w, hw, ha⟩ := m.emit_live q p L u v (B.request hD hd idx x.1 (m.sheet q p v, f))
    rfl (Option.isSome_iff_ne_none.mpr hne)
  have hh := home_eq (G := G) hD hd p L w
  rw [hw, he] at hh
  exact hx ⟨w, Prod.ext (B.seat_inj (Prod.mk.inj hh).1 ((B.seat_eq hD hd p L w).trans ha))
    (Prod.mk.inj hh).2⟩

end Compass
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# 由输出的位置实例记录行构造有向表示

**英文原文**

Building a directed presentation from printed occurrence rows
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Rounds Coloring
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet Node)

-- 读法：`Engine.seat` 的结果类型为 `V × I ↪ U.scheme.Vtx`。
def Engine.seat {F A V I : Type} (U : Engine F A) (host : V ↪ B U.m) (block : I ↪ B U.h) :
    V × I ↪ U.scheme.Vtx :=
  ⟨fun x => (host x.1, block x.2, 0), fun _ _ h =>
    Prod.ext (host.injective (congrArg Prod.fst h)) (block.injective (congrArg (fun y => y.2.1) h))⟩

namespace Compass
variable {F T X E V K J A : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D W₀ R g k d : ℕ} {W : ℝ} {P : Input F a b h D W₀ R g W}
  {G : S.Geo P k} {m : Marking S J (Number D k) A} (T : Compass G m)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) {e : E → ℕ} (p : Profile C e) (L u : ℕ) (q : Order.Rules S)

-- 读法：在后续公式中，`FinalLane` 是 `Layer (Lane J (Number D k) A M) (Sharing.radius k * d)` 的缩写。
abbrev FinalLane (J A : Type) (M D k d : ℕ) := Layer (Lane J (Number D k) A M) (Sharing.radius k * d)

variable {U : Engine F (FinalLane J A M D k d)}
  (host : Host P.V M D k d ↪ B U.m) (block : Packing.Cell h ↪ B U.h)
  (idx : Host P.V M D k d → Host P.V M D k d → B U.d)
  (rows : U.scheme.format.obj)
  (pages : P.V × Packing.Cell h → Option (Page F J (Number D k) A M r t))

local notation "H" => G.layout hD hd p L

-- 读法：`vertex` 的取值由 `(show Node S.Position (Sharing.radius k * d) ↪ _ from ⟨(H).place, (H).injective⟩).trans (U.seat host block)` 给出。
def vertex : Node S.Position (Sharing.radius k * d) ↪ U.scheme.Vtx :=
  (show Node S.Position (Sharing.radius k * d) ↪ _ from ⟨(H).place, (H).injective⟩).trans
    (U.seat host block)

-- 读法：结构的字段包括 `pattern`、`padding`、`nav`。
structure Prints : Prop where
  pattern : ∀ i, U.scheme.pattern rows (U.seat host block i) =
    Print.pattern (T.requestAt hD hd idx pages i) L u U.ix
  padding : ∀ i ∉ Set.range (U.seat host block), U.scheme.pattern rows i = Star.vacant
  nav : ∀ v w, w ∈ (G.tree hD hd).adj v → (rows (host v)).1 (idx v w) = host w

-- 读法：用字段 `vertex`、`pos`、`width`、`bound` 构造 `Frame U rows (m.names p L u H idx) ((H).routed (q.script p L) u) u`。
def frame (hu : 0 < u) (hw : ∀ i, Diagram.padWidth u ((S.backdrop.emitted p L).width i) / u ≤ U.cap)
    (hs : Ready (G := G) (m := m) p q pages)
    (hr : T.Prints hD hd L u host block idx rows pages) :
    Frame U rows (m.names p L u H idx) ((H).routed (q.script p L) u) u where
  vertex := vertex (G := G) hD hd p L host block
  pos := hu
  width i := Diagram.dvd_padWidth hu _
  bound i := hw i.1
  active v := by
    change U.scheme.pattern rows (U.seat host block ((H).place v)) = _
    rw [hr.pattern, Print.pattern, T.print_active hD hd idx p L u q pages hs]
    rfl
  inactive v hv := by
    by_cases hx : v ∈ Set.range (U.seat host block)
    · obtain ⟨z, rfl⟩ := hx
      have hz : z ∉ Set.range (H).place := fun ⟨w, h⟩ => hv ⟨w, congrArg (U.seat host block) h⟩
      rw [hr.pattern, Print.pattern, T.print_vacant hD hd idx p L u q pages hs _ hz]
      rfl
    · exact hr.padding v hx
  address s i := by
    let x := (H).place (side ((H).pad u).route.net s i)
    let y := (H).place (side ((H).pad u).route.net (!s) i)
    have he : x.2 = y.2 ∧ y.1 ∈ (G.tree hD hd).adj x.1 := by
      have hi := ((H).pad u).edges i
      have hp (v : Node S.Position (Sharing.radius k * d)) : ((H).pad u).place v = (H).place v := by
        cases v <;> rfl
      simp only [Layout.Fanout.linked, hp] at hi
      unfold x y
      cases s
      · exact hi
      · exact ⟨hi.1.symm, (G.tree hD hd).adj_symm hi.2⟩
    change ((rows (host x.1)).1 (idx x.1 y.1), block x.2, (0 : B 0)) = (host y.1, block y.2, 0)
    rw [hr.nav _ _ he.2, he.1]

end Compass
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end
