-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial

/-!
# 移动核心时保留冻结表

第二份局部记录包含整个边界和系接线的端点。宿主地址与块编号和核心记录共用。第一个站点槽位始终留给核心，即使核心为空也一样。

**英文原文**

Keeping frozen tables while the core moves

A second local record contains the full border and the tether endpoints.
Host addresses and the block number are shared with the core record. The
first station slot is reserved for the core, even if it is empty.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing

-- 读法：结构的字段包括 `k`、`e`、`ℓ`、`decode`、`live`。
structure Attachment {F : Type} (D : Template F) where
  k : ℕ
  e : ℕ
  ℓ : ℕ
  decode : B ℓ → Pattern F D.scheme.d k e
  live : B ℓ → B k → Bool
  charge : B ℓ → B k → ℝ
  coreSpan : B D.scheme.e ↪ B e

namespace Attachment

variable {F T : Type} {D : Template F} (A : Attachment D)

-- 读法：在后续公式中，`scheme` 是 `⟨D.scheme.m, D.scheme.d, D.scheme.h, A.k, A.e, A.ℓ, A.decode⟩` 的缩写。
abbrev scheme : Scheme F :=
  ⟨D.scheme.m, D.scheme.d, D.scheme.h, A.k, A.e, A.ℓ, A.decode⟩

-- 读法：在后续公式中，`label` 是 `Format.vec D.scheme.m (.vec D.scheme.h (.addr A.ℓ))` 的缩写。
abbrev label := Format.vec D.scheme.m (.vec D.scheme.h (.addr A.ℓ))

-- 读法：在后续公式中，`format` 是 `D.format.pair A.label` 的缩写。
abbrev format := D.format.pair A.label

-- 读法：输入 `v` 时返回 `(D.nav r.1 v, r.2 v)`。
def rows (r : A.format.obj) : A.scheme.format.obj :=
  fun v => (D.nav r.1 v, r.2 v)

-- 读法：`A.format.width` 等于 `D.format.width + 2 ^ D.scheme.m * (2 ^ D.scheme.h * A.ℓ)`。
theorem width : A.format.width = D.format.width + 2 ^ D.scheme.m * (2 ^ D.scheme.h * A.ℓ) := by
  simp only [format, label, Format.width_pair, Format.width_vec, Format.width_addr]

variable [Field F] [Fintype T] {x y a b : Wire} {u : ℕ} {L : Fringe x y T}
variable (r : A.format.obj) (G : HostNet F L D.scheme.h u) (Z : Border F T a b x y)

-- 读法：结构的字段包括 `full`、`tether`、`core`、`pres`、`directed`。
/-- 核心记录与边界记录必须按同一次序描述核心的每个比特。每张冻结表保存在分配给它的槽位中。

英文原文：The core and the border records must describe the same individual
core bits, in order. A frozen table is kept on its own assigned slot.
-/
structure Encloses where
  full : D.full = true
  tether : L.tensor = Z.tensor
  core : D.Encodes r.1 G
  pres : A.scheme.Presentation (A.rows r) (Z.attach G.diagram)
  directed : pres.Directed
  occupied : ∀ v : A.scheme.Vtx, A.live (r.2 v.1 v.2.1) v.2.2 = true ↔ v ∈ Set.range pres.vertex
  slot : T → B A.k
  positive : ∀ t, slot t ≠ 0
  internal : ∀ v, pres.vertex (.inl v) =
    (core.post.host (G.units.place v).1, core.post.block (G.units.place v).2, 0)
  frozen : ∀ t, pres.vertex (.inr t) =
    (core.post.host (G.park t).1, core.post.block (G.park t).2, slot t)
  charge : ∀ t, A.charge (r.2 (core.post.host (G.park t).1) (core.post.block (G.park t).2))
    (slot t) = L.charge t
  ordered : ∀ v (j : G.diagram.Port v),
    (pres.pin (.inl v) j).1 = A.coreSpan (core.post.pin v j).1 ∧
      (pres.pin (.inl v) j).2.val = (core.post.pin v j).2.val

variable {r G Z A}

-- 读法：`v` 等于 `w`。这里调用 `Sum.inr.inj`。
theorem Encloses.distinct (q : A.Encloses r G Z) {v w : T}
    (h : G.park v = G.park w) (hs : q.slot v = q.slot w) : v = w := by
  apply Sum.inr.inj
  apply q.pres.vertex.injective
  rw [q.frozen, q.frozen, h, hs]

end Attachment
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# 保留边界时各阶段的公共边界

**英文原文**

Common stage boundary while the border is retained
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
    (x y : Wire) (u height : ℕ)

-- 读法：结构的字段包括 `T`、`a`、`b`、`L`、`G`。
structure Data where
  T : Type
  [finite : Fintype T]
  a : Wire
  b : Wire
  L : Fringe a b T
  G : HostNet F L D.scheme.h u
  Z : Border F T x y a b
  raw : A.format.obj
  q : A.Encloses raw G Z

attribute [instance] Data.finite

-- 读法：在后续公式中，`volume` 是 `2 ^ m + wd x + wd y` 的缩写。
abbrev volume (m : ℕ) := 2 ^ m + wd x + wd y
-- 读法：在后续公式中，`payload` 是 `Fmt.payload m (volume x y m) height` 的缩写。
abbrev payload (m : ℕ) := Fmt.payload m (volume x y m) height
-- 读法：在后续公式中，`port` 是 `A.format.pair (payload x y height D.scheme.m)` 的缩写。
abbrev port := A.format.pair (payload x y height D.scheme.m)

namespace Data
variable {A x y u height} (X : Data A x y u)

-- 读法：在后续公式中，`diagram` 是 `X.Z.attach X.G.diagram` 的缩写。
abbrev diagram := X.Z.attach X.G.diagram
-- 读法：在后续公式中，`Fits` 是 `A.scheme.Fits (A.rows X.raw) (volume x y D.scheme.m) height` 的缩写。
abbrev Fits (height : ℕ) := A.scheme.Fits (A.rows X.raw) (volume x y D.scheme.m) height

-- 读法：`data` 的取值由 `A.scheme.store _ fit (X.q.pres.exterior i j)` 给出。
def data (fit : X.Fits height) (i : Val x) (j : Val y) : (payload x y height D.scheme.m).obj :=
  A.scheme.store _ fit (X.q.pres.exterior i j)

-- 读法：`Neutral` 的取值由 `∀ v, X.G.diagram.arity v = 0 → ∀ t, Transcript.sample (X.G.diagram.table v) t = 1` 给出。
def Neutral := ∀ v, X.G.diagram.arity v = 0 → ∀ t, Transcript.sample (X.G.diagram.table v) t = 1

end Data

-- 读法：用字段 `state`、`eval`、`port`、`encode` 构造 `Assembly.Snapshot.{1} F x y`。
def frame (P : Data A x y u → Prop) : Assembly.Snapshot.{1} F x y where
  state := {X : Data A x y u // P X ∧ X.Fits height}
  eval i := i.val.diagram.eval
  port := A.port x y height
  encode i a b := (i.val.raw, i.val.data i.property.2 a b)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end
