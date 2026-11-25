-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.ContractRates
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders

/-!
# 生成以接触信息作为输入一部分的指令序列

**英文原文**

Emitting a script whose contacts are part of the input
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Emit
open Coloring SpanPlan
variable (m p w n : ℕ)
local notation "P" => Perm (m + p)
local notation "C" => Payload.Script m m p w n
local notation "E" => Ports m m (entries w p n) (entries w p n)

-- 读法：在后续公式中，`source` 是 `(P).pair E` 的缩写。
abbrev source := (P).pair E
-- 读法：`emit` 的取值由 `SpanPlan.emit z.1 z.2` 给出。
def emit (z : (source m p w n).obj) : (C).obj := SpanPlan.emit z.1 z.2
-- 读法：`cost` 的取值由 `(P).width + emitCost m m w p n + (((P).pair C).width + 2 * (C).width)` 给出。
def cost := (P).width + emitCost m m w p n + (((P).pair C).width + 2 * (C).width)

-- 读法：在 `F` 上按格式 `(source m p w n)`、`C` 编码输入输出，映射 `(emit m p w n)` 的电路规模至多为 `(cost m p w n)`。这里调用 `Circuit.project`。
theorem circuit (F : Type) [Field F] : Circuit F (source m p w n) C (emit m p w n) (cost m p w n) := by
  let g : ((P).pair C).obj → (C).obj := fun z => ((z.2.1.1, z.1), z.2.2)
  have patch : Circuit F ((P).pair C) C g
      (((P).pair C).width + 2 * (C).width) := by
    let atBit : (C).pins → ((P).pair C).pins
      | .inl (.inl i) => .inr (.inl (.inl i))
      | .inl (.inr i) => .inl i
      | .inr i => .inr (.inr i)
    exact Circuit.project atBit (by rintro _ ((i|i)|i) <;> rfl)
  have write := emit_net (m:=m) (m':=m) (w:=w) (p:=p) (n:=n) id F
  have eq : g ∘ Prod.map id (SpanPlan.emit (m:=m) (m':=m) (w:=w) (p:=p) (n:=n) id) =
      emit m p w n := by
    funext x
    simp only [g, emit, SpanPlan.emit, SpanPlan.assemble, Function.comp_apply, Prod.map, id_eq]
  rw [← eq]
  exact ((Circuit.id F P).par write).comp patch

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Emit
end

/-!
# 从填充后的站点记录中提取外部比特

**英文原文**

Extracting exterior bits from padded station records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
open Coloring SpanPlan

-- 读法：在后续公式中，`input` 是 `Format.pair (.vec m (entries w z n)) (.vec m (entries w 0 n))` 的缩写。
abbrev input (m z w n : ℕ) :=
  Format.pair (.vec m (entries w z n)) (.vec m (entries w 0 n))

-- 读法：在后续公式中，`middle` 是 `Format.pair (.vec m (SpanPlan.Row w z n)) (.vec m (SpanPlan.Row w 0 n))` 的缩写。
private abbrev middle (m z w n : ℕ) :=
  Format.pair (.vec m (SpanPlan.Row w z n)) (.vec m (SpanPlan.Row w 0 n))

variable {m z w n : ℕ}

-- 读法：输入 `i` 时返回 `((b i).1, (b i).2.1, (b i).2.2, (offsets a i).2.2.2)`。
def outgoing (a : (entries w z n).obj) (b : (entries w 0 n).obj) : (Input w 0 n).obj :=
  fun i => ((b i).1, (b i).2.1, (b i).2.2, (offsets a i).2.2.2)

-- 读法：`script` 的取值由 `SpanPlan.assemble (SpanPlan.total ∘ x.1) (SpanPlan.total ∘ x.2) (fun i => outgoing (x.1 i) (x.2 i)) (offsets ∘ x.2) id` 给出。
def script (x : (input m z w n).obj) : (Payload.Script m m 0 w n).obj :=
  SpanPlan.assemble (SpanPlan.total ∘ x.1) (SpanPlan.total ∘ x.2) (fun i => outgoing (x.1 i) (x.2 i)) (offsets ∘ x.2) id

-- 读法：`gather` 的结果类型为 `(Payload.Script m m 0 w n).obj`。
private def gather (x : (middle m z w n).obj) : (Payload.Script m m 0 w n).obj :=
  organize id (fun i => ((x.1 i).1, (x.2 i).2.1, fun j =>
    let u := (x.2 i).2.2 j
    (u.1, u.2.1, u.2.2.1, ((x.1 i).2.2 j).2.2.2)), x.2)

-- 读法：`price` 的取值由 `2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140` 给出。
private def price (w p n : ℕ) := 2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140

-- 读法：`cost` 的取值由 `2 ^ m * price w z n + 2 ^ m * price w 0 n + ((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width)` 给出。
def cost (m z w n : ℕ) :=
  2 ^ m * price w z n + 2 ^ m * price w 0 n +
    ((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width)

-- 读法：两端由定义化简为同一项。
private theorem gather_eq : gather ∘ Prod.map (fun (x : (Format.vec m (entries w z n)).obj) i => compile (x i))
    (fun (x : (Format.vec m (entries w 0 n)).obj) i => compile (x i)) = script := by
  rfl

-- 读法：在 `F` 上按格式 `(middle m z w n)`、`(Payload.Script m m 0 w n)` 编码输入输出，映射 `gather` 的电路规模至多为 `((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width)`。这里调用 `Window.Tile.project_const`。
private theorem final (F : Type) [Field F] : Circuit F (middle m z w n) (Payload.Script m m 0 w n) gather
    ((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width) := by
  apply Window.Tile.project_const
  rintro ((((⟨i, j⟩|⟨i, j⟩)|(⟨i, j⟩|⟨i, j⟩))|⟨i, j⟩)|⟨i, k, j|j|j|j⟩|⟨i, j⟩)
  · exact .inl ⟨.inl (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr _).code i j, fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inl j))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inr (.inl j)))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inr (.inr (.inl j))))), fun _ => rfl⟩
  · exact .inl ⟨.inl (i, .inr (.inr (k, .inr (.inr (.inr j))))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr j)), fun _ => rfl⟩

-- 读法：在 `F` 上按格式 `(input m z w n)`、`(Payload.Script m m 0 w n)` 编码输入输出，映射 `script` 的电路规模至多为 `(cost m z w n)`。这里调用 `hk.mono`。
theorem circuit (F : Type) [Field F] (m z w n : ℕ) :
    Circuit F (input m z w n) (Payload.Script m m 0 w n) script (cost m z w n) := by
  have stage (p : ℕ) : Circuit F (entries w p n) (SpanPlan.Row w p n) compile (price w p n) := by
    obtain ⟨k, hk, he⟩ := cheap_entries F w p n
    exact hk.mono (by unfold price; omega)
  have out := ((Circuit.map _ (fun _ : B m => stage z)).par (Circuit.map _ (fun _ : B m => stage 0))).comp (final F)
  rw [gather_eq] at out
  exact out

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
end

/-!
# 按三种成本尺度编译两个终端数据传送过程

**英文原文**

Compiling both terminal payload scripts on the three cost scales
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring

-- 读法：`effort` 的取值由 `2 ^ i.S.m * (2 ^ (i.n + a) * (100 + (2 * i.n + a + i.w)) ^ 140)` 给出。
private def effort (i : Size) (a : ℕ) := 2 ^ i.S.m * (2 ^ (i.n + a) * (100 + (2 * i.n + a + i.w)) ^ 140)

-- 读法：要证明的命题是 `Work (fun i => effort i (a i))`。
private theorem compile (a : Size → ℕ) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => effort i (a i)) := by
  have step := (num 100).short.add ((((num 2).short.mul n.short).add ha).add w.short)
  refine (Work.spans (he.mul (step.pow 140))).mono fun i => ?_
  simp only [effort, Size.spans, Size.hosts, pow_add, mul_assoc, le_refl]

-- 读法：要证明的命题是 `Work (fun i => (Format.vec i.S.m (SpanPlan.Row i.w (a i) i.n)).width)`。这里调用 `Nat.mul_le_mul_left`。
private theorem rows {a : Size → ℕ} (h : Work (fun i => effort i (a i))) :
    Work (fun i => (Format.vec i.S.m (SpanPlan.Row i.w (a i) i.n)).width) := by
  refine h.mono fun i => ?_
  obtain ⟨s, _, hs⟩ := SpanPlan.cheap_entries i.F i.w (a i) i.n
  rw [Format.width_vec]
  exact Nat.mul_le_mul_left _ (le_trans ((Nat.le_add_left ..).trans (Nat.le_add_right ..)) hs)

-- 读法：要证明的命题是 `Work (fun i => (Payload.Script i.S.m i.S.m i.p i.w i.n).width)`。
private theorem internal : Work (fun i => (Payload.Script i.S.m i.S.m i.p i.w i.n).width) := by
  refine instruction.mono fun i => ?_
  unfold Size.instruction Terminal.instruction
  simp only [Format.width_pair]
  omega

-- 读法：要证明的命题是 `Work (fun i => (Payload.Script i.S.m i.S.m 0 i.w i.n).width)`。
private theorem external : Work (fun i => (Payload.Script i.S.m i.S.m 0 i.w i.n).width) := by
  refine instruction.mono fun i => ?_
  unfold Size.instruction Terminal.instruction
  simp only [Format.width_pair]
  omega

-- 读法：要证明的命题是 `Work (fun i => (Perm (i.S.m + i.p)).width)`。
theorem names : Work (fun i => (Perm (i.S.m + i.p)).width) := by
  refine internal.mono fun i => ?_
  unfold Payload.Script PeerLayout.input Perm
  simp only [Format.width_pair]
  omega

-- 读法：要证明的命题是 `Work (fun i => Emit.cost i.S.m i.p i.w i.n)`。
theorem emit : Work (fun i => Emit.cost i.S.m i.p i.w i.n) := by
  have h := compile Size.p p links
  have r := rows h
  have write := (h.add h).add ((r.add r).add (internal.scale (num 34)))
  have patch := (names.add internal).add (internal.scale (num 2))
  refine ((names.add write).add patch).mono fun i => ?_
  simp only [Emit.cost, SpanPlan.emitCost, SpanPlan.Ports, effort, Format.width_pair, add_mul, le_refl]

-- 读法：要证明的命题是 `Work (fun i => Terminal.Outer.cost i.S.m i.p i.w i.n)`。
theorem project : Work (fun i => Terminal.Outer.cost i.S.m i.p i.w i.n) := by
  have a := compile Size.p p links
  have b := compile (fun _ => 0) (num 0).short (num 1).short
  refine ((a.add b).add (((rows a).add (rows b)).add (external.scale (num 34)))).mono fun i => ?_
  change effort i i.p + effort i 0 +
    ((Format.pair (.vec i.S.m (SpanPlan.Row i.w i.p i.n)) (.vec i.S.m (SpanPlan.Row i.w 0 i.n))).width +
      34 * (Payload.Script i.S.m i.S.m 0 i.w i.n).width) ≤ _
  rw [Format.width_pair]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-!
# 按区段次序给出外部信道的范围

**英文原文**

Exterior channel extents in span order
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
open Finset Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {V k w : ℕ}
  {u : SpanPlan.Rows S.m w 0 S.spanRows}

-- 读法：结构的字段包括 `size`、`order`。
structure Aligned (S : Scheme F) (r : S.format.obj) (u : SpanPlan.Rows S.m w 0 S.spanRows) : Prop where
  size : ∀ i j, SpanPlan.len (u i) j = S.extent r i j
  order : ∀ i j, SpanPlan.pos (u i) j = j

-- 读法：`i` 等于 `0`。使用 `Fin.eq_zero` 给出的结论。
theorem zero (i : B 0) : i = 0 := Fin.eq_zero i

namespace Aligned
variable (ha : Aligned S r u) (h : S.Fits r V k) (hk : k < w)
include ha

-- 读法：要证明的命题是 `SpanPlan.Unique (u v)`。
theorem unique (v : B S.m) : SpanPlan.Unique (u v) := by
  intro i j _ _ _ he
  simpa only [ha.order] using he

include h hk

-- 读法：`(∑ j, SpanPlan.len (u v) j)` 严格小于 `2 ^ w`。
theorem small (v : B S.m) : (∑ j, SpanPlan.len (u v) j) < 2 ^ w := by
  simp_rw [ha.size, ← S.load_eq]
  exact (h.2 v).trans_lt (Nat.pow_lt_pow_right (by decide) hk)

-- 读法：要证明的命题是 `SpanPlan.Fits (u v)`。
theorem fits (v : B S.m) : SpanPlan.Fits (u v) :=
  fun _ => (sum_le_sum_of_subset (subset_univ _)).trans_lt (ha.small h hk v)

-- 读法：`(((SpanPlan.pack (u v)).1 0).val)` 等于 `S.load r v`。
theorem length (v : B S.m) : (((SpanPlan.pack (u v)).1 0).val) = S.load r v := by
  rw [SpanPlan.lengths _ (ha.fits h hk _) 0, S.load_eq]
  change (∑ j with SpanPlan.port (u v) j = 0, SpanPlan.len (u v) j) = _
  simp [zero, ha.size]

-- 读法：`SpanPlan.start (u v) j` 等于 `S.start r v j`。
theorem start (v : B S.m) (j : B S.spanRows) : SpanPlan.start (u v) j = S.start r v j := by
  rw [SpanPlan.start, SpanPlan.starts _ (ha.fits h hk _), Scheme.start]
  change (∑ i with SpanPlan.port (u v) i = SpanPlan.port (u v) j ∧
    SpanPlan.pos (u v) i < SpanPlan.pos (u v) j, SpanPlan.len (u v) i) = _
  simp only [zero, true_and, ha.order, ha.size]

-- 读法：结论为 `let v := S.owner r i let j := S.spanIndex i.val.1 Payload.Script.At (SpanPlan.pack (u v)).2 0 (S.index r h i).2.val (SpanPlan.offset (u v) j + i.val.2.val)`。这里调用 `SpanPlan.Hit.at_bit`。
theorem at_bit (i : S.exposed r) :
    let v := S.owner r i
    let j := S.spanIndex i.val.1
    Payload.Script.At (SpanPlan.pack (u v)).2 0 (S.index r h i).2.val
      (SpanPlan.offset (u v) j + i.val.2.val) := by
  intro v j
  apply SpanPlan.Hit.at_bit
  refine ⟨j, i.val.2.val, zero _, ?_, ?_, rfl⟩
  · rw [ha.size]
    simp [j, v, Scheme.extent, Scheme.owner, i.property]
  · rw [ha.start h hk, S.index_val]

end Aligned
end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
end
