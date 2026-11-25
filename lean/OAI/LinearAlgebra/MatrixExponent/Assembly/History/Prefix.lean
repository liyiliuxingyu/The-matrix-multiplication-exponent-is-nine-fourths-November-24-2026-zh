-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Entry
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks

/-!
# 消去已布线连线的私有连接变量

**英文原文**

Eliminating the private join variables of a routed wire
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

open Classical
variable {K S E X Y : Type} [Field K] [Fintype S] [Fintype E] [Fintype X] [Fintype Y]

-- 读法：`(hf.series hg).entry () v x y u` 等于 `hf.entry () v x k (u ∘ Sum.inl) * hg.entry () v k y (u ∘ Sum.inr)`。这里调用 `hf.local'`。
/-- 若一项贡献要非零就必须将各局部连接比特固定在唯一一组赋值上，则串联求和等于该赋值下的乘积。

英文原文：If nonzero contributions force a single setting of every local
joining bit, the serial sum is the product at that setting.
-/
theorem series_eval {a b c : E → S} {W : X → S × S} {U : Y → S × S}
    (hf : Rule K (fun e => (a e, b e)) (fun _ : Unit => W))
    (hg : Rule K (fun e => (b e, c e)) (fun _ : Unit => U))
    (v : S) (x y : E → Bool) (u : X ⊕ Y → Bool) (k : E → Bool)
    (hp : ∀ t, hf.entry () v x t (u ∘ Sum.inl) ≠ 0 → hg.entry () v t y (u ∘ Sum.inr) ≠ 0 →
      ∀ e, b e = v → t e = k e) :
    (hf.series hg).entry () v x y u =
      hf.entry () v x k (u ∘ Sum.inl) * hg.entry () v k y (u ∘ Sum.inr) := by
  let T := {e // b e = v}
  let fill (t : T → Bool) (e : E) := if h : b e = v then t ⟨e, h⟩ else false
  let z (e : T) := k e.1
  change (∑ t, hf.entry () v x (fill t) (u ∘ Sum.inl) * hg.entry () v (fill t) y (u ∘ Sum.inr)) = _
  rw [Fintype.sum_eq_single z]
  · have he (e) (h : b e = v) : fill z e = k e := by simp [fill, h, z]
    apply congrArg₂ (· * ·)
    · exact hf.local' _ _ _ _ _ _ _ _ (fun _ _ => rfl) he (fun _ _ => rfl)
    · exact hg.local' _ _ _ _ _ _ _ _ he (fun _ _ => rfl) (fun _ _ => rfl)
  · intro t ht
    by_contra hn
    apply ht
    funext e
    have hh := hp (fill t) (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn) e.val e.property
    simpa only [fill, dite_eq_left e.property] using hh

-- 读法：两端由定义化简为同一项。
theorem path_entry (D : ℕ → E → S) (n : ℕ) (v : S) (x y : E → Bool) (z : Fin n × E → Bool) :
    (Rule.path K D n).entry () v x y z =
      if ∀ (i : Fin (n + 1)) e, D i.val e = v →
        Fin.cons (α := fun _ => E → Bool) x (Function.curry z) i e =
          Fin.snoc (α := fun _ => E → Bool) (Function.curry z) y i e then 1 else 0 := rfl

-- 读法：`x e` 等于 `z (0, e)`。
theorem path_head (D : ℕ → E → S) {n : ℕ} (v : S) (x y : E → Bool) (z : Fin (n + 1) × E → Bool)
    (hn : (Rule.path K D (n + 1)).entry () v x y z ≠ 0) (e : E) (he : D 0 e = v) :
    x e = z (0, e) := by
  rw [path_entry] at hn
  split at hn
  · rename_i h
    simpa [Fin.snoc] using h 0 e he
  · contradiction

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
end

/-!
# 具名比特上的三价表之积

把具有同一有序输入三元组的所有因子逐点相乘并合为一项。在有限域上，所得系数表的描述长度有三次上界。

**英文原文**

Products of trivalent tables on named bits

Collect all factors with the same ordered triple of inputs by
pointwise multiplication. Over a finite field the resulting table
of coefficients has a cubic description length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Classical Finset
variable (F J : Type) [Field F] [Fintype J]

-- 读法：在后续公式中，`Triple` 是 `Fin 3 → Option J` 的缩写。
abbrev Triple := Fin 3 → Option J
-- 读法：在后续公式中，`Tables` 是 `Triple J → (Fin 3 → Bool) → F` 的缩写。
abbrev Tables := Triple J → (Fin 3 → Bool) → F
-- 读法：`readBit` 的取值由 `s.elim false x` 给出。
def readBit (x : J → Bool) (s : Option J) : Bool := s.elim false x

-- 读法：`evaluate` 的取值由 `∏ j, c j (readBit J x ∘ j)` 给出。
def evaluate (c : Tables F J) (x : J → Bool) := ∏ j, c j (readBit J x ∘ j)

-- 读法：用字段 `carrier`、`one_mem'`、`mul_mem'` 构造 `Submonoid ((J → Bool) → F)`。
def simple : Submonoid ((J → Bool) → F) where
  carrier := Set.range (evaluate F J)
  one_mem' := ⟨1, by ext; simp [evaluate]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by ext; simp [evaluate, prod_mul_distrib]⟩

-- 读法：`tripleCost` 的取值由 `(Fintype.card J + 1) ^ 3 * 8 * Nat.clog 2 (Fintype.card F)` 给出。
def tripleCost [Fintype F] := (Fintype.card J + 1) ^ 3 * 8 * Nat.clog 2 (Fintype.card F)

omit [Field F] in
-- 读法：`Fintype.card (Tables F J)` 不超过 `2 ^ tripleCost F J`。这里调用 `Nat.pow_le_pow_left`。
theorem triple_bound [Fintype F] : Fintype.card (Tables F J) ≤ 2 ^ tripleCost F J := by
  simp only [Tables, Triple, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
  unfold tripleCost
  rw [mul_comm _ (Nat.clog _ _), pow_mul (2 : ℕ), ← pow_mul]
  rw [mul_comm (2 ^ 3)]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _

variable {F J}

-- 读法：`(fun x => g (readBit J x ∘ j))` 属于 `simple F J`。
theorem one_table (j : Triple J) (g : (Fin 3 → Bool) → F) :
    (fun x => g (readBit J x ∘ j)) ∈ simple F J := by
  refine ⟨fun k z => if k = j then g z else 1, ?_⟩
  ext x
  simp [evaluate]

-- 读法：`f` 属于 `simple F J`。
theorem local_table {I : Type} [Fintype I] (f : (J → Bool) → F) (a : I → Option J)
    (hb : Fintype.card I ≤ 3)
    (hf : ∀ x y, (∀ j, readBit J x (a j) = readBit J y (a j)) → f x = f y) :
    f ∈ simple F J := by
  obtain ⟨e⟩ : Nonempty (I ↪ Fin 3) := Function.Embedding.nonempty_of_card_le (by simpa using hb)
  let addr := Function.extend e a (fun _ => none)
  let pull (x : J → Bool) := readBit J x ∘ addr
  have he (x y : J → Bool) (h : pull x = pull y) : f x = f y := by
    apply hf
    intro i
    simpa only [pull, Function.comp_apply, addr, e.injective.extend_apply] using congrFun h (e i)
  let k (t : Fin 3 → Bool) := f (Function.invFun pull t)
  have h := one_table addr k
  convert h using 1
  funext x
  exact he _ _ (Function.invFun_eq ⟨x, rfl⟩).symm

-- 读法：`(fun x => ∏ i ∈ S, f i x)` 属于 `simple F J`。这里调用 `Finset.prod_apply`。
theorem prod_simple {I : Type} (S : Finset I) (f : I → (J → Bool) → F)
    (hf : ∀ i ∈ S, f i ∈ simple F J) :
    (fun x => ∏ i ∈ S, f i x) ∈ simple F J := by
  convert (simple F J).prod_mem hf using 1
  ext
  exact (Finset.prod_apply ..).symm

-- 读法：`(fun x => if readBit J x a = readBit J x b then (1 : F) else 0)` 属于 `simple F J`。使用 `one_table` 给出的结论。
theorem check_simple (a b : Option J) :
    (fun x => if readBit J x a = readBit J x b then (1 : F) else 0) ∈ simple F J :=
  one_table ![a, b, none] (fun t => if t 0 = t 1 then 1 else 0)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# 重置站点的局部描述

**英文原文**

A local description of a reset station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring
open scoped Classical
variable {F : Type} [Field F]

-- 读法：在后续公式中，`Addr` 是 `B e ⊕ B e` 的缩写。
abbrev Addr (e : ℕ) := B e ⊕ B e
-- 读法：在后续公式中，`Control` 是 `Bool × B S.k × (B S.e → Addr e)` 的缩写。
abbrev Control (S : Scheme F) (e : ℕ) := Bool × B S.k × (B S.e → Addr e)
-- 读法：在后续公式中，`Shape` 是 `Fin (2 ^ e + 1) × (B e → Control S e) × Tables F (Addr e)` 的缩写。
abbrev Shape (S : Scheme F) (e : ℕ) := Fin (2 ^ e + 1) × (B e → Control S e) × Tables F (Addr e)
-- 读法：在后续公式中，`Recipe` 是 `Shape S e × (B e → B S.ℓ)` 的缩写。
abbrev Recipe (S : Scheme F) (e : ℕ) := Shape S e × (B e → B S.ℓ)

variable {S : Scheme F} {e : ℕ}

-- 读法：逐一匹配以下输入模式：`.inl i, j`、`.inr i, j`。
def fetch {n u : ℕ} (x : B e → ℕ → Bool) (y : Fin n × Fin u → Bool) : Addr e → ℕ → Bool
  | .inl i, j => x i j
  | .inr i, j => if h : i.val < n ∧ j < u then y (⟨i, h.1⟩, ⟨j, h.2⟩) else false

-- 读法：`prior` 的取值由 `if c.1 then (S.decode (o.symm t)).value c.2.1 (fun i j => f (c.2.2 i) j.val) else 1` 给出。
def prior (o : B S.ℓ ≃ B S.ℓ) (c : Control S e) (t : B S.ℓ) (f : Addr e → ℕ → Bool) : F :=
  if c.1 then (S.decode (o.symm t)).value c.2.1 (fun i j => f (c.2.2 i) j.val) else 1

-- 读法：`run` 的结果类型为 `F`。
def run (o : B S.ℓ ≃ B S.ℓ) (u : ℕ) (r : Recipe S e) (x : B e → ℕ → Bool) : F :=
  ∑ y : Fin r.1.1.val × Fin u → Bool,
    (∏ i : B e, prior o (r.1.2.1 i) (r.2 i) (fetch x y)) *
      ∏ j : Fin u, evaluate F (Addr e) r.1.2.2 (fun i => fetch x y i j.val)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# 重置表的规范标签

构造方案存储定长控制量，并按原标签各自的实际位长存储这些标签。对每个函数选用最小标签，可使输出记录与用来证明其长度界的具体构造方案无关。

**英文原文**

Canonical labels for reset tables

A recipe stores fixed-size controls and the old labels at their actual
bit lengths. Choosing the least label for a function makes the emitted
record independent of the recipe witnessing its length bound.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring
open scoped Classical

variable {F : Type} [Fintype F] (S : Scheme F) (e : ℕ)

-- 读法：`shapeWidth` 的取值由 `e + 1 + 2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1)) + tripleCost F (Addr e)` 给出。
def shapeWidth := e + 1 + 2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1)) + tripleCost F (Addr e)
-- 读法：`overhead` 的取值由 `shapeWidth S e + 2 ^ e * Dense.used S.ℓ` 给出。
def overhead := shapeWidth S e + 2 ^ e * Dense.used S.ℓ

-- 读法：`Fintype.card (Addr e)` 等于 `2 ^ (e + 1)`。
private theorem card_addr : Fintype.card (Addr e) = 2 ^ (e + 1) := by
  simp only [Addr, B, Fintype.card_sum, Fintype.card_fin, pow_succ, mul_two]

omit [Fintype F] in
-- 读法：`Fintype.card (Control S e)` 等于 `2 ^ (1 + S.k + 2 ^ S.e * (e + 1))`。
private theorem card_control : Fintype.card (Control S e) = 2 ^ (1 + S.k + 2 ^ S.e * (e + 1)) := by
  simp only [Control, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, card_addr, B, Fintype.card_fin]
  rw [← pow_mul, mul_comm (e + 1), pow_add, pow_add, pow_one, mul_assoc]

omit [Fintype F] in
-- 读法：`Fintype.card (B e → Control S e)` 等于 `2 ^ (2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1)))`。
private theorem card_controls : Fintype.card (B e → Control S e) = 2 ^ (2 ^ e * (1 + S.k + 2 ^ S.e * (e + 1))) := by
  rw [Fintype.card_fun, card_control, ← pow_mul, mul_comm]
  simp only [B, Fintype.card_fin]

-- 读法：`Fintype.card (A × B × C)` 不超过 `2 ^ (a + b + c)`。这里调用 `Nat.mul_le_mul`。
private theorem prod_bound (A B C : Type) [Fintype A] [Fintype B] [Fintype C] (a b c : ℕ)
    (ha : Fintype.card A ≤ 2 ^ a) (hb : Fintype.card B ≤ 2 ^ b) (hc : Fintype.card C ≤ 2 ^ c) :
    Fintype.card (A × B × C) ≤ 2 ^ (a + b + c) := by
  rw [Fintype.card_prod, Fintype.card_prod, pow_add, pow_add, mul_assoc]
  exact Nat.mul_le_mul ha (Nat.mul_le_mul hb hc)

-- 读法：`@Fintype.card _ I` 不超过 `2 ^ tripleCost F J`。
private theorem tables_bound (J : Type) [Fintype J] (I : Fintype (Tables F J)) :
    @Fintype.card _ I ≤ 2 ^ tripleCost F J := by
  convert! triple_bound F J using 2

-- 读法：`Fintype.card (Shape S e)` 不超过 `2 ^ shapeWidth S e`。这里调用 `Nat.add_le_add_left`。
theorem shape_bound : Fintype.card (Shape S e) ≤ 2 ^ shapeWidth S e := by
  have hn : Fintype.card (Fin (2 ^ e + 1)) ≤ 2 ^ (e + 1) := by
    rw [Fintype.card_fin, pow_succ, mul_two]
    exact Nat.add_le_add_left (Nat.two_pow_pos _) _
  exact prod_bound _ _ _ _ _ _ hn (card_controls S e).le (tables_bound (Addr e) inferInstance)

-- 读法：`shapeCode` 的取值由 `(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (shape_bound S e))` 给出。
private def shapeCode : Shape S e ↪ B (shapeWidth S e) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (shape_bound S e))

variable {S e}

-- 读法：`recipeCode` 的取值由 `Dense.pack (shapeCode S e r.1, r.2)` 给出。
def recipeCode (r : Recipe S e) := Dense.pack (shapeCode S e r.1, r.2)

-- 读法：`(recipeCode (S := S) (e := e))` 是单射。这里调用 `Prod.ext`。
private theorem recipeCode_inj : Function.Injective (recipeCode (S := S) (e := e)) := by
  intro r s h
  obtain ⟨ha, hb⟩ := Prod.mk.inj (Dense.injective h)
  exact Prod.ext ((shapeCode S e).injective ha) hb

-- 读法：`Dense.used (recipeCode r)` 不超过 `overhead S e + Dense.cost r.2`。
theorem recipe_length (r : Recipe S e) :
    Dense.used (recipeCode r) ≤ overhead S e + Dense.cost r.2 := by
  simpa only [recipeCode, overhead, Dense.header, B, Fintype.card_fin] using
    Dense.length (shapeCode S e r.1, r.2)

variable [Field F] (o : B S.ℓ ≃ B S.ℓ) (u cap : ℕ)

-- 读法：`decoder` 的取值由 `run o u (Function.invFun (recipeCode (S := S) (e := e)) c.val)` 给出。
def decoder (c : B cap) : (B e → ℕ → Bool) → F :=
  run o u (Function.invFun (recipeCode (S := S) (e := e)) c.val)

variable (target : (B e → ℕ → Bool) → F)

-- 读法：`candidates` 的取值由 `Finset.univ.filter (fun c : B cap => decoder o u cap c = target)` 给出。
private def candidates := Finset.univ.filter (fun c : B cap => decoder o u cap c = target)

-- 读法：当 `h : (candidates o u cap target).Nonempty` 成立时取 `(candidates o u cap target).min' h`，否则取 `0`。
def canonical : B cap :=
  if h : (candidates o u cap target).Nonempty then (candidates o u cap target).min' h else 0

variable {o u cap target}

-- 读法：`decoder o u cap (canonical o u cap target) = target` 与 `Dense.used (canonical o u cap target).val ≤ overhead S e + Dense.cost r.2` 同时成立。
theorem canonical_spec (r : Recipe S e) (hr : run o u r = target)
    (hc : overhead S e + Dense.cost r.2 ≤ cap) :
    decoder o u cap (canonical o u cap target) = target ∧
      Dense.used (canonical o u cap target).val ≤ overhead S e + Dense.cost r.2 := by
  let c : B cap := ⟨recipeCode r, Dense.used_le.mp ((recipe_length r).trans hc)⟩
  let t := candidates o u cap target
  have ht : c ∈ t := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change run o u (Function.invFun recipeCode (recipeCode r)) = target
    rw [Function.leftInverse_invFun recipeCode_inj r]
    exact hr
  have hn : t.Nonempty := ⟨c, ht⟩
  have he : canonical o u cap target = t.min' hn := dite_eq_left hn
  rw [he]
  refine ⟨(Finset.mem_filter.mp (t.min'_mem hn)).2, Dense.used_le.mpr ?_⟩
  exact lt_of_le_of_lt (t.min'_le c ht) (Dense.used_le.mp (recipe_length r))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# 收缩后表的短标签

完整保留短指针行。只有递归生成的标签需要变长打包。未占槽位用零标签，因此不占标签比特。

**英文原文**

Short tags for a contracted table

Keep the short pointer rows intact. Only the recursively generated
labels need variable-length packing. Unoccupied slots use the zero
tag and so consume no tag bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring
open scoped Classical
variable {F A T : Type} {m e l s d : ℕ}

namespace Dense

-- 读法：`split` 的取值由 `((code m e 0 s d).serial (c.1, fun i => ((c.2 i).1, 0, (c.2 i).2.2)), fun i => (c.2 i).2.1)` 给出。
def split (c : (code m e l s d).obj) : B (code m e 0 s d).width × (B m → B l) :=
  ((code m e 0 s d).serial (c.1, fun i => ((c.2 i).1, 0, (c.2 i).2.2)), fun i => (c.2 i).2.1)

-- 读法：`(split (m := m) (e := e) (l := l) (s := s) (d := d))` 是单射。按 `Prod.ext` 的外延性准则比较各分量。
private theorem split_inj : Function.Injective (split (m := m) (e := e) (l := l) (s := s) (d := d)) := by
  intro x y h
  obtain ⟨a, b⟩ := Prod.mk.inj h
  obtain ⟨u, v⟩ := Prod.mk.inj ((code m e 0 s d).serial.injective a)
  refine Prod.ext u (funext fun i => ?_)
  have he := congrFun v i
  exact Prod.ext (Prod.mk.inj he).1 (Prod.ext (congrFun b i) (Prod.mk.inj (Prod.mk.inj he).2).2)

-- 读法：`index` 的取值由 `pack (split c)` 给出。
def index (c : (code m e l s d).obj) := pack (split c)

-- 读法：`(index (m := m) (e := e) (l := l) (s := s) (d := d))` 是单射。使用 `injective.comp` 给出的结论。
theorem index_inj : Function.Injective (index (m := m) (e := e) (l := l) (s := s) (d := d)) :=
  injective.comp split_inj

-- 读法：`overhead` 的取值由 `(code m e 0 s d).width + 2 ^ m * used l` 给出。
def overhead (m e l s d : ℕ) := (code m e 0 s d).width + 2 ^ m * used l

-- 读法：`used (index c)` 不超过 `overhead m e l s d + ∑ i, used ((c.2 i).2.1).val`。
theorem index_length (c : (code m e l s d).obj) :
    used (index c) ≤ overhead m e l s d + ∑ i, used ((c.2 i).2.1).val := by
  simpa only [index, overhead, header, cost, split, B, Fintype.card_fin] using length (split c)

-- 读法：当 `h : index c < 2 ^ q` 成立时取 `⟨index c, h⟩`，否则取 `0`。
/-- 只查询小于选定上限的标签。对其他输入，计算可以返回占位值。

英文原文：Only tags below the chosen limit are requested. On other inputs
the computation may return a dummy value.
-/
def encode (q : ℕ) (c : (code m e l s d).obj) : B q :=
  if h : index c < 2 ^ q then ⟨index c, h⟩ else 0

-- 读法：`unpack` 的取值由 `Function.invFun index v.val` 给出。
def unpack (q : ℕ) (v : B q) : (code m e l s d).obj :=
  Function.invFun index v.val

-- 读法：`(encode q c).val` 等于 `index c`。
theorem encode_val {q : ℕ} {c : (code m e l s d).obj} (h : used (index c) ≤ q) :
    (encode q c).val = index c := by simp [encode, used_le.mp h]

-- 读法：`unpack q (encode q c)` 等于 `c`。这里调用 `Function.leftInverse_invFun`。
theorem unpack_encode {q : ℕ} {c : (code m e l s d).obj} (h : used (index c) ≤ q) :
    unpack q (encode q c) = c := by
  rw [unpack, encode_val h]
  exact Function.leftInverse_invFun index_inj c

end Dense

namespace Packed
variable [Fintype A] (p : Packed A T e l s d) (g : A ↪ B m) (f : T ↪ B e)

-- 读法：`Dense.used (Dense.index (p.encode g f))` 不超过 `Dense.overhead m e l s d + ∑ i, Dense.used (p.tag i).val`。这里调用 `Dense.used_zero`。
theorem index_length :
    Dense.used (Dense.index (p.encode g f)) ≤
      Dense.overhead m e l s d + ∑ i, Dense.used (p.tag i).val := by
  refine (Dense.index_length _).trans_eq (congrArg _ ?_)
  symm
  refine Fintype.sum_of_injective g g.injective _ _ ?_ ?_
  · intro j hj
    simp only [encode, Function.extend_apply' _ _ _ hj]
    exact Dense.used_zero
  · intro i
    rw [store]

-- 读法：`Dense.unpack q (Dense.encode q (p.encode g f))` 等于 `p.encode g f`。通过传递性衔接 `Dense.unpack_encode` 与 `h`。
theorem unpack_encode {q : ℕ} (h : Dense.overhead m e l s d + (∑ i, Dense.used (p.tag i).val) ≤ q) :
    Dense.unpack q (Dense.encode q (p.encode g f)) = p.encode g f :=
  Dense.unpack_encode ((p.index_length g f).trans h)

end Packed
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 节省连线的步骤所用的局部记录

解码器只读取块记录。全局名称出现在宿主的公共邻居数组中。空记录没有参数，权重为一，在正特征下也如此。

**英文原文**

Local records for a wire-saving step

The decoder reads only the block record. Global names appear in the
host's common neighbor array. The vacant record has no arguments
and weight one, including in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Post
open Coloring

-- 读法：在后续公式中，`field` 是 `.pair (.addr ℓ) (.pair .bit (.pair .bit (.pair (.addr d) (.addr e))))` 的缩写。
/-- 依次为长度索引、方向、挂接标志、邻居槽位和对端槽位。

英文原文：Length index, direction, attached flag, neighbor slot, peer slot.
-/
abbrev field (d e ℓ : ℕ) : Format :=
  .pair (.addr ℓ) (.pair .bit (.pair .bit (.pair (.addr d) (.addr e))))

-- 读法：在后续公式中，`record` 是 `.pair .bit (.pair (.vec e (field d e ℓ)) Y)` 的缩写。
abbrev record (d e ℓ : ℕ) (Y : Format) : Format :=
  .pair .bit (.pair (.vec e (field d e ℓ)) Y)

-- 读法：`(record d e ℓ Y).width` 等于 `1 + (2 ^ e * (ℓ + (1 + (1 + (d + e)))) + Y.width)`。
theorem width_record (d e ℓ : ℕ) (Y : Format) :
    (record d e ℓ Y).width = 1 + (2 ^ e * (ℓ + (1 + (1 + (d + e)))) + Y.width) := by
  simp [record, field]

variable {F : Type} [Field F] {m d h e l s ℓ a : ℕ} {Y : Format}

-- 读法：在后续公式中，`unused` 是 `(0, false, false, 0, 0)` 的缩写。
abbrev unused : (field d e ℓ).obj := (0, false, false, 0, 0)

-- 读法：`vacant` 的取值由 `(false, fun _ => unused, Y.serial.symm 0)` 给出。
def vacant : (record d e ℓ Y).obj := (false, fun _ => unused, Y.serial.symm 0)

-- 读法：用字段 `width`、`direction`、`peer`、`value` 构造 `Pattern F d 0 e`。
def pattern (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (r : (record d e ℓ Y).obj) : Pattern F d 0 e where
  width _ t := M.length (r.2.1 t).1
  direction _ t := (r.2.1 t).2.1
  peer _ t := if (r.2.1 t).2.2.1 then some ((r.2.1 t).2.2.2.1, 0, (r.2.1 t).2.2.2.2) else none
  value _ x := if r.1 then M.decode (fun t => M.length (r.2.1 t).1) (unpack r.2.2) (fun i => x i.1 i.2) else 1

-- 读法：在后续公式中，`scheme` 是 `⟨m, d, h, 0, e, (record d e ℓ Y).width, pattern M unpack ∘ (record d e ℓ Y).serial.symm⟩` 的缩写。
abbrev scheme (m d h e : ℕ) (Y : Format) (M : Menu F l s ℓ)
    (unpack : Y.obj → (code a e l s ℓ).obj) : Scheme F :=
  ⟨m, d, h, 0, e, (record d e ℓ Y).width, pattern M unpack ∘ (record d e ℓ Y).serial.symm⟩

-- 读法：输入 `v` 时返回 `(nav v, (record d e ℓ Y).serial ∘ R v)`。
def write (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (nav : B m → B d → B m) (R : B m → B h → (record d e ℓ Y).obj) :
    (scheme m d h e Y M unpack).format.obj :=
  fun v => (nav v, (record d e ℓ Y).serial ∘ R v)

-- 读法：`(scheme m d h e Y M unpack).pattern (write M unpack nav R) v` 等于 `pattern M unpack (R v.1 v.2.1)`。
theorem read_write (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (nav : B m → B d → B m) (R : B m → B h → (record d e ℓ Y).obj)
    (v : (scheme m d h e Y M unpack).Vtx) :
    (scheme m d h e Y M unpack).pattern (write M unpack nav R) v = pattern M unpack (R v.1 v.2.1) :=
  congrArg (pattern M unpack) ((record d e ℓ Y).serial.symm_apply_apply (R v.1 v.2.1))

-- 读法：`(scheme m d h e Y M unpack).table out v x` 等于 `if r.1 then M.decode (fun t => (scheme m d h e Y M unpack).width out (v, t)) (unpack r.2.2) x else 1`。
theorem table_eq (M : Menu F l s ℓ) (unpack : Y.obj → (code a e l s ℓ).obj)
    (out : (scheme m d h e Y M unpack).format.obj)
    (v : (scheme m d h e Y M unpack).Vtx) (r : (record d e ℓ Y).obj)
    (hr : (scheme m d h e Y M unpack).pattern out v = pattern M unpack r)
    (x : (scheme m d h e Y M unpack).LocalPin out v → Bool) :
    (scheme m d h e Y M unpack).table out v x = if r.1 then
      M.decode (fun t => (scheme m d h e Y M unpack).width out (v, t)) (unpack r.2.2) x else 1 := by
  have eq (P : Pattern F d 0 e) (he : P = pattern M unpack r) (j : B 0)
      (x : Positions (P.width j) → Bool) :
      P.value j (fun s i => x ⟨s, i⟩) =
        if r.1 then M.decode (P.width j) (unpack r.2.2) x else 1 := by
    subst P
    rfl
  exact eq _ hr _ x

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Post
end

/-!
# 将出现位置标签中的长段置于高位端

用一个固定双射在实际序列化次序与测量标签长度的次序之间转换。在下一阶段将原站点作为原子时，也采用同一次序。

**英文原文**

Putting the long part of an occurrence label at the high end

A fixed bijection translates between the physical serialization and
the ordering used to measure label lengths. The same ordering is
used when an old station becomes an atom at the next stage.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring
open scoped Classical

namespace Dense

-- 读法：`concat` 的取值由 `finProdFinEquiv.trans (finCongr (pow_add 2 h l).symm)` 给出。
def concat (h l : ℕ) : B h × B l ≃ B (h + l) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 h l).symm)

-- 读法：`used (concat h l (a, b)).val` 不超过 `used a.val + l`。
theorem concat_length {h l : ℕ} (a : B h) (b : B l) :
    used (concat h l (a, b)).val ≤ used a.val + l := by
  rw [used_le, pow_add 2 (used a.val) l]
  change b.val + 2 ^ l * a.val < _
  calc
    _ < 2 ^ l + 2 ^ l * a.val := Nat.add_lt_add_right b.isLt _
    _ = (a.val + 1) * 2 ^ l := by rw [add_mul, one_mul, mul_comm a.val, add_comm]
    _ ≤ _ := Nat.mul_le_mul_right _ (used_le.mp le_rfl)

end Dense

namespace Post

-- 读法：在后续公式中，`headerFmt` 是 `Format.pair .bit (.vec e (field d e n))` 的缩写。
abbrev headerFmt (d e n : ℕ) := Format.pair .bit (.vec e (field d e n))
-- 读法：在后续公式中，`width` 是 `(record d e n (.addr l)).width` 的缩写。
abbrev width (d e n l : ℕ) := (record d e n (.addr l)).width

-- 读法：`l + (headerFmt d e n).width` 等于 `width d e n l`。
private theorem width_eq (d e n l : ℕ) : l + (headerFmt d e n).width = width d e n l := by
  simp only [width, headerFmt, record, Format.width_pair, Format.width_addr]
  omega

-- 读法：`order` 的结果类型为 `B (width d e n l) ≃ B (width d e n l)`。
def order (d e n l : ℕ) : B (width d e n l) ≃ B (width d e n l) :=
  (record d e n (.addr l)).serial.symm |>.trans ((Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodComm _ _).trans (((Equiv.refl _).prodCongr (headerFmt d e n).serial).trans
      ((Dense.concat _ _).trans (finCongr (congrArg (2^·) (width_eq d e n l)))))))

-- 读法：`Dense.used (order d e n l ((record d e n (.addr l)).serial c)).val` 不超过 `Dense.used c.2.2.val + (headerFmt d e n).width`。这里调用 `Dense.concat_length`。
theorem order_length {d e n l : ℕ} (c : (record d e n (.addr l)).obj) :
    Dense.used (order d e n l ((record d e n (.addr l)).serial c)).val ≤
      Dense.used c.2.2.val + (headerFmt d e n).width := by
  simp only [order, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Dense.concat_length c.2.2 ((headerFmt d e n).serial (c.1, c.2.1))

end Post

namespace Kind
variable {F : Type} [Field F] (S : Scheme F) (P : Packing.Gadget F) (c : ℕ)

-- 读法：在后续公式中，`Small` 是 `B S.k ⊕ Role P ⊕ B c` 的缩写。
abbrev Small := B S.k ⊕ Role P ⊕ B c

-- 读法：`width` 的取值由 `Dense.used (Fintype.card (Small S P c))` 给出。
def width := Dense.used (Fintype.card (Small S P c))

-- 读法：`tags` 的取值由 `(Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (le_of_lt (Dense.used_le.mp le_rfl)))` 给出。
private def tags : Small S P c ↪ B (width S P c) :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (le_of_lt (Dense.used_le.mp le_rfl)))

variable (o : B S.ℓ ≃ B S.ℓ)

-- 读法：逐一匹配以下输入模式：`.inl x`、`.inr x`。
private def parts : Kind S P c → B S.ℓ × Small S P c
  | .inl x => (o x.1, .inl x.2)
  | .inr x => (0, .inr x)

-- 读法：`(parts S P c o)` 是单射。
private theorem parts_inj : Function.Injective (parts S P c o) := by
  rintro (⟨x, i⟩|x) (⟨y, j⟩|y) h <;> simp [parts] at h ⊢ <;> exact h

-- 读法：`names` 的结果类型为 `Kind S P c ↪ B (S.ℓ + width S P c)`。
def names : Kind S P c ↪ B (S.ℓ + width S P c) :=
  (⟨parts S P c o, parts_inj S P c o⟩ : Kind S P c ↪ _).trans
    (((Function.Embedding.refl _).prodMap (tags S P c)).trans (Dense.concat _ _).toEmbedding)

-- 读法：`carried` 的取值由 `Dense.used (parts S P c o j).1.val` 给出。
def carried (j : Kind S P c) := Dense.used (parts S P c o j).1.val

-- 读法：`Dense.used (names S P c o j).val` 不超过 `carried S P c o j + width S P c`。使用 `Dense.concat_length` 给出的结论。
theorem names_length (j : Kind S P c) :
    Dense.used (names S P c o j).val ≤ carried S P c o j + width S P c :=
  Dense.concat_length _ _

-- 读法：`carried S P c o (.inl (x, i))` 等于 `Dense.used (o x).val`。两端由定义化简为同一项。
@[simp] theorem carried_old (x : B S.ℓ) (i : B S.k) :
    carried S P c o (.inl (x, i)) = Dense.used (o x).val := rfl

-- 读法：`carried S P c o (.inr i)` 等于 `0`。使用 `Dense.used_zero` 给出的结论。
@[simp] theorem carried_new (i : Role P ⊕ B c) : carried S P c o (.inr i) = 0 :=
  Dense.used_zero

end Kind

namespace Post

variable {F A T : Type} [Field F] [Fintype A]
    {m e d s n c : ℕ} (S : Scheme F) (P : Packing.Gadget F) (o : B S.ℓ ≃ B S.ℓ)
    (p : Packed A T e (S.ℓ + Kind.width S P c) s n)
    (g : A ↪ B m) (f : T ↪ B e)

-- 读法：`bookkeeping` 的取值由 `Dense.overhead m e (old + role) s n + 2 ^ m * role` 给出。
/-- 首部成本包括角色名称、宽度和指针；此前的标签上界仅以其对数影响该成本。

英文原文：Header cost includes role names, widths and pointers. It depends
on the previous label bound only through its logarithm.
-/
def bookkeeping (m e s n old role : ℕ) :=
  Dense.overhead m e (old + role) s n + 2 ^ m * role

-- 读法：`Dense.used (Dense.index (p.encode g f))` 不超过 `bookkeeping m e s n S.ℓ (Kind.width S P c) + ∑ i, Kind.carried S P c o (t i)`。这里调用 `Finset.sum_le_sum`。
theorem packed_length (t : A → Kind S P c) (ht : p.tag = Kind.names S P c o ∘ t) :
    Dense.used (Dense.index (p.encode g f)) ≤
      bookkeeping m e s n S.ℓ (Kind.width S P c) + ∑ i, Kind.carried S P c o (t i) := by
  refine (p.index_length g f).trans ?_
  have ha : Fintype.card A ≤ 2 ^ m := by simpa using Fintype.card_le_of_injective g g.injective
  have h : (∑ i, Dense.used (p.tag i).val) ≤ ∑ i, (Kind.carried S P c o (t i) + Kind.width S P c) := by
    rw [ht]
    exact Finset.sum_le_sum fun i _ => Kind.names_length S P c o (t i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at h
  have h' := Nat.mul_le_mul_right (Kind.width S P c) ha
  unfold bookkeeping
  omega

-- 读法：结论为 `Dense.unpack l v.2.2 = p.encode g f ∧ Dense.used (order d e n l ((record d e n (.addr l)).serial v)).val ≤ (headerFmt d e n).width + bookkeeping m e s n S.ℓ (Kind.width S P c) + bound`。
/-- 接收记录只需保留各祖先的有效长度。特别地，无须将原记录的最大长度乘以候选端口数或原子数。

英文原文：The receipt need only retain the effective lengths of its
ancestors. In particular the maximum old length is not multiplied
by the number of candidate ports or atoms.
-/
theorem stored_length {l bound : ℕ} (t : A → Kind S P c)
    (ht : p.tag = Kind.names S P c o ∘ t)
    (hb : (∑ i, Kind.carried S P c o (t i)) ≤ bound)
    (hl : bookkeeping m e s n S.ℓ (Kind.width S P c) + bound ≤ l)
    (v : (record d e n (.addr l)).obj) (hv : v.2.2 = Dense.encode l (p.encode g f)) :
    Dense.unpack l v.2.2 = p.encode g f ∧
    Dense.used (order d e n l ((record d e n (.addr l)).serial v)).val ≤
      (headerFmt d e n).width + bookkeeping m e s n S.ℓ (Kind.width S P c) + bound := by
  have h := (packed_length S P o p g f t ht).trans (Nat.add_le_add_left hb _)
  refine ⟨by rw [hv]; exact Dense.unpack_encode (h.trans hl), ?_⟩
  have he := order_length v
  rw [hv, Dense.encode_val (h.trans hl)] at he
  omega

end Post
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 解码输出的区段记录

**英文原文**

Decoding the emitted span records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram}
  {q : G.Projection Δ D a}
  {m' d h' e ℓ n l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
  {u : Y.obj → (code n e l s ℓ).obj}

local notation "U" => Post.scheme m' d h' e Y M u
local notation "Face'" => Face g m P i p
local notation "Host" => endHost (p := p) (q := q)

variable (A : Allocation P G g m i p q (Post.scheme m' d h' e Y M u))

-- 读法：逐一匹配以下输入模式：`.inl j`、`.inr (b, t)`。
def header (A : Allocation P G g m i p q U) (size : Face' → B ℓ) : Face' → (Post.field d e ℓ).obj
  | .inl j => (size (.inl j), S.direction r (p.vertex j.val.1, j.val.2), false, 0, 0)
  | .inr (b, t) =>
    (size (.inr (b, t)), t, true, A.index (Host b t) (Host b (!t)), A.unitSeat b (!t))

variable {nav : B m' → B d → B m'} {R : B m' → B h' → (Post.record d e ℓ Y).obj}
  {size : Face g m P i p → B ℓ}

local notation "out" => Post.write M u nav R

-- 读法：结构的字段包括 `zero`、`length`、`active`、`vacant`、`used`。
/-- 活跃记录的字段仅由局部位置索引。未使用的参数位置长度为零，且没有对端。

英文原文：The active record fields are indexed only by the local seats.
Unused argument seats have zero length and no peer.
-/
structure Emitted (A : Allocation P G g m i p q U) (size : Face' → B ℓ) (nav : B m' → B d → B m')
    (R : B m' → B h' → (Post.record d e ℓ Y).obj) : Prop where
  zero : M.length 0 = 0
  length : ∀ j, M.length (size j) = visibleWidth g m P i p z j
  active : ∀ v, (R (A.vertex v).1 (A.vertex v).2.1).1 = true
  vacant : ∀ v : (U).Vtx, v ∉ Set.range A.vertex → (R v.1 v.2.1).1 = false
  used : ∀ j : Face', let t : (U).Span := A.span j
    (R t.1.1 t.1.2.1).2.1 t.2 = A.header size j
  idle : ∀ t : (U).Span, t ∉ Set.range A.span → (R t.1.1 t.1.2.1).2.1 t.2 = Post.unused
  hop : ∀ (b : g.Survivors m P i) t, let v := Host b t
    let w := Host b (!t)
    nav (A.host v) (A.index v w) = A.host w

namespace Emitted
variable {A} (H : A.Emitted size nav R)

include H in
-- 读法：要证明的命题是 `A.Lengths out`。
theorem lengths : A.Lengths out where
  used j := by
    rw [Scheme.width, Post.read_write]
    change M.length ((R _ _).2.1 _).1 = _
    rw [H.used j]
    rcases j with j|⟨b, t⟩ <;> exact H.length _
  idle t ht := by
    rw [Scheme.width, Post.read_write]
    change M.length ((R _ _).2.1 _).1 = _
    rw [H.idle t ht]
    exact H.zero

include H in
-- 读法：`(U).direction out (A.span (.inl j))` 等于 `S.direction r (p.vertex j.val.1, j.val.2)`。
theorem exposed_direction (j : p.BorderSpan) :
    (U).direction out (A.span (.inl j)) = S.direction r (p.vertex j.val.1, j.val.2) := by
  rw [Scheme.direction, Post.read_write]
  change ((R _ _).2.1 _).2.1 = _
  rw [H.used]
  rfl

-- 读法：要证明的命题是 `A.Agrees H.lengths hz`。
theorem agrees (hz : 0 < z)
    (hs : ∀ v t, M.decode (fun a => (U).width out (A.vertex v, a))
        (u (R (A.vertex v).1 (A.vertex v).2.1).2.2) t =
      Transcript.sample ((g.contract m P G.units hz i).table v) (t ∘ A.pin H.lengths hz v)) :
    A.Agrees H.lengths hz where
  sample v t := by
    rw [Post.table_eq M u out _ _ (Post.read_write _ _ _ _ _), H.active]
    exact hs v t
  vacant v hv t := by
    rw [Post.table_eq M u out _ _ (Post.read_write _ _ _ _ _), H.vacant v hv]
    rfl
  outside j := by
    rw [Scheme.peer, Post.read_write]
    simp only [Post.pattern, H.used, header, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  idle t ht := by
    rw [Scheme.peer, Post.read_write]
    simp only [Post.pattern, H.idle t ht, Post.unused, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  dir b t := by
    rw [Scheme.direction, Post.read_write]
    simp only [Post.pattern, H.used, header]
  link b t := by
    dsimp only
    rw [Post.read_write]
    simp only [Post.pattern, H.used, header, ↓reduceIte]
  nav b t := H.hop b t

-- 读法：结论为 `let p' := A.presentation H.lengths hz hA let b := p.toSeating.ends (boundaryEnd _ t) let b' := p'.toSeating.ends (boundaryEnd _ t) (U).width out b'.1 = S.width r b.1 ∧ (U).direction out b'.1 = S.direction r b.1 ∧ b'.2.val = b.2.val`。
/-- 原来的每个外部偏移位置都保留所属区段的长度与方向。

英文原文：Every original exterior offset retains its span length and orientation.
-/
theorem boundary (hz : 0 < z) (hA : A.Agrees H.lengths hz) (t : slots x ⊕ slots y) :
    let p' := A.presentation H.lengths hz hA
    let b := p.toSeating.ends (boundaryEnd _ t)
    let b' := p'.toSeating.ends (boundaryEnd _ t)
    (U).width out b'.1 = S.width r b.1 ∧ (U).direction out b'.1 = S.direction r b.1 ∧
      b'.2.val = b.2.val := by
  obtain ⟨j, rfl⟩ := p.exteriorBits.surjective t
  dsimp only [presentation]
  rw [p.border_pin, A.exposed_pin]
  exact ⟨H.lengths.used (.inl j.1), H.exposed_direction j.1, rfl⟩

-- 读法：对每个 `b`，`w` 不超过 `(A.presentation H.lengths hz hA).borderWidth b`。
theorem floor (hz : 0 < z) (hA : A.Agrees H.lengths hz) {w : ℕ}
    (hw : ∀ b, w ≤ p.borderWidth b) :
    ∀ b, w ≤ (A.presentation H.lengths hz hA).borderWidth b := by
  let p' := A.presentation H.lengths hz hA
  intro b
  let j : p'.BorderBit := ⟨b, ⟨0, b.property.1⟩⟩
  obtain ⟨t, ht⟩ := p.exteriorBits.surjective (p'.exteriorBits j)
  have h := (H.boundary hz hA (p'.exteriorBits j)).1
  rw [p'.border_pin, ← ht, p.border_pin] at h
  exact (hw _).trans_eq h.symm

end Emitted
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end

/-!
# 构造可见区段记录

**英文原文**

Constructing the visible span records
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z a : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram}
  {q : G.Projection Δ D a}
  {m' d h' e ℓ n l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
  {u : Y.obj → (code n e l s ℓ).obj}

local notation "U" => Post.scheme m' d h' e Y M u
local notation "Face'" => Face g m P i p
local notation "Host" => endHost (p := p) (q := q)

variable (A : Allocation P G g m i p q (Post.scheme m' d h' e Y M u))

variable (size : Face g m P i p → B ℓ) (data : Site G.V h → Y.obj)

-- 读法：`fields` 的取值由 `Function.extend (A.seat v) (fun j => A.header size j.val) (fun _ => Post.unused)` 给出。
def fields (v : Site G.V h) : B e → (Post.field d e ℓ).obj :=
  Function.extend (A.seat v) (fun j => A.header size j.val) (fun _ => Post.unused)

-- 读法：`localRecord` 的取值由 `(true, A.fields size v, data v)` 给出。
def localRecord (v : Site G.V h) : (Post.record d e ℓ Y).obj :=
  (true, A.fields size v, data v)

-- 读法：`records` 的取值由 `Function.extend A.vertex (A.localRecord size data) (fun _ => Post.vacant) (x, y, 0)` 给出。
def records (x : B m') (y : B h') : (Post.record d e ℓ Y).obj :=
  Function.extend A.vertex (A.localRecord size data) (fun _ => Post.vacant) (x, y, 0)

-- 读法：`A.records size data (A.vertex v).1 (A.vertex v).2.1` 等于 `A.localRecord size data v`。使用 `A.vertex.injective.extend_apply` 给出的结论。
theorem record_at (v : Site G.V h) :
    A.records size data (A.vertex v).1 (A.vertex v).2.1 = A.localRecord size data v :=
  A.vertex.injective.extend_apply _ _ v

-- 读法：`A.records size data v.1 v.2.1` 等于 `Post.vacant`。这里调用 `Function.extend_apply'`。
theorem record_vacant (v : (U).Vtx) (hv : v ∉ Set.range A.vertex) :
    A.records size data v.1 v.2.1 = Post.vacant := by
  have he : (v.1, v.2.1, (0 : B 0)) = v := Prod.ext rfl (Prod.ext rfl (Fin.eq_zero _).symm)
  unfold records
  rw [he]
  exact Function.extend_apply' _ _ _ hv

variable (nav : B m' → B d → B m')

-- 读法：要证明的命题是 `A.Emitted size nav (A.records size data)`。
theorem emitted (h₀ : M.length 0 = 0) (hsize : ∀ j, M.length (size j) = visibleWidth g m P i p z j)
    (hop : ∀ (b : g.Survivors m P i) t, nav (A.host (Host b t))
      (A.index (Host b t) (Host b (!t))) = A.host (Host b (!t))) :
    A.Emitted size nav (A.records size data) where
  zero := h₀
  length := hsize
  active v := by rw [record_at]; rfl
  vacant v hv := by rw [record_vacant _ _ _ _ hv]; rfl
  used j := by
    let v := whereAt g m P G.units i p j
    change (A.records size data (A.vertex v).1 (A.vertex v).2.1).2.1 (A.slot j) = _
    rw [record_at]
    let e : Visible g m P G.units i p v := ⟨j, rfl⟩
    change A.fields size v (A.seat v e) = A.header size e.val
    rw [fields, (A.seat v).injective.extend_apply]
  idle t ht := by
    rcases t with ⟨v, j⟩
    by_cases hv : v ∈ Set.range A.vertex
    -- 推导：从 `hv` 中取出 `w, rfl`。
    · obtain ⟨w, rfl⟩ := hv
      rw [record_at]
      have hn : j ∉ Set.range (A.seat w) := by
        rintro ⟨e, rfl⟩
        exact ht ⟨e.val, Prod.ext (congrArg A.vertex e.property) (A.slot_eq w e)⟩
      change A.fields size w j = _
      rw [fields, Function.extend_apply' _ _ _ hn]
    · rw [record_vacant _ _ _ _ hv]
      rfl
  hop := hop

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Allocation
end
