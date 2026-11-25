-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryEfficient
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Coloring.Pad

/-!
# 用于有限检测的置换群

每种情景都为每个高度选取一个输入置换。在这些输入上求值给出群同态。控制器的选择可依赖高度，与输入无关。

**英文原文**

The permutation group for finite detection

A world chooses one input permutation at each height. Evaluation at
these inputs is a group homomorphism. The choice of a controller
depends on the height but is independent of the input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open scoped Classical
variable {F J : Type} [Field F] {X : J → Type} {h : J → ℕ} {e : ∀ j, X j ↪ B (h j)}

-- 读法：要证明的命题是 `Efficient F e g⁻¹`。
theorem Efficient.inv {g : Family X} (hg : Efficient F e g) : Efficient F e g⁻¹ := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨max c 100 + 1, fun j => ?_⟩
  obtain ⟨f, hf, he⟩ := hc j
  obtain ⟨v, hv, hi⟩ := cheap_inverse F (h j)
  refine ⟨_, hf.comp hv, fun p => ?_⟩
  simp only [Function.comp_apply, he, pack, Pi.inv_apply, map_inv]
  exact hi _

variable (F e)

-- 读法：用字段 `carrier`、`one_mem'`、`mul_mem'`、`inv_mem'` 构造 `Subgroup (Family X)`。
def controllers : Subgroup (Family X) where
  carrier := {g | Efficient F e g}
  one_mem' := efficient_fixed F e 1
  mul_mem' := Efficient.mul
  inv_mem' := Efficient.inv

-- 读法：`target` 的取值由 `⟨fun _ p => p, efficient_target F e⟩` 给出。
def target : controllers F e := ⟨fun _ p => p, efficient_target F e⟩

-- 读法：用字段 `toFun`、`map_one'`、`map_mul'` 构造 `controllers F e →* (∀ j, Equiv.Perm (X j))`。
def read (t : ∀ j, Equiv.Perm (X j)) : controllers F e →* (∀ j, Equiv.Perm (X j)) where
  toFun g j := g.val j (t j)
  map_one' := rfl
  map_mul' _ _ := rfl

-- 读法：用字段 `toFun`、`map_one'`、`map_mul'` 构造 `controllers F e →* Equiv.Perm (X j)`。
/-- 固定高度和输入后，群直接作用于标签。指定目标按该输入所给的置换作用。

英文原文：At a fixed height and a given input the group acts directly on the
labels. The distinguished target acts by that input permutation.
-/
def run (j : J) (p : Equiv.Perm (X j)) : controllers F e →* Equiv.Perm (X j) where
  toFun g := g.val j p
  map_one' := rfl
  map_mul' _ _ := rfl

variable [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]

-- 读法：用字段 `World`、`read`、`fixed`、`read_fixed` 构造 `Routing.PermSystem X (controllers F e)`。
def system {c : ℕ} (H : Factors F c) : Routing.PermSystem X (controllers F e) where
  World := ∀ j, Equiv.Perm (X j)
  read := read F e
  fixed g := ⟨fun j _ => g j, efficient_fixed F e g⟩
  read_fixed _ _ := rfl
  factor s g hg := by
    have hf (j : J) (p : Equiv.Perm (X j)) (x : X j) :
        (s j (g.val j p x)).1 = (s j x).1 := by
      let t := Function.update (fun j => (1 : Equiv.Perm (X j))) j p
      have he := hg t j x
      change (s j (g.val j (t j) x)).1 = _ at he
      simpa [t] using he
    obtain ⟨u, v, w, hu, hv, hw, he, hu', hv', hw'⟩ := Efficient.factor s H g.property hf
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩, Subtype.ext he,
      fun t j => hu' j (t j), fun t j => hv' j (t j), fun t j => hw' j (t j)⟩

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# 带标签路由的高效跳转与局部价格检验

固定候选跳转集中的每个跳转，都可用规模近线性的控制器从输入置换算出对应的置换。在给定输入前就已固定其分组。

**英文原文**

Efficient hops and local price tests for tagged routing

A member of the fixed hop menu computes its permutation from the
input permutation by a controller of near-linear size. Its groups
are fixed before the input is given.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Coloring
open scoped Pointwise BigOperators Classical

-- 读法：结构的字段包括 `labels`、`size`、`embed`、`base`、`initial`。
structure Routes (F : Type) [Field F] (m : ℕ) where
  labels : ℕ → Type
  [finiteLabels : ∀ h, Fintype (labels h)]
  [inhabitedLabels : ∀ h, Nonempty (labels h)]
  size : ∀ h, 2 ^ h ≤ Fintype.card (labels h) ∧ Fintype.card (labels h) < 2 ^ (h + 1)
  embed : ∀ h, labels h ↪ Coloring.B (h + 1)
  base : ∀ h, Coloring.B h ↪ labels h
  initial : ∀ h i, (embed h (base h i)).val = i.val
  Plane : Type
  moves : Plane → Subgroup (controllers F embed)
  params : Parameters F moves (Coloring.target F embed)⁻¹
  overhead : ℕ
  groups : ∀ g ∈ params.core, ∀ h : ℕ, ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B)
    (f : labels h ≃ A × B), Fintype.card B ≤ 2 ^ (h / m + overhead) ∧
      ∀ σ i, (f (g.val h σ i)).1 = (f i).1

attribute [instance] Routes.finiteLabels Routes.inhabitedLabels

variable {F : Type} [Field F] {m : ℕ}

-- 读法：在后续公式中，`Routes.onLabels` 是 `MulAction.compHom _ ((Equiv.Perm.viaEmbeddingHom (T.embed h)).comp (Coloring.run F T.embed h σ))` 的缩写。
abbrev Routes.onLabels (T : Routes F m) (h : ℕ) (σ : Equiv.Perm (T.labels h)) :
    MulAction (controllers F T.embed) (Coloring.B (h + 1)) :=
  MulAction.compHom _ ((Equiv.Perm.viaEmbeddingHom (T.embed h)).comp (Coloring.run F T.embed h σ))

-- 读法：在后续公式中，`Routes.action` 是 `T.onLabels h (σ.viaEmbedding (T.base h))` 的缩写。
abbrev Routes.action (T : Routes F m) (h : ℕ) (σ : Equiv.Perm (Coloring.B h)) :
    MulAction (controllers F T.embed) (Coloring.B (h + 1)) :=
  T.onLabels h (σ.viaEmbedding (T.base h))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 计算可选路由的有限集合

通过增加不动点填充以列表给出的置换。若控制器数目固定，并行求值所需规模相对于输入为近线性。

**英文原文**

Computing the finite menu of routes

Pad a listed permutation by fixed points. For a fixed number of
controllers, parallel evaluation has near-linear size in the input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Coloring
open scoped Classical

-- 读法：逐一匹配以下输入模式：`0, _`、`h + 1, x`。
private def extendWord : (h : ℕ) → Val (word h) → Val (word (h + 1))
  | 0, _ => (false, ())
  | h + 1, x => (x.1, extendWord h x.2)

-- 读法：`Lookup.value (h + 1) (extendWord h x)` 等于 `Lookup.value h x`。对 `h` 作归纳。
private theorem extend_value (h : ℕ) (x : Val (word h)) :
    Lookup.value (h + 1) (extendWord h x) = Lookup.value h x := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change _ + 2 * Lookup.value (h + 1) (extendWord h x.2) = _
    rw [ih]
    rfl

-- 读法：`(∃ i : slots (word h), ∀ x, bits (word (h + 1)) (extendWord h x) j = bits (word h) x i)`、`∀ x, bits (word (h + 1)) (extendWord h x) j = false` 至少有一项成立。对 `h` 作归纳。
private theorem extend_bits (h : ℕ) (j : slots (word (h + 1))) :
    (∃ i : slots (word h), ∀ x, bits (word (h + 1)) (extendWord h x) j = bits (word h) x i) ∨
      ∀ x, bits (word (h + 1)) (extendWord h x) j = false := by
  induction h with
  | zero =>
    right
    cases j with
    | inl => exact fun _ => rfl
    | inr a => exact a.elim
  | succ h ih =>
    cases j with
    | inl a => exact .inl ⟨.inl a, fun _ => rfl⟩
    | inr j =>
      rcases ih j with ⟨i, hi⟩ | hi
      · exact .inl ⟨.inr i, fun x => hi x.2⟩
      · exact .inr (fun x => hi x.2)

-- 读法：`(Format.addr (h + 1)).code (lowerHalf h k)` 等于 `bits (word (h + 1)) (extendWord h ((Control.index h).symm k))`。这里调用 `Control.decode`。
private theorem lower_code (h : ℕ) (k : B h) :
    (Format.addr (h + 1)).code (lowerHalf h k) =
      bits (word (h + 1)) (extendWord h ((Control.index h).symm k)) := by
  apply (Control.decode (h + 1)).injective
  rw [show (Format.addr (h + 1)).code = (Control.decode (h + 1)).symm from rfl,
    Equiv.apply_symm_apply, Control.decode, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Fin.ext
  change k.val = Lookup.value _ (extendWord _ _)
  rw [extend_value]
  exact (Lookup.value_bits k.isLt).symm

-- 读法：映射 `(inflate h)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((h + 1)) * (100 + ((h + 1))) ^ (2)` 为上界。按 `a.val < 2 ^ h` 成立与否分情况。
private theorem cheap_inflate (F : Type) [Field F] (h : ℕ) :
    Cheap F (h + 1) (h + 1) (Perm h) (Perm (h + 1)) (inflate h) 2 := by
  let f := (Perm (h + 1)).code ∘ inflate h ∘ (Perm h).code.symm
  have hc : Install.Depends f 1 := by
    rintro ⟨a, b⟩
    have he (x) : f x (a, b) = (Format.addr (h + 1)).code (inflate h ((Perm h).code.symm x) a) b := rfl
    by_cases ha : a.val < 2 ^ h
    · let k : B h := ⟨a.val, ha⟩
      have he' (x) : f x (a, b) =
          bits (word (h + 1)) (extendWord h ((Control.index h).symm (((Perm h).code.symm x) k))) b := by
        rw [he, inflate, dite_eq_left ha, lower_code]
      rcases extend_bits h b with ⟨i, hi⟩ | hi
      · have hh (x) : f x (a, b) = x (k, i) := by
          rw [he', hi]
          exact congrFun ((Perm h).code.apply_symm_apply x) (k, i)
        refine ⟨{(k, i)}, by simp, fun x y hxy => ?_⟩
        rw [hh, hh, hxy _ (Finset.mem_singleton_self _)]
      · exact ⟨∅, by simp, fun _ _ _ => by rw [he', he', hi, hi]⟩
    · exact ⟨∅, by simp, fun _ _ _ => by rw [he, he, inflate, inflate, dite_eq_right ha, dite_eq_right ha]⟩
  refine ⟨_, hc.bnet F, ?_⟩
  change (Perm h).width + (Perm (h + 1)).width + ((Perm h).width + 34 * (Perm (h + 1)).width) ≤ _
  simp only [Perm, Format.width_vec, Format.width_addr]
  rw [Format.width_addr (h + 1)]
  -- 推导：记下中间结论 `hh`：`2 ^ h * h ≤ 2 ^ (h + 1) * (h + 1)`。
  have hh : 2 ^ h * h ≤ 2 ^ (h + 1) * (h + 1) := by gcongr <;> omega
  calc
    _ ≤ 37 * (2 ^ (h + 1) * (h + 1)) := by nlinarith only [hh]
    _ = 2 ^ (h + 1) * (37 * (h + 1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

variable {F : Type} [Field F] {m : ℕ} (T : Routes F m)

-- 读法：`T.embed h (T.base h i)` 等于 `lowerHalf h i`。使用 `Fin.ext` 给出的结论。
theorem Routes.embed_base (h : ℕ) (i : B h) : T.embed h (T.base h i) = lowerHalf h i :=
  Fin.ext (T.initial _ _)

-- 读法：`pack (T.embed h) (π.viaEmbedding (T.base h))` 等于 `inflate h π`。用函数外延性比较等号两侧在 `a` 处的取值。
theorem Routes.pack_eq (h : ℕ) (π : Equiv.Perm (B h)) :
    pack (T.embed h) (π.viaEmbedding (T.base h)) = inflate h π := by
  funext a
  change (π.viaEmbedding (T.base h)).viaEmbedding (T.embed h) a = inflate h π a
  unfold inflate
  split
  · rename_i ha
    let i : B h := ⟨a, ha⟩
    have eq : a = T.embed h (T.base h i) := (Fin.ext (T.initial h i)).symm
    change _ = lowerHalf h (π i)
    rw [eq, Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply, T.embed_base]
  · rename_i ha
    by_cases he : a ∈ Set.range (T.embed h)
    -- 推导：从 `he` 中取出 `b, rfl`。
    · obtain ⟨b, rfl⟩ := he
      have hb : b ∉ Set.range (T.base h) := by
        rintro ⟨i, rfl⟩
        exact ha ((T.initial h i).trans_lt i.isLt)
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hb]
    · exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he

-- 读法：`(T.action h π).smul (Coloring.target F T.embed) i` 等于 `inflate h π i`。
theorem Routes.target_action (h : ℕ) (π : Equiv.Perm (B h)) (i : B (h + 1)) :
    (T.action h π).smul (Coloring.target F T.embed) i = inflate h π i :=
  congrFun (T.pack_eq h π) i

-- 读法：结论为 `∃ c : ℕ, ∀ h : ℕ, 2 ^ t ≤ h + 1 → ∃ v, Cheap F (h + 1) (h + 1) (Perm h) (.vec t (Perm (h + 1))) v c ∧ ∀ π : Equiv.Perm (B h), ∀ i j, v π i j = (T.action h π).smul (f i) j`。
theorem Routes.controllers_net (t : ℕ) (f : B t → controllers F T.embed) :
    ∃ c : ℕ, ∀ h : ℕ, 2 ^ t ≤ h + 1 →
      ∃ v, Cheap F (h + 1) (h + 1) (Perm h) (.vec t (Perm (h + 1))) v c ∧
        ∀ π : Equiv.Perm (B h), ∀ i j, v π i j = (T.action h π).smul (f i) j := by
  have he (i : B t) : Efficient F T.embed (f i).val := (f i).property
  choose c hc using he
  let C := Finset.univ.sup c
  refine ⟨max 2 (C + 2) + 1, fun h ht => ?_⟩
  choose u hu hu' using fun i => hc i h
  have hall (i : B t) : Cheap F (h + 1) (h + 1) (Perm (h + 1)) (Perm (h + 1)) (u i) C :=
    (hu i).mono (Finset.le_sup (Finset.mem_univ i))
  refine ⟨_, (cheap_inflate F h).comp (Cheap.share u hall ht), ?_⟩
  intro π i j
  change u i (inflate h π) j = _
  rw [← T.pack_eq, hu']
  rfl

end OAI.LinearAlgebra.MatrixExponent.Routing
end
