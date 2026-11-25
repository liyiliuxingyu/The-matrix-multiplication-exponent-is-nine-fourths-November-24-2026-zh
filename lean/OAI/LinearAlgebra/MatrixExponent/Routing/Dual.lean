-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Routing.PartitionsPlane
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometrySharp
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryControl
import OAI.LinearAlgebra.MatrixExponent.Coloring.Run
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import OAI.LinearAlgebra.MatrixExponent.Routing.SortSpec
import OAI.LinearAlgebra.MatrixExponent.Radix.Budget
import OAI.LinearAlgebra.MatrixExponent.Radix.Short
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Install
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Compatible
import OAI.LinearAlgebra.MatrixExponent.Transport.Scale
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.Install.Close
import OAI.LinearAlgebra.MatrixExponent.Radix.Estimate
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import Mathlib.RingTheory.Algebraic.Cardinality

/-!
# 平面运动的地址长度

对指定的任意地址长度缩减幅度，选取充分多的普通坐标。填充后大小不到原来的两倍。同一平面上的所有运动都保持同一个分划。

**英文原文**

Address length for plane motions

Choose the number of ordinary coordinates sufficiently large for any
prescribed reduction of the address length. Pad by fewer than a factor
of two. All motions on a given plane preserve the same partition.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped Classical

-- 读法：存在 `K : ℕ`，对每个 `h : ℕ`，存在 `r c : ℕ`，`0 < c` 与 `2 ^ h ≤ q ^ ((v + w) * r) * c ∧ q ^ ((v + w) * r) * c < 2 ^ (h + 1) ∧ q ^ ((2 + w) * r) * c ≤ 2 ^ (h / m + K)` 同时成立。
private theorem sizes (q v w m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (hv : m * (2 + w) ≤ v + w) :
    ∃ K : ℕ, ∀ h : ℕ, ∃ r c : ℕ, 0 < c ∧
      2 ^ h ≤ q ^ ((v + w) * r) * c ∧ q ^ ((v + w) * r) * c < 2 ^ (h + 1) ∧
      q ^ ((2 + w) * r) * c ≤ 2 ^ (h / m + K) := by
  let b := q ^ (v + w)
  have hb : 1 < b := one_lt_pow₀ (by omega) (by nlinarith)
  refine ⟨1 + Nat.clog 2 b, fun h => ?_⟩
  let n := 2 ^ h
  have hn : 0 < n := by unfold n; positivity
  let r := Nat.log b n
  let a := b ^ r
  let c := (n - 1) / a + 1
  -- 推导：记下中间结论 `ha`：`0 < a`。
  have ha : 0 < a := by unfold a; positivity
  have heq : q ^ ((v + w) * r) = a := pow_mul _ _ _
  have hlo : a ≤ n := Nat.pow_log_le_self b hn.ne'
  have hhi : n < a * b := by
    rw [show a * b = b ^ (r + 1) by rw [pow_succ]]
    exact Nat.lt_pow_succ_log_self hb n
  have hc : c ≤ b := (Nat.div_lt_iff_lt_mul ha).mpr (by rw [mul_comm]; omega)
  have hc' : n - 1 < a * c := by
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul ha).mp (by unfold c; omega)
  -- 推导：记下中间结论 `hc''`：`a * c ≤ n - 1 + a`。
  have hc'' : a * c ≤ n - 1 + a := by
    unfold c
    rw [mul_add, mul_one, mul_comm a]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hsize : q ^ ((2 + w) * r) ≤ 2 ^ (h / m + 1) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hm.ne').mp
    rw [← pow_mul, ← pow_mul]
    calc
      q ^ ((2 + w) * r * m) = q ^ ((m * (2 + w)) * r) := by ring
      _ ≤ q ^ ((v + w) * r) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right r hv)
      _ ≤ 2 ^ h := heq.le.trans hlo
      _ ≤ 2 ^ ((h / m + 1) * m) := Nat.pow_le_pow_right (by decide)
        ((Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)).le
  refine ⟨r, c, Nat.succ_pos _, ?_, ?_, ?_⟩
  · rw [heq]; change n ≤ _; omega
  · rw [heq, pow_succ]; change _ < n * 2; omega
  · rw [← Nat.add_assoc, pow_add]
    exact Nat.mul_le_mul hsize (hc.trans (Nat.le_pow_clog (by decide) b))

variable {k V W : Type} [Field k] [Fintype k]
  [AddCommGroup V] [Module k V] [Fintype V] [AddCommGroup W] [Module k W] [Fintype W]

-- 读法：`Fintype.card (Labels V I (Aux k W I R) j)` 等于 `(Fintype.card k) ^ ((Module.finrank k V + Module.finrank k W) * Fintype.card (I j)) * Fintype.card (R j)`。
private theorem card_labels (I R : ℕ → Type) [∀ j, Fintype (I j)] [∀ j, Fintype (R j)] (j : ℕ) :
    Fintype.card (Labels V I (Aux k W I R) j) =
      (Fintype.card k) ^ ((Module.finrank k V + Module.finrank k W) * Fintype.card (I j)) *
        Fintype.card (R j) := by
  have : Finite (W →ₗ[k] I j → k) :=
    Finite.of_injective (fun f : W →ₗ[k] I j → k => (f : W → I j → k)) DFunLike.coe_injective
  let : Fintype (W →ₗ[k] I j → k) := Fintype.ofFinite _
  rw [← Nat.card_eq_fintype_card]
  unfold Labels Aux
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fun,
    Module.card_eq_pow_finrank (K := k) (V := V), Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := k) (V := W →ₗ[k] I j → k),
    Module.finrank_linearMap, Module.finrank_pi, Nat.card_eq_fintype_card]
  ring

-- 读法：`address_sizes` 的证明用到 `Fintype.card`、`Fintype.one_lt_card`、`Fintype.card_fin`。
theorem address_sizes (m : ℕ) (hm : 0 < m)
    (hv : m * (2 + Module.finrank k W) ≤ Module.finrank k V + Module.finrank k W) :
    ∃ (I R : ℕ → Type) (_ : ∀ h, Fintype (I h)) (_ : ∀ h, Fintype (R h))
      (_ : ∀ h, Nonempty (R h)) (K : ℕ), ∀ h,
      2 ^ h ≤ Fintype.card (Labels V I (Aux k W I R) h) ∧
      Fintype.card (Labels V I (Aux k W I R) h) < 2 ^ (h + 1) ∧
      ∀ P : VPlane k V, Fintype.card (Labels P.1 I (Aux k W I R) h) ≤ 2 ^ (h / m + K) := by
  obtain ⟨K, hK⟩ := sizes (Fintype.card k) _ _ m Fintype.one_lt_card hm hv
  choose r c hc hl hu hd using hK
  refine ⟨fun h => Fin (r h), fun h => Fin (c h), inferInstance, inferInstance,
    fun h => ⟨⟨0, hc h⟩⟩, K, fun h => ?_⟩
  simp only [card_labels, Fintype.card_fin]
  exact ⟨hl h, hu h, fun P => by rw [P.2]; exact hd h⟩

omit [Fintype k] [Fintype V] in
-- 读法：`∃ (D : Submodule k V) (f : ∀ j, Labels V I R j ≃ (I j → D) × Labels P.1 I R j), ∀ g` 属于 `motion I R P.1, ∀ j x, (f j (g j x)).1 = (f j x).1`。
/-- 第二个因子是沿该平面跳转一步的固定容量。

英文原文：The second factor is the fixed capacity of a hop along this plane.
-/
theorem plane_partition {J : Type} (I R : J → Type) (P : VPlane k V) :
    ∃ (D : Submodule k V) (f : ∀ j, Labels V I R j ≃ (I j → D) × Labels P.1 I R j),
      ∀ g ∈ motion I R P.1, ∀ j x, (f j (g j x)).1 = (f j x).1 := by
  obtain ⟨D, hD⟩ := P.1.exists_isCompl
  let e := (D.prodEquivOfIsCompl P.1 hD.symm).symm
  let f (j : J) : Labels V I R j ≃ (I j → D) × Labels P.1 I R j :=
    { toFun := fun x => (fun i => (e (x.1 i)).1, (fun i => (e (x.1 i)).2), x.2)
      invFun := fun y => (fun i => e.symm (y.1 i, y.2.1 i), y.2.2)
      left_inv := by intro x; simp
      right_inv := by intro y; simp }
  refine ⟨D, f, fun g hg j x => ?_⟩
  funext i
  change (e ((g j x).1 i)).1 = (e (x.1 i)).1
  have hz : (e ((g j x).1 i - x.1 i)).1 = 0 :=
    (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero _ _ hD.symm).mpr (hg j x i)
  simpa only [map_sub, Prod.fst_sub, sub_eq_zero] using hz

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 为所有高度统一选取一套路由布局和检验项

**英文原文**

Choosing a single routing layout and test menu for all heights
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped Classical
open Coloring

variable {F k V W L : Type} [Field F]

-- 读法：`(Routes F m)` 有元素。
private theorem make_routes [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
    [AddCommGroup W] [Module k W] [Fintype W] {c : ℕ} (hf : Factors F c)
    (hmod : HasModels F (flagPoint (K := k) (V := V)) Prod.fst Prod.fst
      (affineGraph (K := k) (V := W))) (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W)
    (m : ℕ) (hm : 0 < m) (hd : m * (2 + Module.finrank k W) ≤ Module.finrank k V + Module.finrank k W) :
    Nonempty (Routes F m) := by
  obtain ⟨I, R, _, _, _, K, hK⟩ := address_sizes m hm hd
  let X := Labels V I (Aux k W I R)
  let x (h : ℕ) := Fintype.equivFin (X h)
  let e (h : ℕ) : X h ↪ B (h + 1) := (x h).toEmbedding.trans (Fin.castLEEmb (hK h).2.1.le)
  let b (h : ℕ) : B h ↪ X h := (Fin.castLEEmb (hK h).1).trans (x h).symm.toEmbedding
  have hi (h : ℕ) (i : B h) : (e h (b h i)).val = i.val := by simp [e, b]
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let M := Coloring.system F e hf
  let G := M.planes I R
  -- 推导：记下中间结论 `gen`：`iSup G = ⊤`。
  have gen : iSup G = ⊤ := M.motion_generate I _ hV
  obtain ⟨params⟩ := Rigid.parameters gen (M.rigid I R hV hW) hmod (Coloring.target F e)⁻¹
  refine ⟨⟨X, fun h => ⟨(hK h).1, (hK h).2.1⟩, e, b, hi, VPlane k V, G, params, K, ?_⟩⟩
  intro g hg h
  obtain ⟨P, hp⟩ := Set.mem_iUnion.mp (params.hop hg)
  obtain ⟨D, f, he⟩ := plane_partition I (Aux k W I R) P
  refine ⟨_, _, inferInstance, inferInstance, f h, (hK h).2.2 P, ?_⟩
  intro σ i
  let t := Function.update (fun j => (1 : Equiv.Perm (X j))) h σ
  have hh := he _ (hp t) h i
  change (f h (g.val h (t h) i)).1 = (f h i).1 at hh
  simpa [t] using hh

-- 读法：`(Routes F m)` 有元素。
/-- 即使特征为二，取七次扩域也可得到至少含 128 个元素的域。在针对仿射对的论证中，为四个独立参数取五次扩域即已足够。

英文原文：Degree seven supplies a field of size at least 128 even in
characteristic two. Degree five suffices for four independent
parameters in the affine pair argument.
-/
theorem routes_of_shared_price [Finite F]
    (hs : Prices.SharedPrice (AlgebraicClosure F))
    (m : ℕ) (hm : 0 < m) : Nonempty (Routes F m) := by
  let p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let k := FiniteField.Extension F p 7
  have : CharP k p := charP_of_injective_algebraMap' F p
  let W := FiniteField.Extension k p 5
  let V := Fin (7 * m) → k
  let L := AlgebraicClosure F
  let : Algebra k L := (IsAlgClosed.lift : k →ₐ[F] L).toRingHom.toAlgebra
  let : Algebra W L := (IsAlgClosed.lift : W →ₐ[k] L).toRingHom.toAlgebra
  let : Fintype k := Fintype.ofFinite k
  let : Fintype W := Fintype.ofFinite W
  -- 推导：记下中间结论 `hq`：`100 ≤ Fintype.card k`。
  have hq : 100 ≤ Fintype.card k := by
    rw [Fintype.card_eq_nat_card, show Nat.card k = Nat.card F ^ 7 from
      FiniteField.natCard_extension F p 7]
    exact le_trans (show 100 ≤ 2 ^ 7 by decide) (Nat.pow_le_pow_left Finite.one_lt_card _)
  have hw : Module.finrank k W = 5 := FiniteField.finrank_extension k p 5
  have hv : Module.finrank k V = 7 * m := by simp [V]
  exact make_routes (V := V) (W := W) (Coloring.factors F) (models_of_shared_price hs hq)
    (by omega) (by omega) m hm (by rw [hv, hw]; omega)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 选择键并检查排序的稳定性

**英文原文**

Selecting keys and checking the stable order
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {F : Type} [Field F] {h w k W m : ℕ}

-- 读法：在 `F` 上，函数 `(key e)` 从 `(word w)` 到 `(word k)` 的图张量可由至多 `w` 个顶点实现。
private theorem key_net (F : Type) [Field F] (e : slots (word k) ↪ slots (word w)) :
    DNet F (word w) (word k) (key e) w := by
  classical
  let R : Set (slots (word w)) := Set.range e
  let _ : Fintype (↥(Rᶜ)) := Fintype.ofFinite _
  let b : Wire := word (Fintype.card ↥(Rᶜ))
  let z : slots b ≃ ↥(Rᶜ) := @Fintype.equivOfCardEq (slots b) ↥(Rᶜ) (slotsFintype b) _
    (by rw [card_slots]; exact wd_word _)
  let r : slots (.pair (word k) b) ≃ slots (word w) :=
    ((Equiv.ofInjective e e.injective).sumCongr z).trans (Equiv.Set.sumCompl R)
  -- 推导：记下中间结论 `hw`：`wd (.pair (word k) b) = w`。
  have hw : wd (.pair (word k) b) = w := by
    exact (card_slots _).symm.trans ((@Fintype.card_congr _ _ (slotsFintype _) (slotsFintype _) r).trans
      ((card_slots _).trans (wd_word _)))
  have he : (fun x : Val (word w) => (reindex r x).1) = key e := by
    funext x
    apply (bits (word k)).injective
    funext i
    rw [key, Equiv.apply_symm_apply]
    exact bits_reindex r x (.inl i)
  rw [← he]
  exact ((DNet.fst F (word k) b).pre (rewire_reindex r)).mono hw.le

-- 读法：`ys` 等于 `zs`。对 `ys` 作归纳，并把 `zs` 保持为任意参数。
private theorem stable_unique {α : Type} {d : α → Val (word k)} {xs ys zs : List α}
    (hy : Radix.Stable d xs ys) (hz : Radix.Stable d xs zs) : ys = zs := by
  have h := hy.1.trans hz.1.symm
  have h₁ := hy.2.1
  have h₂ := hz.2.1
  have h₃ i := (hy.2.2 i).trans (hz.2.2 i).symm
  clear hy hz xs
  induction ys generalizing zs with
  | nil => exact h.symm.eq_nil.symm
  | cons y ys ih =>
    cases zs with
    | nil => simp at h
    | cons z zs =>
      -- 推导：记下中间结论 `min₁`：`d y ≤ d z`。
      have min₁ : d y ≤ d z := by
        rcases List.mem_cons.mp (h.mem_iff.mpr (List.mem_cons_self ..)) with eq | mem
        · exact eq ▸ le_rfl
        · exact (List.pairwise_cons.mp h₁).1 _ mem
      have min₂ : d z ≤ d y := by
        rcases List.mem_cons.mp (h.mem_iff.mp (List.mem_cons_self ..)) with eq | mem
        · exact eq ▸ le_rfl
        · exact (List.pairwise_cons.mp h₂).1 _ mem
      have eq := le_antisymm min₁ min₂
      have same : y = z := by
        have ht := h₃ (d z)
        simp [eq] at ht
        exact ht.1
      subst z
      congr 1
      apply ih h.cons_inv (List.pairwise_cons.mp h₁).2 (List.pairwise_cons.mp h₂).2
      intro i
      have he := h₃ i
      by_cases hj : d y = i <;> simpa [hj] using he

-- 读法：要证明的命题是 `SortingBound F h w ((4 * m + 3000000 * 2 ^ h * W : ℕ) : ℝ)`。这里调用 `hnet.pre`。
/-- 足够宽的带标签置换网络可实现这两种检验，并能支付暴露其各自独立参数的成本。

英文原文：A sufficiently wide tagged-permutation network supplies both
checks, including the cost of exposing their independent arguments.
-/
theorem sorting_bound (ht : Radix.Tag F h W m) (hu : 1 + h + 2 * w ≤ W) :
    SortingBound F h w ((4 * m + 3000000 * 2 ^ h * W : ℕ) : ℝ) := by
  constructor
  · obtain ⟨v, hv, hnet⟩ := Tagged.tag_shrink (b := word w) (Tagged.Batch.of_net ht 1)
      (by simp only [wd_word]; omega)
    refine ⟨v, ?_, ?_⟩
    · simpa only [power, mul_one] using (hnet.pre (.unit' _)).post (.unit' _)
    · simp only [wd_word, one_mul] at hv
      apply Nat.cast_le.mpr
      have hb : 2 ^ h * (h + 2 * w) ≤ 2 ^ h * W := Nat.mul_le_mul_left _ (by omega)
      -- 推导：记下中间结论 `hc`：`2 ^ h * (h + 2 * W) ≤ 2 ^ h * (3 * W)`。
      have hc : 2 ^ h * (h + 2 * W) ≤ 2 ^ h * (3 * W) := Nat.mul_le_mul_left _ (by omega)
      linarith [Nat.zero_le (2 ^ h * W)]
  · intro k e
    have hw : k ≤ w := by simpa using Fintype.card_le_of_injective _ e.injective
    obtain ⟨f, ⟨v, hv, hnet⟩, hs⟩ := Radix.stable_net (key_net F e) (by simp only [wd_word]; omega) ht
    have he (x y : Val (tree h (word w))) :
        Radix.Stable (key e) (flatten h x) (flatten h y) ↔ f x = y :=
      ⟨fun hy => Tagged.flatten_inj h (stable_unique (hs x) hy), fun h => h ▸ hs x⟩
    refine ⟨v, ?_, ?_⟩
    · unfold stableTensor
      simp only [he]
      exact hnet
    · apply Nat.cast_le.mpr
      -- 推导：记下中间结论 `hh`：`2 ^ h * w ≤ 2 ^ h * W`。
      have hh : 2 ^ h * w ≤ 2 ^ h * W := Nat.mul_le_mul_left _ (by omega)
      linarith [Nat.zero_le (2 ^ h * W)]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 利用共享价格实现带标签置换和批量查表

对每个高度比，价格检验给出一个固定的跳转选项表。控制器可处理任意输入置换，库存上界对高度比一致。安装并递归实现较短的调用，得到宽记录上界；逐位基数排序给出对数宽度的估计。

**英文原文**

Tagged permutations and batched lookup from shared prices

For each height ratio the price tests give a fixed hop menu. The
controller handles an arbitrary input permutation; the inventory
bound is uniform in the ratio. Installing and recursively realizing
the shorter calls gives the wide-record bound. Radix passes supply
the logarithmic-width estimate.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {F : Type} [Field F] [Finite F]

-- 读法：要证明的命题是 `Radix.WideTag F`。这里调用 `Radix.wide_of_protocol`。
theorem wide_of_shared_price (hs : Prices.SharedPrice (AlgebraicClosure F)) : Radix.WideTag F := by
  apply Radix.wide_of_protocol
  apply Install.protocol_of_open
  apply Install.open_of_groups
  apply Transport.groups_of_local
  apply local_of_routes
  intro m hm
  obtain ⟨t⟩ := routes_of_shared_price (F := F) hs m hm
  obtain ⟨r⟩ := t.params.rig
  exact ⟨t, r, Rig.compatible t r⟩

-- 读法：存在 `p : ℝ`，`1 < p` 与 `p < 2 ∧ Lookup.Sorting F p` 同时成立。
theorem sorting_of_shared_price (hs : Prices.SharedPrice (AlgebraicClosure F)) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ Lookup.Sorting F p := by
  obtain ⟨p, hl, hu, h⟩ := Radix.short_of_wide (wide_of_shared_price hs)
  exact ⟨p, hl, hu, Lookup.sorting_of_tag hl.le h⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# 对偶指数的严格节省给出排序和局部集中

对偶指数在扩域时保持不变。因此同步论证可以在可数代数闭包中进行，而路由与集中的全部估计仍在原域上成立。

**英文原文**

A strict dual saving supplies sorting and local concentration

The dual exponent is unchanged on field extension. This allows the
synchronization argument to use the countable algebraic closure while
all routing and concentration estimates remain over the original field.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：`dual K a b` 等于 `dual F a b`。按 `c ∈ Set.Icc 0 (min a b)` 成立与否分情况。
theorem Rectangle.dual_extension (F K : Type*) [Field F] [Field K] [Algebra F K]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : dual K a b = dual F a b := by
  unfold dual
  apply congrArg sSup
  ext c
  simp only [Set.mem_ofPred_eq]
  by_cases hc : c ∈ Set.Icc 0 (min a b)
  · rw [exponent_extension F K ha hb hc.1]
  · simp only [hc, false_and]

variable {F : Type} [Field F] [Finite F]

-- 读法：要证明的命题是 `Prices.SharedPrice (AlgebraicClosure F)`。这里调用 `h.ne'`。
theorem shared_of_dual (h : 1 / 2 < Rectangle.dual F 1 1) :
    Prices.SharedPrice (AlgebraicClosure F) := by
  by_contra bad
  obtain ⟨hs, hr⟩ := contact_of_not_shared bad
  exact h.ne' (Rectangle.dual_square hr hs)

-- 读法：要证明的命题是 `Radix.WideTag F`。使用 `Routing.wide_of_shared_price` 给出的结论。
theorem wide_of_dual (h : 1 / 2 < Rectangle.dual F 1 1) : Radix.WideTag F :=
  Routing.wide_of_shared_price (shared_of_dual h)

-- 读法：要证明的命题是 `Rounds.LocalLaw F ℓ`。使用 `Rounds.local_law` 给出的结论。
theorem local_of_dual (h : 1 / 2 < Rectangle.dual F 1 1) (ℓ : ℕ) : Rounds.LocalLaw F ℓ :=
  Rounds.local_law (shared_of_dual h) ℓ

-- 读法：要证明的命题是 `Rounds.LocalLaw F ℓ`。使用 `Rounds.local_law` 给出的结论。
theorem local_of_saving (h : omega F < 9 / 4) (ℓ : ℕ) : Rounds.LocalLaw F ℓ :=
  Rounds.local_law (shared_of_saving h) ℓ

end OAI.LinearAlgebra.MatrixExponent
end
