-- 本文件所属证明环节：从谱价格和关联几何构造局部置换与稳定排序协议，分别估计短记录和宽记录的路由成本，把共享价格假设接入压缩构造。
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# 作用于紧凑编码地址的近线性控制器

在标签集以外，输入置换及每个输出置换均按恒等映射延拓。电路可依赖高度和固定地址格式，其成本指数具有统一界。

**英文原文**

Near-linear controllers on packed addresses

An input permutation and each output permutation are extended by
the identity outside the label set. Circuits may depend on the
height and the fixed address format. Their cost exponent is uniform.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open scoped Classical
open Equiv

variable {F J : Type} [Field F] {X : J → Type} {h : J → ℕ} {e : ∀ j, X j ↪ B (h j)}

-- 读法：在后续公式中，`Family` 是 `∀ j, Equiv.Perm (X j) → Equiv.Perm (X j)` 的缩写。
abbrev Family (X : J → Type) := ∀ j, Equiv.Perm (X j) → Equiv.Perm (X j)

-- 读法：在后续公式中，`pack` 是 `⇑(Equiv.Perm.viaEmbeddingHom i g)` 的缩写。
abbrev pack {T : Type} {h : ℕ} (i : T ↪ B h) (g : Equiv.Perm T) : (Perm h).obj :=
  ⇑(Equiv.Perm.viaEmbeddingHom i g)

-- 读法：`Efficient` 表示以下条件：存在 `c : ℕ`，对每个 `j`，存在 `f`，`Cheap F (h j) (h j) (Perm (h j)) (Perm (h j)) f c` 与 `∀ p, f (pack (e j) p) = pack (e j) (g j p)` 同时成立。
def Efficient (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j)) (g : Family X) : Prop :=
  ∃ c : ℕ, ∀ j, ∃ f, Cheap F (h j) (h j) (Perm (h j)) (Perm (h j)) f c ∧
    ∀ p, f (pack (e j) p) = pack (e j) (g j p)

-- 读法：`(Perm h).width` 不超过 `2 ^ h * (100 + h) ^ 1`。
private theorem perm_width (h : ℕ) : (Perm h).width ≤ 2 ^ h * (100 + h) ^ 1 := by
  simp [Perm]

-- 读法：要证明的命题是 `Efficient F e (fun j _ => g j)`。
theorem efficient_fixed (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j))
    (g : ∀ j, Equiv.Perm (X j)) : Efficient F e (fun j _ => g j) :=
  ⟨2, fun j => ⟨_, Cheap.const F (perm_width _) (perm_width _) (pack (e j) (g j)), fun _ => rfl⟩⟩

-- 读法：要证明的命题是 `Efficient F e (fun _ p => p)`。
theorem efficient_target (F : Type) [Field F] (e : ∀ j, X j ↪ B (h j)) :
    Efficient F e (fun _ p => p) :=
  ⟨2, fun _ => ⟨_, Cheap.id F (perm_width _), fun _ => rfl⟩⟩

variable {g g' : Family X}

-- 读法：要证明的命题是 `Efficient F e (g * g')`。
theorem Efficient.mul (hg : Efficient F e g) (hg' : Efficient F e g') : Efficient F e (g * g') := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hg'
  refine ⟨max (max c d + 1) 8 + 1, fun j => ?_⟩
  obtain ⟨u, hu, he⟩ := hc j
  obtain ⟨v, hv, hf⟩ := hd j
  refine ⟨_, (hu.pair hv).comp (Cheap.lookup F (h j) (h j) (.addr (h j)) le_rfl (by simp)), ?_⟩
  intro p
  simp only [Function.comp_apply, he, hf, Pi.mul_apply, pack, map_mul]
  rfl

-- 读法：当 `a ∈ Set.range i` 成立时取 `x a`，否则取 `a`。
private def clean {T : Type} {n : ℕ} (i : T ↪ B n) (x : (Perm n).obj) (a : B n) :=
  if a ∈ Set.range i then x a else a

-- 读法：映射 `(clean i)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (n) * (100 + (n)) ^ (2)` 为上界。
private theorem cheap_clean {T : Type} {n : ℕ} (i : T ↪ B n) :
    Cheap F n n (Perm n) (Perm n) (clean i) 2 := by
  have he (x : (Perm n).pins → Bool) (a : B n) (b : slots (word n)) :
      ((Perm n).code ∘ clean i ∘ (Perm n).code.symm) x (a, b) =
        if a ∈ Set.range i then x (a, b) else (Format.addr n).code a b := by
    change (Format.addr n).code (clean i ((Perm n).code.symm x) a) b = _
    unfold clean
    split
    · exact congrFun ((Perm n).code.apply_symm_apply x) (a, b)
    · rfl
  have hc : Install.Depends ((Perm n).code ∘ clean i ∘ (Perm n).code.symm) 1 := by
    rintro ⟨a, b⟩
    refine ⟨{(a, b)}, by simp, fun x y h => ?_⟩
    rw [he, he, h (a, b) (Finset.mem_singleton_self _)]
  refine ⟨_, hc.bnet F, ?_⟩
  change (Perm n).width + (Perm n).width + ((Perm n).width + 34 * (Perm n).width) ≤ _
  simp only [Perm, Format.width_vec, Format.width_addr]
  calc
    _ = 2 ^ n * (37 * n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

-- 读法：要证明的命题是 `Efficient F e g`。用函数外延性比较等号两侧在 `a` 处的取值。
theorem efficient_of_on
    {c : ℕ} (hh : ∀ j, ∃ f, Cheap F (h j) (h j) (Perm (h j)) (Perm (h j)) f c ∧
      ∀ p a, f (pack (e j) p) (e j a) = e j (g j p a)) : Efficient F e g := by
  refine ⟨max c 2 + 1, fun j => ?_⟩
  obtain ⟨f, hf, he⟩ := hh j
  refine ⟨_, hf.comp (cheap_clean (e j)), fun p => ?_⟩
  funext a
  change clean (e j) _ a = (g j p).viaEmbedding (e j) a
  unfold clean
  split
  · rename_i ha
    obtain ⟨b, rfl⟩ := ha
    rw [Equiv.Perm.viaEmbedding_apply]
    exact he _ _
  · exact (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ‹_›).symm

variable [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]

-- 读法：`Efficient.factor` 的证明用到 `Finite.of_surjective`、`Classical.arbitrary`、`Fintype.ofFinite`。
/-- 对所有有效输入使用同一个输出电路，就能诱导出三个置换族，每个族的额外开销都有一致的多项式上界。

英文原文：A single output circuit for all valid inputs induces three
permutation families, each with a uniform polynomial overhead.
-/
theorem Efficient.factor {C A D : J → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (D j)]
    (s : ∀ j, X j ≃ C j × (A j × D j)) {c : ℕ} (H : Factors F c) (hg : Efficient F e g)
    (hf : ∀ j p x, (s j (g j p x)).1 = (s j x).1) :
    ∃ u v w : Family X, Efficient F e u ∧ Efficient F e v ∧ Efficient F e w ∧ g = u * v * w ∧
      (∀ j p x, (s j (u j p x)).1 = (s j x).1 ∧ (s j (u j p x)).2.1 = (s j x).2.1) ∧
      (∀ j p x, (s j (v j p x)).1 = (s j x).1 ∧ (s j (v j p x)).2.2 = (s j x).2.2) ∧
      (∀ j p x, (s j (w j p x)).1 = (s j x).1 ∧ (s j (w j p x)).2.1 = (s j x).2.1) := by
  have (j : J) : Finite (C j) := Finite.of_surjective (fun x => (s j x).1) (by
    intro a
    exact ⟨(s j).symm (a, (s j (Classical.arbitrary _)).2), by simp⟩)
  let (j : J) : Fintype (C j) := Fintype.ofFinite _
  choose f hc he using fun j => H (h j) _ _ _ _ (s j) (e j)
  -- 推导：从 `hg` 中取出 `d, hd`。
  obtain ⟨d, hd⟩ := hg
  choose f' hc' he' using hd
  have hy (j) (p : Equiv.Perm (X j)) (x : X j) :
      f' j (pack (e j) p) (e j x) = e j (g j p x) := by
    rw [he']
    exact Equiv.Perm.viaEmbedding_apply _ _ _
  choose u v w heq hu hv hw hu' hv' hw' using
    fun j p => he j (g j p) (hf j p) _ (hy j p)
  have hb (j) := (hc' j).comp (hc j)
  refine ⟨u, v, w, ?_, ?_, ?_, funext (fun j => funext (heq j)), hu, hv, hw⟩
  · exact efficient_of_on (fun j => ⟨_, (hb j).fst, hu' j⟩)
  · exact efficient_of_on (fun j => ⟨_, (hb j).snd.fst, hv' j⟩)
  · exact efficient_of_on (fun j => ⟨_, (hb j).snd.snd, hw' j⟩)

end OAI.LinearAlgebra.MatrixExponent.Coloring
