-- 本文件所属证明环节：为置换网络中配对的边作匹配和均衡着色，并把图论分配步骤编码成可计算的有限地址和置换。
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Control.Address

/-!
# 编码数据上的电路

格式是数据与指定比特上的赋值之间的双射。对仅比线性成本多一个地址宽度多项式因子的计算，核算成本时计入两个边界的长度。

**英文原文**

Circuits on encoded data

A format is a bijection between data and assignments to named bits.
Cost includes the lengths of both boundaries when accounting for
near-linear computation with polynomial overhead in the address width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open Install
-- 读法：在后续公式中，`B` 是 `Fin (2 ^ h)` 的缩写。
abbrev B (h : ℕ) := Fin (2 ^ h)

-- 读法：结构的字段包括 `obj`、`pins`、`code`。
structure Format where
  obj : Type
  pins : Type
  [finite : Fintype pins]
  code : obj ≃ (pins → Bool)

attribute [instance] Format.finite

namespace Format

-- 读法：在后续公式中，`width` 是 `Fintype.card A.pins` 的缩写。
abbrev width (A : Format) := Fintype.card A.pins

-- 读法：在后续公式中，`wire` 是 `⟨Val a, slots a, bits a⟩` 的缩写。
abbrev wire (a : Wire) : Format := ⟨Val a, slots a, bits a⟩

-- 读法：在后续公式中，`bit` 是 `wire .bit` 的缩写。
abbrev bit := wire .bit
-- 读法：在后续公式中，`addr` 是 `⟨B h, slots (word h), (Control.decode h).symm⟩` 的缩写。
abbrev addr (h : ℕ) : Format := ⟨B h, slots (word h), (Control.decode h).symm⟩

-- 读法：在后续公式中，`pair` 是 `⟨A.obj × D.obj, A.pins ⊕ D.pins, (A.code.prodCongr D.code).trans (Equiv.sumPiEquivProdPi (fun _ => Bool)).symm⟩` 的缩写。
abbrev pair (A D : Format) : Format :=
  ⟨A.obj × D.obj, A.pins ⊕ D.pins,
    (A.code.prodCongr D.code).trans (Equiv.sumPiEquivProdPi (fun _ => Bool)).symm⟩

-- 读法：在后续公式中，`vec` 是 `⟨B h → A.obj, B h × A.pins, (Equiv.piCongrRight (fun _ => A.code)).trans (Equiv.curry _ _ _).symm⟩` 的缩写。
abbrev vec (h : ℕ) (A : Format) : Format :=
  ⟨B h → A.obj, B h × A.pins,
    (Equiv.piCongrRight (fun _ => A.code)).trans (Equiv.curry _ _ _).symm⟩

-- 读法：`(pair A D).width` 等于 `A.width + D.width`。使用 `Fintype.card_sum` 给出的结论。
-- 读法：`(addr h).width` 等于 `h`。
-- 读法：`bit.width` 等于 `1`。两端由定义化简为同一项。
@[simp] theorem width_bit : bit.width = 1 := rfl
@[simp] theorem width_addr (h : ℕ) : (addr h).width = h := by simp [width]
@[simp] theorem width_pair (A D : Format) : (pair A D).width = A.width + D.width :=
  Fintype.card_sum
-- 读法：`(vec h A).width` 等于 `2 ^ h * A.width`。
@[simp] theorem width_vec (h : ℕ) (A : Format) : (vec h A).width = 2 ^ h * A.width := by
  simp [width, Fintype.card_prod]

end Format

-- 读法：在后续公式中，`Perm` 是 `Format.vec h (.addr h)` 的缩写。
abbrev Perm (h : ℕ) := Format.vec h (.addr h)

-- 读法：`Circuit` 表示以下条件：对输入、输出的每组相容槽位编号，布尔位映射 `(D.code ∘ f ∘ A.code.symm)` 均在 `F` 上有顶点数至多为 `m` 的网络实现。
def Circuit (F : Type) [Field F] (A D : Format) (f : A.obj → D.obj) (m : ℕ) : Prop :=
  BNet F (D.code ∘ f ∘ A.code.symm) m

-- 读法：`Cheap` 表示以下条件：存在 `m`，`Circuit F A D f m` 与 `A.width + D.width + m ≤ 2 ^ h * (100 + k) ^ c` 同时成立。
def Cheap (F : Type) [Field F] (h k : ℕ) (A D : Format) (f : A.obj → D.obj) (c : ℕ) : Prop :=
  ∃ m, Circuit F A D f m ∧ A.width + D.width + m ≤ 2 ^ h * (100 + k) ^ c

namespace Circuit

variable {F : Type} [Field F] {A D E G : Format} {m n h : ℕ} {f : A.obj → D.obj}

-- 读法：在 `F` 上按格式 `A`、`D` 编码输入输出，映射 `f` 的电路规模至多为 `n`。使用 `BNet.mono` 给出的结论。
theorem mono (hf : Circuit F A D f m) (h : m ≤ n) : Circuit F A D f n :=
  BNet.mono hf h

-- 读法：在 `F` 上按格式 `A`、`E` 编码输入输出，映射 `(g ∘ f)` 的电路规模至多为 `(m + n)`。这里调用 `BNet.comp`。
theorem comp {g : D.obj → E.obj} (hf : Circuit F A D f m) (hg : Circuit F D E g n) :
    Circuit F A E (g ∘ f) (m + n) := by
  simpa only [Circuit, Function.comp_def, Equiv.symm_apply_apply] using BNet.comp hf hg

-- 读法：在 `F` 上按格式 `A`、`(.pair D E)` 编码输入输出，映射 `(fun x => (f x, g x))` 的电路规模至多为 `(5 * A.width + m + n)`。使用 `BNet.pair` 给出的结论。
theorem pair {g : A.obj → E.obj} (hf : Circuit F A D f m) (hg : Circuit F A E g n) :
    Circuit F A (.pair D E) (fun x => (f x, g x)) (5 * A.width + m + n) :=
  BNet.pair hf hg

-- 读法：在 `F` 上按格式 `(.pair A E)`、`(.pair D G)` 编码输入输出，映射 `(Prod.map f g)` 的电路规模至多为 `(m + n)`。使用 `BNet.parallel` 给出的结论。
theorem par {g : E.obj → G.obj} (hf : Circuit F A D f m) (hg : Circuit F E G g n) :
    Circuit F (.pair A E) (.pair D G) (Prod.map f g) (m + n) :=
  BNet.parallel hf hg

-- 读法：在 `F` 上按格式 `(.vec h A)`、`(.vec h D)` 编码输入输出，映射 `(fun x i => f i (x i))` 的电路规模至多为 `(2 ^ h * m)`。使用 `BNet.family` 给出的结论。
theorem map (f : B h → A.obj → D.obj) (hf : ∀ i, Circuit F A D (f i) m) :
    Circuit F (.vec h A) (.vec h D) (fun x i => f i (x i)) (2 ^ h * m) :=
  BNet.family h _ hf

-- 读法：在 `F` 上按格式 `A`、`A` 编码输入输出，映射 `_root_.id` 的电路规模至多为 `A.width`。这里调用 `BNet.id`。
theorem id (F : Type) [Field F] (A : Format) : Circuit F A A _root_.id A.width := by
  simp only [Circuit, Function.comp_def, id_eq, Equiv.apply_symm_apply]
  exact BNet.id F A.pins

-- 读法：在 `F` 上按格式 `A`、`D` 编码输入输出，映射 `f` 的电路规模至多为 `(A.width + 2 * D.width)`。用函数外延性比较等号两侧在 `x` 处的取值。
/-- 结构投影可以任意重复使用各个比特。

英文原文：A structural projection can reuse bits arbitrarily.
-/
theorem project (e : D.pins → A.pins) (he : ∀ x i, D.code (f x) i = A.code x (e i)) :
    Circuit F A D f (A.width + 2 * D.width) := by
  intro a b i j
  unfold Format.width
  rw [Fintype.card_congr i, Fintype.card_congr j, card_slots, card_slots]
  convert Install.project_net F (i ∘ e ∘ j.symm) using 1
  funext x
  apply (bits b).injective
  funext k
  simp only [bits_project, Function.comp_apply, Equiv.apply_symm_apply, he]

-- 读法：在 `F` 上按格式 `A`、`D` 编码输入输出，映射 `f` 的电路规模至多为 `m`。这里调用 `BNet.of_layout`。
theorem of_dnet {a b : Wire} (i : A.pins ≃ slots a) (j : D.pins ≃ slots b)
    {g : Val a → Val b} (hg : DNet F a b g m)
    (he : ∀ x, bits b (g x) ∘ j = D.code (f (A.code.symm (bits a x ∘ i)))) :
    Circuit F A D f m := by
  apply BNet.of_layout i j
  convert hg using 1
  funext x
  apply (bits b).injective
  rw [Equiv.apply_symm_apply]
  funext k
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using (congrFun (he x) (j.symm k)).symm

end Circuit
end OAI.LinearAlgebra.MatrixExponent.Coloring
