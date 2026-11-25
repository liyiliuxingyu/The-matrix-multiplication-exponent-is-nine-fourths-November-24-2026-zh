-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet

section
/-!
# 在有效输入上同时执行算术运算

同一电路处理指定定义域中的所有配置。寄存器值均按其容量取模解释。只有比较和间接读取对操作数的大小有要求。

**英文原文**

Simultaneous arithmetic on valid inputs

The same circuit handles every setting in the indicated domain.
Registers are interpreted modulo their capacity. Only comparisons and
indirect reads need hypotheses about the sizes of their operands.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector
open Coloring
variable {F S : Type} [Field F] {w : ℕ} {U : Coloring.Format}

-- 读法：在后续公式中，`Array` 是 `S → B w → ℕ` 的缩写。
abbrev Array (S : Type) (w : ℕ) := S → B w → ℕ

-- 读法：`fits` 的取值由 `∀ s i, f s i < 2 ^ w` 给出。
def fits (f : Array S w) := ∀ s i, f s i < 2 ^ w

-- 读法：`packed` 表示以下条件：存在 `g`，`Coloring.Cheap F w w U (Perm w) g c` 与 `∀ s i, g (inp s) i = Fin.ofNat (2 ^ w) (f s i)` 同时成立。
def packed (F : Type) [Field F] (inp : S → U.obj) (f : Array S w) (c : ℕ) : Prop :=
  ∃ g, Coloring.Cheap F w w U (Perm w) g c ∧ ∀ s i, g (inp s) i = Fin.ofNat (2 ^ w) (f s i)

namespace packed

variable {inp : S → U.obj} {f g : Array S w} {m n : ℕ}

-- 读法：要证明的命题是 `packed F inp f n`。
theorem mono (h : packed F inp f m) (le : m ≤ n) : packed F inp f n := by
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, ha.mono le, he⟩

-- 读法：要证明的命题是 `packed F inp (fun _ => f) (m + 2)`。这里调用 `Nat.mul_le_mul_left`。
theorem const (F : Type) [Field F] (inp : S → U.obj) (f : B w → ℕ)
    (hw : U.width ≤ 2 ^ w * (100 + w) ^ m) : packed F inp (fun _ => f) (m + 2) := by
  have h₁ : U.width ≤ 2 ^ w * (100 + w) ^ (m + 1) := hw.trans (by gcongr; omega)
  have h₂ : (Perm w).width ≤ 2 ^ w * (100 + w) ^ (m + 1) := by
    rw [Format.width_vec, Format.width_addr]
    exact Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans (Nat.le_pow (by omega)))
  exact ⟨_, Cheap.const F h₁ h₂ (fun i => Fin.ofNat (2 ^ w) (f i)), fun _ _ => rfl⟩

-- 读法：`U.width` 不超过 `2 ^ w * (100 + w) ^ m`。
theorem width (hf : packed F inp f m) : U.width ≤ 2 ^ w * (100 + w) ^ m := by
  obtain ⟨_, ⟨v, _, hv⟩, _⟩ := hf
  omega

-- 读法：要证明的命题是 `packed F inp (fun s i => f s (Fin.ofNat (2 ^ w) (g s i))) (max m n + 10)`。
theorem lookup (hf : packed F inp f m) (hg : packed F inp g n) :
    packed F inp (fun s i => f s (Fin.ofNat (2 ^ w) (g s i))) (max m n + 10) := by
  obtain ⟨a, ha, he⟩ := hf
  obtain ⟨b, hb, hi⟩ := hg
  have h := (ha.pair hb).comp (Cheap.lookup F w w (.addr w) le_rfl (by simp))
  exact ⟨_, h.mono (by omega), fun s i => by simp only [Function.comp_apply, hi, he]⟩

-- 读法：要证明的命题是 `packed F inp (fun s i => t (f s i)) (m + 12)`。用函数外延性比较等号两侧在 `s i` 处的取值。
/-- 固定的一元表可同时在所有寄存器上求值。

英文原文：A fixed unary table may be evaluated on every register at once.
-/
theorem unary (hf : packed F inp f m) (h : fits f) (t : ℕ → ℕ) :
    packed F inp (fun s i => t (f s i)) (m + 12) := by
  have he := ((const F inp (fun i : B w => t i.val) hf.width).lookup hf).mono
    (n := m + 12) (by omega)
  convert he using 1
  funext s i
  exact congrArg t (Nat.mod_eq_of_lt (h s i)).symm

-- 读法：要证明的命题是 `packed F inp (fun s i => f s i + g s i) (max m n + 7)`。
theorem add (hf : packed F inp f m) (hg : packed F inp g n) :
    packed F inp (fun s i => f s i + g s i) (max m n + 7) := by
  obtain ⟨a, ha, he⟩ := hf
  obtain ⟨b, hb, hi⟩ := hg
  have h : Coloring.Cheap F 0 w (.pair (.addr w) (.addr w)) (.addr w) (fun x => x.1 + x.2) 4 :=
    ⟨_, numeric_add F w, by simp only [Format.width_pair, Format.width_addr]; ring_nf; omega⟩
  refine ⟨_, (((ha.pair hb).zip).comp (Coloring.Cheap.map _ (fun _ => h))).mono (by omega), ?_⟩
  intro s i
  change a (inp s) i + b (inp s) i = _
  rw [he, hi]
  exact Fin.ext (Nat.add_mod _ _ _).symm

-- 读法：要证明的命题是 `packed F inp (fun s i => if f s i < g s i then t s i else u s i) (max (max m n) (max a b) + 12)`。
theorem select {t u : Array S w} {a b : ℕ}
    (hf : packed F inp f m) (hg : packed F inp g n)
    (ht : packed F inp t a) (hu : packed F inp u b) (h : fits f) (k : fits g) :
    packed F inp (fun s i => if f s i < g s i then t s i else u s i)
      (max (max m n) (max a b) + 12) := by
  obtain ⟨x, hx, hx'⟩ := hf
  obtain ⟨y, hy, hy'⟩ := hg
  obtain ⟨z, hz, hz'⟩ := ht
  obtain ⟨v, hv, hv'⟩ := hu
  have cmp : Coloring.Cheap F 0 w (.pair (.addr w) (.addr w)) .bit (fun x => decide (x.1 < x.2)) 3 :=
    ⟨_, numeric_lt F w, by simp only [Format.width_pair, Format.width_addr]; rw [Format.width_bit]; ring_nf; omega⟩
  have bit := ((hx.pair hy).zip).comp (Coloring.Cheap.map _ (fun _ => cmp))
  have step := (((hz.pair hv).zip.pair bit).zip).comp (Coloring.Cheap.map _ (fun _ => cheap_select F w))
  refine ⟨_, step.mono (by omega), ?_⟩
  intro s i
  simp only [Function.comp_apply, hx', hy', hz', hv', decide_eq_true_eq]
  change (if f s i % 2 ^ w < g s i % 2 ^ w then _ else _) = _
  rw [Nat.mod_eq_of_lt (h s i), Nat.mod_eq_of_lt (k s i)]
  split <;> rfl

end packed
end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-!
# 按固定划分将各数据通道路由到两种计算之一

**英文原文**

Routing lanes to one of two computations by a fixed partition
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S I J K : Type} [Field F] {w c : ℕ} {U : Coloring.Format} {inp : S → U.obj}

-- 读法：要证明的命题是 `packed F inp (fun s j => f s (idx j) (arg j)) (c + 14)`。
/-- 两个阶段都可以使用全部通道。索引集为空时无需补入虚设输入。

英文原文：Both stages may use every lane. Empty index sets need no dummy input.
-/
theorem casesOn (hw : 1 ≤ w) (f : S → K → I ⊕ J → ℕ) (idx : B w → K) (arg : B w → I ⊕ J)
    (h₁ : ∀ a : B w → I, packed F inp (fun s j => f s (idx j) (.inl (a j))) c)
    (h₂ : ∀ a : B w → J, packed F inp (fun s j => f s (idx j) (.inr (a j))) c) :
    packed F inp (fun s j => f s (idx j) (arg j)) (c + 14) := by
  classical
  rcases isEmpty_or_nonempty I with he|hi
  · let k := Sum.elim (isEmptyElim : I → J) id
    have h (x : I ⊕ J) : Sum.inr (k x) = x := by cases x; exact isEmptyElim ‹I›; rfl
    simpa only [Function.comp_apply, h] using (h₂ (k ∘ arg)).mono (n := c + 14) (by omega)
  rcases isEmpty_or_nonempty J with he|hj
  · let k := Sum.elim id (isEmptyElim : J → I)
    have h (x : I ⊕ J) : Sum.inl (k x) = x := by cases x; rfl; exact isEmptyElim ‹J›
    simpa only [Function.comp_apply, h] using (h₁ (k ∘ arg)).mono (n := c + 14) (by omega)
  let l := Sum.elim id (fun _ : J => hi.some)
  let r := Sum.elim (fun _ : I => hj.some) id
  let mask := Sum.elim (fun _ : I => 0) (fun _ : J => 1)
  have a := h₁ (l ∘ arg)
  have b := h₂ (r ∘ arg)
  have m := const F inp (mask ∘ arg) a.width
  have n := const F inp (fun _ => 1) a.width
  -- 推导：记下中间结论 `hp`：`1 < 2 ^ w`。
  have hp : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
  have hf := m.select n a b (fun _ j => by cases h : arg j <;> simp [mask, h, hp])
    (fun _ _ => hp)
  convert hf.mono (n := c + 14) (by omega) using 1
  funext s j
  cases h : arg j <;> simp [l, r, mask, h]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# 通过固定的有限查找表间接读取

**英文原文**

Indirect reads through fixed finite lookup tables
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S J : Type} [Field F] {w : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {c d : ℕ}

-- 读法：要证明的命题是 `packed F inp (fun s i => f s i % 2 ^ w) c`。
theorem reduce {f : Array S w} (h : packed F inp f c) :
    packed F inp (fun s i => f s i % 2 ^ w) c := by
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht, fun s i => (he s i).trans (Fin.ext (Nat.mod_mod _ _).symm)⟩

-- 读法：要证明的命题是 `packed F inp (fun s i => f s (keys s i)) (max d c + 10)`。
/-- 为所有可能的请求预先固定一个索引就已足够，无需从输入数据计算逆向查找表。

英文原文：A fixed indexing of the possible requests suffices. It is not
necessary to compute an inverse table from the input data.
-/
theorem fetch [Nonempty J] (keys : S → B w → J) (idx : J ↪ B w) (f : S → J → ℕ)
    (hk : packed F inp (fun s i => (idx (keys s i)).val) c)
    (ht : ∀ key : B w → J, packed F inp (fun s i => f s (key i)) d) :
    packed F inp (fun s i => f s (keys s i)) (max d c + 10) := by
  classical
  let j := Function.invFun idx
  have hh := (ht j).lookup hk
  have he (s : S) (i : B w) : Fin.ofNat (2 ^ w) (idx (keys s i)).val = idx (keys s i) :=
    Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
  have hi (k : J) : j (idx k) = k := Function.leftInverse_invFun idx.injective _
  simpa only [he, hi] using hh

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# 将有名比特上的电路转换为紧凑存储的字数组

**英文原文**

Converting circuits on named bits into packed word arrays
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector
open Install Coloring

-- 读法：在后续公式中，`raw` 是 `⟨I → Bool, I, .refl _⟩` 的缩写。
abbrev raw (I : Type) [Fintype I] : Coloring.Format := ⟨I → Bool, I, .refl _⟩

variable {F S I J : Type} [Field F] [Fintype I] [Fintype J] {w : ℕ}
  {inp : S → I → Bool} {f : Array S w} {m c : ℕ}

-- 读法：要证明的命题是 `packed (U := raw I) F inp f c`。
theorem packed.of_net (k : (I → Bool) → B w × slots (word w) → Bool)
    (hk : BNet F k m) (hc : Fintype.card I + 2 ^ w * w + m ≤ 2 ^ w * (100 + w) ^ c)
    (he : ∀ s j b, k (inp s) (j, b) = digits w (f s j) b) :
    packed (U := raw I) F inp f c := by
  refine ⟨(Perm w).code.symm ∘ k, ⟨m, ?_, ?_⟩, ?_⟩
  · simpa only [Circuit, Function.comp_def, Equiv.apply_symm_apply, raw, Equiv.refl_symm, Equiv.refl_apply] using hk
  · simpa [raw, Perm] using hc
  · intro s i
    change Control.decode w (fun t => k (inp s) (i, t)) = _
    simp only [he, digits, Equiv.apply_symm_apply]

-- 读法：要证明的命题是 `packed (U := raw I) F inp f c`。
theorem packed.reshape (k : (I → Bool) → J × slots (word w) → Bool) (idx : B w → J)
    (hk : BNet F k m) (hc : Fintype.card I + 4 * 2 ^ w * w + Fintype.card J * w + m ≤ 2 ^ w * (100 + w) ^ c)
    (he : ∀ s j b, k (inp s) (idx j, b) = digits w (f s j) b) :
    packed (U := raw I) F inp f c := by
  let e : B w × slots (word w) → J × slots (word w) := Prod.map idx id
  have h := hk.comp ((BNet.id F _).pull e)
  refine packed.of_net _ h ?_ he
  simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
  nlinarith only [hc]

-- 读法：存在 `k : (U.pins → Bool) → (J × slots (word w)) → Bool`，`BNet F k (2 ^ w * (100 + w) ^ c + 3 * Fintype.card J * w)` 与 `∀ s j b, k (U.code (inp s)) (j, b) = digits w (f s (idx j)) b` 同时成立。
theorem packed.unpack {U : Coloring.Format} {inp : S → U.obj}
    (h : packed F inp f c) (idx : J → B w) :
    ∃ k : (U.pins → Bool) → (J × slots (word w)) → Bool,
      BNet F k (2 ^ w * (100 + w) ^ c + 3 * Fintype.card J * w) ∧
      ∀ s j b, k (U.code (inp s)) (j, b) = digits w (f s (idx j)) b := by
  obtain ⟨g, ⟨m, hg, hm⟩, he⟩ := h
  let e : J × slots (word w) → B w × slots (word w) := Prod.map idx id
  have t := BNet.comp hg ((BNet.id F _).pull e)
  refine ⟨_, t.mono ?_, fun s j b => ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word, Perm, Format.width_vec,
      Format.width_addr] at hm ⊢
    nlinarith only [hm]
  · simp only [Function.comp_apply, id_eq, Equiv.symm_apply_apply]
    change (Control.decode w).symm (g (inp s) (idx j)) b = _
    rw [he]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-!
# 小型信道长度方阵的各行之和

**英文原文**

Row sums of small square arrays of channel lengths
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector

open Coloring Install
variable {F S : Type} [Field F] {w R : ℕ} [NeZero R]

-- 读法：在后续公式中，`Pair` 是 `Fin R × Fin R` 的缩写。
abbrev Pair (R : ℕ) := Fin R × Fin R

-- 读法：`index` 的取值由 `Fin.ofNat (2 ^ w) (p.1.val * R + p.2.val)` 给出。
def index (w : ℕ) (p : Pair R) : B w := Fin.ofNat (2 ^ w) (p.1.val * R + p.2.val)

-- 读法：`atPair` 的取值由 `finProdFinEquiv.symm (Fin.ofNat (R * R) i.val)` 给出。
def atPair (R : ℕ) [NeZero R] (i : B w) : Pair R :=
  finProdFinEquiv.symm (Fin.ofNat (R * R) i.val)

-- 读法：`atPair R (index w p)` 等于 `p`。这里调用 `finProdFinEquiv.injective`。
theorem pair_index (hw : R ^ 2 ≤ 2 ^ w) (p : Pair R) : atPair R (index w p) = p := by
  apply finProdFinEquiv.injective
  simp only [atPair, Equiv.apply_symm_apply]
  apply Fin.ext
  have he : p.1.val * R + p.2.val = (finProdFinEquiv p).val := by
    change _ = p.2.val + R * p.1.val
    ring
  change (p.1.val * R + p.2.val) % 2 ^ w % (R * R) = _
  rw [he, Nat.mod_eq_of_lt ((finProdFinEquiv p).isLt.trans_le (by rwa [pow_two] at hw)),
    Nat.mod_eq_of_lt (finProdFinEquiv p).isLt]

-- 读法：输入 `s i` 时返回 `f s (atPair R i).1 (atPair R i).2`。
def matrix (w : ℕ) (f : S → Fin R → Fin R → ℕ) : Array S w :=
  fun s i => f s (atPair R i).1 (atPair R i).2

-- 读法：`matrix w f s (Fin.ofNat (2 ^ w) (u.val * R + v.val))` 等于 `f s u v`。
theorem matrix_index (hw : R ^ 2 ≤ 2 ^ w) (f : S → Fin R → Fin R → ℕ) (s : S) (u v : Fin R) :
    matrix w f s (Fin.ofNat (2 ^ w) (u.val * R + v.val)) = f s u v := by
  change matrix w f s (index w (u, v)) = _
  rw [matrix, pair_index hw]

-- 读法：在后续公式中，`Cell` 是 `Pair R × slots (word w)` 的缩写。
abbrev Cell (R w : ℕ) := Pair R × slots (word w)

-- 读法：`decode` 的取值由 `(Control.decode w (fun k => x (p, k))).val` 给出。
private def decode (x : Cell R w → Bool) (p : Pair R) := (Control.decode w (fun k => x (p, k))).val

omit [NeZero R] in
-- 读法：要证明的命题是 `Register F w (fun x => decode (w := w) x p) (Fintype.card (Cell R w) + 3 * w)`。这里调用 `Control.decode`。
private theorem decoded (F : Type) [Field F] (p : Pair R) :
    Register F w (fun x => decode (w := w) x p) (Fintype.card (Cell R w) + 3 * w) := by
  have hp := (BNet.id F (slots (word w))).pull (fun i => (p, i))
  unfold Register
  have he (x : Cell R w → Bool) : digits w (decode x p) = fun i => x (p, i) := by
    unfold digits decode
    rw [show Fin.ofNat (2 ^ w) (Control.decode w (fun k => x (p, k))).val =
      Control.decode w (fun k => x (p, k)) from Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))]
    exact (Control.decode w).symm_apply_apply _
  simp only [he]
  exact hp.mono (by unfold Cell; rw [card_slots, wd_word]; omega)

-- 读法：`prefixWords` 的取值由 `∑ j : Fin R, if j < p.2 then decode x (p.1, j) else 0` 给出。
def prefixWords (x : Cell R w → Bool) (p : Pair R) :=
  ∑ j : Fin R, if j < p.2 then decode x (p.1, j) else 0

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : Cell R w → Bool) (q : Cell R w) => digits w (prefixWords x q.1) q.2)` 均在 `F` 上有顶点数至多为 `(100000 * R ^ 5 * (w + 1))` 的网络实现。按 `j < p.2` 成立与否分情况。
theorem prefixWords_net :
    BNet F (fun (x : Cell R w → Bool) (q : Cell R w) => digits w (prefixWords x q.1) q.2)
      (100000 * R ^ 5 * (w + 1)) := by
  let T := Fintype.card (Cell R w)
  have hj (p : Pair R) (j : Fin R) :
      Register F w (fun x : Cell R w → Bool => if j < p.2 then decode x (p.1, j) else 0)
        (T + 16 * w) := by
    by_cases h : j < p.2
    · simp only [ite_eq_left h]
      exact (decoded F _).mono (by omega)
    · simp only [ite_eq_right h]
      exact Register.const _
  have hp (p : Pair R) := Register.sum _ (hj p)
  apply (BNet.collect _ hp).mono
  -- 推导：记下中间结论 `ht`：`Fintype.card (Cell R w) = R ^ 2 * w`。
  have ht : Fintype.card (Cell R w) = R ^ 2 * w := by simp [Cell, Pair, pow_two]
  have hr : 1 ≤ R := NeZero.pos R
  have hR : R ^ 2 ≤ R ^ 5 := Nat.pow_le_pow_right hr (by decide)
  have h₁ : 1 ≤ R ^ 2 := Nat.one_le_pow _ _ hr
  have hh : w ≤ R ^ 2 * w := Nat.le_mul_of_pos_left _ h₁
  unfold T
  rw [ht, show Fintype.card (Pair R) = R ^ 2 by simp [Pair, pow_two], Fintype.card_fin]
  calc
    _ ≤ R ^ 5 * w + R ^ 2 * (2 * (R ^ 2 * w) + (2 * R) * (40000 * R ^ 2 * (w + 1))) := by
      gcongr
      · omega
      · nlinarith only [hh, h₁]
    _ ≤ _ := by
      -- 推导：记下中间结论 `h`：`R ^ 4 * w ≤ R ^ 5 * w`。
      have h : R ^ 4 * w ≤ R ^ 5 * w := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hr (by decide))
      nlinarith only [h, Nat.zero_le (R ^ 5 * w), Nat.zero_le (R ^ 5)]

omit [NeZero R] in
-- 读法：`prefixWords x p` 等于 `∑ j ∈ Finset.Iio p.2, g (p.1, j)`。
theorem prefixWords_eq (x : Cell R w → Bool) (g : Pair R → ℕ) (p : Pair R)
    (h : ∀ q k, x (q, k) = digits w (g q) k) (hb : ∀ q, g q < 2 ^ w) :
    prefixWords x p = ∑ j ∈ Finset.Iio p.2, g (p.1, j) := by
  unfold prefixWords decode
  simp only [h, digits, Equiv.apply_symm_apply, Fin.val_ofNat, Nat.mod_eq_of_lt (hb _)]
  rw [← Finset.sum_filter, show Finset.univ.filter (fun j : Fin R => j < p.2) = Finset.Iio p.2 by
    ext; simp]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end

section
/-!
# 将比特载入字通道并同时检验各项断言

**英文原文**

Loading bits into word lanes and checking simultaneous assertions
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Install Coloring
variable {F S I : Type} [Field F] [Fintype I] {w c : ℕ}

-- 读法：`2 * (2 ^ w * (100 + w) ^ c) + 35 * (2 ^ w * w) + 1` 不超过 `2 ^ w * (100 + w) ^ (c + 2)`。
private theorem slack (w c : ℕ) :
    2 * (2 ^ w * (100 + w) ^ c) + 35 * (2 ^ w * w) + 1 ≤ 2 ^ w * (100 + w) ^ (c + 2) := by
  let T := 2 ^ w * (100 + w) ^ c
  have hh : 2 ^ w ≤ T := Nat.le_mul_of_pos_right _ (by positivity)
  have ht : 0 < T := by unfold T; positivity
  rw [pow_add, ← mul_assoc (2 ^ w)]
  calc
    _ ≤ 2 * T + 35 * (T * w) + T := by gcongr; omega
    _ = T * (3 + 35 * w) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by nlinarith)

-- 读法：要证明的命题是 `packed (U := raw I) F inp (fun s i => (inp s (idx i)).toNat) (c + 2)`。
theorem named (F : Type) [Field F] (inp : S → I → Bool) (idx : B w → I)
    (hi : Fintype.card I ≤ 2 ^ w * (100 + w) ^ c) :
    packed (U := raw I) F inp (fun s i => (inp s (idx i)).toNat) (c + 2) := by
  let k (x : I → Bool) (i : B w × slots (word w)) := digits w (x (idx i.1)).toNat i.2
  have hd : Depends k 1 := by
    intro i
    refine ⟨{idx i.1}, by simp, fun x y h => ?_⟩
    unfold k
    rw [h _ (Finset.mem_singleton_self _)]
  refine of_net k (hd.bnet F) ?_ (fun _ _ _ => rfl)
  simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
  rw [show localCost 1 = 34 by decide]
  have := slack w c
  omega

open Classical in
-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun x => fun _ : Unit => decide (x = z))` 均在 `F` 上有顶点数至多为 `(10 * Fintype.card I + 1)` 的网络实现。这里调用 `BNet.of_layout`。
private theorem equal (z : I → Bool) :
    BNet F (fun x => fun _ : Unit => decide (x = z)) (10 * Fintype.card I + 1) := by
  let a := word (Fintype.card I)
  let e : I ≃ slots (word (Fintype.card I)) := Fintype.equivOfCardEq (by simp)
  let r := (bits a).trans (e.symm.arrowCongr (.refl Bool))
  apply BNet.of_layout (a := a) (b := .bit) e (.refl Unit)
  have h := Control.equal_net F a (r.symm z)
  change DNet F a .bit (fun x => decide (r x = z)) _
  simpa only [r.eq_symm_apply, a, wd_word] using h

-- 读法：存在 `b : (I → Bool) → Unit → Bool`，`BNet F b (2 ^ w * (100 + w) ^ (c + 2))` 与 `∀ s, b (inp s) () = decide (∀ i, f s i = 1)` 同时成立。
theorem conjunction {inp : S → I → Bool} {f : Array S w} (hw : 1 ≤ w)
    (h : packed (U := raw I) F inp f c) (hfit : fits f) :
    ∃ b : (I → Bool) → Unit → Bool, BNet F b (2 ^ w * (100 + w) ^ (c + 2)) ∧
      ∀ s, b (inp s) () = decide (∀ i, f s i = 1) := by
  classical
  obtain ⟨k, hk, he⟩ := h.unpack id
  let z (i : B w × slots (word w)) := digits w 1 i.2
  have H := hk.comp (equal (F := F) z)
  refine ⟨_, H.mono ?_, fun s => ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
    rw [mul_assoc 3]
    have := slack w c
    omega
  · simp only [Function.comp_apply, decide_eq_decide]
    -- 推导：记下中间结论 `hm`：`1 < 2 ^ w`。
    have hm : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
    change k (inp s) = z ↔ _
    have hv (i j) : k (inp s) (i, j) = digits w (f s i) j := he s i j
    constructor
    · intro h i
      have hd : digits w (f s i) = digits w 1 := funext fun j =>
        (hv i j).symm.trans (congrFun h (i, j))
      have := congrArg Fin.val ((Control.decode w).symm.injective hd)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt (hfit s i), Nat.mod_eq_of_lt hm] using this
    · intro h
      funext ⟨i, j⟩
      rw [hv, h]

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# 用两个较小的键索引静态表

即使同一记录被多次使用，仍可用工作单元编号和局部记录编号联合查询一张表。两个键的取值范围大小之积必须能装入共享数组。

**英文原文**

Static tables indexed by two smaller keys

A worker number and a local record number can jointly index a table
even when the record is used many times. The product of the two key
ranges must fit in the shared array.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring

variable {F S : Type} [Field F] {w m n : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {f g : Array S w} {c d : ℕ}

-- 读法：要证明的命题是 `packed F inp (fun s i => a (f s i) (g s i)) (max c d + 32)`。这里调用 `Nat.add_lt_add_left`。
theorem binary (a : ℕ → ℕ → ℕ) (hw : m * n ≤ 2 ^ w)
    (hf : packed F inp f c) (hg : packed F inp g d)
    (hm : ∀ s i, f s i < m) (hn : ∀ s i, g s i < n) :
    packed F inp (fun s i => a (f s i) (g s i)) (max c d + 32) := by
  have hw' : fits f := fun s i => (hm s i).trans_le
    ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt (hn s i))).trans hw)
  have he : fits (fun s i => f s i * n + g s i) := by
    intro s i
    exact (Nat.add_lt_add_left (hn s i) _).trans_le
      (by rw [← Nat.succ_mul]; exact (Nat.mul_le_mul_right _ (hm s i)).trans hw)
  have ha := ((hf.unary hw' (·*n)).add hg).unary he (fun x => a (x / n) (x % n))
  convert ha.mono (n := max c d + 32) (by omega) using 1
  funext s i
  have hpos : 0 < n := Nat.zero_lt_of_lt (hn s i)
  rw [mul_comm (f s i), Nat.mul_add_div hpos, Nat.div_eq_of_lt (hn s i), add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (hn s i)]

-- 读法：要证明的命题是 `packed F inp (fun s i => a (x s i) (y s i)) (max c d + 32)`。
theorem named_table {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (a : A → B → ℕ) (ha : Fintype.card A * Fintype.card B ≤ 2 ^ w)
    (x : S → Coloring.B w → A) (y : S → Coloring.B w → B)
    (p : A ≃ Fin (Fintype.card A)) (q : B ≃ Fin (Fintype.card B))
    (hp : packed F inp (fun s i => (p (x s i)).val) c)
    (hq : packed F inp (fun s i => (q (y s i)).val) d) :
    packed F inp (fun s i => a (x s i) (y s i)) (max c d + 32) := by
  let _ : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let _ : NeZero (Fintype.card B) := ⟨Fintype.card_ne_zero⟩
  have h := binary (fun u v => a (p.symm (Fin.ofNat _ u)) (q.symm (Fin.ofNat _ v)))
    ha hp hq (fun _ _ => Fin.isLt _) (fun _ _ => Fin.isLt _)
  have he {m : ℕ} [NeZero m] (i : Fin m) : Fin.ofNat m i.val = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [he, Equiv.symm_apply_apply] using h

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# 变更紧凑并行计算的输入与通道索引

**英文原文**

Changing the input and the lane indexing of a packed computation
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring
variable {F S T I J : Type} [Field F] [Fintype I] [Fintype J] {w c : ℕ}
  {inp : S → I → Bool} {f : Array S w}

-- 读法：要证明的命题是 `packed (U := raw J) F inp' (fun t => f (k t)) (c + 2)`。
theorem lift (h : packed (U := raw I) F inp f c)
    (inp' : T → J → Bool) (k : T → S) (p : I → J) (hi : Fintype.card J ≤ 2 ^ w)
    (he : ∀ t, inp' t ∘ p = inp (k t)) :
    packed (U := raw J) F inp' (fun t => f (k t)) (c + 2) := by
  have hw : (raw J).width ≤ 2 ^ w * (100 + w) ^ c :=
    hi.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hp := Cheap.project F (f := fun (x : (raw J).obj) => (x ∘ p : (raw I).obj))
    hw h.width p (fun _ _ => rfl)
  obtain ⟨a, ha, hf⟩ := h
  refine ⟨_, (hp.comp ha).mono (by omega), ?_⟩
  intro t i
  change a (inp' t ∘ p) i = _
  rw [he]
  exact hf _ _

-- 读法：要证明的命题是 `packed F inp (fun s j => fn (a s j)) (c + 12)`。这里调用 `idx.injective.extend_apply`。
/-- 用任意静态函数给压紧存储的数据域重新编号。

英文原文：Renumber a packed domain by any static function.
-/
theorem remap {D : Type} {U : Coloring.Format} {inp : S → U.obj}
    (a : S → B w → D) (idx : D ↪ B w) (ha : packed F inp (fun s j => (idx (a s j)).val) c)
    (fn : D → ℕ) : packed F inp (fun s j => fn (a s j)) (c + 12) := by
  classical
  let g (k : ℕ) := Function.extend idx fn (fun _ => 0) (Fin.ofNat (2 ^ w) k)
  have h := ha.unary (fun _ _ => Fin.isLt _) g
  have he (s : S) (j : B w) : g (idx (a s j)).val = fn (a s j) := by
    unfold g
    rw [show Fin.ofNat (2 ^ w) (idx (a s j)).val = idx (a s j) from
      Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))]
    exact idx.injective.extend_apply _ _ _
  simpa only [he] using h

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# 从紧凑并行计算中传回有名的布尔结果

**英文原文**

Returning named Boolean results from a packed calculation
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring Install
variable {F S I J : Type} [Field F] [Fintype I] [Fintype J] {w c : ℕ}
  {inp : S → I → Bool}

-- 读法：存在 `(k : slots (word w)) (t : Bool → Bool)`，对每个 `b : Bool`，`t (digits w b.toNat k)` 等于 `b`。
private theorem read_flag (hw : 1 ≤ w) :
    ∃ (k : slots (word w)) (t : Bool → Bool), ∀ b : Bool, t (digits w b.toNat k) = b := by
  have hz : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
  have hn : digits w 0 ≠ digits w 1 := by
    intro he
    have := congrArg Fin.val ((Control.decode w).symm.injective he)
    simp only [Fin.val_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt hz] at this
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  exact ⟨i, fun a => decide (a = digits w 1 i), by rintro (_|_) <;> simp [hi]⟩

-- 读法：存在 `t`，`BNet F t (2 ^ w * (100 + w) ^ (c + 2))` 与 `∀ s, t (inp s) = f s` 同时成立。
/-- 若每条通道的寄存器都表示一个比特，则可预先为所请求的比特任意命名，并用这些名称标识电路输出。

英文原文：If the register in each lane represents a bit, any fixed naming
of the requested bits can be used for the output of the circuit.
-/
theorem output (hw : 1 ≤ w) (hi : Fintype.card I ≤ 2 ^ w) (hj : Fintype.card J ≤ 2 ^ w)
    (f : S → J → Bool)
    (hf : ∀ ix : B w → J, packed (U := raw I) F inp (fun s j => (f s (ix j)).toNat) c) :
    ∃ t, BNet F t (2 ^ w * (100 + w) ^ (c + 2)) ∧ ∀ s, t (inp s) = f s := by
  classical
  have hsize : 2 ^ w * (100 + w) ^ c + 4 * Fintype.card J * w + 34 * Fintype.card J ≤ 2 ^ w * (100 + w) ^ (c + 2) := by
    have hc : 1 ≤ (100 + w) ^ c := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ 2 ^ w * (100 + w) ^ c + 4 * 2 ^ w * w + 34 * 2 ^ w := by gcongr
      _ = 2 ^ w * ((100 + w) ^ c + (4 * w + 34)) := by ring
      _ ≤ 2 ^ w * ((100 + w) ^ c * (1 + (4 * w + 34))) := by
        rw [mul_add ((100 + w) ^ c), mul_one]
        gcongr
        exact Nat.le_mul_of_pos_left _ hc
      _ ≤ _ := by rw [pow_add]; gcongr; nlinarith
  cases isEmpty_or_nonempty J
  -- 推导：记下中间结论 `hd`：`Depends (fun (_ : I → Bool) (_ : J) => false) 0`。
  · have hd : Depends (fun (_ : I → Bool) (_ : J) => false) 0 :=
      fun _ => ⟨∅, by simp, fun _ _ _ => rfl⟩
    refine ⟨_, (hd.bnet F).mono ?_, fun _ => Subsingleton.elim _ _⟩
    simpa only [Fintype.card_eq_zero, mul_zero, add_zero] using
      hi.trans (Nat.le_mul_of_pos_right _ (by positivity : 0 < (100 + w) ^ (c + 2)))
  · obtain ⟨idx⟩ : Nonempty (J ↪ B w) := Function.Embedding.nonempty_of_card_le (by simpa using hj)
    obtain ⟨k, t, he⟩ := read_flag hw
    obtain ⟨g, hg, hg'⟩ := (hf (Function.invFun idx)).unpack idx
    let a (x : J × slots (word w) → Bool) (j : J) := t (x (j, k))
    have ha : Depends a 1 := fun j => ⟨{(j, k)}, by simp, fun x y h => congrArg t (h _ (by simp))⟩
    refine ⟨_, (hg.comp (ha.bnet F)).mono ?_, fun s => funext fun j => ?_⟩
    · rw [Fintype.card_prod, card_slots, wd_word]
      rw [show localCost 1 = 34 by decide]
      exact le_trans (le_of_eq (by ring)) hsize
    · have h := hg' s j k
      rw [Function.leftInverse_invFun idx.injective j] at h
      exact (congrArg t h).trans (he _)

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end
