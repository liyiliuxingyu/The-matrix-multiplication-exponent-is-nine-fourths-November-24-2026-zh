-- 本文件所属证明环节：用二元地址的自相关及碰撞得分评价混排选择，为重置中选择合适的块排列提供计量工具。
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import OAI.LinearAlgebra.MatrixExponent.Packing.BadBases
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad

section
/-!
# 二进制自相关

未归一化的沃尔什变换重复作用时，每层都会引入因子二。它将二进制地址上的卷积对角化。这些恒等式只使用交换环的运算，在特征为二时也成立。

**英文原文**

Binary autocorrelations

The unnormalized Walsh transform doubles at each level under iteration.
It diagonalizes convolution on binary addresses. The identities only
use commutative ring operations, including in characteristic two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Mixer
open Packing Finset

variable {K : Type} [CommRing K] {h : ℕ}

-- 读法：`slice` 的取值由 `f (Fin.cons i x)` 给出。
def slice (i : ZMod 2) (f : Cell (h + 1) → K) (x : Cell h) := f (Fin.cons i x)

omit [CommRing K] in
-- 读法：`f` 等于 `g`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem slice_ext {f g : Cell (h + 1) → K} (h₀ : slice 0 f = slice 0 g)
    (h₁ : slice 1 f = slice 1 g) : f = g := by
  funext x
  rw [← Fin.cons_self_tail x]
  have bit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases bit (x 0) with h | h
  · rw [h]; exact congrFun h₀ _
  · rw [h]; exact congrFun h₁ _

-- 读法：`slice i (f + g)` 等于 `slice i f + slice i g`。两端由定义化简为同一项。
@[simp] theorem slice_add (i) (f g : Cell (h + 1) → K) :
    slice i (f + g) = slice i f + slice i g := rfl

-- 读法：`slice i (f - g)` 等于 `slice i f - slice i g`。两端由定义化简为同一项。
@[simp] theorem slice_sub (i) (f g : Cell (h + 1) → K) :
    slice i (f - g) = slice i f - slice i g := rfl

-- 读法：`slice i (f * g)` 等于 `slice i f * slice i g`。两端由定义化简为同一项。
@[simp] theorem slice_mul (i) (f g : Cell (h + 1) → K) :
    slice i (f * g) = slice i f * slice i g := rfl

omit [CommRing K] in
-- 读法：`slice (h := h) i (fun _ => z)` 等于 `fun _ => z`。两端由定义化简为同一项。
@[simp] theorem slice_const (i) (z : K) :
    slice (h := h) i (fun _ => z) = fun _ => z := rfl

-- 读法：逐一匹配以下输入模式：`0, f, x`、`_ + 1, f, x`。
def walsh : {h : ℕ} → (Cell h → K) → Cell h → K
  | 0, f, x => f x
  | _ + 1, f, x =>
    let a := walsh (slice 0 f) (Fin.tail x)
    let b := walsh (slice 1 f) (Fin.tail x)
    if x 0 = 0 then a + b else a - b

-- 读法：`slice 0 (walsh f)` 等于 `walsh (slice 0 f) + walsh (slice 1 f)`。用函数外延性比较等号两侧在 `x` 处的取值。
@[simp] theorem slice₀ (f : Cell (h + 1) → K) :
    slice 0 (walsh f) = walsh (slice 0 f) + walsh (slice 1 f) := by
  funext x
  simp [slice, walsh]

-- 读法：`slice 1 (walsh f)` 等于 `walsh (slice 0 f) - walsh (slice 1 f)`。用函数外延性比较等号两侧在 `x` 处的取值。
@[simp] theorem slice₁ (f : Cell (h + 1) → K) :
    slice 1 (walsh f) = walsh (slice 0 f) - walsh (slice 1 f) := by
  funext x
  simp [slice, walsh]

-- 读法：`walsh (f + g)` 等于 `walsh f + walsh g`。对 `h` 作归纳。
@[simp] theorem walsh_add (f g : Cell h → K) : walsh (f + g) = walsh f + walsh g := by
  induction h with
  | zero => rfl
  | succ h ih =>
    apply slice_ext <;> simp only [slice₀, slice₁, slice_add, ih] <;>
      funext x <;> simp only [Pi.add_apply, Pi.sub_apply] <;> ring

-- 读法：`walsh (f - g)` 等于 `walsh f - walsh g`。对 `h` 作归纳。
@[simp] theorem walsh_sub (f g : Cell h → K) : walsh (f - g) = walsh f - walsh g := by
  induction h with
  | zero => rfl
  | succ h ih =>
    apply slice_ext <;> simp only [slice₀, slice₁, slice_sub, ih] <;>
      funext x <;> simp only [Pi.add_apply, Pi.sub_apply] <;> ring

-- 读法：`walsh (walsh f)` 等于 `(fun _ => (2 : K) ^ h) * f`。对 `h` 作归纳。
theorem twice (f : Cell h → K) : walsh (walsh f) = (fun _ => (2 : K) ^ h) * f := by
  induction h with
  | zero => funext x; simp [walsh]
  | succ h ih =>
    apply slice_ext <;>
      simp only [slice₀, slice₁, slice_mul, slice_const, walsh_add, walsh_sub, ih] <;>
      funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, pow_succ] <;> ring

-- 读法：`conv` 的取值由 `∑ x, f x * g (x + z)` 给出。
def conv (f g : Cell h → K) (z : Cell h) := ∑ x, f x * g (x + z)

-- 读法：`(Fin.cons i x : Cell (h + 1)) + Fin.cons j y` 等于 `Fin.cons (i + j) (x + y)`。用函数外延性比较等号两侧在 `r` 处的取值。
private theorem cons_add (i j : ZMod 2) (x y : Cell h) :
    (Fin.cons i x : Cell (h + 1)) + Fin.cons j y = Fin.cons (i + j) (x + y) := by
  funext r
  induction r using Fin.cases <;> simp

-- 读法：`slice i (conv f g)` 等于 `conv (slice 0 f) (slice i g) + conv (slice 1 f) (slice (1 + i) g)`。用函数外延性比较等号两侧在 `z` 处的取值。
theorem split_conv (f g : Cell (h + 1) → K) (i : ZMod 2) :
    slice i (conv f g) = conv (slice 0 f) (slice i g) + conv (slice 1 f) (slice (1 + i) g) := by
  funext z
  let e : ZMod 2 × Cell h ≃ Cell (h + 1) := Fin.consEquiv (fun _ => ZMod 2)
  change (∑ x : Cell (h + 1), f x * g (x + Fin.cons i z)) = _
  rw [← e.sum_comp, Fintype.sum_prod_type]
  change (∑ j : ZMod 2, ∑ x : Cell h, f (Fin.cons j x) * g (Fin.cons j x + Fin.cons i z)) = _
  rw [show (univ : Finset (ZMod 2)) = {0, 1} by decide, sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  simp only [cons_add, zero_add, Pi.add_apply, conv, slice]

-- 读法：`walsh (conv f g)` 等于 `walsh f * walsh g`。对 `h` 作归纳。
theorem walsh_conv (f g : Cell h → K) : walsh (conv f g) = walsh f * walsh g := by
  induction h with
  | zero =>
    funext x
    unfold walsh conv
    rw [Fintype.sum_eq_single x (fun y hy => (hy (Subsingleton.elim _ _)).elim)]
    rw [show x + x = x from Subsingleton.elim _ _]
    rfl
  | succ h ih =>
    apply slice_ext <;> simp only [slice₀, slice₁, slice_mul, split_conv, add_zero,
      show (1 : ZMod 2) + 1 = 0 by decide, walsh_add, ih] <;>
      funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] <;> ring

-- 读法：`walsh (walsh f * walsh f)` 等于 `(fun _ => (2 : K) ^ h) * conv f f`。
/-- 实施两次蝶形变换并逐项平方，算得自相关乘以块数。

英文原文：Two butterfly transforms and entrywise squaring compute the
autocorrelation times the number of blocks.
-/
theorem autocorrelation (f : Cell h → K) :
    walsh (walsh f * walsh f) = (fun _ => (2 : K) ^ h) * conv f f := by
  rw [← walsh_conv, twice]

end OAI.LinearAlgebra.MatrixExponent.Mixer
end

/-!
# 按深度与二进制差汇总重置得分

只有非中心二阶矩依赖于混合器。因此，一张以深度与块差为索引的数组就足以比较所有线性混合器。各个位置与接触的数组由各自的自相关构成。

**英文原文**

Aggregating the reset score by depth and binary difference

Only the uncentered second moments depend on the mixer. Consequently
one array, indexed by depth and by block difference, suffices to
compare all linear mixers. The arrays of the individual positions
and contacts are formed from their autocorrelations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Mixer
open Packing Finset
open scoped Classical

-- 读法：在后续公式中，`Perm` 是 `Cell h ≃ₗ[ZMod 2] Cell h` 的缩写。
abbrev Perm (h : ℕ) := Cell h ≃ₗ[ZMod 2] Cell h
-- 读法：在后续公式中，`Coeff` 是 `Fin (h + 1) → Cell h → ℝ` 的缩写。
abbrev Coeff (h : ℕ) := Fin (h + 1) → Cell h → ℝ

variable {h : ℕ} (p : Perm h)

-- 读法：用字段 `toFun`、`map_add'`、`map_smul'` 构造 `Coeff h →ₗ[ℝ] ℝ`。
def eval : Coeff h →ₗ[ℝ] ℝ where
  toFun f := ∑ i : Fin (h + 1), ∑ z, if ancestor i.is_le (p z) = 0 then f i z else 0
  map_add' f g := by
    simp only [Pi.add_apply, ← sum_add_distrib, ite_add_ite, add_zero]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum, mul_ite, mul_zero, RingHom.id_apply]

-- 读法：当 `j.val = i` 成立时取 `conv l l z`，否则取 `0`。
def atDepth (l : Cell h → ℝ) (i : ℕ) : Coeff h :=
  fun j z => if j.val = i then conv l l z else 0

-- 读法：`(∑ z, (load l p.toEquiv i z) ^ 2)` 等于 `∑ z, if ancestor hi (p z) = 0 then conv l l z else 0`。这里调用 `sum_congr`。
private theorem moment (l : Cell h → ℝ) {i : ℕ} (hi : i ≤ h) :
    (∑ z, (load l p.toEquiv i z) ^ 2) =
      ∑ z, if ancestor hi (p z) = 0 then conv l l z else 0 := by
  rw [square_load _ _ _ hi]
  have he (z : Cell h) : (if ancestor hi (p z) = 0 then conv l l z else 0) =
      ∑ x, if ancestor hi (p z) = 0 then l x * l (x + z) else 0 := by
    split_ifs <;> simp [conv]
  simp_rw [he]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (Equiv.addLeft x)]
  apply sum_congr rfl
  intro z _
  change (if ancestor hi (p x) = ancestor hi (p (x + z)) then l x * l (x + z) else 0) = _
  rw [map_add, show ancestor hi (p x + p z) = ancestor hi (p x) + ancestor hi (p z) from rfl]
  simp

-- 读法：`eval p (atDepth l i)` 等于 `∑ z, (load l p.toEquiv i z) ^ 2`。按 `i ≤ h` 成立与否分情况。
theorem eval_atDepth (l : Cell h → ℝ) (i : ℕ) :
    eval p (atDepth l i) = ∑ z, (load l p.toEquiv i z) ^ 2 := by
  change (∑ j : Fin (h + 1), ∑ z, if ancestor j.is_le (p z) = 0 then atDepth l i j z else 0) = _
  by_cases hi : i ≤ h
  · rw [Fintype.sum_eq_single (⟨i, by omega⟩ : Fin (h + 1))]
    · simpa only [atDepth, ite_true] using (moment p l hi).symm
    · intro j hj
      have : j.val ≠ i := fun he => hj (Fin.ext he)
      simp [atDepth, this]
  · have hn (j : Fin (h + 1)) : j.val ≠ i := by have := j.isLt; omega
    simp [atDepth, hn, load, hi]

-- 读法：`estimate l p.toEquiv k b j - estimate l q.toEquiv k b j` 等于 `2 * (eval p - eval q) (atDepth l (b + j))`。
private theorem estimate_diff (q : Perm h) (l : Cell h → ℝ) (k b j : ℕ) :
    estimate l p.toEquiv k b j - estimate l q.toEquiv k b j =
      2 * (eval p - eval q) (atDepth l (b + j)) := by
  rw [LinearMap.sub_apply, eval_atDepth, eval_atDepth]
  unfold estimate
  split_ifs with hi hk
  · rw [variance_eq _ _ _ hi, variance_eq _ _ _ hi]
    ring
  · rw [sum_cross _ _ _ hi, sum_cross _ _ _ hi]
    ring
  · simp [load, hi]

variable {V A : Type} [Fintype V] [Fintype A]
  (base : V → ℕ) (depth : A → ℕ) (l : V → Cell h → ℝ) (y : A → Cell h → ℝ) (g : ℝ)

-- 读法：`coefficients` 的结果类型为 `Coeff h`。
def coefficients : Coeff h :=
  3 • (∑ v, ∑ j ∈ range (h + 1), (2 * resetWeight j) • atDepth (l v) (base v + j)) +
    4 • ∑ c, g ^ 2 • atDepth (y c) (depth c)

-- 读法：`score base depth l y g p.toEquiv k - score base depth l y g q.toEquiv k` 等于 `(eval p - eval q) (coefficients base depth l y g)`。
/-- 成本之差的符号恰等于两个检验量在汇总数组上取值之差的符号。

英文原文：The sign of the cost difference is exactly the sign of the difference
of the two tests on the aggregated array.
-/
theorem score_diff (q : Perm h) (hd : ∀ c, depth c ≤ h) (k : ℕ) :
    score base depth l y g p.toEquiv k - score base depth l y g q.toEquiv k =
      (eval p - eval q) (coefficients base depth l y g) := by
  let f := eval p - eval q
  have h₁ (v : V) : f (∑ j ∈ range (h + 1), (2 * resetWeight j) • atDepth (l v) (base v + j)) =
      (∑ j ∈ range (h + 1), resetWeight j * estimate (l v) p.toEquiv k (base v) j) -
      (∑ j ∈ range (h + 1), resetWeight j * estimate (l v) q.toEquiv k (base v) j) := by
    rw [map_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, ← mul_sub, estimate_diff]
    unfold f
    ring
  have h₂ c : f (g ^ 2 • atDepth (y c) (depth c)) =
      g ^ 2 * variance (y c) p.toEquiv (depth c) - g ^ 2 * variance (y c) q.toEquiv (depth c) := by
    unfold f
    rw [map_smul, smul_eq_mul, LinearMap.sub_apply, eval_atDepth, eval_atDepth,
      variance_eq _ _ _ (hd c), variance_eq _ _ _ (hd c)]
    ring
  change _ = f _
  rw [coefficients, map_add, map_nsmul, map_nsmul, map_sum, map_sum]
  simp only [h₁, h₂, sum_sub_distrib, score, nsmul_eq_mul, Nat.cast_ofNat]
  ring

end OAI.LinearAlgebra.MatrixExponent.Mixer
end

/-!
# 具有固定字典的蝶形电路

所有算术运算都使用编码后的字。一张表同时计算蝶形运算的两个输出，另一张表求一个字的平方。两张表的张量条目均为网络基域中的零或一。

**英文原文**

Butterfly circuits with a fixed dictionary

All arithmetic uses encoded words. One table computes the two butterfly
outputs together. A second table squares a word. The tensor entries of
both tables are zero or one in the network's ground field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Mixer

open Packing
open scoped Classical

variable {a : Wire}

-- 读法：逐一匹配以下输入模式：`0, x, _`、`h + 1, x, j`。
def read : (h : ℕ) → Val (tree h a) → Cell h → Val a
  | 0, x, _ => x
  | h + 1, x, j => if j 0 = 0 then read h x.1 (Fin.tail j) else read h x.2 (Fin.tail j)

-- 读法：逐一匹配以下输入模式：`0, x`、`h + 1, x`。
private def rows (s : Val a → Val a) : (h : ℕ) → Val (tree h a) → Val (tree h a)
  | 0, x => s x
  | h + 1, x => (rows s h x.1, rows s h x.2)

-- 读法：逐一匹配以下输入模式：`0, x`、`h + 1, x`。
private def both (g : Val (.pair a a) → Val (.pair a a)) :
    (h : ℕ) → Val (tree (h + 1) a) → Val (tree (h + 1) a)
  | 0, x => g x
  | h + 1, x =>
    let u := both g h (x.1.1, x.2.1)
    let v := both g h (x.1.2, x.2.2)
    ((u.1, v.1), (u.2, v.2))

-- 读法：`read h (rows s h x) j` 等于 `s (read h x j)`。对 `h` 作归纳。
private theorem read_rows (s : Val a → Val a) (h : ℕ) (x : Val (tree h a)) (j : Cell h) :
    read h (rows s h x) j = s (read h x j) := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [read, rows]; split_ifs <;> exact ih _ _

-- 读法：`(read h (both g h x).1 j, read h (both g h x).2 j)` 等于 `g (read h x.1 j, read h x.2 j)`。对 `h` 作归纳。
private theorem read_both (g : Val (.pair a a) → Val (.pair a a)) (h : ℕ)
    (x : Val (tree (h + 1) a)) (j : Cell h) :
    (read h (both g h x).1 j, read h (both g h x).2 j) = g (read h x.1 j, read h x.2 j) := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [read, both]; split_ifs <;> exact ih _ _

variable {K F : Type} [CommRing K] [Field F] (e : Val a ≃ K)

-- 读法：`step` 的取值由 `(e.symm (e p.1 + e p.2), e.symm (e p.1 - e p.2))` 给出。
def step (p : Val (.pair a a)) : Val (.pair a a) :=
  (e.symm (e p.1 + e p.2), e.symm (e p.1 - e p.2))

-- 读法：`square` 的取值由 `e.symm (e x * e x)` 给出。
def square (x : Val a) : Val a := e.symm (e x * e x)

-- 读法：逐一匹配以下输入模式：`0, x`、`h + 1, x`。
def butterfly : (h : ℕ) → Val (tree h a) → Val (tree h a)
  | 0, x => x
  | h + 1, x => both (step e) h (butterfly h x.1, butterfly h x.2)

-- 读法：`correlation` 的取值由 `butterfly e h (rows (square e) h (butterfly e h x))` 给出。
def correlation (h : ℕ) (x : Val (tree h a)) :=
  butterfly e h (rows (square e) h (butterfly e h x))

-- 读法：`view` 的取值由 `e (read h x j)` 给出。
def view (h : ℕ) (x : Val (tree h a)) (j : Cell h) := e (read h x j)

-- 读法：`view e h (butterfly e h x)` 等于 `walsh (view e h x)`。对 `h` 作归纳。
theorem view_butterfly (h : ℕ) (x : Val (tree h a)) :
    view e h (butterfly e h x) = walsh (view e h x) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have h₀ : slice 0 (view e (h + 1) x) = view e h x.1 := by funext j; simp [view, read, slice]
    have h₁ : slice 1 (view e (h + 1) x) = view e h x.2 := by funext j; simp [view, read, slice]
    funext j
    rw [walsh, h₀, h₁, ← ih, ← ih]
    have hp := read_both (step e) h (butterfly e h x.1, butterfly e h x.2) (Fin.tail j)
    obtain ⟨hl, hr⟩ := Prod.mk.inj hp
    simp only [view, read, butterfly]
    split_ifs <;> simp only [hl, hr, Equiv.apply_symm_apply]

-- 读法：`view e h (correlation e h x)` 等于 `(fun _ => (2 : K) ^ h) * conv (view e h x) (view e h x)`。用函数外延性比较等号两侧在 `j` 处的取值。
theorem view_correlation (h : ℕ) (x : Val (tree h a)) :
    view e h (correlation e h x) = (fun _ => (2 : K) ^ h) * conv (view e h x) (view e h x) := by
  have sq y : view e h (rows (square e) h y) = view e h y * view e h y := by
    funext j
    simp [view, read_rows, square]
  rw [correlation, view_butterfly, sq, view_butterfly, autocorrelation]

variable {u m : ℕ} {L : Set (Table F)}

-- 读法：要证明的命题是 `DWide F u L (tree h a) (tree h a) (rows s h) (2 ^ h * m)`。对 `h` 作归纳。
private theorem net_rows {s : Val a → Val a} (hs : DWide F u L a a s m) (h : ℕ) :
    DWide F u L (tree h a) (tree h a) (rows s h) (2 ^ h * m) := by
  induction h with
  | zero => simpa [rows] using hs
  | succ h ih => rw [pow_succ', mul_assoc, two_mul]; exact ih.par ih

-- 读法：要证明的命题是 `DWide F u L (tree (h + 1) a) (tree (h + 1) a) (both s h) (2 ^ h * m)`。对 `h` 作归纳。
private theorem net_both {s : Val (.pair a a) → Val (.pair a a)}
    (hs : DWide F u L (.pair a a) (.pair a a) s m) (h : ℕ) :
    DWide F u L (tree (h + 1) a) (tree (h + 1) a) (both s h) (2 ^ h * m) := by
  induction h with
  | zero => simpa [both] using hs
  | succ h ih =>
    rw [pow_succ', mul_assoc, two_mul]
    exact ((ih.par ih).pre (.middle _ _ _ _)).post (.middle _ _ _ _)

-- 读法：要证明的命题是 `DWide F u L (tree h a) (tree h a) (butterfly e h) (2 ^ h * (h + 1) * m)`。对 `h` 作归纳。
private theorem net_butterfly (hu : 3 ≤ u) (hm : 4 * wd a ≤ m)
    (hs : DWide F u L (.pair a a) (.pair a a) (step e) m) (h : ℕ) :
    DWide F u L (tree h a) (tree h a) (butterfly e h) (2 ^ h * (h + 1) * m) := by
  induction h with
  | zero =>
    exact (DWide.of_dnet hu (DNet.id F a)).mono (by simpa using hm)
  | succ h ih =>
    refine ((ih.par ih).comp (net_both hs h)).mono ?_
    rw [pow_succ]
    nlinarith only [Nat.zero_le (2 ^ h * m)]

-- 读法：`operation` 的取值由 `⟨b, b, fun x y => if s x = y then 1 else 0⟩` 给出。
private def operation (F : Type) [Field F] (b : Wire) (s : Val b → Val b) : Table F :=
  ⟨b, b, fun x y => if s x = y then 1 else 0⟩

-- 读法：`dictionary` 的取值由 `{operation F (.pair a a) (step e), operation F a (square e)}` 给出。
def dictionary (F : Type) [Field F] : Finset (Table F) :=
  {operation F (.pair a a) (step e), operation F a (square e)}

-- 读法：`(dictionary e F).card` 不超过 `2`。使用 `Finset.card_le_two` 给出的结论。
theorem dictionary_size : (dictionary e F).card ≤ 2 := Finset.card_le_two

-- 读法：`wd t.1 + wd t.2.1` 不超过 `4 * wd a`。
theorem dictionary_arity {t : Table F} (ht : t ∈ dictionary e F) :
    wd t.1 + wd t.2.1 ≤ 4 * wd a := by
  simp only [dictionary, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> simp only [operation, wd] <;> omega

-- 读法：要证明的命题是 `DWide F u (dictionary e F) (tree h a) (tree h a) (correlation e h) (2 ^ h * (2 * h + 3) * (1 + 4 * wd a))`。
/-- 站点数和端口数均为拟线性量级，与被编码环的算术运算无关。

英文原文：Quasilinear station and port count, independent of the arithmetic
of the encoded ring.
-/
theorem correlation_net (h : ℕ) (hu : 3 ≤ u) (hw : 4 * wd a ≤ u) :
    DWide F u (dictionary e F) (tree h a) (tree h a) (correlation e h)
      (2 ^ h * (2 * h + 3) * (1 + 4 * wd a)) := by
  let m := 1 + 4 * wd a
  have table (b : Wire) (s : Val b → Val b) (hb : wd b + wd b ≤ 4 * wd a)
      (ht : operation F b s ∈ dictionary e F) : DWide F u (dictionary e F) b b s m :=
    ⟨_, Nat.add_le_add_left hb _, .table _ _ _ (hb.trans hw) (.inr ht)⟩
  have t := net_butterfly e hu (by unfold m; omega)
    (table (.pair a a) (step e) (by simp only [wd]; omega) (by simp [dictionary])) h
  have b := net_rows (table a (square e) (by omega) (by simp [dictionary])) h
  exact ((t.comp b).comp t).mono (by unfold m; exact le_of_eq (by ring))

end OAI.LinearAlgebra.MatrixExponent.Mixer
end

/-!
# 利用有界长度的二进制字精确计算整数自相关

对 `2^h` 个不超过 `2^d` 的输入，每个字选取 `2(h+d)+1` 位。两次变换中始终按该字长取模计算。最终经缩放的整数小于模数，因此即使某些中间运算发生回绕，仍可恢复该整数。

**英文原文**

Exact integer autocorrelations in bounded binary words

For `2^h` inputs bounded by `2^d` choose `2(h+d)+1` bits per
word. Compute modulo that word size throughout the two transforms.
The final scaled integer is below the modulus. It can therefore be
recovered even though some intermediate operations may wrap.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Mixer

open Packing Finset

-- 读法：`wordCode` 的结果类型为 `Val (word n) ≃ ZMod (2 ^ n)`。
def wordCode (n : ℕ) : Val (word n) ≃ ZMod (2 ^ n) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_congr (bits (word n)), Fintype.card_fun, card_slots, wd_word,
      Fintype.card_bool, ZMod.card])

-- 读法：逐一匹配以下输入模式：`0, f`、`h + 1, f`。
def write {a : Wire} : (h : ℕ) → (Cell h → Val a) → Val (tree h a)
  | 0, f => f 0
  | h + 1, f => (write h (slice 0 f), write h (slice 1 f))

-- 读法：`read h (write h f)` 等于 `f`。对 `h` 作归纳。
theorem read_write {a : Wire} (h : ℕ) (f : Cell h → Val a) : read h (write h f) = f := by
  induction h with
  | zero => funext x; exact congrArg f (Subsingleton.elim _ _)
  | succ h ih =>
    apply slice_ext <;> funext x <;> simp [slice, read, write, ih]

-- 读法：`encode` 的取值由 `write h (fun x => (wordCode n).symm (u x : ZMod (2 ^ n)))` 给出。
def encode (h n : ℕ) (u : Cell h → ℕ) :=
  write h (fun x => (wordCode n).symm (u x : ZMod (2 ^ n)))

-- 读法：结论为 `let n := 2 * (h + d) + 1 let e := wordCode n (view e h (correlation e h (encode h n u)) z).val = 2 ^ h * ∑ x, u x * u (x + z)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem exact_correlation (h d : ℕ) (u : Cell h → ℕ) (hu : ∀ x, u x ≤ 2 ^ d) (z : Cell h) :
    let n := 2 * (h + d) + 1
    let e := wordCode n
    (view e h (correlation e h (encode h n u)) z).val = 2 ^ h * ∑ x, u x * u (x + z) := by
  intro n e
  have he : view e h (encode h n u) = fun x => (u x : ZMod (2 ^ n)) := by
    funext x
    simp only [encode, view, read_write, e, Equiv.apply_symm_apply]
  have hlim : 2 ^ h * (∑ x, u x * u (x + z)) < 2 ^ n := calc
    _ ≤ 2 ^ h * ∑ _x : Cell h, 2 ^ d * 2 ^ d :=
      Nat.mul_le_mul_left _ (sum_le_sum fun x _ => Nat.mul_le_mul (hu x) (hu (x + z)))
    _ = 2 ^ (2 * (h + d)) := by
      rw [sum_const, card_univ, card_cell, Nat.nsmul_eq_mul, two_mul]
      simp only [pow_add]
      ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by unfold n; omega)
  rw [view_correlation, he]
  change ((2 : ZMod (2 ^ n)) ^ h * ∑ x, (u x : ZMod (2 ^ n)) * u (x + z)).val = _
  simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using ZMod.val_natCast_of_lt hlim

end OAI.LinearAlgebra.MatrixExponent.Mixer
end
