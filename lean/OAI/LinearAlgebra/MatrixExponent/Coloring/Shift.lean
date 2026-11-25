-- 本文件所属证明环节：为置换网络中配对的边作匹配和均衡着色，并把图论分配步骤编码成可计算的有限地址和置换。
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import Mathlib.Order.Preorder.Finite

section
/-!
# 将整数边重数减半

在两侧的顶点上分别拆分重数为奇数的边。保留奇重虚拟边较少的颜色，可将每个顶点的度数减半，并使虚拟边总数至少减半。

**英文原文**

Halving integral edge multiplicities

Split the edges of odd multiplicity at both sets of vertices. Keeping
the colour with fewer odd dummy edges halves every vertex degree and
at least halves the total number of dummy edges.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h k : ℕ}

-- 读法：`stock` 的取值由 `∑ i ∈ Finset.univ.filter (fun i => f i = j), m i` 给出。
def stock (f : Fin (2 ^ h) → Fin (2 ^ k)) (m : Fin (2 ^ h) → ℕ) (j : Fin (2 ^ k)) :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = j), m i

-- 读法：`dummyStock` 的取值由 `∑ i ∈ Finset.univ.filter (fun i => δ i), m i` 给出。
def dummyStock (δ : Fin (2 ^ h) → Bool) (m : Fin (2 ^ h) → ℕ) :=
  ∑ i ∈ Finset.univ.filter (fun i => δ i), m i

-- 读法：`oddMask` 的取值由 `decide (m i % 2 = 1)` 给出。
def oddMask (m : Fin (2 ^ h) → ℕ) (i : Fin (2 ^ h)) := decide (m i % 2 = 1)

-- 读法：`minority` 的结果类型为 `Bool`。
def minority (δ a c : Fin (2 ^ h) → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => δ i = true ∧ a i = true ∧ c i = true)).card ≤
    (Finset.univ.filter (fun i => δ i = true ∧ a i = true ∧ c i = false)).card)

-- 读法：`halve` 的取值由 `let a := oddMask m let c := split f g a m i / 2 + if a i && (c i == minority δ a c) then 1 else 0` 给出。
def halve (f g : Fin (2 ^ h) → Fin (2 ^ k)) (δ : Fin (2 ^ h) → Bool) (m : Fin (2 ^ h) → ℕ)
    (i : Fin (2 ^ h)) : ℕ :=
  let a := oddMask m
  let c := split f g a
  m i / 2 + if a i && (c i == minority δ a c) then 1 else 0

variable {f g : Fin (2 ^ h) → Fin (2 ^ k)} {δ : Fin (2 ^ h) → Bool} {m : Fin (2 ^ h) → ℕ}

-- 读法：结论为 `∑ i ∈ S, m i = 2 * (∑ i ∈ S, m i / 2) + (S.filter (fun i => oddMask m i)).card`。
private theorem stock_sum (S : Finset (Fin (2 ^ h))) (m : Fin (2 ^ h) → ℕ) :
    ∑ i ∈ S, m i = 2 * (∑ i ∈ S, m i / 2) + (S.filter (fun i => oddMask m i)).card := by
  rw [Finset.mul_sum, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [oddMask, decide_eq_true_eq]
  split <;> omega

-- 读法：结论为 `∑ i ∈ S, halve f g δ m i = (∑ i ∈ S, m i / 2) + (S.filter (fun i => oddMask m i = true ∧ split f g (oddMask m) i = minority δ (oddMask m) (split f g (oddMask m)))).card`。
private theorem halve_sum (S : Finset (Fin (2 ^ h))) :
    ∑ i ∈ S, halve f g δ m i = (∑ i ∈ S, m i / 2) +
      (S.filter (fun i => oddMask m i = true ∧
        split f g (oddMask m) i = minority δ (oddMask m) (split f g (oddMask m)))).card := by
  simp only [halve, Bool.and_eq_true, beq_iff_eq, Finset.sum_add_distrib, Finset.card_filter]

-- 读法：要证明的命题是 `EvenFibers f (oddMask m)`。
private theorem even_mask (hf : ∀ j, Even (stock f m j)) : EvenFibers f (oddMask m) := by
  intro j
  obtain ⟨n, hn⟩ := hf j
  rw [stock, stock_sum] at hn
  simp only [Finset.filter_filter, and_comm (a := f _ = j)] at hn
  refine ⟨n - ∑ i ∈ Finset.univ.filter (fun i => f i = j), m i / 2, ?_⟩
  omega

-- 读法：`2 * stock f (halve f g δ m) j = stock f m j` 与 `2 * stock g (halve f g δ m) j = stock g m j` 同时成立。
theorem stock_halve (hf : ∀ j, Even (stock f m j)) (hg : ∀ j, Even (stock g m j))
    (δ : Fin (2 ^ h) → Bool) (j : Fin (2 ^ k)) :
    2 * stock f (halve f g δ m) j = stock f m j ∧
    2 * stock g (halve f g δ m) j = stock g m j := by
  let a := oddMask m
  let c := split f g a
  let b := minority δ a c
  have aux (p : Fin (2 ^ h) → Fin (2 ^ k))
      (hp : 2 * (Finset.univ.filter (fun i => a i = true ∧ p i = j ∧ c i = b)).card =
        (Finset.univ.filter (fun i => a i = true ∧ p i = j)).card) :
      2 * stock p (halve f g δ m) j = stock p m j := by
    unfold stock
    rw [halve_sum, stock_sum _ m, mul_add]
    simp only [Finset.filter_filter, and_comm (a := p _ = j) (b := oddMask m _ = true),
      and_left_comm (a := p _ = j)]
    exact congrArg _ hp
  obtain ⟨hl, hr⟩ := split_balanced (even_mask hf) (even_mask hg) j b
  exact ⟨aux f hl, aux g hr⟩

-- 读法：`2 * (Finset.univ.filter fun i => δ i = true ∧ a i = true ∧ c i = minority δ a c).card` 不超过 `(Finset.univ.filter fun i => δ i = true ∧ a i = true).card`。按 `num true ≤ num false` 成立与否分情况。
private theorem minority_le (δ a c : Fin (2 ^ h) → Bool) :
    2 * (Finset.univ.filter fun i => δ i = true ∧ a i = true ∧ c i = minority δ a c).card ≤
      (Finset.univ.filter fun i => δ i = true ∧ a i = true).card := by
  let S := Finset.univ.filter (fun i => δ i = true ∧ a i = true)
  let num (b : Bool) := (Finset.univ.filter fun i => δ i = true ∧ a i = true ∧ c i = b).card
  have hs : num true + num false = S.card := by
    have he := Finset.card_filter_add_card_filter_not (s := S) (fun i => c i = true)
    simpa [S, num, Finset.filter_filter, and_assoc] using he
  change 2 * num (decide (num true ≤ num false)) ≤ S.card
  by_cases hd : num true ≤ num false
  · rw [decide_eq_true hd]
    omega
  · rw [decide_eq_false hd]
    omega

-- 读法：`2 * dummyStock δ (halve f g δ m)` 不超过 `dummyStock δ m`。这里调用 `Nat.add_le_add_left`。
theorem dummy_halve (f g : Fin (2 ^ h) → Fin (2 ^ k)) (δ : Fin (2 ^ h) → Bool) (m : Fin (2 ^ h) → ℕ) :
    2 * dummyStock δ (halve f g δ m) ≤ dummyStock δ m := by
  unfold dummyStock
  rw [halve_sum, stock_sum _ m, mul_add]
  simp only [Finset.filter_filter]
  exact Nat.add_le_add_left (minority_le δ _ _) _

-- 读法：`halve f g δ m i` 不超过 `m i`。
theorem halve_le (f g : Fin (2 ^ h) → Fin (2 ^ k)) (δ : Fin (2 ^ h) → Bool)
    (m : Fin (2 ^ h) → ℕ) (i : Fin (2 ^ h)) : halve f g δ m i ≤ m i := by
  simp only [halve, Bool.and_eq_true, oddMask, decide_eq_true_eq]
  split <;> omega

-- 读法：结论为 `let y := (halve f g δ)^[d] m (∀ j, stock f y j = if j ∈ S then 1 else 0) ∧ (∀ j, stock g y j = if j ∈ S then 1 else 0) ∧ (∀ i, y i ≤ m i) ∧ ∀ i, δ i = true → y i = 0`。对 `d` 作归纳，并把 `m` 保持为任意参数。
/-- 从二的幂次度数出发，反复折半可在支集中的每个顶点选出一条边。严格小于该度数的占位预算最终降为零。

英文原文：Starting at power-of-two degree, repeated halving selects one edge
at each supported vertex. A strictly smaller dummy budget vanishes.
-/
theorem perfect {d : ℕ} (S : Finset (Fin (2 ^ k)))
    (hf : ∀ j, stock f m j = if j ∈ S then 2 ^ d else 0)
    (hg : ∀ j, stock g m j = if j ∈ S then 2 ^ d else 0) (hd : dummyStock δ m < 2 ^ d) :
    let y := (halve f g δ)^[d] m
    (∀ j, stock f y j = if j ∈ S then 1 else 0) ∧
    (∀ j, stock g y j = if j ∈ S then 1 else 0) ∧
    (∀ i, y i ≤ m i) ∧ ∀ i, δ i = true → y i = 0 := by
  induction d generalizing m with
  | zero =>
    refine ⟨hf, hg, fun i => le_rfl, fun i hi => ?_⟩
    change m i = 0
    -- 推导：记下中间结论 `h`：`m i ≤ dummyStock δ m`。
    have h : m i ≤ dummyStock δ m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hi])
    omega
  | succ d ih =>
    have he (j : Fin (2 ^ k)) : Even (if j ∈ S then 2 ^ (d + 1) else 0 : ℕ) := by
      split
      · exact ⟨2 ^ d, by rw [pow_succ, mul_two]⟩
      · exact ⟨0, rfl⟩
    have hp := stock_halve (fun j => (hf j).symm ▸ he j) (fun j => (hg j).symm ▸ he j) δ
    have next (j : Fin (2 ^ k)) :
        stock f (halve f g δ m) j = (if j ∈ S then 2 ^ d else 0) ∧
        stock g (halve f g δ m) j = (if j ∈ S then 2 ^ d else 0) := by
      -- 推导：从 `hp j` 中取出 `hl, hr`。
      obtain ⟨hl, hr⟩ := hp j
      rw [hf, pow_succ] at hl
      rw [hg, pow_succ] at hr
      split_ifs at * <;> omega
    have hs := dummy_halve f g δ m
    rw [pow_succ] at hd
    obtain ⟨hl, hr, hm, hz⟩ := ih (fun j => (next j).1) (fun j => (next j).2) (by omega)
    rw [Function.iterate_succ_apply]
    exact ⟨hl, hr, fun i => (hm i).trans (halve_le f g δ m i), hz⟩

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 对小端序地址加一与移位

**英文原文**

Incrementing and shifting little-endian addresses
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：`double` 的结果类型为 `B (n + 1)`。
def double {n : ℕ} (x : B n) (b : Bool) : B (n + 1) :=
  ⟨2 * x.val + b.toNat, by have := x.isLt; cases b <;> simp [pow_succ] <;> omega⟩

-- 读法：`half` 的取值由 `⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩` 给出。
def half {n : ℕ} (x : B n) : B n := ⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩

-- 读法：`odd` 的取值由 `decide (x.val % 2 = 1)` 给出。
def odd {n : ℕ} (x : B n) : Bool := decide (x.val % 2 = 1)

-- 读法：`Lookup.value n (Lookup.inc n x)` 等于 `if Lookup.value n x + 1 < 2 ^ n then Lookup.value n x + 1 else 0`。对 `n` 作归纳。
private theorem inc_value (n : ℕ) (x : Val (word n)) :
    Lookup.value n (Lookup.inc n x) =
      if Lookup.value n x + 1 < 2 ^ n then Lookup.value n x + 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b, y⟩ := x
    have := Control.value_lt n y
    cases b <;> simp [Lookup.inc, Lookup.value, ih, pow_succ] <;> split_ifs <;> omega

-- 读法：逐一匹配以下输入模式：`0, _`、`n + 1, x`。
private def extend : (n : ℕ) → Val (word n) → Val (word (n + 1))
  | 0, _ => (false, ())
  | n + 1, x => (x.1, extend n x.2)

-- 读法：`Lookup.value (n + 1) (extend n x)` 等于 `Lookup.value n x`。对 `n` 作归纳。
private theorem extend_value (n : ℕ) (x : Val (word n)) :
    Lookup.value (n + 1) (extend n x) = Lookup.value n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change x.1.toNat + 2 * Lookup.value (n + 1) (extend n x.2) = _
    rw [ih]
    rfl

variable (F : Type) [Field F]

-- 读法：在 `F` 上，函数 `(extend n)` 从 `(word n)` 到 `(word (n + 1))` 的图张量可由至多 `(n + 1)` 个顶点实现。对 `n` 作归纳。
private theorem extend_net (n : ℕ) : DNet F (word n) (word (n + 1)) (extend n) (n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih => exact ((DNet.id F .bit).par ih).mono (by simp [wd]; omega)

-- 读法：在 `F` 上按格式 `(.addr n)`、`(.addr (n + 1))` 编码输入输出，映射 `(fun x => Fin.castLE (by rw [pow_succ]; omega) x)` 的电路规模至多为 `(n + 1)`。这里调用 `Circuit.of_dnet`。
/-- 在最高位补入一个零。

英文原文：Append a zero as the new most significant bit.
-/
theorem numeric_extend (n : ℕ) :
    Circuit F (.addr n) (.addr (n + 1))
      (fun x => Fin.castLE (by rw [pow_succ]; omega) x) (n + 1) := by
  apply Circuit.of_dnet (.refl _) (.refl _) (extend_net F n)
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_addr, ← code_addr]
  congr 1
  exact Fin.ext (extend_value n x)

-- 读法：在 `F` 上按格式 `(.pair (.pair (.addr n) (.addr n)) .bit)`、`(.addr n)` 编码输入输出，映射 `(fun x => if x.2 then x.1.1 else x.1.2)` 的电路规模至多为 `(1000 * (1 + n))`。这里调用 `Circuit.of_dnet`。
theorem numeric_select (n : ℕ) :
    Circuit F (.pair (.pair (.addr n) (.addr n)) .bit) (.addr n)
      (fun x => if x.2 then x.1.1 else x.1.2) (1000 * (1 + n)) := by
  apply Circuit.of_dnet (.refl _) (.refl _) ((selectWord F n).mono (n := 1000 * (1 + n)) (by omega))
  intro x
  let f (p : (B n × B n) × Bool) := (Format.addr n).code (if p.2 then p.1.1 else p.1.2)
  have hd : (Format.pair (.pair (.addr n) (.addr n)) .bit).code.symm
      (bits (.pair (.pair (word n) (word n)) .bit) x) =
      ((Control.index n x.1.1, Control.index n x.1.2), x.2) :=
    Prod.ext (decode_pair n x.1) rfl
  refine Eq.trans ?_ (congrArg f hd.symm)
  obtain ⟨⟨a, b⟩, c⟩ := x
  cases c <;> exact (code_addr n _).symm

-- 读法：在 `F` 上按格式 `(.addr n)`、`(.addr n)` 编码输入输出，映射 `(fun x => x + 1)` 的电路规模至多为 `(1000 * (1 + n))`。这里调用 `Circuit.of_dnet`。
theorem numeric_inc (n : ℕ) :
    Circuit F (.addr n) (.addr n) (fun x => x + 1) (1000 * (1 + n)) := by
  apply Circuit.of_dnet (.refl _) (.refl _) ((Lookup.inc_net F n).mono (n := 1000 * (1 + n)) (by omega))
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_addr n x, ← code_addr n (Lookup.inc n x)]
  congr 1
  apply Fin.ext
  change Lookup.value n (Lookup.inc n x) = (Lookup.value n x + 1 % 2 ^ n) % 2 ^ n
  rw [Nat.add_mod_mod, inc_value]
  have := Control.value_lt n x
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · rw [show Lookup.value n x + 1 = 2 ^ n by omega, Nat.mod_self]

-- 读法：在 `F` 上按格式 `(.pair (.addr n) .bit)`、`(.addr (n + 1))` 编码输入输出，映射 `(fun x => double x.1 x.2)` 的电路规模至多为 `(1000 * (1 + n))`。这里调用 `Circuit.of_dnet`。
theorem numeric_double (n : ℕ) :
    Circuit F (.pair (.addr n) .bit) (.addr (n + 1)) (fun x => double x.1 x.2) (1000 * (1 + n)) := by
  have h := (DNet.id F (.pair (word n) .bit)).post (.swap _ _)
  apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 1000 * (1 + n)) (by simp [wd]; omega))
  intro x
  change bits (word (n + 1)) (x.2, x.1) =
    (Format.addr (n + 1)).code (double ((Format.addr n).code.symm (bits (word n) x.1)) x.2)
  rw [decode_addr, ← code_addr]
  congr 1
  apply Fin.ext
  exact Nat.add_comm _ _

-- 读法：在 `F` 上按格式 `(.addr n)`、`(.addr n)` 编码输入输出，映射 `half` 的电路规模至多为 `(1000 * (1 + n))`。对 `n` 分类讨论。
theorem numeric_half (n : ℕ) :
    Circuit F (.addr n) (.addr n) half (1000 * (1 + n)) := by
  cases n with
  | zero =>
    convert (Circuit.id F (.addr 0)).mono (n := 1000 * (1 + 0)) (by simp) using 1
    funext x
    exact @Subsingleton.elim (Fin 1) _ _ _
  | succ n =>
    have h := (DNet.snd F .bit (word n)).comp (extend_net F n)
    apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 1000 * (1 + (n + 1))) (by simp [wd]; omega))
    intro x
    change bits (word (n + 1)) (extend n x.2) =
      (Format.addr (n + 1)).code (half ((Format.addr (n + 1)).code.symm (bits (word (n + 1)) x)))
    rw [decode_addr, ← code_addr]
    congr 1
    apply Fin.ext
    change Lookup.value (n + 1) (extend n x.2) = Lookup.value (n + 1) x / 2
    -- 推导：从 `x` 中取出 `b, x`。
    obtain ⟨b, x⟩ := x
    rw [extend_value]
    cases b <;> simp [Lookup.value]
    omega

-- 读法：在 `F` 上按格式 `(.addr n)`、`.bit` 编码输入输出，映射 `odd` 的电路规模至多为 `(1000 * (1 + n))`。对 `n` 分类讨论。
theorem numeric_odd (n : ℕ) :
    Circuit F (.addr n) .bit odd (1000 * (1 + n)) := by
  cases n with
  | zero =>
    have h := Lookup.const_net F .bit false
    apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 1000 * (1 + 0)) (by decide))
    intro x
    rfl
  | succ n =>
    have h := DNet.fst F .bit (word n)
    apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 1000 * (1 + (n + 1))) (by simp [wd]; omega))
    intro x
    change bits .bit x.1 = bits .bit (odd ((Format.addr (n + 1)).code.symm (bits (word (n + 1)) x)))
    rw [decode_addr]
    congr 1
    change x.1 = decide (Lookup.value (n + 1) x % 2 = 1)
    obtain ⟨b, x⟩ := x
    cases b <;> simp [Lookup.value]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# 通过排序求显式列出置换的逆

**英文原文**

Inverting an explicitly listed permutation by sorting
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

-- 读法：`permutation g (fun _ => true)` 等于 `g.symm`。这里调用 `lt_irrefl`。
private theorem sorted_inverse {h : ℕ} (g : Equiv.Perm (B h)) :
    permutation g (fun _ => true) = g.symm := by
  let σ := permutation g (fun _ => true)
  have hm : Monotone (g ∘ σ) := by
    intro i j hij
    have he := Tuple.monotone_sort (fun a => toLex (false, toLex (g a, a))) hij
    change toLex (false, toLex (g (σ i), σ i)) ≤ toLex (false, toLex (g (σ j), σ j)) at he
    rcases Prod.Lex.toLex_le_toLex.mp he with he | ⟨_, he⟩
    · exact (lt_irrefl _ he).elim
    rcases Prod.Lex.toLex_le_toLex.mp he with hl | ⟨he, _⟩
    · exact hl.le
    · exact he.le
  have he := (hm.strictMono_of_injective (g.injective.comp σ.injective)).eq_id
  exact Equiv.ext (fun i => g.eq_symm_apply.mpr (congrFun he i))

-- 读法：存在 `f`，`Cheap F h h (Perm h) (Perm h) f 100` 与 `∀ g : Equiv.Perm (B h), f g = ⇑g.symm` 同时成立。这里调用 `Nat.mul_le_mul_left`。
theorem cheap_inverse (F : Type) [Field F] (h : ℕ) :
    ∃ f, Cheap F h h (Perm h) (Perm h) f 100 ∧
      ∀ g : Equiv.Perm (B h), f g = ⇑g.symm := by
  have hp : (Perm h).width ≤ 2 ^ h * (100 + h) ^ 1 := by simp [Perm]
  have hb : (Format.vec h .bit).width ≤ 2 ^ h * (100 + h) ^ 1 := by
    rw [Format.width_vec, Format.width_bit, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have he : Cheap F h h (.pair (Perm h) (.vec h .bit)) (Perm h)
      (fun x => ⇑(permutation x.1 x.2)) 80 := by
    obtain ⟨m, hm, hc⟩ := cheap_permutation F h h
    refine ⟨m, hm, hc.trans (Nat.mul_le_mul_left _ ?_)⟩
    rw [show 80 = 2 * 40 from rfl, pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) _
  have hi := (Cheap.id F hp).pair (Cheap.const F hp hb (fun _ => true))
  refine ⟨_, (hi.comp he).mono (by decide), fun g => ?_⟩
  change ⇑(permutation g (fun _ => true)) = ⇑g.symm
  rw [sorted_inverse]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
