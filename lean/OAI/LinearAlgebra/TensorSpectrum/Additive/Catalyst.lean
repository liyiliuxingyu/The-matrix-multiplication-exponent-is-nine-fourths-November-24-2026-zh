-- 本文件所属证明环节：把有限加性系统给出的稳定等式整理为带催化元的不等式；在可加的展平秩条件下排除催化元为零。乘法迭代始终保留同一份催化元。
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# 加性态障碍中的催化子

所有比较始终保留催化元。特别地，下面的乘法归纳只保留一个 `s`，既不约去 `s`，也不将其替换为 `s^j`。假设仅为有序半环的基本运算律，随后由具体的张量限制半环加以实例化。

**英文原文**

Catalysts in the additive-state obstruction

All comparisons retain the catalyst. In particular the multiplicative induction
below keeps a single copy of `s`; it neither cancels `s` nor substitutes `s^j`.
The hypotheses are elementary ordered-semiring laws, to be instantiated by the
concrete tensor restriction semiring.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

variable {S : Type*} [CommSemiring S] [PartialOrder S]

-- 读法：`StableEquality` 表示以下条件：存在 `c : S`，`a + c` 等于 `b + c`。
/-- 有限加法证书清除分母后给出的稳定等式。

英文原文：The stable equality supplied by a cleared finite additive certificate.
-/
def StableEquality (a b : S) : Prop := ∃ c : S, a + c = b + c

omit [PartialOrder S] in
-- 读法：要证明的命题是 `StableEquality a a`。
theorem StableEquality.refl (a : S) : StableEquality a a := ⟨0, rfl⟩

omit [PartialOrder S] in
-- 读法：要证明的命题是 `StableEquality b a`。
theorem StableEquality.symm {a b : S} (h : StableEquality a b) :
    StableEquality b a := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

omit [PartialOrder S] in
-- 读法：要证明的命题是 `StableEquality a c`。
theorem StableEquality.trans {a b c : S}
    (hab : StableEquality a b) (hbc : StableEquality b c) :
    StableEquality a c := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨u + v, ?_⟩
  calc
    a + (u + v) = (a + u) + v := by ring
    _ = (b + u) + v := by rw [hu]
    _ = (b + v) + u := by ring
    _ = (c + v) + u := by rw [hv]
    _ = c + (u + v) := by ring

omit [PartialOrder S] in
-- 读法：要证明的命题是 `StableEquality (a + c) (b + d)`。
theorem StableEquality.add {a b c d : S}
    (hab : StableEquality a b) (hcd : StableEquality c d) :
    StableEquality (a + c) (b + d) := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hcd
  refine ⟨u + v, ?_⟩
  calc
    a + c + (u + v) = (a + u) + (c + v) := by ring
    _ = (b + u) + (d + v) := by rw [hu, hv]
    _ = b + d + (u + v) := by ring

-- 读法：存在 `D : S`，`D + (m : S) + T * s` 不超过 `D + (k : S) * s`。
theorem stable_certificate_to_catalyst
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    {m k : ℕ} {T s x y : S} (hxy : x ≤ y)
    (hstable : StableEquality ((m : S) + y + T * s) (x + (k : S) * s)) :
    ∃ D : S, D + (m : S) + T * s ≤ D + (k : S) * s := by
  obtain ⟨c, hc⟩ := hstable
  refine ⟨y + c, ?_⟩
  calc
    y + c + (m : S) + T * s = ((m : S) + y + T * s) + c := by ring
    _ = (x + (k : S) * s) + c := hc
    _ = x + ((k : S) * s + c) := by ring
    _ ≤ y + ((k : S) * s + c) := hadd _ _ _ hxy
    _ = y + c + (k : S) * s := by ring

omit [PartialOrder S] in
-- 读法：`F (n : S)` 等于 `n`。对 `n` 作归纳。
theorem additiveMap_natCast (F : S →+ ℕ) (hF : F 1 = 1) (n : ℕ) :
    F (n : S) = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, F.map_zero]
  | succ n ih => rw [Nat.cast_succ, F.map_add, ih, hF]

-- 读法：`s` 不等于 `0`。
/-- 利用展平秩的可加性排除 `s = 0`；这里所用的量是展平秩。

英文原文：Additive flattening rank, not ordinary tensor rank, rules out `s = 0`.
-/
theorem catalyst_nonzero (F : S →+ ℕ) (hF : F 1 = 1) (hmono : Monotone F)
    {D T s : S} {m k : ℕ} (hm : 0 < m)
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) : s ≠ 0 := by
  intro hs
  subst s
  have h' := hmono h
  simp only [mul_zero, add_zero, F.map_add, additiveMap_natCast F hF] at h'
  omega

-- 读法：`D + (n : S) * (m : S) + (n : S) * (T * s)` 不超过 `D + (n : S) * ((k : S) * s)`。对 `n` 作归纳。
/-- 在加法迭代中保持同一固定的 `D`，两侧的增益均随 `n` 成比例增长。

英文原文：Additive iteration retains one fixed `D`, while both gains scale with `n`.
-/
theorem catalyst_additive_iteration
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    {D T s : S} {m k : ℕ}
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) (n : ℕ) :
    D + (n : S) * (m : S) + (n : S) * (T * s) ≤
      D + (n : S) * ((k : S) * s) := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    rw [Nat.cast_succ]
    calc
      D + ((n : S) + 1) * (m : S) + ((n : S) + 1) * (T * s) =
          (D + (m : S) + T * s) + ((n : S) * (m : S) + (n : S) * (T * s)) := by ring
      _ ≤ (D + (k : S) * s) + ((n : S) * (m : S) + (n : S) * (T * s)) :=
        hadd _ _ _ h
      _ = (D + (n : S) * (m : S) + (n : S) * (T * s)) + (k : S) * s := by ring
      _ ≤ (D + (n : S) * ((k : S) * s)) + (k : S) * s := hadd _ _ _ ih
      _ = D + ((n : S) + 1) * ((k : S) * s) := by ring

-- 读法：`(n : S) * T * s` 不超过 `((n * k + r : ℕ) : S) * s`。
/-- 利用固定催化子的秩界以及 `1 ≤ s` 将其吸收。

英文原文：Absorb the fixed catalyst using its rank bound and `1 ≤ s`.
-/
theorem catalyst_absorbed_comparison
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : S, 0 ≤ a)
    {D T s : S} {m k r : ℕ} (hD : D ≤ (r : S)) (hs : 1 ≤ s)
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) (n : ℕ) :
    (n : S) * T * s ≤ ((n * k + r : ℕ) : S) * s := by
  have hDs : D ≤ (r : S) * s :=
    hD.trans (by simpa only [mul_one] using hmul 1 s (r : S) hs)
  calc
    (n : S) * T * s = 0 + ((n : S) * (T * s)) := by ring
    _ ≤ (D + (n : S) * (m : S)) + ((n : S) * (T * s)) :=
      hadd _ _ _ (hzero _)
    _ ≤ D + (n : S) * ((k : S) * s) := catalyst_additive_iteration hadd h n
    _ ≤ (r : S) * s + (n : S) * ((k : S) * s) := hadd _ _ _ hDs
    _ = ((n * k + r : ℕ) : S) * s := by rw [Nat.cast_add, Nat.cast_mul]; ring

-- 读法：`b ^ j * s` 不超过 `a ^ j * s`。对 `j` 作归纳。
/-- 对含催化子的乘法比较作迭代时，保留其中的张量因子。

英文原文：Iteration of a catalytic multiplicative comparison does not cancel the tensor.
-/
theorem catalytic_power_iteration
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    {a b s : S} (h : b * s ≤ a * s) (j : ℕ) :
    b ^ j * s ≤ a ^ j * s := by
  induction j with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ j ih =>
    calc
      b ^ (j + 1) * s = b ^ j * (b * s) := by ring
      _ ≤ b ^ j * (a * s) := hmul _ _ _ h
      _ = a * (b ^ j * s) := by ring
      _ ≤ a * (a ^ j * s) := hmul _ _ _ ih
      _ = a ^ (j + 1) * s := by ring

end OAI.LinearAlgebra.TensorSpectrum
