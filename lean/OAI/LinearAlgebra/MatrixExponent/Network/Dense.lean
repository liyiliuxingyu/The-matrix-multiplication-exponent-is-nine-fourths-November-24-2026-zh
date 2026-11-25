-- 本文件所属证明环节：定义三价比特网络及多表判重张量的实现关系，并通过表分解和基域转换比较不同实现的成本。
import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# 用三价网络实现任意表

为表增设一个使能比特。按下一个地址比特拆分时，两个子表中恰有一个被启用，未启用的子表贡献因子一。每次拆分时，复制其余比特的成本等于其宽度。

**英文原文**

Trivalent realization of arbitrary tables

Give the table one enable bit. Splitting on the next address bit enables
exactly one of two subtables, while a disabled subtable contributes the
factor one. Copying the remaining bits costs their width at each split.
-/

namespace OAI.LinearAlgebra.MatrixExponent
namespace Net

variable {F : Type} [Field F]

-- 读法：存在从 `.unit` 到 `(.pair a a)` 的网络，核为 `(fun _ y => if y.1 = y.2 then 1 else 0)`，顶点数为 `(wd a)`，系数取自 `F`。对 `a` 作归纳。
/-- 无输入时产生的一对相同线束。

英文原文：A pair of identical bundles with no inputs.
-/
theorem cup (F : Type) [Field F] (a : Wire) :
    Net F .unit (.pair a a) (fun _ y => if y.1 = y.2 then 1 else 0) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact (Net.empty (F := F)).post (.unit _)
  | pair a b ha hb =>
    simpa only [wd, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using
      ((ha.par hb).pre (.unit' _)).post (.middle a b a b)

-- 读法：存在从 `a` 到 `b` 的网络，核为 `k`，顶点数为 `(m + wd b)`，系数取自 `F`。
/-- 将一部分输入转为输出，代价是在相应比特上逐对检验相等性。

英文原文：Turn some inputs into outputs, paying for a pairwise equality test
on the corresponding bits.
-/
theorem curry {a b : Wire} {k : Val a → Val b → F} {m : ℕ}
    (h : Net F (.pair a b) .unit (fun x _ => k x.1 x.2) m) :
    Net F a b k (m + wd b) := by
  have g := ((h.par (cup F b)).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using g.trace

-- 读法：`Enabled` 表示以下条件：对每个 `k : Val a → F`，存在 `m`，`Net F (.pair .bit a) .unit (fun x _ => if x.1 then k x.2 else 1) m` 与 `m + wd a + 5 ≤ 6 * 2 ^ wd a` 同时成立。
/-- 宽度的加法项用于支付复制尚未处理的地址比特的成本。

英文原文：The additive width term pays for copying the unprocessed address bits.
-/
private def Enabled (F : Type) [Field F] (a : Wire) : Prop :=
  ∀ k : Val a → F, ∃ m, Net F (.pair .bit a) .unit (fun x _ => if x.1 then k x.2 else 1) m ∧
    m + wd a + 5 ≤ 6 * 2 ^ wd a

-- 读法：要证明的命题是 `Enabled F (.pair .bit a)`。
private theorem enabled_bit {a : Wire} (h : Enabled F a) : Enabled F (.pair .bit a) := by
  intro k
  obtain ⟨m, lo, hm⟩ := h (fun x => k (false, x))
  obtain ⟨n, hi, hn⟩ := h (fun x => k (true, x))
  have zero := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && !x.2) (by decide)
  have one := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
  obtain ⟨v, hv, split⟩ :=
    (((zero.pair one).par (DNet.dup F a)).pre (.assoc' .bit .bit a)).post (.middle .bit .bit a a)
  refine ⟨v + (m + n), ?_, ?_⟩
  · have H := (split.comp (lo.par hi)).post (.unit' _)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at H
    convert H using 1
    funext ⟨b, c, x⟩ y
    cases b <;> cases c <;> simp
  · simp only [wd, pow_add, pow_one] at hv ⊢
    omega

-- 读法：要证明的命题是 `Enabled F (.pair a b)`。对 `a` 作归纳，并把 `b` 保持为任意参数。
private theorem enabled_extend (a : Wire) {b : Wire} (h : Enabled F b) :
    Enabled F (.pair a b) := by
  induction a generalizing b with
  | bit => exact enabled_bit h
  | unit =>
    intro k
    obtain ⟨m, H, hm⟩ := h (fun x => k ((), x))
    exact ⟨m, H.pre ((Rewire.id _).par ((Rewire.swap _ _).comp (.unit _))),
      by simpa only [wd, Nat.zero_add] using hm⟩
  | pair a c ha hc =>
    intro k
    obtain ⟨m, H, hm⟩ := ha (hc h) (fun x => k ((x.1, x.2.1), x.2.2))
    exact ⟨m, H.pre ((Rewire.id _).par (.assoc _ _ _)),
      by simpa only [wd, Nat.add_assoc] using hm⟩

-- 读法：存在 `m`，`Net F a .unit (fun x _ => k x) m` 与 `m ≤ 6 * 2 ^ wd a` 同时成立。
private theorem dense_weight (a : Wire) (k : Val a → F) :
    ∃ m, Net F a .unit (fun x _ => k x) m ∧ m ≤ 6 * 2 ^ wd a := by
  have base : Enabled F .unit := fun _ => ⟨1, .table _ _ _ (by decide), by decide⟩
  obtain ⟨m, H, hm⟩ := enabled_extend a base (fun x => k x.1)
  have pin := DNet.table F .unit .bit (fun _ => true) (by decide)
  obtain ⟨v, hv, G⟩ := (pin.par (DNet.id F a)).pre ((Rewire.unit' a).comp (.swap _ _))
  refine ⟨v + m, ?_, by simp only [wd, Nat.add_zero] at hm; omega⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
    G.comp (H.pre ((Rewire.id _).par (.unit' _)))

-- 读法：存在 `m`，`Net F a b k m` 与 `m ≤ 8 * 2 ^ (wd a + wd b)` 同时成立。
/-- 任意作用于 `r` 个外部比特的表至多需要 `8 * 2 ^ r` 个三价顶点。

英文原文：Any table on `r` exterior bits needs at most `8 * 2 ^ r` trivalent vertices.
-/
theorem dense (a b : Wire) (k : Val a → Val b → F) :
    ∃ m, Net F a b k m ∧ m ≤ 8 * 2 ^ (wd a + wd b) := by
  obtain ⟨m, H, hm⟩ := dense_weight (.pair a b) (fun x => k x.1 x.2)
  refine ⟨m + wd b, H.curry, ?_⟩
  have := Nat.lt_two_pow_self (n := wd a + wd b)
  simp only [wd] at hm
  omega

end Net
end OAI.LinearAlgebra.MatrixExponent
