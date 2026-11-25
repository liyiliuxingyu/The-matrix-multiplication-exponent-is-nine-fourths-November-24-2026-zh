-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Processor.Handle
import OAI.LinearAlgebra.MatrixExponent.Processor.WindowSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Broadcast

/-!
# 有限域上的对角阻力

对于指定规模下的每一种替换，都可以使用同一个处理器。随后在不同站点可以独立选择处理器的字面编码。控制器及其规模上界都不需要计算复杂性假设。

**英文原文**

Diagonal resistance over a finite field

One processor works for every replacement of the prescribed size.
Its literal codes can then be chosen independently at the different
sites. The controller and its size bound require no complexity assumptions.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Filter

variable {F : Type} [Field F] [Fintype F]

-- 读法：`2 ^ W * (100 + W) ^ (Q + s)` 不超过 `N * w ^ ((Q + 10) + 2 * (Q + s))`。这里调用 `Nat.mul_le_mul`。
private theorem fit_window {N w W Q s : ℕ} (hs : W ≤ 2 * w) (hb : 2 ^ W ≤ N * w ^ (Q + 10))
    (hw : 200 ≤ w) : 2 ^ W * (100 + W) ^ (Q + s) ≤ N * w ^ ((Q + 10) + 2 * (Q + s)) := by
  rw [pow_add w, pow_mul, ← mul_assoc]
  exact Nat.mul_le_mul hb (Nat.pow_le_pow_left (by nlinarith : 100 + W ≤ w ^ 2) _)

-- 读法：要证明的命题是 `ControlBound F`。
theorem control (F : Type) [Field F] [Fintype F] : ControlBound F := by
  classical
  intro n h K Q hn hh hK A
  let t := (Q + 10) + 2 * (Q + 660)
  refine ⟨max t 5 + 1, ?_⟩
  filter_upwards [window n h K Q hn hh hK A, dispatch_scale A hn K t,
    eventually_ge_atTop 200] with w getW dispatch hw
  intro N r d l B fa hf _ P M hm hlabel hroom hex
  obtain ⟨W, H⟩ := getW fa M hm hex
  have hr : 0 < r := lt_of_lt_of_le (by decide) H.three
  let _ : NeZero r := ⟨hr.ne'⟩
  let _ : NeZero (3 * r) := ⟨by omega⟩
  -- 推导：记下中间结论 `hn4`：`0 < N / 4`。
  have hn4 : 0 < N / 4 := by have := hex.some.links; have := Nat.le_pow (a := 3 * r) (by decide : 0 < 2); omega
  let _ : NeZero (N / 4) := ⟨hn4.ne'⟩
  let e := Fintype.equivFin (Name n r)
  let _ : LinearOrder (Name n r) := LinearOrder.lift' e e.injective
  have he : P.which = (Format.prescribed d h P.count P.colors).which := rfl
  have hg : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N := hf
  have hc (i) : Nonempty (Cells.Domain P ↪ Fin (2 ^ M.width i)) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    apply (Nat.mul_le_mul_right_iff hr).mp
    exact (Cells.domain_size P hlabel (by omega) H.positions).trans (hroom i)
  let a : Cells.Address P M := fun i => (hc i).some
  let C := Cells.install hn he hg a hex.some
  -- 推导：记下中间结论 `hwW`：`w ≤ W`。
  have hwW : w ≤ W := by
    by_contra! hlt
    have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    exact hh.not_ge H.limits.bits
  have hM : M.budget F ≤ 2 ^ W * (100 + W) ^ Q :=
    hm.trans (Nat.mul_le_mul H.limits.bits (Nat.pow_le_pow_left (by omega) _))
  refine ⟨C.numberInOrder, dispatch fa M C.numberInOrder ?_⟩
  intro i
  obtain ⟨f, hf, he⟩ := C.handles H he hg a rfl hM i
  exact ⟨f, hf.mono (fit_window H.small H.cost hw), he⟩

-- 读法：要证明的命题是 `Diagonal.Resists F (Cheap F K q)`。这里调用 `resists_of_programmable`。
/-- 有一族对象可用很低的成本实现，但即使允许拟线性宏门，任何规模充分小的同时实现也无法实现整个族。

英文原文：A cheaply realizable family resists all sufficiently small
simultaneous implementations, even with quasilinear macro gates.
-/
theorem resists (F : Type) [Field F] [Finite F] (K q : ℕ) :
    Diagonal.Resists F (Cheap F K q) := by
  let _ := Fintype.ofFinite F
  exact resists_of_programmable (programmable_of_control (control F) K q)

-- 读法：要证明的命题是 `Tagged.Hard F`。使用 `hard_of_resists` 给出的结论。
theorem hard_of_descent {F : Type} [Field F] [Finite F] {K q : ℕ}
    (h : Diagonal.Descent F (Cheap F K q)) : Tagged.Hard F :=
  hard_of_resists (resists F K q) h

end OAI.LinearAlgebra.MatrixExponent.Processor
