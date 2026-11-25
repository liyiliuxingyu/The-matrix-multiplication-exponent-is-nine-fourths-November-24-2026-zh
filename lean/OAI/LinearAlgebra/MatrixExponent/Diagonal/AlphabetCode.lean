-- 本文件所属证明环节：给不同处理器和独立副本分配地址、切口、信道和广播资源，把虚拟连线送上实际网络，控制由固定模板带来的额外开销。
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Cuts
import OAI.LinearAlgebra.MatrixExponent.Spectral.Packets
import Mathlib.Data.Sigma.Order

section
/-!
# 一个数据包的两个组名的均匀性

**英文原文**

Uniformity of the two group names of a packet
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z] [DecidableEq Z]

-- 读法：`multiplicity (fun a => (e a).1) z * Fintype.card Z` 等于 `Fintype.card A`。这里调用 `Fintype.card_congr`。
/-- 采用乘积参数化，可精确确定每个标签对应的点数。

英文原文：A product parametrization makes the number of points per label exact.
-/
private theorem uniform (e : A ≃ Z × B) (z : Z) :
    multiplicity (fun a => (e a).1) z * Fintype.card Z = Fintype.card A := by
  have ht : multiplicity (fun a => (e a).1) z = Fintype.card B := by
    apply Fintype.card_congr
    exact {
      toFun := fun a => (e a.val).2
      invFun := fun b => ⟨e.symm (z, b), congrArg Prod.fst (e.apply_symm_apply (z, b))⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_eq.mpr (Prod.ext a.2.symm rfl))
      right_inv := by intro b; simp }
  rw [ht, Fintype.card_congr e, Fintype.card_prod, mul_comm]

variable {n r d : ℕ}


-- 读法：`multiplicity (fun a : Label n r => a i) g * r` 等于 `r ^ n`。
theorem label_uniform (i : Fin n) (g : Fin r) :
    multiplicity (fun a : Label n r => a i) g * r = r ^ n := by
  have H := uniform (Equiv.funSplitAt i (Fin r)) g
  change multiplicity (fun a : Label n r => a i) g * _ = _ at H
  simpa using H

-- 读法：在后续公式中，`Key` 是 `Fin n × Bool` 的缩写。
/-- 两个标签在每个坐标上各有一个可以独立变化的符号。

英文原文：Each of the two labels has one independently variable symbol per coordinate.
-/
abbrev Key (n : ℕ) := Fin n × Bool

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Template n r ≃ (Key n → Fin r)`。
def symbols (n r : ℕ) : Template n r ≃ (Key n → Fin r) where
  toFun p i := group p i.1 i.2
  invFun f := (fun i => f (i, false), fun i => f (i, true))
  left_inv _ := rfl
  right_inv _ := by funext ⟨i, b⟩; cases b <;> rfl

-- 读法：`multiplicity (fun p : Packet n r d => group p.1 i b) g * r` 等于 `Fintype.card (Packet n r d)`。
theorem group_uniform (i : Fin n) (b : Bool) (g : Fin r) :
    multiplicity (fun p : Packet n r d => group p.1 i b) g * r =
      Fintype.card (Packet n r d) := by
  let e := (symbols n r).trans (Equiv.funSplitAt (i, b) (Fin r))
  let t := (e.prodCongr (Equiv.refl (Fin d))).trans (Equiv.prodAssoc _ _ _)
  have H := uniform t g
  change multiplicity (fun p : Packet n r d => group p.1 i b) g * _ = _ at H
  simpa only [Fintype.card_fin] using H

-- 读法：要证明的命题是 `multiplicity (fun p : Packet n r d => (symbols n r p.1 i, symbols n r p.1 j)) (g, g') * r ^ 2 = Fintype.card (Packet n r d)`。
theorem pair_uniform (i j : Key n) (hne : j ≠ i) (g g' : Fin r) :
    multiplicity (fun p : Packet n r d => (symbols n r p.1 i, symbols n r p.1 j)) (g, g') * r ^ 2 =
      Fintype.card (Packet n r d) := by
  let e := (symbols n r).trans (Equiv.funSplitAt i (Fin r))
  let a := Equiv.funSplitAt (⟨j, hne⟩ : {u : Key n // u ≠ i}) (Fin r)
  let f := (e.trans ((Equiv.refl _).prodCongr a)).trans (Equiv.prodAssoc _ _ _).symm
  let t := (f.prodCongr (Equiv.refl (Fin d))).trans (Equiv.prodAssoc _ _ _)
  have H := uniform t (g, g')
  change multiplicity (fun p : Packet n r d => (symbols n r p.1 i, symbols n r p.1 j))
    (g, g') * _ = _ at H
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using H

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 过载分组的两种坐标分配

轻负载任务留在所属组，用标签的另一个坐标分配重负载任务。下述界同时适用于重新分配的任务，以及各轻组与重组之间的接触。

**英文原文**

Two coordinate assignments for overloaded groups

Keep light work at its group. Assign heavy work by a different
coordinate of its label. The bound below applies both to the reassigned
work and to each light group's contacts with heavy groups.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset

variable {n r d : ℕ}

-- 读法：`contact` 的取值由 `univ.filter (fun p => (∃ s, group p.1 i s ∈ H) ∧ (∃ s, group p.1 j s = g))` 给出。
/-- 数据包在切分坐标处接触一个重组，在工作单元坐标处接触一个指定的组。

英文原文：The packet touches a heavy group at the cut and a given group
at the worker coordinate.
-/
def contact (i j : Fin n) (H : Finset (Fin r)) (g : Fin r) : Finset (Packet n r d) :=
  univ.filter (fun p => (∃ s, group p.1 i s ∈ H) ∧ (∃ s, group p.1 j s = g))

-- 读法：`(univ.filter (fun p : Packet n r d => group p.1 i b = g ∧ group p.1 j c = e)).card * r ^ 2` 不超过 `Fintype.card (Packet n r d)`。按 `(j, c) = (i, b)` 成立与否分情况。
private theorem contact_pair (i j : Fin n) (g e : Fin r) (b c : Bool)
    (hne : i ≠ j ∨ g ≠ e) :
    (univ.filter (fun p : Packet n r d => group p.1 i b = g ∧ group p.1 j c = e)).card * r ^ 2 ≤
      Fintype.card (Packet n r d) := by
  by_cases hpair : (j, c) = (i, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    have hne' := hne.resolve_left (not_ne_iff.mpr rfl)
    have he (p : Packet n r d) : ¬ (group p.1 j c = g ∧ group p.1 j c = e) :=
      fun h => hne' (h.1.symm.trans h.2)
    simp [he]
  · have he := pair_uniform (d := d) (i, b) (j, c) hpair g e
    change multiplicity (fun p : Packet n r d => (group p.1 i b, group p.1 j c)) (g, e) * r ^ 2 = _ at he
    simpa [multiplicity, Fintype.card_subtype] using he.le

-- 读法：`(contact (d := d) i j H g).card * r ^ 2` 不超过 `4 * H.card * Fintype.card (Packet n r d)`。这里调用 `mem_biUnion.mpr`。
theorem contact_bound (i j : Fin n) (H : Finset (Fin r)) (g : Fin r) (h : i ≠ j ∨ g ∉ H) :
    (contact (d := d) i j H g).card * r ^ 2 ≤ 4 * H.card * Fintype.card (Packet n r d) := by
  let S := H ×ˢ (univ : Finset (Bool × Bool))
  let T (a : Fin r × Bool × Bool) := univ.filter (fun p : Packet n r d =>
    group p.1 i a.2.1 = a.1 ∧ group p.1 j a.2.2 = g)
  have sub : contact (d := d) i j H g ⊆ S.biUnion T := by
    intro p hp
    obtain ⟨_, ⟨b, hb⟩, ⟨c, hc⟩⟩ := mem_filter.mp hp
    exact mem_biUnion.mpr ⟨(group p.1 i b, b, c), mem_product.mpr ⟨hb, mem_univ _⟩,
      mem_filter.mpr ⟨mem_univ _, rfl, hc⟩⟩
  calc
    _ ≤ (∑ i ∈ S, (T i).card) * r ^ 2 :=
      Nat.mul_le_mul_right _ ((card_le_card sub).trans card_biUnion_le)
    _ = ∑ i ∈ S, (T i).card * r ^ 2 := sum_mul ..
    _ ≤ ∑ _ ∈ S, Fintype.card (Packet n r d) := sum_le_sum (fun u hu => by
      apply contact_pair
      rcases h with h | h
      · exact .inl h
      · exact .inr (fun he => h (he ▸ (mem_product.mp hu).1)))
    _ = _ := by simp [S, mul_comm]

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 用两个固定的工作处理器池给出通信量上界

轻负载归属组能够承担其轻负载配对的跨界比特。涉及重组的数据包整包求值，按第二个坐标分配工作处理器。每个此类数据包在任意一个处理器上至多占用两个完整的槽位块。

**英文原文**

Bounding communication with two fixed pools of workers

A light home can afford the crossing bits of its light pairs. Packets
touching a heavy group are evaluated whole, assigning workers by a
second coordinate. Each such packet costs at most two full blocks of
slots at any one worker.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset

variable {n r d : ℕ}

-- 读法：`charge` 的取值由 `∑ p, ((if group p.1 i false = g then q p else 0) + (if group p.1 i true = g then q p else 0))` 给出。
/-- 两次关联均须计数，即使它们属于同一组。

英文原文：Count both incidences, even if they belong to the same group.
-/
def charge (i : Fin n) (q : Packet n r d → ℕ) (g : Fin r) :=
  ∑ p, ((if group p.1 i false = g then q p else 0) + (if group p.1 i true = g then q p else 0))

-- 读法：结论为 `∑ g, charge i q g = 2 * ∑ p, q p`。
theorem charge_total (i : Fin n) (q : Packet n r d → ℕ) :
    ∑ g, charge i q g = 2 * ∑ p, q p := by
  unfold charge
  rw [sum_comm]
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, two_mul]

-- 读法：`heavy` 的取值由 `univ.filter (fun g => N < T * charge i q g)` 给出。
def heavy (T N : ℕ) (i : Fin n) (q : Packet n r d → ℕ) :=
  univ.filter (fun g => N < T * charge i q g)

-- 读法：`(heavy T N i q).card * L` 不超过 `4 * T * C * r`。
private theorem heavy_bound {C L W T N : ℕ} (hN : 0 < N)
    (hw : Fintype.card (Packet n r d) * W ≤ C * r * N) (i : Fin n) (q : Packet n r d → ℕ)
    (hs : L * ∑ p, q p ≤ 2 * Fintype.card (Packet n r d) * W) :
    (heavy T N i q).card * L ≤ 4 * T * C * r := by
  let H := heavy T N i q
  have hb : H.card * N ≤ T * ∑ g, charge i q g := by
    calc
      _ = ∑ _ ∈ H, N := by simp
      _ ≤ ∑ g ∈ H, T * charge i q g := sum_le_sum (fun g hg => (mem_filter.mp hg).2.le)
      _ ≤ ∑ g, T * charge i q g := sum_le_sum_of_subset (subset_univ _)
      _ = _ := (mul_sum ..).symm
  rw [charge_total] at hb
  apply (Nat.mul_le_mul_right_iff hN).mp
  calc
    _ = (H.card * N) * L := by unfold H; ring
    _ ≤ (T * (2*∑ p, q p)) * L := Nat.mul_le_mul_right _ hb
    _ = (2 * T) * (L * ∑ p, q p) := by ring
    _ ≤ (2 * T) * (2 * Fintype.card (Packet n r d) * W) := Nat.mul_le_mul_left _ hs
    _ = 4 * T * (Fintype.card (Packet n r d) * W) := by ring
    _ ≤ 4 * T * (C * r * N) := Nat.mul_le_mul_left _ hw
    _ = _ := by ring

-- 读法：`T * (2 * W * (contact (d := d) i j (heavy T N i q) g).card)` 不超过 `N`。这里调用 `Nat.mul_le_mul_right_iff`。
/-- 对每个被重新分配的工作单元（`i ≠ j`）的全部负载给出上界；对任意轻归属点（`g ∉ H`），则估计其发送给重伙伴的负载。

英文原文：Bound the entire workload of each reassigned worker (`i ≠ j`)
or the work sent to heavy partners by any light home (`g ∉ H`).
-/
theorem workload {C L W T N : ℕ} (hN : 0 < N) (hL : 0 < L)
    (hsave : 32 * T ^ 2 * C ^ 2 ≤ L) (hw : Fintype.card (Packet n r d) * W ≤ C * r * N)
    (i j : Fin n) (q : Packet n r d → ℕ) (hs : L * ∑ p, q p ≤ 2 * Fintype.card (Packet n r d) * W)
    (g : Fin r) (hg : i ≠ j ∨ g ∉ heavy T N i q) :
    T * (2 * W * (contact (d := d) i j (heavy T N i q) g).card) ≤ N := by
  let H := heavy T N i q
  let K := (contact (d := d) i j H g).card
  have hH : H.card * L ≤ 4 * T * C * r := heavy_bound hN hw i q hs
  have hK : K * r ^ 2 ≤ 4 * H.card * Fintype.card (Packet n r d) := contact_bound i j H g hg
  have hr : 0 < r := g.isLt |> Nat.zero_lt_of_lt
  apply (Nat.mul_le_mul_right_iff (by positivity : 0 < L * r ^ 2)).mp
  change (T * (2 * W * K)) * (L * r ^ 2) ≤ N * (L * r ^ 2)
  calc
    _ = (2 * T * W * L) * (K * r ^ 2) := by ring
    _ ≤ (2 * T * W * L) * (4 * H.card * Fintype.card (Packet n r d)) := Nat.mul_le_mul_left _ hK
    _ = 8 * T * (H.card * L) * (Fintype.card (Packet n r d) * W) := by ring
    _ ≤ 8 * T * (4 * T * C * r) * (C * r * N) := by gcongr
    _ = 32 * T ^ 2 * C ^ 2 * (N * r ^ 2) := by ring
    _ ≤ L * (N * r ^ 2) := Nat.mul_le_mul_right _ hsave
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# 为每个虚拟比特分配两个处理器

由辅助坐标索引的两个工作处理器池负责重组，使处理器位置独立于批次的内部接线。自环链路可以在本地处理。

**英文原文**

Assigning each virtual bit to two processors

Two pools indexed by the auxiliary coordinate handle the heavy groups.
This makes the locations of the workers independent of the internal
wiring of the batch. Self-links may remain private.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {n r d h : ℕ}

-- 读法：归纳构造子包括 `home`、`station`、`packet`。
inductive Worker (r : ℕ) where
  | home (g : Fin r)
  | station (g : Fin r)
  | packet (g : Fin r)
  deriving DecidableEq, Fintype

-- 读法：结构的字段包括 `cut`、`aux`、`groups`、`q`。
structure Plan (n r d : ℕ) where
  cut : Fin n
  aux : Fin n
  groups : Finset (Fin r)
  q : Packet n r d → ℕ

namespace Plan
variable (π : Plan n r d)

-- 读法：当 `x π.cut ∈ π.groups` 成立时取 `.station (x π.aux)`，否则取 `.home (x π.cut)`。
def base (x : Label n r) : Worker r :=
  if x π.cut ∈ π.groups then .station (x π.aux) else .home (x π.cut)

-- 读法：`marked` 的结果类型为 `Prop`。
def marked (p : Packet n r d) : Prop := ∃ s, group p.1 π.cut s ∈ π.groups
  deriving Decidable

-- 读法：在后续公式中，`Message` 是 `{ _m : Bool × Cube n × Fin h // π.marked p } ⊕ { _m : Fin (π.q p) // ¬π.marked p }` 的缩写。
/-- 重数据包共用两块槽位；轻数据包共用选择器以及所选切分处的连线比特。

英文原文：Heavy packets share both blocks of slots. Light packets share
the selector and the wire bits at the chosen cut.
-/
abbrev Message (h : ℕ) (p : Packet n r d) :=
  { _m : Bool × Cube n × Fin h // π.marked p } ⊕ { _m : Fin (π.q p) // ¬π.marked p }

-- 读法：逐一匹配以下输入模式：`.inl m`、`.inr _`。
def sender (p : Packet n r d) : π.Message h p → Worker r
  | .inl m => π.base (corner p.1 (if m.1.1 then Cube.flip Finset.univ m.1.2.1 else m.1.2.1))
  | .inr _ => .home (group p.1 π.cut false)

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr _`。
def receiver (p : Packet n r d) : π.Message h p → Worker r
  | .inl _ => .packet (group p.1 π.aux false)
  | .inr _ => .home (group p.1 π.cut true)

-- 读法：`slotsAt` 的取值由 `Fintype.card {m : π.Message h p // π.sender p m = u ∨ π.receiver p m = u}` 给出。
def slotsAt (h : ℕ) (u : Worker r) (p : Packet n r d) :=
  Fintype.card {m : π.Message h p // π.sender p m = u ∨ π.receiver p m = u}

-- 读法：`eligible` 的结果类型为 `Finset (Packet n r d)`。
def eligible (u : Worker r) : Finset (Packet n r d) :=
  match u with
  | .home g => if g ∈ π.groups then ∅ else contact π.cut π.cut π.groups g
  | .station g | .packet g => contact π.cut π.aux π.groups g

-- 读法：`p` 属于 `π.eligible (π.base (corner p.1 x))`。这里调用 `Finset.mem_filter.mpr`。
private theorem base_mem (p : Packet n r d) (hm : π.marked p) (x : Cube n) :
    p ∈ π.eligible (π.base (corner p.1 x)) := by
  unfold base
  split_ifs with h
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨x π.aux, rfl⟩⟩
  · simp only [eligible, h, ite_false]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨x π.cut, rfl⟩⟩

-- 读法：`p` 属于 `π.eligible (.packet (group p.1 π.aux false))`。使用 `Finset.mem_filter.mpr` 给出的结论。
private theorem receiver_mem (p : Packet n r d) (hm : π.marked p) :
    p ∈ π.eligible (.packet (group p.1 π.aux false)) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨false, rfl⟩⟩

-- 读法：`light` 的结果类型为 `Worker r → ℕ`。
private def light (p : Packet n r d) : Worker r → ℕ
  | .home g => if g ∈ π.groups then 0 else
      (if group p.1 π.cut false = g then π.q p else 0) +
      (if group p.1 π.cut true = g then π.q p else 0)
  | _ => 0

-- 读法：`π.q p` 不超过 `π.light p (.home (group p.1 π.cut b))`。
private theorem light_le (p : Packet n r d) (hm : ¬π.marked p) (b : Bool) :
    π.q p ≤ π.light p (.home (group p.1 π.cut b)) := by
  have he : group p.1 π.cut b ∉ π.groups := fun h => hm ⟨b, h⟩
  simp only [light, he, ite_false]
  cases b <;> simp

-- 读法：`π.slotsAt h u p` 不超过 `π.light p u + if p ∈ π.eligible u then 2 * (Fintype.card (Cube n) * h) else 0`。按 `π.slotsAt h u p = 0` 成立与否分情况。
private theorem slotsAt_le (u : Worker r) (p : Packet n r d) :
    π.slotsAt h u p ≤ π.light p u +
      if p ∈ π.eligible u then 2 * (Fintype.card (Cube n) * h) else 0 := by
  classical
  by_cases hz : π.slotsAt h u p = 0
  · rw [hz]; exact Nat.zero_le _
  have hc : π.slotsAt h u p ≤ Fintype.card (π.Message h p) := Fintype.card_subtype_le _
  obtain ⟨⟨m, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
  rcases m with m|m
  · have he : p ∈ π.eligible u := by
      rcases hs with rfl | rfl
      · exact π.base_mem p m.2 _
      · exact π.receiver_mem p m.2
    rw [ite_eq_left he]
    refine hc.trans (le_trans ?_ (Nat.le_add_left _ _))
    simp [Message, m.2]
  -- 推导：记下中间结论 `he`：`π.q p ≤ π.light p u`。
  · have he : π.q p ≤ π.light p u := by
      rcases hs with rfl | rfl
      · exact π.light_le p m.2 false
      · exact π.light_le p m.2 true
    refine hc.trans (le_trans ?_ (he.trans (Nat.le_add_right _ _)))
    simp [Message, m.2]

-- 读法：结论为 `T * ∑ p, π.slotsAt h u p ≤ 2 * N`。对 `u` 分类讨论。
/-- 所有数据包的端点预算，包含每个填充位置。

英文原文：The endpoint budget for all packets, including every padded position.
-/
theorem capacity {C L T N : ℕ} (hN : 0 < N) (hL : 0 < L) (hsave : 32 * T ^ 2 * C ^ 2 ≤ L)
    (hw : Fintype.card (Position n r d h) ≤ C * r * N) (hne : π.cut ≠ π.aux)
    (hH : π.groups = heavy T N π.cut π.q)
    (hs : L * ∑ p, π.q p ≤ 2 * Fintype.card (Position n r d h)) (u : Worker r) :
    T * ∑ p, π.slotsAt h u p ≤ 2 * N := by
  let W := Fintype.card (Cube n) * h
  have size : Fintype.card (Position n r d h) = Fintype.card (Packet n r d) * W := by
    simp only [Position, Fintype.card_prod, Fintype.card_fin, W]
  rw [size] at hw
  rw [size, ← mul_assoc] at hs
  -- 推导：记下中间结论 `hl`：`T * ∑ p, π.light p u ≤ N`。
  have hl : T * ∑ p, π.light p u ≤ N := by
    cases u with
    | station g | packet g => simp [light]
    | home g =>
      by_cases hg : g ∈ π.groups
      · simp [light, hg]
      · simp only [light, hg, ite_false]
        change T * charge π.cut π.q g ≤ N
        simpa only [hH, heavy, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hg
  have he : T * (2 * W * (π.eligible u).card) ≤ N := by
    cases u with
    | station g | packet g =>
      simp only [eligible, hH]
      exact workload hN hL hsave hw _ _ _ hs _ (.inl hne)
    | home g =>
      simp only [eligible, hH]
      split_ifs with hg
      · simp
      · exact workload hN hL hsave hw _ _ _ hs _ (.inr hg)
  calc
    _ ≤ T * ∑ p, (π.light p u + if p ∈ π.eligible u then 2 * W else 0) :=
      Nat.mul_le_mul_left T (Finset.sum_le_sum (fun p _ => π.slotsAt_le u p))
    _ = T * (∑ p, π.light p u) + T * (2 * W * (π.eligible u).card) := by
      simp [Finset.sum_add_distrib, mul_add, mul_comm]
    _ ≤ _ := by omega

end Plan
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 对图式的独立副本作自适应数据包展开

**英文原文**

Adaptive packet expansion for independent copies of a diagram
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical

variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b} {n r h B : ℕ}
variable (L : Layout G n r h)

-- 读法：`batchLoad` 的取值由 `L.load (x (finProdFinEquiv.symm p.2).1) (p.1, (finProdFinEquiv.symm p.2).2)` 给出。
/-- 保留立方体模板，并合并批次索引与重复索引。

英文原文：Keep the cube template and combine the batch and repetition indices.
-/
def batchLoad (x : Fin B → G.End → Bool) (p : Packet n r (B * L.d)) : Block n h :=
  L.load (x (finProdFinEquiv.symm p.2).1) (p.1, (finProdFinEquiv.symm p.2).2)

-- 读法：`(L.batchLoad (B := B))` 是单射。用函数外延性比较等号两侧在 `j` 处的取值。
theorem batchLoad_injective : Function.Injective (L.batchLoad (B := B)) := by
  intro x y he
  funext j
  apply L.load_injective
  funext p
  simpa only [batchLoad, Equiv.symm_apply_apply] using
    congrFun he (p.1, finProdFinEquiv (j, p.2))

-- 读法：这里调用 `Fintype.prod_sum`。
/-- 所有副本可以共用一个根据全部选择器确定的坐标。站点比特与接合点比特各自独立，直到对数据包求和才恢复二者的相等关系。

英文原文：All copies may share a single coordinate choice based on all selectors.
Station and junction bits remain separate until the packet sum restores their
equality.
-/
theorem eval_batch (A : Expansion F n h) (x : Fin B → Val a) (y : Fin B → Val b)
    (cut : (Packet n r (B * L.d) → A.I) → Fin n)
    (split : (Packet n r (B * L.d) → A.I) → Packet n r (B * L.d) → Bool) :
    ∏ j, G.eval (x j) (y j) =
      ∑ u : Fin B → G.End → Bool, ∑ v : Fin B → G.End → Bool,
        (∏ j, ∏ i : G.V, G.normalized.vertex (x j) (y j) (u j) (.inl i)) *
        (∏ j, ∏ i : G.Joint, G.normalized.vertex (x j) (y j) (v j) (.inr i)) *
        ∑ s, ∑ z : A.Wires s (cut s) (split s), ∏ p,
          A.value (s p) (cut s) (L.batchLoad u p) (L.batchLoad v p) (split s p) (z p) := by
  simp only [A.adaptive, L.batchLoad_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.prod_mul_distrib]
  simp_rw [L.eval A, A.full_product, L.load_injective.eq_iff, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Fintype.prod_sum _

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# 沿一个立方体坐标切开一个数据包

将供给边分成跨界边与两组内部边。固定跨界比特后，两侧分别独立收缩。每条供给边只在一个坐标上计费。

**英文原文**

Cutting a packet across one cube coordinate

Partition the supply edges into crossing edges and two sets of internal
edges. Fixing the crossing bits leaves independent contractions on the
two sides. Each supply edge is charged at exactly one coordinate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Classical Spectral
variable {F J : Type} [Field F] [Fintype J]

namespace Cut

-- 读法：在后续公式中，`Shared` 是 `{e // κ e = none}` 的缩写。
private abbrev Shared (κ : J → Option Bool) := {e // κ e = none}
-- 读法：在后续公式中，`Own` 是 `{e // κ e = some b}` 的缩写。
private abbrev Own (κ : J → Option Bool) (b : Bool) := {e // κ e = some b}

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Shared κ → Bool) × (Own κ false → Bool) × (Own κ true → Bool) ≃ (J → Bool)`。
private def combine (κ : J → Option Bool) :
    (Shared κ → Bool) × (Own κ false → Bool) × (Own κ true → Bool) ≃ (J → Bool) where
  toFun u e := if h : κ e = none then u.1 ⟨e, h⟩ else
    if g : κ e = some false then u.2.1 ⟨e, g⟩ else u.2.2 ⟨e, by
      cases he : κ e with
      | none => contradiction
      | some b => cases b <;> simp_all⟩
  invFun p := (fun e => p e, fun e => p e, fun e => p e)
  left_inv u := by
    ext ⟨e, he⟩ <;> simp [he]
  right_inv p := by funext e; simp

-- 读法：`patch` 的取值由 `if h : κ e = none then u ⟨e, h⟩ else if h : κ e = some b then v ⟨e, h⟩ else false` 给出。
private def patch (κ : J → Option Bool) (b : Bool) (u : Shared κ → Bool)
    (v : Own κ b → Bool) (e : J) : Bool :=
  if h : κ e = none then u ⟨e, h⟩ else if h : κ e = some b then v ⟨e, h⟩ else false

-- 读法：`part` 的取值由 `∑ v, φ b (patch κ b (u ∘ Fintype.equivFin (Shared κ)) v)` 给出。
def part (κ : J → Option Bool) (φ : Bool → (J → Bool) → F) (b : Bool)
    (u : Fin (Fintype.card (Shared κ)) → Bool) : F :=
  ∑ v, φ b (patch κ b (u ∘ Fintype.equivFin (Shared κ)) v)

-- 读法：`(∑ u, φ false u * φ true u)` 等于 `∑ z, part κ φ false z * part κ φ true z`。这里调用 `Finset.sum_congr`。
theorem split (κ : J → Option Bool) (φ : Bool → (J → Bool) → F)
    (h : ∀ b u v, (∀ e, κ e = none ∨ κ e = some b → u e = v e) → φ b u = φ b v) :
    (∑ u, φ false u * φ true u) = ∑ z, part κ φ false z * part κ φ true z := by
  have hf (u v w) : φ false (combine κ (u, v, w)) = φ false (patch κ false u v) :=
    h _ _ _ (fun e he => by rcases he with he | he <;> simp [combine, patch, he])
  have ht (u v w) : φ true (combine κ (u, v, w)) = φ true (patch κ true u w) :=
    h _ _ _ (fun e he => by rcases he with he | he <;> simp [combine, patch, he])
  rw [← (combine κ).sum_comp, Fintype.sum_prod_type]
  let E := Equiv.arrowCongr (Fintype.equivFin (Shared κ)).symm (Equiv.refl Bool)
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type]
  simp only [hf, ht, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

end Cut

variable {n h : ℕ}

-- 读法：当 `p.2 = i` 成立时取 `none`，否则取 `some (p.1 i)`。
/-- 将每个供给比特计入其对应边所改变的唯一坐标。

英文原文：Charge each supply bit to the unique coordinate changed by its edge.
-/
private def region (p : Cube n × Fin n) (i : Fin n) : Option Bool :=
  if p.2 = i then none else some (p.1 i)

-- 读法：结论为 `∑ i, Fintype.card {e // region (t e) i = none} = Fintype.card J`。
private theorem region_card (t : J → Cube n × Fin n) :
    ∑ i, Fintype.card {e // region (t e) i = none} = Fintype.card J := by
  simp [region, Fintype.card_subtype, Finset.sum_card_fiberwise_eq_card_filter]

-- 读法：`half` 的取值由 `∏ v, if v i = b then g v else 1` 给出。
private def half (i : Fin n) (g : Cube n → F) (b : Bool) : F :=
  ∏ v, if v i = b then g v else 1

-- 读法：`(∏ v, g v)` 等于 `half i g false * half i g true`。这里调用 `Finset.prod_congr`。
private theorem prod_half (i : Fin n) (g : Cube n → F) :
    (∏ v, g v) = half i g false * half i g true := by
  rw [half, half, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  cases v i <;> simp

-- 读法：`half i g b` 等于 `half i g' b`。这里调用 `Finset.prod_congr`。
private theorem half_congr {i : Fin n} {g g' : Cube n → F} {b : Bool}
    (he : ∀ v, v i = b → g v = g' v) : half i g b = half i g' b := by
  apply Finset.prod_congr rfl
  intro v _
  split
  · apply he; assumption
  · rfl

-- 读法：存在 `E : Expansion F n h`，`Fintype.card E.I` 等于 `Fintype.card I ∧ ∀ s, ∃ t : I, ∑ i, E.cross s i = Fintype.card (A t)`。
theorem expand_packet {I : Type} {A : I → Type} [Fintype I] [∀ s, Fintype (A s)]
    (edges : (s : I) → A s → Cube n × Fin n)
    (packet : Spectral.Packet F (fun p : Cube n × Fin h => (p.1, Cube.flip Finset.univ p.1))
      (fun s e => ((edges s e).1, Cube.flip {(edges s e).2} (edges s e).1))) :
    ∃ E : Expansion F n h, Fintype.card E.I = Fintype.card I ∧
      ∀ s, ∃ t : I, ∑ i, E.cross s i = Fintype.card (A t) := by
  obtain ⟨f, hf, full⟩ := packet
  let κ (s : I) (i : Fin n) (e : A s) := region (edges s e) i
  let φ (s : I) (i : Fin n) (x y : Block n h) (b : Bool) (u : A s → Bool) :=
    half i (fun v => f s v x y u) b
  let E : Expansion F n h := {
    I := I
    weight := fun s x y => ∑ u, ∏ v, f s v x y u
    cross := fun s i => Fintype.card {e // κ s i e = none}
    side := fun s i b x y z => Cut.part (κ s i) (φ s i x y) b z
    full := fun x y => (full x y).symm
    split := by
      intro s i x y
      simp_rw [prod_half i]
      apply Cut.split (κ s i) (φ s i x y)
      intro b u u' he
      apply half_congr
      intro v hv
      refine hf _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun e hh => he e ?_)
      by_cases hc : (edges s e).2 = i
      · exact .inl (by simp [κ, region, hc])
      · right
        rcases hh with h₁ | h₂
        · change (edges s e).1 = v at h₁
          simp [κ, region, hc, h₁, hv]
        · have h₃ := (congrFun h₂ i).trans hv
          simpa [κ, region, Cube.flip, hc, Ne.symm hc] using h₃
    depends := by
      intro s i b x x' y y' z hx hy
      apply Finset.sum_congr rfl
      intro u _
      apply half_congr
      intro v hv
      apply hf
      · intro e he
        exact hx e ((congrFun he i).trans hv)
      · intro e he
        apply hy
        have h₁ := (congrFun he i).trans hv
        simp [Cube.flip] at h₁
        grind
      · intro e _; rfl
  }
  exact ⟨E, rfl, fun s => ⟨s, region_card (edges s)⟩⟩

-- 读法：存在 `n ≥ n₀`，存在 `h : ℕ`，存在 `E : Expansion F n h`，`0` 小于 `h ∧ L * Nat.clog 2 (Fintype.card E.I) ≤ h ∧ ∀ s, L * ∑ i, E.cross s i < n * Fintype.card (Cube n) * h`。这里调用 `Nat.le_add_right`。
/-- 存在维数任意大且具有数据包展开的立方体。相对于所需的比特数，平均跨越成本与选择器长度都可以任意小。

英文原文：A cube of arbitrarily large dimension with a packet expansion.
The average crossing cost and the selector length can both be made
arbitrarily small compared with the number of demanded bits.
-/
theorem expansion (F : Type) [Field F] (L n₀ : ℕ) (hL : 0 < L) :
    ∃ n ≥ n₀, ∃ h : ℕ, ∃ E : Expansion F n h, 0 < h ∧
      L * Nat.clog 2 (Fintype.card E.I) ≤ h ∧
      ∀ s, L * ∑ i, E.cross s i < n * Fintype.card (Cube n) * h := by
  obtain ⟨n, hn, b, C, H, hb, hc, hp⟩ := Spectral.Tensor.cube_packets F L n₀ hL
  let z := L * Nat.clog 2 (Fintype.card (Fin C × ↥H)) + 1
  have hz : 0 < z := Nat.zero_lt_succ _
  let edges (s : Fin C × ↥H) (e : Σ j : Cube n × Fin n, Fin (s.2.val j * z)) := e.1
  obtain ⟨E, he, hcost⟩ := expand_packet edges (hp z hz)
  refine ⟨n, hn, b * z, E, Nat.mul_pos hb hz, ?_, ?_⟩
  · rw [he]
    exact (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left z hb)
  · intro s
    obtain ⟨t, ht⟩ := hcost s
    rw [ht, Fintype.card_sigma]
    simp only [Fintype.card_fin, ← Finset.sum_mul, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (hc t.2.val t.2.property) hz

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 精确数据包展开式的统一通信方案

**英文原文**

Uniform communication plans for exact packet expansions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {F : Type} [Field F] {n h d r : ℕ}

-- 读法：存在 `i`，对每个 `j`，`c i < c j`、`c i = c j ∧ i ≤ j` 至少有一项成立。
private theorem exists_first (hn : 2 ≤ n) (c : Fin n → ℕ) :
    ∃ i, ∀ j, c i < c j ∨ c i = c j ∧ i ≤ j := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun j => toLex (c j, j))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  exact ⟨i, fun j => Prod.Lex.toLex_le_toLex.mp (hi j (Finset.mem_univ _))⟩

-- 读法：`first` 的取值由 `(exists_first hn c).choose` 给出。
def first (hn : 2 ≤ n) (c : Fin n → ℕ) : Fin n := (exists_first hn c).choose

-- 读法：`c (first hn c) < c j`、`c (first hn c) = c j ∧ first hn c ≤ j` 至少有一项成立。使用 `exists_first` 给出的结论。
theorem first_spec (hn : 2 ≤ n) (c : Fin n → ℕ) (j : Fin n) :
    c (first hn c) < c j ∨ c (first hn c) = c j ∧ first hn c ≤ j :=
  (exists_first hn c).choose_spec j

-- 读法：`other` 的结果类型为 `Fin n`。
def other (hn : 2 ≤ n) (i : Fin n) : Fin n :=
  if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

-- 读法：`i` 不等于 `other hn i`。
theorem other_ne (hn : 2 ≤ n) (i : Fin n) : i ≠ other hn i := by
  unfold other
  split_ifs <;> intro h <;> have := congrArg Fin.val h <;> simp_all

namespace Expansion

variable (A : Expansion F n h)

-- 读法：`plan` 的结果类型为 `Plan n r d`。
def plan (hn : 2 ≤ n) (N : ℕ) (s : Packet n r d → A.I) : Plan n r d :=
  let i := first hn (fun j => ∑ p, A.cross (s p) j)
  let q := fun p => A.cross (s p) i + Nat.clog 2 (Fintype.card A.I)
  ⟨i, other hn i, heavy 256 N i q, q⟩

-- 读法：`splitPacket` 的取值由 `decide (¬(A.plan hn N s).marked p)` 给出。
def splitPacket (hn : 2 ≤ n) (N : ℕ) (s : Packet n r d → A.I) (p : Packet n r d) : Bool :=
  decide (¬(A.plan hn N s).marked p)

-- 读法：结论为 `128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N`。这里调用 `first_spec`。
private theorem plan_bound (hn : 2 ≤ n) (N C L : ℕ) (s : Packet n r d → A.I)
    (hN : 0 < N) (hL : 0 < L) (hsave : 32 * 256 ^ 2 * C ^ 2 ≤ L)
    (hw : Fintype.card (Position n r d h) ≤ C * r * N)
    (hc : ∀ s, L * ∑ i, A.cross s i ≤ n * Fintype.card (Cube n) * h)
    (hl : L * Nat.clog 2 (Fintype.card A.I) ≤ h) (u : Worker r) :
    128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N := by
  let π := A.plan hn N s
  obtain ⟨i, hi, hm⟩ := A.coordinate (by omega) L hc hl s
  have he : ∑ p, A.cross (s p) π.cut = ∑ p, A.cross (s p) i := by
    refine le_antisymm ?_ (hi _)
    exact (first_spec hn (fun j => ∑ p, A.cross (s p) j) i).elim
      (fun h => h.le) (fun h => h.1.le)
  -- 推导：记下中间结论 `hb`：`L * ∑ p, π.q p ≤ 2 * Fintype.card (Position n r d h)`。
  have hb : L * ∑ p, π.q p ≤ 2 * Fintype.card (Position n r d h) := by
    change L * (∑ p, (A.cross (s p) π.cut + Nat.clog 2 (Fintype.card A.I))) ≤ _
    rw [Finset.sum_add_distrib, he, ← Finset.sum_add_distrib]
    simpa only [Position, Fintype.card_prod, Fintype.card_fin, mul_assoc] using hm
  have := π.capacity hN hL hsave hw (other_ne hn π.cut) rfl hb u
  change 128 * ∑ p, π.slotsAt h u p ≤ N
  omega

end Expansion

-- 读法：结论为 `∃ n, ∃ hn : 2 ≤ n, ∃ h, ∃ A : Expansion F n h, 0 < h ∧ ∀ (r d N : ℕ), 0 < N → Fintype.card (Position n r d h) ≤ C * r * N → ∀ (s : Packet n r d → A.I) (u : Worker r), 128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N`。
/-- 同一个精确的立方体恒等式适用于任意问题规模与任意选择器元组。数据包连接对每个工作单元消耗的虚拟比特预算至多为一半，余下空间供字面量引脚使用。

英文原文：One exact cube identity works for every problem size and every tuple
of selectors. The packet links consume at most half of each worker's
virtual bit budget, leaving room for the literal pins.
-/
theorem bounded_expansion (F : Type) [Field F] (C : ℕ) :
    ∃ n, ∃ hn : 2 ≤ n, ∃ h, ∃ A : Expansion F n h, 0 < h ∧
      ∀ (r d N : ℕ), 0 < N → Fintype.card (Position n r d h) ≤ C * r * N →
        ∀ (s : Packet n r d → A.I) (u : Worker r),
          128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N := by
  let L := 32 * 256 ^ 2 * C ^ 2 + 1
  have hl : 0 < L := Nat.zero_lt_succ _
  obtain ⟨n, hn, h, A, hh, hs, hc⟩ := expansion F L 2 hl
  exact ⟨n, hn, h, A, hh, fun _ _ N hN hw s u =>
    A.plan_bound hn N C L s hN hl (Nat.le_succ _) hw (fun t => (hc t).le) hs u⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 自适应方案的公开报告

同一类别中的数据包具有相同的一对归属组和同一数据包工作处理器。按类别报告各选择器的数量。报告给出所有候选切割的成本，因此即使类别划分本身依赖候选切割，也能检验所选切割是否按规则取得最小值。

**英文原文**

A public report for the adaptive plan

Packets in one class have the same pair of homes and the same packet
worker. Report selector counts by class. A report gives the costs at
all candidate cuts, so one can check the minimizing rule even though
the partition into classes itself depends on the proposed cut.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Finset Classical
variable {F : Type} [Field F] {n h d r : ℕ}

-- 读法：在后续公式中，`Class` 是 `Fin r × Fin r × Fin r` 的缩写。
abbrev Class (r : ℕ) := Fin r × Fin r × Fin r

-- 读法：`packetClass` 的取值由 `(group p.1 i false, group p.1 i true, group p.1 (other hn i) false)` 给出。
def packetClass (hn : 2 ≤ n) (i : Fin n) (p : Packet n r d) : Class r :=
  (group p.1 i false, group p.1 i true, group p.1 (other hn i) false)

namespace Expansion

variable (A : Expansion F n h) (hn : 2 ≤ n)

-- 读法：在后续公式中，`Report` 是 `Fin n × (Class r × A.I → Fin (Fintype.card (Packet n r d) + 1))` 的缩写。
/-- 单个类别所报告的数量不超过数据包总数。

英文原文：A class can report at most the total number of packets.
-/
abbrev Report (r d : ℕ) :=
  Fin n × (Class r × A.I → Fin (Fintype.card (Packet n r d) + 1))

-- 读法：`counts` 的取值由 `⟨multiplicity (fun p => (packetClass hn i p, s p)) z, Nat.lt_succ_of_le (Fintype.card_subtype_le _)⟩` 给出。
def counts (s : Packet n r d → A.I) (i : Fin n)
    (z : Class r × A.I) : Fin (Fintype.card (Packet n r d) + 1) :=
  ⟨multiplicity (fun p => (packetClass hn i p, s p)) z,
    Nat.lt_succ_of_le (Fintype.card_subtype_le _)⟩

-- 读法：`total` 的取值由 `∑ z, (R.2 z).val * f z.1 z.2` 给出。
def total (R : A.Report r d) (f : Class r → A.I → ℕ) :=
  ∑ z, (R.2 z).val * f z.1 z.2

-- 读法：`A.total (i, A.counts hn s i) f` 等于 `∑ p, f (packetClass hn i p) (s p)`。
theorem total_counts (s : Packet n r d → A.I) (i : Fin n) (f : Class r → A.I → ℕ) :
    A.total (i, A.counts hn s i) f = ∑ p, f (packetClass hn i p) (s p) := by
  simp only [total, counts, multiplicity, Fintype.card_subtype]
  have he (p : Packet n r d → Prop) [DecidablePred p] : (univ.filter p).card = ∑ i, if p i then 1 else 0 := by
    simp

  simp_rw [he, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]

-- 读法：`report` 的取值由 `let i := first hn (fun j => ∑ p, A.cross (s p) j) (i, A.counts hn s i)` 给出。
def report (s : Packet n r d → A.I) : A.Report r d :=
  let i := first hn (fun j => ∑ p, A.cross (s p) j)
  (i, A.counts hn s i)

-- 读法：`checks` 表示以下条件：`R.1 = first hn (fun j => A.total R (fun _ t => A.cross t j))` 与 `∀ c, R.2 c = A.counts hn s R.1 c` 同时成立。
def checks (R : A.Report r d) (s : Packet n r d → A.I) : Prop :=
  R.1 = first hn (fun j => A.total R (fun _ t => A.cross t j)) ∧
    ∀ c, R.2 c = A.counts hn s R.1 c

-- 读法：`A.checks hn R s` 与 `R = A.report hn s` 等价。
/-- 选择器的每组赋值都恰好对应一份有效报告。

英文原文：Every selector assignment has exactly one valid report.
-/
theorem checks_iff (R : A.Report r d) (s : Packet n r d → A.I) :
    A.checks hn R s ↔ R = A.report hn s := by
  constructor
  · rcases R with ⟨i, N⟩
    rintro ⟨hi, hs⟩
    have he : N = A.counts hn s i := funext hs
    subst N
    simp only [total_counts] at hi
    exact congrArg (fun i => (i, A.counts hn s i)) hi
  · rintro rfl
    unfold checks report
    simp only [total_counts, implies_true, and_self]

-- 读法：`reportGroups` 的结果类型为 `Finset (Fin r)`。
def reportGroups (N : ℕ) (R : A.Report r d) : Finset (Fin r) :=
  univ.filter (fun g => N < 256 * A.total R (fun c t =>
    let w := A.cross t R.1 + Nat.clog 2 (Fintype.card A.I)
    (if c.1 = g then w else 0) + (if c.2.1 = g then w else 0)))

-- 读法：`A.reportGroups N (A.report hn s)` 等于 `(A.plan hn N s).groups`。
theorem report_groups (N : ℕ) (s : Packet n r d → A.I) :
    A.reportGroups N (A.report hn s) = (A.plan hn N s).groups := by
  simp only [reportGroups, report, total_counts, packetClass, plan, heavy, charge]
  rfl

-- 读法：`Fintype.card (A.Report r d)` 不超过 `2 ^ (Nat.clog 2 n + r ^ 3 * Fintype.card A.I * Nat.clog 2 (Fintype.card (Packet n r d) + 1))`。这里调用 `Nat.mul_le_mul`。
/-- 固定立方体与系数域后，公共报告的计数字段有多项式多个，每个字段的比特长度为对数级。

英文原文：The public report has polynomially many count fields, each of
logarithmic bit length, at fixed cube and coefficient field.
-/
theorem report_size :
    Fintype.card (A.Report r d) ≤
      2 ^ (Nat.clog 2 n + r ^ 3 * Fintype.card A.I * Nat.clog 2 (Fintype.card (Packet n r d) + 1)) := by
  change Fintype.card (Fin n × (Class r × A.I → Fin (Fintype.card (Packet n r d) + 1))) ≤ _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Class r) A.I]
  have he : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring
  rw [he, pow_add, mul_comm (r ^ 3 * Fintype.card A.I), pow_mul (2 : ℕ)]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide : 1 < 2) n)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) _) _)

end Expansion
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# 编码一个数据包类别中的各项选择

报告一旦固定，总跨界宽度就独立于该类中各选择器的具体分配。因而可以把选择器及其跨界比特装入一个长度如报告所示的比特串。

**英文原文**

Encoding the choices of one packet class

Once the report is fixed the total crossing width is independent of the
assignment of selectors in a class. The selectors and their crossing
bits therefore fit in a single bit string of the reported length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Finset Classical
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)

-- 读法：在后续公式中，`Members` 是 `{p : Packet n r d // packetClass hn R.1 p = c}` 的缩写。
abbrev Members (hn : 2 ≤ n) (R : A.Report r d) (c : Class r) :=
  {p : Packet n r d // packetClass hn R.1 p = c}

-- 读法：在后续公式中，`Selectors` 是 `{s : A.Members hn R c → A.I // ∀ z, multiplicity s z = (R.2 (c, z)).val}` 的缩写。
abbrev Selectors (hn : 2 ≤ n) (R : A.Report r d) (c : Class r) :=
  {s : A.Members hn R c → A.I // ∀ z, multiplicity s z = (R.2 (c, z)).val}

-- 读法：`shared` 的取值由 `decide (c.1 ∉ A.reportGroups N R ∧ c.2.1 ∉ A.reportGroups N R)` 给出。
def shared (N : ℕ) (R : A.Report r d) (c : Class r) : Bool :=
  decide (c.1 ∉ A.reportGroups N R ∧ c.2.1 ∉ A.reportGroups N R)

-- 读法：在后续公式中，`Alphabet` 是 `Σ s : A.Selectors hn R c, A.Wires s.val R.1 (fun _ => A.shared N R c)` 的缩写。
abbrev Alphabet (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r) :=
  Σ s : A.Selectors hn R c, A.Wires s.val R.1 (fun _ => A.shared N R c)

-- 读法：`classWidth` 的取值由 `∑ z, (R.2 (c, z)).val * (A.cross z R.1 + Nat.clog 2 (Fintype.card A.I))` 给出。
def classWidth (R : A.Report r d) (c : Class r) :=
  ∑ z, (R.2 (c, z)).val * (A.cross z R.1 + Nat.clog 2 (Fintype.card A.I))

variable {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

-- 读法：为 `Fintype (A.Selectors hn R c)` 构造类型类实例。
instance selectorFintype : Fintype (A.Selectors hn R c) := by
  unfold Selectors
  infer_instance

-- 读法：为 `Fintype (A.Wires s.val R.1 (fun _ => A.shared N R c))` 构造类型类实例。
instance wiresFintype {N : ℕ} (s : A.Selectors hn R c) :
    Fintype (A.Wires s.val R.1 (fun _ => A.shared N R c)) := by
  unfold Wires
  infer_instance

-- 读法：为 `Fintype (A.Alphabet hn N R c)` 构造类型类实例。
instance alphabetFintype {N : ℕ} : Fintype (A.Alphabet hn N R c) := by
  unfold Alphabet
  infer_instance

-- 读法：`A.classWidth R c` 等于 `∑ p, (A.cross (s.val p) R.1 + Nat.clog 2 (Fintype.card A.I))`。
theorem classWidth_spec (s : A.Selectors hn R c) :
    A.classWidth R c = ∑ p, (A.cross (s.val p) R.1 + Nat.clog 2 (Fintype.card A.I)) := by
  unfold classWidth
  simp_rw [← s.property, multiplicity, Fintype.card_subtype]
  have he (p : A.Members hn R c → Prop) [DecidablePred p] :
      (univ.filter p).card = ∑ i, if p i then 1 else 0 := by
    simp
  simp_rw [he, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# 按数据包次序打包一个选择器类别

**英文原文**

Packing one selector class in packet order
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
open Finset Classical

section Pack
variable {P : Type} [LinearOrder P] [Fintype P] (f : P → ℕ)

-- 读法：`packOrder` 的取值由 `Fintype.orderIsoFinOfCardEq _ (by simp)` 给出。
def packOrder : Fin (∑ p, f p) ≃o Lex (Σ p, Fin (f p)) :=
  Fintype.orderIsoFinOfCardEq _ (by simp)

variable {l : ℕ} (hl : ∑ p, f p ≤ l)

-- 读法：`pack` 的结果类型为 `((p : P) → Fin (f p) → Bool) ↪ (Fin l → Bool)`。
/-- 按数据包次序拼接各块，必要时补零。

英文原文：Concatenate blocks in packet order, padding with zero when necessary.
-/
def pack : ((p : P) → Fin (f p) → Bool) ↪ (Fin l → Bool) := by
  let e := (packOrder f).symm.toEquiv.toEmbedding.trans (Fin.castLEEmb hl)
  refine ⟨fun x => Function.extend e (fun z => x z.1 z.2) (fun _ => false), ?_⟩
  intro x y he
  funext p i
  have hh := congrFun he (e ⟨p, i⟩)
  exact ((e.injective.extend_apply (fun z => x z.1 z.2) _ ⟨p, i⟩).symm.trans hh).trans
    (e.injective.extend_apply (fun z => y z.1 z.2) _ ⟨p, i⟩)

-- 读法：`pack f hl x (Fin.castLE hl ((packOrder f).symm z))` 等于 `x z.1 z.2`。这里调用 `e.injective.extend_apply`。
theorem pack_at (x : (p : P) → Fin (f p) → Bool) (z : Lex (Σ p, Fin (f p))) :
    pack f hl x (Fin.castLE hl ((packOrder f).symm z)) = x z.1 z.2 := by
  let e := (packOrder f).symm.toEquiv.toEmbedding.trans (Fin.castLEEmb hl)
  exact e.injective.extend_apply (fun y => x y.1 y.2) (fun _ => false) z

end Pack

variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)

-- 读法：`selectorCode` 的结果类型为 `A.I ↪ (Fin (Nat.clog 2 (Fintype.card A.I)) → Bool)`。
def selectorCode : A.I ↪ (Fin (Nat.clog 2 (Fintype.card A.I)) → Bool) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card A.I)))

variable (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r)

-- 读法：`memberOrder` 的结果类型为 `LinearOrder (A.Members hn R c)`。
@[instance_reducible] def memberOrder : LinearOrder (A.Members hn R c) := by
  letI : LinearOrder (Packet n r d) :=
    inferInstanceAs (LinearOrder (Lex (Lex (Lex (Label n r) × Lex (Label n r)) × Fin d)))
  exact LinearOrder.lift' Subtype.val Subtype.val_injective

attribute [local instance] memberOrder

-- 读法：`selectorWidth` 的取值由 `∑ _ : A.Members hn R c, Nat.clog 2 (Fintype.card A.I)` 给出。
def selectorWidth := ∑ _ : A.Members hn R c, Nat.clog 2 (Fintype.card A.I)

variable {hn R c}

-- 读法：`A.classWidth R c` 等于 `A.selectorWidth hn R c + ∑ p, A.cross (s.val p) R.1`。
theorem classWidth_split (s : A.Selectors hn R c) :
    A.classWidth R c = A.selectorWidth hn R c + ∑ p, A.cross (s.val p) R.1 := by
  rw [A.classWidth_spec s, sum_add_distrib, add_comm]
  rfl

-- 读法：结论为 `∑ p, A.width (s.val p) R.1 (A.shared N R c) ≤ A.classWidth R c - A.selectorWidth hn R c`。这里调用 `sum_le_sum`。
theorem tail_bound (s : A.Selectors hn R c) :
    ∑ p, A.width (s.val p) R.1 (A.shared N R c) ≤ A.classWidth R c - A.selectorWidth hn R c := by
  rw [A.classWidth_split s, Nat.add_sub_cancel_left]
  apply sum_le_sum
  intro p _
  unfold width
  split_ifs <;> omega

-- 读法：`selectorPrefix` 的取值由 `pack (fun _ : A.Members hn R c => Nat.clog 2 (Fintype.card A.I)) le_rfl (fun p => A.selectorCode (s.val p))` 给出。
def selectorPrefix (s : A.Selectors hn R c) : Fin (A.selectorWidth hn R c) → Bool :=
  pack (fun _ : A.Members hn R c => Nat.clog 2 (Fintype.card A.I)) le_rfl
    (fun p => A.selectorCode (s.val p))

-- 读法：`crossingSuffix` 的取值由 `pack _ (A.tail_bound N z.1) z.2` 给出。
def crossingSuffix (z : A.Alphabet hn N R c) : Fin (A.classWidth R c - A.selectorWidth hn R c) → Bool :=
  pack _ (A.tail_bound N z.1) z.2

-- 读法：`codeSplit` 的结果类型为 `Fin (A.classWidth R c) ≃ Fin (A.selectorWidth hn R c + (A.classWidth R c - A.selectorWidth hn R c))`。
def codeSplit (s : A.Selectors hn R c) :
    Fin (A.classWidth R c) ≃ Fin (A.selectorWidth hn R c + (A.classWidth R c - A.selectorWidth hn R c)) :=
  finCongr (by have := A.classWidth_split s; omega)

-- 读法：用字段 `toFun`、`inj'`、`Fin.append`、`have` 构造 `A.Alphabet hn N R c ↪ (Fin (A.classWidth R c) → Bool)`。
/-- 固定前缀决定各跨越块的长度。

英文原文：The fixed prefix determines the lengths of the crossing blocks.
-/
def alphabetCode (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r) :
    A.Alphabet hn N R c ↪ (Fin (A.classWidth R c) → Bool) where
  toFun z i := Fin.append (A.selectorPrefix z.1) (A.crossingSuffix N z) (A.codeSplit z.1 i)
  inj' := by
    rintro ⟨s, x⟩ ⟨s', y⟩ he
    have he' (i) :
        Fin.append (A.selectorPrefix s) (A.crossingSuffix N ⟨s, x⟩) i =
        Fin.append (A.selectorPrefix s') (A.crossingSuffix N ⟨s', y⟩) i := by
      have hi : A.codeSplit s' = A.codeSplit s := rfl
      simpa only [hi, Equiv.apply_symm_apply] using congrFun he ((A.codeSplit s).symm i)
    have hs : A.selectorPrefix s = A.selectorPrefix s' := funext fun i => by
      simpa only [Fin.append_left] using he' (Fin.castAdd _ i)
    unfold selectorPrefix at hs
    have hs' := (pack _ le_rfl).injective hs
    have : s = s' := Subtype.ext (funext fun p => A.selectorCode.injective (congrFun hs' p))
    subst s'
    have ht : A.crossingSuffix N ⟨s, x⟩ = A.crossingSuffix N ⟨s, y⟩ := funext fun i => by
      simpa only [Fin.append_right] using he' (Fin.natAdd _ i)
    have : x = y := (pack _ (A.tail_bound N s)).injective ht
    rw [this]

-- 读法：`A.alphabetCode hn N R c z` 等于 `Fin.append (A.selectorPrefix z.1) (A.crossingSuffix N z) ∘ A.codeSplit z.1`。两端由定义化简为同一项。
theorem alphabetCode_eq (z : A.Alphabet hn N R c) :
    A.alphabetCode hn N R c z =
      Fin.append (A.selectorPrefix z.1) (A.crossingSuffix N z) ∘ A.codeSplit z.1 := rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end
