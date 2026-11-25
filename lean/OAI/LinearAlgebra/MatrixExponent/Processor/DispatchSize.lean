-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Physical
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Processor.Capacity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Install.ControlWeight

/-!
# 在工作单元中读取编码符号

非自环比特没有私有指派。对每个这样的比特，将其无序端点对的编号反解。通常读取从工作单元出发的链路段；若工作单元正是中继，则由另一个端点提供唯一的链路段。

**英文原文**

Reading encoded symbols at a worker

Nonloop bits have no private assignments. For each such bit invert
the numbering of its unordered endpoint pair. Read the leg starting
at the worker, unless the worker is the relay, in which case the
other endpoint supplies the unique leg.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

variable {R n : ℕ} {M : Type} [Fintype M] (src dst : M → Fin R)
  (serial : Numbering src dst)

-- 读法：`token` 的结果类型为 `Virtual (count src dst)`。
def token (e : M) (he : src e ≠ dst e) : Virtual (count src dst) :=
  if h : src e < dst e then
    ⟨⟨(src e, dst e), h⟩, (serial _ _).symm ⟨e, .inl ⟨rfl, rfl⟩⟩⟩
  else
    ⟨⟨(dst e, src e), lt_of_le_of_ne (le_of_not_gt h) he.symm⟩,
      (serial _ _).symm ⟨e, .inr ⟨rfl, rfl⟩⟩⟩

-- 读法：`ports src dst serial (.inl (token src dst serial e he))` 等于 `e`。
private theorem port_token (e : M) (he : src e ≠ dst e) :
    ports src dst serial (.inl (token src dst serial e he)) = e := by
  change edge src dst serial (.inl (token src dst serial e he)) = _
  unfold token
  split <;> simp [edge]

-- 读法：要证明的命题是 `sees u (token src dst serial e he).1`。
theorem sees_token (e : M) (he : src e ≠ dst e) (u : Fin R) (hu : src e = u ∨ dst e = u) :
    sees u (token src dst serial e he).1 := by
  unfold token
  split <;> simp only [sees] <;> grind

variable {q : Fin R → Fin R → ℕ}

-- 读法：`endpointLeg` 的结果类型为 `Leg q`。
def endpointLeg (b : Virtual q) (u : Fin R) (h : sees u b.1) : Leg q :=
  if hv : u ≠ via b then ⟨b, u, h, hv⟩
  else if hu : u = b.1.val.1 then ⟨b, b.1.val.2, .inr rfl, by grind [sees]⟩
  else ⟨b, b.1.val.1, .inl rfl, by grind⟩

-- 读法：`(at_endpoint b u h).choose` 等于 `endpointLeg b u h`。
private theorem at_endpoint_eq (b : Virtual q) (u : Fin R) (h : sees u b.1) :
    (at_endpoint b u h).choose = endpointLeg b u h := by
  have aux (l : Leg q) (hl : l.1 = b) (hi : sees u (link l)) :
      l = endpointLeg b u h := by
    have hi' := (incident l u).mp hi
    rcases l with ⟨c, v, hv, hne⟩
    change c = b at hl
    subst c
    change u = v ∨ u = via b at hi'
    unfold endpointLeg
    split_ifs <;> congr 2 <;> grind [sees]
  exact aux _ (at_endpoint b u h).choose_spec.1 (at_endpoint b u h).choose_spec.2

variable (hq : ∀ u, ∑ v, count src dst u v ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)

-- 读法：`location` 的结果类型为 `Fin (n / 4)`。
def location (u : Fin R) (e : M) (he : src e ≠ dst e) (hu : src e = u ∨ dst e = u) : Fin (n / 4) :=
  address (slot (count_symm src dst) hq hn
    (endpointLeg (token src dst serial e he) u (sees_token src dst serial e he u hu)))

-- 读法：`assignments src dst serial (receive (count_symm src dst) hq hn u t, x) e` 等于 `t (location src dst serial hq hn u e he hu)`。
theorem read_location (u : Fin R) (t : Fin (n / 4) → Bool) (x : ∀ v, Private src dst v → Bool)
    (e : M) (he : src e ≠ dst e) (hu : src e = u ∨ dst e = u) :
    assignments src dst serial (receive (count_symm src dst) hq hn u t, x) e =
      t (location src dst serial hq hn u e he hu) := by
  have hp := (ports src dst serial).symm_apply_eq.mpr (port_token src dst serial e he).symm
  unfold assignments
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, hp]
  change receive (count_symm src dst) hq hn u t (token src dst serial e he) = _
  rw [receive, dite_eq_left (sees_token src dst serial e he u hu), at_endpoint_eq]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Encoded
open Classical
variable {R n : ℕ} {M : Type} [Fintype M] (src dst : M → Fin R)
  (alph : M → Type) (w : M → ℕ) (code : ∀ e, alph e ↪ (Fin (w e) → Bool))

local notation "S" => left src dst w
local notation "D" => right src dst w

-- 读法：要证明的命题是 `IsEmpty (Links.Private S D u)`。
theorem private_empty (u : Fin R) : IsEmpty (Links.Private S D u) := by
  have : IsEmpty (Links.Between S D u u) := by
    refine ⟨fun ⟨b, h⟩ => b.1.2 ?_⟩
    rcases h with h | h <;> exact h.1.trans h.2.symm
  rw [Links.Private, Links.count, Fintype.card_eq_zero]
  infer_instance

variable (hd : ∀ u, ∑ e ∈ Finset.univ.filter
  (fun e => src e ≠ dst e ∧ (src e = u ∨ dst e = u)), w e ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)
  (serial : Links.Numbering (left src dst w) (right src dst w))

include hd in
-- 读法：结论为 `∑ v, Links.count S D u v ≤ n / 64`。通过传递性衔接 `Links.count_le` 与 `hd`。
theorem count_bound (u : Fin R) : ∑ v, Links.count S D u v ≤ n / 64 :=
  (Links.count_le S D u).trans ((load src dst w u).le.trans (hd u))

-- 读法：`location` 的结果类型为 `Fin (n / 4)`。
def location (u : Fin R) (b : Bits src dst w) (hu : S b = u ∨ D b = u) : Fin (n / 4) := by
  have he : S b ≠ D b := b.1.property
  exact Links.location S D serial (count_bound src dst w hd) hn u b he hu

-- 读法：`receives` 的结果类型为 `Prop`。
/-- 将共享符号的每个比特与其物理输入地址处的比特进行比较。

英文原文：Compare every bit of a shared symbol with its physical input address.
-/
def receives (u : Fin R) (t : Fin (n / 4) → Bool) (z : Local src dst alph u) : Prop :=
  ∀ (e : Shared src dst) (he : src e.val = u ∨ dst e.val = u) (j : Fin (w e.val)),
    code e.val (z ⟨e.val, he⟩) j =
      t (location src dst w hd hn serial u ⟨e, j⟩ he)

variable [DecidableEq M] [∀ e, Fintype (alph e)] {F : Type} [Field F]

-- 读法：这里调用 `forall_congr'`。
/-- 检验完中继相等条件和未用连线的固定取值后，只剩局部符号需要求和。

英文原文：Once relay equality and unused-wire pins have been checked,
only the local symbols remain to be summed.
-/
theorem worker_eq (g : Fin R → (∀ e, alph e) → F) (u : Fin R) (t : Fin (n / 4) → Bool) :
    worker src dst alph w code hd hn g serial u t =
      if Links.valid (Links.count_symm S D) (count_bound src dst w hd) hn u t then
        ∑ z : Local src dst alph u,
          if receives src dst alph w code hd hn serial u t z then localize src dst alph g u z else 0
      else 0 := by
  have := private_empty src dst w u
  have he (x : ∀ v, Links.Private S D v → Bool) (z : Local src dst alph u) :
      agrees src dst alph w code u
        (Links.assignments S D serial
          (Links.receive (Links.count_symm S D) (count_bound src dst w hd) hn u t, x)) z ↔
        receives src dst alph w code hd hn serial u t z := by
    unfold agrees receives location
    apply forall_congr'
    intro e
    apply forall_congr'
    intro h
    apply forall_congr'
    intro j
    rw [Links.read_location S D serial _ hn u t x (⟨e, j⟩ : Bits src dst w) e.property h]
  unfold worker Links.worker Links.site Links.tally
  rw [Fintype.sum_unique]
  simp only [bitSite, he]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Encoded
end

/-!
# 实现对公开报告的检验

验证某类的总数需要两个不等式，与每个候选切口比较则各需一个不等式。若并列，利用偏移量选取最先出现的索引。

**英文原文**

Realizing the public report checks

A class total needs two inequalities and comparing against each
candidate cut needs one. The offsets resolve ties by the first index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Classical Processor Finset
variable {F : Type} [Field F] {n h r d v : ℕ} (A : Expansion F n h) (hn : 2 ≤ n)

-- 读法：`i` 等于 `first hn s ↔ ∀ j, s i < s j + if i ≤ j then 1 else 0`。
private theorem first_iff (s : Fin n → ℕ) (i : Fin n) :
    i = first hn s ↔ ∀ j, s i < s j + if i ≤ j then 1 else 0 := by
  constructor
  · rintro rfl j
    have := first_spec hn s j
    split_ifs <;> omega
  · intro h
    have h₁ := h (first hn s)
    have h₂ := first_spec hn s i
    split_ifs at h₁ <;> omega

-- 读法：在后续公式中，`Tests` 是 `Fin n ⊕ Class r × Bool` 的缩写。
abbrev Tests (n r : ℕ) := Fin n ⊕ Class r × Bool

-- 读法：`limit` 的取值由 `Fintype.card {p : Packet n r d // packetClass hn i p = c}` 给出。
private def limit (d : ℕ) (i : Fin n) (c : Class r) :=
  Fintype.card {p : Packet n r d // packetClass hn i p = c}

-- 读法：逐一匹配以下输入模式：`.inl j`、`.inr (c, t)`。
private def sides (d : ℕ) (i : Fin n) (side : Bool) :
    Tests n r → Form (Class r × A.I)
  | .inl j =>
    if side then ⟨fun z => A.cross z.2 j, if i ≤ j then 1 else 0⟩
    else ⟨fun z => A.cross z.2 i, 0⟩
  | .inr (c, t) =>
    if t = side then ⟨fun z => if z.1 = c then 1 else 0, side.toNat⟩
    else ⟨fun _ => 0, limit hn d i c + side.toNat⟩

-- 读法：`linear (fun z => if z.1 = c then 1 else 0) x` 等于 `∑ j, A.cnt x (c, j)`。
private theorem class_total (x : A.CountBit r d → Bool) (c : Class r) :
    linear (fun z => if z.1 = c then 1 else 0) x = ∑ j, A.cnt x (c, j) := by
  unfold linear
  rw [Fintype.sum_prod_type, sum_comm]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true, cnt]

-- 读法：`A.guard hn i x` 与 `∀ u : Tests n r, (A.sides hn d i false u).value x < (A.sides hn d i true u).value x` 等价。
private theorem guard_tests (i : Fin n) (x : A.CountBit r d → Bool) :
    A.guard hn i x ↔ ∀ u : Tests n r,
      (A.sides hn d i false u).value x < (A.sides hn d i true u).value x := by
  let s (i : Fin n) := ∑ z, A.cnt x z * A.cross z.2 i
  let t (c : Class r) := ∑ z, A.cnt x (c, z)
  let test (u : Tests n r) := (A.sides hn d i false u).value x < (A.sides hn d i true u).value x
  have h₀ : linear (fun _ => 0) x = 0 := by simp [linear]
  have h₁ (j : Fin n) : test (.inl j) ↔ s i < s j + if i ≤ j then 1 else 0 := Iff.rfl
  have h₂ (c : Class r) : test (.inr (c, false)) ↔ t c ≤ limit hn d i c := by
    simp [test, sides, Form.value, class_total, h₀, t]
  have h₃ (c : Class r) : test (.inr (c, true)) ↔ limit hn d i c ≤ t c := by
    simp [test, sides, Form.value, class_total, h₀, t]
  change (∀ c, t c = limit hn d i c) ∧ i = first hn s ↔ ∀ u, test u
  rw [first_iff]
  constructor
  · rintro ⟨ht, hs⟩ (j|⟨c, _|_⟩)
    · exact (h₁ j).2 (hs j)
    · exact (h₂ c).2 (ht c).le
    · exact (h₃ c).2 (ht c).ge
  · intro h
    exact ⟨fun c => le_antisymm ((h₂ c).mp (h _)) ((h₃ c).mp (h _)), fun j => (h₁ j).mp (h _)⟩

-- 读法：在后续公式中，`registerWidth` 是 `Nat.clog 2 (Fintype.card (Packet n r d) + 1)` 的缩写。
abbrev registerWidth (n r d : ℕ) := Nat.clog 2 (Fintype.card (Packet n r d) + 1)

-- 读法：`(A.sides hn d i b u).value x` 严格小于 `2 ^ v`。按 `y = b <;> by_cases ht : j.1 = t <;> simp [sides, hy, ht, hM]` 成立与否分情况。
private theorem sides_lt {M : ℕ} (hM : 1 ≤ M) (hc : ∀ s j, A.cross s j ≤ M)
    (hv : Fintype.card (Class r × A.I) * (2 ^ registerWidth n r d * M) +
      Fintype.card (Packet n r d) + 1 < 2 ^ v)
    (i : Fin n) (b : Bool) (u : Tests n r) (x : A.CountBit r d → Bool) :
    (A.sides hn d i b u).value x < 2 ^ v := by
  have hh : ∀ j, (A.sides hn d i b u).factors j ≤ M := by
    intro j
    rcases u with k|⟨t, y⟩
    · cases b <;> exact hc _ _
    · by_cases hy : y = b <;> by_cases ht : j.1 = t <;> simp [sides, hy, ht, hM]
  have ho : (A.sides hn d i b u).offset ≤ Fintype.card (Packet n r d) + 1 := by
    rcases u with k|⟨t, y⟩
    · cases b <;> by_cases hi : i ≤ k <;> simp [sides, hi]
    · have : limit hn d i t ≤ Fintype.card (Packet n r d) := Fintype.card_subtype_le _
      have : b.toNat ≤ 1 := by cases b <;> decide
      by_cases hy : y = b <;> simp only [sides, hy, ite_true, ite_false] <;> omega
  exact lt_of_le_of_lt (Nat.add_le_add (linear_le hh x) ho) (by rw [add_assoc] at hv; exact hv)

-- 读法：`guardCost` 的取值由 `100000 * (1 + Fintype.card (Tests n r)) * (1 + Fintype.card (Class r × A.I) * registerWidth n r d) * (1 + v)` 给出。
def guardCost (r d v : ℕ) :=
  100000 * (1 + Fintype.card (Tests n r)) *
    (1 + Fintype.card (Class r × A.I) * registerWidth n r d) * (1 + v)

-- 读法：要证明的命题是 `Install.Weight F (fun x : A.CountBit r d → Bool => if A.guard hn i x then 1 else 0) (A.guardCost r d v)`。这里调用 `checks_net`。
theorem guard_net {M : ℕ} (hM : 1 ≤ M) (hc : ∀ s j, A.cross s j ≤ M)
    (hv : Fintype.card (Class r × A.I) * (2 ^ registerWidth n r d * M) +
      Fintype.card (Packet n r d) + 1 < 2 ^ v) (i : Fin n) :
    Install.Weight F (fun x : A.CountBit r d → Bool => if A.guard hn i x then 1 else 0)
      (A.guardCost r d v) := by
  simp only [guard_tests]
  exact checks_net F (A.sides hn d i false) (A.sides hn d i true) v _
    (A.sides_lt hn hM hc hv i false) (A.sides_lt hn hM hc hv i true)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

section
/-!
# 检验报告所用的寄存器与电路规模上界

**英文原文**

Register and circuit size bounds for the report checks
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
open Classical
variable {F : Type} [Field F] {n r d h : ℕ} (A : Expansion F n h)

-- 读法：`Fintype.card (Class r)` 等于 `r ^ 3`。
private theorem class_card (r : ℕ) : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring

-- 读法：要证明的命题是 `Install.Weight F (fun x : A.CountBit r d → Bool => if A.guard hn i x then 1 else 0) (2 ^ w * w ^ 5)`。这里调用 `Nat.clog_le_of_le_pow`。
theorem guard_size (hn : 2 ≤ n) (w : ℕ)
    (hw : 100000000 ≤ w) (hnw : n ≤ w) (hI : Fintype.card A.I ≤ w)
    (hc : ∀ s i, A.cross s i ≤ w) (hr : 0 < r) (hrw : r ^ 6 ≤ 2 ^ w)
    (hpc : Fintype.card (Packet n r d) < (2 ^ w) ^ 8) (i : Fin n) :
    Install.Weight F (fun x : A.CountBit r d → Bool => if A.guard hn i x then 1 else 0)
      (2 ^ w * w ^ 5) := by
  let N := 2 ^ w
  have hwN : w < N := Nat.lt_two_pow_self
  have hN : 2 ≤ N := by omega
  have hw' : 1 ≤ w := by omega
  -- 推导：记下中间结论 `hword`：`registerWidth n r d ≤ w * 8`。
  have hword : registerWidth n r d ≤ w * 8 := by
    apply Nat.clog_le_of_le_pow
    rwa [pow_mul]
  have hr' : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ hr
  have hrN : r ^ 3 ≤ N := (Nat.pow_le_pow_right hr (by decide : 3 ≤ 6)).trans hrw
  have hrows : Fintype.card (Class r × A.I) ≤ r ^ 3 * w := by
    rw [Fintype.card_prod, class_card]
    gcongr
  have htests : Fintype.card (Tests n r) ≤ n + 2 * r ^ 3 := by
    simp only [Tests, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
    exact le_of_eq (by ring)
  have hupper : Fintype.card (Class r × A.I) * (2 ^ registerWidth n r d * w) +
      Fintype.card (Packet n r d) + 1 < 2 ^ (w * 13) := by
    calc
      _ ≤ (r ^ 3 * w) * (2 ^ (w * 8) * w) + N ^ 8 := by
        rw [add_assoc]
        exact Nat.add_le_add (Nat.mul_le_mul hrows (by gcongr)) hpc
      _ ≤ (N * N) * (N ^ 8 * N) + N ^ 8 := by rw [pow_mul]; gcongr
      _ = N ^ 11 + N ^ 8 := by ring
      _ ≤ 2 * N ^ 11 := by rw [two_mul]; gcongr; omega
      _ < N ^ 2 * N ^ 11 := by gcongr; nlinarith
      _ = 2 ^ (w * 13) := by unfold N; rw [← pow_add, pow_mul]
  apply (A.guard_net hn hw' hc hupper i).mono
  unfold guardCost
  -- 推导：记下中间结论 `h₁`：`1 + Fintype.card (Tests n r) ≤ 4 * r ^ 3 * w`。
  have h₁ : 1 + Fintype.card (Tests n r) ≤ 4 * r ^ 3 * w := by
    nlinarith only [htests, hnw, hr', hw', Nat.le_mul_of_pos_left w hr',
      Nat.le_mul_of_pos_right (r ^ 3) hw']
  have h₂ : 1 + Fintype.card (Class r × A.I) * registerWidth n r d ≤ 9 * r ^ 3 * w ^ 2 := by
    have ht := Nat.mul_le_mul hrows hword
    have : 0 < r ^ 3 * w ^ 2 := by positivity
    nlinarith only [ht, this]
  calc
    _ ≤ 100000 * (4 * r ^ 3 * w) * (9 * r ^ 3 * w ^ 2) * (14 * w) := by gcongr; omega
    _ = r ^ 6 * 50400000 * w ^ 4 := by ring
    _ ≤ 2 ^ w * w * w ^ 4 := by gcongr; omega
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

section
/-!
# 在获知图式前固定模板组

立方体的每个坐标各用一个模板。处理器长度的一个小正次幂足以吸收各脚本中的所有多对数因子。同一份脚本可以在多份副本中复用。

**英文原文**

A bank fixed before the diagram is known

Use one template per cube coordinate. A small power of the processor
length covers every polylogarithmic factor in the individual scripts.
The same scripts can be reused in many copies.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Filter

-- 读法：对每个 `ᶠ w : ℕ in atTop`，`w ^ q` 不超过 `2 ^ (w / k)`。
theorem poly_bound (q k : ℕ) (hk : 0 < k) :
    ∀ᶠ w : ℕ in atTop, w ^ q ≤ 2 ^ (w / k) := by
  have ht : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := isLittleO_pow_exp_pos_mul_atTop q (by positivity : 0 < Real.log 2 / (2 * k))
  filter_upwards [eventually_ge_atTop k, ht.eventually hp.eventuallyLE] with w hw he
  have hw' : w ≤ (2 * k) * (w / k) := by
    have := Nat.mod_add_div w k
    have := Nat.mod_lt w hk
    have := Nat.le_mul_of_pos_right k (Nat.div_pos hw hk)
    rw [mul_assoc]
    omega
  -- 推导：记下中间结论 `hj`：`(w : ℝ) / (2 * k) ≤ (w / k : ℕ)`。
  have hj : (w : ℝ) / (2 * k) ≤ (w / k : ℕ) := by
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact_mod_cast hw'
  have h : (w : ℝ) ^ q ≤ (2 : ℝ) ^ (w / k) := by
    calc
      _ ≤ Real.exp (Real.log 2 / (2 * k) * w) := by
        simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (w : ℝ) ^ q),
          Real.norm_of_nonneg (Real.exp_nonneg _)] using he
      _ = (2 : ℝ) ^ ((w : ℝ) / (2 * k)) := by rw [Real.rpow_def_of_pos (by positivity)]; congr 1; ring
      _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hj
  exact_mod_cast h

-- 读法：`C * (2 + K * (1 + Nat.clog 2 (2 ^ w + 3)) ^ q)` 不超过 `w ^ (q + 1)`。这里调用 `Nat.clog_le_of_le_pow`。
private theorem log_rate (C K q w : ℕ) (hw : 2 ≤ w) (hc : C * (2 + K * 2 ^ q) ≤ w) :
    C * (2 + K * (1 + Nat.clog 2 (2 ^ w + 3)) ^ q) ≤ w ^ (q + 1) := by
  have hg : Nat.clog 2 (2 ^ w + 3) ≤ w + 1 := by
    apply Nat.clog_le_of_le_pow
    have h : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    rw [pow_succ]
    omega
  calc
    _ ≤ C * (2 * w ^ q + K * (2 * w) ^ q) := by
      gcongr
      · exact Nat.le_mul_of_pos_right _ (by positivity)
      · omega
    _ = C * (2 + K * 2 ^ q) * w ^ q := by rw [mul_pow]; ring
    _ ≤ w * w ^ q := Nat.mul_le_mul_right _ hc
    _ = _ := (pow_succ' _ _).symm

-- 读法：`Fintype.card (b.Bits F)` 等于 `∑ i, 2 ^ (b.width i + 1) * (4 * (b.width i + 1) + 16 * Fintype.card F)`。这里调用 `Finset.sum_congr`。
private theorem card_bits (F : Type) [Fintype F] {n : ℕ} (b : Bank (Fin n)) :
    Fintype.card (b.Bits F) =
      ∑ i, 2 ^ (b.width i + 1) * (4 * (b.width i + 1) + 16 * Fintype.card F) := by
  simp only [Bank.Bits, Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => card_script F (b.width i + 1))

-- 读法：证明中先建立 `hw`，即 `2 ≤ w`。
theorem scales (F : Type) [Field F] [Fintype F] (n C K q : ℕ) (hn : 2 ≤ n) :
    ∀ᶠ w : ℕ in atTop,
      let N := 2 ^ w
      let r := 2 ^ (w / (16 * n))
      let d := 2 ^ (w / (32 * n))
      ∃ b : Bank (Fin n), b.budget F ≤ N * w ^ (q + 8) ∧
        Fintype.card (b.Bits F) ≤ N / 2048 / 2 ∧
        ∀ i : Fin n, C * N * d * (2 + K * (1 + Nat.clog 2 (N + 3)) ^ q) ≤ 2 ^ (b.width i) * r ∧
          4 * r ≤ d * 2 ^ (b.repetitions i) := by
  let T := 2 + C * (2 + K * 2 ^ q) + 64 * n * templateCost F + 8192 * n * (8 + 16 * Fintype.card F)
  filter_upwards [eventually_ge_atTop T, poly_bound (q + 4) (32 * n) (by omega)] with w hT he
  intro N r d
  -- 推导：记下中间结论 `hw`：`2 ≤ w`。
  have hw : 2 ≤ w := by omega
  let j := w / (32 * n)
  have hj : j ≤ w := Nat.div_le_self _ _
  have hr : w / (16 * n) / 2 = j := by
    rw [Nat.div_div_eq_div_mul, show 16 * n * 2 = 32 * n by ring]
  have hr₀ : d * d ≤ r := by
    change 2 ^ j * 2 ^ j ≤ 2 ^ (w / (16 * n))
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hr₁ : r ≤ d * d * 2 := by
    change 2 ^ (w / (16 * n)) ≤ 2 ^ j * 2 ^ j * 2
    rw [← pow_add, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  let L := Nat.log 2 (w ^ (q + 1)) + 1
  -- 推导：记下中间结论 `hlo`：`w ^ (q + 1) ≤ 2 ^ L`。
  have hlo : w ^ (q + 1) ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by decide) _).le
  have hhi : 2 ^ L ≤ w ^ (q + 2) := by
    dsimp only [L]
    rw [pow_succ, show q + 2 = (q + 1) + 1 by omega, pow_succ w (q + 1)]
    exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (by positivity)) hw
  have hL : L ≤ j := by
    have h := hhi.trans ((Nat.pow_le_pow_right (by omega : 0 < w) (by omega : q + 2 ≤ q + 4)).trans he)
    exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp h
  let u := w - j + L
  have hu : u ≤ w := by omega
  -- 推导：记下中间结论 `hd`：`2 ^ (w - j) * d = N`。
  have hd : 2 ^ (w - j) * d = N := by change 2 ^ (w - j) * 2 ^ j = 2 ^ w; rw [← pow_add, Nat.sub_add_cancel hj]
  have hu' : 2 ^ u = 2 ^ (w - j) * 2 ^ L := pow_add _ _ _
  have hd' : 2 ^ (j + 3) = 8 * d := by rw [pow_add, mul_comm]; rfl
  let b : Bank (Fin n) := ⟨fun _ => u, fun _ => j + 3⟩
  refine ⟨b, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [Bank.budget, b, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id, hd', hu']
    calc
      _ = n * templateCost F * 8 * N * 2 ^ L * (u + 2) ^ 3 := by rw [← hd]; ring
      _ ≤ n * templateCost F * 8 * N * w ^ (q + 2) * (2 * w) ^ 3 := by gcongr; omega
      _ = N * (64 * n * templateCost F) * w ^ (q + 5) := by rw [show q + 5 = (q + 2) + 3 by omega, pow_add w (q + 2)]; ring
      _ ≤ N * w * w ^ (q + 5) := by gcongr; omega
      _ ≤ _ := by
        rw [mul_assoc, ← pow_succ']
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  · apply (Nat.le_div_iff_mul_le (by decide)).mpr
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    rw [card_bits]
    simp only [b, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    -- 推导：记下中间结论 `ht`：`4 * (u + 1) + 16 * Fintype.card F ≤ (8 + 16 * Fintype.card F) * w`。
    have ht : 4 * (u + 1) + 16 * Fintype.card F ≤ (8 + 16 * Fintype.card F) * w := by
      have := Nat.le_mul_of_pos_right (Fintype.card F) (by omega : 0 < w)
      nlinarith
    calc
      _ ≤ n * (2 ^ (u + 1) * ((8 + 16 * Fintype.card F) * w)) * 2 * 2048 := by gcongr
      _ = 2 ^ (w - j) * (8192 * n * (8 + 16 * Fintype.card F) * 2 ^ L * w) := by rw [pow_succ, hu']; ring
      _ ≤ 2 ^ (w - j) * (w * w ^ (q + 2) * w) := by gcongr; omega
      _ = 2 ^ (w - j) * w ^ (q + 4) := by rw [← pow_succ', ← pow_succ]
      _ ≤ N := by rw [← hd]; exact Nat.mul_le_mul_left _ he
  · have h := (log_rate C K q w hw (by omega)).trans hlo
    calc
      _ = N * d * (C * (2 + K * (1 + Nat.clog 2 (N + 3)) ^ q)) := by ring
      _ ≤ N * d * 2 ^ L := Nat.mul_le_mul_left _ h
      _ = 2 ^ u * (d * d) := by rw [hu', ← hd]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hr₀
  · change 4 * r ≤ d * 2 ^ (j + 3)
    rw [hd']
    nlinarith only [hr₁]

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-!
# 可能产生贡献的广播串

普通分支要求报告可行。不可行的计数表对应空的符号空间，因此在每个站点的权重都是零。额外分支使用全零广播。

**英文原文**

Which broadcast strings can contribute

An ordinary branch requires a feasible report. An infeasible count
table has an empty symbol space, hence zero weight at every site.
The extra branch uses the all-zero broadcast.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

variable {F : Type} [Field F] {n h : ℕ} (A : Expansion F n h) (hn : 2 ≤ n)
  (N r d b : ℕ) (hb : Nat.clog 2 n + r ^ 3 * Fintype.card A.I *
    Nat.clog 2 (Fintype.card (Packet n r d) + 1) + 1 ≤ b)

-- 读法：`stamp` 的结果类型为 `Prop`。
def stamp (i : Fin n) (z : Fin b → Bool) : Prop :=
  z (A.reportPort r d b hb (.inl ())) = true ∧
    (∀ j, z (A.reportPort r d b hb (.inr (.inl j))) = i.val.testBit j.val) ∧
    ∀ k ∉ Set.range (A.reportPort r d b hb), z k = false

-- 读法：`readCounts` 的取值由 `z (A.reportPort r d b hb (.inr (.inr p)))` 给出。
def readCounts (z : Fin b → Bool) (p : A.CountBit r d) : Bool :=
  z (A.reportPort r d b hb (.inr (.inr p)))

-- 读法：`A.readCounts r d b hb (A.encodeReport hn N r d b hb (some R))` 等于 `A.countBits R.val`。用函数外延性比较等号两侧在 `(A.encodeReport_count hn N r d b hb R)` 处的取值。
@[simp] theorem readCounts_encodeReport (R : A.Accepted (r := r) (d := d) hn (A.budget hn N)) :
    A.readCounts r d b hb (A.encodeReport hn N r d b hb (some R)) = A.countBits R.val :=
  funext (A.encodeReport_count hn N r d b hb R)

-- 读法：按 `j ∈ Set.range (A.reportPort r d b hb)` 成立与否分情况。
theorem guard_broadcast (hbudget : ∀ s : Packet n r d → A.I, A.budget hn N (A.report hn s))
    (i : Fin n) (z : Fin b → Bool) :
    A.stamp r d b hb i z ∧ A.guard hn i (A.readCounts r d b hb z) ↔
      ∃ R : A.Accepted (r := r) (d := d) hn (A.budget hn N),
        A.feasible hn R.val ∧ R.val.1 = i ∧ A.encodeReport hn N r d b hb (some R) = z := by
  rw [A.guard_iff hn N hbudget]
  constructor
  · rintro ⟨⟨hflag, hcut, hpad⟩, R, hf, hi, hcount⟩
    refine ⟨R, hf, hi, funext fun j => ?_⟩
    by_cases hj : j ∈ Set.range (A.reportPort r d b hb)
    -- 推导：从 `hj` 中取出 `_|k|p, rfl`。
    · obtain ⟨_|k|p, rfl⟩ := hj
      · exact (A.encodeReport_flag hn N r d b hb R).trans hflag.symm
      · rw [encodeReport_cut, hi, hcut]
      · rw [encodeReport_count, hcount]
        rfl
    · exact (A.encodeReport_pad hn N r d b hb (some R) j hj).trans (hpad j hj).symm
  · rintro ⟨R, hf, rfl, rfl⟩
    exact ⟨⟨A.encodeReport_flag hn N r d b hb R, A.encodeReport_cut hn N r d b hb R,
      A.encodeReport_pad hn N r d b hb (some R)⟩, R, hf, rfl,
      (A.readCounts_encodeReport hn N r d b hb R).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal
variable {F : Type} [Field F] [Fintype F] {N l d B n r h : ℕ}
  {P : Format N l d n r h} {A : Expansion F n h} {hn : 2 ≤ n} {M : Bank (Fin n)}
  (C : Controller P A hn M B) (i : Fin (3 * r)) (c : M.Bits F → Bool)

-- 读法：`C.site i c R y` 等于 `0`。
theorem site_infeasible (R : P.Reports A hn B) (y : Fin (N / 4) → Bool)
    (hf : ¬ A.feasible hn R.val) : C.site i c R y = 0 := by
  classical
  have he := mt (A.feasible_symbols hn R.val N (T := Pin N l l r)).mpr hf
  unfold site Expansion.extraProcessor
  rw [Encoded.worker_eq]
  simp only [Encoded.localize, he, dite_false, ite_self, Finset.sum_const_zero]

-- 读法：`C.run i c z y` 等于 `0`。按 `z ∈ Set.range e` 成立与否分情况。
theorem run_invalid (z : Fin l → Bool) (y : Fin (N / 4) → Bool) (hz : z ≠ fun _ => false)
    (hr : ∀ R : P.Reports A hn B, A.feasible hn R.val →
      A.encodeReport hn N r (B * P.count) l C.fits (some R) ≠ z) :
    C.run i c z y = 0 := by
  classical
  let e := A.encodeReport hn N r (B * P.count) l C.fits
  by_cases h : z ∈ Set.range e
  · obtain ⟨_|R, rfl⟩ := h
    · exact (hz (funext (A.encodeReport_none hn N r (B * P.count) l C.fits))).elim
    · unfold run Machine.branch
      rw [e.injective.extend_apply]
      exact C.site_infeasible i c R y (fun hf => hr R hf rfl)
  · unfold run Machine.branch
    exact Function.extend_apply' _ _ _ h

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# 按广播首部选择处理器执行的分支

一个控制比特与所选切口共同选定固定切口的实现。其余检验确保类别计数正确并固定未用比特的值。单独处理全零情形，可实现单位元分支。

**英文原文**

Dispatching the processor by its broadcast header

One control bit and the cut select a fixed-cut implementation. The
remaining checks impose the class counts and pin the unused bits.
A separate all-zero case realizes the unit branch.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal Classical Install
variable {F : Type} [Field F]

-- 读法：要证明的命题是 `Weight F (fun x => if ∀ j, x (a j) = false then 1 else 0) (Fintype.card I + 4 * Fintype.card J + 17)`。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem pin_net {I J : Type} [Fintype I] [Fintype J] (a : J → I) :
    Weight F (fun x => if ∀ j, x (a j) = false then 1 else 0)
      (Fintype.card I + 4 * Fintype.card J + 17) := by
  have h := ((BNet.any F J).pull a).weight
    (Weight.dense F Unit (fun x => if x () then 0 else 1))
  convert h using 1
  · funext x
    simp only [Function.comp_apply, decide_eq_true_eq, ← Bool.not_eq_true, ← not_exists, ite_not]
  · simp; omega

variable [Fintype F] {N l d B n r h g m : ℕ}
  {P : Format N l d n r h} {A : Expansion F n h} {hn : 2 ≤ n} {M : Bank (Fin n)}
  (C : Controller P A hn M B)

-- 读法：在后续公式中，`Input` 是 `Machine.Ports N l l → Bool` 的缩写。
private abbrev Input (N l : ℕ) := Machine.Ports N l l → Bool
-- 读法：在后续公式中，`Header` 是 `Unit ⊕ Fin (Nat.clog 2 n)` 的缩写。
private abbrev Header (n : ℕ) := Unit ⊕ Fin (Nat.clog 2 n)
-- 读法：在后续公式中，`port` 是 `A.reportPort r (B * P.count) l C.fits` 的缩写。
private abbrev port := A.reportPort r (B * P.count) l C.fits
-- 读法：在后续公式中，`reportCode` 是 `A.encodeReport hn N r (B * P.count) l C.fits` 的缩写。
private abbrev reportCode := A.encodeReport hn N r (B * P.count) l C.fits

-- 读法：`Handles` 表示以下条件：对每个 `i c (R : P.Reports A hn B) y`，由 `R.val.1 = k` 推出 `A.feasible hn R.val → f (Sum.elim (C.code (some (i, c))) (Sum.elim (C.reportCode (some R)) y)) = C.site i c R y`。
/-- 在对角收缩所用的字面值与报告上成立的正确性。

英文原文：Correctness on the literals and reports used by the diagonal contraction.
-/
def Handles (k : Fin n) (f : (Machine.Ports N l l → Bool) → F) : Prop :=
  ∀ i c (R : P.Reports A hn B) y, R.val.1 = k → A.feasible hn R.val →
    f (Sum.elim (C.code (some (i, c))) (Sum.elim (C.reportCode (some R)) y)) = C.site i c R y

-- 读法：逐一匹配以下输入模式：`.inl _`、`.inr j`。
private def head : Header n → Fin l
  | .inl _ => C.port (.inl ())
  | .inr j => C.port (.inr (.inl j))

-- 读法：`parse` 的取值由 `if h : x (.inl ()) = true ∧ Processor.number (x ∘ Sum.inr) < n then some ⟨Processor.number (x ∘ Sum.inr), h.2⟩ else none` 给出。
private def parse (x : Header n → Bool) : Option (Fin n) :=
  if h : x (.inl ()) = true ∧ Processor.number (x ∘ Sum.inr) < n then
    some ⟨Processor.number (x ∘ Sum.inr), h.2⟩ else none

-- 读法：`parse (C.reportCode (some R) ∘ C.head)` 等于 `some R.val.1`。这里调用 `number_test`。
private theorem parse_report (R : P.Reports A hn B) :
    parse (C.reportCode (some R) ∘ C.head) = some R.val.1 := by
  have ht : Processor.number ((C.reportCode (some R) ∘ C.head) ∘ Sum.inr) = R.val.1.val := by
    simp only [Function.comp_def, head, reportCode, port, Expansion.encodeReport_cut]
    exact number_test _ (R.val.1.isLt.trans_le (Nat.le_pow_clog (by decide) _))
  unfold parse
  simp only [ht, Function.comp_apply, head, port, reportCode, Expansion.encodeReport_flag,
    R.val.1.isLt, and_self, dite_eq_left]

-- 读法：在后续公式中，`Pad` 是 `{i : Fin l // i ∉ Set.range C.port}` 的缩写。
private abbrev Pad := {i : Fin l // i ∉ Set.range C.port}

-- 读法：`good` 表示以下条件：`(∀ j : C.Pad, z j.val = false)` 与 `A.guard hn k (A.readCounts r (B * P.count) l C.fits z)` 同时成立。
private def good (k : Fin n) (z : Fin l → Bool) : Prop :=
  (∀ j : C.Pad, z j.val = false) ∧ A.guard hn k (A.readCounts r (B * P.count) l C.fits z)

-- 读法：`C.good k z` 与 `∃ R : P.Reports A hn B, A.feasible hn R.val ∧ R.val.1 = k ∧ C.reportCode (some R) = z` 等价。这里调用 `and_congr_left'`。
private theorem good_iff (z : Fin l → Bool) (k : Fin n) (hk : parse (z ∘ C.head) = some k) :
    C.good k z ↔ ∃ R : P.Reports A hn B,
      A.feasible hn R.val ∧ R.val.1 = k ∧ C.reportCode (some R) = z := by
  rw [← A.guard_broadcast hn N r (B * P.count) l C.fits C.packets k z]
  unfold good
  apply and_congr_left'
  unfold parse at hk
  split at hk
  · rename_i h
    have he : Processor.number ((z ∘ C.head) ∘ Sum.inr) = k.val := congrArg Fin.val (Option.some.inj hk)
    have ht (j : Fin (Nat.clog 2 n)) : z (C.port (.inr (.inl j))) = k.val.testBit j.val := by
      rw [← he, test_number]
      rfl
    exact ⟨fun hb => ⟨h.1, ht, fun j hj => hb ⟨j, hj⟩⟩, fun hb j => hb.2.2 j.val j.property⟩
  · contradiction

-- 读法：输入 `j` 时返回 `x (.inr (.inl j))`。
private def broadcast (x : Input N l) : Fin l → Bool := fun j => x (.inr (.inl j))

-- 读法：逐一匹配以下输入模式：`none, x`、`some k, x`。
private def step (f : Fin n → Input N l → F) : Option (Fin n) → Input N l → F
  | none, x => if ∀ j, x (.inr j) = false then 1 else 0
  | some k, x => if C.good k (broadcast x) then f k x else 0

-- 读法：`runAt` 的取值由 `C.step f (parse (broadcast x ∘ C.head)) x` 给出。
private def runAt (f : Fin n → Input N l → F) (x : Input N l) : F :=
  C.step f (parse (broadcast x ∘ C.head)) x

-- 读法：`C.runAt f (Sum.elim ξ (Sum.elim (fun _ => false) y))` 等于 `if y = (fun _ => false) then 1 else 0`。
private theorem runAt_zero (f : Fin n → Input N l → F) (ξ : Fin l → Bool) (y : Fin (N / 4) → Bool) :
    C.runAt f (Sum.elim ξ (Sum.elim (fun _ => false) y)) =
      if y = (fun _ => false) then 1 else 0 := by
  simp [runAt, broadcast, parse, step, funext_iff]

-- 读法：`C.runAt f (Sum.elim (C.code (some (i, c))) (Sum.elim z y))` 等于 `C.run i c z y`。按 `z = fun _ => false` 成立与否分情况。
private theorem runAt_eq (f : Fin n → Input N l → F) (hf : ∀ k, C.Handles k (f k))
    (i : Fin (3 * r)) (c : M.Bits F → Bool) (z : Fin l → Bool) (y : Fin (N / 4) → Bool) :
    C.runAt f (Sum.elim (C.code (some (i, c))) (Sum.elim z y)) = C.run i c z y := by
  by_cases hz : z = fun _ => false
  · have he : C.reportCode none = z := (funext (A.encodeReport_none hn N r _ l C.fits)).trans hz.symm
    rw [hz, runAt_zero, ← hz, ← he, run, Machine.branch, C.reportCode.injective.extend_apply]
    rfl
  change C.step f (parse (z ∘ C.head)) _ = _
  by_cases hvalid : ∃ R : P.Reports A hn B, A.feasible hn R.val ∧ C.reportCode (some R) = z
  · obtain ⟨R, hR, rfl⟩ := hvalid
    have hp := C.parse_report R
    have hg := (C.good_iff _ _ hp).mpr ⟨R, hR, rfl, rfl⟩
    rw [hp, run, Machine.branch, C.reportCode.injective.extend_apply]
    change (if C.good R.val.1 (C.reportCode (some R)) then _ else _) = C.site i c R y
    rw [ite_eq_left hg]
    exact hf _ i c R y rfl hR
  · rw [C.run_invalid i c z y hz (fun R h he => hvalid ⟨R, h, he⟩)]
    cases hp : parse (z ∘ C.head) with
    | none =>
      unfold step
      exact ite_eq_right (fun h => hz (funext (fun j => h (.inl j))))
    | some k =>
      have hh : ¬ C.good k z := by
        rintro h
        obtain ⟨R, hR, _, he⟩ := (C.good_iff z k hp).mp h
        exact hvalid ⟨R, hR, he⟩
      exact ite_eq_right hh

-- 读法：要证明的命题是 `Weight F (C.step f s) (g + m + 50 * (l + l + N / 4 + 1))`。对 `s` 分类讨论。
private theorem step_net (f : Fin n → Input N l → F)
    (hg : ∀ k, Weight F (fun x : A.CountBit r (B * P.count) → Bool => if A.guard hn k x then 1 else 0) g)
    (hf : ∀ k, Weight F (f k) m) (s : Option (Fin n)) :
    Weight F (C.step f s) (g + m + 50 * (l + l + N / 4 + 1)) := by
  let I := Machine.Ports N l l
  have hI : Fintype.card I = l + l + N / 4 := by simp [I, Machine.Ports, Nat.add_assoc]
  cases s with
  | none =>
    have h := pin_net (F := F) (Sum.inr : Fin l ⊕ Fin (N / 4) → I)
    apply h.mono
    rw [hI, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  | some k =>
    -- 推导：记下中间结论 `pads`：`C.Pad → I`。
    let pads : C.Pad → I := fun j => .inr (.inl j.val)
    let counts : A.CountBit r (B * P.count) → I := fun j => .inr (.inl (C.port (.inr (.inr j))))
    have hp : Fintype.card C.Pad ≤ l := by
      exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin l)
    have hc : Fintype.card (A.CountBit r (B * P.count)) ≤ Fintype.card I := by
      apply Fintype.card_le_of_injective counts
      intro i j he
      exact Sum.inr.inj (Sum.inr.inj (C.port.injective (Sum.inl.inj (Sum.inr.inj he))))
    have hw := (pin_net (F := F) pads).mul (((hg k).pull counts).mul (hf k))
    convert hw.mono (n := g + m + 50 * (l + l + N / 4 + 1)) (by rw [hI] at hc ⊢; omega) using 1
    funext x
    simp only [step, good, ite_mul, one_mul, zero_mul, broadcast, pads]
    by_cases hpad : ∀ j : C.Pad, x (.inr (.inl j.val)) = false
    · simp only [hpad, implies_true, true_and, ite_true]; rfl
    · simp only [hpad, false_and, ite_false]

-- 读法：`dispatchCost` 的取值由 `100 * (1 + Weight.switchCost (1 + Nat.clog 2 n))` 给出。
def dispatchCost (n : ℕ) := 100 * (1 + Weight.switchCost (1 + Nat.clog 2 n))

-- 读法：存在 `U v`，`C.Agrees U` 与 `Net F (Machine.tape N l l) .unit U v ∧ v ≤ dispatchCost n * (g + m + (l + l + N / 4) + 1)` 同时成立。这里调用 `hs.pull`。
/-- 只有固定切口的各站点计算及计数检查需要单独估计成本。其余控制与引脚检验的成本都是线性的。

英文原文：Only the fixed-cut site computations and the count guard need their
own cost estimates. The other control and pin tests are linear.
-/
theorem dispatch
    (hg : ∀ k, Weight F (fun x : A.CountBit r (B * P.count) → Bool => if A.guard hn k x then 1 else 0) g)
    (hf : ∀ k, ∃ f, Weight F f m ∧ C.Handles k f) :
    ∃ U v, C.Agrees U ∧ Net F (Machine.tape N l l) .unit U v ∧
      v ≤ dispatchCost n * (g + m + (l + l + N / 4) + 1) := by
  choose f hm hsite using hf
  let I := Machine.Ports N l l
  let addr : Header n ⊕ I → I := Sum.elim (fun i => .inr (.inl (C.head i))) id
  have hs := Weight.switch (fun s => C.step f (parse s)) (fun s => C.step_net f hg hm (parse s))
  have hrun : Weight F (C.runAt f) (dispatchCost n * (g + m + (l + l + N / 4) + 1)) := by
    apply (hs.pull addr).mono
    -- 推导：记下中间结论 `hi`：`Fintype.card I = l + l + N / 4`。
    have hi : Fintype.card I = l + l + N / 4 := by simp [I, Machine.Ports, Nat.add_assoc]
    have hh : 1 + Nat.clog 2 n ≤ l := by have := C.fits; omega
    simp only [Header, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    unfold dispatchCost
    ring_nf
    omega
  obtain ⟨v, hv, net⟩ := hrun (Machine.tape N l l) (Machine.address N l l).symm
  refine ⟨_, v, ?_, net, hv⟩
  have he (ξ z : Fin l → Bool) (y : Fin (N / 4) → Bool) :
      bits (Machine.tape N l l) (Machine.feed ξ z y) ∘ (Machine.address N l l).symm =
        Sum.elim ξ (Sum.elim z y) := by
    funext j
    rw [Function.comp_apply, Machine.bits_feed, Equiv.apply_symm_apply]
  constructor
  · simp only [pad, he, runAt_zero, ite_true]
  · intro i c z y
    simpa only [he] using C.runAt_eq f hsite i c z y

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

section
/-!
# 将控制器的估计与被模拟的网络分开

输入长度一经固定，控制器就不再以图式、网络或顶点表为参数。本文件将对角处理器的实现归结为对该控制器规模的估计。

**英文原文**

Separating the controller estimate from the network being simulated

After fixing the input length the controller has no diagram, network
or vertex tables as parameters. This file reduces implementation of
the diagonal processor to a size estimate for that controller.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Machine Filter

variable {F : Type} [Field F] [Fintype F]

-- 读法：`ControlBound` 的结果类型为 `Prop`。
/-- 控制器围绕一组规模固定的模板解释器执行报告处理与布线操作。

英文原文：The controller carries out the report and wiring operations around
a fixed-size bank of template interpreters.
-/
def ControlBound (F : Type) [Field F] [Fintype F] : Prop :=
  ∀ n h C Q : ℕ, ∀ hn : 2 ≤ n, 0 < h → 4 ≤ C → ∀ A : Expansion F n h,
    ∃ k : ℕ, ∀ᶠ w : ℕ in atTop,
      let N := 2 ^ w
      let r := 2 ^ (w / (16 * n))
      let d := 2 ^ (w / (32 * n))
      let l := N / 2048
      let B := (3 * r + d - 1) / d
      ∀ fa : Machine.Ports N l l → Label n r,
        (∀ z, multiplicity fa z * r ^ n ≤ 4 * N) →
        (∀ i g, multiplicity (fun t : Fin l => fa (.inl t) i) g * r ≤ 2 * l) →
        let P := Format.prescribed d h (rounds n r h (12 * (C * N * d))) fa
        ∀ M : Bank (Fin n), M.budget F ≤ N * w ^ Q → r ^ n ≤ C * N * d →
          (∀ i, 100 * C * N * d ≤ 2 ^ M.width i * r) →
          Nonempty (Controller P A hn M B) →
          ∃ (S : Controller P A hn M B) (U : Val (tape N l l) → Val .unit → F) (v : ℕ),
            S.Agrees U ∧ Net F (tape N l l) .unit U v ∧ v ≤ N * w ^ k

-- 读法：要证明的命题是 `Programmable F (Cheap F K q)`。
theorem programmable_of_control (hctrl : ControlBound F) (K q : ℕ) :
    Programmable F (Cheap F K q) := by
  intro C hC n h hn hh A
  obtain ⟨k, hk⟩ := hctrl n h C (q + 8) hn hh hC A
  obtain ⟨δ, _, hs⟩ := Diagonal.scales C n h (Fintype.card A.I) hC hn
  refine ⟨k, ?_⟩
  filter_upwards [hk, hs, scales F n (1000000 * C) K q hn, eventually_ge_atTop (64 * n)] with w ctrl sc hb hw
  let N := 2 ^ w
  let r := 2 ^ (w / (16 * n))
  let d := 2 ^ (w / (32 * n))
  let l := N / 2048
  let B := (3 * r + d - 1) / d
  have ⟨hd, hd', _⟩ := batch_floor w n
  have s : Diagonal.Scales C n h (Fintype.card A.I) N r l l d 0 B :=
    sc.2 d 0 hd hd' (by simp)
  -- 推导：记下中间结论 `hr`：`16 ≤ r`。
  have hr : 16 ≤ r := by
    have ht : 4 ≤ w / (16 * n) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact Nat.pow_le_pow_right (n := 2) (by decide) ht
  obtain ⟨M, hm, hbit, hspec⟩ := hb
  have hl : 1 + 3 * r + Fintype.card (M.Bits F) ≤ l := by
    have hsq : r ^ 2 ≤ l := (Nat.pow_le_pow_right (by omega) hn).trans s.labels
    have hlin : 2 * (1 + 3 * r) ≤ l := by nlinarith
    change Fintype.card (M.Bits F) ≤ l / 2 at hbit
    omega
  have hsize : r ^ n ≤ C * N * d :=
    s.labels.trans ((by omega : l ≤ N).trans
      ((Nat.le_mul_of_pos_left N (by omega : 0 < C)).trans (Nat.le_mul_of_pos_right _ hd)))
  -- 推导：记下中间结论 `hwidth`：`∀ i, 1000000 * C * N * d * rate K q (N + 2) ≤ 2 ^ M.width i * r`。
  have hwidth : ∀ i, 1000000 * C * N * d * rate K q (N + 2) ≤ 2 ^ M.width i * r := by
    intro i
    rw [rate, show 1 + (N + 2) = N + 3 by omega]
    exact (hspec i).1
  have hrepeat (i : Fin n) : B ≤ 2 ^ M.repetitions i :=
    (Nat.mul_le_mul_right_iff hd).mp (s.copies.trans (by rw [mul_comm _ d]; exact (hspec i).2))
  intro fa hf hf'
  let P := Format.prescribed d h (rounds n r h (12 * (C * N * d))) fa
  by_cases hex : Nonempty (Controller P A hn M B)
  · have hroom (i : Fin n) : 100 * C * N * d ≤ 2 ^ M.width i * r := by
      calc
        _ ≤ 1000000 * C * N * d := by gcongr; decide
        _ ≤ 1000000 * C * N * d * rate K q (N + 2) := Nat.le_mul_of_pos_right _ (by unfold rate; omega)
        _ ≤ _ := hwidth i
    -- 推导：从 `ctrl fa hf hf' M hm hsize hroom hex` 中取出 `S, U, v, hu, hnet, hv`。
    obtain ⟨S, U, v, hu, hnet, hv⟩ := ctrl fa hf hf' M hm hsize hroom hex
    refine ⟨U, S.pad, v, hu.1, hnet, hv, ?_⟩
    intro _ D hD G _ had T hcol ht hc hcode
    exact S.programs T (Format.ofScheme_eq T hcol ht) had
      (bill_bound T M hc hD s.pos hsize hwidth) hrepeat hcode U hu
  · obtain ⟨v, hv, hnet⟩ := DNet.discard F (tape N l l)
    let pad := (bits (tape N l l)).symm (fun _ => false)
    refine ⟨fun _ _ => 1, pad, v, rfl, hnet, ?_, ?_⟩
    · rw [wd_word] at hv
      exact (hv.trans s.tape).trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0 < w) _))
    · intro _ D hD G _ _ T hcol ht hc hcode
      have he := controller_exists T M hcode hl (bill_bound T M hc hD s.pos hsize hwidth)
      rw [Format.ofScheme_eq T hcol ht] at he
      exact (hex he).elim

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# 在对角尺度上估计分派开销的上界

站点实现只需处理某个固定切口下的可行广播。分派器检查全部公开条件，并处理格式有误的广播和单独的单位元分支。

**英文原文**

Bounding the overhead of dispatch at the diagonal scale

Only feasible broadcasts at one fixed cut have to be supplied by
the site implementation. The dispatcher checks all public conditions
and handles malformed broadcasts and the separate unit branch.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Filter
variable {F : Type} [Field F] [Fintype F] {n h : ℕ}

-- 读法：这里调用 `Nat.pow_le_pow_right`。
private theorem packet_count (w n C h : ℕ) (hn : 2 ≤ n) (hw : 12 * C + 8 ≤ w) :
    let N := 2 ^ w
    let r := 2 ^ (w / (16 * n))
    let d := 2 ^ (w / (32 * n))
    let B := (3 * r + d - 1) / d
    r ^ 6 ≤ N ∧ Fintype.card (Packet n r (B * rounds n r h (12 * (C * N * d)))) < N ^ 8 := by
  intro N r d B
  have hw' : w < N := Nat.lt_two_pow_self
  have hr : 0 < r := by unfold r; positivity
  have ht (j : ℕ) (hj : j ≤ 16 * n) : r ^ j ≤ N := by
    unfold r N
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide)
      ((Nat.mul_le_mul_left _ hj).trans (Nat.div_mul_le_self w _))
  -- 推导：记下中间结论 `hrN`：`r ≤ N`。
  have hrN : r ≤ N := by simpa using ht 1 (by omega)
  have hdN : d ≤ N := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.div_le_self w _)
  have hb : B ≤ N ^ 2 := by
    have hb' : B ≤ 3 * r + d := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    nlinarith
  have hg : rounds n r h (12 * (C * N * d)) ≤ N ^ 3 := by
    unfold rounds
    calc
      _ ≤ (12 * C) * N * d + 1 := by rw [← mul_assoc, ← mul_assoc]; exact Nat.add_le_add_right (Nat.div_le_self _ _) 1
      _ ≤ (12 * C) * N * N + N * N := by gcongr; nlinarith
      _ = (12 * C + 1) * N * N := by ring
      _ ≤ N ^ 3 := by rw [pow_succ, pow_two]; gcongr; omega
  refine ⟨ht 6 (by omega), ?_⟩
  simp only [Packet, Template, Label, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  calc
    _ ≤ N * N * (N ^ 2 * N ^ 3) := by have := ht n (by omega); gcongr
    _ = N ^ 7 := by ring
    _ < N ^ 8 := Nat.pow_lt_pow_right (by omega) (by decide)

-- 读法：证明中先建立 `he`，即 `A.cross s i ≤ t`。
theorem dispatch_scale (A : Expansion F n h) (hn : 2 ≤ n) (C k : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      let N := 2 ^ w
      let r := 2 ^ (w / (16 * n))
      let d := 2 ^ (w / (32 * n))
      let l := N / 2048
      let B := (3 * r + d - 1) / d
      ∀ (fa : Machine.Ports N l l → Label n r) (M : Bank (Fin n)),
        let P := Format.prescribed d h (rounds n r h (12 * (C * N * d))) fa
        ∀ S : Controller P A hn M B,
          (∀ i, ∃ f, Install.Weight F f (N * w ^ k) ∧ S.Handles i f) →
          ∃ (U : Val (Machine.tape N l l) → Val .unit → F) (v : ℕ),
            S.Agrees U ∧ Net F (Machine.tape N l l) .unit U v ∧ v ≤ N * w ^ (max k 5 + 1) := by
  classical
  let c := Controller.dispatchCost n
  let t := ∑ s, ∑ i, A.cross s i
  filter_upwards [eventually_ge_atTop (100000000 + n + 12 * C + 8 + Fintype.card A.I + t + 6 * c)] with w hw
  intro N r d l B fa M P S hsite
  have hc (s) (i) : A.cross s i ≤ w := by
    -- 推导：记下中间结论 `he`：`A.cross s i ≤ t`。
    have he : A.cross s i ≤ t := le_trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      (Finset.single_le_sum (f := fun s => ∑ i, A.cross s i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
    omega
  have ⟨hr, hcount⟩ := packet_count w n C h hn (by omega)
  obtain ⟨U, v, hu, hnet, hv⟩ := S.dispatch
    (A.guard_size hn w (by omega) (by omega) (by omega) hc (by positivity) hr hcount) hsite
  refine ⟨U, v, hu, hnet, hv.trans ?_⟩
  have hw' : 0 < w := by omega
  let m := N * w ^ (max k 5)
  have hb (i : ℕ) (hi : i ≤ max k 5) : N * w ^ i ≤ m :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hw' hi)
  have h₁ := hb 5 (le_max_right k 5)
  have h₂ := hb k (le_max_left k 5)
  -- 推导：记下中间结论 `h₃`：`N ≤ m`。
  have h₃ : N ≤ m := Nat.le_mul_of_pos_right _ (by positivity)
  have : 0 < N := by unfold N; positivity
  calc
    _ ≤ c * (6 * m) := by apply Nat.mul_le_mul_left; change N * w ^ 5 + _ + _ + _ ≤ _; omega
    _ = (6 * c) * m := by ring
    _ ≤ w * m := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by unfold m; rw [pow_succ]; ring

end OAI.LinearAlgebra.MatrixExponent.Processor
end
