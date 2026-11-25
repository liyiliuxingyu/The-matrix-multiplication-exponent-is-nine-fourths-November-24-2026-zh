-- 本文件所属证明环节：给控制器计算留下的地址、调用、匹配和恢复记录分配编码，检验记录的一致性与唯一性，并估计验证开销。
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Packets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# 对处理器记录进行无重数编码

只有在执行记录被接受时才要求它满足总量界和逐点界。未使用的槽位具有预先指定的内容。

**英文原文**

Encoding processor records without multiplicity

A transcript need only satisfy the aggregate and pointwise bounds when
it is accepted. The unused slots have prescribed contents.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript
open Finset Classical

variable {P V k : ℕ} {R : Type}

-- 读法：`readRecord` 的取值由 `Fin.lastCases none (fun p => some (p, x p))` 给出。
def readRecord (x : Fin P → R) : Fin (P + 1) → Option (Fin P × R) :=
  Fin.lastCases none (fun p => some (p, x p))

-- 读法：逐一匹配以下输入模式：`none`、`some (p, _)`。
def name : Option (Fin P × R) → Fin (P + 1)
  | none => Fin.last P
  | some (p, _) => p.castSucc

-- 读法：`name (readRecord x p)` 等于 `p`。
@[simp] theorem name_read (x : Fin P → R) (p : Fin (P + 1)) : name (readRecord x p) = p := by
  induction p using Fin.lastCases <;> simp [name, readRecord]

-- 读法：在后续公式中，`Records` 是 `Slot P V k → Option (Fin P × R)` 的缩写。
abbrev Records (P V k : ℕ) (R : Type) := Slot P V k → Option (Fin P × R)

-- 读法：`Encodes` 表示以下条件：`(∀ j : Fin (k + 1), OrderedSeats (bucket (fun p => c p (x p)) j.val) (fun s => name (y ⟨j, s⟩))) ∧ ∀ s, y s = readRecord x (name (y s))`。
/-- 各非空位置的计费量和有效载荷均正确。非活动位置不承载有效载荷。

英文原文：All occupied positions have the right charge and payload. An inactive
position carries no payload.
-/
def Encodes (c : Fin P → R → ℕ) (x : Fin P → R) (y : Records P V k R) : Prop :=
  (∀ j : Fin (k + 1), OrderedSeats (bucket (fun p => c p (x p)) j.val)
    (fun s => name (y ⟨j, s⟩))) ∧
  ∀ s, y s = readRecord x (name (y s))

-- 读法：存在唯一的 `y : Records P V k R`，要证明的命题是 `Encodes c x y`。用函数外延性比较等号两侧在 `⟨j, t⟩` 处的取值。
theorem unique_encoding (c : Fin P → R → ℕ) (x : Fin P → R)
    (hp : ∀ i, 0 < c i (x i)) (hs : ∑ i, c i (x i) ≤ V) :
    ∃! y : Records P V k R, Encodes c x y := by
  have h (j : Fin (k + 1)) := unique_seats _ (bucket_capacity hp hs j)
  let y : Records P V k R := fun s => readRecord x ((h s.1).choose s.2)
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · intro j; simpa only [y, name_read] using (h j).choose_spec.1
  · intro s; simp only [y, name_read]
  · intro z hz
    funext ⟨j, t⟩
    rw [hz.2]
    have he := (h j).choose_spec.2 _ (hz.1 j)
    exact congrArg (readRecord x) (congrFun he t)

-- 读法：存在 `s : Slot P V k`，`y s` 等于 `some (p, x p)`。
theorem Encodes.covers {c : Fin P → R → ℕ} {x : Fin P → R} {y : Records P V k R}
    (h : Encodes c x y) (hc : ∀ i, c i (x i) ≤ 2 ^ k) (p : Fin P) :
    ∃ s : Slot P V k, y s = some (p, x p) := by
  have hp : Nat.clog 2 (c p (x p)) ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr (hc p)
  let j : Fin (k + 1) := ⟨_, Nat.lt_succ_of_le hp⟩
  obtain ⟨i, hi⟩ := ((h.1 j).2.1 p).mpr (by simp [bucket, j])
  refine ⟨⟨j, i⟩, ?_⟩
  change name (y ⟨j, i⟩) = p.castSucc at hi
  rw [h.2, hi]; simp [readRecord]

-- 读法：`x` 等于 `z`。用函数外延性比较等号两侧在 `p` 处的取值。
theorem Encodes.unique {c : Fin P → R → ℕ} {x z : Fin P → R} {y : Records P V k R}
    (h : Encodes c x y) (hc : ∀ i, c i (x i) ≤ 2 ^ k) (hz : Encodes c z y) : x = z := by
  funext p
  obtain ⟨s, he⟩ := h.covers hc p
  have ht := hz.2 s
  simpa [he, name, readRecord] using ht

-- 读法：结论为 `∑ y, g y = ∑ x, if good x then f x else 0`。按 `∃ x, good x ∧ Encodes c x y` 成立与否分情况。
/-- 若见证关系为双射，则在任意特征下都保持加权和。被拒绝的配置可以有任意长度。

英文原文：A bijective witness relation preserves a weighted sum in all
characteristics. Rejected configurations can have arbitrary lengths.
-/
theorem encode_sum {F : Type} [AddCommMonoid F] [Fintype R]
    (c : Fin P → R → ℕ) (good : (Fin P → R) → Prop) (f : (Fin P → R) → F)
    (g : Records P V k R → F)
    (bounds : ∀ x, good x → (∀ i, 0 < c i (x i) ∧ c i (x i) ≤ 2 ^ k) ∧ ∑ i, c i (x i) ≤ V)
    (match_value : ∀ x y, good x → Encodes c x y → g y = f x)
    (reject : ∀ y, (¬∃ x, good x ∧ Encodes c x y) → g y = 0) :
    ∑ y, g y = ∑ x, if good x then f x else 0 := by
  have row (y : Records P V k R) :
      g y = ∑ x, if good x ∧ Encodes c x y then f x else 0 := by
    by_cases h : ∃ x, good x ∧ Encodes c x y
    -- 推导：从 `h` 中取出 `x, hx, he`。
    · obtain ⟨x, hx, he⟩ := h
      have hu (z) : good z ∧ Encodes c z y ↔ z = x :=
        ⟨fun hz => (he.unique (fun i => ((bounds x hx).1 i).2) hz.2).symm,
          fun ez => ez.symm ▸ And.intro hx he⟩
      simp only [hu, sum_ite_eq', mem_univ, ite_true]
      exact match_value x y hx he
    · rw [reject y h]
      simp only [not_exists] at h
      simp only [h, ite_false, sum_const_zero]
  simp_rw [row]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : good x
  -- 推导：从 `bounds x hx` 中取出 `hp, hs`。
  · obtain ⟨hp, hs⟩ := bounds x hx
    obtain ⟨y, hy, hu⟩ := unique_encoding (k := k) c x (fun i => (hp i).1) hs
    have hz (z) : Encodes c x z ↔ z = y := ⟨hu z, fun e => e.symm ▸ hy⟩
    simp only [hx, true_and, hz, sum_ite_eq', mem_univ, ite_true]
  · simp only [hx, false_and, ite_false, sum_const_zero]

end OAI.LinearAlgebra.MatrixExponent.Transcript
end

section
/-!
# 经数据包通信连接局部加权检验

每张记录表都为猜测、辅助信息和消息记录设置固定位置。非活跃记录携带互不相同的占位标识。局部因子可以包含已实现的子网络或单个字典表项。对消息带只执行一次全局检查。

**英文原文**

Connecting local weighted checks by packet communication

A sheet has fixed positions for guesses, advice, and message records.
Inactive records carry distinct dummy identifiers. The local factors
may include previously realized subnetworks or individual dictionary
entries. There is a single global check on the message tapes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript

-- 读法：结构的字段包括 `privateBits`、`I`、`port`、`data`、`read`。
structure Sheet (K : Type) (x y : Wire) (j H w : ℕ) where
  privateBits : Wire
  I : Type
  [finite : Fintype I]
  port : I → Wire
  data : ∀ i, Val (port i) → K
  read : ∀ i, slots (port i) → slots (.pair (.pair x y) privateBits)
  messages : slots (tree j (Messages.row H w)) → slots (.pair (.pair x y) privateBits)

attribute [instance] Sheet.finite

noncomputable section
namespace Sheet
open Classical

variable {K : Type} [Field K] {a b : Wire} {j H w : ℕ} (S : Sheet K a b j H w)

-- 读法：`eval` 的结果类型为 `K`。
def eval (x : Val a) (y : Val b) : K :=
  ∑ z : Val S.privateBits,
    if Messages.valid j H w (Install.project S.messages ((x, y), z))
    then ∏ i, S.data i (Install.project (S.read i) ((x, y), z)) else 0

-- 读法：`volume` 的取值由 `wd a + wd b + wd S.privateBits + ∑ i, cost i` 给出。
def volume (cost : S.I → ℕ) :=
  wd a + wd b + wd S.privateBits + ∑ i, cost i

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
private def allPorts : Option S.I → Wire
  | none => tree j (Messages.row H w)
  | some i => S.port i

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
private def allData : (i : Option S.I) → Val (S.allPorts i) → K
  | none => fun x => if Messages.valid j H w x then 1 else 0
  | some i => S.data i

-- 读法：逐一匹配以下输入模式：`none`、`some i`。
private def allReads : (i : Option S.I) → slots (S.allPorts i) → slots (.pair (.pair a b) S.privateBits)
  | none => S.messages
  | some i => S.read i

-- 读法：`∃ s` 不超过 `9 * S.volume cost + 36 * (m + 10000 * 2 ^ j * (w + (1 + H) * (j + 1) ^ 2)), Wide K r L a b S.eval s`。对 `i` 分类讨论。
theorem build {F : Type} [Field F] [Algebra F K] {r m : ℕ} {L : Set (Table K)}
    (hr : 3 ≤ r) (tag : Radix.Tag F j (H + w + 2) m) (cost : S.I → ℕ)
    (localChecks : ∀ i, ∃ s ≤ cost i, Wide K r L (S.port i) .unit (fun x _ => S.data i x) s) :
    ∃ s ≤ 9 * S.volume cost + 36 * (m + 10000 * 2 ^ j * (w + (1 + H) * (j + 1) ^ 2)),
      Wide K r L a b S.eval s := by
  obtain ⟨n, hn, check⟩ := Messages.net tag
  let t : Option S.I → ℕ := fun i => i.elim (4 * n) cost
  have factors (i : Option S.I) :
      ∃ s ≤ t i, Wide K r L (S.allPorts i) .unit (fun x _ => S.allData i x) s := by
    cases i with
    | some i => exact localChecks i
    | none =>
      have hm := check.map (algebraMap F K)
      simp only [apply_ite (algebraMap F K), map_one, map_zero] at hm
      exact hm.includeWide hr
  -- 推导：从 `wide S.allPorts S.allData t S.allReads hr factors` 中取出 `s, hs, hw`。
  obtain ⟨s, hs, hw⟩ := wide S.allPorts S.allData t S.allReads hr factors
  refine ⟨s, ?_, ?_⟩
  · rw [Fintype.sum_option] at hs
    dsimp [volume, t] at hs ⊢
    omega
  · have he : value S.allPorts S.allData S.allReads = S.eval := by
      funext x y
      unfold value eval
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Fintype.prod_option]
      simp only [allPorts, allData, allReads]
      split_ifs <;> simp_all only [ite_true, ite_false, one_mul, zero_mul]
    rwa [he] at hw

end Sheet
end
end OAI.LinearAlgebra.MatrixExponent.Transcript
end

section
/-!
# 固定执行记录的通信成本

取高度的一个足够大的幂，以同时满足宽记录路由估计和对报头进行普通排序的需求。局部的多对数损失以及路由所耗费的很小的幂次，都可容纳在任意给定的正余量内。

**英文原文**

Cost of fixed transcript communication

Choose a power of the height large enough for the wide-record routing
estimate and the ordinary sort of the headers. Local polylogarithmic
losses and a small power spent on routing fit within any positive slack.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Sheet
open Filter

-- 读法：结论为 `let w := h ^ (2 * A + 6) j ^ A ≤ H + w + 2 ∧ H + w + 2 ≤ 4 * w ∧ w + (1 + H) * (j + 1) ^ 2 ≤ 9 * w`。
private theorem widths (A h j H : ℕ) (hh : 1 ≤ h) (hj : j ≤ h ^ 2) (hH : H ≤ h ^ 2) :
    let w := h ^ (2 * A + 6)
    j ^ A ≤ H + w + 2 ∧ H + w + 2 ≤ 4 * w ∧ w + (1 + H) * (j + 1) ^ 2 ≤ 9 * w := by
  let w := h ^ (2 * A + 6)
  have hw : h ^ 6 ≤ w := pow_le_pow_right₀ hh (by omega)
  have h2 : 1 ≤ h ^ 2 := one_le_pow₀ hh
  have h6 : h ^ 2 ≤ h ^ 6 := pow_le_pow_right₀ hh (by decide)
  have hscale : j ^ A ≤ w := calc
    _ ≤ (h ^ 2) ^ A := Nat.pow_le_pow_left hj _
    _ ≤ _ := by rw [← pow_mul]; exact pow_le_pow_right₀ hh (by omega)
  have hheads : (1 + H) * (j + 1) ^ 2 ≤ 8 * w := calc
    _ ≤ (2 * h ^ 2) * (2 * h ^ 2) ^ 2 := by gcongr <;> omega
    _ = 8 * h ^ 6 := by ring
    _ ≤ 8 * w := Nat.mul_le_mul_left _ hw
  change j ^ A ≤ H + w + 2 ∧ H + w + 2 ≤ 4 * w ∧ w + (1 + H) * (j + 1) ^ 2 ≤ 9 * w
  omega

-- 读法：对每个 `ᶠ h : ℕ in atTop`，`C * (h : ℝ) ^ (2 * ζ) * (Real.log h) ^ q` 不超过 `(h : ℝ) ^ τ`。
private theorem eventually_small {τ ζ : ℝ} (hz : 2 * ζ < τ) (q : ℕ) (C : ℝ) :
    ∀ᶠ h : ℕ in atTop, C * (h : ℝ) ^ (2 * ζ) * (Real.log h) ^ q ≤ (h : ℝ) ^ τ := by
  have he := (isLittleO_log_rpow_rpow_atTop (q : ℝ) (sub_pos.mpr hz)).const_mul_left C
  filter_upwards [eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually he.eventuallyLE] with h hh hb
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  rw [Real.rpow_natCast, Real.norm_of_nonneg (Real.rpow_nonneg hh'.le _)] at hb
  calc
    _ = C * (Real.log h) ^ q * (h : ℝ) ^ (2 * ζ) := by ring
    _ ≤ (h : ℝ) ^ (τ - 2 * ζ) * (h : ℝ) ^ (2 * ζ) :=
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans hb) (by positivity)
    _ = _ := by rw [← Real.rpow_add hh', sub_add_cancel]

-- 读法：证明中先建立 `hz`，即 `0 < ζ`。
/-- 先确定分块宽度和处理器额外开销，再确定局部对数因子的指数。后者可影响阈值，但不会进入处理器数的多项式指数。

英文原文：Fix the chunk width and processor overhead before fixing the exponent on
local logarithmic factors. In particular, the latter can affect the threshold
but cannot enter the polynomial exponent on the number of processors.
-/
theorem realizes {F : Type} [Field F] (wide : Radix.WideTag F)
    {τ : ℝ} (hτ : 0 < τ) (c : ℕ) :
    ∃ A C₀ : ℕ, 1 < A ∧ ∀ q : ℕ, ∀ᶠ h : ℕ in atTop,
    ∀ (K : Type) [Field K] [Algebra F K] (x y : Wire) (P V j H r : ℕ) (L : Set (Table K))
      (S : Sheet K x y j H (h ^ A)) (cost : S.I → ℕ),
      1 ≤ j → j ≤ h ^ 2 → H ≤ h ^ 2 → 3 ≤ r →
      (∀ i, ∃ s ≤ cost i, Wide K r L (S.port i) .unit (fun t _ => S.data i t) s) →
      (S.volume cost + 2 ^ j * h ^ A : ℕ) ≤ (Real.log h) ^ q * (V + (P : ℝ) * h ^ (A + c)) →
      ∃ s, Wide K r L x y S.eval s ∧ (s : ℝ) ≤ (h : ℝ) ^ τ * V + P * (h : ℝ) ^ C₀ := by
  let ζ := min τ 1 / 4
  -- 推导：记下中间结论 `hz`：`0 < ζ`。
  have hz : 0 < ζ := by unfold ζ; positivity
  have hz' : 2 * ζ < min τ 1 := by unfold ζ; linarith [lt_min hτ (by norm_num : (0 : ℝ) < 1)]
  obtain ⟨B, _, C, ht⟩ := wide ζ hz
  have hc : 0 ≤ C := by
    obtain ⟨m, _, hb⟩ := ht 1 1 le_rfl (by simp)
    norm_num at hb
    linarith [Nat.cast_nonneg (α := ℝ) m]
  let A := 2 * B + 6
  let D := 9 + 36 * (4 * C + 90000)
  have hd : 0 < D := by unfold D; positivity
  refine ⟨A, A + c + 1, by unfold A; omega, fun q => ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_small hz' q D]
    with h hh hsmall K _ _ x y P V j H r L S cost hj hj' hH hr localChecks hvol
  let w := h ^ A
  -- 推导：记下中间结论 `hh'`：`1 ≤ (h : ℝ)`。
  have hh' : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  obtain ⟨hwidth, hdata, hheads⟩ := widths B h j H hh hj' hH
  obtain ⟨m, hm, hcost⟩ := ht j (H + w + 2) hj hwidth
  obtain ⟨s, hs, hsnet⟩ := S.build hr hm cost localChecks
  refine ⟨s, hsnet, ?_⟩
  let t := (h : ℝ) ^ (2 * ζ)
  have ht' : 1 ≤ t := Real.one_le_rpow hh' (by positivity)
  have hjz : (j : ℝ) ^ ζ ≤ t := calc
    _ ≤ ((h : ℝ) ^ 2 : ℝ) ^ ζ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hj') hz.le
    _ = _ := by unfold t; rw [← Real.rpow_natCast_mul (by positivity)]; norm_num
  let U : ℝ := 2 ^ j * w
  -- 推导：记下中间结论 `hU`：`0 ≤ U`。
  have hU : 0 ≤ U := by unfold U; positivity
  have hcm : (m : ℝ) ≤ 4 * C * U * t := calc
    _ ≤ C * (2 : ℝ) ^ j * (H + w + 2 : ℕ) * (j : ℝ) ^ ζ := hcost
    _ ≤ C * (2 : ℝ) ^ j * (4 * (w : ℝ)) * t := by gcongr; exact_mod_cast hdata
    _ = _ := by unfold U; ring
  have hcs : s ≤ 9 * S.volume cost + 36 * (m + 90000 * (2 ^ j * w)) := by
    refine hs.trans ?_
    rw [show 90000 * (2 ^ j * w) = 10000 * 2 ^ j * (9 * w) by ring]
    gcongr
  have hnet : (s : ℝ) ≤ 9 * (S.volume cost : ℝ) + 36 * ((m : ℝ) + 90000 * U) := by
    unfold U; exact_mod_cast hcs
  -- 推导：记下中间结论 `hst`：`(s : ℝ) ≤ D * t * ((S.volume cost : ℝ) + U)`。
  have hst : (s : ℝ) ≤ D * t * ((S.volume cost : ℝ) + U) := by
    have h1 : 9 ≤ D * t := by unfold D; nlinarith
    have h2 : 36 * (4 * C * t + 90000) ≤ D * t := by unfold D; nlinarith
    nlinarith only [hnet, hcm, mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) (S.volume cost)),
      mul_le_mul_of_nonneg_right h2 hU]
  calc
    _ ≤ D * t * ((S.volume cost : ℝ) + U) := hst
    _ ≤ D * t * ((Real.log h) ^ q * (V + (P : ℝ) * h ^ (A + c))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [U, w, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hvol
    _ ≤ (h : ℝ) ^ (min τ 1) * (V + (P : ℝ) * h ^ (A + c)) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ _ := by
      rw [mul_add, pow_succ, mul_comm ((h : ℝ) ^ (min τ 1)) ((P : ℝ) * _), mul_assoc]
      have h₁ := Real.rpow_le_rpow_of_exponent_le hh' (min_le_left τ 1)
      have h₂ := Real.rpow_le_rpow_of_exponent_le hh' (min_le_right τ 1)
      rw [Real.rpow_one] at h₂
      gcongr

end OAI.LinearAlgebra.MatrixExponent.Transcript.Sheet
end
