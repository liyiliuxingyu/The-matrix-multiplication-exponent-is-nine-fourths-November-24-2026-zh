-- 本文件所属证明环节：给不同处理器和独立副本分配地址、切口、信道和广播资源，把虚拟连线送上实际网络，控制由固定模板带来的额外开销。
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.AlphabetCode

section
/-!
# 通过完全互连的物理链路路由虚拟比特

一对端点间编号为 `i` 的比特经过处理器 `i % R`。若该处理器就是端点，则采用直接路径。每条物理链路的两个方向分别使用偶数和奇数位置。对给定端点，其余各端点获分配的商 `i/R` 区间两两不交。

**英文原文**

Routing virtual bits over complete physical links

Bit number `i` of a pair passes through processor `i % R`. If that
processor is an endpoint, the path is direct. The two orientations of
each physical link use even and odd positions. At a given endpoint,
each other endpoint is allotted a disjoint interval of quotients `i/R`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

open Finset
variable {R n : ℕ}

-- 读法：在后续公式中，`Link` 是 `{p : Fin R × Fin R // p.1 < p.2}` 的缩写。
abbrev Link (R : ℕ) := {p : Fin R × Fin R // p.1 < p.2}
-- 读法：在后续公式中，`Slot` 是 `Link R × Fin (n / (4 * R))` 的缩写。
abbrev Slot (R n : ℕ) := Link R × Fin (n / (4 * R))

-- 读法：`address` 的取值由 `Fin.castLE (by rw [← Nat.div_div_eq_div_mul]; exact Nat.mul_div_le _ _) (finProdFinEquiv (s.1.val.1 + s.1.val.2, s.2))` 给出。
/-- 按两个处理器的索引之和模 R 分类，至多得到 R 个匹配。共享比特的两个端点使用完全相同的地址。

英文原文：The sum of the two processor indices modulo R gives at most R
matchings. Both endpoints use the very same address for a shared bit.
-/
def address (s : Slot R n) : Fin (n / 4) :=
  Fin.castLE (by rw [← Nat.div_div_eq_div_mul]; exact Nat.mul_div_le _ _)
    (finProdFinEquiv (s.1.val.1 + s.1.val.2, s.2))

-- 读法：`s` 等于 `t`。按 `Prod.ext` 的外延性准则比较各分量。
theorem address_injective {s t : Slot R n} (u : Fin R)
    (hs : u = s.1.val.1 ∨ u = s.1.val.2) (ht : u = t.1.val.1 ∨ u = t.1.val.2)
    (h : address s = address t) : s = t := by
  have he : (s.1.val.1 + s.1.val.2, s.2) = (t.1.val.1 + t.1.val.2, t.2) :=
    finProdFinEquiv.injective (Fin.ext (congrArg (fun i : Fin (n / 4) => i.val) h))
  obtain ⟨he, hp⟩ := Prod.mk.inj he
  refine Prod.ext (Subtype.ext ?_) hp
  have h₁ := s.1.property
  have h₂ := t.1.property
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    simp [← hs, ← ht, add_comm] at he <;> apply Prod.ext <;> omega

-- 读法：在后续公式中，`Virtual` 是 `Σ p : Link R, Fin (q p.val.1 p.val.2)` 的缩写。
abbrev Virtual (q : Fin R → Fin R → ℕ) := Σ p : Link R, Fin (q p.val.1 p.val.2)

variable {q : Fin R → Fin R → ℕ}

-- 读法：`via` 的取值由 `⟨b.2.val % R, Nat.mod_lt _ b.1.val.1.pos⟩` 给出。
def via (b : Virtual q) : Fin R :=
  ⟨b.2.val % R, Nat.mod_lt _ b.1.val.1.pos⟩

-- 读法：在后续公式中，`Leg` 是 `Σ b : Virtual q, {u : Fin R // (u = b.1.val.1 ∨ u = b.1.val.2) ∧ u ≠ via b}` 的缩写。
/-- 每个端点到中间处理器各有一段链路，端点与中间处理器重合时省去该段。

英文原文：There is a leg from each endpoint to the intermediate processor,
except when they coincide.
-/
abbrev Leg (q : Fin R → Fin R → ℕ) :=
  Σ b : Virtual q, {u : Fin R // (u = b.1.val.1 ∨ u = b.1.val.2) ∧ u ≠ via b}

-- 读法：当 `l.2.val = l.1.1.val.1` 成立时取 `l.1.1.val.2`，否则取 `l.1.1.val.1`。
def other (l : Leg q) : Fin R :=
  if l.2.val = l.1.1.val.1 then l.1.1.val.2 else l.1.1.val.1

-- 读法：存在 `l : Leg q`，`l.1` 等于 `b`。按 `b.1.val.1 = via b` 成立与否分情况。
theorem has_leg (b : Virtual q) : ∃ l : Leg q, l.1 = b := by
  by_cases h : b.1.val.1 = via b
  · exact ⟨⟨b, b.1.val.2, .inr rfl, h ▸ b.1.property.ne'⟩, rfl⟩
  · exact ⟨⟨b, b.1.val.1, .inl rfl, h⟩, rfl⟩

-- 读法：`(l.2.val = l.1.1.val.1 ∧ other l = l.1.1.val.2)`、`(l.2.val = l.1.1.val.2 ∧ other l = l.1.1.val.1)` 至少有一项成立。
private theorem endpoints (l : Leg q) :
    (l.2.val = l.1.1.val.1 ∧ other l = l.1.1.val.2) ∨
    (l.2.val = l.1.1.val.2 ∧ other l = l.1.1.val.1) := by
  unfold other
  split
  · exact .inl ⟨by assumption, rfl⟩
  · exact .inr ⟨l.2.property.1.resolve_left (by assumption), rfl⟩

-- 读法：`l.1.2.val` 严格小于 `q l.2.val (other l)`。
private theorem index_lt (hs : ∀ u v, q u v = q v u) (l : Leg q) :
    l.1.2.val < q l.2.val (other l) := by
  rcases endpoints l with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h, h']; exact l.1.2.isLt
  · rw [h, h']; exact l.1.2.isLt.trans_eq (hs _ _)

-- 读法：`offset` 的取值由 `∑ z ∈ Iio v, (p z / R + 1)` 给出。
private def offset (p : Fin R → ℕ) (v : Fin R) : ℕ :=
  ∑ z ∈ Iio v, (p z / R + 1)

-- 读法：`offset p v + p v / R + 1` 不超过 `∑ z ∈ s, (p z / R + 1)`。
private theorem offset_le (p : Fin R → ℕ) (v : Fin R) (s : Finset (Fin R))
    (hs : ∀ z ≤ v, z ∈ s) :
    offset p v + p v / R + 1 ≤ ∑ z ∈ s, (p z / R + 1) := by
  have h : insert v (Iio v) ⊆ s := by
    intro z hz
    simp only [mem_insert, mem_Iio] at hz
    exact hs z (by omega)
  have hb := sum_le_sum_of_subset (f := fun z => p z / R + 1) h
  rw [sum_insert (by simp)] at hb
  unfold offset
  omega

-- 读法：`v = z` 与 `i / R = j / R` 同时成立。
private theorem offset_unique (p : Fin R → ℕ) {v z : Fin R} {i j : ℕ}
    (hi : i < p v) (hj : j < p z)
    (h : offset p v + i / R = offset p z + j / R) : v = z ∧ i / R = j / R := by
  have before (a b : Fin R) (hab : a < b) : offset p a + p a / R + 1 ≤ offset p b :=
    offset_le p a (Iio b) (fun _ hx => mem_Iio.mpr (lt_of_le_of_lt hx hab))
  have := Nat.zero_le (i / R)
  have := Nat.zero_le (j / R)
  rcases lt_trichotomy v z with hv | rfl | hv
  · have := before v z hv
    have := Nat.div_le_div_right (c := R) hi.le
    omega
  · exact ⟨rfl, Nat.add_left_cancel h⟩
  · have := before z v hv
    have := Nat.div_le_div_right (c := R) hj.le
    omega

-- 读法：`2 * (offset p v + i / R) + 1` 严格小于 `n / (4 * R)`。
private theorem capacity (p : Fin R → ℕ) (hp : ∑ v, p v ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)
    (v : Fin R) {i : ℕ} (hi : i < p v) :
    2 * (offset p v + i / R) + 1 < n / (4 * R) := by
  have hb : offset p v + i / R + 1 ≤ ∑ z, (p z / R + 1) := by
    have := offset_le p v univ (fun z _ => mem_univ z)
    have := Nat.div_le_div_right (c := R) hi.le
    omega
  have hd : (offset p v + i / R + 1) * R ≤ n / 64 + R ^ 2 := by
    calc
      _ ≤ (∑ z, (p z / R + 1)) * R := Nat.mul_le_mul_right R hb
      _ ≤ ∑ z, (p z + R) := by
        rw [sum_mul]
        apply sum_le_sum
        intro z _
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
      _ ≤ n / 64 + R ^ 2 := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]
        exact Nat.add_le_add_right hp _
  have hr := v.pos
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith only [hd, hn, Nat.div_mul_le_self n 64]

-- 读法：`link` 的结果类型为 `Link R`。
/-- 实际承载一段链路的无序处理器对。

英文原文：The actual unordered processor pair carrying a leg.
-/
def link (l : Leg q) : Link R :=
  if h : l.2.val < via l.1 then ⟨(l.2.val, via l.1), h⟩
  else ⟨(via l.1, l.2.val), lt_of_le_of_ne (le_of_not_gt h) l.2.property.2.symm⟩

-- 读法：`(u = (link l).val.1 ∨ u = (link l).val.2)` 与 `(u = l.2.val ∨ u = via l.1)` 等价。这里调用 `or_comm`。
theorem incident (l : Leg q) (u : Fin R) :
    (u = (link l).val.1 ∨ u = (link l).val.2) ↔ (u = l.2.val ∨ u = via l.1) := by
  unfold link
  split
  · rfl
  · exact or_comm

-- 读法：存在 `l : Leg q`，`l.1 = b` 与 `(u = (link l).val.1 ∨ u = (link l).val.2)` 同时成立。按 `u = via b` 成立与否分情况。
/-- 两个端点都能读取该比特，直接路径也包括在内。

英文原文：Both endpoints can read the bit, including on a direct path.
-/
theorem at_endpoint (b : Virtual q) (u : Fin R) (h : u = b.1.val.1 ∨ u = b.1.val.2) :
    ∃ l : Leg q, l.1 = b ∧ (u = (link l).val.1 ∨ u = (link l).val.2) := by
  by_cases he : u = via b
  · obtain ⟨l, hl⟩ := has_leg b
    exact ⟨l, hl, (incident l u).mpr (.inr (by rw [hl, he]))⟩
  · let l : Leg q := ⟨b, u, h, he⟩
    exact ⟨l, rfl, (incident l u).mpr (.inl rfl)⟩

-- 读法：`position` 的取值由 `2 * (offset (q l.2.val) (other l) + l.1.2.val / R) + if l.2.val < via l.1 then 0 else 1` 给出。
def position (l : Leg q) : ℕ :=
  2 * (offset (q l.2.val) (other l) + l.1.2.val / R) + if l.2.val < via l.1 then 0 else 1

-- 读法：`l` 等于 `k`。按 `Subtype.ext` 的外延性准则比较各分量。
private theorem leg_ext {l k : Leg q} (hu : l.2.val = k.2.val) (hv : other l = other k)
    (hi : l.1.2.val = k.1.2.val) : l = k := by
  have he : l.1.1 = k.1.1 := by
    apply Subtype.ext
    have h₁ := l.1.1.property
    have h₂ := k.1.1.property
    rcases endpoints l with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      rcases endpoints k with ⟨g, g'⟩ | ⟨g, g'⟩ <;> apply Prod.ext <;> omega
  rcases l with ⟨⟨a, i⟩, u⟩
  rcases k with ⟨⟨b, j⟩, v⟩
  change a = b at he
  subst b
  have hh : i = j := Fin.ext hi
  subst j
  have : u = v := Subtype.ext hu
  subst v
  rfl

variable (hs : ∀ u v, q u v = q v u) (hq : ∀ u, ∑ v, q u v ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)

-- 读法：`slot` 的结果类型为 `Slot R n`。
def slot (l : Leg q) : Slot R n :=
  (link l, ⟨position l, by
    have hb := capacity _ (hq l.2.val) hn _ (index_lt hs l)
    unfold position
    split <;> omega⟩)

-- 读法：`(slot hs hq hn)` 是单射。
theorem injective : Function.Injective (slot hs hq hn) := by
  intro l k h
  have he : (link l).val = (link k).val := congrArg (fun s => s.1.val) h
  have hp : position l = position k := congrArg (fun s => s.2.val) h
  have hh : l.2.val = k.2.val ∧ via l.1 = via k.1 ∧
      offset (q l.2.val) (other l) + l.1.2.val / R =
        offset (q k.2.val) (other k) + k.1.2.val / R := by
    unfold link at he
    unfold position at hp
    split_ifs at he hp <;> simp only [Prod.mk.injEq] at he <;> omega
  -- 推导：从 `hh` 中取出 `hu, hm, ho`。
  obtain ⟨hu, hm, ho⟩ := hh
  have ha := index_lt hs k
  rw [← hu] at ho ha
  obtain ⟨hv, hd⟩ := offset_unique _ (index_lt hs l) ha ho
  apply leg_ext hu hv
  have hr : l.1.2.val % R = k.1.2.val % R := congrArg Fin.val hm
  calc
    _ = l.1.2.val % R + R * (l.1.2.val / R) := (Nat.mod_add_div ..).symm
    _ = _ := by rw [hr, hd, Nat.mod_add_div]

-- 读法：存在唯一的 `y : Slot R n → Bool`，`(∀ l, y (slot hs hq hn l) = x l.1)` 与 `(∀ s ∉ Set.range (slot hs hq hn), y s = false)` 同时成立。用函数外延性比较等号两侧在 `s` 处的取值。
/-- 将未使用的槽位固定为零，使物理编码唯一。

英文原文：Fixing unused slots to zero makes the physical encoding unique.
-/
theorem encode (x : Virtual q → Bool) :
    ∃! y : Slot R n → Bool, (∀ l, y (slot hs hq hn l) = x l.1) ∧
      (∀ s ∉ Set.range (slot hs hq hn), y s = false) := by
  let y := Function.extend (slot hs hq hn) (fun l => x l.1) (fun _ => false)
  have hy (l : Leg q) : y (slot hs hq hn l) = x l.1 :=
    (injective hs hq hn).extend_apply _ _ _
  have hz (s : Slot R n) (h : s ∉ Set.range (slot hs hq hn)) : y s = false :=
    Function.extend_apply' _ _ _ h
  refine ⟨y, ⟨hy, hz⟩, fun z h => ?_⟩
  funext s
  by_cases hr : s ∈ Set.range (slot hs hq hn)
  -- 推导：从 `hr` 中取出 `l, rfl`。
  · obtain ⟨l, rfl⟩ := hr
    rw [hy, h.1]
  · rw [hz s hr, h.2 s hr]

-- 读法：存在唯一的 `x : Virtual q → Bool`，对每个 `l`，`y (slot hs hq hn l)` 等于 `x l.1`。用函数外延性比较等号两侧在 `b` 处的取值。
/-- 若两段链路在共用的中间处理器上取值一致，就能唯一确定虚拟比特的赋值。

英文原文：When the two legs agree at their shared intermediate processor,
they determine a unique virtual bit assignment.
-/
theorem decode (y : Slot R n → Bool)
    (h : ∀ l k, l.1 = k.1 → y (slot hs hq hn l) = y (slot hs hq hn k)) :
    ∃! x : Virtual q → Bool, ∀ l, y (slot hs hq hn l) = x l.1 := by
  choose g hg using (has_leg (q := q))
  refine ⟨fun b => y (slot hs hq hn (g b)), fun l => h _ _ (hg _).symm, ?_⟩
  intro x hx
  funext b
  exact (congrArg x (hg b)).symm.trans (hx (g b)).symm

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links
end

/-!
# 沿物理链路收缩局部表

每个处理器可读取其关联链路上的共享位置，在各中继处检验相等性，并将未使用的位置固定为零。于是每个虚拟赋值恰好贡献一次，对任意特征都成立。

**英文原文**

Contracting local tables over physical links

A processor sees the shared positions of its incident links. It tests
equality at every relay and pins unused positions to zero. Each virtual
assignment then contributes exactly once, in any characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

open Classical
variable {R n : ℕ} {q : Fin R → Fin R → ℕ}

-- 读法：`sees` 表示以下条件：`u = p.val.1`、`u = p.val.2` 至少有一项成立。
def sees (u : Fin R) (p : Link R) : Prop := u = p.val.1 ∨ u = p.val.2

-- 读法：`view` 的取值由 `Function.extend (fun s : {s : Slot R n // sees u s.1} => address s.val) (fun s => y s.val) (fun _ => false)` 给出。
/-- 在同步地址读取关联的比特。链路预留区间中的其余位置取零。

英文原文：Read the incident bits at synchronized addresses. Other positions
in the reserved link interval contain zero.
-/
def view (u : Fin R) (y : Slot R n → Bool) : Fin (n / 4) → Bool :=
  Function.extend (fun s : {s : Slot R n // sees u s.1} => address s.val)
    (fun s => y s.val) (fun _ => false)

-- 读法：`view u y (address s)` 等于 `y s`。这里调用 `hi.extend_apply`。
theorem view_address (u : Fin R) (y : Slot R n → Bool) (s : Slot R n) (h : sees u s.1) :
    view u y (address s) = y s := by
  have hi : Function.Injective (fun t : {s : Slot R n // sees u s.1} => address t.val) :=
    fun a b he => Subtype.ext (address_injective u a.2 b.2 he)
  exact hi.extend_apply _ _ ⟨s, h⟩

variable (hs : ∀ u v, q u v = q v u) (hq : ∀ u, ∑ v, q u v ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)

-- 读法：`valid` 的结果类型为 `Prop`。
def valid (u : Fin R) (t : Fin (n / 4) → Bool) : Prop :=
  (∀ l k, l.1 = k.1 → via l.1 = u →
    t (address (slot hs hq hn l)) = t (address (slot hs hq hn k))) ∧
  (∀ s ∉ Set.range (slot hs hq hn), u = s.1.val.1 → t (address s) = false)

-- 读法：当 `h : sees u b.1` 成立时取 `t (address (slot hs hq hn (at_endpoint b u h).choose))`，否则取 `false`。
def receive (u : Fin R) (t : Fin (n / 4) → Bool) (b : Virtual q) : Bool :=
  if h : sees u b.1 then t (address (slot hs hq hn (at_endpoint b u h).choose)) else false

-- 读法：`Tied` 表示以下条件：`(∀ l, y (slot hs hq hn l) = x l.1)` 与 `∀ s ∉ Set.range (slot hs hq hn), y s = false` 同时成立。
private def Tied (x : Virtual q → Bool) (y : Slot R n → Bool) : Prop :=
  (∀ l, y (slot hs hq hn l) = x l.1) ∧ ∀ s ∉ Set.range (slot hs hq hn), y s = false

-- 读法：要证明的命题是 `sees (via l.1) (slot hs hq hn l).1`。
private theorem via_sees (l : Leg q) : sees (via l.1) (slot hs hq hn l).1 :=
  (incident l _).mpr (.inr rfl)

-- 读法：要证明的命题是 `valid hs hq hn u (view u y)`。
private theorem valid_of_tied {x y} (h : Tied hs hq hn x y) (u : Fin R) :
    valid hs hq hn u (view u y) := by
  constructor
  · intro l k hl hu
    subst u
    have hk : sees (via l.1) (slot hs hq hn k).1 := hl ▸ via_sees hs hq hn k
    rw [view_address _ _ _ (via_sees hs hq hn l), view_address _ _ _ hk, h.1, h.1, hl]
  · intro s he hu
    rw [view_address _ _ _ (.inl hu), h.2 s he]

-- 读法：存在唯一的 `x`，要证明的命题是 `Tied hs hq hn x y`。
private theorem tied_of_valid (y : Slot R n → Bool)
    (hy : ∀ u, valid hs hq hn u (view u y)) : ∃! x, Tied hs hq hn x y := by
  have he (l k : Leg q) (h : l.1 = k.1) : y (slot hs hq hn l) = y (slot hs hq hn k) := by
    have hh := (hy (via l.1)).1 l k h rfl
    have hk : sees (via l.1) (slot hs hq hn k).1 := h ▸ via_sees hs hq hn k
    rwa [view_address _ _ _ (via_sees hs hq hn l), view_address _ _ _ hk] at hh
  obtain ⟨x, hx, hu⟩ := decode hs hq hn y he
  refine ⟨x, ⟨hx, ?_⟩, fun z hz => hu z hz.1⟩
  intro s h
  have := (hy s.1.val.1).2 s h rfl
  rwa [view_address _ _ _ (.inl rfl)] at this

variable {F : Type} [Field F]

-- 读法：当 `valid hs hq hn u t` 成立时取 `g u (receive hs hq hn u t)`，否则取 `0`。
/-- 仅以该处理器的预留区间为输入的表。

英文原文：A table whose input is only the processor's reserved interval.
-/
def site (g : Fin R → (Virtual q → Bool) → F) (u : Fin R) (t : Fin (n / 4) → Bool) : F :=
  if valid hs hq hn u t then g u (receive hs hq hn u t) else 0

-- 读法：`(∑ x, ∏ u, g u x)` 等于 `∑ y, ∏ u, site hs hq hn g u (view u y)`。
theorem eval (g : Fin R → (Virtual q → Bool) → F)
    (hg : ∀ u x x', (∀ b, sees u b.1 → x b = x' b) → g u x = g u x') :
    (∑ x, ∏ u, g u x) = ∑ y, ∏ u, site hs hq hn g u (view u y) := by
  have heq (x y) (h : Tied hs hq hn x y) (u : Fin R) :
      site hs hq hn g u (view u y) = g u x := by
    rw [site, ite_eq_left (valid_of_tied hs hq hn h u)]
    apply hg
    intro b hb
    rw [receive, dite_eq_left hb]
    obtain ⟨he, hl⟩ := (at_endpoint b u hb).choose_spec
    rw [view_address u y (slot hs hq hn _) hl, h.1, he]
  calc
    _ = ∑ x, ∑ y, if Tied hs hq hn x y then ∏ u, g u x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      obtain ⟨y, hy, hu⟩ : ∃! y, Tied hs hq hn x y := encode hs hq hn x
      rw [Fintype.sum_eq_single y (fun z hz => ite_eq_right (fun h => hz (hu z h))), ite_eq_left hy]
    _ = ∑ y, ∑ x, if Tied hs hq hn x y then ∏ u, g u x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : ∀ u, valid hs hq hn u (view u y)
      -- 推导：从 `tied_of_valid hs hq hn y h` 中取出 `x, hx, hu`。
      · obtain ⟨x, hx, hu⟩ := tied_of_valid hs hq hn y h
        rw [Fintype.sum_eq_single x (fun z hz => ite_eq_right (fun h => hz (hu z h))), ite_eq_left hx]
        simp_rw [heq x y hx]
      · obtain ⟨u, hu⟩ := not_forall.mp h
        have hb (x) : ¬ Tied hs hq hn x y := fun h => hu (valid_of_tied hs hq hn h u)
        simp only [hb, ite_false, Finset.sum_const_zero]
        exact (Finset.prod_eq_zero (Finset.mem_univ u) (ite_eq_right hu)).symm

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links
end

/-!
# 任意虚拟链路上的局部收缩

平行边可按任意指定顺序编号。自环在本地求和，不占用物理链路。

**英文原文**

Local contraction with arbitrary virtual links

Parallel edges may be numbered in any prescribed order. Loops are
summed privately so they consume no physical links.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

open Classical
variable {R n : ℕ} {M : Type} [Fintype M] (src dst : M → Fin R)

-- 读法：在后续公式中，`Between` 是 `{e // (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)}` 的缩写。
abbrev Between (u v : Fin R) :=
  {e // (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)}

-- 读法：`count` 的取值由 `Fintype.card (Between src dst u v)` 给出。
def count (u v : Fin R) : ℕ := Fintype.card (Between src dst u v)

-- 读法：在后续公式中，`Numbering` 是 `∀ u v, Fin (count src dst u v) ≃ Between src dst u v` 的缩写。
abbrev Numbering := ∀ u v, Fin (count src dst u v) ≃ Between src dst u v

-- 读法：`count src dst u v` 等于 `count src dst v u`。
theorem count_symm (u v : Fin R) : count src dst u v = count src dst v u := by
  simp only [count, Between, or_comm]

-- 读法：结论为 `∑ v, count src dst u v ≤ Fintype.card {e // src e = u ∨ dst e = u}`。
theorem count_le (u : Fin R) :
    ∑ v, count src dst u v ≤ Fintype.card {e // src e = u ∨ dst e = u} := by
  let f : (Σ v, Between src dst u v) → {e // src e = u ∨ dst e = u} :=
    fun t => ⟨t.2.val, by rcases t.2.property with h | h <;> grind⟩
  have hi : Function.Injective f := by
    rintro ⟨v, e⟩ ⟨w, k⟩ he
    have eqn : e.val = k.val := congrArg Subtype.val he
    have h₁ := e.property
    have h₂ := k.property
    have : v = w := by grind
    subst w
    rw [Subtype.ext eqn]
  simpa only [Fintype.card_sigma, count] using Fintype.card_le_of_injective f hi

variable (serial : Numbering src dst)

-- 读法：在后续公式中，`Private` 是 `Fin (count src dst u u)` 的缩写。
abbrev Private (u : Fin R) := Fin (count src dst u u)
-- 读法：在后续公式中，`Edges` 是 `Virtual (count src dst) ⊕ Σ u, Private src dst u` 的缩写。
abbrev Edges := Virtual (count src dst) ⊕ Σ u, Private src dst u

-- 读法：逐一匹配以下输入模式：`.inl ⟨p, i⟩`、`.inr ⟨u, i⟩`。
def edge : Edges src dst → M
  | .inl ⟨p, i⟩ => (serial p.val.1 p.val.2 i).val
  | .inr ⟨u, i⟩ => (serial u u i).val

-- 读法：`(edge src dst serial)` 是单射。
private theorem edge_injective : Function.Injective (edge src dst serial) := by
  have distinct (p : Link R) (u : Fin R) i j :
      (serial p.val.1 p.val.2 i).val ≠ (serial u u j).val := by
    have hi := (serial p.val.1 p.val.2 i).property
    have hj := (serial u u j).property
    have hp := p.property
    grind
  rintro (⟨p, i⟩ | ⟨u, i⟩) (⟨q, j⟩ | ⟨v, j⟩) he <;> dsimp only [edge] at he
  · have hi := (serial p.val.1 p.val.2 i).property
    have hj := (serial q.val.1 q.val.2 j).property
    have hp := p.property
    have hq := q.property
    have : p = q := Subtype.ext (Prod.ext (by grind) (by grind))
    subst q
    rw [(serial _ _).injective (Subtype.ext he)]
  · exact (distinct p v i j he).elim
  · exact (distinct q u j i he.symm).elim
  · have hi := (serial u u i).property
    have hj := (serial v v j).property
    have : u = v := by grind
    subst v
    rw [(serial _ _).injective (Subtype.ext he)]

-- 读法：`(edge src dst serial)` 是满射。
private theorem edge_surjective : Function.Surjective (edge src dst serial) := by
  intro e
  have h (u v : Fin R) (huv : u < v)
      (he : (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)) :
      ∃ i, edge src dst serial i = e := by
    obtain ⟨i, hi⟩ := (serial u v).surjective ⟨e, he⟩
    exact ⟨.inl ⟨⟨(u, v), huv⟩, i⟩, congrArg Subtype.val hi⟩
  rcases lt_trichotomy (src e) (dst e) with hl | he | hl
  · exact h _ _ hl (.inl ⟨rfl, rfl⟩)
  · obtain ⟨i, hi⟩ := (serial (src e) (src e)).surjective ⟨e, .inl ⟨rfl, he.symm⟩⟩
    exact ⟨.inr ⟨src e, i⟩, congrArg Subtype.val hi⟩
  · exact h _ _ hl (.inr ⟨rfl, rfl⟩)

-- 读法：`ports` 的取值由 `Equiv.ofBijective (edge src dst serial) ⟨edge_injective src dst serial, edge_surjective src dst serial⟩` 给出。
def ports : Edges src dst ≃ M :=
  Equiv.ofBijective (edge src dst serial) ⟨edge_injective src dst serial, edge_surjective src dst serial⟩

-- 读法：`assignments` 的结果类型为 `(Virtual (count src dst) → Bool) × ((u : Fin R) → Private src dst u → Bool) ≃ (M → Bool)`。
def assignments :
    (Virtual (count src dst) → Bool) × ((u : Fin R) → Private src dst u → Bool) ≃ (M → Bool) :=
  ((Equiv.refl _).prodCongr (Equiv.piCurry (fun _ _ => Bool)).symm).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
      ((ports src dst serial).arrowCongr (.refl _)))

-- 读法：`assignments src dst serial (x, z) (ports src dst serial e)` 等于 `Sum.elim x (fun p => z p.1 p.2) e`。
private theorem assignments_at (x z) (e : Edges src dst) :
    assignments src dst serial (x, z) (ports src dst serial e) =
      Sum.elim x (fun p => z p.1 p.2) e := by
  unfold assignments
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.refl_apply]
  cases e <;> rfl

-- 读法：`assignments src dst serial (x, z) e` 等于 `assignments src dst serial (x', z') e`。
private theorem assignments_local (u : Fin R) (x x' z z')
    (hx : ∀ b, sees u b.1 → x b = x' b) (hz : z u = z' u)
    (e : M) (he : src e = u ∨ dst e = u) :
    assignments src dst serial (x, z) e = assignments src dst serial (x', z') e := by
  obtain ⟨k, rfl⟩ := (ports src dst serial).surjective e
  rw [assignments_at, assignments_at]
  rcases k with ⟨p, i⟩ | ⟨v, i⟩
  · apply hx
    have h := (serial p.val.1 p.val.2 i).property
    change src (serial p.val.1 p.val.2 i).val = u ∨ dst (serial p.val.1 p.val.2 i).val = u at he
    change u = p.val.1 ∨ u = p.val.2
    grind
  · have h := (serial v v i).property
    change src (serial v v i).val = u ∨ dst (serial v v i).val = u at he
    have hv : v = u := by grind
    subst v
    exact congrFun hz i

variable (hd : ∀ u, Fintype.card {e // src e = u ∨ dst e = u} ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)
variable {F : Type} [Field F] (g : Fin R → (M → Bool) → F)

-- 读法：`tally` 的取值由 `∑ z : Private src dst u → Bool, g u (assignments src dst serial (x, Function.update (fun _ _ => false) u z))` 给出。
def tally (u : Fin R) (x : Virtual (count src dst) → Bool) : F :=
  ∑ z : Private src dst u → Bool,
    g u (assignments src dst serial (x, Function.update (fun _ _ => false) u z))

-- 读法：`worker` 的取值由 `site (count_symm src dst) (fun u => (count_le src dst u).trans (hd u)) hn (tally src dst serial g) u t` 给出。
def worker (u : Fin R) (t : Fin (n / 4) → Bool) : F :=
  site (count_symm src dst) (fun u => (count_le src dst u).trans (hd u)) hn
    (tally src dst serial g) u t

-- 读法：`(∑ x, ∏ u, g u x)` 等于 `∑ y, ∏ u, worker src dst serial hd hn g u (view u y)`。这里调用 `Finset.sum_congr`。
theorem contract [DecidableEq M]
    (hg : ∀ u x y, (∀ e, src e = u ∨ dst e = u → x e = y e) → g u x = g u y) :
    (∑ x, ∏ u, g u x) = ∑ y, ∏ u, worker src dst serial hd hn g u (view u y) := by
  have ht (u : Fin R) (x x' : Virtual (count src dst) → Bool)
      (hx : ∀ b, sees u b.1 → x b = x' b) :
      tally src dst serial g u x = tally src dst serial g u x' := by
    apply Finset.sum_congr rfl
    intro z _
    exact hg _ _ _ (assignments_local src dst serial u _ _ _ _ hx rfl)
  unfold worker
  rw [← eval _ _ _ _ ht, ← (assignments src dst serial).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  unfold tally
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.prod_congr rfl
  intro u _
  exact hg _ _ _ (assignments_local src dst serial u _ _ _ _ (fun _ _ => rfl)
    (by simp))

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links
end

/-!
# 有限字母表上的路由

在每个端点，于本地对关联符号求和，并要求其编码与共享比特匹配。编码的单射性保证两端使用同一个符号。自环无须共享比特。

**英文原文**

Routing finite alphabets

At each endpoint, privately sum over the incident symbols and require
their encodings to match the shared bits. An injective code forces the
same symbol at both ends. A loop needs no shared bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Encoded

open Classical
variable {R n : ℕ} {M : Type} (src dst : M → Fin R)
variable (alph : M → Type) (w : M → ℕ) (code : ∀ e, alph e ↪ (Fin (w e) → Bool))

-- 读法：在后续公式中，`Shared` 是 `{e // src e ≠ dst e}` 的缩写。
abbrev Shared := {e // src e ≠ dst e}
-- 读法：在后续公式中，`Bits` 是 `Σ e : Shared src dst, Fin (w e.val)` 的缩写。
abbrev Bits := Σ e : Shared src dst, Fin (w e.val)
-- 读法：在后续公式中，`Local` 是 `(e : {e // src e = u ∨ dst e = u}) → alph e.val` 的缩写。
abbrev Local (u : Fin R) := (e : {e // src e = u ∨ dst e = u}) → alph e.val

-- 读法：在后续公式中，`left` 是 `src b.1.val` 的缩写。
abbrev left (b : Bits src dst w) := src b.1.val
-- 读法：在后续公式中，`right` 是 `dst b.1.val` 的缩写。
abbrev right (b : Bits src dst w) := dst b.1.val

-- 读法：输入 `e` 时返回 `x e.val`。
def restrict (u : Fin R) (x : ∀ e, alph e) : Local src dst alph u :=
  fun e => x e.val

-- 读法：`agrees` 表示以下条件：`∀ (e : Shared src dst) (he : src e.val = u ∨ dst e.val = u) (j : Fin (w e.val)), code e.val (t ⟨e.val, he⟩) j = b ⟨e, j⟩`。
def agrees (u : Fin R) (b : Bits src dst w → Bool) (t : Local src dst alph u) : Prop :=
  ∀ (e : Shared src dst) (he : src e.val = u ∨ dst e.val = u) (j : Fin (w e.val)),
    code e.val (t ⟨e.val, he⟩) j = b ⟨e, j⟩

-- 读法：在后续公式中，`State` 是 `(Bits src dst w → Bool) × ((u : Fin R) → Local src dst alph u)` 的缩写。
private abbrev State := (Bits src dst w → Bool) × ((u : Fin R) → Local src dst alph u)

-- 读法：`encode` 的取值由 `(fun b => code b.1.val (x b.1.val) b.2, fun u => restrict src dst alph u x)` 给出。
private def encode (x : ∀ e, alph e) : State src dst alph w :=
  (fun b => code b.1.val (x b.1.val) b.2, fun u => restrict src dst alph u x)

-- 读法：`(encode src dst alph w code)` 是单射。用函数外延性比较等号两侧在 `e` 处的取值。
private theorem injective : Function.Injective (encode src dst alph w code) := by
  intro x y he
  funext e
  exact congrArg (fun s : State src dst alph w => s.2 (src e) ⟨e, .inl rfl⟩) he

-- 读法：`(∀ u, agrees src dst alph w code u s.1 (s.2 u))` 与 `∃ x, encode src dst alph w code x = s` 等价。用函数外延性比较等号两侧在 `⟨e, j⟩` 处的取值。
private theorem coherent (s : State src dst alph w) :
    (∀ u, agrees src dst alph w code u s.1 (s.2 u)) ↔
      ∃ x, encode src dst alph w code x = s := by
  constructor
  · intro ok
    let x (e : M) := s.2 (src e) ⟨e, .inl rfl⟩
    refine ⟨x, Prod.ext ?_ ?_⟩
    · funext ⟨e, j⟩
      exact ok (src e.val) e (.inl rfl) j
    · funext u ⟨e, he⟩
      by_cases h : src e = u
      · subst u; rfl
      · have hne : src e ≠ dst e := fun heq => h (heq.trans (he.resolve_left h))
        apply (code e).injective
        funext j
        exact (ok (src e) ⟨e, hne⟩ (.inl rfl) j).trans (ok u ⟨e, hne⟩ he j).symm
  · rintro ⟨x, rfl⟩ _ _ _ _
    rfl

variable [Fintype M] [∀ e, Fintype (alph e)]

-- 读法：结论为 `Fintype.card {b : Bits src dst w // left src dst w b = u ∨ right src dst w b = u} = ∑ e ∈ Finset.univ.filter (fun e => src e ≠ dst e ∧ (src e = u ∨ dst e = u)), w e`。
theorem load (u : Fin R) :
    Fintype.card {b : Bits src dst w // left src dst w b = u ∨ right src dst w b = u} =
      ∑ e ∈ Finset.univ.filter (fun e => src e ≠ dst e ∧ (src e = u ∨ dst e = u)), w e := by
  let T := {e // src e ≠ dst e ∧ (src e = u ∨ dst e = u)}
  let E : {b : Bits src dst w // left src dst w b = u ∨ right src dst w b = u} ≃
      (Σ e : T, Fin (w e.val)) := {
    toFun := fun b => ⟨⟨b.1.1.val, b.1.1.property, b.2⟩, b.1.2⟩
    invFun := fun s => ⟨⟨⟨s.1.val, s.1.property.1⟩, s.2⟩, s.1.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  rw [Fintype.card_congr E, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype _ (by simp) w).symm

variable [DecidableEq M]
variable (hd : ∀ u, ∑ e ∈ Finset.univ.filter
  (fun e => src e ≠ dst e ∧ (src e = u ∨ dst e = u)), w e ≤ n / 64) (hn : 64 * R ^ 2 ≤ n)

variable {F : Type} [Field F] (g : Fin R → (∀ e, alph e) → F)

-- 读法：`localize` 的取值由 `if h : Nonempty (∀ e, alph e) then g u (fun e => if he : src e = u ∨ dst e = u then t ⟨e, he⟩ else (choice h) e) else 0` 给出。
def localize (u : Fin R) (t : Local src dst alph u) : F :=
  if h : Nonempty (∀ e, alph e) then
    g u (fun e => if he : src e = u ∨ dst e = u then t ⟨e, he⟩ else (choice h) e)
  else 0

-- 读法：`bitSite` 的取值由 `∑ t, if agrees src dst alph w code u b t then localize src dst alph g u t else 0` 给出。
def bitSite (u : Fin R) (b : Bits src dst w → Bool) : F :=
  ∑ t, if agrees src dst alph w code u b t then localize src dst alph g u t else 0

-- 读法：`bitSite src dst alph w code g u x` 等于 `bitSite src dst alph w code g u y`。
private theorem bitSite_local (u : Fin R) (x y : Bits src dst w → Bool)
    (he : ∀ e, left src dst w e = u ∨ right src dst w e = u → x e = y e) :
    bitSite src dst alph w code g u x = bitSite src dst alph w code g u y := by
  have ho (t) : agrees src dst alph w code u x t ↔ agrees src dst alph w code u y t :=
    ⟨fun h e h' j => (h e h' j).trans (he ⟨e, j⟩ h'),
      fun h e h' j => (h e h' j).trans (he ⟨e, j⟩ h').symm⟩
  simp only [bitSite, ho]

-- 读法：`(∑ x, ∏ u, g u x)` 等于 `∑ b, ∏ u, bitSite src dst alph w code g u b`。
private theorem bit_sum
    (hg : ∀ u x y, (∀ e, src e = u ∨ dst e = u → x e = y e) → g u x = g u y) :
    (∑ x, ∏ u, g u x) = ∑ b, ∏ u, bitSite src dst alph w code g u b := by
  let enc := encode src dst alph w code
  let ok := agrees src dst alph w code
  let v := localize src dst alph g
  have hv (u) (x) : v u ((enc x).2 u) = g u x := by
    unfold v localize
    rw [dite_eq_left (show Nonempty (∀ e, alph e) from ⟨x⟩)]
    exact hg _ _ _ (fun e he => by rw [dite_eq_left he]; rfl)
  have heq (s : State src dst alph w) :
      (∑ x, if enc x = s then ∏ u, g u x else 0) =
        ∏ u, if ok u s.1 (s.2 u) then v u (s.2 u) else 0 := by
    by_cases h : ∀ u, ok u s.1 (s.2 u)
    -- 推导：从 `(coherent src dst alph w code s).mp h` 中取出 `x, hx`。
    · obtain ⟨x, hx⟩ := (coherent src dst alph w code s).mp h
      change enc x = s at hx
      simp only [h, ite_true]
      rw [← hx]
      have hi : Function.Injective enc := injective src dst alph w code
      simp only [hi.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hv]
    · have hn (x) : enc x ≠ s :=
        fun e => h ((coherent src dst alph w code s).mpr ⟨x, e⟩)
      obtain ⟨u, hu⟩ := not_forall.mp h
      simp only [hn, ite_false, Finset.sum_const_zero]
      exact (Finset.prod_eq_zero (Finset.mem_univ u) (ite_eq_right hu)).symm
  calc
    _ = ∑ x, ∑ s, if enc x = s then ∏ u, g u x else 0 := by simp
    _ = ∑ s, ∑ x, if enc x = s then ∏ u, g u x else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [heq]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      unfold bitSite
      rw [Fintype.prod_sum]

-- 读法：`worker` 的取值由 `Links.worker _ _ serial (fun u => (load src dst w u).le.trans (hd u)) hn (bitSite src dst alph w code g)` 给出。
def worker (serial : Links.Numbering (left src dst w) (right src dst w)) :
    Fin R → (Fin (n / 4) → Bool) → F :=
  Links.worker _ _ serial (fun u => (load src dst w u).le.trans (hd u)) hn
    (bitSite src dst alph w code g)

-- 读法：`(∑ x, ∏ u, g u x)` 等于 `∑ y, ∏ u, worker src dst alph w code hd hn g serial u (Links.view u y)`。这里调用 `Links.contract`。
/-- 每条边上的字母表可以为空。只有连接不同处理器的边才计入带宽条件。

英文原文：The alphabet on each edge may be empty. Only edges joining distinct
processors contribute to the bandwidth condition.
-/
theorem contract
    (hg : ∀ u x y, (∀ e, src e = u ∨ dst e = u → x e = y e) → g u x = g u y)
    (serial : Links.Numbering (left src dst w) (right src dst w) :=
      fun _ _ => (Fintype.equivFin _).symm) :
    (∑ x, ∏ u, g u x) =
      ∑ y, ∏ u, worker src dst alph w code hd hn g serial u (Links.view u y) := by
  rw [bit_sum src dst alph w code g hg]
  exact Links.contract _ _ serial _ hn _ (bitSite_local src dst alph w code g)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Encoded
end

/-!
# 有效报告下的链路用量

共享类别传送其选择器和跨界比特。其他类别逐个传送数据包中的位置。自环不占用带宽。

**英文原文**

Link usage under a valid report

A shared class transmits its selector and crossing bits. Other classes
transmit the individual packet positions. Loops consume no bandwidth.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Spectral Finset
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (s : Packet n r d → A.I) (u : Worker r)

-- 读法：`A.owner hn N (A.report hn s) x` 等于 `(A.plan hn N s).base x`。
private theorem owner_plan (x : Label n r) :
    A.owner hn N (A.report hn s) x = (A.plan hn N s).base x := by
  rw [owner, report_groups]
  rfl

-- 读法：`A.shared N (A.report hn s) (packetClass hn (A.report hn s).1 p) = true` 与 `¬(A.plan hn N s).marked p` 等价。
private theorem shared_plan (p : Packet n r d) :
    A.shared N (A.report hn s) (packetClass hn (A.report hn s).1 p) = true ↔
      ¬(A.plan hn N s).marked p := by
  rw [shared, decide_eq_true_eq, report_groups]
  change (_ ∉ _ ∧ _ ∉ _) ↔ ¬ ∃ b, group p.1 (A.report hn s).1 b ∈ _
  simp only [packetClass, Bool.exists_bool, not_or]

-- 读法：`bill` 的取值由 `if A.src hn N R e ≠ A.dst hn N R e ∧ (A.src hn N R e = u ∨ A.dst hn N R e = u) then k else 0` 给出。
private def bill (R : A.Report r d) (e : Edge n r d h) (k : ℕ) : ℕ :=
  if A.src hn N R e ≠ A.dst hn N R e ∧ (A.src hn N R e = u ∨ A.dst hn N R e = u)
    then k else 0

-- 读法：结论为 `let R := A.report hn s ∑ c, A.bill hn N u R (.inr c) (A.classWidth R c) = ∑ p, A.bill hn N u R (.inr (packetClass hn R.1 p)) ((A.plan hn N s).q p)`。这里调用 `sum_congr`。
private theorem class_sumFromSiteBound :
    let R := A.report hn s
    ∑ c, A.bill hn N u R (.inr c) (A.classWidth R c) =
      ∑ p, A.bill hn N u R (.inr (packetClass hn R.1 p)) ((A.plan hn N s).q p) := by
  intro R
  let f (c : Class r) (z : A.I) := A.bill hn N u R (.inr c)
    (A.cross z R.1 + Nat.clog 2 (Fintype.card A.I))
  calc
    _ = A.total R f := by
      unfold total
      conv_rhs => rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro c _
      unfold f bill classWidth
      split <;> simp_all
    _ = _ := A.total_counts hn s R.1 f

-- 读法：在后续公式中，`Index` 是 `Bool × Cube n × Fin h` 的缩写。
private abbrev Index (n h : ℕ) := Bool × Cube n × Fin h

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Packet n r d × Index n h ≃ Position n r d h × Bool`。
private def positionPair : Packet n r d × Index n h ≃ Position n r d h × Bool where
  toFun t := ((t.1, t.2.2), t.2.1)
  invFun t := (t.1.1, t.2, t.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

-- 读法：结论为 `let R := A.report hn s let π := A.plan hn N s (∑ k, A.bill hn N u R (.inl (positionPair (p, k))) 1) + A.bill hn N u R (.inr (packetClass hn R.1 p)) (π.q p) ≤ π.slotsAt h u p`。
private theorem packet_bill (p : Packet n r d) :
    let R := A.report hn s
    let π := A.plan hn N s
    (∑ k, A.bill hn N u R (.inl (positionPair (p, k))) 1) +
      A.bill hn N u R (.inr (packetClass hn R.1 p)) (π.q p) ≤ π.slotsAt h u p := by
  intro R π
  let c := packetClass hn R.1 p
  let e (k : Index n h) : Edge n r d h := .inl (positionPair (p, k))
  let T := {m : π.Message h p // π.sender p m = u ∨ π.receiver p m = u}
  change (∑ k, A.bill hn N u R (e k) 1) + A.bill hn N u R (.inr c) (π.q p) ≤ Fintype.card T
  -- 推导：记下中间结论 `hm`：`A.shared N R c = true ↔ ¬π.marked p`。
  have hm : A.shared N R c = true ↔ ¬π.marked p := A.shared_plan hn N s p
  have hd (k) : A.dst hn N R (e k) = if A.shared N R c then A.src hn N R (e k)
      else .packet c.2.2 := rfl
  by_cases hs : A.shared N R c = true
  · have hb (k) : A.bill hn N u R (e k) 1 = 0 := by simp [bill, hd, hs]
    simp only [hb, sum_const_zero, zero_add]
    simp only [bill, src, dst, hs, ite_true]
    split
    · rename_i hu
      let f : Fin (π.q p) → T := fun i => ⟨.inr ⟨i, hm.mp hs⟩, hu.2⟩
      have hf : Function.Injective f := by
        intro i j he
        exact congrArg Subtype.val (Sum.inr.inj (congrArg Subtype.val he))
      simpa using Fintype.card_le_of_injective f hf
    · exact Nat.zero_le _
  -- 推导：记下中间结论 `hb`：`A.bill hn N u R (.inr c) (π.q p) = 0`。
  · have hb : A.bill hn N u R (.inr c) (π.q p) = 0 := by simp [bill, src, dst, hs]
    rw [hb, add_zero]
    let P (k : Index n h) := A.src hn N R (e k) = u ∨ Worker.packet c.2.2 = u
    have he (k) : A.bill hn N u R (e k) 1 ≤ if P k then 1 else 0 := by
      simp only [bill, hd, ite_eq_right hs, P]
      split_ifs <;> grind
    refine (sum_le_sum (fun k _ => he k)).trans ?_
    rw [sum_boole, ← Fintype.card_subtype]
    have marked : π.marked p := by tauto
    have hu (k : Index n h) : A.src hn N R (e k) = π.sender p (.inl ⟨k, marked⟩) :=
      owner_plan A hn N s _
    -- 推导：记下中间结论 `f`：`{k // P k} → T`。
    let f : {k // P k} → T := fun k =>
      ⟨.inl ⟨k.val, marked⟩, k.2.imp (fun h => (hu _).symm.trans h) id⟩
    apply Fintype.card_le_of_injective f
    intro i j he
    apply Subtype.ext
    have e := Sum.inl.inj (congrArg Subtype.val he)
    exact congrArg (fun x : {_k : Index n h // π.marked p} => x.val) e

-- 读法：结论为 `let R := A.report hn s 128 * ∑ e ∈ univ.filter (fun e => A.src hn N R e ≠ A.dst hn N R e ∧ (A.src hn N R e = u ∨ A.dst hn N R e = u)), A.size R e ≤ N`。这里调用 `le_trans`。
theorem site_bound (hb : 128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N) :
    let R := A.report hn s
    128 * ∑ e ∈ univ.filter (fun e => A.src hn N R e ≠ A.dst hn N R e ∧
      (A.src hn N R e = u ∨ A.dst hn N R e = u)), A.size R e ≤ N := by
  intro R
  apply le_trans _ hb
  apply Nat.mul_le_mul_left
  rw [sum_filter]
  change (∑ e, A.bill hn N u R e (A.size R e)) ≤ _
  rw [Fintype.sum_sum_type]
  simp only [size]
  rw [← positionPair.sum_comp, Fintype.sum_prod_type, class_sumFromSiteBound, ← sum_add_distrib]
  exact sum_le_sum (fun p _ => A.packet_bill hn N s u p)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# 报告所描述网络的赋值

**英文原文**

Assignments of a reported network
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Classical
variable {F : Type} [Field F] {n h r d : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d)

-- 读法：`symbolCode` 的取值由 `match e with | .inl _ => ⟨fun b _ => b, fun _ _ he => congrFun he (0 : Fin 1)⟩ | .inr c => A.alphabetCode hn N R c` 给出。
def symbolCode (e : Edge n r d h) : A.symbol hn N R e ↪ (Fin (A.size R e) → Bool) :=
  match e with
  | .inl _ => ⟨fun b _ => b, fun _ _ he => congrFun he (0 : Fin 1)⟩
  | .inr c => A.alphabetCode hn N R c

-- 读法：用字段 `toFun`、`left_inv`、`right_inv` 构造 `A.Assignment hn N R ≃ (Packet n r d → Block n h) × (Packet n r d → Block n h) × ((c : Class r) → A.Alphabet hn N R c)`。
private def coordinates : A.Assignment hn N R ≃
    (Packet n r d → Block n h) × (Packet n r d → Block n h) ×
      ((c : Class r) → A.Alphabet hn N R c) where
  toFun a := (A.rows a false, A.rows a true, fun c => a (.inr c))
  invFun z
    | .inl ((p, i), false) => z.1 p i
    | .inl ((p, i), true) => z.2.1 p i
    | .inr c => z.2.2 c
  left_inv a := by
    funext e
    rcases e with ⟨⟨p, i⟩, b⟩ | c
    · cases b <;> rfl
    · rfl
  right_inv _ := rfl

-- 读法：结论为 `(∑ a : A.Assignment hn N R, f (A.rows a false) (A.rows a true) (fun c => a (.inr c))) = ∑ x, ∑ y, ∑ z, f x y z`。
theorem sum_assignment (f : (Packet n r d → Block n h) → (Packet n r d → Block n h) →
    ((c : Class r) → A.Alphabet hn N R c) → F) :
    (∑ a : A.Assignment hn N R, f (A.rows a false) (A.rows a true) (fun c => a (.inr c))) =
      ∑ x, ∑ y, ∑ z, f x y z := by
  let _ : Fintype (Packet n r d → Block n h) := inferInstance
  let _ : Fintype ((c : Class r) → A.Alphabet hn N R c) := inferInstance
  rw [← (A.coordinates hn N R).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# 报告所描述数据包网络的物理链路

**英文原文**

Physical links for a reported packet network
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

-- 读法：用字段 `invFun`、`left_inv`、`right_inv` 构造 `Worker r ≃ Fin 3 × Fin r`。
private def pools (r : ℕ) : Worker r ≃ Fin 3 × Fin r where
  toFun
    | .home i => (0, i)
    | .station i => (1, i)
    | .packet i => (2, i)
  invFun v := if v.1 = 0 then .home v.2 else if v.1 = 1 then .station v.2 else .packet v.2
  left_inv w := by cases w <;> rfl
  right_inv v := by obtain ⟨i, j⟩ := v; fin_cases i <;> rfl

-- 读法：`Worker.index` 的取值由 `(pools r).trans finProdFinEquiv` 给出。
/-- 先给归属处理器编号，再给站点工作处理器编号，最后给数据包工作处理器编号。

英文原文：Number homes first, then station workers and finally packet workers.
-/
def Worker.index (r : ℕ) : Worker r ≃ Fin (3 * r) :=
  (pools r).trans finProdFinEquiv

namespace Expansion

open Classical
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d)

-- 读法：`budget` 表示以下条件：对每个 `u : Worker r`，结论为 `128 * ∑ e ∈ Finset.univ.filter (fun e => A.src hn N R e ≠ A.dst hn N R e ∧ (A.src hn N R e = u ∨ A.dst hn N R e = u)), A.size R e ≤ N`。
/-- 只有连接不同工作处理器的链路才占用通信预算。

英文原文：Only links between distinct workers use the communication budget.
-/
def budget : Prop :=
  ∀ u : Worker r, 128 * ∑ e ∈ Finset.univ.filter (fun e => A.src hn N R e ≠ A.dst hn N R e ∧
    (A.src hn N R e = u ∨ A.dst hn N R e = u)), A.size R e ≤ N

-- 读法：要证明的命题是 `A.budget hn N (A.report hn s)`。
theorem report_budget (s : Packet n r d → A.I)
    (hb : ∀ u, 128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N) :
    A.budget hn N (A.report hn s) := fun u => A.site_bound hn N s u (hb u)

variable (idx : Worker r ≃ Fin (3 * r))

-- 读法：结论为 `∑ e ∈ Finset.univ.filter (fun e => idx (A.src hn N R e) ≠ idx (A.dst hn N R e) ∧ (idx (A.src hn N R e) = i ∨ idx (A.dst hn N R e) = i)), A.size R e ≤ N / 64`。
private theorem indexed (hb : A.budget hn N R) (i : Fin (3 * r)) :
    ∑ e ∈ Finset.univ.filter (fun e => idx (A.src hn N R e) ≠ idx (A.dst hn N R e) ∧
      (idx (A.src hn N R e) = i ∨ idx (A.dst hn N R e) = i)), A.size R e ≤ N / 64 := by
  obtain ⟨u, rfl⟩ := idx.surjective i
  have hb' := hb u
  simp only [ne_eq, idx.injective.eq_iff] at hb' ⊢
  omega

-- 读法：`Serial` 的构造用到 `Links.Numbering`、`Encoded.left`、`A.src`。
abbrev Serial :=
  Links.Numbering (Encoded.left (idx ∘ A.src hn N R) (idx ∘ A.dst hn N R) (A.size R))
    (Encoded.right (idx ∘ A.src hn N R) (idx ∘ A.dst hn N R) (A.size R))

variable (hb : A.budget hn N R) (hN : 64 * (3 * r) ^ 2 ≤ N)
  (g : Worker r → A.Assignment hn N R → F)

-- 读法：`processor` 的结果类型为 `Fin (3 * r) → (Fin (N / 4) → Bool) → F`。
/-- 处理器的表作用在自己的输入区间上。各条平行连线的统一编号由调用方指定。

英文原文：The processor table acts on its own input interval. Simultaneous
numbering of the parallel wires is specified by the caller.
-/
def processor (serial : A.Serial hn N R idx) : Fin (3 * r) → (Fin (N / 4) → Bool) → F :=
  Encoded.worker (idx ∘ A.src hn N R) (idx ∘ A.dst hn N R) (A.symbol hn N R) (A.size R)
    (A.symbolCode hn N R) (A.indexed hn N R idx hb) hN (g ∘ idx.symm) serial

-- 读法：`(∑ a, ∏ u, g u a)` 等于 `∑ y, ∏ u, A.processor hn N R idx hb hN g serial u (Links.view u y)`。这里调用 `Finset.sum_congr`。
theorem physical
    (hg : ∀ u x y, (∀ e, A.src hn N R e = u ∨ A.dst hn N R e = u → x e = y e) → g u x = g u y)
    (serial : A.Serial hn N R idx := fun _ _ => (Fintype.equivFin _).symm) :
    (∑ a, ∏ u, g u a) =
      ∑ y, ∏ u, A.processor hn N R idx hb hN g serial u (Links.view u y) := by
  calc
    _ = ∑ a, ∏ i, g (idx.symm i) a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (idx.symm.prod_comp (fun u => g u a)).symm
    _ = _ := by
      apply Encoded.contract (idx ∘ A.src hn N R) (idx ∘ A.dst hn N R) (A.symbol hn N R)
        (A.size R) (A.symbolCode hn N R) (A.indexed hn N R idx hb) hN (g ∘ idx.symm) _ serial
      intro i x y he
      apply hg
      intro e h
      exact he e (h.imp idx.eq_symm_apply.mp idx.eq_symm_apply.mp)

end Expansion
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end
