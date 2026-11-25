-- 本文件所属证明环节：对二进分组的站点和线束装包、匹配及重新布线，逐项控制异常基区、临界负载、重置度数以及核心连线宽度的递推。
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix
import OAI.LinearAlgebra.MatrixExponent.Spectral.CubeGadget
import OAI.LinearAlgebra.MatrixExponent.Spectral.Packets
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# 将连线束放在各置换层上

每一层是终端集的一个置换。为了补全匹配，允许在一条尚有余量的行与一条尚有余量的列之间设零需求。通过对已饱和的行或已饱和的列计数，可得霍尔条件。

**英文原文**

Placing bundles on permutation layers

A layer is a permutation of the terminals. To complete a matching we
allow a zero demand between a slack row and a slack column. Hall's
condition follows by counting either saturated rows or saturated columns.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {X : Type} [Fintype X]

-- 读法：`s.card` 不超过 `t.card`。这里调用 `Nat.le_of_mul_le_mul_right`。
private theorem saturated (a : X → X → ℕ) (n : ℕ) (hn : 0 < n)
    (cols : ∀ j, ∑ i, a i j ≤ n) (s t : Finset X)
    (full : ∀ i ∈ s, ∑ j, a i j = n)
    (supp : ∀ i ∈ s, ∀ j ∉ t, a i j = 0) : s.card ≤ t.card := by
  apply Nat.le_of_mul_le_mul_right _ hn
  calc
    s.card * n = ∑ i ∈ s, ∑ j ∈ t, a i j := by
      rw [← Nat.nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl fun i hi =>
        ((sum_subset (subset_univ t) (fun j _ hj => supp i hi j hj)).trans (full i hi)).symm
    _ ≤ ∑ j ∈ t, n := by
      rw [sum_comm]
      exact sum_le_sum fun j _ => (sum_le_sum_of_subset (subset_univ s)).trans (cols j)
    _ = t.card * n := by simp

-- 读法：存在 `σ : Equiv.Perm X`，对每个 `i`，`0 < a i (σ i)`、`(∑ j, a i j) < n ∧ (∑ k, a k (σ i)) < n` 至少有一项成立。
private theorem match_full (a : X → X → ℕ) (n : ℕ) (hn : 0 < n)
    (rows : ∀ i, ∑ j, a i j ≤ n) (cols : ∀ j, ∑ i, a i j ≤ n) :
    ∃ σ : Equiv.Perm X, ∀ i,
      0 < a i (σ i) ∨ (∑ j, a i j) < n ∧ (∑ k, a k (σ i)) < n := by
  let f (i : X) := univ.filter fun j => 0 < a i j ∨ (∑ k, a i k) < n ∧ (∑ k, a k j) < n
  have hall (s : Finset X) : s.card ≤ (s.biUnion f).card := by
    let t := s.biUnion f
    have no_edge i (hi : i ∈ s) j (hj : j ∉ t) :
        a i j = 0 ∧ ((∑ k, a i k) < n → (∑ k, a k j) = n) := by
      have h : j ∉ f i := fun e => hj (mem_biUnion.mpr ⟨i, hi, e⟩)
      simp only [f, mem_filter, mem_univ, true_and] at h
      have := cols j
      omega
    change s.card ≤ t.card
    by_cases full : ∀ i ∈ s, ∑ j, a i j = n
    · exact saturated a n hn cols s t full (fun i hi j hj => (no_edge i hi j hj).1)
    · push Not at full
      -- 推导：从 `full` 中取出 `i, hi, hdef`。
      obtain ⟨i, hi, hdef⟩ := full
      have hb := saturated (fun j k => a k j) n hn rows tᶜ sᶜ
        (fun j hj => (no_edge i hi j (mem_compl.mp hj)).2 (lt_of_le_of_ne (rows i) hdef))
        (fun j hj k hk => (no_edge k (by simpa using hk) j (mem_compl.mp hj)).1)
      rw [card_compl, card_compl] at hb
      have := card_le_univ s
      have := card_le_univ t
      omega
  obtain ⟨g, hg, hs⟩ := (all_card_le_biUnion_card_iff_existsInjective' f).mp hall
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg),
    fun i => (mem_filter.mp (hs i)).2⟩

-- 读法：存在 `σ : Fin n → Equiv.Perm X`，对每个 `i j`，`a i j` 不超过 `∑ t, if σ t i = j then 1 else 0`。对 `n` 作归纳，并把 `a` 保持为任意参数。
/-- 若非负整数需求矩阵的每行和与每列和均不超过 `n`，则存在 `n` 个置换矩阵，其和逐项大于或等于该矩阵。

英文原文：A nonnegative integral demand matrix with row and column sums at most
`n` is dominated entrywise by a sum of `n` permutation matrices.
-/
theorem permutation_layers (a : X → X → ℕ) (n : ℕ)
    (rows : ∀ i, ∑ j, a i j ≤ n) (cols : ∀ j, ∑ i, a i j ≤ n) :
    ∃ σ : Fin n → Equiv.Perm X, ∀ i j, a i j ≤ ∑ t, if σ t i = j then 1 else 0 := by
  induction n generalizing a with
  | zero =>
    refine ⟨Fin.elim0, fun i j => ?_⟩
    have h := (single_le_sum (fun k _ => Nat.zero_le (a i k)) (mem_univ j)).trans (rows i)
    exact h.trans (Nat.zero_le _)
  | succ n ih =>
    obtain ⟨τ, hτ⟩ := match_full a (n + 1) (by omega) rows cols
    let b (i j : X) := a i j - if τ i = j then 1 else 0
    have cut (f g : X → ℕ) (x : X) (cap : ∑ i, f i ≤ n + 1)
        (hfg : ∀ i, g i ≤ f i) (dec : g x = f x - 1)
        (tight : 0 < f x ∨ ∑ i, f i < n + 1) : (∑ i, g i) ≤ n := by
      rcases tight with hx | hs
      · have := sum_lt_sum (fun i (_ : i ∈ univ) => hfg i)
          ⟨x, mem_univ x, by omega⟩
        omega
      · exact (sum_le_sum (fun i _ => hfg i)).trans (Nat.le_of_lt_succ hs)
    have hr i : ∑ j, b i j ≤ n :=
      cut (a i) (b i) (τ i) (rows i) (fun _ => Nat.sub_le _ _) (by simp [b])
        ((hτ i).imp_right And.left)
    have hc j : ∑ i, b i j ≤ n := by
      refine cut (fun i => a i j) (fun i => b i j) (τ.symm j) (cols j)
        (fun _ => Nat.sub_le _ _) (by simp [b]) ?_
      simpa only [Equiv.apply_symm_apply] using (hτ (τ.symm j)).imp_right And.right
    -- 推导：从 `ih b hr hc` 中取出 `σ, hσ`。
    obtain ⟨σ, hσ⟩ := ih b hr hc
    refine ⟨Fin.cons τ σ, ?_⟩
    intro i j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hi := hσ i j
    unfold b at hi
    omega

-- 读法：存在 `σ : Fin (U / w + Fintype.card X) → Equiv.Perm X`，对每个 `i j`，`(Fin (a i j) ↪ {t // σ t i = j} × Fin w)` 有元素。这里调用 `Nat.add_le_add_right`。
/-- 把所需的每个单位置于承载其终端有序对的层与端口上。由于每层都按一个置换进行路由，不同的终端对不会在同一终端发生冲突。

英文原文：Place each requested unit on a layer and port carrying its ordered
pair of terminals. Different pairs cannot collide at a terminal, since
each layer routes a permutation.
-/
theorem rotor_placement (a : X → X → ℕ) (U w : ℕ) (hw : 0 < w)
    (rows : ∀ i, ∑ j, a i j ≤ U) (cols : ∀ j, ∑ i, a i j ≤ U) :
    ∃ σ : Fin (U / w + Fintype.card X) → Equiv.Perm X, ∀ i j,
      Nonempty (Fin (a i j) ↪ {t // σ t i = j} × Fin w) := by
  have round (f : X → ℕ) (hf : ∑ i, f i ≤ U) :
      (∑ i, (f i / w + 1)) ≤ U / w + Fintype.card X := by
    rw [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one]
    apply Nat.add_le_add_right
    rw [Nat.le_div_iff_mul_le hw, sum_mul]
    exact (sum_le_sum (fun i _ => Nat.div_mul_le_self (f i) w)).trans hf
  -- 推导：从 `permutation_layers (fun i j => a i j / w + 1) _` 中取出 `σ, hs`。
  obtain ⟨σ, hs⟩ := permutation_layers (fun i j => a i j / w + 1) _
    (fun i => round _ (rows i)) (fun j => round _ (cols j))
  refine ⟨σ, fun i j => Function.Embedding.nonempty_of_card_le ?_⟩
  rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  calc
    _ ≤ (a i j / w + 1) * w := by
      rw [add_mul, one_mul]
      exact (Nat.lt_div_mul_add hw).le
    _ ≤ _ := Nat.mul_le_mul_right _ (by simpa only [sum_boole, Nat.cast_id] using hs i j)

-- 读法：`((U / w + Y : ℕ) : ℝ) * Y * w * u` 不超过 `10 * b`。
/-- 以标量比特计的容量，其中终端数为 `Y`，单位大小为 `u`，预算为 `b = F B`。取整的额外开销至多为一份预算。

英文原文：Capacity in scalar bits, with `Y` terminals, unit size `u` and
budget `b = F B`. The rounding overhead costs at most one budget.
-/
theorem rotor_cost (U Y w : ℕ) (u b : ℝ) (hu : 0 ≤ u)
    (hU : (U : ℝ) * Y * u ≤ 9 * b) (hw : (Y : ℝ) ^ 2 * w * u ≤ b) :
    ((U / w + Y : ℕ) : ℝ) * Y * w * u ≤ 10 * b := by
  have hr : ((U / w : ℕ) : ℝ) * w ≤ U := by exact_mod_cast Nat.div_mul_le_self U w
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg Y)) hu
  rw [Nat.cast_add]
  linarith

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 接触的两端迁移后的共同支撑

**英文原文**

Common support after relocating the ends of a contact
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {X : Type} (N : X → Finset X)

-- 读法：`cube` 的取值由 `(N p).biUnion fun q => (N q).biUnion N` 给出。
def cube (p : X) : Finset X :=
  (N p).biUnion fun q => (N q).biUnion N

-- 读法：`q ∈ cube N p` 与 `∃ x ∈ N p, ∃ y ∈ N x, q ∈ N y` 等价。
theorem mem_cube (p q : X) :
    q ∈ cube N p ↔ ∃ x ∈ N p, ∃ y ∈ N x, q ∈ N y := by
  simp only [cube, mem_biUnion]

-- 读法：`p` 属于 `cube N q`。这里调用 `mem_cube`。
theorem cube_symm (sym : ∀ x y, y ∈ N x → x ∈ N y) (p q : X) (hq : q ∈ cube N p) :
    p ∈ cube N q := by
  obtain ⟨x, hx, y, hy, hz⟩ := (mem_cube _ _ _).mp hq
  exact (mem_cube _ _ _).mpr ⟨y, sym _ _ hz, x, sym _ _ hy, sym _ _ hx⟩

-- 读法：`cube C p` 包含于 `cube N p`。这里调用 `mem_cube`。
theorem cube_mono {C : X → Finset X} (sub : ∀ x, C x ⊆ N x) (p : X) :
    cube C p ⊆ cube N p := by
  intro q hq
  obtain ⟨x, hx, y, hy, hz⟩ := (mem_cube _ _ _).mp hq
  exact (mem_cube _ _ _).mpr ⟨x, sub _ hx, y, sub _ hy, sub _ hz⟩

-- 读法：`(cube N p).card` 不超过 `D ^ 3`。
theorem cube_card {D : ℕ} (bound : ∀ p, (N p).card ≤ D) (p : X) :
    (cube N p).card ≤ D ^ 3 := by
  have step (T : X → Finset X) (L : ℕ) (ht : ∀ p, (T p).card ≤ L) (p : X) :
      ((N p).biUnion T).card ≤ D * L := calc
    _ ≤ ∑ x ∈ N p, (T x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ N p, L := sum_le_sum fun x _ => ht x
    _ ≤ D * L := by simpa using Nat.mul_le_mul_right L (bound p)
  simpa [cube, pow_succ, mul_assoc] using step _ _ (step N D bound) p

namespace Grouping
variable {V E : Type} [Fintype V] {N C : V → Finset V} {Δ D h k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
  (hedge : ∀ e, dst e ∈ C (src e))

include cs sub hedge

-- 读法：`g.route m col w x` 属于 `cube (near C Δ) (g.route m col v x)`。
theorem contact_core (col : Bool) {v w : V} (hw : w ∈ C v) (x : Cell h) :
    g.route m col w x ∈ cube (near C Δ) (g.route m col v x) :=
  (mem_cube _ _ _).mpr ⟨_, near_symm cs _ _ _ (g.route_near m cs sub hedge col v x),
    _, g.here_core cs sub hw x, g.route_near m cs sub hedge col w x⟩

-- 读法：`g.route m col w x` 属于 `cube (near N D) (g.route m col v x)`。
theorem contact_full (ns : ∀ v w, w ∈ N v → v ∈ N w) (le : Δ ≤ D)
    (col : Bool) {v w : V} (hw : w ∈ N v) (x : Cell h) :
    g.route m col w x ∈ cube (near N D) (g.route m col v x) :=
  (mem_cube _ _ _).mpr
    ⟨_, near_mono sub le _ (near_symm cs _ _ _ (g.route_near m cs sub hedge col v x)),
     _, g.here_full ns le hw x, near_mono sub le _ (g.route_near m cs sub hedge col w x)⟩

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 将每个匹配对的六个参与方放在收缩后的宿主上

**英文原文**

Placing the six parties of each matched pair on the contracted host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Grouping

open Spectral.Tensor

variable {V E : Type} [Fintype V] {N C : V → Finset V} {Δ D h k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

-- 读法：`rep` 的结果类型为 `Fin 6 → V × Cell h`。
/-- 最后两个参与方将各自的关联数计入所指的原端点。

英文原文：The last two parties charge their incidences to the indicated old endpoint.
-/
def rep (col : Bool) (e : m.items) : Fin 6 → V × Cell h :=
  let a := (src (m.mate e), ix (m.mate e))
  let b := (dst (m.mate e), ix (m.mate e))
  let c := (src e.val, ix e.val)
  let d := (dst e.val, ix e.val)
  ![a, b, c, d, if col then d else a, if col then b else d]

-- 读法：`party` 的取值由 `g.route m col (g.rep m col e i).1 (g.rep m col e i).2` 给出。
def party (col : Bool) (e : m.items) (i : Fin 6) : Site V h :=
  g.route m col (g.rep m col e i).1 (g.rep m col e i).2

-- 读法：`g.party m col e 2` 等于 `if col then g.party m col e 1 else g.party m col e 0`。
private theorem join_source (col : Bool) (e : m.items) :
    g.party m col e 2 = if col then g.party m col e 1 else g.party m col e 0 := by
  have hx := (m.spec e).1
  change g.route m col (src e.val) (ix e.val) =
    if col then g.route m col (dst (m.mate e)) (ix (m.mate e))
    else g.route m col (src (m.mate e)) (ix (m.mate e))
  rw [g.route_thin, g.route_thick m _ _ _ hx, g.route_thick m _ _ _ hx]

-- 读法：结论为 `let c := decide (4 ≤ t.val) g.party m c e (sixPair t).1 = g.party m c e (sixPair t).2`。这里调用 `r.symm`。
/-- 每个轮廓类在其指定的一侧均为内部类。

英文原文：Each profile class is internal on its designated side.
-/
theorem party_closed (e : m.items) (t : Fin 8) :
    let c := decide (4 ≤ t.val)
    g.party m c e (sixPair t).1 = g.party m c e (sixPair t).2 := by
  have r : g.party m false e 2 = g.party m false e 0 := g.join_source m false e
  have c : g.party m true e 2 = g.party m true e 1 := g.join_source m true e
  fin_cases t
  · exact r.symm
  · rfl
  · exact r
  · rfl
  · exact c.symm
  · rfl
  · exact c
  · rfl

-- 读法：`g.party m false e (sixPair t).1 = g.party m false e (sixPair t).2`、`g.party m true e (sixPair t).1 = g.party m true e (sixPair t).2` 至少有一项成立。
/-- 每条替换连线至少在一种布局中是内部连线。

英文原文：Every replacement wire is internal in at least one layout.
-/
theorem party_internal (e : m.items) (t : Fin 8) :
    g.party m false e (sixPair t).1 = g.party m false e (sixPair t).2 ∨
    g.party m true e (sixPair t).1 = g.party m true e (sixPair t).2 := by
  have h := g.party_closed m e t
  cases hc : decide (4 ≤ t.val)
  · exact .inl (hc ▸ h)
  · exact .inr (hc ▸ h)

-- 读法：`g.party m col e j` 属于 `cube (near C Δ) (g.party m col e i)`。
/-- 六个参与方均位于同一条长度至多为三的路径上的三个站点中。

英文原文：All six parties lie among three sites on a path of length at most three.
-/
theorem party_near (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (col : Bool) (e : m.items) (i j : Fin 6) :
    g.party m col e j ∈ cube (near C Δ) (g.party m col e i) := by
  let a := g.here (src (m.mate e)) (ix (m.mate e))
  let b := g.here (dst (m.mate e)) (ix (m.mate e))
  let d := g.here (dst e.val) (ix e.val)
  let y := g.route m col (dst e.val) (ix e.val)
  have ab : b ∈ near C Δ a := g.here_core cs sub (hedge _) _
  have ad : d ∈ near C Δ a := by
    have ha : a = g.here (src e.val) (ix e.val) := congrArg g.site (m.spec e).2.1
    rw [ha]
    exact g.here_core cs sub (hedge _) _
  -- 推导：记下中间结论 `dy`：`y ∈ near C Δ d`。
  have dy : y ∈ near C Δ d := g.route_near m cs sub hedge _ _ _
  have anchor (i : Fin 6) : ∃ z, (z = a ∨ z = d) ∧ g.party m col e i ∈ near C Δ z := by
    have h₀ : g.party m col e 0 ∈ near C Δ a := by
      change g.route m col _ (ix (m.mate e)) ∈ _
      rw [g.route_thick m _ _ _ (m.spec e).1]
      exact near_self _ _ _
    have h₁ : g.party m col e 1 ∈ near C Δ a := by
      change g.route m col _ (ix (m.mate e)) ∈ _
      rw [g.route_thick m _ _ _ (m.spec e).1]
      exact ab
    -- 推导：记下中间结论 `h₂`：`g.party m col e 2 ∈ near C Δ a`。
    have h₂ : g.party m col e 2 ∈ near C Δ a := by
      rw [g.join_source]; split_ifs <;> assumption
    have h₃ : g.party m col e 3 ∈ near C Δ d := dy
    fin_cases i
    · exact ⟨a, .inl rfl, h₀⟩
    · exact ⟨a, .inl rfl, h₁⟩
    · exact ⟨a, .inl rfl, h₂⟩
    · exact ⟨d, .inr rfl, h₃⟩
    · cases col
      · exact ⟨a, .inl rfl, h₀⟩
      · exact ⟨d, .inr rfl, h₃⟩
    · cases col
      · exact ⟨d, .inr rfl, h₃⟩
      · exact ⟨a, .inl rfl, h₁⟩
  -- 推导：从 `anchor i` 中取出 `x, hx, hi`。
  obtain ⟨x, hx, hi⟩ := anchor i
  obtain ⟨z, hz, hj⟩ := anchor j
  refine (mem_cube _ _ _).mpr ⟨x, near_symm cs _ _ _ hi, z, ?_, hj⟩
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · exact near_self _ _ _
  · exact ad
  · exact near_symm cs _ _ _ ad
  · exact near_self _ _ _

end OAI.LinearAlgebra.MatrixExponent.Packing.Grouping
end

/-!
# 将原有单位连线分成匹配对与未改变的连线

**英文原文**

Splitting the original unit wires into matched pairs and untouched wires
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset Spectral.Tensor
open scoped Classical

variable {V E P : Type} {h : ℕ} {ix : E → Cell h}

namespace Matching
variable {src dst : E → P} (m : Matching src dst ix)

-- 读法：用字段 `toFun`、`inj'` 构造 `m.items × Fin 2 ↪ E`。
def pairEdge : m.items × Fin 2 ↪ E where
  toFun p := if p.2 = 0 then m.mate p.1 else p.1.val
  inj' := by
    rintro ⟨x, i⟩ ⟨y, j⟩ he
    have disjoint (a b : m.items) : m.mate a ≠ b.val := fun h =>
      m.thin _ _ b.property (h ▸ (m.spec a).1)
    fin_cases i <;> fin_cases j
    · exact Prod.ext (m.mate.injective he) rfl
    · exact (disjoint _ _ he).elim
    · exact (disjoint _ _ he.symm).elim
    · exact Prod.ext (Subtype.ext he) rfl

-- 读法：在后续公式中，`unpaired` 是 `{e // e ∉ Set.range m.pairEdge}` 的缩写。
abbrev unpaired := {e // e ∉ Set.range m.pairEdge}

-- 读法：`partition` 的取值由 `(m.pairEdge.toEquivRange.sumCongr (.refl _)).trans (Equiv.Set.sumCompl _)` 给出。
def partition [Fintype E] : (m.items × Fin 2) ⊕ m.unpaired ≃ E :=
  (m.pairEdge.toEquivRange.sumCongr (.refl _)).trans (Equiv.Set.sumCompl _)

-- 读法：在后续公式中，`replaced` 是 `(Σ e : m.items, Σ j : Fin 8, Fin (f e j)) ⊕ (m.unpaired × Fin b)` 的缩写。
abbrev replaced (b : ℕ) (f : m.items → Fin 8 → ℕ) :=
  (Σ e : m.items, Σ j : Fin 8, Fin (f e j)) ⊕ (m.unpaired × Fin b)

variable [Fintype E]

-- 读法：`Fintype.card m.items` 等于 `m.count`。使用 `Fintype.card_subtype` 给出的结论。
theorem card_items : Fintype.card m.items = m.count := Fintype.card_subtype _

-- 读法：`2 * m.count + Fintype.card m.unpaired` 等于 `Fintype.card E`。
theorem card_partition : 2 * m.count + Fintype.card m.unpaired = Fintype.card E := by
  simpa [Fintype.card_sum, Fintype.card_prod, m.card_items, Nat.mul_comm] using
    Fintype.card_congr m.partition

end Matching

namespace Grouping

variable [Fintype V] {N C : V → Finset V} {Δ D k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} (m : Matching (g.ends src ix) (g.ends dst ix) ix)

-- 读法：`Prod.map (g.rep m col e) (g.rep m col e) (sixDemandPair j)` 等于 `((src (m.pairEdge (e, j)), ix (m.pairEdge (e, j))), (dst (m.pairEdge (e, j)), ix (m.pairEdge (e, j))))`。使用 `fin_cases` 给出的结论。
theorem rep_demand (col : Bool) (e : m.items) (j : Fin 2) :
    Prod.map (g.rep m col e) (g.rep m col e) (sixDemandPair j) =
      ((src (m.pairEdge (e, j)), ix (m.pairEdge (e, j))),
       (dst (m.pairEdge (e, j)), ix (m.pairEdge (e, j)))) := by
  fin_cases j <;> rfl

variable {b : ℕ} {f : m.items → Fin 8 → ℕ}

-- 读法：逐一匹配以下输入模式：`.inl ⟨e, j, _⟩`、`.inr (e, _)`。
/-- 移除自环前的端点。替换边的宽度为一个原有单位宽度的 `b` 分之一。

英文原文：Endpoints before removing loops. A replacement edge has width
one `b`-th of an original unit.
-/
def contact (col : Bool) : m.replaced b f → Site V h × Site V h
  | .inl ⟨e, j, _⟩ => Prod.map (g.party m col e) (g.party m col e) (sixPair j)
  | .inr (e, _) => (g.route m col (src e.val) (ix e.val), g.route m col (dst e.val) (ix e.val))

-- 读法：`(g.contact m col s).2` 属于 `cube (near C Δ) (g.contact m col s).1`。这里调用 `g.party_near`。
theorem contact_mem (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (col : Bool) (s : m.replaced b f) :
    (g.contact m col s).2 ∈ cube (near C Δ) (g.contact m col s).1 := by
  rcases s with ⟨e, j, t⟩ | ⟨e, t⟩
  · exact g.party_near m cs sub hedge col e _ _
  · exact g.contact_core m cs sub hedge col (hedge _) _

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 将组索引视作额外的宿主坐标

**英文原文**

Treating a group index as an extra host coordinate
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} {h : ℕ}

-- 读法：`inGroup` 的取值由 `N p.1 ×ˢ {p.2}` 给出。
def inGroup (a : ℕ) (N : V → Finset V) (p : V × Cell a) := N p.1 ×ˢ {p.2}

-- 读法：`q ∈ inGroup a N p` 与 `q.1 ∈ N p.1 ∧ q.2 = p.2` 等价。
@[simp] theorem mem_inGroup (a : ℕ) (N : V → Finset V) (p q : V × Cell a) :
    q ∈ inGroup a N p ↔ q.1 ∈ N p.1 ∧ q.2 = p.2 := by simp only [inGroup, mem_product, mem_singleton]

-- 读法：`splitCell` 的结果类型为 `Cell h ≃ Cell a × Cell (h - a)`。
def splitCell (a : ℕ) (ha : a ≤ h) : Cell h ≃ Cell a × Cell (h - a) :=
  Equiv.ofBijective (fun x => (ancestor ha x, suffix a x)) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, by rw [Fintype.card_prod, card_cell, card_cell, card_cell, ← pow_add,
      Nat.add_sub_of_le ha]⟩
    intro x y e
    obtain ⟨hp, hs⟩ := Prod.mk.inj e
    funext i
    by_cases hi : i.val < a
    · exact congrFun hp ⟨i, hi⟩
    · have he := congrFun hs ⟨i.val - a, by have := i.isLt; omega⟩
      simpa [suffix, Nat.add_sub_of_le (Nat.le_of_not_gt hi)] using he)

-- 读法：`splitAddr` 的取值由 `((Equiv.refl V).prodCongr (splitCell a ha)).trans (Equiv.prodAssoc _ _ _).symm` 给出。
def splitAddr (V : Type) (a : ℕ) (ha : a ≤ h) :
    V × Cell h ≃ (V × Cell a) × Cell (h - a) :=
  ((Equiv.refl V).prodCongr (splitCell a ha)).trans (Equiv.prodAssoc _ _ _).symm

namespace HostNet

variable {F T : Type} {x y : Wire} {u : ℕ} {L : Fringe x y T}
  (G : HostNet F L h u) (a : ℕ) (ha : a ≤ h)

-- 读法：用字段 `diagram`、`V`、`E`、`src` 构造 `HostNet F L (h - a) u`。
def regroup : HostNet F L (h - a) u where
  diagram := G.diagram
  V := G.V × Cell a
  E := G.E
  src e := (G.src e, ancestor ha (G.ix e))
  dst e := (G.dst e, ancestor ha (G.ix e))
  ix e := suffix a (G.ix e)
  units := {
    place := splitAddr G.V a ha ∘ G.units.place
    bits := G.units.bits
    left e := congrArg (splitAddr G.V a ha) (G.units.left e)
    right e := congrArg (splitAddr G.V a ha) (G.units.right e) }
  park := splitAddr G.V a ha ∘ G.park
  past := G.past ∘ (splitAddr G.V a ha).symm
  frozen v := G.frozen v.1
  N := inGroup a G.N
  C := inGroup a G.C
  ns v z he := by rw [mem_inGroup] at he ⊢; exact ⟨G.ns _ _ he.1, he.2.symm⟩
  cs v z he := by rw [mem_inGroup] at he ⊢; exact ⟨G.cs _ _ he.1, he.2.symm⟩
  sub v z he := by rw [mem_inGroup] at he ⊢; exact ⟨G.sub _ he.1, he.2⟩
  kept := G.kept
  core := G.core
  edge e := (mem_inGroup _ _ _ _).mpr ⟨G.edge e, rfl⟩
  tether q := by
    obtain ⟨hp, hi, hz⟩ := G.tether q
    exact ⟨hp, congrArg (suffix a) hi, (mem_inGroup _ _ _ _).mpr
      ⟨hz, congrArg (ancestor ha) hi.symm⟩⟩

-- 读法：`(G.regroup a ha).mass` 等于 `G.mass`。
-- 读法：`(G.regroup a ha).X` 等于 `G.X`。两端由定义化简为同一项。
@[simp] theorem regroup_X : (G.regroup a ha).X = G.X := rfl

@[simp] theorem regroup_mass : (G.regroup a ha).mass = G.mass :=
  (splitAddr G.V a ha).symm.sum_comp G.past

-- 读法：`(G.regroup a ha).rate` 等于 `G.rate`。
@[simp] theorem regroup_rate : (G.regroup a ha).rate = G.rate := by
  rw [rate, rate, regroup_mass]

variable [Fintype T]

-- 读法：`(G.regroup a ha).load (splitAddr G.V a ha p).1 (splitAddr G.V a ha p).2` 等于 `G.load p.1 p.2`。
theorem regroup_load (p : G.V × Cell h) :
    (G.regroup a ha).load (splitAddr G.V a ha p).1 (splitAddr G.V a ha p).2 =
      G.load p.1 p.2 := by
  let e := splitAddr G.V a ha
  have ex : (exterior G.diagram (e ∘ G.units.place) (e p) : ℝ) = G.tetherLoad p := by
    rw [exterior_comp]
    simp [push, tetherLoad]
  have ed : degree (fun i => Prod.map e e (G.pair i)) (e p) = degree G.pair p := by
    rw [degree_map]
    simp
  -- 推导：记下中间结论 `ep`：`push (e ∘ G.park) L.charge (e p) = push G.park L.charge p`。
  have ep : push (e ∘ G.park) L.charge (e p) = push G.park L.charge p := by
    simp [push]
    congr! 2
  change (exterior G.diagram (e ∘ G.units.place) (e p) : ℝ) +
    degree (fun i => Prod.map e e (G.pair i)) (e p) * (u : ℝ) +
    L.scale * push (e ∘ G.park) L.charge (e p) +
    (G.regroup a ha).rate * G.past (e.symm (e p)) = _
  rw [ex, ed, ep, regroup_rate, Equiv.symm_apply_apply]
  rfl

-- 读法：要证明的命题是 `(G.regroup a ha).Bounded Δ D B`。这里调用 `h.2.1`。
theorem regroup_bounded {Δ D : ℕ} {B : ℝ} (h : G.Bounded Δ D B) :
    (G.regroup a ha).Bounded Δ D B := by
  refine ⟨fun p => ?_, fun p => ?_, fun v x => ?_⟩
  · change (inGroup a G.C p).card ≤ _
    simpa [inGroup] using h.1 p.1
  · change (inGroup a G.N p).card ≤ _
    simpa [inGroup] using h.2.1 p.1
  · obtain ⟨p, hp⟩ := (splitAddr G.V a ha).surjective (v, x)
    have ht := (G.regroup_load a ha p).le.trans (h.2.2 _ _)
    rwa [hp] at ht

end HostNet
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 将同时进行的收缩投影到共同宿主上

**英文原文**

Projecting simultaneous contractions onto a common host
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} {a h : ℕ}

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Site (V × Cell a) h ≃ Site V h × Cell a`。
def splitSite : Site (V × Cell a) h ≃ Site V h × Cell a where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V]

-- 读法：`(splitSite p).2 = (splitSite q).2` 与 `(splitSite q).1 ∈ near N D (splitSite p).1` 同时成立。
theorem split_near (N : V → Finset V) (D : ℕ) {p q : Site (V × Cell a) h}
    (he : q ∈ near (inGroup a N) D p) :
    (splitSite p).2 = (splitSite q).2 ∧ (splitSite q).1 ∈ near N D (splitSite p).1 := by
  rcases (mem_near _ _ _ _).mp he with rfl | ⟨hn, hx, h₁, h₂⟩
  · exact ⟨rfl, near_self _ _ _⟩
  obtain ⟨hn, hi⟩ := (mem_inGroup _ _ _ _).mp hn
  exact ⟨hi.symm, (mem_near _ _ _ _).mpr (.inr ⟨hn, hx, h₁, h₂⟩)⟩

-- 读法：`(splitSite p).2 = (splitSite q).2` 与 `(splitSite q).1 ∈ cube (near N D) (splitSite p).1` 同时成立。
private theorem split_cube (N : V → Finset V) (D : ℕ) {p q : Site (V × Cell a) h}
    (he : q ∈ cube (near (inGroup a N) D) p) :
    (splitSite p).2 = (splitSite q).2 ∧ (splitSite q).1 ∈ cube (near N D) (splitSite p).1 := by
  obtain ⟨x, hx, y, hy, hz⟩ := (mem_cube _ _ _).mp he
  obtain ⟨ix, hx⟩ := split_near N D hx
  obtain ⟨iy, hy⟩ := split_near N D hy
  obtain ⟨iz, hz⟩ := split_near N D hz
  exact ⟨ix.trans (iy.trans iz), (mem_cube _ _ _).mpr ⟨_, hx, _, hy, hz⟩⟩

-- 读法：`(cube (near N D) p).card` 不超过 `(4 * D) ^ 900`。这里调用 `cube_card`。
theorem cube_near_card (N : V → Finset V) (D : ℕ) (hD : 0 < D)
    (deg : ∀ v, (N v).card ≤ D) (p : Site V h) :
    (cube (near N D) p).card ≤ (4 * D) ^ 900 := by
  rw [show (900 : ℕ) = 300 * 3 by decide, pow_mul]
  exact cube_card _ (near_card N D hD deg) p

namespace HostNet

variable {F T : Type} {x y : Wire} {u : ℕ} {L : Fringe x y T}

-- 读法：结构的字段包括 `W`、`place`、`N`、`C`、`ns`。
/-- 将组标签与共同宿主的槽位分开。

英文原文：Separate group labels from the slots of the common host.
-/
structure Projection (G : HostNet F L h u) (Δ D a : ℕ) where
  W : Type
  [fw : Fintype W]
  place : Site G.V h ≃ W × Cell a
  N : W → Finset W
  C : W → Finset W
  ns : ∀ v z, z ∈ N v → v ∈ N z
  cs : ∀ v z, z ∈ C v → v ∈ C z
  sub : ∀ v, C v ⊆ N v
  frozen : W → Prop
  keep : ∀ p, frozen (place p).1 ↔ G.frozen p.1
  core : ∀ p q, q ∈ cube (near G.C Δ) p → (place p).2 = (place q).2 ∧ (place q).1 ∈ C (place p).1
  full : ∀ p q, q ∈ cube (near G.N D) p → (place p).2 = (place q).2 ∧ (place q).1 ∈ N (place p).1

attribute [instance] Projection.fw

-- 读法：用字段 `W`、`place`、`N`、`C` 构造 `(G.regroup a ha).Projection Δ D a`。
def project (G : HostNet F L h u) (a : ℕ) (ha : a ≤ h) (Δ D : ℕ) (hle : Δ ≤ D) :
    (G.regroup a ha).Projection Δ D a where
  W := Site G.V (h - a)
  place := splitSite
  N := cube (near G.N D)
  C := cube (near G.C Δ)
  ns := cube_symm _ (near_symm G.ns _)
  cs := cube_symm _ (near_symm G.cs _)
  sub := cube_mono _ (near_mono G.sub hle)
  frozen p := G.frozen p.1
  keep _ := Iff.rfl
  core _ _ := split_cube G.C Δ
  full _ _ := split_cube G.N D

end HostNet
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# 共享边缘的网络之和

预算 `n` 给出以比特计的选择器长度上界。与依赖于选择器的选择复合时使用依赖和，因此即使所得网络中有一些相同，每个加项也仍保留原有重数。

**英文原文**

Sums of networks sharing a fringe

The budget `n` bounds the selector length in bits. Composition with
selector-dependent choices uses a dependent sum, so each term keeps its
multiplicity even when some of the resulting networks coincide.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

open Finset

variable {F T : Type} {x y : Wire} {h u a z b w : ℕ} {L : Fringe x y T}

-- 读法：`seats` 的取值由 `Fintype.card G.V * 2 ^ h` 给出。
def seats (G : HostNet F L h u) := Fintype.card G.V * 2 ^ h

-- 读法：`Q.seats` 不超过 `K * G.seats`。
theorem seats_le (G : HostNet F L h u) (Q : HostNet F L a z)
    (ha : a ≤ h) {K : ℕ} (hs : Fintype.card Q.V ≤ K * 2 ^ (h - a) * Fintype.card G.V) :
    Q.seats ≤ K * G.seats := by
  unfold seats
  refine (Nat.mul_le_mul_right _ hs).trans_eq ?_
  have he : 2 ^ (h - a) * 2 ^ a = (2 : ℕ) ^ h := by rw [← pow_add, Nat.sub_add_cancel ha]
  rw [← he]
  ring

variable [Field F] {G : HostNet F L h u}

-- 读法：`Expands` 表示以下条件：存在 `(I : Type) (_ : Fintype I) (q : I → HostNet F L a z)`，`Fintype.card I ≤ 2 ^ n` 与 `(∀ x y, ∑ i, (q i).diagram.eval x y = G.diagram.eval x y) ∧ ∀ i, G.Preserves (q i) ∧ P (q i)` 同时成立。
def Expands (G : HostNet F L h u) (n : ℕ) (P : HostNet F L a z → Prop) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (q : I → HostNet F L a z), Fintype.card I ≤ 2 ^ n ∧
    (∀ x y, ∑ i, (q i).diagram.eval x y = G.diagram.eval x y) ∧ ∀ i, G.Preserves (q i) ∧ P (q i)

variable {P P' : HostNet F L a z → Prop} {Q : HostNet F L b w → Prop} {n m : ℕ}

-- 读法：要证明的命题是 `G.Expands n P`。
theorem Expands.single (q : HostNet F L a z) (he : ∀ x y, q.diagram.eval x y = G.diagram.eval x y)
    (hp : G.Preserves q) (hq : P q) : G.Expands n P :=
  ⟨Unit, inferInstance, fun _ => q, Nat.one_le_pow _ _ (by decide),
    fun x y => by simpa using he x y, fun _ => ⟨hp, hq⟩⟩

-- 读法：要证明的命题是 `G.Expands m P'`。
theorem Expands.mono (h₁ : G.Expands n P) (hn : n ≤ m) (h₂ : ∀ q, P q → P' q) :
    G.Expands m P' := by
  obtain ⟨I, _, q, hi, he, h⟩ := h₁
  exact ⟨I, inferInstance, q, hi.trans (Nat.pow_le_pow_right (by decide) hn), he,
    fun i => ⟨(h i).1, h₂ _ (h i).2⟩⟩

-- 读法：要证明的命题是 `G.Expands (n + m) Q`。这里调用 `Nat.mul_le_mul_right`。
theorem Expands.bind (hf : G.Expands n P) (hg : ∀ q, P q → q.Expands m Q) :
    G.Expands (n + m) Q := by
  obtain ⟨I, _, q, hi, he, hp⟩ := hf
  choose J hJ t ht he' hp' using fun i => hg (q i) (hp i).2
  let : ∀ i, Fintype (J i) := hJ
  refine ⟨Σ i, J i, inferInstance, fun p => t p.1 p.2, ?_, ?_, ?_⟩
  · rw [Fintype.card_sigma, pow_add]
    refine le_trans (sum_le_sum (s := univ) fun i _ => ht i) ?_
    simpa only [sum_const, card_univ, Nat.nsmul_eq_mul] using Nat.mul_le_mul_right (2 ^ m) hi
  · intro x y
    rw [Fintype.sum_sigma]
    simp only [he', he]
  · exact fun p => ⟨(hp p.1).1.trans (hp' p.1 p.2).1, (hp' p.1 p.2).2⟩

variable [Fintype T]

omit [Field F] in
-- 读法：要证明的命题是 `G.Bounded Δ' D' B'`。
theorem Bounded.mono {G : HostNet F L h u} {Δ Δ' D D' : ℕ} {B B' : ℝ}
    (hg : G.Bounded Δ D B) (hΔ : Δ ≤ Δ') (hD : D ≤ D') (hB : B ≤ B') :
    G.Bounded Δ' D' B' :=
  ⟨fun v => (hg.1 v).trans hΔ, fun v => (hg.2.1 v).trans hD,
    fun v i => (hg.2.2 v i).trans hB⟩

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# 核心接连收缩时的系线端点

即使宿主的完整度数大得多，系线的可能源位置集合也只取决于核心度数。对目的地计数时还需计入块数之比。

**英文原文**

Tether ends through a sequence of core contractions

The set of possible source positions of a tether depends only on core
degrees, even when the full host has much larger degree. Counting
destinations also pays the ratio of block counts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

open Finset
open scoped Classical

variable {F T : Type} {x y : Wire} {L : Fringe x y T} {h a b u z w : ℕ}
  (G : HostNet F L h u) (Q : HostNet F L a z) (R : HostNet F L b w)

-- 读法：`tip` 的取值由 `(G.units.place (portEnd G.diagram t)).1` 给出。
def tip (t : slots x ⊕ slots y) := (G.units.place (portEnd G.diagram t)).1

-- 读法：`reach` 的取值由 `(univ.filter fun t => G.tip t = v).image Q.tip` 给出。
def reach (v : G.V) : Finset Q.V :=
  (univ.filter fun t => G.tip t = v).image Q.tip

-- 读法：`q ∈ G.reach Q v` 与 `∃ t, G.tip t = v ∧ Q.tip t = q` 等价。
theorem mem_reach {v : G.V} {q : Q.V} :
    q ∈ G.reach Q v ↔ ∃ t, G.tip t = v ∧ Q.tip t = q := by simp [reach]

-- 读法：`Q.tip t` 属于 `G.reach Q (G.tip t)`。使用 `mem_reach` 给出的结论。
theorem reach_self (t : slots x ⊕ slots y) : Q.tip t ∈ G.reach Q (G.tip t) :=
  (mem_reach _ _).mpr ⟨t, rfl, rfl⟩

-- 读法：`(G.reach R v).card` 不超过 `K * K'`。这里调用 `mem_biUnion.mpr`。
private theorem chain {K K' : ℕ} (hg : ∀ p, (G.reach Q p).card ≤ K)
    (hq : ∀ p, (Q.reach R p).card ≤ K') (v : G.V) : (G.reach R v).card ≤ K * K' := by
  have sub : G.reach R v ⊆ (G.reach Q v).biUnion (Q.reach R) := by
    intro t ht
    obtain ⟨i, rfl, rfl⟩ := (mem_reach _ _).mp ht
    exact mem_biUnion.mpr ⟨Q.tip i, reach_self _ _ i, reach_self _ _ i⟩
  refine (card_le_card sub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum (fun t _ => hq t)).trans ?_
  simpa only [sum_const, Nat.nsmul_eq_mul] using Nat.mul_le_mul_right K' (hg v)

-- 读法：`Tracks` 表示以下条件：`(∀ v, (Q.reach G v).card ≤ K)` 与 `(∀ v, (G.reach Q v).card ≤ K * 2 ^ (h - a))` 同时成立。
def Tracks (K : ℕ) : Prop :=
  (∀ v, (Q.reach G v).card ≤ K) ∧ (∀ v, (G.reach Q v).card ≤ K * 2 ^ (h - a))

variable {G Q R} {K H : ℕ}

-- 读法：要证明的命题是 `G.Tracks Q H`。
theorem Tracks.mono (p : G.Tracks Q K) (h : K ≤ H) : G.Tracks Q H :=
  ⟨fun v => (p.1 v).trans h, fun v => (p.2 v).trans (Nat.mul_le_mul_right _ h)⟩

-- 读法：要证明的命题是 `G.Tracks R (H * K)`。
theorem Tracks.trans (p : G.Tracks Q K) (q : Q.Tracks R H) (ha : a ≤ h) (hb : b ≤ a) :
    G.Tracks R (H * K) := by
  refine ⟨chain R Q G q.1 p.1, fun v => (chain G Q R p.2 q.2 v).trans_eq ?_⟩
  rw [show h - b = (h - a) + (a - b) by omega, pow_add]
  ring

-- 读法：要证明的命题是 `G.Tracks Q (K * H)`。
/-- 各站可以移至邻点的槽位。

英文原文：Individual stations can move to a neighbor's slots.
-/
theorem tracks_of_slots {A : Type} [Fintype A] (f : Q.V ≃ G.V × A) (N : G.V → Finset G.V)
    (hN : ∀ u v, v ∈ N u → u ∈ N v) (hsize : ∀ v, (N v).card ≤ K)
    (hpos : 0 < H) (seats : Fintype.card Q.V ≤ H * 2 ^ (h - a) * Fintype.card G.V)
    (loc : ∀ t, (f (Q.tip t)).1 ∈ N (G.tip t)) : G.Tracks Q (K * H) := by
  constructor
  · intro q
    refine (card_le_card (t := N (f q).1) ?_).trans ((hsize _).trans (Nat.le_mul_of_pos_right _ hpos))
    intro v hv
    obtain ⟨t, rfl, rfl⟩ := (mem_reach _ _).mp hv
    exact hN _ _ (loc t)
  intro v
  -- 推导：记下中间结论 `bound`：`Fintype.card A ≤ H * 2 ^ (h - a)`。
  have bound : Fintype.card A ≤ H * 2 ^ (h - a) := by
    rw [Fintype.card_congr f, Fintype.card_prod, mul_comm (Fintype.card G.V)] at seats
    exact Nat.le_of_mul_le_mul_right seats (Fintype.card_pos_iff.mpr ⟨v⟩)
  have sub : (G.reach Q v).image f ⊆ (N v) ×ˢ univ := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    obtain ⟨t, rfl, rfl⟩ := (mem_reach _ _).mp hz
    exact mem_product.mpr ⟨loc t, mem_univ _⟩
  have hc := card_le_card sub
  rw [card_image_of_injective _ f.injective, card_product, card_univ] at hc
  rw [mul_assoc]
  exact hc.trans (Nat.mul_le_mul (hsize _) bound)

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# 复合多个分组步骤

宽度估计对原宽度以及冻结费用与余量之和呈仿射形式；其余界是乘法形式。对席位计数，即以宿主位置数乘以块数，可使余量估计与每步聚合的块数无关。

**英文原文**

Composing grouping steps

The width estimate is affine in the old width and the sum of frozen
charge and slack. The other bounds are multiplicative. Counting seats
(host positions times blocks) makes the slack estimate independent of
how many blocks are grouped at a step.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open HostNet

-- 读法：结构的字段包括 `unit`、`overhead`、`degree`、`factor`、`loss`。
/-- 细分因子为 `b` 的归约，使用 `n` 个分组步骤，满度数指数为 `e`，额外开销为 `K`。即使复合多个归约，选择器长度仍有一个以输出宽度为单位的上界。

英文原文：A reduction with subdivision factor `b`, using `n` grouping steps,
full-degree exponent `e` and overhead `K`. The selector length is
bounded in units of the output width, even across composed reductions.
-/
structure Reduction (F : Type) [Field F] (Δ Δ' b n e K : ℕ) (ρ C : ℝ) : Prop where
  unit : 0 < b
  overhead : 0 < K
  degree : ∀ D, Δ ≤ D → Δ' ≤ D ^ e
  factor : 0 ≤ ρ
  loss : 0 ≤ C
  run : ∀ {T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T}
    {h u : ℕ} (G : HostNet F L h u) (z r a D M : ℕ) (B σ : ℝ),
    0 < z → u = b * z → u ≤ B → Δ ≤ D → G.Bounded Δ D B → 0 ≤ σ →
    a + n * r ≤ h → K ≤ 2 ^ r → (K : ℝ) * B * G.seats ≤ σ * (2 : ℝ) ^ r → G.X + (L.Z + σ) ≤ (M : ℝ) * z →
    G.Expands (K * M) (fun Q : HostNet F L a z =>
      Q.seats ≤ K * G.seats ∧ Q.Bounded Δ' (D ^ e) (K * B) ∧ Q.X ≤ ρ * G.X + C * (L.Z + σ) ∧
      (Q.mass : ℝ) ≤ G.mass + 2 * (K : ℝ) * (G.X + (L.Z + σ)) ∧ G.Tracks Q K)

namespace Reduction

variable {F : Type} [Field F] {Δ Δ' Δ'' b b' n n' e e' K K' : ℕ} {ρ ρ' C C' : ℝ}

-- 读法：`fee` 的取值由 `K + K * K + ⌈ρ + C + 1⌉₊` 给出。
def fee (K : ℕ) (ρ C : ℝ) := K + K * K + ⌈ρ + C + 1⌉₊

-- 读法：要证明的命题是 `Reduction F Δ Δ'' (b * b') (n + n') (e * e') (fee K ρ C * K') (ρ' * ρ) (ρ' * C + C')`。
theorem comp (p : Reduction F Δ Δ' b n e K ρ C) (q : Reduction F Δ' Δ'' b' n' e' K' ρ' C') :
    Reduction F Δ Δ'' (b * b') (n + n') (e * e') (fee K ρ C * K') (ρ' * ρ) (ρ' * C + C') := by
  let s := ⌈ρ + C + 1⌉₊
  let H := fee K ρ C * K'
  have hk := p.overhead
  have hk' := q.overhead
  have hf : K + K' * s ≤ H := by
    calc
      _ ≤ K * K' + K' * s := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hk') _
      _ = (K + s) * K' := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by unfold fee; omega)
  -- 推导：记下中间结论 `hm`：`K' * K * K ≤ H`。
  have hm : K' * K * K ≤ H := by
    rw [mul_assoc, mul_comm K']
    exact Nat.mul_le_mul_right _ (by unfold fee; omega)
  have hprod : K' * K ≤ H := (Nat.le_mul_of_pos_right _ hk).trans hm
  have hkH : K ≤ H := (Nat.le_add_right _ _).trans hf
  have hkH' : K' ≤ H := (Nat.le_mul_of_pos_right _ hk).trans hprod
  refine ⟨Nat.mul_pos p.unit q.unit, hk.trans_le hkH, ?_, mul_nonneg q.factor p.factor,
    add_nonneg (mul_nonneg q.factor p.loss) q.loss, ?_⟩
  · intro D hd
    rw [pow_mul]
    exact q.degree _ (p.degree _ hd)
  intro T _ x y L h u G z r a D M B σ hz hu huB hD hb hσ ha hr slack budget
  let mid := a + n' * r
  let U := b' * z
  -- 推导：记下中间结论 `hB`：`0 ≤ B`。
  have hB : 0 ≤ B := (Nat.cast_nonneg u).trans huB
  have hL : 0 ≤ L.Z + σ := add_nonneg L.total_nonneg hσ
  have hu' : u = b * U := by unfold U; rw [hu, mul_assoc]
  have hz' : 0 < U := Nat.mul_pos q.unit hz
  have hU : U ≤ u := by rw [hu']; exact Nat.le_mul_of_pos_left _ p.unit
  have hzu : z ≤ U := Nat.le_mul_of_pos_left _ q.unit
  have hs : (K : ℝ) * B * G.seats ≤ σ * (2 : ℝ) ^ r := by
    refine le_trans ?_ slack
    gcongr
  have hl := p.run G U r mid D M B σ hz' hu' huB hD hb hσ
    (by unfold mid; rw [add_mul] at ha; omega) (hkH.trans hr) hs
    (budget.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hzu) (Nat.cast_nonneg _)))
  -- 推导：记下中间结论 `sel`：`K * M + K' * (s * M) ≤ H * M`。
  have sel : K * M + K' * (s * M) ≤ H * M := by
    rw [← mul_assoc, ← add_mul]
    exact Nat.mul_le_mul_right _ hf
  refine (hl.bind (m := K' * (s * M)) ?_).mono sel (fun _ h => h)
  rintro Q ⟨hseat, hbound, hwidth, hist, track⟩
  have hub' : (U : ℝ) ≤ (K : ℝ) * B := calc
    _ ≤ (u : ℝ) := Nat.cast_le.mpr hU
    _ ≤ B := huB
    _ ≤ _ := le_mul_of_one_le_left hB (by exact_mod_cast hk)
  have hs' : (K' : ℝ) * (K * B) * Q.seats ≤ σ * 2 ^ r := calc
    _ ≤ (K' : ℝ) * (K * B) * (K * G.seats) := by gcongr; exact_mod_cast hseat
    _ = ((K' * K * K : ℕ) : ℝ) * B * G.seats := by push_cast; ring
    _ ≤ (H : ℝ) * B * G.seats := by gcongr
    _ ≤ _ := slack
  -- 推导：记下中间结论 `hQ`：`Q.X + (L.Z + σ) ≤ (s : ℝ) * (G.X + (L.Z + σ))`。
  have hQ : Q.X + (L.Z + σ) ≤ (s : ℝ) * (G.X + (L.Z + σ)) := calc
    _ ≤ (ρ + C + 1) * (G.X + (L.Z + σ)) := by
      nlinarith only [hwidth, mul_nonneg p.factor hL,
        mul_nonneg p.loss (Nat.cast_nonneg (α := ℝ) G.X), Nat.cast_nonneg (α := ℝ) G.X]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have ht : Q.X + (L.Z + σ) ≤ ((s * M : ℕ) : ℝ) * z := by
    rw [Nat.cast_mul, mul_assoc]
    exact hQ.trans (mul_le_mul_of_nonneg_left budget (Nat.cast_nonneg _))
  have hh := q.run Q z r a (D ^ e) (s * M) _ σ hz rfl hub' (p.degree _ hD) hbound hσ
    le_rfl (hkH'.trans hr) hs' ht
  refine hh.mono le_rfl ?_
  rintro R ⟨hseat', hbound', hwidth', hist', track'⟩
  refine ⟨hseat'.trans ?_, hbound'.mono le_rfl (pow_mul _ _ _).ge ?_, ?_, ?_,
    (track.trans track' (by unfold mid; rw [add_mul] at ha; omega) (Nat.le_add_right _ _)).mono hprod⟩
  · exact (Nat.mul_le_mul_left _ hseat).trans (by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hprod)
  · rw [← mul_assoc, ← Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hprod) hB
  · have hw := mul_le_mul_of_nonneg_left hwidth q.factor
    linarith
  · calc
      (R.mass : ℝ) ≤ Q.mass + 2 * (K' : ℝ) * (Q.X + (L.Z + σ)) := hist'
      _ ≤ (G.mass + 2 * (K : ℝ) * (G.X + (L.Z + σ))) +
          2 * (K' : ℝ) * ((s : ℝ) * (G.X + (L.Z + σ))) :=
        add_le_add hist (mul_le_mul_of_nonneg_left hQ (by positivity))
      _ = G.mass + 2 * ((K + K' * s : ℕ) : ℝ) * (G.X + (L.Z + σ)) := by push_cast; ring
      _ ≤ G.mass + 2 * (H : ℝ) * (G.X + (L.Z + σ)) := by gcongr

end Reduction
end OAI.LinearAlgebra.MatrixExponent.Packing
end
