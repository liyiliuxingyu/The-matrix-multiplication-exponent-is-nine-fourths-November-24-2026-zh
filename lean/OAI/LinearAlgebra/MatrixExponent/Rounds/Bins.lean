-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path

/-!
# 转置并行端口的叠层

每一层都将副本地址的一个比特与端口地址的对应比特交换，余下比特记录在线束内的次序。由此得到有界的度数，无需假定原图中相邻站点的元数相近。

**英文原文**

Transposing a stack of parallel ports

At each layer one bit of the copy address is exchanged with the
corresponding bit of the port address. The remaining bits record the
order inside the bundle. This gives bounded degree without requiring
adjacent original stations to have comparable arities.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Classical

variable {V : Type} {t : ℕ} (d : V → ℕ)

-- 读法：在后续公式中，`Node` 是 `(Σ v, Cell (d v)) × Fin (t + 1)` 的缩写。
abbrev Node := (Σ v, Cell (d v)) × Fin (t + 1)

namespace Node

variable {d} (hd : ∀ v, d v ≤ t)

-- 读法：当 `i.val < k` 成立时取 `p i`，否则取 `x (i.castLE (hd v))`。
def address (k : ℕ) (v : V) (x : Cell t) (p : Cell (d v)) : Cell (d v) :=
  fun i => if i.val < k then p i else x (i.castLE (hd v))

-- 读法：当 `h : k ≤ i.val ∧ i.val < d v` 成立时取 `p ⟨i.val, h.2⟩`，否则取 `x i`。
def residue (k : ℕ) (v : V) (x : Cell t) (p : Cell (d v)) : Cell t :=
  fun i => if h : k ≤ i.val ∧ i.val < d v then p ⟨i.val, h.2⟩ else x i

-- 读法：`x = y` 与 `p = q` 同时成立。用函数外延性比较等号两侧在 `i` 处的取值。
theorem inject (k : ℕ) (v : V) {x y : Cell t} {p q : Cell (d v)}
    (h₁ : address hd k v x p = address hd k v y q)
    (h₂ : residue k v x p = residue k v y q) : x = y ∧ p = q := by
  constructor
  · funext i
    by_cases h : k ≤ i.val ∧ i.val < d v
    · simpa only [address, ite_eq_right h.1.not_gt, Fin.castLE_mk, Fin.eta] using
        congrFun h₁ (⟨i, h.2⟩ : Fin (d v))
    · simpa [residue, h] using congrFun h₂ i
  · funext i
    by_cases h : i.val < k
    · simpa [address, h] using congrFun h₁ i
    · simpa [residue, not_lt.mp h] using congrFun h₂ (i.castLE (hd v))

-- 读法：`atLayer` 的取值由 `(⟨p.1, address hd k.val p.1 x p.2⟩, k)` 给出。
def atLayer (k : Fin (t + 1)) (x : Cell t) (p : Σ v, Cell (d v)) : Node (t := t) d :=
  (⟨p.1, address hd k.val p.1 x p.2⟩, k)

-- 读法：`start` 的取值由 `(⟨v, ancestor (hd v) x⟩, 0)` 给出。
def start (v : V) (x : Cell t) : Node (t := t) d := (⟨v, ancestor (hd v) x⟩, 0)

-- 读法：`atLayer hd 0 x p` 等于 `start hd p.1 x`。两端由定义化简为同一项。
@[simp] theorem layer_zero (x : Cell t) (p : Σ v, Cell (d v)) :
    atLayer hd 0 x p = start hd p.1 x := rfl

-- 读法：`atLayer hd (Fin.last t) x p` 等于 `(p, Fin.last t)`。用函数外延性比较等号两侧在 `i; exact ite_eq_left (i.isLt.trans_le (hd _))` 处的取值。
@[simp] theorem layer_last (x : Cell t) (p : Σ v, Cell (d v)) :
    atLayer hd (Fin.last t) x p = (p, Fin.last t) := by
  have he : address hd t p.1 x p.2 = p.2 := by
    funext i; exact ite_eq_left (i.isLt.trans_le (hd _))
  simp only [atLayer, Fin.val_last, he, Sigma.eta]

-- 读法：`i = j` 与 `x = y ∧ p = q` 同时成立。
/-- 给定位置和剩余比特地址，至多有一个端点使用这对数据。

英文原文：At most one endpoint uses a given position and residual bit address.
-/
theorem layer_inj {i j : Fin (t + 1)} {x y : Cell t} {p q : Σ v, Cell (d v)}
    (hp : atLayer hd i x p = atLayer hd j y q)
    (hr : residue i.val p.1 x p.2 = residue j.val q.1 y q.2) :
    i = j ∧ x = y ∧ p = q := by
  have hij : i = j := congrArg Prod.snd hp
  subst j
  rcases p with ⟨u, p⟩; rcases q with ⟨v, q⟩
  have huv : u = v := congrArg (fun z => z.1.1) hp
  subst v
  have h : address hd i u x p = address hd i u y q := by
    simpa [atLayer] using congrArg Prod.fst hp
  obtain ⟨rfl, rfl⟩ := inject hd i u h hr
  exact ⟨rfl, rfl, rfl⟩

-- 读法：`next` 的取值由 `(⟨p.1.1, fun i => if i.val = min p.2.val j.val then b else p.1.2 i⟩, j)` 给出。
-- 相邻层的邻点至多在一个坐标上不同。
def next (p : Node (t := t) d) (j : Fin (t + 1)) (b : ZMod 2) : Node (t := t) d :=
  (⟨p.1.1, fun i => if i.val = min p.2.val j.val then b else p.1.2 i⟩, j)

-- 读法：`links` 的结果类型为 `Finset (Node (t := t) d)`。
def links (p : Node (t := t) d) : Finset (Node (t := t) d) :=
  (Finset.univ.image (next p ⟨p.2.val - 1, by have := p.2.isLt; omega⟩)) ∪
    (Finset.univ.image (next p ⟨min t (p.2.val + 1), by omega⟩))

-- 读法：`(links p).card` 不超过 `4`。这里调用 `Nat.add_le_add`。
theorem links_card (p : Node (t := t) d) : (links p).card ≤ 4 := by
  unfold links
  refine (Finset.card_union_le _ _).trans ?_
  have h (j) : (Finset.univ.image (next p j)).card ≤ 2 :=
    Finset.card_image_le.trans (by simp)
  exact Nat.add_le_add (h _) (h _)

-- 读法：`atLayer hd j x p` 属于 `links (atLayer hd i x p)`。用函数外延性比较等号两侧在 `e` 处的取值。
theorem layer_link (i j : Fin (t + 1)) (hc : i.val + 1 = j.val ∨ j.val + 1 = i.val)
    (x : Cell t) (p : Σ v, Cell (d v)) : atLayer hd j x p ∈ links (atLayer hd i x p) := by
  let v := p.1
  let k := min i.val j.val
  let b := if h : k < d v then address hd j.val v x p.2 ⟨k, h⟩ else 0
  have hm : next (atLayer hd i x p) j b = atLayer hd j x p := by
    unfold next atLayer
    congr 2
    funext e
    change (if e.val = k then b else address hd i.val v x p.2 e) = address hd j.val v x p.2 e
    by_cases he : e.val = k
    -- 推导：记下中间结论 `hv`：`e.val < d v`。
    · have hv : e.val < d v := e.isLt
      simp [he.symm, b, hv]
    · have : (e.val < i.val) = (e.val < j.val) := propext (by unfold k at he; omega)
      simp only [ite_eq_right he, address, this]
  unfold links
  apply Finset.mem_union.mpr
  rcases hc with h|h
  · right
    have h' : min t ((atLayer hd i x p).2.val + 1) = j.val := by
      change min t (i.val + 1) = _; have := j.isLt; omega
    simp only [h', Fin.eta]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hm⟩
  · left
    -- 推导：记下中间结论 `h'`：`(atLayer hd i x p).2.val - 1 = j.val`。
    have h' : (atLayer hd i x p).2.val - 1 = j.val := by change i.val - 1 = _; omega
    simp only [h', Fin.eta]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hm⟩

end Node
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 在保持平方和预算的条件下装包站点

在每个单元中，把下一个站点放在任一负载不超过最终平均上界的槽位上。这样无需单独处理大型站点。

**英文原文**

Packing stations without losing the square budget

At each cell place the next station in any slot of load at most
the final average bound. This avoids a separate case for large stations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset
open scoped Classical

-- 读法：存在 `s : A → Fin D`，`(∑ z, (push (fun x => (f x, s x)) l z) ^ 2)` 不超过 `(∑ x, l x ^ 2) + 2 * T * (∑ x, l x)`。
theorem bins {A B : Type} [Fintype A] [Fintype B] (f : A → B) (l : A → ℝ)
    (D : ℕ) (T : ℝ) (hD : 0 < D) (hl : ∀ x, 0 ≤ l x) (hb : ∀ b, push f l b ≤ D * T) :
    ∃ s : A → Fin D, (∑ z, (push (fun x => (f x, s x)) l z) ^ 2) ≤
      (∑ x, l x ^ 2) + 2 * T * (∑ x, l x) := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  let mass (S : Finset A) (s : A → Fin D) (z : B × Fin D) :=
    ∑ x ∈ S, if (f x, s x) = z then l x else 0
  have cap S s b : (∑ i, mass S s (b, i)) ≤ D * T := by
    unfold mass
    rw [sum_comm]
    simp only [Prod.mk.injEq, ite_and, sum_ite_irrel, sum_ite_eq, mem_univ, ite_true, sum_const_zero]
    refine le_trans ?_ (hb b)
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => by
      split_ifs <;> first | exact hl x | exact le_rfl
  have aux (S : Finset A) : ∃ s, (∑ z, (mass S s z) ^ 2) ≤
      (∑ x ∈ S, l x ^ 2) + 2 * T * (∑ x ∈ S, l x) := by
    induction S using Finset.induction with
    | empty => exact ⟨fun _ => ⟨0, hD⟩, by simp [mass]⟩
    | @insert x S hx ih =>
      -- 推导：从 `ih` 中取出 `s, hs`。
      obtain ⟨s, hs⟩ := ih
      have he : (∑ i, mass S s (f x, i)) ≤ ∑ _i : Fin D, T := by simpa using cap S s (f x)
      obtain ⟨i, _, hi⟩ := exists_le_of_sum_le univ_nonempty he
      let s' := Function.update s x i
      have eq z : mass (insert x S) s' z = (if (f x, i) = z then l x else 0) + mass S s z := by
        unfold mass
        rw [sum_insert hx, show s' x = i by simp [s']]
        congr 1
        apply sum_congr rfl
        intro y hy
        rw [show s' y = s y from Function.update_of_ne (show y ≠ x from fun e => hx (e ▸ hy)) _ _]
      have sq z : (mass (insert x S) s' z) ^ 2 ≤
          (if (f x, i) = z then l x ^ 2 + 2 * T * l x else 0) + (mass S s z) ^ 2 := by
        rw [eq]
        split_ifs with h
        · subst z
          nlinarith only [mul_le_mul_of_nonneg_right hi (hl x)]
        · simp
      refine ⟨s', ?_⟩
      have := sum_le_sum (s := univ) (fun z _ => sq z)
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true] at this
      rw [sum_insert hx, sum_insert hx]
      linarith
  -- 推导：从 `aux univ` 中取出 `s, hs`。
  obtain ⟨s, hs⟩ := aux univ
  refine ⟨s, ?_⟩
  have he z : push (fun x => (f x, s x)) l z = mass univ s z := by
    apply sum_congr rfl
    intro x _
    split_ifs <;> rfl
  simpa only [he] using hs

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 初始叠层的有界度宿主图

沿一个站点的各条连接形成蝴蝶网络。在它的末层，每个互异的原端口地址至多只需与另一个地址相连。平行边和自环也都适用。

**英文原文**

A bounded-degree host for an initial stack

The links along one station form a butterfly. On its last layer,
distinct original port addresses can each be joined to at most one
other address. This works also for parallel edges and loops.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Packing Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b) {h t : ℕ}

-- 读法：`dim` 的取值由 `Nat.clog 2 (G.arity v)` 给出。
def dim (v : G.V) := Nat.clog 2 (G.arity v)

-- 读法：在后续公式中，`Site` 是 `Node (t := t) (dim G)` 的缩写。
abbrev Site (t : ℕ) := Node (t := t) (dim G)

-- 读法：`Fintype.card (Site G t)` 不超过 `2 * G.cost * (t + 1)`。按 `G.arity v = 0` 成立与否分情况。
theorem card (t : ℕ) : Fintype.card (Site G t) ≤ 2 * G.cost * (t + 1) := by
  rw [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, Diagram.cost, Finset.mul_sum]
  refine Nat.mul_le_mul_right _ (Finset.sum_le_sum (fun v _ => ?_))
  rw [card_cell, dim]
  by_cases h : G.arity v = 0
  · simp [h]
  · exact (Transcript.pow_clog_le_twice (Nat.pos_of_ne_zero h)).trans (by omega)

-- 读法：`address` 的结果类型为 `G.Port v ↪ Cell (dim G v)`。
private def address (v : G.V) : G.Port v ↪ Cell (dim G v) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_sum, card_slots, card_slots, card_cell]
    exact Nat.le_pow_clog (by decide) _))

-- 读法：`port` 的结果类型为 `G.End ↪ Σ v, Cell (dim G v)`。
def port : G.End ↪ Σ v, Cell (dim G v) :=
  G.portEquiv.symm.toEmbedding.trans
    ⟨fun z => ⟨z.1, address G z.1 z.2⟩, by
      rintro ⟨v, p⟩ ⟨w, q⟩ he
      have hv : v = w := congrArg Sigma.fst he
      subst w
      have hp := (address G v).injective (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
      exact congrArg (Sigma.mk v) hp⟩

-- 读法：`(port G e).1` 等于 `G.station e`。
theorem station (e : G.End) : (port G e).1 = G.station e := by
  have := (G.station_port (G.portEquiv.symm e)).symm
  rwa [Equiv.apply_symm_apply] at this

-- 读法：逐一匹配以下输入模式：`.inl (.inr e)`、`.inr (.inr e)`、`x`。
def other : G.End → G.End
  | .inl (.inr e) => .inr (.inr e)
  | .inr (.inr e) => .inl (.inr e)
  | x => x

-- 读法：当 `h : ∃ e, port G e = z.1` 成立时取 `(port G (other G h.choose), z.2)`，否则取 `z`。
def peer (z : Site G t) : Site G t :=
  if h : ∃ e, port G e = z.1 then (port G (other G h.choose), z.2) else z

-- 读法：`peer G (port G e, i)` 等于 `(port G (other G e), i)`。
theorem peer_port (e : G.End) (i : Fin (t + 1)) :
    peer G (port G e, i) = (port G (other G e), i) := by
  have h : ∃ z, port G z = port G e := ⟨e, rfl⟩
  simp only [peer, dite_eq_left h, (port G).injective h.choose_spec]

-- 读法：`adjacent` 的取值由 `(insert (peer G z) (Node.links z)).filter fun w => z ∈ insert (peer G w) (Node.links w)` 给出。
-- 要求双方互相包含，便可由构造直接保证宿主图的对称性。
def adjacent (z : Site G t) :=
  (insert (peer G z) (Node.links z)).filter fun w => z ∈ insert (peer G w) (Node.links w)

-- 读法：`v` 属于 `adjacent G z`。
theorem adj_sym (v z : Site G t) (hv : z ∈ adjacent G v) : v ∈ adjacent G z := by
  simpa only [adjacent, Finset.mem_filter, and_comm] using hv

-- 读法：`(adjacent G v).card` 不超过 `5`。
theorem adj_card (v : Site G t) : (adjacent G v).card ≤ 5 :=
  (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Node.links_card v) 1))

variable (bound : ∀ v, dim G v ≤ t)

-- 读法：`place` 的取值由 `Node.atLayer bound i x (port G e)` 给出。
def place (i : Fin (t + 1)) (x : Cell t) (e : G.End) : Site G t :=
  Node.atLayer bound i x (port G e)

-- 读法：`place G bound j x e` 属于 `adjacent G (place G bound i x e)`。
theorem line (i j : Fin (t + 1)) (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) (x : Cell t) (e : G.End) :
    place G bound j x e ∈ adjacent G (place G bound i x e) :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_insert_of_mem (Node.layer_link bound i j h x _),
     Finset.mem_insert_of_mem (Node.layer_link bound j i h.symm x _)⟩

-- 读法：当 `k ≤ t` 成立时取 `.inl (.inr e)`，否则取 `.inr (.inr e)`。
def endpoint {t : ℕ} (e : G.E) (k : ℕ) : G.End :=
  if k ≤ t then .inl (.inr e) else .inr (.inr e)

-- 读法：`level` 的结果类型为 `Fin (t + 1)`。
def level (t k : ℕ) : Fin (t + 1) := ⟨min k (2 * t + 1 - k), by omega⟩

-- 读法：`walk` 的取值由 `place G bound (level t k) x (endpoint (t := t) G e k)` 给出。
def walk (k : ℕ) (x : Cell t) (e : G.E) : Site G t :=
  place G bound (level t k) x (endpoint (t := t) G e k)

-- 读法：`walk G bound 0 x e` 等于 `Node.start bound (G.source e) x`。
theorem walk_start (x : Cell t) (e : G.E) :
    walk G bound 0 x e = Node.start bound (G.source e) x := by
  rw [walk, place, show level t 0 = 0 by ext; simp [level], Node.layer_zero, station]
  simp [endpoint, Diagram.station, Diagram.source]

-- 读法：`walk G bound (2 * t + 1) x e` 等于 `Node.start bound (G.target e) x`。
theorem walk_end (x : Cell t) (e : G.E) :
    walk G bound (2 * t + 1) x e = Node.start bound (G.target e) x := by
  rw [walk, place, show level t (2 * t + 1) = 0 by ext; simp [level], Node.layer_zero, station]
  simp [endpoint, Diagram.station, Diagram.target, show ¬ 2 * t + 1 ≤ t by omega]

-- 读法：`walk G bound (k + 1) x e` 属于 `adjacent G (walk G bound k x e)`。
theorem walk_adj (x : Cell t) (e : G.E) (k : ℕ) (hk : k < 2 * t + 1) :
    walk G bound (k + 1) x e ∈ adjacent G (walk G bound k x e) := by
  rcases lt_trichotomy k t with h | he | h
  · unfold walk endpoint
    rw [ite_eq_left (show k + 1 ≤ t by omega), ite_eq_left h.le]
    exact line G bound _ _ (by left; dsimp [level]; omega) _ _
  · subst k
    have h₁ : level t t = Fin.last t := Fin.ext (by simp [level]; omega)
    have h₂ : level t (t + 1) = Fin.last t := Fin.ext (by simp [level]; omega)
    simp only [walk, h₁, h₂, endpoint, ite_eq_left le_rfl, ite_eq_right (show ¬t + 1 ≤ t by omega),
      place, Node.layer_last, adjacent, Finset.mem_filter, Finset.mem_insert, peer_port, other]
    simp
  · unfold walk endpoint
    rw [ite_eq_right (show ¬ k + 1 ≤ t by omega), ite_eq_right h.not_ge]
    exact line G bound _ _ (by right; dsimp [level]; omega) _ _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# 估计叠层中的端口占用数

**英文原文**

Bounding port occupancy in a stack
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Packing Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b) {t h : ℕ} (bound : ∀ v, dim G v ≤ t)

-- 读法：在后续公式中，`Index` 是 `Cell t × Cell h` 的缩写。
abbrev Index (t h : ℕ) := Cell t × Cell h
-- 读法：在后续公式中，`Task` 是 `Fin (t + 1) × Index t h × G.End` 的缩写。
abbrev Task := Fin (t + 1) × Index t h × G.End

-- 读法：`atTask` 的取值由 `(place G bound e.1 e.2.1.1 e.2.2, e.2.1.2)` 给出。
def atTask (e : Task G (t := t) (h := h)) : Site G t × Cell h :=
  (place G bound e.1 e.2.1.1 e.2.2, e.2.1.2)

-- 读法：`rest` 的取值由 `Node.residue e.1.val (port G e.2.2).1 e.2.1.1 (port G e.2.2).2` 给出。
private def rest (e : Task G (t := t) (h := h)) : Cell t :=
  Node.residue e.1.val (port G e.2.2).1 e.2.1.1 (port G e.2.2).2

-- 读法：`e` 等于 `f`。这里调用 `Prod.ext`。
private theorem unique_task {e f : Task G (t := t) (h := h)}
    (he : atTask G bound e = atTask G bound f) (hr : rest G e = rest G f) : e = f := by
  obtain ⟨h₁, h₂, h₃⟩ := Node.layer_inj bound (congrArg Prod.fst he) hr
  have h₄ := congrArg Prod.snd he
  exact Prod.ext h₁ (Prod.ext (Prod.ext h₂ h₄) ((port G).injective h₃))

-- 读法：`Fintype.card {x // k x = y}` 不超过 `2 ^ t`。这里调用 `Fintype.card_le_of_injective`。
theorem capacity {X : Type} [Fintype X] (f : X ↪ Task G (t := t) (h := h))
    (k : X → Site G t × Cell h) (eqn : ∀ x, atTask G bound (f x) = k x)
    (y : Site G t × Cell h) : Fintype.card {x // k x = y} ≤ 2 ^ t := by
  rw [← card_cell t]
  apply Fintype.card_le_of_injective (fun x : {x // k x = y} => rest G (f x))
  intro x z hr
  exact Subtype.ext (f.injective (unique_task G bound
    (by rw [eqn, eqn, x.property, z.property]) hr))

-- 读法：在后续公式中，`Channel` 是 `Fin (2 * t + 1) × Index t h × G.E` 的缩写。
abbrev Channel := Fin (2 * t + 1) × Index t h × G.E

-- 读法：`route` 的取值由 `(walk G bound j e.1.1 e.2, e.1.2)` 给出。
def route (j : ℕ) (e : Index t h × G.E) : Site G t × Cell h :=
  (walk G bound j e.1.1 e.2, e.1.2)

-- 读法：`task` 的取值由 `(level t (e.1.val + s), e.2.1, endpoint (t := t) G e.2.2 (e.1.val + s))` 给出。
private def task (s : ℕ) (e : Channel G (t := t) (h := h)) : Task G (t := t) (h := h) :=
  (level t (e.1.val + s), e.2.1, endpoint (t := t) G e.2.2 (e.1.val + s))

-- 读法：`(task (t := t) (h := h) G s)` 是单射。按 `i.val + s ≤ t <;> by_cases hj : j.val + s ≤ t` 成立与否分情况。
private theorem task_inj (s : ℕ) (hs : s ≤ 1) :
    Function.Injective (task (t := t) (h := h) G s) := by
  rintro ⟨i, x, e⟩ ⟨j, y, f⟩ he
  have h₁ : min (i.val + s) (2 * t + 1 - (i.val + s)) = min (j.val + s) (2 * t + 1 - (j.val + s)) :=
    congrArg (fun z => z.1.val) he
  have h₂ : x = y := congrArg (fun z => z.2.1) he
  have h₃ : endpoint (t := t) G e (i.val + s) = endpoint (t := t) G f (j.val + s) :=
    congrArg (fun z => z.2.2) he
  by_cases hi : i.val + s ≤ t <;> by_cases hj : j.val + s ≤ t
  all_goals simp [endpoint, hi, hj] at h₃
  all_goals have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
  all_goals simp only [this, h₂, h₃]

-- 读法：`Fintype.card {e : Channel G (t := t) (h := h) // route G bound (e.1.val + s) e.2 = y}` 不超过 `2 ^ t`。
theorem edge_capacity (s : ℕ) (hs : s ≤ 1) (y : Site G t × Cell h) :
    Fintype.card {e : Channel G (t := t) (h := h) // route G bound (e.1.val + s) e.2 = y} ≤ 2 ^ t :=
  capacity G bound ⟨_, task_inj G s hs⟩ _ (fun _ => rfl) y

-- 读法：`owner` 的取值由 `(Node.start bound p.2 p.1.1, p.1.2)` 给出。
def owner (p : Index t h × G.V) : Site G t × Cell h :=
  (Node.start bound p.2 p.1.1, p.1.2)

-- 读法：结论为 `Fintype.card {i : slots (copies a n) // owner G bound ((G.replicate c).src.symm (.inl i)).1 = y} ≤ 2 ^ t ∧ Fintype.card {i : slots (copies b n) // owner G bound ((G.replicate c).dst.symm (.inl i)).1 = y} ≤ 2 ^ t`。
theorem exterior_capacity {n : ℕ} (c : Index t h ≃ Fin n) (y : Site G t × Cell h) :
    Fintype.card {i : slots (copies a n) // owner G bound ((G.replicate c).src.symm (.inl i)).1 = y}
      ≤ 2 ^ t ∧
    Fintype.card {i : slots (copies b n) // owner G bound ((G.replicate c).dst.symm (.inl i)).1 = y}
      ≤ 2 ^ t := by
  have aux (w : Wire) (f : slots w ↪ G.End) :
      Fintype.card {i : slots (copies w n) //
        owner G bound (c.symm (Diagonal.port w n i).1, G.station (f (Diagonal.port w n i).2)) = y}
        ≤ 2 ^ t := by
    let e : slots (copies w n) ↪ Task G (t := t) (h := h) :=
      ((Diagonal.port w n).toEmbedding.trans (c.symm.toEmbedding.prodMap f)).trans
        ⟨fun p => (0, p), fun _ _ h => congrArg Prod.snd h⟩
    refine capacity G bound e _ ?_ y
    intro i
    change (Node.atLayer bound 0 _ _, _) = _
    rw [Node.layer_zero, station]
    rfl
  exact ⟨aux a (Function.Embedding.inl.trans Function.Embedding.inl),
    aux b (Function.Embedding.inl.trans Function.Embedding.inr)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

section
/-!
# 各轮交界处的不变量

每个出现位置至多有一个站点。空闲硬件可以零费用携带一个标量。正费用覆盖元数，并且至少为当前宽度的某个常数倍。

**英文原文**

The invariants at the boundary of each round

There is at most one station per occurrence. Empty hardware can carry
a scalar with zero charge. Positive charge covers the arity and has
a lower bound proportional to the current width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Packing Finset

-- 读法：结构的字段包括 `V`、`diagram`、`place`、`one`、`adj`。
structure Board (F : Type) (x y : Wire) (h : ℕ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  place : diagram.V → V × Cell h
  one : Function.Injective place
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  edge : ∀ e, let q := place (diagram.source e)
    let p := place (diagram.target e)
    p.2 = q.2 ∧ p.1 ∈ adj q.1
  charge : diagram.V → ℝ
  cover : ∀ v, diagram.arity v ≤ charge v

attribute [instance] Board.fv

namespace Board

variable {F : Type} {x y : Wire} {h : ℕ} (P : Board F x y h)

-- 读法：`seats` 的取值由 `Fintype.card P.V * 2 ^ h` 给出。
def seats := Fintype.card P.V * 2 ^ h

-- 读法：`Ready` 的结果类型为 `Prop`。
def Ready (g D T : ℕ) (L θ : ℝ) : Prop :=
  (∀ v, (P.adj v).card ≤ g) ∧
  (∑ v, P.charge v) ≤ L ∧ (∑ v, P.charge v ^ 2) ≤ L * T ∧
  ∀ v, P.charge v ≤ (D : ℝ) * T / 2 ∧ (P.charge v = 0 ∨ θ * T ≤ P.charge v)

end Board
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# 初始有界度叠层

以相应地址间的一条路径取代每根原始连线。逐层收缩这些路径的顶点会得到精确的张量幂，每个副本的所有外部比特都保持外露。

**英文原文**

The initial bounded-degree stack

Each original wire is replaced by a path between the appropriate
addresses. Contracting its vertices layer by layer gives an exact
power, with all external bits of every copy exposed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Packing Classical

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b) {t h n : ℕ}
    (bound : ∀ v, dim G v ≤ t) (c : Index t h ≃ Fin n)

-- 读法：在后续公式中，`paths` 是 `Spectral.Packet.Rule.path F (route (h := h) G bound) (2 * t + 1)` 的缩写。
private abbrev paths := Spectral.Packet.Rule.path F (route (h := h) G bound) (2 * t + 1)

omit [Field F] in
-- 读法：要证明的命题是 `(G.replicate c).Aligned (fun _ : Unit => owner G bound) (fun _ => id) (fun e => (route G bound 0 e, route G bound (2 * t + 1) e))`。
private theorem aligned :
    (G.replicate c).Aligned (fun _ : Unit => owner G bound) (fun _ => id)
      (fun e => (route G bound 0 e, route G bound (2 * t + 1) e)) := by
  rintro _ ⟨⟨x, y⟩, e⟩
  simp only [Diagram.source_replicate, Diagram.target_replicate, owner, route, id_eq,
    walk_start, walk_end, and_self]

-- 读法：在后续公式中，`diagram` 是 `(G.replicate c).replaced (paths G bound) (fun _ => owner G bound) (fun _ => id) ()` 的缩写。
abbrev diagram := (G.replicate c).replaced (paths G bound) (fun _ => owner G bound) (fun _ => id) ()

-- 读法：`(diagram G bound c).eval` 等于 `power G.eval n`。用函数外延性比较等号两侧在 `x y` 处的取值。
theorem eval : (diagram G bound c).eval = power G.eval n := by
  funext x y
  have he := (G.replicate c).eval_replaced (paths G bound)
    (fun _ => owner G bound) (fun _ => id) x y
  rw [Fintype.sum_unique, Diagram.eval_replicate] at he
  exact he

-- 读法：结论为 `let p := (diagram G bound c).source e let q := (diagram G bound c).target e q.2 = p.2 ∧ q.1 ∈ adjacent G p.1`。
theorem linked (e : (diagram G bound c).E) :
    let p := (diagram G bound c).source e
    let q := (diagram G bound c).target e
    q.2 = p.2 ∧ q.1 ∈ adjacent G p.1 := by
  obtain ⟨⟨⟨k, x, w⟩, he⟩, rfl⟩ := ((G.replicate c).cutEdges (paths G bound) _ _ (aligned G bound c) ()).surjective e
  exact ⟨rfl, walk_adj G bound x.1 w _ k.isLt⟩

-- 读法：`(diagram G bound c).arity v` 不超过 `4 * 2 ^ t`。
theorem arity (v : Site G t × Cell h) :
    (diagram G bound c).arity v ≤ 4 * 2 ^ t := by
  have hw := (G.replicate c).arity_replaced (paths G bound) _ _ (aligned G bound c) () v
  obtain ⟨hin, hout⟩ := exterior_capacity G bound c v
  have hs := edge_capacity G bound 0 (by decide) v
  have ht := edge_capacity G bound 1 le_rfl v
  have hy := Nat.add_le_add (Nat.add_le_add hin hout) (Nat.add_le_add hs ht)
  simp only [← Nat.card_eq_fintype_card, id_eq, add_zero] at hw hy
  refine hw.trans ?_
  refine hy.trans ?_
  omega

-- 读法：用字段 `V`、`diagram`、`place`、`one` 构造 `Board F (copies a n) (copies b n) h`。
def board : Board F (copies a n) (copies b n) h where
  V := Site G t
  diagram := diagram G bound c
  place := id
  one := Function.injective_id
  adj := adjacent G
  sym := adj_sym G
  edge := linked G bound c
  charge _ := 4 * (2 : ℝ) ^ t
  cover := by
    intro v
    exact_mod_cast arity G bound c v

-- 读法：要证明的命题是 `(board G bound c).Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * (Fintype.card (Site G t) * 2 ^ h : ℕ)) θ`。
theorem ready {D : ℕ} {θ : ℝ} (hD : 8 ≤ D) (hθ : θ ≤ (4 : ℝ)) :
    (board G bound c).Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * (Fintype.card (Site G t) * 2 ^ h : ℕ)) θ := by
  have hv : Fintype.card (diagram G bound c).V = Fintype.card (Site G t) * 2 ^ h := by
    change Fintype.card (Site G t × Cell h) = _
    rw [Fintype.card_prod, card_cell]
  have hD' : 8 ≤ (D : ℝ) := by exact_mod_cast hD
  refine ⟨adj_card G, ?_, ?_, ?_⟩
  · change (∑ _ : (diagram G bound c).V, 4 * (2 : ℝ) ^ t) ≤ _
    rw [Finset.sum_const, Finset.card_univ, hv, nsmul_eq_mul, mul_comm]
    gcongr; norm_num
  · change (∑ _ : (diagram G bound c).V, (4 * (2 : ℝ) ^ t) ^ 2) ≤ _
    rw [Finset.sum_const, Finset.card_univ, hv, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  · intro v
    change 4 * (2 : ℝ) ^ t ≤ _ ∧ (_ ∨ θ * _ ≤ 4 * (2 : ℝ) ^ t)
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact ⟨by rw [le_div_iff₀ (by norm_num)]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) t],
      Or.inr (mul_le_mul_of_nonneg_right hθ (by positivity))⟩

-- 读法：存在 `P : Board F (copies a (2 ^ t * 2 ^ h)) (copies b (2 ^ t * 2 ^ h)) h`，`P.diagram.eval = power G.eval (2 ^ t * 2 ^ h)` 与 `Fintype.card P.V ≤ 2 * G.cost * (t + 1) ∧ P.Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * P.seats) θ` 同时成立。
/-- 每个站点的宿主成本在其元数与堆叠地址长度之积上线性有界。其度数上界与该地址长度无关。

英文原文：The host cost per station is linear in its arity times the stack
address length. Its degree is bounded independently of that length.
-/
theorem initial (G : Diagram F a b) (t h D : ℕ) (θ : ℝ)
    (hu : ∀ v, G.arity v ≤ 2 ^ t) (hD : 8 ≤ D) (hθ : θ ≤ 4) :
    ∃ P : Board F (copies a (2 ^ t * 2 ^ h)) (copies b (2 ^ t * 2 ^ h)) h,
      P.diagram.eval = power G.eval (2 ^ t * 2 ^ h) ∧
      Fintype.card P.V ≤ 2 * G.cost * (t + 1) ∧
      P.Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * P.seats) θ := by
  have bound (v) : dim G v ≤ t := (Nat.clog_le_iff_le_pow (by decide)).mpr (hu v)
  let c : Index t h ≃ Fin (2 ^ t * 2 ^ h) := Fintype.equivOfCardEq (by simp [Index, Cell])
  exact ⟨board G bound c, eval G bound c, card G t, ready G bound c hD hθ⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end
