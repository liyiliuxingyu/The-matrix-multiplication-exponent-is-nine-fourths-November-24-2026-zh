-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode

/-!
# 每个宿主位置所用的公共二叉树

在核心位置，通往不同邻点的边共用一棵前缀树。在冻结位置，每个邻点各有一条从根出发的独立路径。因此，元数很大的冻结站点也无需让其全部比特通过同一个核心中继。所有可能的中继位置均由宿主图固定。

**英文原文**

A common binary tree for each host position

At a core position edges for different neighbors share a prefix tree.
At a frozen position each neighbor has a separate path from the root.
Thus a frozen station of large arity need not send all its bits through
one core relay. All potential relay positions are fixed by the host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset

-- 读法：在后续公式中，`Address` 是 `Fin d → Bool` 的缩写。
abbrev Address (d : ℕ) := Fin d → Bool
-- 读法：在后续公式中，`Relay` 是 `V × Fin (d + 1) × Address d` 的缩写。
abbrev Relay (V : Type) (d : ℕ) := V × Fin (d + 1) × Address d
-- 读法：在后续公式中，`Node` 是 `V ⊕ Relay V d` 的缩写。
abbrev Node (V : Type) (d : ℕ) := V ⊕ Relay V d

-- 读法：`Fintype.card (Node V d)` 等于 `(1 + (d + 1) * 2 ^ d) * Fintype.card V`。
theorem node_count (V : Type) [Fintype V] (d : ℕ) :
    Fintype.card (Node V d) = (1 + (d + 1) * 2 ^ d) * Fintype.card V := by
  simp [Node, Relay, Address]
  ring

-- 读法：结构的字段包括 `frozen`、`near`、`symm`、`code`、`inject`。
/-- 每个潜在邻点都分配有独立地址。

英文原文：Each potential neighbor gets its own address.
-/
structure Trie (V : Type) (d : ℕ) where
  frozen : V → Prop
  near : V → Finset V
  symm : ∀ u v, u ∈ near v → v ∈ near u
  code : V → V → Address d
  inject : ∀ v, Set.InjOn (code v) (near v)

namespace Trie
variable {V : Type} {d : ℕ}

-- 读法：用字段 `frozen`、`near`、`symm`、`code` 构造 `Trie V d`。
def make (frozen : V → Prop) (near : V → Finset V)
    (hs : ∀ u v, u ∈ near v → v ∈ near u) (hd : ∀ v, (near v).card ≤ 2 ^ d) : Trie V d where
  frozen := frozen
  near := near
  symm := hs
  code v u := if h : u ∈ near v then
    binaryCode ↥(near v) d (by simpa using hd v) ⟨u, h⟩ else fun _ => false
  inject v u hu w hw he := by
    change u ∈ near v at hu
    change w ∈ near v at hw
    simp only [dite_eq_left hu, dite_eq_left hw] at he
    exact congrArg Subtype.val ((binaryCode _ _ _).injective he)

variable (T : Trie V d)

-- 读法：`fixed` 的取值由 `Sum.elim T.frozen (fun _ => False)` 给出。
def fixed : Node V d → Prop := Sum.elim T.frozen (fun _ => False)

-- 读法：当 `h : ∃ w ∈ T.near v, T.code v w = c` 成立时取 `h.choose`，否则取 `v`。
def peer (v : V) (c : Address d) : V :=
  if h : ∃ w ∈ T.near v, T.code v w = c then h.choose else v

-- 读法：`T.peer v (T.code v w)` 等于 `w`。这里调用 `T.inject`。
theorem peer_code {v w : V} (hw : w ∈ T.near v) : T.peer v (T.code v w) = w := by
  have h : ∃ u ∈ T.near v, T.code v u = T.code v w := ⟨w, hw, rfl⟩
  rw [peer, dite_eq_left h]
  exact T.inject v h.choose_spec.1 hw h.choose_spec.2

-- 读法：当 `i.val < j` 成立时取 `c i`，否则取 `false`。
private def mask (c : Address d) (j : ℕ) : Address d :=
  fun i => if i.val < j then c i else false

-- 读法：当 `T.frozen v` 成立时取 `T.code v w`，否则取 `mask (T.code v w) j`。
def address (v w : V) (j : Fin (d + 1)) :=
  if T.frozen v then T.code v w else mask (T.code v w) j

-- 读法：`branch` 的取值由 `(v, j, T.address v w j)` 给出。
def branch (v w : V) (j : Fin (d + 1)) : Relay V d := (v, j, T.address v w j)

-- 读法：`T.address v w (Fin.last d)` 等于 `T.code v w`。
theorem address_last (v w : V) : T.address v w (Fin.last d) = T.code v w := by
  have h : mask (T.code v w) d = T.code v w := funext fun i => ite_eq_left i.isLt
  simp [address, h]

-- 读法：`up` 的取值由 `Fin.cases (.inl v) (fun i => .inr (v, i.castSucc, if T.frozen v then c else mask c i)) j` 给出。
private def up (v : V) (j : Fin (d + 1)) (c : Address d) : Node V d :=
  Fin.cases (.inl v) (fun i => .inr (v, i.castSucc, if T.frozen v then c else mask c i)) j

-- 读法：`down` 的结果类型为 `Node V d`。
private def down (v : V) (j : Fin (d + 1)) (c : Address d) (b : Bool) : Node V d :=
  Fin.lastCases (.inr (T.branch (T.peer v c) v (Fin.last d)))
    (fun i => .inr (v, i.succ, if T.frozen v then c else Function.update c i b)) j

-- 读法：`T.up v j.succ (T.address v w j.succ)` 等于 `.inr (T.branch v w j.castSucc)`。按 `T.frozen v` 成立与否分情况。
private theorem up_branch (v w : V) (j : Fin d) :
    T.up v j.succ (T.address v w j.succ) = .inr (T.branch v w j.castSucc) := by
  simp only [up, Fin.cases_succ, branch, address]
  by_cases h : T.frozen v
  · simp [h]
  · simp only [ite_eq_right h]
    congr 3
    funext i
    simp only [mask, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega

-- 读法：`T.down v j.castSucc (T.address v w j.castSucc) (T.code v w j)` 等于 `.inr (T.branch v w j.succ)`。按 `T.frozen v` 成立与否分情况。
private theorem down_branch (v w : V) (j : Fin d) :
    T.down v j.castSucc (T.address v w j.castSucc) (T.code v w j) = .inr (T.branch v w j.succ) := by
  simp only [down, Fin.lastCases_castSucc, branch, address]
  by_cases h : T.frozen v
  · simp [h]
  · simp only [ite_eq_right h]
    congr 3
    funext i
    by_cases he : i = j
    · subst i; simp [mask]
    · rw [Function.update_of_ne he]
      simp only [mask, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> first | rfl | omega

-- 读法：逐一匹配以下输入模式：`.inl v`、`.inr (v, j, c)`。
private def possible : Node V d → Finset (Node V d)
  | .inl v => if T.frozen v then univ.image (fun c : Address d => .inr (v, 0, c))
    else {.inr (v, 0, fun _ => false)}
  | .inr (v, j, c) => {T.up v j c, T.down v j c false, T.down v j c true}

-- 读法：`adj` 的取值由 `(T.possible x).filter (fun y => x ∈ T.possible y)` 给出。
def adj (x : Node V d) := (T.possible x).filter (fun y => x ∈ T.possible y)

-- 读法：`core` 的取值由 `(T.adj x).filter (fun y => ¬ T.fixed x ∧ ¬ T.fixed y)` 给出。
def core (x : Node V d) := (T.adj x).filter (fun y => ¬ T.fixed x ∧ ¬ T.fixed y)

-- 读法：由 `y ∈ T.adj x` 推出 `x ∈ T.adj y`。
theorem adj_symm {x y : Node V d} : y ∈ T.adj x → x ∈ T.adj y := by
  simp [adj, and_comm]

-- 读法：`x` 属于 `T.core y`。这里调用 `mem_filter.mpr`。
theorem core_symm {x y : Node V d} (h : y ∈ T.core x) : x ∈ T.core y := by
  obtain ⟨h, hx, hy⟩ := mem_filter.mp h
  exact mem_filter.mpr ⟨T.adj_symm h, hy, hx⟩

-- 读法：要证明的命题是 `¬ (T.fixed v ∧ T.fixed w)`。对 `v` 分类讨论。
theorem separate {v w : Node V d} (h : w ∈ T.adj v) : ¬ (T.fixed v ∧ T.fixed w) := by
  rintro ⟨hv, hw⟩
  cases v with
  | inr _ => exact hv
  | inl v =>
    cases w with
    | inr _ => exact hw
    | inl w =>
      change T.frozen v at hv
      have := (mem_filter.mp h).1
      simp [possible, hv] at this

-- 读法：`(T.adj (.inr v)).card` 不超过 `3`。这里调用 `card_insert_le`。
private theorem relay_degree (v : Relay V d) : (T.adj (.inr v)).card ≤ 3 := by
  obtain ⟨u, j, c⟩ := v
  refine (card_filter_le _ _).trans ?_
  unfold possible
  have hh := card_insert_le (T.down u j c false) {T.down u j c true}
  simp only [card_singleton] at hh
  exact (card_insert_le _ _).trans (by omega)

-- 读法：`(T.adj v).card` 不超过 `max 3 (2 ^ d)`。对 `v` 分类讨论。
theorem degree (v : Node V d) : (T.adj v).card ≤ max 3 (2 ^ d) := by
  cases v with
  | inl v =>
    refine (card_filter_le _ _).trans ?_
    simp only [possible]
    split_ifs
    · apply le_trans card_image_le
      simp [Address]
    · simp
  | inr v => exact (T.relay_degree v).trans (le_max_left _ _)

-- 读法：`(T.core v).card` 不超过 `3`。对 `v` 分类讨论。
theorem core_degree (v : Node V d) : (T.core v).card ≤ 3 := by
  cases v with
  | inl v =>
    by_cases h : T.frozen v
    · simp [core, fixed, h]
    · refine (card_filter_le _ _).trans ((card_filter_le _ _).trans ?_)
      simp [possible, h]
  | inr v => exact (card_filter_le _ _).trans (T.relay_degree v)

-- 读法：`T.up v j c` 属于 `T.possible (.inr (v, j, c))`。使用 `mem_insert_self` 给出的结论。
private theorem mem_up (v : V) (j : Fin (d + 1)) (c : Address d) :
    T.up v j c ∈ T.possible (.inr (v, j, c)) := mem_insert_self _ _

-- 读法：`T.down v j c b` 属于 `T.possible (.inr (v, j, c))`。
private theorem mem_down (v : V) (j : Fin (d + 1)) (c : Address d) (b : Bool) :
    T.down v j c b ∈ T.possible (.inr (v, j, c)) := by cases b <;> simp [possible]

-- 读法：`.inr (T.branch v w 0)` 属于 `T.adj (.inl v)`。这里调用 `mem_filter.mpr`。
theorem root (v w : V) : .inr (T.branch v w 0) ∈ T.adj (.inl v) := by
  apply mem_filter.mpr
  refine ⟨?_, T.mem_up v 0 (T.address v w 0)⟩
  by_cases h : T.frozen v
  · simp [possible, h, branch]
  · have he : mask (T.code v w) 0 = fun _ => false := by funext i; simp [mask]
    simp [possible, h, branch, address, he]

-- 读法：`.inr (T.branch v w j.succ)` 属于 `T.adj (.inr (T.branch v w j.castSucc))`。这里调用 `mem_filter.mpr`。
theorem edge (v w : V) (j : Fin d) :
    .inr (T.branch v w j.succ) ∈ T.adj (.inr (T.branch v w j.castSucc)) := by
  apply mem_filter.mpr
  constructor
  · rw [← T.down_branch]
    exact T.mem_down _ _ _ _
  · rw [← T.up_branch]
    exact T.mem_up _ _ _

-- 读法：`.inr (T.branch w v (Fin.last d))` 属于 `T.possible (.inr (T.branch v w (Fin.last d)))`。
private theorem end_mem {v w : V} (h : w ∈ T.near v) :
    .inr (T.branch w v (Fin.last d)) ∈ T.possible (.inr (T.branch v w (Fin.last d))) := by
  have he := T.mem_down v (Fin.last d) (T.address v w (Fin.last d)) false
  simpa only [down, Fin.lastCases_last, branch, address_last, T.peer_code h] using he

-- 读法：`.inr (T.branch w v (Fin.last d))` 属于 `T.adj (.inr (T.branch v w (Fin.last d)))`。使用 `mem_filter.mpr` 给出的结论。
theorem join {v w : V} (h : w ∈ T.near v) :
    .inr (T.branch w v (Fin.last d)) ∈ T.adj (.inr (T.branch v w (Fin.last d))) :=
  mem_filter.mpr ⟨T.end_mem h, T.end_mem (T.symm w v h)⟩

end Trie
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
