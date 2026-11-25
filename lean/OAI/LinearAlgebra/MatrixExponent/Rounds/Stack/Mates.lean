-- 本文件所属证明环节：将元数集中、装包、重置和固定图上的安装编成可重复施行的一轮，逐轮跟踪尺度、站点表和连线预算，得到元数缩减。
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Rounds.Bins
import OAI.LinearAlgebra.MatrixExponent.Diagram.Canonical
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames

section
/-!
# 局部替换由相同表组成的叠层

**英文原文**

Local replacement of a stack of identical tables
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack

-- 读法：结构的字段包括 `diagram`、`eval`、`name`、`external`、`adj`。
/-- 每个原始外部端口的所有副本都接到同一指定顶点。连接器件时，该点还有余量再接一条边。

英文原文：All copies of each original exterior port meet one named vertex.
There is room for one more adjacency when joining devices.
-/
structure Device {F : Type} [Field F] (T : Table F) (t : ℕ) where
  diagram : Diagram F (copies T.1 (2 ^ t)) (copies T.2.1 (2 ^ t))
  eval : diagram.eval = (BatchDescent.Stack.tensor T (2 ^ t)).2.2
  name : Transcript.Ports T ↪ diagram.V
  external : ∀ p : Transcript.Ports (BatchDescent.Stack.tensor T (2 ^ t)),
    Packing.portEnd diagram p = name ((BatchDescent.Stack.pin T (2 ^ t)) p).2
  adj : diagram.V → Finset diagram.V
  sym : ∀ v w, w ∈ adj v → v ∈ adj w
  degree : ∀ v, (adj v).card ≤ 4
  linked : ∀ e, diagram.target e ∈ adj (diagram.source e)
  loopless : ∀ e, diagram.source e ≠ diagram.target e
  arity : ∀ v, diagram.arity v ≤ 4 * 2 ^ t
  size : Fintype.card diagram.V ≤ 4 * (1 + wd T.1 + wd T.2.1) * (t + 1)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# 连接复制网络的各站点装置

局部图至多引入四个邻点。由端口名称各不相同，原网络中至多再有一个邻点。

**英文原文**

Joining the station devices of a replicated network

The local graph contributes at most four neighbors. Distinct port
names leave at most one further neighbor on the original network.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Packing Finset
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h t n : ℕ}
  (G : Diagram F a b) (f : ∀ v, Device (G.table v) t) (c : Cell h × Fin (2 ^ t) ≃ Fin n)

-- 读法：在后续公式中，`built` 是 `(BatchDescent.Stack.gathered G c).plug (fun v => (f v.2).diagram)` 的缩写。
abbrev built := (BatchDescent.Stack.gathered G c).plug (fun v => (f v.2).diagram)

-- 读法：在后续公式中，`Location` 是 `Σ v, (f v).diagram.V` 的缩写。
abbrev Location := Σ v, (f v).diagram.V

namespace Device

-- 读法：`endpoint` 的取值由 `G.portEquiv.symm.toEmbedding.trans ((Function.Embedding.refl G.V).sigmaMap fun v => (f v).name)` 给出。
def endpoint : G.End ↪ Location G f :=
  G.portEquiv.symm.toEmbedding.trans ((Function.Embedding.refl G.V).sigmaMap fun v => (f v).name)

-- 读法：`(built G f c).eval` 等于 `power G.eval n`。
theorem exact_value : (built G f c).eval = power G.eval n :=
  ((BatchDescent.Stack.gathered G c).eval_plug _ (fun v => (f v.2).eval)).trans
    ((BatchDescent.Stack.eval_gathered G c).trans (G.eval_replicate c))

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(built G f c).V ≃ Location G f × Cell h`。
def place : (built G f c).V ≃ Location G f × Cell h where
  toFun z := (⟨z.1.2, z.2⟩, z.1.1)
  invFun z := ⟨(z.2, z.1.1), z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- 读法：当 `h : ∃ e, endpoint G f e = z` 成立时取 `endpoint G f (other G h.choose)`，否则取 `z`。
def partner (z : Location G f) :=
  if h : ∃ e, endpoint G f e = z then endpoint G f (other G h.choose) else z

-- 读法：`partner G f (endpoint G f e)` 等于 `endpoint G f (other G e)`。
theorem partner_end (e : G.End) :
    partner G f (endpoint G f e) = endpoint G f (other G e) := by
  have he : ∃ d, endpoint G f d = endpoint G f e := ⟨e, rfl⟩
  simp only [partner, dite_eq_left he, (endpoint G f).injective he.choose_spec]

-- 读法：要证明的命题是 `Function.Involutive (partner G f)`。按 `∃ e, endpoint G f e = z` 成立与否分情况。
theorem partner_involution : Function.Involutive (partner G f) := by
  intro z
  by_cases he : ∃ e, endpoint G f e = z
  · obtain ⟨e, rfl⟩ := he
    rw [partner_end, partner_end]
    rcases e with (i|e)|(j|e) <;> rfl
  · have eq : partner G f z = z := dite_eq_right he
    rw [eq, eq]

-- 读法：`neighbors` 的取值由 `insert (partner G f z) (((f z.1).adj z.2).image (Sigma.mk z.1))` 给出。
def neighbors (z : Location G f) : Finset (Location G f) :=
  insert (partner G f z) (((f z.1).adj z.2).image (Sigma.mk z.1))

-- 读法：`v` 属于 `neighbors G f w`。这里调用 `mem_insert.mpr`。
theorem sym_neighbors (v w : Location G f) (h : w ∈ neighbors G f v) :
    v ∈ neighbors G f w := by
  rcases mem_insert.mp h with rfl | h
  · exact mem_insert.mpr (.inl (partner_involution G f v).symm)
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    exact mem_insert_of_mem (mem_image_of_mem (Sigma.mk v.1) ((f v.1).sym _ _ hx))

-- 读法：`(neighbors G f v).card` 不超过 `5`。通过传递性衔接 `card_insert_le` 与 `Nat.add_le_add_right`。
theorem neighbors_bound (v : Location G f) : (neighbors G f v).card ≤ 5 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right (card_image_le.trans ((f v.1).degree _)) 1)

-- 读法：`place G f c ((built G f c).source (.inl ((i, j), e)))` 等于 `(endpoint G f (.inl (.inr e)), i)`。
theorem outer_source (i : Cell h) (j : Fin (2 ^ t)) (e : G.E) :
    place G f c ((built G f c).source (.inl ((i, j), e))) = (endpoint G f (.inl (.inr e)), i) := by
  let p := G.src.symm (.inr e)
  let k := (Diagonal.port (G.table p.1).1 (2 ^ t)).symm (j, p.2)
  change ((⟨p.1, portEnd (f p.1).diagram (.inl k)⟩ : Location G f), i) =
    (⟨p.1, (f p.1).name (.inl p.2)⟩, i)
  rw [(f p.1).external]
  simp [BatchDescent.Stack.pin, k]

-- 读法：`place G f c ((built G f c).target (.inl ((i, j), e)))` 等于 `(endpoint G f (.inr (.inr e)), i)`。
theorem outer_target (i : Cell h) (j : Fin (2 ^ t)) (e : G.E) :
    place G f c ((built G f c).target (.inl ((i, j), e))) = (endpoint G f (.inr (.inr e)), i) := by
  let p := G.dst.symm (.inr e)
  let k := (Diagonal.port (G.table p.1).2.1 (2 ^ t)).symm (j, p.2)
  change ((⟨p.1, portEnd (f p.1).diagram (.inr k)⟩ : Location G f), i) =
    (⟨p.1, (f p.1).name (.inr p.2)⟩, i)
  rw [(f p.1).external]
  simp [BatchDescent.Stack.pin, k]

-- 读法：结论为 `let p := place G f c ((built G f c).source e) let q := place G f c ((built G f c).target e) q.2 = p.2 ∧ q.1 ∈ neighbors G f p.1`。
theorem wires (e : (built G f c).E) :
    let p := place G f c ((built G f c).source e)
    let q := place G f c ((built G f c).target e)
    q.2 = p.2 ∧ q.1 ∈ neighbors G f p.1 := by
  rcases e with ⟨⟨i, j⟩, e⟩ | ⟨⟨i, v⟩, e⟩
  · rw [outer_source, outer_target]
    exact ⟨rfl, mem_insert.mpr (.inl (partner_end G f (.inl (.inr e))).symm)⟩
  · exact ⟨rfl, mem_insert_of_mem (mem_image_of_mem (Sigma.mk v) ((f v).linked e))⟩

-- 读法：`(built G f c).source e` 不等于 `(built G f c).target e`。
theorem built_loopless (e : (built G f c).E) :
    (built G f c).source e ≠ (built G f c).target e := by
  intro he
  rcases e with ⟨⟨i, j⟩, e⟩ | ⟨⟨i, v⟩, e⟩
  · have eq := congrArg (place G f c) he
    rw [outer_source, outer_target] at eq
    cases (endpoint G f).injective (congrArg Prod.fst eq)
  · exact (f v).loopless e (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

-- 读法：`Fintype.card (Location G f)` 不超过 `4 * G.cost * (t + 1)`。
theorem location_bound : Fintype.card (Location G f) ≤ 4 * G.cost * (t + 1) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ v, 4 * (1 + G.arity v) * (t + 1) :=
      sum_le_sum fun v _ => by simpa [Diagram.arity, add_assoc] using (f v).size
    _ = _ := by rw [Diagram.cost, mul_sum, sum_mul]

-- 读法：用字段 `V`、`diagram`、`place`、`one` 构造 `Board F (copies a n) (copies b n) h`。
abbrev board : Board F (copies a n) (copies b n) h where
  V := Location G f
  diagram := built G f c
  place := place G f c
  one := (place G f c).injective
  adj := neighbors G f
  sym := sym_neighbors G f
  edge := wires G f c
  charge _ := 4 * (2 : ℝ) ^ t
  cover z := by
    change ((f z.1.2).diagram.arity z.2 : ℝ) ≤ _
    exact_mod_cast (f z.1.2).arity z.2

-- 读法：`(board G f c).seats` 不超过 `4 * G.cost * (t + 1) * 2 ^ h`。使用 `Nat.mul_le_mul_right` 给出的结论。
theorem seats_bound : (board G f c).seats ≤ 4 * G.cost * (t + 1) * 2 ^ h :=
  Nat.mul_le_mul_right _ (location_bound G f)

-- 读法：要证明的命题是 `(board G f c).Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * (board G f c).seats) θ`。
theorem ready {D : ℕ} {θ : ℝ} (hD : 8 ≤ D) (hθ : θ ≤ 4) :
    (board G f c).Ready 5 D (2 ^ t) (16 * (2 : ℝ) ^ t * (board G f c).seats) θ := by
  have size : Fintype.card (built G f c).V = (board G f c).seats := by
    rw [Fintype.card_congr (place G f c), Fintype.card_prod, card_cell]
    rfl
  refine ⟨neighbors_bound G f, ?_, ?_, ?_⟩
  · change (∑ _ : (built G f c).V, 4 * (2 : ℝ) ^ t) ≤ _
    rw [sum_const, card_univ, size, nsmul_eq_mul, mul_comm]
    gcongr; norm_num
  · change (∑ _ : (built G f c).V, (4 * (2 : ℝ) ^ t) ^ 2) ≤ _
    rw [sum_const, card_univ, size, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (by ring)
  · intro v
    change 4 * (2 : ℝ) ^ t ≤ _ ∧ (_ ∨ θ * _ ≤ 4 * (2 : ℝ) ^ t)
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    refine ⟨?_, .inr (mul_le_mul_of_nonneg_right hθ (by positivity))⟩
    -- 推导：记下中间结论 `hD'`：`(8 : ℝ) ≤ D`。
    have hD' : (8 : ℝ) ≤ D := by exact_mod_cast hD
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) t]

end Device
end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# 转置同一张表的各个副本

将每个副本存入第零层。把它的各个比特路由到末层；表的每个端口在那里都有一个由所有副本共用的顶点。对每种外部输入，相等性约束均有唯一解。

**英文原文**

Transposing the copies of a single table

Store every copy at layer zero. Route its bits to the final layer,
where each port of the table has one vertex shared by all copies.
The equality constraints have one solution for every exterior input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Finset Packing Transcript BatchDescent.Stack
open scoped Classical

variable {F : Type} [Field F] {T : Table F} {t : ℕ}

namespace Butterfly

-- 读法：在后续公式中，`dim` 是 `Nat.clog 2 (wd T.1 + wd T.2.1)` 的缩写。
private abbrev dim (T : Table F) (_ : Unit) := Nat.clog 2 (wd T.1 + wd T.2.1)
-- 读法：在后续公式中，`Site` 是 `Node (t := t) (dim T)` 的缩写。
private abbrev Site (T : Table F) (t : ℕ) := Node (t := t) (dim T)
-- 读法：在后续公式中，`Pin` 是 `Ports (tensor T (2 ^ t))` 的缩写。
private abbrev Pin (T : Table F) (t : ℕ) := Ports (tensor T (2 ^ t))
-- 读法：在后续公式中，`Link` 是 `Fin t × Pin T t` 的缩写。
private abbrev Link (T : Table F) (t : ℕ) := Fin t × Pin T t

-- 读法：`idx` 的取值由 `Fintype.equivOfCardEq (by simp [Cell])` 给出。
private def idx (t : ℕ) : Fin (2 ^ t) ≃ Cell t := Fintype.equivOfCardEq (by simp [Cell])

-- 读法：`addr` 的结果类型为 `Ports T ↪ Σ j, Cell (dim T j)`。
private def addr (T : Table F) : Ports T ↪ Σ j, Cell (dim T j) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simp only [Ports, Fintype.card_sum, card_slots, Fintype.card_sigma, card_cell, dim, sum_const,
      card_univ, Fintype.card_unit, one_smul]
    exact Nat.le_pow_clog (by decide) _))

-- 读法：`terminal` 的取值由 `⟨fun p => (addr T p, Fin.last t), fun _ _ h => (addr T).injective (congrArg Prod.fst h)⟩` 给出。
private def terminal (T : Table F) (t : ℕ) : Ports T ↪ Site T t :=
  ⟨fun p => (addr T p, Fin.last t), fun _ _ h => (addr T).injective (congrArg Prod.fst h)⟩

variable (hd : ∀ j, dim T j ≤ t)

-- 读法：`loc` 的取值由 `Node.atLayer hd k (idx t (pin T _ p).1) (addr T (pin T _ p).2)` 给出。
private def loc (k : Fin (t + 1)) (p : Pin T t) : Site T t :=
  Node.atLayer hd k (idx t (pin T _ p).1) (addr T (pin T _ p).2)

-- 读法：`base` 的取值由 `Node.start hd () (idx t i)` 给出。
private def base (i : Fin (2 ^ t)) : Site T t := Node.start hd () (idx t i)

-- 读法：`loc hd 0 ((pin T _).symm (i, p))` 等于 `base hd i`。
private theorem first (i : Fin (2 ^ t)) (p : Ports T) :
    loc hd 0 ((pin T _).symm (i, p)) = base hd i := by
  simp only [loc, Equiv.apply_symm_apply, Node.layer_zero, base]

-- 读法：`loc hd (Fin.last t) p` 等于 `terminal T t ((pin T _ p).2)`。
private theorem last (p : Pin T t) : loc hd (Fin.last t) p = terminal T t ((pin T _ p).2) := by
  rw [loc, Node.layer_last]; rfl

-- 读法：`code` 的取值由 `Node.residue k.val (addr T (pin T _ p).2).1 (idx t (pin T _ p).1) (addr T (pin T _ p).2).2` 给出。
private def code (k : Fin (t + 1)) (p : Pin T t) : Cell t :=
  Node.residue k.val (addr T (pin T _ p).2).1 (idx t (pin T _ p).1) (addr T (pin T _ p).2).2

-- 读法：`i = j` 与 `p = q` 同时成立。
private theorem unique {i j : Fin (t + 1)} {p q : Pin T t}
    (hl : loc hd i p = loc hd j q) (hc : code i p = code j q) : i = j ∧ p = q := by
  obtain ⟨hk, hx, hp⟩ := Node.layer_inj hd hl hc
  exact ⟨hk, (pin T _).injective (Prod.ext ((idx t).injective hx) ((addr T).injective hp))⟩

-- 读法：要证明的命题是 `Fintype.card {q : X ⊕ Link T t // Sum.elim (fun x => loc hd (Fin.last t) (f x)) (fun e => loc hd (k e.1) e.2) q = v} ≤ 2 * 2 ^ t`。这里调用 `Subtype.ext`。
/-- 每一层中，单个站址上的比特数至多等于副本数。具有同一层地址的比特通过剩余地址来区分。

英文原文：At each layer there are at most as many bits at one site as copies.
Residual addresses distinguish bits with the same layer address.
-/
private theorem capacity {X : Type} [Fintype X]
    (f : X → Pin T t) (hf : Function.Injective f)
    (k : Fin t → Fin (t + 1)) (hk : Function.Injective k) (v : Site T t) :
    Fintype.card {q : X ⊕ Link T t // Sum.elim (fun x => loc hd (Fin.last t) (f x))
      (fun e => loc hd (k e.1) e.2) q = v} ≤ 2 * 2 ^ t := by
  let key : X ⊕ Link T t → Cell t ⊕ Cell t := Sum.elim
    (fun x => .inl (code (Fin.last t) (f x))) (fun e => .inr (code (k e.1) e.2))
  refine le_trans ?_ (show Fintype.card (Cell t ⊕ Cell t) ≤ 2 * 2 ^ t by simp [two_mul, Cell])
  refine Fintype.card_le_of_injective (fun q => key q.val) ?_
  rintro ⟨x | e, hx⟩ ⟨y | j, hy⟩ h
  · exact Subtype.ext (congrArg Sum.inl (hf (unique hd (hx.trans hy.symm) (Sum.inl.inj h)).2))
  · cases h
  · cases h
  · obtain ⟨ha, hp⟩ := unique hd (hx.trans hy.symm) (Sum.inr.inj h)
    exact Subtype.ext (congrArg Sum.inr (Prod.ext (hk ha) hp))

-- 读法：`src` 的取值由 `Sum.elim (fun i => loc hd (Fin.last t) (.inl i)) (fun e => loc hd e.1.castSucc e.2)` 给出。
private def src : slots (copies T.1 (2 ^ t)) ⊕ Link T t → Site T t :=
  Sum.elim (fun i => loc hd (Fin.last t) (.inl i)) (fun e => loc hd e.1.castSucc e.2)

-- 读法：`dst` 的取值由 `Sum.elim (fun i => loc hd (Fin.last t) (.inr i)) (fun e => loc hd e.1.succ e.2)` 给出。
private def dst : slots (copies T.2.1 (2 ^ t)) ⊕ Link T t → Site T t :=
  Sum.elim (fun i => loc hd (Fin.last t) (.inr i)) (fun e => loc hd e.1.succ e.2)

-- 读法：在后续公式中，`X` 是 `slots (copies T.1 (2 ^ t)) ⊕ Link T t → Bool` 的缩写。
private abbrev X (T : Table F) (t : ℕ) := slots (copies T.1 (2 ^ t)) ⊕ Link T t → Bool
-- 读法：在后续公式中，`Y` 是 `slots (copies T.2.1 (2 ^ t)) ⊕ Link T t → Bool` 的缩写。
private abbrev Y (T : Table F) (t : ℕ) := slots (copies T.2.1 (2 ^ t)) ⊕ Link T t → Bool

-- 读法：`read` 的取值由 `Fin.lastCases (Sum.elim (x ∘ Sum.inl) (y ∘ Sum.inl) p) (fun k => x (.inr (k, p))) k` 给出。
private def read (x : X T t) (y : Y T t) (k : Fin (t + 1)) (p : Pin T t) : Bool :=
  Fin.lastCases (Sum.elim (x ∘ Sum.inl) (y ∘ Sum.inl) p) (fun k => x (.inr (k, p))) k

-- 读法：`weight` 的结果类型为 `F`。
private def weight (v : Site T t) (x : X T t) (y : Y T t) : F :=
  if ∀ e : Link T t, dst hd (.inr e) = v → y (.inr e) = read x y e.1.succ e.2 then
    ∏ i ∈ univ.filter (fun i => base hd i = v),
      sample T (fun p => read x y 0 ((pin T _).symm (i, p)))
  else 0

-- 读法：要证明的命题是 `Diagram.Local (src hd) (dst hd) (weight hd)`。对 `k` 作归纳，采用 `Fin.lastCases` 的归纳原则。
private theorem local_weight : Diagram.Local (src hd) (dst hd) (weight hd) := by
  intro v x y x' y' hx hy
  have hr (k : Fin (t + 1)) (p : Pin T t) (h : loc hd k p = v) :
      read x y k p = read x' y' k p := by
    induction k using Fin.lastCases with
    | last =>
      simp only [read, Fin.lastCases_last]
      cases p with
      | inl i => exact hx (.inl i) h
      | inr i => exact hy (.inl i) h
    | cast k =>
      simp only [read, Fin.lastCases_castSucc]
      exact hx (.inr (k, p)) h
  have hc : (∀ e : Link T t, dst hd (.inr e) = v → y (.inr e) = read x y e.1.succ e.2) ↔
      (∀ e : Link T t, dst hd (.inr e) = v → y' (.inr e) = read x' y' e.1.succ e.2) := by
    refine forall_congr' fun e => imp_congr_right fun he => ?_
    rw [hy _ he, hr _ _ he]
  simp only [weight, hc]
  split
  · refine prod_congr rfl fun i hi => congrArg (sample T) (funext fun p => ?_)
    exact hr _ _ ((first hd i p).trans (mem_filter.mp hi).2)
  · rfl

-- 读法：在后续公式中，`network` 是 `Diagram.ofLocal (src hd) (dst hd) (weight hd)` 的缩写。
private abbrev network := Diagram.ofLocal (src hd) (dst hd) (weight hd)

-- 读法：`(network hd).eval` 等于 `(tensor T (2 ^ t)).2.2`。用函数外延性比较等号两侧在 `x y` 处的取值。
private theorem evaluate : (network hd).eval = (tensor T (2 ^ t)).2.2 := by
  funext x y
  let f : Pin T t → Bool := Sum.elim (bits (copies T.1 (2 ^ t)) x) (bits (copies T.2.1 (2 ^ t)) y)
  let z₀ : Link T t → Bool := fun e => f e.2
  let val (z : Link T t → Bool) := read (Sum.elim (bits (copies T.1 (2 ^ t)) x) z) (Sum.elim (bits (copies T.2.1 (2 ^ t)) y) z)
  have end_val (z) (p) : val z (Fin.last t) p = f p := by
    simp only [val, read, Fin.lastCases_last]
    cases p <;> rfl
  have before (z) (i : Fin t) (p) : val z i.castSucc p = z (i, p) := by
    simp [val, read]
  have good (k : Fin (t + 1)) (p) : val z₀ k p = f p := by
    induction k using Fin.lastCases with
    | last => exact end_val _ _
    | cast k => exact before z₀ k p
  have forced (z : Link T t → Bool) (h : ∀ e, z e = val z e.1.succ e.2) : z = z₀ := by
    funext ⟨k, p⟩
    have eq (i : Fin (t + 1)) : val z i p = f p := by
      induction i using Fin.reverseInduction with
      | last => exact end_val _ _
      | cast i ih => exact (before z i p).trans ((h (i, p)).trans ih)
    exact (h (k, p)).trans (eq k.succ)
  have hw (v) (z : Link T t → Bool) : (network hd).vertex x y z v =
      if ∀ e, dst hd (.inr e) = v → z e = val z e.1.succ e.2 then
        ∏ i ∈ univ.filter (fun i => base hd i = v),
          sample T (fun p => val z 0 ((pin T _).symm (i, p))) else 0 :=
    Diagram.vertex_ofLocal _ _ _ (local_weight hd) x y z v
  unfold Diagram.eval
  rw [sum_eq_single z₀]
  · have ht (v) : (network hd).vertex x y z₀ v =
        ∏ i ∈ univ.filter (fun i => base hd i = v),
          sample T (fun p => f ((pin T _).symm (i, p))) := by
      rw [hw, ite_eq_left (fun e _ => (good _ _).symm)]
      simp only [good]
    simp_rw [ht]
    rw [prod_fiberwise, ←sample_tensor]
    simp only [sample, f, Function.comp_def, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]
  · intro z _ hne
    -- 推导：记下中间结论 `h`：`¬∀ e, z e = val z e.1.succ e.2`。
    have h : ¬∀ e, z e = val z e.1.succ e.2 := fun h => hne (forced z h)
    push Not at h
    obtain ⟨e, he⟩ := h
    refine prod_eq_zero (mem_univ (dst hd (.inr e))) ?_
    rw [hw, ite_eq_right (fun h => he (h e rfl))]
  · simp

-- 读法：`(network hd).arity v` 不超过 `4 * 2 ^ t`。
private theorem arity (v : Site T t) : (network hd).arity v ≤ 4 * 2 ^ t := by
  rw [Diagram.arity_ofLocal]
  have h₁ := capacity hd Sum.inl Sum.inl_injective Fin.castSucc (Fin.castSucc_injective _) v
  have h₂ := capacity hd Sum.inr Sum.inr_injective Fin.succ (Fin.succ_injective _) v
  convert! Nat.add_le_add h₁ h₂ using 1 <;> first | omega | congr! 3

omit [Field F] in
-- 读法：`Fintype.card (Site T t)` 不超过 `4 * (1 + wd T.1 + wd T.2.1) * (t + 1)`。这里调用 `Nat.mul_le_mul_right`。
private theorem size (T : Table F) (t : ℕ) :
    Fintype.card (Site T t) ≤ 4 * (1 + wd T.1 + wd T.2.1) * (t + 1) := by
  simp only [Site, Node, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, card_cell, dim,
    sum_const, card_univ, Fintype.card_unit, one_smul]
  apply Nat.mul_le_mul_right
  by_cases h : wd T.1 + wd T.2.1 = 0
  · simp only [h, Nat.clog_zero_right, pow_zero]; omega
  · exact (Transcript.pow_clog_le_twice (Nat.pos_of_ne_zero h)).trans (by omega)

-- 读法：用字段 `diagram`、`eval`、`name`、`external` 构造 `Device T t`。
private def make : Device T t where
  diagram := network hd
  eval := evaluate hd
  name := terminal T t
  external p := by cases p <;> exact last hd _
  adj v := (Node.links v).filter (fun w => v ∈ Node.links w)
  sym _ _ hw := mem_filter.mpr ⟨(mem_filter.mp hw).2, (mem_filter.mp hw).1⟩
  degree v := (card_filter_le ..).trans (Node.links_card v)
  linked e := mem_filter.mpr
    ⟨Node.layer_link hd _ _ (.inl rfl) _ _, Node.layer_link hd _ _ (.inr rfl) _ _⟩
  loopless e he := by
    have := congrArg (fun v : Site T t => v.2.val) he
    change e.1.val = e.1.val + 1 at this
    omega
  arity := arity hd
  size := size T t

end Butterfly

-- 读法：`(Device T t)` 有元素。
/-- 替换一张堆叠表，使每个端口上的副本次序保持不变。

英文原文：Replace one stacked table, preserving the copy order on every port.
-/
theorem device (T : Table F) (t : ℕ) (_ht : 0 < t) (bound : wd T.1 + wd T.2.1 ≤ 2 ^ t) :
    Nonempty (Device T t) :=
  ⟨Butterfly.make (fun _ => Nat.clog_le_of_le_pow bound)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# 一个局部蝶形网络中的跨度

固定方向的平行线形成一个跨度。器件终端的外部比特形成另一个跨度，按堆叠索引排列。本文件的全部编号仅使用一张输入表所对应的器件。

**英文原文**

Spans inside one local butterfly

Parallel wires in a fixed direction form one span. The exterior bits
at a device terminal form another span, ordered by stack index. All
numbering in this file uses only the device of a single input table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Device
open Assembly Coloring Transcript Packing Finset
open scoped Classical

variable {F : Type} [Field F] {T : Table F} {t : ℕ} (D : Device T t)
local notation "G" => D.diagram

-- 读法：`pair` 的取值由 `((G).source e, (G).target e)` 给出。
def pair (e : (G).E) := ((G).source e, (G).target e)
-- 读法：在后续公式中，`Link` 是 `Set.range D.pair` 的缩写。
abbrev Link := Set.range D.pair
-- 读法：`link` 的取值由 `⟨D.pair e, e, rfl⟩` 给出。
def link (e : (G).E) : D.Link := ⟨D.pair e, e, rfl⟩

-- 读法：在后续公式中，`Line` 是 `(D.Link × Bool) ⊕ Ports T` 的缩写。
abbrev Line := (D.Link × Bool) ⊕ Ports T

-- 读法：逐一匹配以下输入模式：`.inl (e, b)`、`.inr p`。
def site : D.Line → (G).V
  | .inl (e, b) => cond b e.val.2 e.val.1
  | .inr p => D.name p

-- 读法：逐一匹配以下输入模式：`.inl (_, b)`、`.inr p`。
def side : D.Line → Bool
  | .inl (_, b) => b
  | .inr p => p.isRight

-- 读法：逐一匹配以下输入模式：`.inl (e, _)`、`.inr _`。
def width : D.Line → ℕ
  | .inl (e, _) => Fintype.card {i // D.link i = e}
  | .inr _ => 2 ^ t

-- 读法：`0` 严格小于 `D.width l`。这里调用 `Fintype.card_pos_iff.mpr`。
theorem width_pos (l : D.Line) : 0 < D.width l := by
  rcases l with ⟨e, b⟩|p
  · obtain ⟨i, hi⟩ := e.property
    exact Fintype.card_pos_iff.mpr ⟨⟨i, Subtype.ext hi⟩⟩
  · exact Nat.two_pow_pos _

-- 读法：`bundle` 的取值由 `(Equiv.sigmaFiberEquiv D.link).symm.trans (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)` 给出。
def bundle : (G).E ≃ Σ e : D.Link, Fin (Fintype.card {i // D.link i = e}) :=
  (Equiv.sigmaFiberEquiv D.link).symm.trans (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)

-- 读法：在后续公式中，`Bit` 是 `Σ l, Fin (D.width l)` 的缩写。
abbrev Bit := Σ l, Fin (D.width l)

-- 读法：`inside` 的取值由 `cond b (.inr (.inr e)) (.inl (.inr e))` 给出。
def inside (e : (G).E) (b : Bool) : (G).End := cond b (.inr (.inr e)) (.inl (.inr e))

-- 读法：逐一匹配以下输入模式：`⟨.inl (e, b), i⟩`、`⟨.inr p, i⟩`。
def decode : D.Bit → (G).End
  | ⟨.inl (e, b), i⟩ => D.inside (D.bundle.symm ⟨e, i⟩) b
  | ⟨.inr p, i⟩ => boundaryEnd (G) ((BatchDescent.Stack.pin T _).symm (i, p))

-- 读法：`internal` 的取值由 `⟨.inl (D.link e, b), (D.bundle e).2⟩` 给出。
def internal (e : (G).E) (b : Bool) : D.Bit := ⟨.inl (D.link e, b), (D.bundle e).2⟩

-- 读法：`externalPin` 的取值由 `let q := BatchDescent.Stack.pin T (2 ^ t) p ⟨.inr q.2, q.1⟩` 给出。
def externalPin (p : Ports (BatchDescent.Stack.tensor T (2 ^ t))) : D.Bit :=
  let q := BatchDescent.Stack.pin T (2 ^ t) p
  ⟨.inr q.2, q.1⟩

-- 读法：逐一匹配以下输入模式：`.inl (.inl p)`、`.inr (.inl p)`、`.inl (.inr e)`、`.inr (.inr e)`。
def encode : (G).End → D.Bit
  | .inl (.inl p) => D.externalPin (.inl p)
  | .inr (.inl p) => D.externalPin (.inr p)
  | .inl (.inr e) => D.internal e false
  | .inr (.inr e) => D.internal e true

-- 读法：`D.encode (D.inside e b)` 等于 `D.internal e b`。
@[simp] theorem encode_inside (e : (G).E) (b : Bool) : D.encode (D.inside e b) = D.internal e b := by
  cases b <;> rfl

-- 读法：`D.encode (boundaryEnd (G) p)` 等于 `D.externalPin p`。
@[simp] theorem encode_boundary (p : Ports (BatchDescent.Stack.tensor T (2 ^ t))) :
    D.encode (boundaryEnd (G) p) = D.externalPin p := by cases p <;> rfl

-- 读法：`D.decode (D.internal e b)` 等于 `D.inside e b`。
private theorem decode_internal (e : (G).E) (b : Bool) : D.decode (D.internal e b) = D.inside e b :=
  congrArg (fun k => D.inside k b) (D.bundle.symm_apply_apply e)

-- 读法：`D.decode (D.externalPin p)` 等于 `boundaryEnd (G) p`。
private theorem decode_outer (p : Ports (BatchDescent.Stack.tensor T (2 ^ t))) :
    D.decode (D.externalPin p) = boundaryEnd (G) p :=
  congrArg (boundaryEnd (G)) ((BatchDescent.Stack.pin T _).symm_apply_apply p)

-- 读法：用字段 `toFun`、`invFun`、`right_inv` 构造 `(G).End ≃ D.Bit`。
def codec : (G).End ≃ D.Bit where
  toFun := D.encode
  invFun := D.decode
  left_inv
    | .inl (.inl p) => D.decode_outer (.inl p)
    | .inr (.inl p) => D.decode_outer (.inr p)
    | .inl (.inr e) => D.decode_internal e false
    | .inr (.inr e) => D.decode_internal e true
  right_inv q := by
    rcases q with ⟨⟨e, b⟩|p, i⟩
    · rw [decode, encode_inside]
      exact congrArg (fun p => (⟨.inl (p.1, b), p.2⟩ : D.Bit)) (D.bundle.apply_symm_apply ⟨e, i⟩)
    · rw [decode, encode_boundary]
      exact congrArg (fun q => (⟨.inr q.2, q.1⟩ : D.Bit))
        ((BatchDescent.Stack.pin T _).apply_symm_apply (i, p))

-- 读法：`D.site (D.codec e).1` 等于 `(G).station e`。这里调用 `D.external`。
theorem site_codec (e : (G).End) : D.site (D.codec e).1 = (G).station e := by
  rcases e with (i|e)|(i|e)
  · exact (D.external (.inl i)).symm
  · rfl
  · exact (D.external (.inr i)).symm
  · rfl

-- 读法：`D.side (D.codec e).1` 等于 `e.isRight`。
theorem side_codec (e : (G).End) : D.side (D.codec e).1 = e.isRight := by
  rcases e with (i|e)|(i|e) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Device
end

/-!
# 每个蝶形站点只需常数个跨度名称

**英文原文**

Constantly many span names per butterfly station
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Device
open Assembly Coloring Transcript Packing Finset
open scoped Classical

variable {F : Type} [Field F] {T : Table F} {t : ℕ} (D : Device T t)
local notation "G" => D.diagram

-- 读法：`neighbor` 的取值由 `Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using D.degree v))` 给出。
private def neighbor (v : (G).V) : ↥(D.adj v) ↪ Fin 4 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using D.degree v))

-- 读法：当 `h : w ∈ D.adj v` 成立时取 `D.neighbor v ⟨w, h⟩`，否则取 `0`。
private def number (v w : (G).V) := if h : w ∈ D.adj v then D.neighbor v ⟨w, h⟩ else 0

-- 读法：`w` 等于 `y`。
private theorem number_inj {v w x y : (G).V} (hw : w ∈ D.adj v) (hy : y ∈ D.adj x)
    (he : v = x) (hn : D.number v w = D.number x y) : w = y := by
  subst x
  simp only [number, dite_eq_left hw, dite_eq_left hy] at hn
  exact congrArg Subtype.val ((D.neighbor _).injective hn)

-- 读法：`c.val.2` 属于 `D.adj c.val.1`。
theorem linked_at (c : D.Link) : c.val.2 ∈ D.adj c.val.1 := by
  obtain ⟨e, he⟩ := c.property
  rw [← he]; exact D.linked e

-- 读法：`code` 的取值由 `Classical.choice (Function.Embedding.nonempty_of_card_le (by simp))` 给出。
private def code : Option (Bool × Fin 4) ↪ B 4 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simp))

-- 读法：逐一匹配以下输入模式：`.inl (c, b)`、`.inr _`。
def slot : D.Line → B 4
  | .inl (c, b) => code (some (b, D.number (D.site (.inl (c, b))) (D.site (.inl (c, !b)))))
  | .inr _ => code none

-- 读法：`x` 等于 `y`。按 `Subtype.ext` 的外延性准则比较各分量。
theorem slot_inj {x y : D.Line} (hv : D.site x = D.site y) (hs : D.slot x = D.slot y) : x = y := by
  rcases x with ⟨c, b⟩|p <;> rcases y with ⟨d, a⟩|q
  · obtain ⟨rfl, he⟩ := Prod.mk.inj (Option.some.inj (code.injective hs))
    have hc := D.linked_at c
    have hd := D.linked_at d
    have eq : c = d := by
      apply Subtype.ext
      cases b
      · exact Prod.ext hv (D.number_inj hc hd hv he)
      · exact Prod.ext (D.number_inj (D.sym _ _ hc) (D.sym _ _ hd) hv he) hv
    rw [eq]
  · cases code.injective hs
  · cases code.injective hs
  · exact congrArg Sum.inr (D.name.injective hv)

-- 读法：当 `h : ∃ p, D.site p = v ∧ D.slot p = s` 成立时取 `some h.choose`，否则取 `none`。
def line (v : (G).V) (s : B 4) : Option D.Line :=
  if h : ∃ p, D.site p = v ∧ D.slot p = s then some h.choose else none

-- 读法：`D.line v s = some p` 与 `D.site p = v ∧ D.slot p = s` 等价。这里调用 `iff_of_false`。
theorem line_eq (v : (G).V) (s : B 4) (p : D.Line) :
    D.line v s = some p ↔ D.site p = v ∧ D.slot p = s := by
  unfold line
  split
  · rename_i h
    rw [Option.some.injEq]
    exact ⟨fun he => he ▸ h.choose_spec, fun he =>
      D.slot_inj (h.choose_spec.1.trans he.1.symm) (h.choose_spec.2.trans he.2.symm)⟩
  · rename_i h
    exact iff_of_false (by simp) (fun e => h ⟨p, e⟩)

-- 读法：`sizeAt` 的取值由 `(D.line v s).elim 0 D.width` 给出。
def sizeAt (v : (G).V) (s : B 4) := (D.line v s).elim 0 D.width

-- 读法：`D.sizeAt v (D.slot l)` 等于 `D.width l`。
theorem sizeAt_slot (v : (G).V) (l : D.Line) (h : D.site l = v) :
    D.sizeAt v (D.slot l) = D.width l := by
  rw [sizeAt, (D.line_eq ..).mpr ⟨h, rfl⟩]; rfl

-- 读法：`localBit` 的取值由 `D.codec ((G).portEquiv ⟨v, p⟩)` 给出。
def localBit (v : (G).V) (p : (G).Port v) := D.codec ((G).portEquiv ⟨v, p⟩)

-- 读法：`D.site (D.localBit v p).1` 等于 `v`。
theorem local_site (v : (G).V) (p : (G).Port v) : D.site (D.localBit v p).1 = v := by
  rw [localBit, site_codec, Diagram.station_port]

-- 读法：`address` 的取值由 `⟨D.slot (D.localBit v p).1, (D.localBit v p).2.cast (D.sizeAt_slot _ _ (D.local_site v p)).symm⟩` 给出。
def address (v : (G).V) (p : (G).Port v) : Σ s, Fin (D.sizeAt v s) :=
  ⟨D.slot (D.localBit v p).1, (D.localBit v p).2.cast (D.sizeAt_slot _ _ (D.local_site v p)).symm⟩

-- 读法：`(D.address v)` 是双射。这里调用 `eq_of_heq`。
theorem bijective (v : (G).V) : Function.Bijective (D.address v) := by
  constructor
  · intro a b he
    have h := D.slot_inj ((D.local_site _ a).trans (D.local_site _ b).symm) (congrArg Sigma.fst he)
    have e : D.localBit v a = D.localBit v b := Sigma.ext h
      ((Fin.heq_ext_iff (congrArg D.width h)).mpr (congrArg (fun i => i.2.val) he))
    exact eq_of_heq (Sigma.mk.inj ((G).portEquiv.injective (D.codec.injective e))).2
  · rintro ⟨s, i⟩
    cases h : D.line v s with
    | none => have := i.isLt; simp [sizeAt, h] at this
    | some l =>
      -- 推导：从 `(D.line_eq ..).mp h` 中取出 `hv, hs`。
      obtain ⟨hv, hs⟩ := (D.line_eq ..).mp h
      have hw : D.sizeAt v s = D.width l := by rw [sizeAt, h]; rfl
      obtain ⟨⟨u, p⟩, he⟩ := ((G).portEquiv.trans D.codec).surjective ⟨l, i.cast hw⟩
      change D.localBit u p = _ at he
      have hu : u = v := (D.local_site u p).symm.trans (he ▸ hv)
      subst u
      refine ⟨p, ?_⟩
      have h₁ : (D.address v p).1 = s := (congrArg (fun k : D.Bit => D.slot k.1) he).trans hs
      exact Sigma.ext h₁ ((Fin.heq_ext_iff (congrArg (D.sizeAt v) h₁)).mpr
        (congrArg (fun k : D.Bit => k.2.val) he))

-- 读法：在后续公式中，`Guide` 是 `B 4 → Option (B 3 × B 0 × B 4)` 的缩写。
abbrev Guide := B 4 → Option (B 3 × B 0 × B 4)

-- 读法：用字段 `width`、`direction`、`peer`、`value` 构造 `Pattern F 3 0 4`。
/-- 只有导引信息依赖于器件的放置位置，其字母表的选取与原图和堆叠宽度无关。

英文原文：Only the guide depends on the placement of the device. Its alphabet
is fixed independently of the original graph and the stack width.
-/
def pattern (v : (G).V) (g : Guide) : Pattern F 3 0 4 where
  width _ := D.sizeAt v
  direction _ s := (D.line v s).elim false D.side
  peer _ := g
  value _ x := sample ((G).table v) (fun p => x (D.address v p).1 (D.address v p).2)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Device
end

/-!
# 叠层中各装置共用同一部字典

**英文原文**

One shared dictionary for the devices of a stack
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
open Assembly Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {t : ℕ}

-- 读法：用字段 `width`、`direction`、`peer`、`value` 构造 `Pattern F 3 0 4`。
def emptyPattern (F : Type) [Field F] : Pattern F 3 0 4 where
  width _ _ := 0
  direction _ _ := false
  peer _ _ := none
  value _ _ := 1

-- 读法：结构的字段包括 `decode`、`label`、`read`、`blank`、`empty`。
structure Codec (G : Diagram F a b) (f : ∀ v, Device (G.table v) t) (ℓ : ℕ) where
  decode : B ℓ → Pattern F 3 0 4
  label : ∀ v, (f v).diagram.V → Device.Guide → B ℓ
  read : ∀ v z a, decode (label v z a) = (f v).pattern z a
  blank : B ℓ
  empty : decode blank = emptyPattern F

-- 读法：存在 `f : ∀ v`，要证明的命题是 `Device (G.table v) t, Nonempty (Codec G f (Nat.clog 2 (1 + M * 4 * (1 + 2 ^ t) * (t + 1) * Nat.card Device.Guide)))`。
/-- 相同的表使用同一个器件。一个标签只需指明表、器件中的顶点及导引信息。另留一个空白标签。

英文原文：Equal tables use the same device. A label names only a table, a
vertex within that device and a guide. Reserve one extra blank label.
-/
theorem codec (G : Diagram F a b) (ht : 0 < t) (bound : ∀ v, G.arity v ≤ 2 ^ t)
    {M : ℕ} (hc : (univ.image G.table).card ≤ M) :
    ∃ f : ∀ v, Device (G.table v) t,
      Nonempty (Codec G f (Nat.clog 2 (1 + M * 4 * (1 + 2 ^ t) * (t + 1) * Nat.card Device.Guide))) := by
  let L := univ.image G.table
  have hwidth (T : L) : wd T.val.1 + wd T.val.2.1 ≤ 2 ^ t := by
    obtain ⟨v, _, hv⟩ := mem_image.mp T.property
    rw [← hv]
    exact bound v
  let D (T : L) := Classical.choice (device T.val t ht (hwidth T))
  let ofV (v : G.V) : L := ⟨G.table v, mem_image_of_mem _ (mem_univ v)⟩
  let f := fun v => D (ofV v)
  let K := Option (Σ T : L, (D T).diagram.V × Device.Guide)
  let N := 1 + M * 4 * (1 + 2 ^ t) * (t + 1) * Nat.card Device.Guide
  -- 推导：记下中间结论 `hcard`：`Fintype.card K ≤ N`。
  have hcard : Fintype.card K ≤ N := by
    have hs (T : L) : Fintype.card (D T).diagram.V ≤ 4 * (1 + 2 ^ t) * (t + 1) := by
      refine (D T).size.trans ?_
      have := hwidth T
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    simp only [K, Fintype.card_option, Fintype.card_sigma, Fintype.card_prod, ←Nat.card_eq_fintype_card (α := Device.Guide)]
    calc
      _ ≤ (∑ _ : L, 4 * (1 + 2 ^ t) * (t + 1) * Nat.card Device.Guide) + 1 :=
        Nat.add_le_add_right (sum_le_sum fun T _ => Nat.mul_le_mul_right _ (hs T)) _
      _ ≤ N := by
        rw [sum_const, card_univ, Fintype.card_coe, Nat.nsmul_eq_mul]
        unfold N
        conv_rhs => rw [add_comm]
        simp only [mul_assoc]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _
  -- 推导：从 `Function.Embedding.nonempty_of_card_le (α := K) (β := B (Nat.clog 2 N))` 中取出 `e`。
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := K) (β := B (Nat.clog 2 N))
    (by rw [Fintype.card_fin]; exact hcard.trans (Nat.le_pow_clog (by decide) _))
  let pattern : K → Pattern F 3 0 4
    | none => emptyPattern F
    | some z => (D z.1).pattern z.2.1 z.2.2
  let decode := pattern ∘ Function.invFun e
  have read (k : K) : decode (e k) = pattern k :=
    congrArg pattern (Function.leftInverse_invFun e.injective k)
  exact ⟨f, ⟨⟨decode, fun v z g => e (some ⟨ofV v, z, g⟩),
    fun v z g => read (some ⟨ofV v, z, g⟩), e none, read none⟩⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack
end

/-!
# 在局部装置叠层中追踪所有具名端口

**英文原文**

Tracking all named ports through a stack of local devices
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {h t n : ℕ} (G : Diagram F a b)
  (f : ∀ v, Device (G.table v) t) (c : Cell h × Fin (2 ^ t) ≃ Fin n)

-- 读法：`wireEnd` 的取值由 `cond b (.inr (.inr e)) (.inl (.inr e))` 给出。
def wireEnd (e : G.E) (b : Bool) : G.End := cond b (.inr (.inr e)) (.inl (.inr e))

-- 读法：在后续公式中，`Stub` 是 `Σ v, (f v).Line` 的缩写。
abbrev Stub := Σ v, (f v).Line

-- 读法：`site` 的取值由 `⟨s.1, (f s.1).site s.2⟩` 给出。
def site (s : Stub G f) : Location G f := ⟨s.1, (f s.1).site s.2⟩
-- 读法：`slot` 的取值由 `(f s.1).slot s.2` 给出。
def slot (s : Stub G f) := (f s.1).slot s.2
-- 读法：`side` 的取值由 `(f s.1).side s.2` 给出。
def side (s : Stub G f) := (f s.1).side s.2
-- 读法：`width` 的取值由 `(f s.1).width s.2` 给出。
def width (s : Stub G f) := (f s.1).width s.2

-- 读法：`outer` 的取值由 `let q := G.portEquiv.symm e ⟨q.1, .inr q.2⟩` 给出。
def outer (e : G.End) : Stub G f :=
  let q := G.portEquiv.symm e
  ⟨q.1, .inr q.2⟩

-- 读法：`inner` 的取值由 `⟨v, .inl ((f v).link e, s)⟩` 给出。
def inner (v : G.V) (e : (f v).diagram.E) (s : Bool) : Stub G f :=
  ⟨v, .inl ((f v).link e, s)⟩

-- 读法：`lift` 的取值由 `(BatchDescent.Stack.gathered G c).plugEnd (fun v => (f v.2).diagram)` 给出。
def lift := (BatchDescent.Stack.gathered G c).plugEnd (fun v => (f v.2).diagram)

-- 读法：`read` 的取值由 `let i := (lift G f c).symm e let b := (f i.1.2).codec i.2 (i.1.1, ⟨i.1.2, b.1⟩, b.2.val)` 给出。
def read (e : (built G f c).End) : Cell h × Stub G f × ℕ :=
  let i := (lift G f c).symm e
  let b := (f i.1.2).codec i.2
  (i.1.1, ⟨i.1.2, b.1⟩, b.2.val)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
end

/-!
# 用标签匹配局部跨度而无需在标签中记录完整顶点名称

**英文原文**

Matching local spans without using full vertex names in the labels
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
open Assembly Finset
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {t : ℕ} (G : Diagram F a b)
  (f : ∀ v, Device (G.table v) t)

-- 读法：逐一匹配输入模式，例如 `.inl (.inr e)`、`.inr (.inr e)`。
private def across : G.End → Option (Stub G f)
  | .inl (.inr e) => some (outer G f (.inr (.inr e)))
  | .inr (.inr e) => some (outer G f (.inl (.inr e)))
  | _ => none

-- 读法：逐一匹配以下输入模式：`⟨v, .inl (e, b)⟩`、`⟨v, .inr p⟩`。
def mate : Stub G f → Option (Stub G f)
  | ⟨v, .inl (e, b)⟩ => some ⟨v, .inl (e, !b)⟩
  | ⟨v, .inr p⟩ => across G f (G.portEquiv ⟨v, p⟩)

-- 读法：`mate G f (outer G f e)` 等于 `across G f e`。
private theorem mate_outer (e : G.End) : mate G f (outer G f e) = across G f e :=
  congrArg (across G f) (G.portEquiv.apply_symm_apply e)

-- 读法：`mate G f (outer G f (wireEnd G e b))` 等于 `some (outer G f (wireEnd G e (!b)))`。
theorem mate_edge (e : G.E) (b : Bool) :
    mate G f (outer G f (wireEnd G e b)) = some (outer G f (wireEnd G e (!b))) := by
  rw [mate_outer]; cases b <;> rfl

-- 读法：`mate G f (inner G f v e b)` 等于 `some (inner G f v e (!b))`。两端由定义化简为同一项。
theorem mate_inner (v : G.V) (e : (f v).diagram.E) (b : Bool) :
    mate G f (inner G f v e b) = some (inner G f v e (!b)) := rfl

-- 读法：`mate G f (outer G f (boundaryEnd G i))` 等于 `none`。
theorem mate_boundary (i : slots a ⊕ slots b) :
    mate G f (outer G f (boundaryEnd G i)) = none := by
  rw [mate_outer]; cases i <;> rfl

-- 读法：`side G f (outer G f e)` 等于 `e.isRight`。
theorem side_outer (e : G.End) : side G f (outer G f e) = e.isRight := by
  cases e <;> rfl

-- 读法：`site G f (outer G f (other G e))` 属于 `Device.neighbors G f (site G f (outer G f e))`。使用 `mem_insert.mpr` 给出的结论。
private theorem adjacent_outer (e : G.End) :
    site G f (outer G f (other G e)) ∈ Device.neighbors G f (site G f (outer G f e)) :=
  mem_insert.mpr (.inl (Device.partner_end G f e).symm)

-- 读法：`mate G f j = some i` 与 `width G f i = width G f j ∧ side G f i ≠ side G f j ∧ site G f j ∈ Device.neighbors G f (site G f i)` 同时成立。对 `z` 分类讨论。
theorem mate_props {i j : Stub G f} (h : mate G f i = some j) :
    mate G f j = some i ∧ width G f i = width G f j ∧ side G f i ≠ side G f j ∧
    site G f j ∈ Device.neighbors G f (site G f i) := by
  rcases i with ⟨v, ⟨e, z⟩|p⟩
  · have : j = ⟨v, .inl (e, !z)⟩ := (Option.some.inj h).symm
    subst j
    have w := (f v).linked_at e
    cases z
    · exact ⟨rfl, rfl, Bool.false_ne_true, mem_insert_of_mem (mem_image_of_mem (Sigma.mk v) w)⟩
    · exact ⟨rfl, rfl, Ne.symm Bool.false_ne_true,
        mem_insert_of_mem (mem_image_of_mem (Sigma.mk v) ((f v).sym _ _ w))⟩
  -- 推导：记下中间结论 `e`：`(⟨v, .inr p⟩ : Stub G f) = outer G f (G.portEquiv ⟨v, p⟩)`。
  · have e : (⟨v, .inr p⟩ : Stub G f) = outer G f (G.portEquiv ⟨v, p⟩) :=
      congrArg (fun k : Σ v, G.Port v => (⟨k.1, .inr k.2⟩ : Stub G f))
        (G.portEquiv.symm_apply_apply ⟨v, p⟩).symm
    rw [e] at h ⊢
    rw [mate_outer] at h
    generalize G.portEquiv ⟨v, p⟩ = k at h ⊢
    rcases k with (i|d)|(i|d)
    · cases h
    · obtain rfl := Option.some.inj h
      exact ⟨mate_edge G f d true, rfl, Bool.false_ne_true, adjacent_outer G f (.inl (.inr d))⟩
    · cases h
    · obtain rfl := Option.some.inj h
      exact ⟨mate_edge G f d false, rfl, Ne.symm Bool.false_ne_true, adjacent_outer G f (.inr (.inr d))⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
end

/-!
# 连接后叠层中每个端点所属的块、跨度及序号

**英文原文**

The block, span and ordinal of every end of the joined stack
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
open Assembly Packing

variable {F : Type} [Field F] {a b : Wire} {h t n : ℕ} (G : Diagram F a b)
  (f : ∀ v, Device (G.table v) t) (c : Cell h × Fin (2 ^ t) ≃ Fin n)

-- 读法：`read G f c e` 等于 `(z.1, outer G f i, z.2.val)`。
private theorem read_outer (z : Cell h × Fin (2 ^ t)) (i : G.End) (e : (built G f c).End)
    (he : let p := G.portEquiv.symm i
      (lift G f c).symm e = ⟨(z.1, p.1), boundaryEnd (f p.1).diagram
        ((BatchDescent.Stack.pin (G.table p.1) (2 ^ t)).symm (z.2, p.2))⟩) :
    read G f c e = (z.1, outer G f i, z.2.val) := by
  unfold read
  rw [he]
  let p := G.portEquiv.symm i
  let D := f p.1
  let q := (BatchDescent.Stack.pin (G.table p.1) (2 ^ t)).symm (z.2, p.2)
  have hc : D.codec (boundaryEnd D.diagram q) = ⟨.inr p.2, z.2⟩ := by
    change D.encode _ = _
    rw [D.encode_boundary, Device.externalPin]
    exact congrArg (fun r => (⟨.inr r.2, r.1⟩ : D.Bit))
      ((BatchDescent.Stack.pin (G.table p.1) (2 ^ t)).apply_symm_apply (z.2, p.2))
  exact congrArg (fun r : D.Bit => (z.1, (⟨p.1, r.1⟩ : Stub G f), r.2.val)) hc

-- 读法：`read G f c (wireEnd (built G f c) (.inl (z, e)) s)` 等于 `(z.1, outer G f (wireEnd G e s), z.2.val)`。这里调用 `read_outer`。
theorem read_edge (z : Cell h × Fin (2 ^ t)) (e : G.E) (s : Bool) :
    read G f c (wireEnd (built G f c) (.inl (z, e)) s) = (z.1, outer G f (wireEnd G e s), z.2.val) := by
  apply read_outer
  cases s <;> rfl

-- 读法：`read G f c (wireEnd (built G f c) (.inr ⟨(z, v), e⟩) s)` 等于 `(z, inner G f v e s, ((f v).bundle e).2.val)`。
theorem read_inner (z : Cell h) (v : G.V) (e : (f v).diagram.E) (s : Bool) :
    read G f c (wireEnd (built G f c) (.inr ⟨(z, v), e⟩) s) =
      (z, inner G f v e s, ((f v).bundle e).2.val) := by
  cases s <;> rfl

-- 读法：`copiedPort` 的取值由 `((Diagonal.port a n).sumCongr (Diagonal.port b n)).trans (Equiv.prodSumDistrib _ _ _).symm` 给出。
def copiedPort (a b : Wire) (n : ℕ) :
    slots (copies a n) ⊕ slots (copies b n) ≃ Fin n × (slots a ⊕ slots b) :=
  ((Diagonal.port a n).sumCongr (Diagonal.port b n)).trans (Equiv.prodSumDistrib _ _ _).symm

-- 读法：结论为 `let p := copiedPort a b n i let z := c.symm p.1 read G f c (boundaryEnd (built G f c) i) = (z.1, outer G f (boundaryEnd G p.2), z.2.val)`。这里调用 `read_outer`。
theorem read_boundary (i : slots (copies a n) ⊕ slots (copies b n)) :
    let p := copiedPort a b n i
    let z := c.symm p.1
    read G f c (boundaryEnd (built G f c) i) = (z.1, outer G f (boundaryEnd G p.2), z.2.val) := by
  apply read_outer
  cases i <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Stack.Label
end
