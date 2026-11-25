-- 本文件所属证明环节：把张量网络中的处理器、数据包、表项和端口寻址表示为有限记录，计算接收核和容量；利用对角抵抗性约束假定的低成本协议。
import OAI.LinearAlgebra.MatrixExponent.Install.ControlWeight
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Diagonal.AlphabetCode

section
/-!
# 不相交的有名比特集上的权重乘积

**英文原文**

Products of weights on disjoint sets of named bits
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install

-- 读法：用字段 `toFun`、`left_inv`、`right_inv` 构造 `I none ⊕ (Σ v : V, I (some v)) ≃ (Σ v, I v)`。
private def optionSlots {V : Type} (I : Option V → Type) :
    I none ⊕ (Σ v : V, I (some v)) ≃ (Σ v, I v) where
  toFun := Sum.elim (Sigma.mk none) (fun p => ⟨some p.1, p.2⟩)
  invFun
    | ⟨none, i⟩ => .inl i
    | ⟨some v, i⟩ => .inr ⟨v, i⟩
  left_inv := by rintro (i|⟨v, i⟩) <;> rfl
  right_inv := by rintro ⟨_|v, i⟩ <;> rfl

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : (Σ v, I v) → Bool) (j : Σ v, J v) => f j.1 (fun i => x ⟨j.1, i⟩) j.2)` 均在 `F` 上有顶点数至多为 `(∑ v, m v)` 的网络实现。这里调用 `Fintype.induction_empty_option`。
/-- 局部输入互不相交的并行确定性电路。

英文原文：Parallel deterministic circuits with disjoint local inputs.
-/
theorem BNet.sigma {F : Type} [Field F] {V : Type} [Fintype V]
    {I J : V → Type} [∀ v, Fintype (I v)] [∀ v, Fintype (J v)]
    (f : ∀ v, (I v → Bool) → J v → Bool) {m : V → ℕ} (h : ∀ v, BNet F (f v) (m v)) :
    BNet F (fun (x : (Σ v, I v) → Bool) (j : Σ v, J v) =>
      f j.1 (fun i => x ⟨j.1, i⟩) j.2) (∑ v, m v) := by
  classical
  revert V
  apply Fintype.induction_empty_option
  · intro A B _ e ih I J _ _ f m h
    let := Fintype.ofEquiv B e.symm
    have k := ih (fun v => f (e v)) (fun v => h (e v))
    rw [← e.sum_comp m]
    -- 推导：记下中间结论 `p`：`= Equiv.sigmaCongrLeft (β`。
    let p := Equiv.sigmaCongrLeft (β := J) e
    convert k.rename (Equiv.sigmaCongrLeft e) p using 1
    funext x j
    obtain ⟨y, rfl⟩ := p.surjective j
    let g (z : Σ v, J (e v)) := f (e z.1) (fun i => x ⟨e z.1, i⟩) z.2
    exact congrArg g (p.symm_apply_apply y).symm
  · intro I J _ _ f m h
    let : IsEmpty (Σ v, I v) := ⟨fun p => p.1.elim⟩
    let : IsEmpty (Σ v, J v) := ⟨fun p => p.1.elim⟩
    apply BNet.of_layout (a := .unit) (b := .unit) (Equiv.equivEmpty _) (Equiv.equivEmpty _)
    rw [Fintype.sum_empty]
    exact DNet.id F .unit
  · intro V _ ih I J _ _ f m h
    have k := ih (fun v => f (some v)) (fun v => h (some v))
    rw [Fintype.sum_option]
    convert ((h none).parallel k).rename (optionSlots I) (optionSlots J) using 1
    funext x j
    rcases j with ⟨_|v, j⟩ <;> rfl

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun x (t : V × J) => f t.1 x t.2)` 均在 `F` 上有顶点数至多为 `(Fintype.card I + Fintype.card V * (2 * Fintype.card I + m))` 的网络实现。这里调用 `k.mono`。
/-- 将一个共同输入读入任意有限个电路中。

英文原文：Read a common input into an arbitrary finite collection of circuits.
-/
theorem BNet.collect {F I J V : Type} [Field F] [Fintype I] [Fintype J] [Fintype V]
    (f : V → (I → Bool) → J → Bool) {m : ℕ} (h : ∀ v, BNet F (f v) m) :
    BNet F (fun x (t : V × J) => f t.1 x t.2)
      (Fintype.card I + Fintype.card V * (2 * Fintype.card I + m)) := by
  have k := ((BNet.sigma f h).pull (fun p => p.2)).rename (Equiv.refl I) (Equiv.sigmaEquivProd V J)
  apply k.mono
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  exact le_of_eq (by ring)

namespace Weight

-- 读法：要证明的命题是 `Weight F (fun x : (Σ v, I v) → Bool => ∏ v, f v (fun i => x ⟨v, i⟩)) (∑ v, m v)`。这里调用 `Fintype.induction_empty_option`。
/-- 不交乘积的成本至多是各局部成本之和，即使各因子使用各自的坐标集也如此。

英文原文：The cost of a disjoint product is at most the sum of local costs,
even if each factor uses its own set of coordinates.
-/
theorem sigma_prod {F : Type} [Field F] {V : Type} [Fintype V]
    {I : V → Type} [∀ v, Fintype (I v)]
    (f : ∀ v, (I v → Bool) → F) {m : V → ℕ} (h : ∀ v, Weight F (f v) (m v)) :
    Weight F (fun x : (Σ v, I v) → Bool => ∏ v, f v (fun i => x ⟨v, i⟩)) (∑ v, m v) := by
  classical
  revert V
  apply Fintype.induction_empty_option
  · intro A B _ e ih I _ f m h
    let := Fintype.ofEquiv B e.symm
    have k := ih (fun v => f (e v)) (fun v => h (e v))
    rw [← e.sum_comp m]
    convert k.rename (Equiv.sigmaCongrLeft e) using 1
    funext x
    rw [← e.prod_comp]
    rfl
  · intro I _ f m h
    have : IsEmpty (Σ v, I v) := ⟨fun p => p.1.elim⟩
    apply of_layout (a := .unit) (Equiv.equivEmpty _)
    exact ⟨0, Nat.zero_le _, by simpa using (Net.empty (F := F))⟩
  · intro V _ ih I _ f m h
    have k := ih (fun v => f (some v)) (fun v => h (some v))
    rw [Fintype.sum_option]
    convert ((h none).parallel k).rename (optionSlots I) using 1
    funext x
    rw [Fintype.prod_option]
    rfl

-- 读法：要证明的命题是 `Weight F (fun x : Unit ⊕ I → Bool => if x (.inl ()) then f (x ∘ Sum.inr) else 1) (1000 * (m + Fintype.card I + 1))`。按 `b () = true` 成立与否分情况。
/-- 用一个控制比特启用因子。在未启用的分支上，该因子的权重为一，与其私有指派无关。

英文原文：Enable a factor with one control bit. On the inactive branch its
weight is one, independently of its private assignments.
-/
theorem branch {F I : Type} [Field F] [Fintype I] {f : (I → Bool) → F} {m : ℕ}
    (h : Weight F f m) :
    Weight F (fun x : Unit ⊕ I → Bool => if x (.inl ()) then f (x ∘ Sum.inr) else 1)
      (1000 * (m + Fintype.card I + 1)) := by
  have hf (b : Unit → Bool) :
      Weight F (fun x => if b () then f x else 1) (m + Fintype.card I) := by
    by_cases hb : b () = true
    · simpa [hb] using h.mono (Nat.le_add_right m (Fintype.card I))
    · intro a i
      obtain ⟨v, hv, hs⟩ := DNet.discard F a
      refine ⟨v, ?_, ?_⟩
      · rw [Fintype.card_congr i, card_slots]
        omega
      · simpa [hb] using hs
  apply (switch _ hf).mono
  simp [switchCost, localCost]
  omega

end Weight
end OAI.LinearAlgebra.MatrixExponent.Install
end

section
/-!
# 高效的高元数表

若一张高元数表的标量条目可由规模相对于元数为拟线性的三价网络实现，图式就可以使用它。处理器只需获得该表的电路描述。

**英文原文**

Efficient high-arity tables

A diagram may use a high-arity table if its scalar entries have a
trivalent realization of size quasilinear in its arity. The processor
needs only a circuit description for this table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Install
variable {F : Type} [Field F] {a b : Wire}

-- 读法：`arity` 的取值由 `wd T.1 + wd T.2.1` 给出。
def arity (T : Table F) : ℕ := wd T.1 + wd T.2.1

-- 读法：`Cheap` 的取值由 `{T | ∃ m ≤ (1 + arity T) * K * (1 + Nat.clog 2 (1 + arity T)) ^ q, Net F T.1 T.2.1 T.2.2 m}` 给出。
def Cheap (F : Type) [Field F] (K q : ℕ) : Set (Table F) :=
  {T | ∃ m ≤ (1 + arity T) * K * (1 + Nat.clog 2 (1 + arity T)) ^ q, Net F T.1 T.2.1 T.2.2 m}

-- 读法：在后续公式中，`PortsOf` 是 `slots T.1 ⊕ slots T.2.1` 的缩写。
abbrev PortsOf (T : Table F) := slots T.1 ⊕ slots T.2.1

-- 读法：`weight` 的取值由 `T.2.2 ((bits T.1).symm (s ∘ Sum.inl)) ((bits T.2.1).symm (s ∘ Sum.inr))` 给出。
def weight (T : Table F) (s : PortsOf T → Bool) : F :=
  T.2.2 ((bits T.1).symm (s ∘ Sum.inl)) ((bits T.2.1).symm (s ∘ Sum.inr))

-- 读法：要证明的命题是 `Weight F (weight ⟨a, b, k⟩) (m + wd b)`。这里调用 `Weight.of_layout`。
private theorem of_net {k : Val a → Val b → F} {m : ℕ} (h : Net F a b k m) :
    Weight F (weight ⟨a, b, k⟩) (m + wd b) := by
  have t := ((h.par (Tagged.cap b)).pre (.assoc a b b)).post (.swap _ _)
  apply Weight.of_layout (a := .pair a b) (.refl _)
  refine ⟨m + wd b, le_rfl, ?_⟩
  convert t.trace using 1
  funext x y
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change k ((bits a).symm (bits a x.1)) ((bits b).symm (bits b x.2)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

-- 读法：`rate` 的取值由 `2 + K * (1 + Nat.clog 2 (1 + D)) ^ q` 给出。
/-- 对每个参数和每个顶点均适用的开销上界。

英文原文：A common overhead bound for each argument and vertex.
-/
def rate (K q D : ℕ) := 2 + K * (1 + Nat.clog 2 (1 + D)) ^ q

-- 读法：要证明的命题是 `Weight F (weight T) ((1 + arity T) * rate K q D)`。这里调用 `Nat.add_le_add_left`。
theorem weight_cheap {T : Table F} {K q D : ℕ} (hd : arity T ≤ D)
    (ht : arity T ≤ 3 ∨ T ∈ Cheap F K q) :
    Weight F (weight T) ((1 + arity T) * rate K q D) := by
  have hi : wd T.2.1 ≤ arity T := Nat.le_add_left _ _
  rcases ht with ht | ⟨m, hm, hn⟩
  · refine (of_net (Net.table _ _ T.2.2 ht)).mono ?_
    unfold rate
    exact (Nat.add_le_add_left hi 1).trans (Nat.le_mul_of_pos_right _ (by omega))
  · refine (of_net hn).mono ?_
    calc
      _ ≤ (1 + arity T) * K * (1 + Nat.clog 2 (1 + arity T)) ^ q + arity T := Nat.add_le_add hm hi
      _ ≤ (1 + arity T) * K * (1 + Nat.clog 2 (1 + D)) ^ q + arity T := by gcongr
      _ ≤ _ := by unfold rate; ring_nf; omega

end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# 公开报告中计数字段上的算术运算

计算输入比特的一个固定非负线性组合，只需线性工作量乘以寄存器宽度。输出按寄存器容量取模。后续比较需要显式给出排除溢出的上界。

**英文原文**

Arithmetic on count fields in public reports

A fixed nonnegative linear combination of input bits requires only
linear work times the register width. The output is modulo the size
of the register. Comparisons below require explicit no-overflow bounds.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Install Coloring
variable {F I J : Type} [Field F] {w m n : ℕ}

-- 读法：`digits` 的取值由 `(Control.decode w).symm (Fin.ofNat (2 ^ w) k)` 给出。
def digits (w k : ℕ) : slots (word w) → Bool := (Control.decode w).symm (Fin.ofNat (2 ^ w) k)

-- 读法：`Register` 的取值由 `BNet F (fun x => digits w (f x)) m` 给出。
def Register (F : Type) [Field F] (w : ℕ) (f : (I → Bool) → ℕ) (m : ℕ) :=
  BNet F (fun x => digits w (f x)) m

namespace Register

variable {f : (I → Bool) → ℕ}

-- 读法：要证明的命题是 `Register F w f n`。使用 `BNet.mono` 给出的结论。
theorem mono (h : Register F w f m) (le : m ≤ n) : Register F w f n := BNet.mono h le

-- 读法：要证明的命题是 `Register F w (fun x => f (x ∘ e)) m`。使用 `BNet.rename` 给出的结论。
theorem rename (h : Register F w f m) (e : I ≃ J) :
    Register F w (fun x => f (x ∘ e)) m := BNet.rename h e (.refl _)

-- 读法：要证明的命题是 `Register F w (fun _ : I → Bool => k) (Fintype.card I + 16 * w)`。这里调用 `h.bnet`。
theorem const [Fintype I] (k : ℕ) :
    Register F w (fun _ : I → Bool => k) (Fintype.card I + 16 * w) := by
  have h : Depends (fun _ : I → Bool => digits w k) 0 :=
    fun _ => ⟨∅, by simp, fun _ _ _ => rfl⟩
  simpa [Register, localCost] using h.bnet F

-- 读法：要证明的命题是 `Register F w (fun x : Unit → Bool => if x () then k else 0) (1 + 34 * w)`。这里调用 `h.bnet`。
private theorem of_bit (k : ℕ) :
    Register F w (fun x : Unit → Bool => if x () then k else 0) (1 + 34 * w) := by
  have h : Depends (fun x : Unit → Bool => digits w (if x () then k else 0)) 1 := by
    intro i
    exact ⟨{()}, by simp, fun x y h => by simp only [h () (by simp)]⟩
  simpa [Register, localCost] using h.bnet F

-- 读法：要证明的命题是 `Register F w (fun x => f (x ∘ Sum.inl) + g (x ∘ Sum.inr)) (m + n + 10000 * (1 + w))`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem add_disjoint [Fintype I] [Fintype J] {g : (J → Bool) → ℕ}
    (h : Register F w f m) (k : Register F w g n) :
    Register F w (fun x => f (x ∘ Sum.inl) + g (x ∘ Sum.inr)) (m + n + 10000 * (1 + w)) := by
  have hb := (BNet.parallel h k).comp (numeric_add F w)
  unfold Register
  convert hb using 1
  funext x
  let i := f (x ∘ Sum.inl)
  let j := g (x ∘ Sum.inr)
  change digits w (i + j) = (Control.decode w).symm
    (Control.decode w (digits w i) + Control.decode w (digits w j))
  simp only [digits, Equiv.apply_symm_apply]
  exact congrArg _ (Fin.ext (Nat.add_mod i j (2 ^ w)))

-- 读法：`optionEquiv` 的结果类型为 `Unit ⊕ I ≃ Option I`。
private def optionEquiv (I : Type) : Unit ⊕ I ≃ Option I :=
  ⟨Sum.elim (fun _ => none) some, fun x => x.elim (.inl ()) Sum.inr,
    by rintro (_|_) <;> rfl, by rintro (_|_) <;> rfl⟩

-- 读法：要证明的命题是 `Register F w (fun x => ∑ i, if x i then k i else 0) (20000 * (1 + Fintype.card I) * (1 + w))`。这里调用 `Fintype.induction_empty_option`。
theorem weighted [Fintype I] (F : Type) [Field F] (w : ℕ) (k : I → ℕ) :
    Register F w (fun x => ∑ i, if x i then k i else 0)
      (20000 * (1 + Fintype.card I) * (1 + w)) := by
  classical
  revert I
  apply Fintype.induction_empty_option
  · intro A B _ e ih k
    let _ := Fintype.ofEquiv B e.symm
    rw [← Fintype.card_congr e]
    convert (ih (k ∘ e)).rename e using 1
    funext x
    rw [← e.sum_comp]
    rfl
  · intro k
    simp only [Fintype.sum_empty]
    exact (const 0).mono (by simp; omega)
  · intro I _ ih k
    -- 推导：记下中间结论 `h`：`= ((of_bit (F`。
    have h := ((of_bit (F := F) (w := w) (k none)).add_disjoint (ih (k ∘ some))).rename (optionEquiv I)
    simp_rw [Fintype.sum_option]
    apply h.mono
    rw [Fintype.card_option]
    ring_nf
    omega

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun x (_ : Unit) => decide (f x < g x))` 均在 `F` 上有顶点数至多为 `(5 * Fintype.card I + m + n + 1000 * (1 + w))` 的网络实现。用函数外延性比较等号两侧在 `x i` 处的取值。
theorem less [Fintype I] {g : (I → Bool) → ℕ}
    (h : Register F w f m) (k : Register F w g n)
    (hf : ∀ x, f x < 2 ^ w) (hg : ∀ x, g x < 2 ^ w) :
    BNet F (fun x (_ : Unit) => decide (f x < g x)) (5 * Fintype.card I + m + n + 1000 * (1 + w)) := by
  have hb := (BNet.pair h k).comp (numeric_lt F w)
  convert hb using 1
  funext x i
  change _ = decide (Control.decode w (digits w (f x)) < Control.decode w (digits w (g x)))
  simp only [digits, Equiv.apply_symm_apply]
  change _ = decide (f x % 2 ^ w < g x % 2 ^ w)
  rw [Nat.mod_eq_of_lt (hf x), Nat.mod_eq_of_lt (hg x)]

end Register
end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-!
# 拼接不同宽度的记录后的地址

**英文原文**

Addresses in a concatenation of variable-width records
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Finset
variable {J : Type} [Fintype J] [LinearOrder J] (w : J → ℕ)

-- 读法：`start` 的取值由 `∑ i ∈ univ.filter (fun i => i < j), w i` 给出。
/-- 在拼接结果中从零开始编号的起始位置。

英文原文：Zero-based start position in the concatenation.
-/
def start (j : J) := ∑ i ∈ univ.filter (fun i => i < j), w i

-- 读法：`start w j + w j` 不超过 `∑ i ∈ s, w i`。
theorem start_le (j : J) (s : Finset J) (h : ∀ i ≤ j, i ∈ s) :
    start w j + w j ≤ ∑ i ∈ s, w i := by
  let t := univ.filter (fun i => i < j)
  have ht : insert j t ⊆ s := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact h _ le_rfl
    · exact h i (mem_filter.mp hi).2.le
  have hh := sum_le_sum_of_subset (f := w) ht
  rw [sum_insert (by simp [t])] at hh
  exact (Nat.add_comm _ _).le.trans hh

-- 读法：`start w i + w i` 不超过 `start w j`。使用 `start_le` 给出的结论。
theorem start_left (i j : J) (h : i < j) : start w i + w i ≤ start w j :=
  start_le w i _ (fun _ hk => mem_filter.mpr ⟨mem_univ _, hk.trans_lt h⟩)

-- 读法：`((Fintype.orderIsoFinOfCardEq _ ht).symm s).val` 等于 `start w s.1 + s.2.val`。这里调用 `Nat.add_lt_add_left`。
theorem serial_rank {t : ℕ} (ht : Fintype.card (Lex (Σ i, Fin (w i))) = t)
    (s : Lex (Σ i, Fin (w i))) :
    ((Fintype.orderIsoFinOfCardEq _ ht).symm s).val = start w s.1 + s.2.val := by
  let f (p : Lex (Σ i, Fin (w i))) : Fin t := ⟨start w p.1 + p.2.val, by
    have h := start_le w p.1 univ (fun _ _ => mem_univ _)
    have he : ∑ i, w i = t := by simpa using ht
    exact (Nat.add_lt_add_left p.2.isLt _).trans_le (h.trans_eq he)⟩
  have hm : StrictMono f := by
    intro p q hp
    rcases Sigma.Lex.lt_def.mp hp with hl|⟨he, hl⟩
    · exact ((Nat.add_lt_add_left p.2.isLt _).trans_le (start_left w _ _ hl)).trans_le
        (Nat.le_add_right _ _)
    -- 推导：从 `p` 中取出 `i, u`。
    · obtain ⟨i, u⟩ := p
      obtain ⟨j, v⟩ := q
      change i = j at he
      subst j
      exact Nat.add_lt_add_left hl _
  have hs := (Fintype.bijective_iff_injective_and_card f).2 ⟨hm.injective, by simpa using ht⟩
  rw [Subsingleton.elim (Fintype.orderIsoFinOfCardEq _ ht).symm
    (StrictMono.orderIsoOfSurjective f hm hs.2)]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Processor
end
