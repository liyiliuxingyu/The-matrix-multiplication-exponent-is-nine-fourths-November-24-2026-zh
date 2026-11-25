-- 本文件所属证明环节：用已获得的线值集合表示直线程序，证明串联、并列、复用中间结果和计算线性组合时的成本估计。
import OAI.LinearAlgebra.MatrixExponent.Integral.Nodes

/-!
# 直线电路的复合与成本

**英文原文**

Composition and costs of straight-line circuits
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {K : Type*} [CommRing K] {S S' T T' U : Set K} {m n : ℕ}

-- 读法：`S` 包含于 `T`。对 `h` 作归纳。
private theorem Integral.Build.retains (h : Integral.Build S m T) : S ⊆ T := by
  induction h with
  | nil => exact Set.Subset.rfl
  | add _ _ _ ih | sub _ _ _ ih | mul _ _ _ ih =>
    exact ih.trans (Set.subset_insert _ _)

-- 读法：存在 `V`，`Integral.Build S (m + n) V` 与 `U ⊆ V` 同时成立。对 `g` 作归纳。
/-- 任意一次计算只要已备好某电路所需的输入，就可在其后重放该电路。

英文原文：Replay a circuit after any computation making its inputs available.
-/
private theorem Integral.Build.append (h : Integral.Build S m T) (g : Integral.Build T' n U) (ht : T' ⊆ T) :
    ∃ V, Integral.Build S (m + n) V ∧ U ⊆ V := by
  induction g with
  | nil => exact ⟨T, h, ht⟩
  | add _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.add (hv hx) (hv hy), Set.insert_subset_insert hv⟩
  | sub _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.sub (hv hx) (hv hy), Set.insert_subset_insert hv⟩
  | mul _ hx hy ih =>
    obtain ⟨V, hV, hv⟩ := ih
    exact ⟨_, hV.mul (hv hx) (hv hy), Set.insert_subset_insert hv⟩

-- 读法：`CanMake` 表示以下条件：存在 `c ≤ m`，存在 `U`，`Integral.Build S c U` 与 `T ⊆ U` 同时成立。
/-- 对计算出一组值所需的成本给出上界。寄存器中还可以保留额外的中间值。

英文原文：A cost bound on producing a set of values. The registers may contain
additional intermediate values.
-/
def CanMake (S : Set K) (m : ℕ) (T : Set K) : Prop :=
  ∃ c ≤ m, ∃ U, Integral.Build S c U ∧ T ⊆ U

namespace CanMake

-- 读法：要证明的命题是 `CanMake S 0 T`。
theorem of_subset (h : T ⊆ S) : CanMake S 0 T :=
  ⟨0, le_rfl, S, .nil, h⟩

-- 读法：要证明的命题是 `CanMake S n T`。
theorem mono_cost (h : CanMake S m T) (hc : m ≤ n) : CanMake S n T := by
  obtain ⟨c, hc', V, hv, ht⟩ := h
  exact ⟨c, hc'.trans hc, V, hv, ht⟩

-- 读法：要证明的命题是 `CanMake S m T'`。
theorem mono_output (h : CanMake S m T) (ht : T' ⊆ T) : CanMake S m T' := by
  obtain ⟨c, hc, V, hv, ht'⟩ := h
  exact ⟨c, hc, V, hv, ht.trans ht'⟩

-- 读法：要证明的命题是 `CanMake S (m + n) U`。
theorem trans (h : CanMake S m T) (g : CanMake T n U) : CanMake S (m + n) U := by
  obtain ⟨a, ha, A, hA, hT⟩ := h
  obtain ⟨b, hb, B, hB, hU⟩ := g
  obtain ⟨V, hV, hv⟩ := hA.append hB hT
  exact ⟨a + b, Nat.add_le_add ha hb, V, hV, hU.trans hv⟩

-- 读法：要证明的命题是 `CanMake S' m T`。这里调用 `of_subset`。
theorem mono_input (h : CanMake S m T) (hs : S ⊆ S') : CanMake S' m T := by
  simpa using (of_subset hs).trans h

-- 读法：要证明的命题是 `CanMake S m (S ∪ T)`。
theorem keep (h : CanMake S m T) : CanMake S m (S ∪ T) := by
  obtain ⟨c, hc, V, hv, ht⟩ := h
  exact ⟨c, hc, V, hv, Set.union_subset hv.retains ht⟩

-- 读法：要证明的命题是 `CanMake S (m + n) (T ∪ U)`。这里调用 `h.keep.trans`。
theorem union (h : CanMake S m T) (g : CanMake S n U) : CanMake S (m + n) (T ∪ U) := by
  have g' : CanMake (S ∪ T) n U := g.mono_input Set.subset_union_left
  exact (h.keep.trans g'.keep).mono_output (Set.union_subset_union_left U Set.subset_union_right)

-- 读法：要证明的命题是 `CanMake S (Fintype.card ι * m) (⋃ i, T i)`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
theorem iUnion {ι : Type*} [Fintype ι] {T : ι → Set K}
    (h : ∀ i, CanMake S m (T i)) : CanMake S (Fintype.card ι * m) (⋃ i, T i) := by
  classical
  have aux (s : Finset ι) : CanMake S (s.card * m) (⋃ i ∈ s, T i) := by
    induction s using Finset.induction_on with
    | empty => simpa using of_subset (Set.empty_subset S)
    | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, add_comm]
      simpa using (h i).union ih
  simpa using aux Finset.univ

-- 读法：要证明的命题是 `CanMake S (Fintype.card ι * m) (Set.range f)`。这里调用 `Set.mem_iUnion_of_mem`。
theorem range {ι : Type*} [Fintype ι] {f : ι → K}
    (h : ∀ i, CanMake S m {f i}) : CanMake S (Fintype.card ι * m) (Set.range f) := by
  refine (iUnion h).mono_output ?_
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion_of_mem i rfl

-- 读法：要证明的命题是 `CanMake S 1 {x * y}`。
theorem mul {x y : K} (hx : x ∈ S) (hy : y ∈ S) : CanMake S 1 {x * y} :=
  ⟨1, le_rfl, _, Integral.Build.nil.mul hx hy, Set.singleton_subset_iff.mpr (Set.mem_insert _ _)⟩

-- 读法：要证明的命题是 `CanMake S 1 {x + y}`。
theorem add {x y : K} (hx : x ∈ S) (hy : y ∈ S) : CanMake S 1 {x + y} :=
  ⟨1, le_rfl, _, Integral.Build.nil.add hx hy, Set.singleton_subset_iff.mpr (Set.mem_insert _ _)⟩

-- 读法：要证明的命题是 `CanMake S (Fintype.card ι * 2) {∑ i, a i * x i}`。对 `s` 作归纳，采用 `Finset.induction_on` 的归纳原则。
/-- 每个项只需两次运算，第一次将该项加到零上的加法也已计入。

英文原文：Two operations per term suffice, including the first addition to zero.
-/
theorem linear {ι : Type*} [Fintype ι] {a x : ι → K}
    (h0 : 0 ∈ S) (ha : ∀ i, a i ∈ S) (hx : ∀ i, x i ∈ S) :
    CanMake S (Fintype.card ι * 2) {∑ i, a i * x i} := by
  classical
  have aux (s : Finset ι) : CanMake S (s.card * 2) {∑ i ∈ s, a i * x i} := by
    induction s using Finset.induction_on with
    | empty => simpa using of_subset (Set.singleton_subset_iff.mpr h0)
    | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Finset.sum_insert hi]
      exact (ih.union (mul (ha i) (hx i))).trans (add (Or.inr rfl) (Or.inl rfl))
  exact aux Finset.univ

end CanMake
end OAI.LinearAlgebra.MatrixExponent
