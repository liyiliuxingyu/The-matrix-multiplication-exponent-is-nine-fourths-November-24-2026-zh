-- 本文件所属证明环节：用有限有向多重图表示带端口的比特张量网络，证明细分、重编号、替换及取幂对张量收缩和规模的影响。
import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# 重新索引每条连线的位置

外部位置的任意双射都可通过结构性重接线实现。逐个取出所需比特，同时追踪其余全部比特的位置。

**英文原文**

Reindexing individual wire positions

An arbitrary bijection of the exterior positions is a structural rewiring.
We pull out the requested bits one at a time, keeping track of the positions
of all remaining bits.
-/

namespace OAI.LinearAlgebra.MatrixExponent

-- 读法：在后续公式中，`slots` 是 `| .bit => Unit | .unit => Empty | .pair a b => slots a ⊕ slots b` 的缩写。
abbrev slots : Wire → Type
  | .bit => Unit
  | .unit => Empty
  | .pair a b => slots a ⊕ slots b

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
instance slotsFintype : (a : Wire) → Fintype (slots a)
  | .bit => inferInstanceAs (Fintype Unit)
  | .unit => inferInstanceAs (Fintype Empty)
  | .pair a b =>
    letI := slotsFintype a
    letI := slotsFintype b
    inferInstanceAs (Fintype (slots a ⊕ slots b))

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
instance slotsDecidableEq : (a : Wire) → DecidableEq (slots a)
  | .bit => inferInstanceAs (DecidableEq Unit)
  | .unit => inferInstanceAs (DecidableEq Empty)
  | .pair a b =>
    letI := slotsDecidableEq a
    letI := slotsDecidableEq b
    inferInstanceAs (DecidableEq (slots a ⊕ slots b))

-- 读法：`Fintype.card (slots a)` 等于 `wd a`。对 `a` 作归纳。
@[simp] theorem card_slots (a : Wire) : Fintype.card (slots a) = wd a := by
  induction a with
  | bit => rfl
  | unit => rfl
  | pair a b ha hb => simpa [slots, wd] using congrArg₂ (· + ·) ha hb

-- 读法：逐一匹配以下输入模式：`.bit`、`.unit`、`.pair a b`。
def bits : (a : Wire) → Val a ≃ (slots a → Bool)
  | .bit => ⟨fun x _ => x, fun f => f (), fun _ => rfl, fun _ => rfl⟩
  | .unit => ⟨fun _ => Empty.elim, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim⟩
  | .pair a b => ((bits a).prodCongr (bits b)).trans
      (Equiv.sumPiEquivProdPi (fun _ : slots a ⊕ slots b => Bool)).symm

variable {a b : Wire}

-- 读法：`reindex` 的取值由 `(bits b).symm (fun i => bits a x (e i))` 给出。
def reindex (e : slots b ≃ slots a) (x : Val a) : Val b :=
  (bits b).symm (fun i => bits a x (e i))

-- 读法：`bits b (reindex e x) i` 等于 `bits a x (e i)`。
@[simp] theorem bits_reindex (e : slots b ≃ slots a) (x : Val a) (i : slots b) :
    bits b (reindex e x) i = bits a x (e i) :=
  congrFun ((bits b).apply_symm_apply _) i

-- 读法：对 `a` 作归纳。
private theorem pluck (a : Wire) (i : slots a) :
    ∃ (b : Wire) (e : Unit ⊕ slots b ≃ slots a) (f : Val a → Val (.pair .bit b)),
      Rewire a (.pair .bit b) f ∧ e (.inl ()) = i ∧
        ∀ x j, bits (.pair .bit b) (f x) j = bits a x (e j) := by
  induction a with
  | bit =>
    refine ⟨.unit, Equiv.sumEmpty Unit Empty, _, .unit' _, rfl, ?_⟩
    intro x j
    cases j with
    | inl => rfl
    | inr k => exact k.elim
  | unit => exact i.elim
  | pair a b ha hb =>
    cases i with
    | inl i =>
      -- 推导：从 `ha i` 中取出 `c, e, f, hf, hi, he`。
      obtain ⟨c, e, f, hf, hi, he⟩ := ha i
      refine ⟨.pair c b, (Equiv.sumAssoc _ _ _).symm.trans (e.sumCongr (.refl _)),
        _, (hf.par (.id b)).comp (.assoc _ _ _), congrArg Sum.inl hi, ?_⟩
      rintro x (j | j | j)
      · exact he x.1 (.inl j)
      · exact he x.1 (.inr j)
      · rfl
    | inr i =>
      obtain ⟨c, e, f, hf, hi, he⟩ := hb i
      refine ⟨.pair c a, ((Equiv.sumAssoc _ _ _).symm.trans (e.sumCongr (.refl _))).trans
          (Equiv.sumComm _ _), _, (Rewire.swap a b).comp ((hf.par (.id a)).comp (.assoc _ _ _)),
        congrArg Sum.inr hi, ?_⟩
      rintro x (j | j | j)
      · exact he x.2 (.inl j)
      · exact he x.2 (.inr j)
      · rfl

-- 读法：存在 `q : α ≃ β`，对每个 `i`，`d (.inr (q i))` 等于 `e (.inr i)`。
private theorem matchRest {α β γ : Type} (e : Unit ⊕ α ≃ γ) (d : Unit ⊕ β ≃ γ)
    (h : d (.inl ()) = e (.inl ())) :
    ∃ q : α ≃ β, ∀ i, d (.inr (q i)) = e (.inr i) := by
  have ex (i : α) : ∃ j : β, d (.inr j) = e (.inr i) := by
    obtain ⟨_ | j, hj⟩ := d.surjective (e (.inr i))
    · cases e.injective (h.symm.trans hj)
    · exact ⟨j, hj⟩
  choose q hq using ex
  have bij : Function.Bijective q := by
    constructor
    · intro i j hij
      apply Sum.inr.inj
      apply e.injective
      rw [← hq, ← hq, hij]
    · intro j
      -- 推导：从 `e.surjective (d (.inr j))` 中取出 `_ | i, hi`。
      obtain ⟨_ | i, hi⟩ := e.surjective (d (.inr j))
      · cases d.injective (h.trans hi)
      · exact ⟨i, Sum.inr.inj (d.injective ((hq i).trans hi))⟩
  exact ⟨Equiv.ofBijective q bij, hq⟩

-- 读法：存在 `(c : Wire) (q : α ≃ slots c) (f : Val a → Val (.pair b c))`，`Rewire a (.pair b c) f` 与 `(∀ x i, bits b (f x).1 i = bits a x (e (.inl i))) ∧ (∀ x i, bits c (f x).2 (q i) = bits a x (e (.inr i)))` 同时成立。
/-- 提取指定的线束，同时保留以 `α` 为索引的其余位置。

英文原文：Extract the requested bundle, retaining the remaining positions indexed by `α`.
-/
private theorem extract (b : Wire) {a : Wire} {α : Type} (e : slots b ⊕ α ≃ slots a) :
    ∃ (c : Wire) (q : α ≃ slots c) (f : Val a → Val (.pair b c)),
      Rewire a (.pair b c) f ∧
      (∀ x i, bits b (f x).1 i = bits a x (e (.inl i))) ∧
      (∀ x i, bits c (f x).2 (q i) = bits a x (e (.inr i))) := by
  induction b generalizing a α with
  | unit =>
    exact ⟨a, (Equiv.emptySum Empty α).symm.trans e, _, (Rewire.unit' a).comp (.swap _ _),
      fun _ i => i.elim, fun _ _ => rfl⟩
  | bit =>
    -- 推导：从 `pluck a (e (.inl ()))` 中取出 `c, d, f, hf, hi, hd`。
    obtain ⟨c, d, f, hf, hi, hd⟩ := pluck a (e (.inl ()))
    obtain ⟨q, hq⟩ := matchRest e d hi
    exact ⟨c, q, f, hf, fun x i => (hd x (.inl i)).trans (congrArg (bits a x) hi),
      fun x i => (hd x (.inr (q i))).trans (congrArg (bits a x) (hq i))⟩
  | pair b c hb hc =>
    obtain ⟨d, p, f, hf, hf₁, hf₂⟩ := hb ((Equiv.sumAssoc _ _ _).symm.trans e)
    obtain ⟨g, q, k, hk, hk₁, hk₂⟩ := hc p
    refine ⟨g, q, _, (hf.comp ((Rewire.id b).par hk)).comp (.assoc' _ _ _), ?_, ?_⟩
    · rintro x (i | i)
      · exact hf₁ x i
      · exact (hk₁ (f x).2 i).trans (hf₂ x (.inl i))
    · exact fun x i => (hk₂ (f x).2 i).trans (hf₂ x (.inr i))

-- 读法：仅通过重新接线，从格式 `a` 变换到 `.unit`，实现映射 `(fun _ => ())`。对 `a` 作归纳。
private theorem empty_rewire (a : Wire) (h : slots a → Empty) :
    Rewire a .unit (fun _ => ()) := by
  induction a with
  | bit => exact (h ()).elim
  | unit => exact .id _
  | pair a b ha hb => exact ((ha (h ∘ Sum.inl)).par (hb (h ∘ Sum.inr))).comp (.unit _)

-- 读法：仅通过重新接线，从格式 `a` 变换到 `b`，实现映射 `(reindex e)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem rewire_reindex (e : slots b ≃ slots a) : Rewire a b (reindex e) := by
  obtain ⟨c, q, f, hf, hi, _⟩ := extract b ((Equiv.sumEmpty _ Empty).trans e)
  have he : reindex e = fun x => (f x).1 := by
    funext x
    apply (bits b).injective
    funext i
    rw [bits_reindex]
    exact (hi x i).symm
  rw [he]
  exact (hf.comp ((Rewire.id b).par (empty_rewire c q.symm))).comp (.unit b)

-- 读法：存在 `f`，`Rewire a b f` 与 `Function.Injective f` 同时成立。用函数外延性比较等号两侧在 `i` 处的取值。
theorem Rewire.exists_of_width (h : wd a = wd b) :
    ∃ f, Rewire a b f ∧ Function.Injective f := by
  let e : slots b ≃ slots a := Fintype.equivOfCardEq (by simp [h])
  refine ⟨reindex e, rewire_reindex e, ?_⟩
  intro x y hxy
  apply (bits a).injective
  funext i
  simpa using congrArg (fun z => bits b z (e.symm i)) hxy

-- 读法：存在 `e : slots b ≃ slots a`，`f` 等于 `reindex e`。对 `h` 作归纳。
theorem Rewire.reindex_exists {f : Val a → Val b} (h : Rewire a b f) :
    ∃ e : slots b ≃ slots a, f = reindex e := by
  suffices ∃ e : slots b ≃ slots a, ∀ x i, bits b (f x) i = bits a x (e i) by
    obtain ⟨e, he⟩ := this
    refine ⟨e, funext fun x => (bits b).injective (funext fun i => ?_)⟩
    rw [bits_reindex, he]
  induction h with
  | id a => exact ⟨.refl _, fun _ _ => rfl⟩
  | swap a b => exact ⟨Equiv.sumComm _ _, by rintro x (i | i) <;> rfl⟩
  | assoc a b c => exact ⟨(Equiv.sumAssoc _ _ _).symm, by rintro x (i | i | i) <;> rfl⟩
  | assoc' a b c => exact ⟨Equiv.sumAssoc _ _ _, by rintro x ((i | i) | i) <;> rfl⟩
  | unit a => exact ⟨(Equiv.sumEmpty _ Empty).symm, fun _ _ => rfl⟩
  | unit' a =>
    refine ⟨Equiv.sumEmpty _ Empty, ?_⟩
    rintro x (i | i)
    · rfl
    · exact i.elim
  | comp _ _ ih ik =>
    -- 推导：从 `ih` 中取出 `e, he`。
    obtain ⟨e, he⟩ := ih
    obtain ⟨d, hd⟩ := ik
    exact ⟨d.trans e, fun x i => (hd _ i).trans (he x (d i))⟩
  | par _ _ ih ik =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨d, hd⟩ := ik
    refine ⟨e.sumCongr d, ?_⟩
    rintro x (i | i)
    · exact he x.1 i
    · exact hd x.2 i

end OAI.LinearAlgebra.MatrixExponent
