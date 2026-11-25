-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense

/-!
# 对活跃原子与局部连线区段编码

关闭未使用的原子槽位。未使用的隐藏槽位宽度为零；若将其视为未使用但仍有正宽度的连线，就会使收缩结果多乘上一个二的幂。

**英文原文**

Encoding the active atoms and local wire spans

Unused atom slots are turned off. Unused hidden slots have zero
width. Counting them as unused but positive-width wires would
multiply a contraction by an unwanted power of two.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Classical Coloring

-- 读法：结构的字段包括 `tag`、`width`、`ptr`。
structure Packed (A T : Type) (e l s d : ℕ) where
  tag : A → B l
  width : T → B d
  ptr : A → B s → (B e ⊕ T) × B d

namespace Packed
variable {A T F : Type} {m e l s d : ℕ}
  (p : Packed A T e l s d) (g : A ↪ B m) (f : T ↪ B e)

-- 读法：`link` 的取值由 `(r.1.isRight, Sum.elim id f r.1, r.2)` 给出。
def link (r : (B e ⊕ T) × B d) : (pointer e d).obj :=
  (r.1.isRight, Sum.elim id f r.1, r.2)

-- 读法：`encode` 的结果类型为 `(code m e l s d).obj`。
def encode : (code m e l s d).obj :=
  (Function.extend f p.width (fun _ => 0),
   Function.extend g (fun i => (true, p.tag i, link f ∘ p.ptr i))
     (fun _ => (false, 0, fun _ => (false, 0, 0))))

-- 读法：`((p.encode g f).2 (g i))` 等于 `(true, p.tag i, link f ∘ p.ptr i)`。
theorem store (i : A) :
    ((p.encode g f).2 (g i)) = (true, p.tag i, link f ∘ p.ptr i) :=
  by simp only [encode, g.injective.extend_apply]

-- 读法：`atoms` 的结果类型为 `A ≃ Menu.Atom (p.encode g f)`。
def atoms : A ≃ Menu.Atom (p.encode g f) := Equiv.ofBijective
  (fun i => ⟨g i, by rw [store]⟩) ⟨fun _ _ h => g.injective (congrArg Subtype.val h), by
    rintro ⟨j, hj⟩
    by_cases he : j ∈ Set.range g
    · obtain ⟨i, rfl⟩ := he
      exact ⟨i, rfl⟩
    · simp only [encode] at hj
      rw [Function.extend_apply' _ _ _ he] at hj
      cases hj⟩

-- 读法：`Menu.label (p.encode g f) (p.atoms g f i)` 等于 `p.tag i`。
@[simp] theorem tag_eq (i : A) : Menu.label (p.encode g f) (p.atoms g f i) = p.tag i :=
  congrArg (fun a => a.2.1) (p.store g f i)

-- 读法：`Menu.ref (p.encode g f) (p.atoms g f i) j` 等于 `link f (p.ptr i j)`。
@[simp] theorem ref_eq (i : A) (j : B s) :
    Menu.ref (p.encode g f) (p.atoms g f i) j = link f (p.ptr i j) :=
  congrArg (fun a => a.2.2 j) (p.store g f i)

variable (M : Menu F l s d) (w : B e → ℕ)

-- 读法：在后续公式中，`Inner` 是 `Σ t : T, Fin (M.length (p.width t))` 的缩写。
abbrev Inner := Σ t : T, Fin (M.length (p.width t))

-- 读法：`M.hidden (p.encode g f) (f t)` 等于 `M.length (p.width t)`。
@[simp] theorem hidden_eq (t : T) :
    M.hidden (p.encode g f) (f t) = M.length (p.width t) :=
  by simp only [Menu.hidden, encode, f.injective.extend_apply]

-- 读法：`inner` 的结果类型为 `p.Inner M ≃ Positions (M.hidden (p.encode g f))`。
def inner (h₀ : M.length 0 = 0) : p.Inner M ≃ Positions (M.hidden (p.encode g f)) :=
  Equiv.ofBijective (fun t => ⟨f t.1, (t.2.cast (p.hidden_eq g f M t.1).symm)⟩) ⟨by
    rintro ⟨i, n⟩ ⟨j, r⟩ h
    have hi : i = j := f.injective (congrArg Sigma.fst h)
    subst j
    have hr : n.val = r.val := congrArg (fun x => x.2.val) h
    rw [Fin.ext hr], by
    rintro ⟨j, r⟩
    by_cases he : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := he
      exact ⟨⟨i, r.cast (p.hidden_eq g f M i)⟩, rfl⟩
    · have ht : M.hidden (p.encode g f) j = 0 := by
        simp only [Menu.hidden, encode]
        rw [Function.extend_apply' _ _ _ he, h₀]
      exact (Fin.elim0 (r.cast ht))⟩

-- 读法：`cap` 的取值由 `Sum.elim w (M.length ∘ p.width) r.1` 给出。
def cap (r : (B e ⊕ T) × B d) := Sum.elim w (M.length ∘ p.width) r.1

-- 读法：`M.capacity w (p.encode g f) (link f r)` 等于 `p.cap M w r`。这里调用 `p.hidden_eq`。
theorem cap_eq (r : (B e ⊕ T) × B d) :
    M.capacity w (p.encode g f) (link f r) = p.cap M w r := by
  rcases r with ⟨i|t, x⟩
  · rfl
  · exact p.hidden_eq g f M t

-- 读法：`Fits` 的取值由 `∀ i j (t : Fin (M.width (p.tag i) j)), M.length (p.ptr i j).2 + t.val < p.cap M w (p.ptr i j)` 给出。
def Fits := ∀ i j (t : Fin (M.width (p.tag i) j)),
  M.length (p.ptr i j).2 + t.val < p.cap M w (p.ptr i j)

-- 读法：要证明的命题是 `M.Fits w (p.encode g f)`。
theorem fits_code (h : p.Fits M w) : M.Fits w (p.encode g f) := by
  intro i
  obtain ⟨t, rfl⟩ := (p.atoms g f).surjective i
  intro j
  rw [tag_eq, ref_eq, cap_eq]
  exact h t j

-- 读法：`resolve` 的取值由 `match r with | (.inl b, _) => .inl ⟨b, i⟩ | (.inr t, _) => .inr ⟨t, i⟩` 给出。
def resolve (r : (B e ⊕ T) × B d) (i : Fin (p.cap M w r)) : Positions w ⊕ p.Inner M :=
  match r with
  | (.inl b, _) => .inl ⟨b, i⟩
  | (.inr t, _) => .inr ⟨t, i⟩

-- 读法：`M.resolve w (p.encode g f) (link f r) (i.cast (p.cap_eq g f M w r).symm)` 等于 `(p.resolve M w r i).map id (p.inner g f M h₀)`。
theorem resolve_eq (h₀ : M.length 0 = 0) (r : (B e ⊕ T) × B d)
    (i : Fin (p.cap M w r)) :
    M.resolve w (p.encode g f) (link f r) (i.cast (p.cap_eq g f M w r).symm) =
      (p.resolve M w r i).map id (p.inner g f M h₀) := by
  rcases r with ⟨b|t, x⟩ <;> rfl

variable [Fintype A] [Fintype T]

-- 读法：用字段 `A`、`E`、`I`、`value` 构造 `History F (Positions w)`。
def history (h : p.Fits M w) : History F (Positions w) where
  A := A
  E := p.Inner M
  I i := Positions (M.width (p.tag i))
  value i := M.value (p.tag i)
  read i t := p.resolve M w (p.ptr i t.1) ⟨_, h i t.1 t.2⟩

-- 读法：`M.value a x` 等于 `M.value b y`。
private theorem value_congr {a b : B l} (he : a = b)
    {x : Positions (M.width a) → Bool} {y : Positions (M.width b) → Bool}
    (h : ∀ j t, x ⟨j, t⟩ = y ⟨j, t.cast (congrArg (fun a => M.width a j) he)⟩) :
    M.value a x = M.value b y := by
  subst b
  exact congrArg _ (funext (fun ⟨j, t⟩ => h j t))

omit [Fintype A] [Fintype T] in
-- 读法：`M.resolve w (p.encode g f) i v` 等于 `M.resolve w (p.encode g f) j u`。
private theorem resolve_congr {i j : (pointer e d).obj} (he : i = j)
    {v : Fin (M.capacity w (p.encode g f) i)} {u : Fin (M.capacity w (p.encode g f) j)}
    (hv : v.val = u.val) :
    M.resolve w (p.encode g f) i v = M.resolve w (p.encode g f) j u := by
  subst j
  rw [Fin.ext hv]

-- 读法：`U.eval x` 等于 `V.eval x`。这里调用 `Fintype.sum_equiv`。
private theorem eval_equiv [Field F] {X : Type} (U V : History F X)
    (a : U.A ≃ V.A) (t : U.E ≃ V.E) (x : X → Bool)
    (h : ∀ z i, U.value i (Sum.elim x z ∘ U.read i) =
      V.value (a i) (Sum.elim x (z ∘ t.symm) ∘ V.read (a i))) :
    U.eval x = V.eval x := by
  unfold eval
  apply Fintype.sum_equiv (t.arrowCongr (Equiv.refl Bool))
  intro z
  exact Fintype.prod_equiv a _ _ (h z)

-- 读法：`M.decode w (p.encode g f) x` 等于 `(p.history M w h).eval x`。这里调用 `value_congr`。
theorem decode [Field F] (h₀ : M.length 0 = 0) (h : p.Fits M w) (x : Positions w → Bool) :
    M.decode w (p.encode g f) x = (p.history M w h).eval x := by
  let c := p.encode g f
  let e := p.inner g f M h₀
  let hc := p.fits_code g f M w h
  rw [Menu.decode, dite_eq_left hc]
  symm
  refine eval_equiv (p.history M w h) (M.history w c hc) (p.atoms g f) e x ?_
  intro z i
  apply value_congr M (p.tag_eq g f i).symm
  intro j t
  let r := p.ptr i j
  let q : Fin (p.cap M w r) := ⟨_, h i j t⟩
  let u := Menu.ref c (p.atoms g f i) j
  -- 推导：记下中间结论 `hu`：`u = link f r`。
  have hu : u = link f r := p.ref_eq g f i j
  let k := t.cast (congrArg (fun a => M.width a j) (p.tag_eq g f i).symm)
  let o : Fin (M.capacity w c u) := ⟨_, hc (p.atoms g f i) j k⟩
  have ho : M.resolve w c u o = (p.resolve M w r q).map id e := by
    rw [← p.resolve_eq g f M w h₀]
    apply p.resolve_congr g f M w hu
    change M.length u.2.2 + t.val = M.length r.2 + t.val
    rw [hu]; rfl
  change Sum.elim x z (p.resolve M w r q) =
    Sum.elim x (z ∘ e.symm) (M.resolve w c u o)
  rw [ho]
  cases p.resolve M w r q with
  | inl a => rfl
  | inr a => exact (congrArg z (e.symm_apply_apply a)).symm

end Packed
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# 异构原子因子的共同选项表

不同类型的区段共用一个地址空间，描述中不存放标量系数数组。给定标签后，区段的宽度及其比特所决定的函数便同时确定。

**英文原文**

A common menu for heterogeneous atomic factors

Spans of different types share one address space. The description
contains no array of scalar coefficients. A label fixes both the
span widths and the function of their bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring Classical

-- 读法：结构的字段包括 `Span`、`width`、`weight`。
structure Atom (F : Type) where
  Span : Type
  width : Span → ℕ
  weight : ((j : Span) → Fin (width j) → Bool) → F

variable {F : Type} {s l d : ℕ}

-- 读法：结构的字段包括 `width`、`weight`。
structure Entry (F : Type) (s : ℕ) where
  width : B s → ℕ
  weight : (Positions width → Bool) → F

-- 读法：用字段 `width`、`weight` 构造 `Entry F s`。
def Atom.pack (a : Atom F) (index : a.Span ↪ B s) : Entry F s where
  width := Function.extend index a.width (fun _ => 0)
  weight x := a.weight fun j t => x ⟨index j, t.cast (index.injective.extend_apply _ _ _).symm⟩

-- 读法：`Entry.eval` 的取值由 `e.weight fun j => x j.1 j.2.val` 给出。
def Entry.eval (e : Entry F s) (x : B s → ℕ → Bool) := e.weight fun j => x j.1 j.2.val

-- 读法：`(a.pack index).eval x` 等于 `a.weight (fun j t => x (index j) t.val)`。两端由定义化简为同一项。
theorem Atom.eval_pack (a : Atom F) (index : a.Span ↪ B s) (x : B s → ℕ → Bool) :
    (a.pack index).eval x = a.weight (fun j t => x (index j) t.val) := rfl

variable {L : Type} [Field F] (a : L → Atom F)
    (names : L ↪ B l) (index : ∀ i, (a i).Span ↪ B s) (len : B d → ℕ)

-- 读法：`entries` 的取值由 `Function.extend names (fun i => (a i).pack (index i)) (fun _ => (⟨fun _ => 0, fun _ => 1⟩ : Entry F s))` 给出。
private def entries := Function.extend names (fun i => (a i).pack (index i))
  (fun _ => (⟨fun _ => 0, fun _ => 1⟩ : Entry F s))

-- 读法：用字段 `width`、`value`、`length` 构造 `Menu F l s d`。
def menu : Menu F l s d where
  width i := (entries a names index i).width
  value i := (entries a names index i).weight
  length := len

-- 读法：`(menu a names index len).width (names i) (index i j)` 等于 `(a i).width j`。
theorem menu_width (i : L) (j : (a i).Span) :
    (menu a names index len).width (names i) (index i j) = (a i).width j := by
  simp only [menu, entries, names.injective.extend_apply, Atom.pack, (index i).injective.extend_apply]

-- 读法：`(menu a names index len).width (names i) j` 等于 `0`。这里调用 `Function.extend_apply'`。
theorem menu_empty (i : L) (j : B s) (hj : j ∉ Set.range (index i)) :
    (menu a names index len).width (names i) j = 0 := by
  simp only [menu, entries, names.injective.extend_apply, Atom.pack]
  exact Function.extend_apply' _ _ _ hj

-- 读法：`(menu a names index len).value (names i) (fun j => x j.1 j.2.val)` 等于 `(a i).weight (fun j t => x (index i j) t.val)`。
theorem menu_value (i : L) (x : B s → ℕ → Bool) :
    (menu a names index len).value (names i) (fun j => x j.1 j.2.val) =
      (a i).weight (fun j t => x (index i j) t.val) := by
  change (entries a names index (names i)).eval x = _
  rw [entries, names.injective.extend_apply, Atom.eval_pack]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end
