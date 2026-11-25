-- 本文件所属证明环节：研究谱点给张量、共享标签及连线赋予的价格，通过距离、测地运动、三脚架接触和同步条件获得价格约束。
import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Spectral.Extra
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport

/-!
# 由测地线上的站点确定价格

通过延拓增加站点副本，并为每一次求值给出上界。由指定的端点不等式及布塞曼凸性可知，相应副本之间的距离为零。

**英文原文**

Price determination at geodesic sites

An extension adds duplicate sites with upper bounds on every evaluation.
The prescribed endpoint inequalities and Busemann convexity identify
these duplicates up to distance zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S T U V : Type} [Field K]
  [Fintype S] [Fintype T] [Fintype U] [Fintype V]
  [DecidableEq S] [DecidableEq T] [DecidableEq U] [DecidableEq V]

-- 读法：`place f (w.map X).prod` 等于 `(w.map (fun i => place f (X i))).prod`。对 `w` 作归纳。
private theorem place_prod {I : Type*} (f : S → T) (X : I → Tensor K S) (w : List I) :
    place f (w.map X).prod = (w.map (fun i => place f (X i))).prod := by
  induction w with
  | nil => exact place_one f
  | cons i w ih => rw [List.map_cons, List.prod_cons, place_mul, ih]; rfl

variable [Nonempty S]

-- 读法：存在 `g : Tensor K ((S ⊕ V) ⊕ U) →+* ℝ`，`Monotone g` 与 `(∀ B, g (pad U B) = f B) ∧ ∀ i, g (place (Sum.map Sum.inl id) (X i)) ≤ p i` 同时成立。这里调用 `extension_iff`。
/-- 增加其他原有站点不会改变在标记站点上进行的闭包检验。

英文原文：Additional old sites do not change closure tests on the marked ones.
-/
theorem enlarge_base {I : Type*} (f : Tensor K (S ⊕ V) →+* ℝ) (hf : Monotone f)
    (X : I → Tensor K (S ⊕ U)) (p : I → ℝ)
    (ht : ∀ w : List I, ∀ B, pad U B ≤ (w.map X).prod → f (pad V B) ≤ (w.map p).prod) :
    ∃ g : Tensor K ((S ⊕ V) ⊕ U) →+* ℝ, Monotone g ∧
      (∀ B, g (pad U B) = f B) ∧ ∀ i, g (place (Sum.map Sum.inl id) (X i)) ≤ p i := by
  apply (extension_iff f hf (fun i => place (Sum.map Sum.inl id) (X i)) p).mpr
  intro w B hB
  rw [← place_prod] at hB
  obtain ⟨C, hC, hX⟩ := close_extra hB
  exact (hf hC).trans (ht w C hX)

-- 读法：`place (Sum.elim x z) (pad U A)` 等于 `place x A`。
theorem place_sum_inl (x : S → T) (z : U → T) (A : Tensor K S) :
    place (Sum.elim x z) (pad U A) = place x A := by
  rw [← place_inl, ← place_comp]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# 在有限布点上由测地线确定价格

**英文原文**

Geodesic determination on finite placements
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S T U V : Type} [Field K]
  [Fintype S] [Fintype T] [Fintype U] [Fintype V]
  [DecidableEq S] [DecidableEq T] [DecidableEq U] [DecidableEq V]
  [Nonempty S] [Nonempty T] [Nonempty V]

-- 读法：`Agree` 表示以下条件：对每个 `A`，`P (place x A)` 等于 `Q (place y A)`。
/-- 通过价格比较有限标记，允许标记重复。

英文原文：Compare possibly repeated finite markings by their prices.
-/
def Agree (P : Tensor K V → ℝ) (Q : Tensor K T → ℝ) (x : S → V) (y : S → T) : Prop :=
  ∀ A, P (place x A) = Q (place y A)

-- 读法：`gap` 的取值由 `P (wire K a b 2)` 给出。
def gap (P : Tensor K S → ℝ) (a b : S) : ℝ := P (wire K a b 2)

-- 读法：`AtFraction` 表示以下条件：`gap P a x = t * gap P a b` 与 `gap P x b = (1 - t) * gap P a b` 同时成立。
def AtFraction (P : Tensor K S → ℝ) (a x b : S) (t : ℝ) : Prop :=
  gap P a x = t * gap P a b ∧ gap P x b = (1 - t) * gap P a b

omit [Nonempty S] [Nonempty T] [Nonempty V] in
-- 读法：`gap P (x a) (x b)` 等于 `gap Q (y a) (y b)`。
theorem Agree.gap {P : Tensor K V → ℝ} {Q : Tensor K T → ℝ} {x : S → V} {y : S → T}
    (h : Agree P Q x y) (a b : S) : gap P (x a) (x b) = gap Q (y a) (y b) := by
  simpa only [Tensor.gap, place_wire] using h (wire K a b 2)

omit [Nonempty S] [Nonempty T] [Nonempty V] in
-- 读法：要证明的命题是 `Agree P Q (x ∘ e) (y ∘ e)`。
theorem Agree.comp {P : Tensor K V → ℝ} {Q : Tensor K T → ℝ} {x : S → V} {y : S → T}
    (h : Agree P Q x y) (e : U → S) : Agree P Q (x ∘ e) (y ∘ e) := by
  intro A
  rw [place_comp, place_comp, h]

-- 读法：结构的字段包括 `unit`、`nonneg`、`mono`、`sub`。
/-- 在乘积与限制下均稳定的价格上界。

英文原文：An upper bound on prices stable under products and restrictions.
-/
structure Cap (P : Tensor K S → ℝ) : Prop where
  unit : P 1 = 0
  nonneg : ∀ A, 0 ≤ P A
  mono : Monotone P
  sub : ∀ A B, P (A * B) ≤ P A + P B

omit [DecidableEq S] in
-- 读法：要证明的命题是 `Cap P`。按 `A = 0` 成立与否分情况。
theorem cap_ordinary {P : Tensor K S → ℝ} {D : ℝ} (h : P ∈ ordinary K S D) : Cap P := by
  obtain ⟨d, hd, f, hf, rfl⟩ := h
  have hi := values_nonneg hd.1 hf
  have hz : values d f 0 = 0 := by simp [values]
  refine ⟨by simp [values], hi, ?_, ?_⟩
  · intro A B h
    by_cases ha : A = 0
    · rw [ha, hz]
      exact hi B
    have hl := Real.log_le_log (zero_lt_one.trans_le (value_one_le hf ha)) (hf h)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hl (Real.log_nonneg (by norm_num))) hd.1
  · intro A B
    by_cases ha : A = 0
    · rw [ha, zero_mul, hz, zero_add]; exact hi _
    by_cases hb : B = 0
    · rw [hb, mul_zero, hz, add_zero]; exact hi _
    unfold values
    rw [map_mul, Real.log_mul (zero_lt_one.trans_le (value_one_le hf ha)).ne'
      (zero_lt_one.trans_le (value_one_le hf hb)).ne', add_div, mul_add]

omit [Nonempty S] [Nonempty T] in
-- 读法：要证明的命题是 `Cap (P ∘ Tensor.place x)`。
theorem Cap.place {P : Tensor K T → ℝ} (h : Cap P) (x : S → T) : Cap (P ∘ Tensor.place x) where
  unit := by rw [Function.comp_apply, place_one, h.unit]
  nonneg _ := h.nonneg _
  mono := h.mono.comp (place_mono x)
  sub A B := by simp only [Function.comp_apply, place_mul]; exact h.sub _ _

omit [DecidableEq S] [Nonempty S] in
-- 读法：要证明的命题是 `Cap (fun A => ∑ j, w j * P j A)`。这里调用 `Finset.sum_le_sum`。
theorem Cap.weighted {J : Type*} [Fintype J] {P : J → Tensor K S → ℝ}
    (h : ∀ j, Cap (P j)) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Cap (fun A => ∑ j, w j * P j A) where
  unit := by simp [(h _).unit]
  nonneg A := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) ((h j).nonneg A)
  mono := fun _ _ hab => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ((h j).mono hab) (hw j)
  sub A B := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => (mul_le_mul_of_nonneg_left ((h j).sub A B) (hw j)).trans_eq
      (mul_add _ _ _)

omit [DecidableEq S] in
-- 读法：`values d f A ≤ r` 与 `f A ≤ (2 : ℝ) ^ (r / d)` 等价。按 `A = 0` 成立与否分情况。
private theorem values_le {d : ℝ} (hd : 0 < d) {f : Tensor K S →+* ℝ} (hf : Monotone f)
    (A : Tensor K S) {r : ℝ} (hr : 0 ≤ r) : values d f A ≤ r ↔ f A ≤ (2 : ℝ) ^ (r / d) := by
  by_cases h : A = 0
  · simp [values, h, hr, Real.rpow_nonneg]
  have hp := zero_lt_one.trans_le (value_one_le hf h)
  have ht : 0 < (2 : ℝ) := by norm_num
  rw [values, mul_comm d, ← le_div_iff₀ hd, div_le_iff₀ (Real.log_pos (by norm_num)),
    ← Real.log_rpow ht, Real.log_le_log_iff hp (Real.rpow_pos_of_pos ht _)]

-- 读法：对每个 `A`，`P (Tensor.place (Sum.elim x p) A)` 不超过 `Q A`。
/-- 只要两个端点处的连线界能确定其各自测地线上的指定位置，次平均不等式就能传播。

英文原文：A submean inequality propagates whenever the two endpoint wire
bounds force the prescribed positions on their geodesics.
-/
theorem Cap.geodesic_le {D : ℝ} {P : Tensor K V → ℝ} (hP : P ∈ ordinary K V D)
    {Q : Tensor K (S ⊕ U) → ℝ} (hQ : Cap Q) (x : S → V) (p : U → V)
    (h : ∀ A, P (Tensor.place x A) ≤ Q (pad U A))
    (he : ∀ u, ∃ a b t, AtFraction P (x a) (p u) (x b) t ∧
      gap Q (.inl a) (.inr u) ≤ gap P (x a) (p u) ∧
      gap Q (.inr u) (.inl b) ≤ gap P (p u) (x b)) :
    ∀ A, P (Tensor.place (Sum.elim x p) A) ≤ Q A := by
  obtain ⟨d, hd, f, hf, rfl⟩ := hP
  rcases hd.1.eq_or_lt with rfl | hd
  · exact fun A => by simpa [values] using hQ.nonneg A
  let e := Sum.elim x id
  have es : Function.Surjective e := fun v => ⟨.inr v, rfl⟩
  let f' := f.comp (group e es)
  have hf' : Monotone f' := hf.comp (group_mono e es)
  let v (A : Tensor K (S ⊕ U)) := (2 : ℝ) ^ (Q A / d)
  have prod (w : List (Tensor K (S ⊕ U))) : v w.prod ≤ (w.map v).prod := by
    induction w with
    | nil => simp [v, hQ.unit]
    | cons A w ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left ih (show 0 ≤ v A by unfold v; positivity))
      unfold v
      rw [← Real.rpow_add (by norm_num), ← add_div]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (div_le_div_of_nonneg_right (hQ.sub _ _) hd.le)
  obtain ⟨k, hk, ek, hkp⟩ := enlarge_base f' hf' id v (fun w A ha => by
    rw [List.map_id] at ha
    change f (Tensor.place (Sum.elim x id) (pad V A)) ≤ _
    rw [place_sum_inl]
    exact ((values_le hd hf _ (hQ.nonneg _)).mp ((h A).trans (hQ.mono ha))).trans (prod w))
  -- 推导：记下中间结论 `L`：`S ⊕ U → (S ⊕ V) ⊕ U`。
  let L : S ⊕ U → (S ⊕ V) ⊕ U := Sum.inl ∘ Sum.map id p
  let R : S ⊕ U → (S ⊕ V) ⊕ U := Sum.map Sum.inl id
  have left (A : Tensor K (S ⊕ U)) : k (Tensor.place L A) = f (Tensor.place (Sum.elim x p) A) := by
    rw [show L = Sum.inl ∘ Sum.map id p from rfl, place_comp, place_inl, ek]
    change f (Tensor.place e (Tensor.place (Sum.map id p) A)) = _
    rw [← place_comp, show e ∘ Sum.map id p = Sum.elim x p by funext i; cases i <;> rfl]
  have dl (i j) : dist k (L i) (L j) = dist f (Sum.elim x p i) (Sum.elim x p j) := by
    unfold dist
    rw [← place_wire L, left, place_wire]
  have right (A : Tensor K (S ⊕ U)) : values d k (Tensor.place R A) ≤ Q A :=
    (values_le hd hk _ (hQ.nonneg _)).mpr (hkp A)
  have dr (i j) : d * dist k (R i) (R j) ≤ gap Q i j := by
    have H := right (wire K i j 2)
    rw [place_wire] at H
    exact H
  -- 推导：记下中间结论 `same`：`∀ i, dist k (L i) (R i) = 0`。
  have same : ∀ i, dist k (L i) (R i) = 0 := by
    rintro (s | u)
    · exact dist_self _ _
    obtain ⟨a, b, t, hp, hq, hq'⟩ := he u
    have key {z w u : ℝ} (h : d * z = u * (d * w)) : z = u * w := by
      rw [mul_left_comm u] at h
      exact mul_left_cancel₀ hd.ne' h
    have hm : Between f (x a) (p u) (x b) t := ⟨key hp.1, key hp.2⟩
    have hx : Between k (L (.inl a)) (L (.inr u)) (L (.inl b)) t := by
      simpa only [Between, dl, Sum.elim_inl, Sum.elim_inr] using hm
    have hy : Between k (L (.inl a)) (R (.inr u)) (L (.inl b)) t := by
      apply between_of_le k hk
      · rw [dl]
        have hh : d * _ ≤ d * dist f (x a) (p u) := (dr (.inl a) (.inr u)).trans hq
        exact (le_of_mul_le_mul_left hh hd).trans_eq hm.1
      · rw [dl]
        have hh : d * _ ≤ d * dist f (p u) (x b) := (dr (.inr u) (.inl b)).trans hq'
        exact (le_of_mul_le_mul_left hh hd).trans_eq hm.2
    have H := busemann k hk hx.1 hx.2 hy.1 hy.2
    rw [dist_self, dist_self, mul_zero, mul_zero, add_zero] at H
    exact le_antisymm H (dist_nonneg _ hk _ _)
  intro A
  unfold values
  rw [← left, price_place_eq k hk L R same]
  exact right A

-- 读法：`P (place (Sum.elim x p) A)` 不超过 `Q (place (Sum.elim y q) A)`。这里调用 `Cap.geodesic_le`。
private theorem determine_le {D E : ℝ} {P : Tensor K V → ℝ} {Q : Tensor K T → ℝ}
    (hP : P ∈ ordinary K V D) (hQ : Q ∈ ordinary K T E)
    {x : S → V} {y : S → T} (h : Agree P Q x y)
    (p : U → V) (q : U → T) (a b : U → S) (t : U → ℝ)
    (hp : ∀ i, AtFraction P (x (a i)) (p i) (x (b i)) (t i))
    (hq : ∀ i, AtFraction Q (y (a i)) (q i) (y (b i)) (t i))
    (A : Tensor K (S ⊕ U)) : P (place (Sum.elim x p) A) ≤ Q (place (Sum.elim y q) A) := by
  apply Cap.geodesic_le hP ((cap_ordinary hQ).place (Sum.elim y q)) x p
  · intro B
    rw [Function.comp_apply, place_sum_inl, h]
  · intro i
    refine ⟨a i, b i, t i, hp i, ?_, ?_⟩
    · rw [gap, Function.comp_apply, place_wire]
      exact ((hq i).1.trans ((congrArg _ (h.gap _ _).symm).trans (hp i).1.symm)).le
    · rw [gap, Function.comp_apply, place_wire]
      exact ((hq i).2.trans ((congrArg _ (h.gap _ _).symm).trans (hp i).2.symm)).le

-- 读法：要证明的命题是 `Agree P Q (Sum.elim x p) (Sum.elim y q)`。
/-- 尺度可以不同，原有站点也无需穷尽任一外围布点。可以在参数不同的位置添加中间点。

英文原文：The scales may differ, and the old sites need not exhaust either ambient
placement. Intermediate points can be added at different parameters.
-/
theorem Agree.extend {D E : ℝ} {P : Tensor K V → ℝ} {Q : Tensor K T → ℝ}
    {x : S → V} {y : S → T} (h : Agree P Q x y)
    (hP : P ∈ ordinary K V D) (hQ : Q ∈ ordinary K T E)
    (p : U → V) (q : U → T) (a b : U → S) (t : U → ℝ)
    (hp : ∀ i, AtFraction P (x (a i)) (p i) (x (b i)) (t i))
    (hq : ∀ i, AtFraction Q (y (a i)) (q i) (y (b i)) (t i)) :
    Agree P Q (Sum.elim x p) (Sum.elim y q) := fun A =>
  le_antisymm (determine_le hP hQ h p q a b t hp hq A)
    (determine_le hQ hP (fun B => (h B).symm) q p a b t hq hp A)

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# 有限测地表达式的求值

**英文原文**

Evaluations of finite geodesic expressions
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Tensor

variable {K S T V : Type} [Field K] [Fintype T] [DecidableEq T]

-- 读法：逐一匹配以下输入模式：`.mark _`、`.seg u a b`。
/-- 在 e 指名的站点上的相容求值，这里限制到一个表达式及其所有子表达式。

英文原文：A consistent evaluation at the sites named by e, restricted to one
term and all its subterms.
-/
def Fits (P : Tensor K T → ℝ) (e : Term S → T) : Term S → Prop
  | .mark _ => True
  | .seg u a b => Fits P e a ∧ Fits P e b ∧ AtFraction P (e a) (e (.seg u a b)) (e b) u

-- 读法：`{P : Tensor K T → ℝ | Fits P e a}` 是闭集。对 `a` 作归纳。
theorem closed_fits (e : Term S → T) (a : Term S) :
    IsClosed {P : Tensor K T → ℝ | Fits P e a} := by
  induction a with
  | mark => exact isClosed_univ
  | seg u a b ha hb =>
    have h (i j : T) : Continuous (fun P : Tensor K T → ℝ => gap P i j) :=
      continuous_apply (wire K i j 2)
    exact ha.inter (hb.inter ((isClosed_eq (h _ _) (continuous_const.mul (h _ _))).inter
      (isClosed_eq (h _ _) (continuous_const.mul (h _ _)))))

variable [Fintype V] [DecidableEq V] [Nonempty T] [Nonempty V]
variable {P : Tensor K T → ℝ} {Q : Tensor K V → ℝ} {D E : ℝ}
    {p : Term S → T} {q : Term S → V}

-- 读法：`snoc` 的取值由 `Sum.elim x (fun _ => z)` 给出。
private def snoc {X Y : Type} (x : X → Y) (z : Y) : X ⊕ Unit → Y := Sum.elim x (fun _ => z)

-- 读法：对 `a` 作归纳。
private theorem append_term (hP : P ∈ ordinary K T D) (hQ : Q ∈ ordinary K V E)
    (a : Term S) (hp : Fits P p a) (hq : Fits Q q a) :
    ∀ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (x : X → T) (y : X → V)
      (m : S → X), (∀ i, x (m i) = p (.mark i)) → (∀ i, y (m i) = q (.mark i)) →
      Agree P Q x y → Agree P Q (snoc x (p a)) (snoc y (q a)) := by
  induction a with
  | mark i =>
    intro X _ _ _ x y m hx hy h
    let e := snoc id (m i)
    have he : x ∘ e = snoc x (p (.mark i)) := by
      funext z; cases z
      · rfl
      · exact hx i
    -- 推导：记下中间结论 `he'`：`y ∘ e = snoc y (q (.mark i))`。
    have he' : y ∘ e = snoc y (q (.mark i)) := by
      funext z; cases z
      · rfl
      · exact hy i
    rw [← he, ← he']
    exact h.comp e
  | seg u a b ha hb =>
    intro X _ _ _ x y m hx hy h
    have ha' := ha hp.1 hq.1 x y m hx hy h
    have hb' := hb hp.2.1 hq.2.1 _ _ (Sum.inl ∘ m) hx hy ha'
    have hc := hb'.extend hP hQ (fun _ : Unit => p (.seg u a b)) (fun _ => q (.seg u a b))
      (fun _ => .inl (.inr ())) (fun _ => .inr ()) (fun _ => u.val)
      (fun _ => hp.2.2) (fun _ => hq.2.2)
    -- 推导：记下中间结论 `e`：`X ⊕ Unit → ((X ⊕ Unit) ⊕ Unit) ⊕ Unit`。
    let e : X ⊕ Unit → ((X ⊕ Unit) ⊕ Unit) ⊕ Unit := Sum.map (Sum.inl ∘ Sum.inl) id
    have project {W : Type} (z : X → W) (a b c : W) :
        snoc (snoc (snoc z a) b) c ∘ e = snoc z c := by funext i; cases i <;> rfl
    have hc' := hc.comp e
    change Agree P Q (snoc (snoc (snoc x (p a)) (p b)) _ ∘ e)
      (snoc (snoc (snoc y (q a)) (q b)) _ ∘ e) at hc'
    rwa [project, project] at hc'

-- 读法：`gap P (p a) (p b)` 等于 `gap Q (q a) (q b)`。这里调用 `hb.gap`。
theorem terms_determine [Fintype S] [DecidableEq S] [Nonempty S]
    (hP : P ∈ ordinary K T D) (hQ : Q ∈ ordinary K V E) (a b : Term S)
    (hpa : Fits P p a) (hpb : Fits P p b) (hqa : Fits Q q a) (hqb : Fits Q q b)
    (h : Agree P Q (p ∘ Term.mark) (q ∘ Term.mark)) :
    gap P (p a) (p b) = gap Q (q a) (q b) := by
  have ha := append_term hP hQ a hpa hqa _ _ id (fun _ => rfl) (fun _ => rfl) h
  have hb := append_term hP hQ b hpb hqb _ _ Sum.inl (fun _ => rfl) (fun _ => rfl) ha
  exact hb.gap (.inl (.inr ())) (.inr ())

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# 测地距离的一致有限检验

在扩充后的价格构成的紧集上，对某一表达式距离的差异作指定限制，所得价格对集合仍是紧的。每一对这样的价格都可由某个原张量区分，因此只需有限多个原张量，且能保留正的容差。

**英文原文**

Uniform finite tests for geodesic distances

On a compact set of enlarged prices, pairs with a prescribed discrepancy
in a term distance are compact. Some old tensor separates each such
pair, so finitely many old tensors suffice with positive tolerance.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Tensor Set

-- 读法：存在 `t : Finset I`，存在 `δ : ℝ`，由 `0 < δ ∧ ∀ x ∈ s, ∀ y ∈ s, (∀ i ∈ t, |f i x - f i y| ≤ δ)` 推出 `∀ j, |g j x - g j y| ≤ ε`。这里调用 `hs.prod`。
private theorem finite_observations {X I J : Type*} [TopologicalSpace X] [Finite J]
    {s : Set X} (hs : IsCompact s) (f : I → X → ℝ) (g : J → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ j, Continuous (g j))
    (he : ∀ x ∈ s, ∀ y ∈ s, (∀ i, f i x = f i y) → ∀ j, g j x = g j y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset I, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∀ y ∈ s,
      (∀ i ∈ t, |f i x - f i y| ≤ δ) → ∀ j, |g j x - g j y| ≤ ε := by
  classical
  let bad := s ×ˢ s ∩ {z : X × X | ∃ j, ε ≤ |g j z.1 - g j z.2|}
  have hc : IsCompact bad := by
    apply (hs.prod hs).inter_right
    rw [ofPred_exists]
    exact isClosed_iUnion_of_finite fun j => isClosed_le continuous_const
      (((hg j).comp continuous_fst).sub ((hg j).comp continuous_snd)).abs
  let U (i : I) := {z : X × X | f i z.1 ≠ f i z.2}
  have hu (i : I) : IsOpen (U i) :=
    isOpen_ne_fun ((hf i).comp continuous_fst) ((hf i).comp continuous_snd)
  have hcover : bad ⊆ ⋃ i, U i := by
    rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, j, h⟩
    apply mem_iUnion.mpr
    exact not_forall.mp fun hxy => hε.not_ge (by simpa [he x hx y hy hxy j] using h)
  -- 推导：从 `hc.elim_finite_subcover U hu hcover` 中取出 `t, ht`。
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hu hcover
  by_cases hn : bad.Nonempty
  swap
  · exact ⟨∅, 1, zero_lt_one, fun x hx y hy _ j =>
      le_of_not_gt fun h => hn ⟨(x, y), ⟨hx, hy⟩, j, h.le⟩⟩
  let d (z : X × X) := ∑ i ∈ t, |f i z.1 - f i z.2|
  have hd : Continuous d := continuous_finsetSum _ fun i _ =>
    (((hf i).comp continuous_fst).sub ((hf i).comp continuous_snd)).abs
  obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hn hd.continuousOn
  obtain ⟨i, hi, hneq⟩ := mem_iUnion₂.mp (ht hz)
  -- 推导：记下中间结论 `hd0`：`0 < d z`。
  have hd0 : 0 < d z := Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, hi, abs_pos.mpr (sub_ne_zero.mpr hneq)⟩
  let δ := d z / ((t.card : ℝ) + 1)
  have hδ : 0 < δ := div_pos hd0 (by positivity)
  refine ⟨t, δ, hδ, fun x hx y hy hxy j => le_of_not_gt fun h => ?_⟩
  have h₁ : d z ≤ d (x, y) := hmin ⟨⟨hx, hy⟩, j, h.le⟩
  have h₂ : d (x, y) ≤ (t.card : ℝ) * δ := by
    simpa [d, nsmul_eq_mul] using Finset.sum_le_sum hxy
  have e : δ * ((t.card : ℝ) + 1) = d z := div_mul_cancel₀ _ (by positivity)
  linarith

variable {K S T : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype T] [DecidableEq T] [Nonempty T]

-- 读法：这里调用 `compact_ordinary`。
private theorem finite_price_tests (w : Finset (Term S)) (e : Term S → T) (D : ℝ)
    {ε : ℝ} (he : 0 < ε) :
    ∃ s : Finset (Tensor K S), ∃ δ : ℝ, 0 < δ ∧
      ∀ P ∈ ordinary K T D, ∀ Q ∈ ordinary K T D,
        (∀ a ∈ w, Fits P e a) → (∀ a ∈ w, Fits Q e a) →
        (∀ A ∈ s, |P (place (e ∘ Term.mark) A) - Q (place (e ∘ Term.mark) A)| ≤ δ) →
        ∀ a ∈ w, ∀ b ∈ w, |gap P (e a) (e b) ^ 2 - gap Q (e a) (e b) ^ 2| ≤ ε := by
  let s := ordinary K T D ∩ {P | ∀ a ∈ w, Fits P e a}
  have hs : IsCompact s := by
    apply (compact_ordinary _).inter_right
    simp only [ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun _ => closed_fits e a
  let f (A : Tensor K S) (P : Tensor K T → ℝ) := P (place (e ∘ Term.mark) A)
  let g (i : w × w) (P : Tensor K T → ℝ) := gap P (e i.1.val) (e i.2.val) ^ 2
  -- 推导：从 `finite_observations hs f g` 中取出 `q, δ, hδ, h`。
  obtain ⟨q, δ, hδ, h⟩ := finite_observations hs f g
    (fun A => continuous_apply _) (fun i => (continuous_apply _).pow 2)
    (fun P hP Q hQ h (i : w × w) => congrArg (fun z : ℝ => z ^ 2)
      (terms_determine hP.1 hQ.1 _ _ (hP.2 _ i.1.2) (hP.2 _ i.2.2)
        (hQ.2 _ i.1.2) (hQ.2 _ i.2.2) h)) he
  exact ⟨q, δ, hδ, fun P hP Q hQ h₁ h₂ h₃ a ha b hb =>
    h P ⟨hP, h₁⟩ Q ⟨hQ, h₂⟩ h₃ (⟨a, ha⟩, ⟨b, hb⟩)⟩

open Classical in
-- 读法：逐一匹配以下输入模式：`.mark i`、`.seg u a b`。
def Term.subterms {G : Type} : Term G → Finset (Term G)
  | .mark i => {.mark i}
  | .seg u a b => insert (.seg u a b) (a.subterms ∪ b.subterms)

-- 读法：`a` 属于 `a.subterms`。
theorem Term.mem_subterms {G : Type} (a : Term G) : a ∈ a.subterms := by
  classical
  cases a <;> simp [subterms]

section Metric
variable {Y : Type*} [MetricSpace Y] (C : Comparison Y) (x : S → Y)

omit [Fintype S] [DecidableEq S] [Nonempty S] in
-- 读法：`dist (a.eval C x) z` 不超过 `D`。对 `a` 作归纳。
private theorem eval_bound {D : ℝ} (hD : 0 ≤ D) (z : Y) (hx : ∀ i, dist (x i) z ≤ D)
    (a : Term S) : dist (a.eval C x) z ≤ D := by
  induction a with
  | mark => exact hx _
  | seg u a b ha hb =>
    apply (sq_le_sq₀ _root_.dist_nonneg hD).mp
    have h := C.along u (a.eval C x) (b.eval C x) z
    have ht := sub_nonneg.mpr u.2.2
    have h₁ := mul_le_mul_of_nonneg_left ((sq_le_sq₀ _root_.dist_nonneg hD).mpr ha) ht
    have h₂ := mul_le_mul_of_nonneg_left ((sq_le_sq₀ _root_.dist_nonneg hD).mpr hb) u.2.1
    have h₃ := mul_nonneg (mul_nonneg u.2.1 ht) (sq_nonneg (dist (a.eval C x) (b.eval C x)))
    change dist (C.seg _ _ _) _ ^ 2 ≤ _
    linarith only [h, h₁, h₂, h₃]

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty T] in
-- 读法：要证明的命题是 `Fits P e a`。对 `a` 作归纳。
private theorem fits_of_eval (P : Tensor K T → ℝ) (e : Term S → T) (z : T → Y)
    (hp : ∀ i j, gap P i j = dist (z i) (z j)) (a : Term S)
    (he : ∀ b ∈ a.subterms, z (e b) = b.eval C x) : Fits P e a := by
  classical
  induction a with
  | mark => trivial
  | seg u a b ha hb =>
    have ha' (s) (h : s ∈ a.subterms) := he s (by simp [Term.subterms, h])
    have hb' (s) (h : s ∈ b.subterms) := he s (by simp [Term.subterms, h])
    refine ⟨ha ha', hb hb', ?_⟩
    simp only [AtFraction, hp, he _ (Term.mem_subterms _), ha' _ a.mem_subterms,
      hb' _ b.mem_subterms, Term.eval]
    have H := C.along u (a.eval C x) (b.eval C x)
    refine ⟨H.start, ?_⟩
    rw [_root_.dist_comm, H.rev.start, _root_.dist_comm]
    rfl
end Metric

-- 读法：证明中先建立 `em`，即 `e ∘ Term.mark = Sum.inl`。
/-- 原有张量价格确定指定表达式之间的全部距离，这一结论对所有完备实现以及所有重复标记都一致成立。

英文原文：Old tensor prices determine all distances among the indicated terms,
uniformly over complete realizations and repetitions of the markings.
-/
theorem finite_terms_tests (K : Type) [Field K] (w : Finset (Term S)) (D : ℝ)
    {ε : ℝ} (he : 0 < ε) :
    ∃ s : Finset (Tensor K S), ∃ δ : ℝ, 0 < δ ∧
      ∀ {Y Z : Type} [MetricSpace Y] [MetricSpace Z] (C : Comparison Y) (C' : Comparison Z)
        {x : S → Y} {y : S → Z} {P Q : Tensor K S → ℝ},
        Realized x P D → Realized y Q D → (∀ A ∈ s, |P A - Q A| ≤ δ) →
        ∀ a ∈ w, ∀ b ∈ w, |dist (a.eval C x) (b.eval C x) ^ 2 - dist (a.eval C' y) (b.eval C' y) ^ 2| ≤ ε := by
  classical
  let i := Classical.arbitrary S
  let W := insert (.mark i) (w.biUnion Term.subterms)
  let _ : Nonempty ↥W := ⟨⟨.mark i, Finset.mem_insert_self _ _⟩⟩
  let e : Term S → S ⊕ ↥W
    | .mark s => .inl s
    | a@(.seg ..) => if h : a ∈ W then .inr ⟨a, h⟩ else .inl i
  -- 推导：记下中间结论 `em`：`e ∘ Term.mark = Sum.inl`。
  have em : e ∘ Term.mark = Sum.inl := rfl
  let B := 2 * D * Fintype.card (S ⊕ ↥W)
  have lift {Y : Type} [MetricSpace Y] (C : Comparison Y) (x : S → Y)
      (P : Tensor K S → ℝ) (hx : Realized x P D) :
      ∃ Q ∈ ordinary K (S ⊕ ↥W) B, (∀ A, Q (pad ↥W A) = P A) ∧
        (∀ a ∈ w, Fits Q e a) ∧
        ∀ a ∈ w, ∀ b ∈ w, gap Q (e a) (e b) = dist (a.eval C x) (b.eval C x) := by
    let z (a : W) := a.val.eval C x
    have hD := _root_.dist_nonneg.trans (hx.1 i i)
    have hbound (j : S ⊕ ↥W) : dist (Sum.elim x z j) (x i) ≤ D := by
      cases j with
      | inl j => exact hx.1 j i
      | inr j => exact eval_bound C x hD (x i) (fun s => hx.1 s i) j.val
    have H (j k : S ⊕ ↥W) : dist (Sum.elim x z j) (Sum.elim x z k) ≤ 2 * D := by
      rw [two_mul]
      exact (_root_.dist_triangle_right _ _ _).trans (add_le_add (hbound j) (hbound k))
    -- 推导：从 `hx.2 _ z H` 中取出 `Q, hQ, he, hd`。
    obtain ⟨Q, hQ, he, hd⟩ := hx.2 _ z H
    have hv (a) (ha : a ∈ w) (b) (hb : b ∈ a.subterms) : Sum.elim x z (e b) = b.eval C x := by
      have h : b ∈ W := Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, hb⟩)
      cases b <;> simp [e, h, z, Term.eval]
    refine ⟨Q, hQ, he, fun a ha => fits_of_eval C x Q e _ hd a (hv a ha), ?_⟩
    intro a ha b hb
    rw [gap, hd, hv a ha a a.mem_subterms, hv b hb b b.mem_subterms]
  obtain ⟨s, δ, hδ, ht⟩ := finite_price_tests (K := K) w e B he
  refine ⟨s, δ, hδ, ?_⟩
  intro Y Z _ _ C C' x y P Q hx hy hxy a ha b hb
  -- 推导：从 `lift C x P hx` 中取出 `P', hP', eP, fP, dP`。
  obtain ⟨P', hP', eP, fP, dP⟩ := lift C x P hx
  obtain ⟨Q', hQ', eQ, fQ, dQ⟩ := lift C' y Q hy
  rw [← dP a ha b hb, ← dQ a ha b hb]
  refine ht P' hP' Q' hQ' fP fQ ?_ a ha b hb
  simpa only [em, place_inl, eP, eQ] using hxy

end OAI.LinearAlgebra.MatrixExponent.Routing
end
