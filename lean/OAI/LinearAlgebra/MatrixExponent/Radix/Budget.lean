-- 本文件所属证明环节：按位段执行稳定排序，将短记录与宽记录的带标签置换问题分解成可安装的较小调用，并估计每阶段的槽位与成本。
import OAI.LinearAlgebra.MatrixExponent.Radix.Defs
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortOne
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Network.Dense
import OAI.LinearAlgebra.MatrixExponent.Radix.Short

section
/-!
# 将局部稳定排序所得的记录分包

在有序前缀中，对每个数位先放置其实际数据行，后接一整包空行。因此，即使一个包与数位边界未对齐，也至多包含一种非空数位。延伸到该前缀以外的活动包至多一个。

**英文原文**

Packing a stable local sort

The ordered prefix consists, for each digit, of its real rows followed by a
full pack of blanks. Thus even an unaligned pack contains at most one real
digit. At most one live pack extends past this prefix.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

section Grouping
variable {α β : Type} [LinearOrder β] [DecidableEq β]

-- 读法：`xs` 等于 `xs.filter (fun x => f x = k) ++ xs.filter (fun x => f x ≠ k)`。对 `xs` 作归纳。
private theorem split_first (f : α → β) (k : β) (xs : List α)
    (ho : xs.Pairwise (fun x y => f x ≤ f y)) (hle : ∀ x ∈ xs, k ≤ f x) :
    xs = xs.filter (fun x => f x = k) ++ xs.filter (fun x => f x ≠ k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h, hs⟩ := List.pairwise_cons.mp ho
    by_cases hx : f x = k
    · simpa [hx] using ih hs (fun y hy => hle y (by simp [hy]))
    · have hne : ∀ y ∈ x :: xs, f y ≠ k := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact ((lt_of_le_of_ne (hle x (by simp)) (Ne.symm hx)).trans_le (h y hy)).ne'
      rw [List.filter_eq_nil_iff.mpr (by simpa using hne), List.nil_append,
        List.filter_eq_self.mpr (by simpa using hne)]

-- 读法：`xs` 等于 `ks.flatMap (fun k => xs.filter (fun x => f x = k)) ++ xs.filter tail`。对 `ks` 作归纳，并把 `xs` 保持为任意参数。
/-- 从最小的键开始逐一读出，将所有更大的键保留在尾部。

英文原文：Read the least keys one at a time, leaving all larger keys as a tail.
-/
private theorem group_prefix (f : α → β) (tail : α → Bool) (ks : List β)
    (hk : ks.Pairwise (· < ·)) (ht : ∀ k ∈ ks, ∀ x, tail x = true → k < f x)
    (xs : List α) (ho : xs.Pairwise (fun x y => f x ≤ f y))
    (hc : ∀ x ∈ xs, f x ∈ ks ∨ tail x = true) :
    xs = ks.flatMap (fun k => xs.filter (fun x => f x = k)) ++ xs.filter tail := by
  induction ks generalizing xs with
  | nil => simpa using (List.filter_eq_self.mpr (by simpa using hc)).symm
  | cons k ks ih =>
    obtain ⟨hmin, hk⟩ := List.pairwise_cons.mp hk
    have hle (x : α) (hx : x ∈ xs) : k ≤ f x := by
      rcases hc x hx with he | h
      · rcases List.mem_cons.mp he with h | h
        · exact h.ge
        · exact (hmin _ h).le
      · exact (ht k (by simp) x h).le
    let zs := xs.filter (fun x => f x ≠ k)
    -- 推导：记下中间结论 `hc'`：`∀ x ∈ zs, f x ∈ ks ∨ tail x = true`。
    have hc' : ∀ x ∈ zs, f x ∈ ks ∨ tail x = true := by
      intro x hx
      obtain ⟨hx, hne⟩ := List.mem_filter.mp hx
      simpa [of_decide_eq_true hne] using hc x hx
    have keep (p : α → Bool) (h : ∀ x, p x = true → f x ≠ k) :
        zs.filter p = xs.filter p := by
      unfold zs
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      cases hx : p x
      · simp
      · simp [h x hx]
    have hh := ih hk (fun i hi => ht i (by simp [hi])) zs (ho.filter _) hc'
    rw [keep tail (fun x hx => (ht k (by simp) x hx).ne')] at hh
    have he : ks.flatMap (fun j => zs.filter (fun x => f x = j)) =
        ks.flatMap (fun j => xs.filter (fun x => f x = j)) := by
      apply List.flatMap_congr
      intro j hj
      exact keep _ (fun _ he => (of_decide_eq_true he) ▸ (hmin j hj).ne')
    rw [he] at hh
    rw [List.flatMap_cons, List.append_assoc, ← hh]
    exact split_first f k xs ho hle

end Grouping

-- 读法：`(ks.flatMap g).filter (fun x => f x = k)` 等于 `if k ∈ ks then g k else []`。对 `ks` 作归纳。
private theorem filter_groups {α β : Type} [DecidableEq β] (f : α → β) (g : β → List α)
    (h : ∀ k x, x ∈ g k → f x = k) (ks : List β) (hn : ks.Nodup) (k : β) :
    (ks.flatMap g).filter (fun x => f x = k) = if k ∈ ks then g k else [] := by
  induction ks with
  | nil => simp
  | cons i ks ih =>
    rw [List.flatMap_cons, List.filter_append, ih hn.of_cons]
    by_cases he : i = k
    · subst i
      rw [List.filter_eq_self.mpr (by simpa using h k)]
      simp [(List.nodup_cons.mp hn).1]
    · rw [List.filter_eq_nil_iff.mpr (by
        intro x hx
        simp [h i x hx, he])]
      simp [Ne.symm he]

variable {α : Type} {s : ℕ} (d : α → Val (word s))

-- 读法：要证明的命题是 `(real xs).Sublist (real ys)`。使用 `h.filter` 给出的结论。
private theorem real_subset {xs ys : List (Bool × α)} (h : xs.Sublist ys) :
    (real xs).Sublist (real ys) := (h.filter _).map _

-- 读法：`Windows` 表示以下条件：对每个 `i r`，由 `r ≤ P` 推出 `homogeneous d (real ((xs.drop i).take r))`。
private def Windows (P : ℕ) (xs : List (Bool × α)) : Prop :=
  ∀ i r, r ≤ P → homogeneous d (real ((xs.drop i).take r))

-- 读法：要证明的命题是 `Windows d P xs`。
private theorem windows_blank {P : ℕ} {xs : List (Bool × α)} (hx : real xs = []) :
    Windows d P xs := by
  intro i r _
  have h := real_subset ((xs.drop i).take_sublist r |>.trans (xs.drop_sublist i))
  simp only [hx, List.sublist_nil] at h
  simp [h, homogeneous]

-- 读法：要证明的命题是 `Windows d P ((true, junk) :: xs)`。
private theorem windows_cons {P : ℕ} {xs : List (Bool × α)} (junk : α)
    (h : Windows d P xs) : Windows d P ((true, junk) :: xs) := by
  rintro (_ | i) (_ | r) hr
  · simp [real, homogeneous]
  · simpa [real] using h 0 r (by omega)
  · simp [real, homogeneous]
  · exact h i (r + 1) hr

-- 读法：要证明的命题是 `Windows d P (ys ++ List.replicate P (true, junk) ++ xs)`。对 `ys` 作归纳。
private theorem windows_group {P : ℕ} {xs : List (Bool × α)} (h : Windows d P xs)
    (junk : α) (ys : List (Bool × α)) (hy : homogeneous d (real ys)) :
    Windows d P (ys ++ List.replicate P (true, junk) ++ xs) := by
  induction ys with
  | nil =>
    have pad (n : ℕ) : Windows d P (List.replicate n (true, junk) ++ xs) := by
      induction n with
      | zero => exact h
      | succ n ih => simpa only [List.replicate_succ, List.cons_append] using windows_cons d junk ih
    exact pad P
  | cons y ys ih =>
    rintro (_ | i) r hr
    · let buf := (y :: ys) ++ List.replicate P (true, junk)
      change homogeneous d (real ((buf ++ xs).take r))
      rw [List.take_append_of_le_length (by simp [buf]; omega)]
      have hs := (real_subset (List.take_sublist r buf)).subset
      -- 推导：记下中间结论 `hb`：`real buf = real (y :: ys)`。
      have hb : real buf = real (y :: ys) := by unfold buf; rw [real_append]; simp [real]
      rw [hb] at hs
      exact fun _ hu _ hv => hy _ (hs hu) _ (hs hv)
    · have hs := (real_subset (List.sublist_cons_self y ys)).subset
      exact ih (fun _ hu _ hv => hy _ (hs hu) _ (hs hv)) i r hr

-- 读法：要证明的命题是 `homogeneous d (real b)`。
private theorem windows_chunk {P : ℕ} {bs : List (List (Bool × α))}
    (h : Windows d P bs.flatten) (b : List (Bool × α)) (hb : b ∈ bs) (hl : b.length = P) :
    homogeneous d (real b) := by
  obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hb
  simpa only [List.flatten_append, List.flatten_cons, List.drop_left, List.take_left] using
    h l.flatten.length b.length hl.le

-- 读法：`bs.filter live` 等于 `[]`。对 `bs` 作归纳。
private theorem no_live {bs : List (List (Bool × α))} (h : real bs.flatten = []) :
    bs.filter live = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatten_cons, real_append, List.append_eq_nil_iff] at h
    simp [live, h.1, ih h.2]

-- 读法：`(bs.filter live).length * P` 不超过 `xs.length + P`。对 `bs` 作归纳，并把 `xs` 保持为任意参数。
private theorem live_bound {P : ℕ} (bs : List (List (Bool × α)))
    (hl : ∀ b ∈ bs, b.length = P) (xs zs : List (Bool × α))
    (hz : real zs = []) (he : bs.flatten = xs ++ zs) :
    (bs.filter live).length * P ≤ xs.length + P := by
  induction bs generalizing xs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hb, hl⟩ := List.forall_mem_cons.mp hl
    have hh : bs.flatten = (xs ++ zs).drop P := by
      rw [← he, List.flatten_cons, ← hb, List.drop_left]
    -- 推导：记下中间结论 `ht`：`(bs.filter live).length * P ≤ xs.length`。
    have ht : (bs.filter live).length * P ≤ xs.length := by
      by_cases hp : P ≤ xs.length
      · rw [List.drop_append_of_le_length hp] at hh
        simpa [Nat.sub_add_cancel hp] using ih hl _ hh
      · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append] at hh
        have hs := real_subset (List.drop_sublist (P - xs.length) zs)
        rw [← hh, hz, List.sublist_nil] at hs
        simp [no_live hs]
    rw [List.filter_cons]
    split
    · rw [List.length_cons, Nat.succ_mul]; omega
    · omega

-- 读法：`digitBlock` 的取值由 `(xs.filter (fun x => d x = k)).map (false, ·) ++ List.replicate P (true, junk)` 给出。
private def digitBlock (xs : List α) (junk : α) (P : ℕ) (k : Val (word s)) :
    List (Bool × α) :=
  (xs.filter (fun x => d x = k)).map (false, ·) ++ List.replicate P (true, junk)

-- 读法：`real (xs.map (false, ·))` 等于 `xs`。
private theorem real_mark (xs : List α) : real (xs.map (false, ·)) = xs := by
  simp [real, List.filter_map, Function.comp_def]

-- 读法：`real (List.replicate P (true, junk))` 等于 `[]`。
private theorem real_pad (junk : α) (P : ℕ) :
    real (List.replicate P (true, junk)) = [] := by simp [real]

-- 读法：对 `ks` 作归纳。
private theorem block_bounds (xs : List α) (junk : α) (P : ℕ) (ks : List (Val (word s)))
    (tail : List (Bool × α)) (ht : real tail = []) :
    let body := ks.flatMap (digitBlock d xs junk P)
    Windows d P (body ++ tail) ∧ body.length = (real body).length + ks.length * P ∧
      real body = ks.flatMap (fun k => xs.filter (fun x => d x = k)) := by
  induction ks with
  | nil => simpa [real] using windows_blank d ht
  | cons k ks ih =>
    obtain ⟨hh, hl, hr⟩ := ih
    simp only [List.flatMap_cons, List.append_assoc, digitBlock, real_append, real_mark, real_pad,
      List.length_append, List.length_cons, List.length_map, List.length_replicate,
      Nat.succ_mul, List.nil_append]
    refine ⟨?_, by omega, by rw [hr]⟩
    rw [← List.append_assoc]
    apply windows_group d hh junk
    rw [real_mark]
    intro x hx y hy
    exact (of_decide_eq_true (List.mem_filter.mp hx).2).trans
      (of_decide_eq_true (List.mem_filter.mp hy).2).symm

-- 读法：在后续公式中，`Row` 是 `Val (word (s + 1)) × (Bool × α)` 的缩写。
private abbrev Row (s : ℕ) (α : Type) := Val (word (s + 1)) × (Bool × α)

-- 读法：`((xs.map (decorate d)).filter (fun x => x.1 = (false, k))).map Prod.snd` 等于 `((real xs).filter (fun x => d x = k)).map (false, ·)`。对 `xs` 作归纳。
private theorem filter_decorate (xs : List (Bool × α)) (k : Val (word s)) :
    ((xs.map (decorate d)).filter (fun x => x.1 = (false, k))).map Prod.snd =
      ((real xs).filter (fun x => d x = k)).map (false, ·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨f, x⟩ := x
    cases f <;> by_cases h : d x = k <;> simp_all [decorate, real]

-- 读法：`((filler junk keys P e).filter (fun x => x.1 = (false, k))).map Prod.snd` 等于 `List.replicate P (true, junk)`。
private theorem filter_filler (junk : α) (keys : List (Val (word s))) (hn : keys.Nodup)
    (P e : ℕ) (k : Val (word s)) (hk : k ∈ keys) :
    ((filler junk keys P e).filter (fun x => x.1 = (false, k))).map Prod.snd =
      List.replicate P (true, junk) := by
  let mark (i : Val (word s)) : Val (word (s + 1)) := (false, i)
  have hm : Function.Injective mark := fun _ _ h => congrArg Prod.snd h
  let pads (i : Val (word (s + 1))) := List.replicate P (i, true, junk)
  have hx := filter_groups Prod.fst pads (by simp [pads]) (keys.map mark)
    (hn.map hm) (mark k)
  rw [ite_eq_left (List.mem_map.mpr ⟨k, hk, rfl⟩)] at hx
  simp only [List.flatMap_map, mark, pads] at hx
  simp [filler, hx]

-- 读法：`real ((ys.filter (fun y => y.1.1)).map Prod.snd)` 等于 `[]`。
private theorem blank_tail (ys : List (Row s α)) (xs : List (Bool × α)) (junk : α)
    (keys : List (Val (word s))) (P e : ℕ)
    (h : ys.Perm (xs.map (decorate d) ++ filler junk keys P e)) :
    real ((ys.filter (fun y => y.1.1)).map Prod.snd) = [] := by
  unfold real
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy, ht⟩ := List.mem_filter.mp hy
  rcases List.mem_append.mp (h.mem_iff.mp hy) with hy | hy
  · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    simpa [decorate] using ht
  · simp [filler] at hy
    grind

-- 读法：要证明的命题是 `(real (ys.map Prod.snd)).Perm (real xs)`。
private theorem real_perm (ys : List (Row s α)) (xs : List (Bool × α)) (junk : α)
    (keys : List (Val (word s))) (P e : ℕ)
    (h : ys.Perm (xs.map (decorate d) ++ filler junk keys P e)) :
    (real (ys.map Prod.snd)).Perm (real xs) := by
  have he : real ((filler junk keys P e).map Prod.snd) = [] := by
    simp [filler, real, List.filter_flatMap, List.map_flatMap]
  have hp : (real (ys.map Prod.snd)).Perm
      (real ((xs.map (decorate d) ++ filler junk keys P e).map Prod.snd)) :=
    ((h.map _).filter _).map _
  simpa [real_append, he, decorate, Function.comp_def] using hp

-- 读法：`ys.map Prod.snd` 等于 `ks.flatMap (digitBlock d (real xs) junk P) ++ (ys.filter (fun y => y.1.1)).map Prod.snd`。这里调用 `List.pairwise_map.mpr`。
private theorem layout (xs : List (Bool × α)) (junk : α)
    (keys ks : List (Val (word s))) (hn : keys.Nodup) (ha : ∀ k, k ∈ keys)
    (hk : ks.Pairwise (· < ·)) (hall : ∀ k, k ∈ ks) (P e : ℕ) (ys : List (Row s α))
    (hs : Stable (s := s + 1) Prod.fst (xs.map (decorate d) ++ filler junk keys P e) ys) :
    ys.map Prod.snd = ks.flatMap (digitBlock d (real xs) junk P) ++
      (ys.filter (fun y => y.1.1)).map Prod.snd := by
  let mark (k : Val (word s)) : Val (word (s + 1)) := (false, k)
  have ho : (ks.map mark).Pairwise (wordOrder (s + 1)).lt := by
    apply List.pairwise_map.mpr
    refine hk.imp fun {a b} h => ?_
    exact Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, h⟩)
  have ht (k) (hm : k ∈ ks.map mark) (x : Row s α) (hx : x.1.1 = true) :
      (wordOrder (s + 1)).lt k x.1 := by
    -- 推导：从 `List.mem_map.mp hm` 中取出 `i, _, rfl`。
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    exact Prod.Lex.toLex_lt_toLex.mpr (.inl (by simp [hx]))
  have hc (x : Row s α) (_ : x ∈ ys) : x.1 ∈ ks.map mark ∨ x.1.1 = true := by
    obtain ⟨⟨_ | _, k⟩, _⟩ := x
    · exact .inl (List.mem_map.mpr ⟨k, hall k, rfl⟩)
    · exact .inr rfl
  have eq := @group_prefix _ _ (wordOrder (s + 1)) (valDecidableEq _) Prod.fst
    (fun y : Row s α => y.1.1) (ks.map mark) ho ht ys hs.2.1 hc
  conv_lhs => rw [eq]
  rw [List.map_append, List.flatMap_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro k _
  rw [hs.2.2 (mark k), List.filter_append, List.map_append]
  exact congrArg₂ (· ++ ·) (filter_decorate d xs k) (filter_filler junk keys hn P e k (ha k))

-- 读法：要证明的命题是 `(ks.flatMap (fun k => xs.filter (fun x => d x = k))).Pairwise (fun x y => d x ≤ d y)`。这里调用 `List.pairwise_flatMap.mpr`。
private theorem ordered_groups (xs : List α) (ks : List (Val (word s)))
    (hk : ks.Pairwise (· < ·)) :
    (ks.flatMap (fun k => xs.filter (fun x => d x = k))).Pairwise (fun x y => d x ≤ d y) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    refine List.pairwise_iff_get.mpr fun x y _ => ?_
    have he (j) : d ((xs.filter (fun x => d x = i)).get j) = i :=
      of_decide_eq_true (List.mem_filter.mp (List.get_mem _ j)).2
    rw [he, he]
  · refine hk.imp fun h x hx y hy => ?_
    rw [of_decide_eq_true (List.mem_filter.mp hx).2, of_decide_eq_true (List.mem_filter.mp hy).2]
    exact h.le

-- 读法：`(∀ b ∈ bs, homogeneous d (real b))` 与 `(bs.filter live).length * P ≤ (real xs).length + (keys.length + 1) * P ∧ Stable d (real xs) (real bs.flatten)` 同时成立。
/-- 局部稳定排序时为每个数位加入 P 个分隔符，使输出中的每个包只含单一数位的数据。只有与实际键前缀重叠的包才可能是活动包。

英文原文：Local stable sorting with P delimiters per digit isolates all digits in
the output packs. Only packs overlapping the real-key prefix can be live.
-/
theorem packing (xs : List (Bool × α)) (junk : α) (keys : List (Val (word s)))
    (hn : keys.Nodup) (ha : ∀ k, k ∈ keys) (P e : ℕ) (_hp : 0 < P)
    (ys : List (Val (word (s + 1)) × (Bool × α)))
    (hs : Stable (s := s + 1) Prod.fst (xs.map (decorate d) ++ filler junk keys P e) ys)
    (bs : List (List (Bool × α))) (hl : ∀ b ∈ bs, b.length = P) (hf : bs.flatten = ys.map Prod.snd) :
    (∀ b ∈ bs, homogeneous d (real b)) ∧
      (bs.filter live).length * P ≤ (real xs).length + (keys.length + 1) * P ∧
      Stable d (real xs) (real bs.flatten) := by
  let ks := keys.insertionSort (· ≤ ·)
  have hk : ks.Perm keys := List.perm_insertionSort _ _
  have hall := fun k => hk.mem_iff.mpr (ha k)
  have hnodup := hk.nodup_iff.mpr hn
  -- 推导：记下中间结论 `hord`：`ks.Pairwise (· < ·)`。
  have hord : ks.Pairwise (· < ·) :=
    ((List.pairwise_insertionSort (· ≤ ·) keys).and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  let body := ks.flatMap (digitBlock d (real xs) junk P)
  let tail := (ys.filter (fun y => y.1.1)).map Prod.snd
  have hey : bs.flatten = body ++ tail :=
    hf.trans (layout d xs junk keys ks hn ha hord hall P e ys hs)
  have ht : real tail = [] := blank_tail d ys xs junk keys P e hs.1
  obtain ⟨hw, hm, hg⟩ := block_bounds d (real xs) junk P ks tail ht
  have hp : (real bs.flatten).Perm (real xs) := by
    rw [hf]
    exact real_perm d ys xs junk keys P e hs.1
  -- 推导：记下中间结论 `hr`：`real bs.flatten = real body`。
  have hr : real bs.flatten = real body := by rw [hey, real_append, ht, List.append_nil]
  refine ⟨(fun b hb => windows_chunk d (hey ▸ hw) b hb (hl b hb)), ?_, hp, ?_, ?_⟩
  · calc
      _ ≤ body.length + P := live_bound bs hl body tail ht hey
      _ = _ := by rw [hm, ← hr, hp.length_eq, hk.length_eq, Nat.succ_mul, Nat.add_assoc]
  · rw [hr, hg]
    exact ordered_groups d (real xs) ks hord
  · intro k
    rw [hr, hg, filter_groups d _ (by simp) _ hnodup, ite_eq_left (hall k)]

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 用带标签的置换作稳定排序

用输入位置标记每条记录。先按数位比较，再按位置比较。最后按记录本身比较，这样即使记录的标记不正确，所得的序也是全序。

**英文原文**

Stable sorting with tagged permutations

Label each record by its input position. Compare by digit, then by
position. A final comparison by record makes the order total even
outside the set of correctly labelled records.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix
open Tagged

variable {a : Wire} {s w : ℕ}

-- 读法：要证明的命题是 `(flatten w (indices w)).Pairwise (· < ·)`。对 `w` 作归纳。
theorem indices_sorted (w : ℕ) : (flatten w (indices w)).Pairwise (· < ·) := by
  induction w with
  | zero => simp [flatten]
  | succ w ih =>
    simp only [indices, flatten, flatten_mapRows, List.pairwise_append, List.pairwise_map]
    refine ⟨?_, ?_, ?_⟩
    · refine ih.imp fun h => ?_
      exact Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, h⟩)
    · refine ih.imp fun h => ?_
      exact Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, h⟩)
    · intro x hx y hy
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
      exact Prod.Lex.toLex_lt_toLex.mpr (.inl (show false < true by decide))

-- 读法：`(flatten w (label w x)).map Prod.snd` 等于 `flatten w x`。对 `n` 作归纳。
private theorem label_values (w : ℕ) (x : Val (tree w a)) :
    (flatten w (label w x)).map Prod.snd = flatten w x := by
  have h (n : ℕ) (y : Val (tree n a)) (i : Val (tree n (word w))) :
      (flatten n (zipRows (c := row w a) (fun u v => (v, u)) n y i)).map Prod.snd =
        flatten n y := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [flatten, zipRows, List.map_append, ih]
  exact h w x (indices w)

-- 读法：在后续公式中，`priority` 是 `LinearOrder.lift' (fun z : Val (row w a) => toLex (d z.2, toLex z)) (fun _ _ h => congrArg Prod.snd h)` 的缩写。
private abbrev priority [LinearOrder (Val a)] (d : Val a → Val (word s)) (w : ℕ) :
    LinearOrder (Val (row w a)) :=
  LinearOrder.lift' (fun z : Val (row w a) => toLex (d z.2, toLex z))
    (fun _ _ h => congrArg Prod.snd h)

-- 读法：要证明的命题是 `Stable d (flatten w x) (ys.map Prod.snd)`。这里调用 `h.1.le`。
private theorem stable_label [LinearOrder (Val a)] (d : Val a → Val (word s))
    (x : Val (tree w a)) (ys : List (Val (row w a)))
    (hp : ys.Perm (flatten w (label w x))) (hs : ys.Pairwise (priority d w).le) :
    Stable d (flatten w x) (ys.map Prod.snd) := by
  rw [← label_values w x]
  refine ⟨hp.map _, List.pairwise_map.mpr ?_, ?_⟩
  · refine hs.imp fun {i j} h => ?_
    rcases (Prod.Lex.toLex_le_toLex (x := (d i.2, toLex i)) (y := (d j.2, toLex j))).mp h with h | h
    · exact h.le
    · exact h.1.le
  · intro k
    -- 推导：记下中间结论 `p`：`Val (row w a) → Bool`。
    let p : Val (row w a) → Bool := fun i => decide (d i.2 = k)
    have hi : (flatten w (label w x)).Pairwise (fun i j => i.1 < j.1) :=
      List.pairwise_map.mp (by rw [label_tags]; exact indices_sorted w)
    have hx : ((flatten w (label w x)).filter p).Pairwise (priority d w).le := by
      refine List.pairwise_filter.mpr (hi.imp fun {i j} h h₁ h₂ => ?_)
      exact Prod.Lex.toLex_le_toLex.mpr (.inr ⟨(of_decide_eq_true h₁).trans (of_decide_eq_true h₂).symm,
        Prod.Lex.toLex_le_toLex.mpr (.inl h)⟩)
    let _ := priority d w
    have he := List.Perm.eq_of_pairwise' (hs.filter p) hx (hp.filter p)
    rw [List.filter_map, List.filter_map]
    exact congrArg (List.map Prod.snd) he

variable {F : Type} [Field F] {W m c : ℕ}

-- 读法：存在 `f : Val (tree w a) → Val (tree w a)`，`DNet F (tree w a) (tree w a) f (4 * m + 1000000 * 2 ^ w * (W + c))` 与 `∀ x, Stable digit (flatten w x) (flatten w (f x))` 同时成立。
theorem stable_net {digit : Val a → Val (word s)} (hd : DNet F a (word s) digit c)
    (hW : 1 + w + wd a + s ≤ W) (h : Net F (inputs w (word W)) .unit (tag F w (word W)) m) :
    ∃ f : Val (tree w a) → Val (tree w a),
      DNet F (tree w a) (tree w a) f (4 * m + 1000000 * 2 ^ w * (W + c)) ∧
      ∀ x, Stable digit (flatten w x) (flatten w (f x)) := by
  obtain ⟨encode, he, hi⟩ := Rewire.exists_of_width (wd_word (wd a)).symm
  let _ : LinearOrder (Val a) := LinearOrder.lift' encode hi
  have acmp : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) (100 * (wd a + 1)) :=
    (compare_lt F (wd a)).pre (he.par he)
  have cmp : letI := priority digit w
      letI : LT (Val (row w a)) := (priority digit w).toLT
      DNet F (.pair (row w a) (row w a)) .bit (fun x => decide (x.1 < x.2)) (800 * W + 2 * c) := by
    let _ : LinearOrder (Val (row w a)) :=
      @Prod.Lex.instLinearOrder _ _ (wordOrder w) inferInstance
    have key := ((DNet.snd F (word w) a).comp hd).pair (DNet.id F (row w a))
    have pos := lex_compare (compare_lt F w) acmp
    have all := (key.par key).comp (lex_compare (compare_lt F s) pos)
    exact all.mono (n := 800 * W + 2 * c) (by simp only [wd, wd_word]; omega)
  let _ := priority digit w
  -- 推导：记下中间结论 `ha`：`= tag_slices (b`。
  have ha := tag_slices (b := row w a) (Batch.of_net h 1) 0
    (by simp only [wd, wd_word]; omega)
  have hs := sort_of_tag ha cmp
  have net := ((label_net F w a).comp ((hs.pre (.unit' _)).post (.unit _))).comp
    (mapRows_net (DNet.snd F (word w) a) w)
  refine ⟨_, net.mono ?_, ?_⟩
  · simp only [wd, wd_word]
    have hm := Nat.mul_le_mul_left (2 ^ w) hW
    ring_nf at hm ⊢
    omega
  · intro x
    rw [flatten_mapRows]
    exact stable_label digit x _ (sortTree_perm ..) (sortTree_sorted ..)

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 对数据包排序并丢弃末尾的空包

非空包内的所有记录都具有同一个数位。因此，若包的排序是稳定的，在记录层面同一数位内的顺序也会保持。

**英文原文**

Sorting packs and discarding the empty tail

All records in a nonempty pack agree on their digit. Stability on packs
therefore preserves order within each digit at the level of records.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

variable {α β : Type} {s : ℕ} (d : α → Val (word s))
    (key : β → Val (word (s + 1))) (load : β → List α)

-- 读法：`packSpec` 表示以下条件：`((key b).1 = true ↔ load b = [])` 与 `∀ x ∈ load b, key b = (false, d x)` 同时成立。
def packSpec (b : β) : Prop :=
  ((key b).1 = true ↔ load b = []) ∧ ∀ x ∈ load b, key b = (false, d x)

-- 读法：`(bs.flatMap load).filter (fun x => d x = z)` 等于 `(bs.filter (fun b => key b = (false, z))).flatMap load`。对 `bs` 作归纳。
private theorem filter_load (z : Val (word s)) (bs : List β)
    (hm : ∀ b ∈ bs, packSpec d key load b) :
    (bs.flatMap load).filter (fun x => d x = z) =
      (bs.filter (fun b => key b = (false, z))).flatMap load := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := (hm b (by simp)).2
    have he := ih (fun i hi => hm i (by simp [hi]))
    by_cases h : key b = (false, z)
    -- 推导：记下中间结论 `hs`：`(load b).filter (fun x => d x = z) = load b`。
    · have hs : (load b).filter (fun x => d x = z) = load b :=
        List.filter_eq_self.mpr fun x hx => by
          simp only [decide_eq_true_eq]
          exact congrArg Prod.snd ((hb x hx).symm.trans h)
      simp [h, he, hs]
    · have hs : (load b).filter (fun x => d x = z) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by
          simp only [decide_eq_true_eq]
          exact fun e => h (by rw [hb x hx, e])
      simp [h, he, hs]

-- 读法：要证明的命题是 `(xs.flatMap load).Pairwise (fun x y => d x ≤ d y)`。这里调用 `List.pairwise_flatMap.mpr`。
private theorem unpack_order (xs : List β) (hm : ∀ b ∈ xs, packSpec d key load b)
    (hs : xs.Pairwise (fun b c => (wordOrder (s + 1)).le (key b) (key c))) :
    (xs.flatMap load).Pairwise (fun x y => d x ≤ d y) := by
  have transfer (b c : β) (hb : b ∈ xs) (hc : c ∈ xs)
      (he : (wordOrder (s + 1)).le (key b) (key c)) (x : α) (hx : x ∈ load b)
      (y : α) (hy : y ∈ load c) : d x ≤ d y := by
    rw [(hm b hb).2 x hx, (hm c hc).2 y hy] at he
    exact ((Prod.Lex.toLex_le_toLex.mp he).resolve_left (lt_irrefl false)).2
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, hs.imp_of_mem (fun hb hc he => transfer _ _ hb hc he)⟩
  intro b hb
  exact List.pairwise_iff_getElem.mpr fun _ _ _ _ _ =>
    transfer _ _ hb hb ((wordOrder (s + 1)).le_refl _) _ (List.getElem_mem _) _ (List.getElem_mem _)

-- 读法：要证明的命题是 `Stable d (xs.flatMap load) (ys.flatMap load)`。这里调用 `List.flatMap_eq_nil_iff.mpr`。
theorem sort_packs (xs ys zs : List β) (hm : ∀ b ∈ xs, packSpec d key load b)
    (hs : Stable (s := s + 1) key xs (ys ++ zs))
    (hcap : (xs.filter (fun b => !(load b).isEmpty)).length ≤ ys.length) :
    Stable d (xs.flatMap load) (ys.flatMap load) := by
  obtain ⟨hp, ho, hf⟩ := hs
  have ht : ∀ b ∈ ys ++ zs, packSpec d key load b := fun b hb => hm b (hp.subset hb)
  have hz : zs.flatMap load = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro z hz
    by_contra hload
    have hkey := (ht z (List.mem_append_right _ hz)).1
    -- 推导：记下中间结论 `hz'`：`(key z).1 = false`。
    have hz' : (key z).1 = false := Bool.eq_false_iff.mpr (mt hkey.mp hload)
    have hy : ys.filter (fun b => !(load b).isEmpty) = ys := by
      apply List.filter_eq_self.mpr
      intro y hy
      have hc := (List.pairwise_append.mp ho).2.2 y hy z hz
      have hx := (ht y (List.mem_append_left _ hy)).1
      have hl : load y ≠ [] := by
        intro e
        have := Prod.Lex.toLex_le_toLex.mp hc
        simp [hx.mpr e, hz'] at this
        exact (by decide : ¬ (true < false)) this
      simp [hl]
    have hp' := (hp.filter (fun b => !(load b).isEmpty)).length_eq
    rw [List.filter_append, hy, List.length_append] at hp'
    -- 推导：记下中间结论 `hv`：`z ∈ zs.filter (fun b => !(load b).isEmpty)`。
    have hv : z ∈ zs.filter (fun b => !(load b).isEmpty) := by simp [hz, hload]
    have := List.length_pos_of_mem hv
    omega
  have he : (ys ++ zs).flatMap load = ys.flatMap load := by simp [hz]
  rw [← he]
  refine ⟨hp.flatMap (fun _ _ => .refl _), unpack_order d key load _ ht ho, fun z => ?_⟩
  rw [filter_load d key load z _ ht, filter_load d key load z _ hm, hf]

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 在线性时间内读取数据包的数位

**英文原文**

Reading the digit of a pack in linear time
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

variable {a : Wire} {s : ℕ} (d : Val a → Val (word s))

-- 读法：在后续公式中，`pack` 是 `tree q (slot a)` 的缩写。
abbrev pack (q : ℕ) (a : Wire) := tree q (slot a)

-- 读法：`content` 的取值由 `real (flatten q x)` 给出。
def content (q : ℕ) (x : Val (pack q a)) : List (Val a) :=
  real (flatten q x)

-- 读法：当 `x.1` 成立时取 `k`，否则取 `(false, d x.2)`。
private def readDigit (k : Val (word (s + 1))) (x : Val (slot a)) : Val (word (s + 1)) :=
  if x.1 then k else (false, d x.2)

-- 读法：`packKey` 的取值由 `(flatten q x).foldl (readDigit d) (true, Lookup.zero s)` 给出。
def packKey (q : ℕ) (x : Val (pack q a)) : Val (word (s + 1)) :=
  (flatten q x).foldl (readDigit d) (true, Lookup.zero s)

-- 读法：`(real xs = [] ∧ xs.foldl (readDigit d) k = k)`、`∃ x ∈ real xs, xs.foldl (readDigit d) k = (false, d x)` 至少有一项成立。对 `xs` 作归纳，并把 `k` 保持为任意参数。
private theorem scan_key (xs : List (Val (slot a))) (k : Val (word (s + 1))) :
    (real xs = [] ∧ xs.foldl (readDigit d) k = k) ∨
      ∃ x ∈ real xs, xs.foldl (readDigit d) k = (false, d x) := by
  induction xs generalizing k with
  | nil => exact .inl ⟨rfl, rfl⟩
  | cons x xs ih =>
    rcases x with ⟨_ | _, x⟩
    · right
      change ∃ y ∈ x :: real xs, xs.foldl (readDigit d) (false, d x) = (false, d y)
      rcases ih (false, d x) with ⟨_, he⟩ | ⟨y, hy, he⟩
      · exact ⟨x, .head _, he⟩
      · exact ⟨y, .tail _ hy, he⟩
    · exact ih k

-- 读法：要证明的命题是 `packSpec d (packKey d q) (content q) x`。
theorem packKey_spec (q : ℕ) (x : Val (pack q a)) (h : homogeneous d (content q x)) :
    packSpec d (packKey d q) (content q) x := by
  rcases scan_key d (flatten q x) (true, Lookup.zero s) with ⟨hx, he⟩ | ⟨y, hy, he⟩
  · simp [packSpec, packKey, he, content, hx]
  · have hk : packKey d q x = (false, d y) := he
    have hl : content q x ≠ [] := List.ne_nil_of_mem hy
    refine ⟨by simp [hk, hl], fun z hz => ?_⟩
    rw [hk, h _ hy _ hz]

variable {F : Type} [Field F] {d}

-- 读法：在 `F` 上，函数 `(packKey d q)` 从 `(pack q a)` 到 `(word (s + 1))` 的图张量可由至多 `(1000 * 2 ^ q * (1 + wd a + s))` 个顶点实现。
theorem packKey_net (hd : DNet F a (word s) d (100 * (1 + wd a + s))) (q : ℕ) :
    DNet F (pack q a) (word (s + 1)) (packKey d q) (1000 * 2 ^ q * (1 + wd a + s)) := by
  let k := word (s + 1)
  have old := DNet.fst F k (slot a)
  have slotNet := DNet.snd F k (slot a)
  have flag := slotNet.comp (DNet.fst F .bit a)
  have get := (slotNet.comp (DNet.snd F .bit a)).comp hd
  have key := ((Lookup.const_net F .bit false).par get).pre ((Rewire.unit' _).comp (.swap _ _))
  have step : DNet F (.pair k (slot a)) k (fun x => readDigit d x.1 x.2)
      (500 * (1 + wd a + s)) :=
    (((old.pair key).pair flag).comp (selectWord F (s + 1))).mono
      (by simp only [wd, k, wd_word]; omega)
  have start := Lookup.const_net F k (true, Lookup.zero s)
  have seed := (start.par (DNet.id F (pack q a))).pre ((Rewire.unit' _).comp (.swap _ _))
  apply (seed.comp (Lookup.fold_net F step q)).mono
  simp only [k, wd, wd_tree, wd_word]
  have h := Nat.one_le_pow q 2 (by decide)
  nlinarith [Nat.mul_le_mul_right s h]

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 在不置换记录的情况下跨越块边界

**英文原文**

Crossing a block boundary without permuting the records
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

variable {a : Wire} {s : ℕ}

-- 读法：逐一匹配以下输入模式：`0, x`、`b + 1, x`。
def gather (q : ℕ) : (b : ℕ) → Val (tree (q + b) a) → Val (tree b (tree q a))
  | 0, x => x
  | b + 1, x => (gather q b x.1, gather q b x.2)

-- 读法：逐一匹配以下输入模式：`0, x`、`b + 1, x`。
def scatter (q : ℕ) : (b : ℕ) → Val (tree b (tree q a)) → Val (tree (q + b) a)
  | 0, x => x
  | b + 1, x => (scatter q b x.1, scatter q b x.2)

-- 读法：仅通过重新接线，从格式 `(tree (q + b) a)` 变换到 `(tree b (tree q a))`，实现映射 `(gather q b)`。对 `b` 作归纳。
theorem gather_wire (q b : ℕ) : Rewire (tree (q + b) a) (tree b (tree q a)) (gather q b) := by
  induction b with
  | zero => exact .id _
  | succ b ih => exact ih.par ih

-- 读法：仅通过重新接线，从格式 `(tree b (tree q a))` 变换到 `(tree (q + b) a)`，实现映射 `(scatter q b)`。对 `b` 作归纳。
theorem scatter_wire (q b : ℕ) : Rewire (tree b (tree q a)) (tree (q + b) a) (scatter q b) := by
  induction b with
  | zero => exact .id _
  | succ b ih => exact ih.par ih

-- 读法：`(flatten b (gather q b x)).flatMap (flatten q)` 等于 `flatten (q + b) x`。对 `b` 作归纳。
theorem flatten_gather (q b : ℕ) (x : Val (tree (q + b) a)) :
    (flatten b (gather q b x)).flatMap (flatten q) = flatten (q + b) x := by
  induction b with
  | zero => simp [gather, flatten]
  | succ b ih =>
    change (flatten b (gather q b x.1) ++ flatten b (gather q b x.2)).flatMap (flatten q) = flatten (q + b) x.1 ++ flatten (q + b) x.2
    exact List.flatMap_append.trans (congrArg₂ (· ++ ·) (ih x.1) (ih x.2))

-- 读法：`real (flatten (q + b) (scatter q b x))` 等于 `(flatten b x).flatMap (content q)`。对 `b` 作归纳。
theorem scatter_content (q b : ℕ) (x : Val (tree b (pack q a))) :
    real (flatten (q + b) (scatter q b x)) = (flatten b x).flatMap (content q) := by
  induction b with
  | zero => simp [scatter, flatten, content]
  | succ b ih =>
    change real (flatten (q + b) (scatter q b x.1) ++ flatten (q + b) (scatter q b x.2)) =
      (flatten b x.1 ++ flatten b x.2).flatMap (content q)
    rw [real_append, List.flatMap_append, ih, ih]

-- 读法：结构的字段包括 `homo`、`bound`、`perm`、`keep`。
/-- 对包排序前的一次部分扫描。分隔符额外占用的空间按每个输入块计费一次。

英文原文：A partial pass before sorting the packs. The additional space for
separators is charged once per input block.
-/
structure Blocked (d : Val a → Val (word s)) (q k : ℕ)
    (xs : List (Val a)) (bs : List (Val (pack q a))) : Prop where
  homo : ∀ b ∈ bs, homogeneous d (content q b)
  bound : (bs.filter (fun b => !(content q b).isEmpty)).length * 2 ^ q ≤
    xs.length + 2 ^ k * ((2 ^ s + 1) * 2 ^ q)
  perm : (bs.flatMap (content q)).Perm xs
  keep : ∀ z, (bs.flatMap (content q)).filter (fun x => d x = z) = xs.filter (fun x => d x = z)

variable {q k : ℕ} {d : Val a → Val (word s)}

-- 读法：要证明的命题是 `Blocked d q (k + 1) (xs ++ ys) (bs ++ cs)`。这里调用 `Nat.add_le_add`。
theorem Blocked.append {xs ys : List (Val a)} {bs cs : List (Val (pack q a))}
    (h : Blocked d q k xs bs) (g : Blocked d q k ys cs) :
    Blocked d q (k + 1) (xs ++ ys) (bs ++ cs) where
  homo b hb := (List.mem_append.mp hb).elim (h.homo b) (g.homo b)
  bound := by
    rw [List.filter_append, List.length_append, List.length_append, add_mul, pow_succ, mul_two,
      add_mul]
    exact (Nat.add_le_add h.bound g.bound).trans_eq (by omega)
  perm := by rw [List.flatMap_append]; exact h.perm.append g.perm
  keep z := by rw [List.flatMap_append, List.filter_append, List.filter_append, h.keep, g.keep]

-- 读法：要证明的命题是 `Stable d xs (cs.flatMap (content q))`。
theorem Blocked.finish {xs : List (Val a)} {bs cs es : List (Val (pack q a))}
    (h : Blocked d q k xs bs)
    (hg : Stable (packKey d q) bs (cs ++ es))
    (hc : xs.length + 2 ^ k * ((2 ^ s + 1) * 2 ^ q) ≤ cs.length * 2 ^ q) :
    Stable d xs (cs.flatMap (content q)) := by
  have hm := fun i hi => packKey_spec d q i (h.homo i hi)
  have hb := Nat.le_of_mul_le_mul_right (h.bound.trans hc) (pow_pos (by decide) q)
  obtain ⟨hp, ho, he⟩ := sort_packs d (packKey d q) (content q) bs cs es hm hg hb
  exact ⟨hp.trans h.perm, ho, fun z => (he z).trans (h.keep z)⟩

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 一趟局部基数排序

将槽位数加倍，并用分隔符填满新增的一半。按扩充后的键稳定排序后，不同数位之间便留有足够的空槽位，使每个包中的非空记录具有相同的数位。

**英文原文**

A local radix pass

Double the number of slots and fill the new half with separators.
Stable sorting by the augmented key leaves enough empty slots between
digits to make each pack homogeneous.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

variable {F : Type} [Field F] {a : Wire} {s q b U x : ℕ} {d : Val a → Val (word s)}

-- 读法：`(filler junk keys P e).length` 等于 `keys.length * P + e`。
private theorem filler_length (junk : Val a) (keys : List (Val (word s))) (P e : ℕ) :
    (filler junk keys P e).length = keys.length * P + e := by
  simp [filler, List.length_flatMap]

-- 读法：`real (bs.map (flatten q)).flatten` 等于 `bs.flatMap (content q)`。对 `bs` 作归纳。
private theorem packs_content (bs : List (Val (pack q a))) :
    real (bs.map (flatten q)).flatten = bs.flatMap (content q) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, List.flatten_cons, real_append, ih, List.flatMap_cons, content]

-- 读法：要证明的命题是 `Blocked d q 0 (real xs) bs`。这里调用 `Tagged.length_flatten`。
private theorem blocked_of_packing (xs : List (Val (slot a))) (junk : Val a)
    (keys : List (Val (word s))) (hn : keys.Nodup) (ha : ∀ k, k ∈ keys) (hk : keys.length = 2 ^ s)
    (e : ℕ) (ys : List (Val (aug s a)))
    (hs : Stable (s := s + 1) Prod.fst (xs.map (decorate d) ++ filler junk keys (2 ^ q) e) ys)
    (bs : List (Val (pack q a))) (hf : bs.flatMap (flatten q) = ys.map Prod.snd) :
    Blocked d q 0 (real xs) bs := by
  have hl : ∀ b ∈ bs.map (flatten q), b.length = 2 ^ q := by
    intro b hb
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hb
    exact Tagged.length_flatten q z
  obtain ⟨hh, hb, ho⟩ := packing d xs junk keys hn ha (2 ^ q) e (by positivity) ys hs
    (bs.map (flatten (a := slot a) q)) hl hf
  rw [packs_content] at ho
  refine ⟨fun z hz => hh _ (List.mem_map.mpr ⟨z, hz, rfl⟩), ?_, ho.1, ho.2.2⟩
  simpa only [List.filter_map, List.length_map, Function.comp_def, live, content, hk, pow_zero,
    one_mul] using hb

-- 读法：结论为 `∃ f, DNet F (tree (q + b) (slot a)) (tree (b + 1) (pack q a)) f (4 * x + 10000000 * 2 ^ (q + b + 1) * U) ∧ ∀ y, Blocked d q 0 (real (flatten (q + b) y)) (flatten (b + 1) (f y))`。
theorem local_net (hd : DNet F a (word s) d (100 * (1 + wd a + s)))
    (hb : s + 2 ≤ b) (hU : 6 + q + b + wd a + 2 * s ≤ U) (hT : Tag F (q + b + 1) U x) :
    ∃ f, DNet F (tree (q + b) (slot a)) (tree (b + 1) (pack q a)) f
      (4 * x + 10000000 * 2 ^ (q + b + 1) * U) ∧
      ∀ y, Blocked d q 0 (real (flatten (q + b) y)) (flatten (b + 1) (f y)) := by
  obtain ⟨z, hn, ha, _⟩ := Lookup.ordered_keys (word s)
  let keys := flatten (wd (word s)) z
  have hk : keys.length = 2 ^ s := by simp [keys, Tagged.length_flatten]
  let junk := (bits a).symm (fun _ => false)
  let e := 2 ^ (q + b) - 2 ^ s * 2 ^ q
  -- 推导：记下中间结论 `hlen`：`(filler junk keys (2 ^ q) e).length = 2 ^ (q + b)`。
  have hlen : (filler junk keys (2 ^ q) e).length = 2 ^ (q + b) := by
    rw [filler_length, hk, Nat.add_sub_of_le]
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨pad, hp⟩ := Lookup.as_tree (a := aug s a) (q + b) _ hlen
  have hx : DNet F (slot a) (aug s a) (decorate d) (200 * U) :=
    (((DNet.id F .bit).par hd).pair (DNet.id F (slot a))).mono (by simp only [wd]; omega)
  have prepared := ((Tagged.mapRows_net hx (q + b)).par (Tagged.literal_net F _ pad)).pre (.unit' _)
  obtain ⟨sort, hsort, ok⟩ := stable_net (s := s + 1) (DNet.fst F (word (s + 1)) (slot a))
    (by simp only [wd, wd_word]; omega) hT
  have proj := Tagged.mapRows_net (DNet.snd F (word (s + 1)) (slot a)) (q + b + 1)
  have net := ((prepared.comp hsort).comp proj).post (gather_wire q (b + 1))
  refine ⟨_, net.mono ?_, fun y => ?_⟩
  · simp only [wd_tree, wd, wd_word, pow_succ]
    have he := Nat.mul_le_mul_left (2 ^ (q + b)) hU
    ring_nf at he ⊢
    omega
  -- 推导：记下中间结论 `hs`：`= ok (Tagged.mapRows (a`。
  · have hs := ok (Tagged.mapRows (a := slot a) (b := aug s a) (decorate d) (q + b) y, pad)
    change Stable (s := s + 1) Prod.fst
      (flatten (q + b) (Tagged.mapRows (a := slot a) (b := aug s a) (decorate d) (q + b) y) ++
        flatten (q + b) pad) _ at hs
    rw [Tagged.flatten_mapRows, hp] at hs
    apply blocked_of_packing _ junk keys hn ha hk e _ hs
    rw [flatten_gather]
    exact Tagged.flatten_mapRows (a := aug s a) (b := slot a) Prod.snd (q + b + 1) _

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 每趟基数排序及所有趟合计的成本预算

**英文原文**

Cost allowances for a radix pass and all passes combined
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：`passCost` 的取值由 `2 ^ k * (4 * x + 10000000 * 2 ^ (q + b + 1) * U) + (4 * y + 2000000000 * 2 ^ (b + k + 1) * V)` 给出。
def passCost (q b k U V x y : ℕ) : ℕ :=
  2 ^ k * (4 * x + 10000000 * 2 ^ (q + b + 1) * U) + (4 * y + 2000000000 * 2 ^ (b + k + 1) * V)

-- 读法：`budget` 的取值由 `(2 * w / s + 1) * passCost q b k U V x y + 200000 * 2 ^ w * (w + 1)` 给出。
def budget (w s q b k U V x y : ℕ) : ℕ :=
  (2 * w / s + 1) * passCost q b k U V x y + 200000 * 2 ^ w * (w + 1)

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 固定容量下的一趟基数排序

预留一半槽位用于填充。各块独立处理，再作一次稳定排序，重新排列各块的数据包。若每个块的包数至少是数位字母表大小的四倍，则后半部分全部为空，可以舍弃。

**英文原文**

A radix pass at fixed capacity

Half the slots are reserved for padding. All blocks are processed
independently, then a single stable sort reorders their packs. If the
number of packs per block is at least four times the digit alphabet
size, the trailing half is entirely empty and can be discarded.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：对 `k` 作归纳。
private theorem blocks_net {F : Type} [Field F] {a : Wire} {q b s m : ℕ}
    {d : Val a → Val (word s)} (k : ℕ)
    (h : ∃ f, DNet F (tree (q + b) (slot a)) (tree (b + 1) (pack q a)) f m ∧
      ∀ y, Blocked d q 0 (real (flatten (q + b) y)) (flatten (b + 1) (f y))) :
    ∃ f, DNet F (tree (q + (b + k)) (slot a)) (tree (b + k + 1) (pack q a)) f (2 ^ k * m) ∧
      ∀ y, Blocked d q k (real (flatten (q + (b + k)) y)) (flatten (b + k + 1) (f y)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    obtain ⟨f, hf, he⟩ := ih
    rw [pow_succ, mul_two, add_mul]
    refine ⟨fun y => (f y.1, f y.2), hf.par hf, fun y => ?_⟩
    change Blocked _ _ _ (real (flatten (q + (b + k)) y.1 ++ flatten (q + (b + k)) y.2))
      (flatten (b + k + 1) (f y.1) ++ flatten (b + k + 1) (f y.2))
    rw [real_append]
    exact (he y.1).append (he y.2)

-- 读法：`n + 2 ^ k * ((2 ^ s + 1) * 2 ^ q)` 不超过 `2 ^ (b + k) * 2 ^ q`。
private theorem capacity {s q b k n : ℕ} (hb : s + 2 ≤ b) (hn : 2 * n ≤ 2 ^ (q + (b + k))) :
    n + 2 ^ k * ((2 ^ s + 1) * 2 ^ q) ≤ 2 ^ (b + k) * 2 ^ q := by
  have h : 2 * (2 ^ s + 1) ≤ 2 ^ b := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hb
    have := (pow_pos (by decide : 0 < 2) s)
    rw [pow_add] at *
    omega
  have h' := Nat.mul_le_mul_right (2 ^ k * 2 ^ q) h
  simp only [pow_add] at hn ⊢
  ring_nf at hn h' ⊢
  omega

-- 读法：证明中先建立 `hw`，即 `1 + (b + k + 1) + wd (pack q a) + (s + 1) ≤ V`。
private theorem finish_net {F : Type} [Field F] {a : Wire} {q b k s V y : ℕ}
    {d : Val a → Val (word s)} (hd : DNet F a (word s) d (100 * (1 + wd a + s)))
    (hV : (4 + b + k + s + wd a) * 2 ^ q ≤ V) (hT : Tag F (b + k + 1) V y) (hb : s + 2 ≤ b) :
    ∃ f, DNet F (tree (b + k + 1) (pack q a)) (tree (q + (b + k)) (slot a)) f
        (4 * y + 2000000000 * 2 ^ (b + k + 1) * V) ∧
      ∀ z xs, 2 * xs.length ≤ 2 ^ (q + (b + k)) → Blocked d q k xs (flatten (b + k + 1) z) →
        Stable d xs (real (flatten (q + (b + k)) (f z))) := by
  have hw : 1 + (b + k + 1) + wd (pack q a) + (s + 1) ≤ V := by
    have h := Nat.mul_le_mul_left (3 + b + k + s) (Nat.one_le_pow q 2 (by decide))
    simp only [wd_tree, wd]
    nlinarith only [hV, h]
  -- 推导：从 `stable_net (packKey_net hd q) hw hT` 中取出 `f, hf, he`。
  obtain ⟨f, hf, he⟩ := stable_net (packKey_net hd q) hw hT
  let half := tree (b + k) (pack q a)
  have net := ((hf.comp (DNet.fst F half half)).post (scatter_wire q (b + k)))
  refine ⟨_, net.mono ?_, fun z xs hn hz => ?_⟩
  · have h := Nat.mul_le_mul_left (2 ^ (b + k + 1)) hV
    simp only [wd, wd_tree, half, pow_succ] at h ⊢
    ring_nf at h ⊢
    omega
  · rw [scatter_content]
    exact hz.finish (es := flatten (b + k) (f z).2) (he z)
      (by rw [Tagged.length_flatten]; exact capacity hb hn)

-- 读法：结论为 `∃ f, DNet F (tree (w + 2) (slot a)) (tree (w + 2) (slot a)) f (passCost q b k U V x y) ∧ ∀ z, 2 * (real (flatten (w + 2) z)).length ≤ 2 ^ (w + 2) → Stable d (real (flatten (w + 2) z)) (real (flatten (w + 2) (f z)))`。
theorem one_pass (F : Type) [Field F] (w s q b k U V x y : ℕ)
    (_hs : 1 ≤ s) (hb : s + 2 ≤ b) (he : q + (b + k) = w + 2)
    (hU : 10 * (w + 2) ≤ U) (hV : 10 * (w + 2) * 2 ^ q ≤ V)
    (h1 : Tag F (q + b + 1) U x) (h2 : Tag F (b + k + 1) V y)
    (a : Wire) (ha : wd a ≤ 2 * w + 1) (d : Val a → Val (word s))
    (hd : DNet F a (word s) d (100 * (1 + wd a + s))) :
    ∃ f, DNet F (tree (w + 2) (slot a)) (tree (w + 2) (slot a)) f (passCost q b k U V x y) ∧
      ∀ z, 2 * (real (flatten (w + 2) z)).length ≤ 2 ^ (w + 2) →
        Stable d (real (flatten (w + 2) z)) (real (flatten (w + 2) (f z))) := by
  rw [← he]
  have hu : 6 + q + b + wd a + 2 * s ≤ U := by omega
  have hv : (4 + b + k + s + wd a) * 2 ^ q ≤ V :=
    (Nat.mul_le_mul_right _ (by omega)).trans hV
  obtain ⟨f, hf, ef⟩ := blocks_net k (local_net hd hb hu h1)
  obtain ⟨g, hg, eg⟩ := finish_net hd hv h2 hb
  exact ⟨_, hf.comp hg, fun z hz => eg (f z) _ hz (ef z)⟩

end OAI.LinearAlgebra.MatrixExponent.Radix
end

section
/-!
# 通过基数排序验证普通带标签置换的成本

**英文原文**

Cost of verifying an ordinary tagged permutation by radix sorting
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

-- 读法：存在 `v`，要证明的命题是 `Tag F w w v`。
theorem tag_exists (F : Type) [Field F] (w : ℕ) : ∃ v, Tag F w w v := by
  obtain ⟨v, hv, _⟩ := Net.dense _ _ (Tagged.tag F w (word w))
  exact ⟨v, hv⟩

-- 读法：存在 `v ≤ budget w s q b k U V x y`，要证明的命题是 `Tag F w w v`。
theorem budget_net (F : Type) [Field F] (w s q b k U V x y : ℕ)
    (hs : 1 ≤ s) (hb : s + 2 ≤ b) (he : q + (b + k) = w + 2)
    (hU : 10 * (w + 2) ≤ U) (hV : 10 * (w + 2) * 2 ^ q ≤ V)
    (h1 : Tag F (q + b + 1) U x) (h2 : Tag F (b + k + 1) V y) :
    ∃ v ≤ budget w s q b k U V x y, Tag F w w v := by
  have one := one_pass F w s q b k U V x y hs hb he hU hV h1 h2
  let a := word (2 * w + 1)
  have ha : wd a = 2 * w + 1 := wd_word _
  obtain ⟨f, hf, hsort⟩ := radix F a (w + 2) s _ hs (one a ha.le)
    (show 2 * w ≤ wd a by omega) Prod.snd (DNet.snd F .bit (word (2 * w)))
  obtain ⟨v, hv, net⟩ := tag_of_sort hf (fun z hz =>
    hsort z (show 2 * (real (flatten (w + 2) z)).length ≤ 2 ^ (w + 2) by rw [pow_succ]; omega))
  refine ⟨v, hv.trans ?_, net⟩
  rw [ha, budget, pow_add]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Radix
end
