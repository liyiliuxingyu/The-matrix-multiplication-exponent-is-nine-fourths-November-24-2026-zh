-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting

/-!
# 沿移动轨迹的插值空间

用从接缝能量中扣除的额度来计数新增标记。剩余接缝能量与插入能量之和足以覆盖各极点的阶数。

**英文原文**

Interpolation space along a motion

Use the seam-energy debit to count new marks. Added to the insertion
energies, the remaining seam energies pay for the pole degrees.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
open Finset
open scoped Classical

variable {F T E V X : Type} {r t P g H U : ℕ} (s : Stage F r t T V E X)

-- 读法：`portWeight s.scene.level (s.scene.cell v).ports` 等于 `∑ e ∈ s.edges v, s.scene.level e`。
theorem portWeight_eq_sum (v : V) (h : ((s.ports v).map Prod.fst).Nodup) :
    portWeight s.scene.level (s.scene.cell v).ports = ∑ e ∈ s.edges v, s.scene.level e := by
  unfold ports at h
  rw [edges, List.sum_toFinset _ h, List.map_map]
  rfl

variable [Fintype V]

-- 读法：`P * sumA (s.scene.cell v).stations + sumB (s.scene.cell v).stations` 不超过 `(s.ledger P H).mobile v + (s.ledger P H).collected v`。对 `us` 作归纳。
theorem energy_le (P H : ℕ) (v : V) :
    P * sumA (s.scene.cell v).stations + sumB (s.scene.cell v).stations ≤
      (s.ledger P H).mobile v + (s.ledger P H).collected v := by
  simp only [ledger, tally, sumA, sumB]
  generalize (s.scene.cell v).stations = us
  induction us with
  | nil => simp
  | cons a as ih =>
    have ha : P * a.a + a.b ≤ a.label.role.mobile (2 * P * H) (energyOf P a) +
        a.label.role.collected (energyOf P a) := by
      cases a.label.role <;> simp [Role.mobile, Role.collected, energyOf]
    simp only [List.map_cons, List.sum_cons, mul_add]
    omega

variable [Field F] [Fintype E] {s} {s' : Stage F r t T V E X}

-- 读法：要证明的命题是 `s'.Room M N`。
theorem Reach.room (h : s.Reach P g H U s') (hp : 0 < P) (hh : 0 < H)
    (unique : ∀ v, ((s.ports v).map Prod.fst).Nodup) (M N : ℕ)
    (hm : ∀ v, (2 * P * H) * (s.scene.cell v).positions.length +
      (∑ e ∈ s.edges v, P * s.scene.level e) ≤ (2 * P * H) * M)
    (hn : ∀ v, (s.ledger P H).cost g v +
      (1 + 2 * g) * (∑ e ∈ s.edges v, P * s.scene.level e) ≤ N) : s'.Room M N := by
  intro v
  have he := h.budget
  have pt := congrFun h.ports_eq v
  change (s'.scene.cell v).ports = (s.scene.cell v).ports at pt
  constructor
  · have hs : (s'.scene.cell v).positions.length + (∑ e ∈ s.edges v, s.hits e) ≤
        (s.scene.cell v).positions.length + (∑ e ∈ s.edges v, s'.hits e) := by
      have := h.stations_le v
      simp only [Cell.positions, List.length_append, List.length_map, pt]
      omega
    have hsum : (2 * P * H) * (∑ e ∈ s.edges v, s'.hits e) ≤
        (∑ e ∈ s.edges v, P * s.scene.level e) + (2 * P * H) * (∑ e ∈ s.edges v, s.hits e) := by
      rw [mul_sum, mul_sum, ←sum_add_distrib]
      exact sum_le_sum fun e _ => le_trans (Nat.le_add_left _ _) (he.edge e)
    have hs' := Nat.mul_le_mul_left (2 * P * H) hs
    simp only [mul_add] at hs'
    have := hm v
    apply Nat.le_of_mul_le_mul_left _ (show 0 < 2 * P * H by positivity)
    omega
  · have ht := (he.site v).trans (hn v)
    have hcost := s'.energy_le P H v
    have ha := Nat.le_mul_of_pos_left (sumA (s'.scene.cell v).stations) hp
    have hb := Nat.le_mul_of_pos_left ((s'.ledger P H).mobile v) (show 0 < 1 + 2 * g by omega)
    have huniq : ((s'.ports v).map Prod.fst).Nodup := by rw [h.ports_eq]; exact unique v
    have hw : portWeight s'.scene.level (s'.scene.cell v).ports ≤
        (1 + 2 * g) * ∑ e ∈ s.edges v, (s'.ledger P H).seam e := by
      rw [s'.portWeight_eq_sum v huniq, h.edges_eq]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by omega))
      exact sum_le_sum fun e _ => Nat.le_mul_of_pos_left _ hp
    unfold Ledger.cost at ht
    unfold Cell.bigA
    omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# 区分私有残余和未改动的辅助标记点

新生成的残留标记读取一次穿越所创建的带编号连线，其第一球面能量为零。未带编号连线的残留标记从未移动或融合，因此两种能量仍满足原有上界。

**英文原文**

Distinguishing private residues from untouched auxiliary marks

A fresh residue reads the numbered wire created by a crossing. It has
zero first-sphere energy. Residues without a numbered wire have never
been moved or fused, so retain their original bounds on both energies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Finset Function
open scoped Classical

variable {F T V E X : Type} {r t P g H U : ℕ}

-- 读法：`thinStation` 表示以下条件：`u.label.role = .residue` 与 `∀ k ∈ u.label.reads, k.isLeft` 同时成立。
def thinStation (u : Station F r t (Tag V T) X) : Prop :=
  u.label.role = .residue ∧ ∀ k ∈ u.label.reads, k.isLeft

-- 读法：`thinCount` 的取值由 `(us.map fun u => if thinStation u then 1 else 0).sum` 给出。
def thinCount (us : List (Station F r t (Tag V T) X)) :=
  (us.map fun u => if thinStation u then 1 else 0).sum

-- 读法：`heavyCount` 的取值由 `(us.map fun u => if thinStation u then 0 else 1).sum` 给出。
def heavyCount (us : List (Station F r t (Tag V T) X)) :=
  (us.map fun u => if thinStation u then 0 else 1).sum

-- 读法：`thinCount us + heavyCount us` 等于 `us.length`。对 `us` 作归纳。
private theorem parts (us : List (Station F r t (Tag V T) X)) :
    thinCount us + heavyCount us = us.length := by
  induction us with
  | nil => rfl
  | cons a as ih =>
    unfold thinCount heavyCount at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split_ifs <;> omega

namespace Stage
variable [Field F] {s s' : Stage F r t T V E X}

-- 读法：结论为 `thinCount (s'.scene.cell z).stations ≤ thinCount (s.scene.cell z).stations ∧ heavyCount (s'.scene.cell z).stations + (∑ e ∈ s.edges z, s.hits e) ≤ heavyCount (s.scene.cell z).stations + ∑ e ∈ s.edges z, s'.hits e`。
theorem Step.counts (h : Step P g H U s s') (z : V) :
    thinCount (s'.scene.cell z).stations ≤ thinCount (s.scene.cell z).stations ∧
      heavyCount (s'.scene.cell z).stations + (∑ e ∈ s.edges z, s.hits e) ≤
        heavyCount (s.scene.cell z).stations + ∑ e ∈ s.edges z, s'.hits e := by
  have hsize := h.stations_le z
  have hp := parts (s.scene.cell z).stations
  have hp' := parts (s'.scene.cell z).stations
  suffices ht : thinCount (s'.scene.cell z).stations = thinCount (s.scene.cell z).stations ∨
      (thinCount (s'.scene.cell z).stations + 1 = thinCount (s.scene.cell z).stations ∧
        (s'.scene.cell z).stations.length < (s.scene.cell z).stations.length ∧ s'.hits = s.hits) by
    rcases ht with ht | ⟨ht, hl, he⟩
    · omega
    · rw [he]; omega
  cases h with
  | perm v ls hs =>
    left
    by_cases he : z = v
    · subst z
      simp only [put, Scene.put, update_self, thinCount]
      exact (hs.symm.map _).sum_eq
    · simp [put, Scene.put, he]
  | expire v c u hv ha =>
    left
    by_cases he : z = v <;> simp [freeze, put, Scene.put, he, hv, Cell.insert, thinCount, thinStation, ha]
  | merge v c a b n hv ha _ j q =>
    by_cases he : z = v
    · subst z
      have hb : ¬thinStation b := by simp [thinStation, ha]
      have hm : ¬thinStation (mergeAt a b (a.label.join b.label) q) := by
        by_cases h : a.label.role = .collector <;> simp [thinStation, mergeAt, Surface.merge, Tag.join, ha, h]
      by_cases ha' : thinStation a
      · right
        simp [put, Scene.put, hv, Cell.insert, thinCount, hb, hm, ha', add_comm]
        rfl
      · left
        simp [put, Scene.put, hv, Cell.insert, thinCount, hb, hm, ha']
        rfl
    · left
      simp [put, Scene.put, he]
  | cross v w j L R u a S i n hv hw ne _ _ ha =>
    left
    by_cases h : z = w
    · simp [advance, Scene.crossed, h, hw, Passage.right, Cell.insert, Cell.pull, Station.pull,
        Passage.arrives, transfer, Tag.take, thinCount, thinStation, Function.comp_def]
    by_cases h' : z = v
    · simp [advance, Scene.crossed, h', ne, hv, ha, Passage.left, Cell.insert, Cell.pull, Station.pull,
        Passage.leaves, residue, Tag.leave, thinCount, thinStation, Function.comp_def]
    simp [advance, Scene.crossed, h, h', Cell.pull, Station.pull, thinCount, thinStation, Function.comp_def]

-- 读法：对 `h` 作归纳。
theorem Reach.counts (h : s.Reach P g H U s') (v : V) :
    thinCount (s'.scene.cell v).stations ≤ thinCount (s.scene.cell v).stations ∧
      heavyCount (s'.scene.cell v).stations + (∑ e ∈ s.edges v, s.hits e) ≤
        heavyCount (s.scene.cell v).stations + ∑ e ∈ s.edges v, s'.hits e := by
  induction h with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | tail r q ih =>
    have hs := q.counts v
    rw [Reach.edges_eq r] at hs
    omega

-- 读法：对每个 `k ∈ s'.hidden`，`k` 不超过 `M`。对 `h` 作归纳。
theorem Reach.hidden_le (h : s.Reach P g H U s') {M : ℕ} (init : ∀ k ∈ s.hidden, k ≤ M)
    (bnd : ∀ y, s.Reach P g H U y → ∀ v a, a ∈ (y.scene.cell v).stations → a.b ≤ M) :
    ∀ k ∈ s'.hidden, k ≤ M := by
  induction h with
  | refl => exact init
  | tail r q ih =>
    cases q with
    | perm => exact ih
    | expire => exact ih
    | merge => exact ih
    | cross v w j L R u a S i n hv =>
      intro k hk
      rcases List.mem_cons.mp hk with he|he
      · rw [he]; exact bnd _ r v u (by simp [hv, Cell.insert])
      · exact ih k he

-- 读法：`Residues` 表示以下条件：对每个 `v u`，使 `u ∈ (s.scene.cell v).stations → u.label.role = .residue → if thinStation u then u.a ≤ A ∧ u.b ≤ B else u.a = 0` 成立。
/-- 剩余态要么满足初始辅助能量界，要么在第一个球面上的能量为零。读取编号连线即可区分这两种情况。

英文原文：A residue either has the initial auxiliary energy bounds or has
zero first-sphere energy. The numbered-wire read distinguishes them.
-/
def Residues (s : Stage F r t T V E X) (A B : ℕ) : Prop :=
  ∀ v u, u ∈ (s.scene.cell v).stations → u.label.role = .residue →
    if thinStation u then u.a ≤ A ∧ u.b ≤ B else u.a = 0

-- 读法：要证明的命题是 `s'.Residues A B`。对 `h` 分类讨论。
theorem Step.residues (h : Step P g H U s s') {A B : ℕ} (initial : s.Residues A B) :
    s'.Residues A B := by
  cases h with
  | perm v ls hs =>
    intro z (b : s.St) hb hr
    apply initial z b _ hr
    by_cases he : z = v
    · subst z
      simp only [put, Scene.put, update_self] at hb
      exact hs.mem_iff.mpr hb
    · simp [put, Scene.put, he] at hb
      exact hb
  | expire v c u hv =>
    intro z (b : s.St) hb hr
    apply initial z b _ hr
    by_cases he : z = v
    · subst z
      simp only [freeze, put, Scene.put, update_self, Cell.insert] at hb
      rcases List.mem_cons.mp hb with rfl | hm
      · cases hr
      · rw [hv]; exact List.mem_cons_of_mem _ hm
    · simp [freeze, put, Scene.put, he] at hb
      exact hb
  | merge v c a u n hv ha _ j q =>
    intro z (b : s.St) hb hr
    apply initial z b _ hr
    by_cases he : z = v
    · subst z
      simp only [put, Scene.put, update_self, Cell.insert] at hb
      rcases List.mem_cons.mp hb with rfl | hm
      · by_cases h : a.label.role = .collector <;>
          simp [mergeAt, Surface.merge, Tag.join, h, ha] at hr
      · rw [hv]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
    · simp [put, Scene.put, he] at hb
      exact hb
  | cross v w j L R u a S i n hv hw ne =>
    intro z (b : Station F r t (Tag V T) (Stack X t s.hidden × Level t u.b)) hb hr
    by_cases hz : z = w
    · subst z
      simp only [advance, Scene.crossed, update_self, Passage.right, Cell.insert, Cell.pull] at hb
      rcases List.mem_cons.mp hb with rfl | hm
      · cases hr
      -- 推导：从 `List.mem_map.mp hm` 中取出 `q, hq, rfl`。
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact initial w q (by rw [hw]; exact hq) hr
    by_cases hz' : z = v
    · subst z
      simp only [advance, Scene.crossed, update_of_ne ne, update_self, Passage.left, Cell.insert, Cell.pull] at hb
      rcases List.mem_cons.mp hb with rfl | hm
      · simp [thinStation, Passage.leaves, residue, Tag.leave]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        exact initial v q (by rw [hv]; exact List.mem_cons_of_mem _ hq) hr
    simp only [advance, Scene.crossed, update_of_ne hz, update_of_ne hz', Cell.pull] at hb
    -- 推导：从 `List.mem_map.mp hb` 中取出 `q, hq, rfl`。
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact initial z q hq hr

-- 读法：要证明的命题是 `s'.Residues A B`。对 `h` 作归纳。
theorem Reach.residues (h : s.Reach P g H U s') {A B : ℕ} (initial : s.Residues A B) :
    s'.Residues A B := by
  induction h with
  | refl => exact initial
  | tail _ q ih => exact q.residues ih

omit [Field F] in
-- 读法：`(thinStation u → u.a ≤ A ∧ u.b ≤ B)` 与 `(¬thinStation u → u.label.role ≠ .collector → u.a = 0)` 同时成立。
theorem Residues.classify {A B : ℕ} (h : s.Residues A B) (stop : s.Stopped) (v : V)
    (u : s.St) (hu : u ∈ (s.scene.cell v).stations) :
    (thinStation u → u.a ≤ A ∧ u.b ≤ B) ∧
    (¬thinStation u → u.label.role ≠ .collector → u.a = 0) := by
  refine ⟨fun ht => by simpa [ht] using h v u hu ht.1, fun ht hc => ?_⟩
  cases hr : u.label.role with
  | active i => exact (stop v u hu i hr).elim
  | collector => exact (hc hr).elim
  | residue => simpa [ht] using h v u hu hr

end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# 所有外部赋值共用一个标量的有限展开

**英文原文**

Finite expansions with a common scalar for all exterior assignments
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset
open scoped Classical
variable {F T V E X : Type} [Field F] [Fintype V] [Fintype E] {r t P : ℕ}

-- 读法：`traceStack t x l (fun y => a * f y)` 等于 `a * traceStack t x l f`。对 `l` 作归纳。
theorem trace_mul (t : ℕ) (x : X) (l : List ℕ) (a : F) (f : Stack X t l → F) :
    traceStack t x l (fun y => a * f y) = a * traceStack t x l f := by
  induction l with
  | nil => rfl
  | cons n l ih => simp only [traceStack, ← mul_sum, ih]

-- 读法：`traceStack t x l (fun y => ∑ i, f i y)` 等于 `∑ i, traceStack t x l (f i)`。对 `l` 作归纳。
theorem trace_sum {I : Type} [Fintype I] (t : ℕ) (x : X) (l : List ℕ)
    (f : I → Stack X t l → F) :
    traceStack t x l (fun y => ∑ i, f i y) = ∑ i, traceStack t x l (f i) := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [traceStack, ← ih]
    congr 1
    funext y
    exact sum_comm

namespace Stage

-- 读法：`observe` 的取值由 `traceStack t x s.hidden (s.scene.observe P v f)` 给出。
def observe (s : Stage F r t T V E X) (P : ℕ) (v : V) (f : Test F r t) (x : X) :=
  traceStack t x s.hidden (s.scene.observe P v f)

-- 读法：`s.observe P v forms` 等于 `s.value P`。
theorem observe_forms (s : Stage F r t T V E X) (v : V) : s.observe P v forms = s.value P := by
  unfold observe value
  rw [funext (s.scene.observe_forms v)]

-- 读法：`Terms` 表示以下条件：存在 `(I : Type) (_ : Fintype I) (c : I → F) (y : I → Stage F r t T V E X)`，`Fintype.card I` 不超过 `n ∧ (∀ i, good (y i)) ∧ ∀ x, f x = ∑ i, c i * (y i).value P x`。
/-- 阶段的有界线性组合，作为逐项的表恒等式成立。

英文原文：A bounded linear combination of stages, valid as a table identity.
-/
def Terms (P : ℕ) (good : Stage F r t T V E X → Prop) (n : ℕ) (f : X → F) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (c : I → F) (y : I → Stage F r t T V E X),
    Fintype.card I ≤ n ∧ (∀ i, good (y i)) ∧ ∀ x, f x = ∑ i, c i * (y i).value P x

namespace Terms
variable {good : Stage F r t T V E X → Prop} {n m : ℕ} {f : X → F}

-- 读法：要证明的命题是 `Terms P good m f`。
theorem mono (h : Terms P good n f) (e : n ≤ m) : Terms P good m f := by
  obtain ⟨I, fi, c, y, hc, hy, hf⟩ := h
  exact ⟨I, fi, c, y, hc.trans e, hy, hf⟩

-- 读法：要证明的命题是 `Terms P good 1 (s.value P)`。
theorem one {s : Stage F r t T V E X} (h : good s) : Terms P good 1 (s.value P) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => s, by simp, fun _ => h, by simp⟩

-- 读法：要证明的命题是 `Terms P good n (fun x => a * f x)`。
theorem scale (h : Terms P good n f) (a : F) : Terms P good n (fun x => a * f x) := by
  obtain ⟨I, fi, c, y, hc, hy, hf⟩ := h
  exact ⟨I, fi, fun i => a * c i, y, hc, hy, fun x => by simp only [hf, mul_sum, mul_assoc]⟩

-- 读法：要证明的命题是 `Terms P good (Fintype.card I * n) (fun x => ∑ i, c i * u i x)`。这里调用 `sum_le_sum`。
theorem combine {I : Type} [Fintype I] (c : I → F) (u : I → X → F)
    (hu : ∀ i, Terms P good n (u i)) : Terms P good (Fintype.card I * n) (fun x => ∑ i, c i * u i x) := by
  unfold Terms at hu ⊢
  choose A hA k y hk hy he using hu
  let _ := hA
  refine ⟨Σ i, A i, inferInstance, fun i => c i.1 * k i.1 i.2, fun i => y i.1 i.2,
    ?_, fun i => hy i.1 i.2, fun x => ?_⟩
  · rw [Fintype.card_sigma]
    simpa using sum_le_sum (s := univ) (fun i _ => hk i)
  · simp only [he, mul_sum, Fintype.sum_sigma, mul_assoc]

end Terms
end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# 位置及移动时钟的保持

**英文原文**

Preservation of positions and the moving clock
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Function
open scoped Classical
variable {F T V E X : Type} {r t P g H U : ℕ}

-- 读法：`(c.insert u).positions` 等于 `u.pos :: c.positions`。两端由定义化简为同一项。
@[simp] theorem Cell.positions_insert (c : Cell F r t T E X) (u : Station F r t T X) :
    (c.insert u).positions = u.pos :: c.positions := rfl

-- 读法：`(c.pull f q).positions` 等于 `c.positions`。
@[simp] theorem Cell.positions_pull {Y K : Type} (c : Cell F r t T E X) (f : Y → X) (q : T → K) :
    (c.pull f q).positions = c.positions := by simp [Cell.positions, Cell.pull, Station.pull, Function.comp_def]

namespace Stage

variable {s : Stage F r t T V E X}

-- 读法：要证明的命题是 `s.Valid U`。按 `b.label.role.clock = 0` 成立与否分情况。
private theorem valid_of_one (hd : ∀ v, (s.scene.cell v).positions.Nodup)
    (hc : ∀ v, ∃ u ∈ (s.scene.cell v).stations, u.label.role = .collector)
    (v : V) (u : s.St) (hu : u.label.role.clock ≤ U)
    (h : ∀ w b, b ∈ (s.scene.cell w).stations → b.label.role.clock ≠ 0 → w = v ∧ b = u) :
    s.Valid U := by
  refine ⟨hd, hc, ?_, ?_⟩
  · intro w b hb
    by_cases hz : b.label.role.clock = 0
    · simp [hz]
    rw [(h w b hb hz).2]
    exact hu
  · intro w b hb hb' w' a ha ha'
    obtain ⟨rfl, rfl⟩ := h w b hb hb'
    exact h w' a ha ha'

-- 读法：存在 `(v : V) (a b : List s.St) (u : s.St) (n : ℕ)`，`(s.scene.cell v).stations = a ++ u :: b` 与 `u.label.role = .active n ∧ n ≤ U ∧ s.Ready v (a ++ b)` 同时成立。
theorem Valid.choose (h : s.Valid U) (hs : ¬ s.Stopped) :
    ∃ (v : V) (a b : List s.St) (u : s.St) (n : ℕ),
      (s.scene.cell v).stations = a ++ u :: b ∧ u.label.role = .active n ∧
        n ≤ U ∧ s.Ready v (a ++ b) := by
  have pick : ∃ v u, u ∈ (s.scene.cell v).stations ∧ (∃ n, u.label.role = .active n) ∧
      (∀ w t, t ∈ (s.scene.cell w).stations → t.label.role.clock ≠ 0 → w = v ∧ t = u) := by
    by_cases pos : ∃ v u, u ∈ (s.scene.cell v).stations ∧ u.label.role.clock ≠ 0
    · obtain ⟨v, u, hu, hc⟩ := pos
      refine ⟨v, u, hu, ?_, h.focus v u hu hc⟩
      cases e : u.label.role <;> simp_all [Role.clock]
    · push Not at pos
      unfold Stopped at hs
      push Not at hs
      -- 推导：从 `hs` 中取出 `v, u, hu, n, hn`。
      obtain ⟨v, u, hu, n, hn⟩ := hs
      exact ⟨v, u, hu, ⟨n, hn⟩, fun w t ht hc => (hc (pos w t ht)).elim⟩
  obtain ⟨v, u, hu, ⟨n, hn⟩, hp⟩ := pick
  obtain ⟨a, b, hb⟩ := List.append_of_mem hu
  have hnd : u ∉ a ++ b := by
    have h' := (List.nodup_append.mp (h.distinct v)).1.of_map Station.pos
    rw [hb] at h'
    exact (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp h')).1
  refine ⟨v, a, b, u, n, hb, hn, by simpa [hn, Role.clock] using h.bound v u hu, ?_, ?_⟩
  · intro t ht
    by_contra h'
    -- 推导：记下中间结论 `he`：`t ∈ (s.scene.cell v).stations`。
    have he : t ∈ (s.scene.cell v).stations := by rw [hb]; exact List.perm_middle.mem_iff.mpr (.tail _ ht)
    exact hnd ((hp v t he h').2 ▸ ht)
  · intro w hw t ht
    by_contra h'
    exact hw (hp w t ht h').1

-- 读法：要证明的命题是 `(s.put v ⟨(s.scene.cell v).ports, ls⟩).Valid U`。按 `w = v` 成立与否分情况。
theorem Valid.perm (h : s.Valid U) (v : V) (ls : List s.St) (hl : (s.scene.cell v).stations.Perm ls) :
    (s.put v ⟨(s.scene.cell v).ports, ls⟩).Valid U := by
  let s' := s.put v ⟨(s.scene.cell v).ports, ls⟩
  have mem (w : V) (u : s.St) : u ∈ (s'.scene.cell w).stations ↔ u ∈ (s.scene.cell w).stations := by
    change u ∈ (update s.scene.cell v ⟨(s.scene.cell v).ports, ls⟩ w).stations ↔ _
    by_cases hv : w = v
    · subst w; simpa using hl.mem_iff.symm
    · simp [hv]
  change s'.Valid U
  refine ⟨?_, ?_, fun w u hu => h.bound w u ((mem w u).mp hu), ?_⟩
  · intro w
    by_cases hv : w = v
    · subst w
      simpa [s', put, Scene.put, Cell.positions] using
        ((hl.map Station.pos).append_right ((s.scene.cell v).ports.map Prod.snd)).nodup_iff.mp
          (h.distinct v)
    · simpa [s', put, Scene.put, hv] using h.distinct w
  · intro w
    -- 推导：从 `h.collector w` 中取出 `u, hu, he`。
    obtain ⟨u, hu, he⟩ := h.collector w
    exact ⟨u, (mem w u).mpr hu, he⟩
  · exact fun w u hu hc w' b hb hb' => h.focus w u ((mem w u).mp hu) hc w' b ((mem w' b).mp hb) hb'

-- 读法：要证明的命题是 `({s.put v (c.insert u) with expired := n}).Valid U`。按 `w = v` 成立与否分情况。
private theorem Valid.place (hs : s.Valid U) (v : V) (c : s.Ct) (u : s.St) (n : ℕ)
    (hr : s.Ready v c.stations) (hc : ∃ a ∈ (c.insert u).stations, a.label.role = .collector)
    (hd : (c.insert u).positions.Nodup) (hu : u.label.role.clock ≤ U) :
    ({s.put v (c.insert u) with expired := n}).Valid U := by
  refine valid_of_one ?_ ?_ v u hu ?_
  · intro w
    change (update s.scene.cell v (c.insert u) w).positions.Nodup
    by_cases e : w = v
    · subst w; simpa using hd
    · rw [update_of_ne e]; exact hs.distinct w
  · intro w
    change ∃ a ∈ (update s.scene.cell v (c.insert u) w).stations, a.label.role = .collector
    by_cases e : w = v
    · subst w; rw [update_self]; exact hc
    · rw [update_of_ne e]; exact hs.collector w
  · intro w b hb hn
    change b ∈ (update s.scene.cell v (c.insert u) w).stations at hb
    by_cases e : w = v
    · subst w
      rw [update_self] at hb
      rcases List.mem_cons.mp hb with h|h
      · exact ⟨rfl, h⟩
      · exact (hn (hr.1 _ h)).elim
    · rw [update_of_ne e] at hb
      exact (hn (hr.2 w e _ hb)).elim

-- 读法：要证明的命题是 `(s.freeze v c u).Valid U`。这里调用 `hs.place`。
theorem Valid.freeze (hs : s.Valid U) (v : V) (c : s.Ct) (u : s.St)
    (hv : s.scene.cell v = c.insert u) (hr : s.Ready v c.stations) :
    (s.freeze v c u).Valid U := by
  unfold Stage.freeze
  apply hs.place v c _ _ hr
  · exact ⟨_, List.mem_cons_self, rfl⟩
  · simpa only [hv, Cell.positions_insert] using hs.distinct v
  · exact Nat.zero_le U

variable [Field F]

-- 读法：要证明的命题是 `(s.put v (c.insert (mergeAt a b (a.label.join b.label) q))).Valid U`。这里调用 `hs.place`。
theorem Valid.merge (hs : s.Valid U) (v : V) (c : s.Ct) (a b : s.St) (n : ℕ)
    (hv : s.scene.cell v = (c.insert b).insert a) (ha : b.label.role = .active n)
    (hr : s.Ready v (a :: c.stations)) (q : ℤ × ℤ) :
    (s.put v (c.insert (mergeAt a b (a.label.join b.label) q))).Valid U := by
  let y := mergeAt a b (a.label.join b.label) q
  have ready : s.Ready v c.stations := ⟨fun t ht => hr.1 t (.tail _ ht), hr.2⟩
  apply hs.place v c y s.expired ready
  · by_cases h : a.label.role = .collector
    · exact ⟨y, List.mem_cons_self, by simp [y, mergeAt, Surface.merge, Tag.join, h]⟩
    obtain ⟨u, hu, hc⟩ := hs.collector v
    rw [hv] at hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact (h hc).elim
    rcases List.mem_cons.mp hu with rfl|hu
    · simp [ha] at hc
    · exact ⟨u, .tail _ hu, hc⟩
  · have h := hs.distinct v
    rw [hv, Cell.positions_insert, Cell.positions_insert] at h
    exact ((List.Sublist.refl _).cons b.pos |>.cons_cons a.pos).nodup h
  · have h := hs.bound v b (by rw [hv]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    change (a.label.join b.label).role.clock ≤ U
    unfold Tag.join
    split_ifs with he
    · simp [he, Role.clock]
    · exact h

-- 读法：要证明的命题是 `(s.advance a v w j L R S i).Valid U`。按 `k = v` 成立与否分情况。
theorem Valid.advance (hs : s.Valid U) (v w : V) (j : E) (L R : s.Sock)
    (u : s.St) (a : Passage P u) (S : Lower F r) (i : a.Branch) (n : ℕ)
    (hv : s.scene.cell v = (L.plug j a.z).insert u) (hw : s.scene.cell w = R.plug j a.y)
    (ne : v ≠ w) (ha : u.label.role = .active n) (hn : n < U) (ready : s.Ready v L.stations)
    (hl : i.2.1.val ∉ (L.plug j a.z).positions) (hr : a.root i.2.2.2 ∉ (R.plug j a.y).positions) :
    (s.advance a v w j L R S i).Valid U := by
  let s' := s.advance a v w j L R S i
  let l : s'.St := a.leaves (Tag.leave s.hidden.length) i
  let z : s'.St := a.arrives (u.label.take s.hidden.length) S i
  let f : Stack X t s'.hidden → Stack X t s.hidden := Prod.fst
  let c (i : V) := if i = v then L.plug j a.z else s.scene.cell i
  have old (k) : (c k).positions.Nodup ∧
      (∃ u ∈ (c k).stations, u.label.role = .collector) ∧ ∀ u ∈ (c k).stations, u.label.role.clock = 0 := by
    by_cases e : k = v
    · subst k
      unfold c; rw [ite_eq_left rfl]
      have h := hs.distinct v
      -- 推导：从 `hs.collector v` 中取出 `p, hp, ht`。
      obtain ⟨p, hp, ht⟩ := hs.collector v
      rw [hv, Cell.positions_insert] at h
      rw [hv] at hp
      rcases List.mem_cons.mp hp with rfl|hp
      · simp [ha] at ht
      · exact ⟨(List.nodup_cons.mp h).2, ⟨p, hp, ht⟩, ready.1⟩
    · unfold c; rw [ite_eq_right e]
      exact ⟨hs.distinct k, hs.collector k, ready.2 k e⟩
  let add (k : V) : List s'.St := if k = v then [l] else if k = w then [z] else []
  have eqn (k : V) : s'.scene.cell k =
      ⟨(c k).ports, add k ++ (c k).stations.map (Station.pull · f id)⟩ := by
    by_cases e : k = v
    · subst k
      simp only [s', Stage.advance, Scene.crossed, update_of_ne ne, update_self, c, add, ↓reduceIte]
      rfl
    by_cases e' : k = w
    · subst k
      simp only [s', Stage.advance, Scene.crossed, update_self, c, add, ite_eq_right e, ↓reduceIte, hw]
      rfl
    simp only [s', Stage.advance, Scene.crossed, update_of_ne e', update_of_ne e, c, add,
      ite_eq_right e, ite_eq_right e']
    rfl
  change s'.Valid U
  refine valid_of_one ?_ ?_ w z ?_ ?_
  · intro k
    rw [eqn]
    have h := (old k).1
    simp only [Cell.positions, List.map_append, List.map_map, Function.comp_def, Station.pull,
      List.append_assoc]
    change ((add k).map Station.pos ++ (c k).positions).Nodup
    by_cases e : k = v
    · subst k
      rw [show add v = [l] by simp [add]]
      change (i.2.1.val :: (c v).positions).Nodup
      exact h.cons (by simpa [c] using hl)
    by_cases e' : k = w
    · subst k
      rw [show add w = [z] by simp [add, e]]
      change (a.root i.2.2.2 :: (c w).positions).Nodup
      exact h.cons (by simpa [c, e, hw] using hr)
    simpa [add, e, e'] using h
  · intro k
    -- 推导：从 `(old k).2.1` 中取出 `u, hu, hr`。
    obtain ⟨u, hu, hr⟩ := (old k).2.1
    rw [eqn]
    exact ⟨u.pull f id, List.mem_append_right _ (List.mem_map_of_mem hu), hr⟩
  · change u.label.role.clock + 1 ≤ U
    simpa [ha, Role.clock] using hn
  · intro k b hb hb'
    rw [eqn] at hb
    rcases List.mem_append.mp hb with hm|hm
    · unfold add at hm
      split_ifs at hm with hv' hw'
      · rw [List.mem_singleton.mp hm] at hb'
        exact (hb' rfl).elim
      · exact ⟨hw', List.mem_singleton.mp hm⟩
      · contradiction
    -- 推导：从 `List.mem_map.mp hm` 中取出 `u, hu, rfl`。
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
      exact (hb' ((old k).2.2 u hu)).elim

end Stage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# 插值和新标记点的有限种选择

**英文原文**

Finite choices for interpolation and fresh marks
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T V E X : Type} {r t P g H U M N : ℕ}

-- 读法：`window` 的取值由 `P * N + N + g * (P * N + N + 2 * P * H) + 1` 给出。
def window (P g H N : ℕ) := P * N + N + g * (P * N + N + 2 * P * H) + 1

-- 读法：`(pairs P a b j).card` 不超过 `window P g H N`。这里调用 `card_image_le.trans`。
theorem pairs_card {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) {j : ℤ}
    (hj : j ≤ (g * (P * N + N + 2 * P * H) : ℕ)) :
    (pairs P a b j).card ≤ window P g H N := by
  unfold pairs
  dsimp only
  split_ifs with he
  · simp
  apply card_image_le.trans
  apply (card_filter_le _ _).trans
  rw [card_range]
  have e := Nat.mul_le_mul_left P ha
  unfold window
  omega

-- 读法：`Fintype.card (Σ i : S, Fin (orders seams collector D g L i.val))` 不超过 `M * window P g H N`。
theorem orders_card {D : F → ℕ} {seams S : Finset F} {collector : F} {L : ℕ}
    (hD : ∀ i, D i ≤ P * N + N) (hL : L ≤ P * N + N + 2 * P * H) (hS : S.card ≤ M) :
    Fintype.card (Σ i : S, Fin (orders seams collector D g L i.val)) ≤ M * window P g H N := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : S, window P g H N := by
      refine sum_le_sum fun i _ => ?_
      rw [Fintype.card_fin]
      have := hD i.val
      have := Nat.mul_le_mul_left g hL
      unfold orders window
      split_ifs <;> omega
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (window P g H N) hS

namespace Cell

variable (c : Cell F r t T E X)

-- 读法：`sites` 的取值由 `c.positions.toFinset` 给出。
def sites := c.positions.toFinset
-- 读法：`inserts` 的取值由 `(c.stations.map Station.pos).toFinset` 给出。
def inserts := (c.stations.map Station.pos).toFinset
-- 读法：`seams` 的取值由 `(c.ports.map Prod.snd).toFinset` 给出。
def seams := (c.ports.map Prod.snd).toFinset

-- 读法：`c.inserts` 包含于 `c.sites`。
-- 读法：`c.sites` 等于 `c.inserts ∪ c.seams`。
@[simp] theorem sites_eq : c.sites = c.inserts ∪ c.seams := by simp [sites, inserts, seams, positions]
theorem inserts_sub : c.inserts ⊆ c.sites := by rw [sites_eq]; exact subset_union_left
-- 读法：`c.seams` 包含于 `c.sites`。
theorem seams_sub : c.seams ⊆ c.sites := by rw [sites_eq]; exact subset_union_right
-- 读法：`u.pos` 属于 `c.inserts`。使用 `List.mem_toFinset.mpr` 给出的结论。
theorem mem_inserts {u} (h : u ∈ c.stations) : u.pos ∈ c.inserts :=
  List.mem_toFinset.mpr (List.mem_map_of_mem h)
-- 读法：`i.2` 属于 `c.seams`。使用 `List.mem_toFinset.mpr` 给出的结论。
theorem mem_seams {i} (h : i ∈ c.ports) : i.2 ∈ c.seams :=
  List.mem_toFinset.mpr (List.mem_map_of_mem h)
-- 读法：要证明的命题是 `Disjoint c.inserts c.seams`。这里调用 `Finset.disjoint_left.mpr`。
theorem disjoint (h : c.positions.Nodup) : Disjoint c.inserts c.seams := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (List.nodup_append.mp h).2.2 x (List.mem_toFinset.mp hx) x (List.mem_toFinset.mp hy) rfl

-- 读法：`c.orderA d ≤ N` 与 `c.orderB ≤ N` 同时成立。
theorem order_bounds (d : E → ℕ) (h : c.bigA d + sumB c.stations ≤ N) :
    c.orderA d ≤ N ∧ c.orderB ≤ N := by
  unfold orderA orderB bigA at *
  omega

-- 读法：`c.sites.card` 不超过 `M`。通过传递性衔接 `List.toFinset_card_le` 与 `h`。
theorem sizes (h : c.positions.length ≤ M) : c.sites.card ≤ M :=
  (List.toFinset_card_le _).trans h

end Cell

variable [Field F]
-- 读法：`x ^ (p ^ l) ∈ powered (p ^ l) A` 与 `x ∈ A` 等价。
theorem powered_iff (p l : ℕ) [ExpChar F p] (A : Finset F) (x : F) :
    x ^ (p ^ l) ∈ powered (p ^ l) A ↔ x ∈ A := by
  simp only [powered, mem_image, (power_injective p l).eq_iff, exists_eq_right]

-- 读法：`fresh` 的取值由 `univ \ s` 给出。
/-- 新的求值点必须避开本单元的全部既有位置，即使某些固定位置对当前球面是正则点也须排除。

英文原文：Positions for a fresh evaluation exclude the full cell, even
stationary positions that are regular for the particular sphere.
-/
def fresh [Fintype F] (s : Finset F) := univ \ s

omit [Field F] in
-- 读法：`M * (2 * N)` 严格小于 `(fresh s).card`。
theorem fresh_size [Fintype F] {s : Finset F} (hs : s.card ≤ M) (h : M * (2 * N + 1) < Fintype.card F) :
    M * (2 * N) < (fresh s).card := by
  rw [fresh, card_sdiff_of_subset (subset_univ s), card_univ]
  rw [mul_add, mul_one] at h
  omega

-- 读法：`breadth` 的取值由 `(M + 1) * window P g H N ^ 2 * (N + 1) * K ^ 2` 给出。
def breadth (P g H M N K : ℕ) := (M + 1) * window P g H N ^ 2 * (N + 1) * K ^ 2

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# 在固定的无自环布局中分离一条接缝

**英文原文**

Isolating a seam in a fixed loopless layout
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T V E X : Type} {r t g : ℕ}

namespace Socket

-- 读法：存在 `L : Socket F r t T E X`，`L.plug j z` 等于 `c`。
theorem exists_of_mem {c : Cell F r t T E X} {j : E} {z : F} (h : (j, z) ∈ c.ports) :
    ∃ L : Socket F r t T E X, L.plug j z = c := by
  obtain ⟨a, b, e⟩ := List.append_of_mem h
  exact ⟨⟨a, b, c.stations⟩, by simp [plug, ← e]⟩

variable (L : Socket F r t T E X) (j : E) (z : F)

-- 读法：`(j, z)` 属于 `(L.plug j z).ports`。
theorem mem : (j, z) ∈ (L.plug j z).ports := by simp [plug]

-- 读法：要证明的命题是 `Unused j L.base.ports`。这里调用 `List.nodup_cons.mp`。
theorem unused (h : ((L.plug j z).ports.map Prod.fst).Nodup) : Unused j L.base.ports := by
  have e := (List.perm_middle.map Prod.fst).nodup_iff.mp h
  intro k hk h'
  exact (List.nodup_cons.mp e).1 (List.mem_map.mpr ⟨k, hk, h'⟩)

-- 读法：`(L.plug j z).bigA d` 等于 `d j + L.base.bigA d`。
theorem bigA (d : E → ℕ) : (L.plug j z).bigA d = d j + L.base.bigA d := by
  simp only [plug, base, Cell.bigA, portWeight, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons]
  omega

-- 读法：`(L.plug j z).sites` 等于 `insert z L.base.sites`。
theorem sites : (L.plug j z).sites = insert z L.base.sites := by
  ext k
  simp [plug, base, Cell.sites, Cell.positions]

-- 读法：`z` 不属于 `L.base.sites`。这里调用 `List.perm_middle`。
theorem avoids (hd : (L.plug j z).positions.Nodup) : z ∉ L.base.sites := by
  have h : (L.plug j z).positions.Perm (z :: L.base.positions) := by
    simp only [Cell.positions, plug, base, List.map_append, List.map_cons, ← List.append_assoc]
    exact List.perm_middle
  exact fun h' => (List.nodup_cons.mp (h.nodup_iff.mp hd)).1 (List.mem_toFinset.mp h')

end Socket

-- 读法：存在 `(w : V) (y : F) (R : s.Sock)`，`v ≠ w` 与 `s.scene.cell w = R.plug i y ∧ (∀ k, k ≠ v → k ≠ w → Unused i (s.ports k))` 同时成立。
theorem Stage.Layout.partner {s : Stage F r t T V E X} {src dst : E → V}
    (hl : s.Layout src dst g) {v : V} {i : E} {z : F} (h : (i, z) ∈ s.ports v) :
    ∃ (w : V) (y : F) (R : s.Sock), v ≠ w ∧ s.scene.cell w = R.plug i y ∧
      (∀ k, k ≠ v → k ≠ w → Unused i (s.ports k)) := by
  have h₁ := (hl.incident v i).mp (List.mem_map.mpr ⟨_, h, rfl⟩)
  let w := if src i = v then dst i else src i
  have e (k : V) : i ∈ (s.ports k).map Prod.fst ↔ k = v ∨ k = w := by
    rw [hl.incident]
    unfold w
    grind
  have ne : v ≠ w := by have := hl.loopless i; unfold w; grind
  obtain ⟨⟨_, y⟩, hy, rfl⟩ := List.mem_map.mp ((e w).mpr (.inr rfl))
  obtain ⟨R, hr⟩ := Socket.exists_of_mem hy
  refine ⟨w, y, R, ne, hr.symm, fun k hv hw a ha he => ?_⟩
  exact ((e k).mp (List.mem_map.mpr ⟨a, ha, he⟩)).elim hv hw

variable [Field F]

-- 读法：要证明的命题是 `c.Fixed (p ^ l) ((powered (p ^ l) S).erase (z ^ (p ^ l))) B`。
theorem Cell.fixed_erase (c : Cell F r t T E X) (p l : ℕ) [ExpChar F p] (z : F)
    (hz : z ∉ c.sites) (S B : Finset F) (hS : c.sites ⊆ S) (hB : c.inserts ⊆ B) :
    c.Fixed (p ^ l) ((powered (p ^ l) S).erase (z ^ (p ^ l))) B := by
  have h (y : F) (hy : y ∈ c.sites) : y ^ (p ^ l) ∈ (powered (p ^ l) S).erase (z ^ (p ^ l)) :=
    mem_erase.mpr ⟨(power_injective p l).ne (fun e => hz (e ▸ hy)), mem_image_of_mem _ (hS hy)⟩
  exact ⟨fun _ hx => h _ (c.seams_sub (c.mem_seams hx)), fun _ hx =>
    ⟨h _ (c.inserts_sub (c.mem_inserts hx)), hB (c.mem_inserts hx)⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# 对普通连线取迹时使过程取得进展的局部变换

**英文原文**

Productive local changes under the trace on ordinary wires
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset Function Motion
open scoped Classical
variable {F T V E X : Type} [Field F] [Fintype V] [Fintype E] {r t P g H U M N : ℕ}
variable {s q : Stage F r t T V E X}

-- 读法：`Gain` 表示以下条件：`s.Reach P g H U q` 与 `q.Valid U ∧ q.potential U < s.potential U` 同时成立。
def Gain (s : Stage F r t T V E X) (P g H U : ℕ) (q : Stage F r t T V E X) : Prop :=
  s.Reach P g H U q ∧ q.Valid U ∧ q.potential U < s.potential U

-- 读法：要证明的命题是 `Terms P (s.Gain P g H U) k f`。
theorem Terms.transfer {f : X → F} {k : ℕ} (h : Terms P (q.Gain P g H U) k f)
    (he : Step P g H U s q) (hle : q.potential U = s.potential U) :
    Terms P (s.Gain P g H U) k f := by
  obtain ⟨I, fi, w, y, hc, hy, hf⟩ := h
  exact ⟨I, fi, w, y, hc, fun i => ⟨(hy i).1.head he, (hy i).2.1, (hy i).2.2.trans_eq hle⟩, hf⟩

-- 读法：`s.value P` 等于 `(s.freeze v c u).value P`。这里调用 `sum_congr`。
theorem freeze_value (v : V) (c : s.Ct) (u : s.St)
    (he : s.scene.cell v = c.insert u) : s.value P = (s.freeze v c u).value P := by
  have e (x : Stack X t s.hidden) : s.scene.value P x = (s.freeze v c u).scene.value P x := by
    unfold Scene.value eval
    apply sum_congr rfl
    intro y _
    refine prod_congr rfl fun k _ => ?_
    by_cases h : k = v
    · subst k
      simp only [freeze, put, Scene.put, update_self, he]
      rfl
    · simp only [freeze, put, Scene.put, update_of_ne h]
  unfold value
  rw [funext e]
  rfl

-- 读法：要证明的命题是 `Terms P (s.Gain P g H U) 1 (s.value P)`。这里调用 `Terms.one`。
theorem freeze_terms (hv : s.Valid U) (v : V) (c : s.Ct) (u : s.St)
    (he : s.scene.cell v = c.insert u) (ha : u.label.role = .active U)
    (hr : s.Ready v c.stations) : Terms P (s.Gain P g H U) 1 (s.value P) := by
  rw [freeze_value v c u he]
  exact Terms.one ⟨.single (.expire _ _ _ _ he ha hr), hv.freeze v c u he hr,
    s.potential_expire v c u he ha⟩

-- 读法：`reord` 的取值由 `s.put v ⟨(s.scene.cell v).ports, b ++ a ++ c⟩` 给出。
def reord (s : Stage F r t T V E X) (v : V) (a b c : List s.St) :=
  s.put v ⟨(s.scene.cell v).ports, b ++ a ++ c⟩

-- 读法：要证明的命题是 `Terms P (s.Gain P g H U) k (s.observe P v f)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem rotate_terms (v : V) (f : Test F r t) (hf : Signed f) (a b c : List s.St)
    (hs : (s.scene.cell v).stations = a ++ b ++ c) {k : ℕ}
    (ht : Terms P ((s.reord v a b c).Gain P g H U) k ((s.reord v a b c).observe P v f)) :
    Terms P (s.Gain P g H U) k (s.observe P v f) := by
  have e : s.observe P v f = fun x => (-1 : F) ^ (sumA a * sumA b + sumB a * sumB b) *
      (s.reord v a b c).observe P v f x := by
    funext x
    unfold observe
    rw [funext (s.scene.rotate v f hf a b c hs), trace_mul]
    rfl
  rw [e]
  have perm : (s.scene.cell v).stations.Perm (b ++ a ++ c) := by
    rw [hs]
    exact List.perm_append_comm.append_right c
  exact (ht.transfer (.perm _ _ _ perm) (s.potential_perm v _ perm)).scale _

-- 读法：结论为 `Terms P (s.Gain P g H U) (merges P a b ((s.scene.cell v).orderA s.scene.level) (s.scene.cell v).orderB j).card (s.observe P v (coefficient P A B a.pos j))`。
theorem merge_terms (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (hvalid : s.Valid U)
    (v : V) (c : s.Ct) (a b : s.St) (n : ℕ) (hv : s.scene.cell v = (c.insert b).insert a)
    (ha : b.label.role = .active n) (hr : s.Ready v (a :: c.stations))
    (A B : Finset F) (ha' : a.pos ^ P ∈ A) (hb' : a.pos ∈ B) (hm : b.pos ^ P ∉ A) (hm' : b.pos ∉ B)
    (hc : c.Fixed P (A.erase (a.pos ^ P)) (B.erase a.pos)) (j : ℤ)
    (hj : j ≤ if a.label.role = .collector then (g * (energyOf P b + 2 * P * H) : ℕ) else 0) :
    Terms P (s.Gain P g H U) (merges P a b ((s.scene.cell v).orderA s.scene.level)
      (s.scene.cell v).orderB j).card (s.observe P v (coefficient P A B a.pos j)) := by
  subst P
  let I := merges (p ^ l) a b ((s.scene.cell v).orderA s.scene.level) (s.scene.cell v).orderB j
  let z (q : I) := mergeAt a b (a.label.join b.label) q.val
  refine ⟨I, inferInstance, fun _ => 1, fun q => s.put v (c.insert (z q)), by simp [I], ?_, ?_⟩
  · intro q
    exact ⟨.single (.merge _ _ _ _ _ n hv ha hr j _ q.property hj),
      hvalid.merge v c a b n hv ha hr q.val, s.potential_merge _ _ _ _ _ hv ha rfl⟩
  · intro x
    unfold observe
    have h := s.scene.merge p l v c a b hv (a.label.join b.label) A B ha' hb' hm hm' hc j
    rw [funext h, trace_sum]
    simp only [one_mul]
    rfl

-- 读法：要证明的命题是 `Terms P (s.Gain P g H U) (Fintype.card a.Branch) (s.observe P v a.coeff)`。
theorem cross_terms (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (hvalid : s.Valid U)
    (v w : V) (j : E) (L R : s.Sock) (u : s.St) (a : Passage P u) (n : ℕ)
    (hv : s.scene.cell v = (L.plug j a.z).insert u) (hw : s.scene.cell w = R.plug j a.y)
    (ne : v ≠ w) (he : s.scene.level j = a.e) (hH : a.H = H) (ha : u.label.role = .active n)
    (hn : n < U) (hr : s.Ready v L.stations)
    (fits : a.Fits L.base R.base s.scene.level) (hl : Unused j L.base.ports) (hr' : Unused j R.base.ports)
    (other : ∀ z, z ≠ v → z ≠ w → Unused j (s.scene.cell z).ports)
    (freshL : ∀ i : a.U, i.val ∉ (L.plug j a.z).positions)
    (freshR : ∀ i : a.V, a.root i ∉ (R.plug j a.y).positions) :
    Terms P (s.Gain P g H U) (Fintype.card a.Branch) (s.observe P v a.coeff) := by
  let S := lowering F r
  let f := a.signed s.scene.level L R p l hP
  have hf := s.scene.cross a v w j L R (Tag.leave s.hidden.length)
    (u.label.take s.hidden.length) p l hP fits ne he hv hw hl hr' other
  refine ⟨a.Branch, inferInstance, f, s.advance a v w j L R S, le_rfl, fun i => ?_, fun x => ?_⟩
  · exact ⟨.single (.cross _ _ _ _ _ _ _ _ _ _ n hv hw ne he hH ha hn hr rfl),
      hvalid.advance v w j L R u a S i n hv hw ne ha hn hr (freshL _) (freshR _),
      s.potential_advance _ _ _ _ _ _ _ _ _ hv hw ne ha hn⟩
  · unfold observe
    rw [funext hf, trace_sum]
    exact sum_congr rfl fun i _ => trace_mul _ _ _ _ _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end
