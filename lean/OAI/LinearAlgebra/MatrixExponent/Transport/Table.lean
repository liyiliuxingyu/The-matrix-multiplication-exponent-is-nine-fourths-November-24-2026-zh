-- 本文件所属证明环节：以有限的局部核及端口表实现带标记记录的运输，使局部选择组合成指定置换并控制扩展规模。
import OAI.LinearAlgebra.MatrixExponent.Install.ControlWeight
import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Transport.System
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.Install.Products

/-!
# 有限组带掩码的局部核

**英文原文**

A finite menu of masked local kernels
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring Protocol Install Classical

-- 读法：在后续公式中，`Profile` 是 `Protocol.Frame F (Fin W ⊕ Fin W) (B p)` 的缩写。
abbrev Profile (F : Type) (p W : ℕ) := Protocol.Frame F (Fin W ⊕ Fin W) (B p)

variable {F : Type} {p W : ℕ}

-- 读法：`Profile.apply` 的取值由 `f z (Sum.elim (Function.curry x) (Function.curry y)) (Function.curry c)` 给出。
def Profile.apply (f : Profile F p W) (z : ℕ) (x y : Data W (2 ^ z)) (c : Channels p (2 ^ z)) : F :=
  f z (Sum.elim (Function.curry x) (Function.curry y)) (Function.curry c)

variable [Field F]

-- 读法：输入 `z x c` 时返回 `if valid = true ∧ ∀ j, active j ≠ true → ∀ i, c j i = false then f z x c else 0`。
def Profile.mask (f : Profile F p W) (valid : Bool) (active : B p → Bool) : Profile F p W :=
  fun z x c => if valid = true ∧ ∀ j, active j ≠ true → ∀ i, c j i = false then f z x c else 0

-- 读法：要证明的命题是 `Frame.Fast (f.mask valid active)`。用函数外延性比较等号两侧在 `z x c` 处的取值。
theorem Profile.mask_fast {f : Profile F p W} (hf : Frame.Fast f) (valid : Bool) (active : B p → Bool) :
    Frame.Fast (f.mask valid active) := by
  let k (_ : Fin W ⊕ Fin W → Bool) (c : B p → Bool) : F :=
    if valid = true ∧ ∀ j, active j ≠ true → c j = false then 1 else 0
  have eq : f.mask valid active = fun z x c => Frame.diagonal k z x c * f z x c := by
    funext z x c
    simp only [Profile.mask, Frame.diagonal, k, Finset.prod_boole, Finset.mem_univ, forall_const,
      ite_mul, one_mul, zero_mul]
    congr 1
    exact propext ⟨fun h i => ⟨h.1, fun j hj => h.2 j hj i⟩,
      fun h => ⟨(h 0).1, fun j hj i => (h i).2 j hj⟩⟩
  rw [eq]
  exact (Frame.fast_diagonal k).mul hf

-- 读法：在后续公式中，`dataPins` 是 `(Fin W × Fin (2 ^ z)) ⊕ (Fin W × Fin (2 ^ z)) ⊕ (B p × Fin (2 ^ z))` 的缩写。
private abbrev dataPins (p W z : ℕ) :=
  (Fin W × Fin (2 ^ z)) ⊕ (Fin W × Fin (2 ^ z)) ⊕ (B p × Fin (2 ^ z))

-- 读法：要证明的命题是 `Weight F (fun x : dataPins p W z → Bool => f.apply z (x ∘ Sum.inl) (fun i => x (.inr (.inl i))) (fun i => x (.inr (.inr i)))) m`。用函数外延性比较等号两侧在 `x` 处的取值。
private theorem apply_weight (f : Profile F p W) (z m : ℕ) (hf : Weight F (Frame.weight f z) m) :
    Weight F (fun x : dataPins p W z → Bool => f.apply z (x ∘ Sum.inl)
      (fun i => x (.inr (.inl i))) (fun i => x (.inr (.inr i)))) m := by
  let e : ((Fin W ⊕ Fin W) ⊕ B p) × Fin (2 ^ z) ≃ dataPins p W z :=
    ((Equiv.sumProdDistrib _ _ _).trans
      ((Equiv.sumProdDistrib _ _ _).sumCongr (.refl _))).trans (Equiv.sumAssoc _ _ _)
  convert hf.rename e using 1
  funext x
  unfold Profile.apply Frame.weight
  congr 1
  funext i j
  cases i <;> rfl

-- 读法：`C * Binary.scale z` 不超过 `2 ^ z * (100 + z) ^ (C + 3)`。这里调用 `Nat.mul_le_mul_left`。
private theorem absorb (C z : ℕ) : C * Binary.scale z ≤ 2 ^ z * (100 + z) ^ (C + 3) := by
  rw [Binary.scale, mul_left_comm, pow_add]
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _))
    (Nat.pow_le_pow_left (by omega) _)

-- 读法：证明中先建立 `hz`，即 `2 ^ z ≤ Binary.scale z`。
theorem profile_weight {l : ℕ} (f : B l → Profile F p W) (hf : ∀ i, Frame.Fast (f i)) :
    ∃ D : ℕ, ∀ z, Weight F (fun x : KernelPins (.addr l) p W (2 ^ z) → Bool =>
      (f ((Format.addr l).code.symm (x ∘ Sum.inl))).apply z (fun i => x (.inr (.inl i)))
        (fun i => x (.inr (.inr (.inl i)))) (fun i => x (.inr (.inr (.inr i)))))
      (2 ^ z * (100 + z) ^ D) := by
  choose c hc using hf
  let M := Finset.univ.sup c
  let C := Weight.switchCost l * (W + W + 2 ^ p + M + 1)
  refine ⟨C + 3, fun z => ?_⟩
  let g (y : (Format.addr l).pins → Bool) := f ((Format.addr l).code.symm y)
  have hw (y) : Weight F (Frame.weight (g y) z) (M * Binary.scale z) :=
    (hc _ z).mono (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ _)))
  have net := Weight.switch _ (fun y => apply_weight (g y) z _ (hw y))
  apply net.mono
  refine le_trans ?_ (absorb C z)
  -- 推导：记下中间结论 `hz`：`2 ^ z ≤ Binary.scale z`。
  have hz : 2 ^ z ≤ Binary.scale z := Nat.le_mul_of_pos_right _ (by positivity)
  have pos := Nat.two_pow_pos z
  have hd : Fintype.card (dataPins p W z) ≤ (W + W + 2 ^ p) * Binary.scale z := by
    simp only [dataPins, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ← add_mul, add_assoc]
    exact Nat.mul_le_mul_left _ hz
  unfold C
  rw [show Fintype.card (Format.addr l).pins = l from Format.width_addr l, mul_assoc]
  apply Nat.mul_le_mul_left
  rw [add_mul, add_mul, one_mul]
  omega

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# 受控传送中的外部变量与求和变量

**英文原文**

Exterior and summed-over variables of a controlled transport
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring

-- 读法：在后续公式中，`raw` 是 `⟨I → Bool, I, .refl _⟩` 的缩写。
abbrev raw (I : Type) [Fintype I] : Format := ⟨I → Bool, I, .refl _⟩
-- 读法：在后续公式中，`Packet` 是 `Format.vec (h + 1) (raw (Fin W × Fin z))` 的缩写。
abbrev Packet (h W z : ℕ) := Format.vec (h + 1) (raw (Fin W × Fin z))
-- 读法：在后续公式中，`Buffer` 是 `Format.vec (h + 1) (raw (B p × Fin z))` 的缩写。
abbrev Buffer (h p z : ℕ) := Format.vec (h + 1) (raw (B p × Fin z))
-- 读法：在后续公式中，`input` 是 `Tagged.inputs h (word n)` 的缩写。
abbrev input (h n : ℕ) := Tagged.inputs h (word n)
-- 读法：在后续公式中，`Exterior` 是 `Format.pair .bit (.pair (Perm h) (.pair (Packet h W z) (Packet h W z)))` 的缩写。
abbrev Exterior (h W z : ℕ) :=
  Format.pair .bit (.pair (Perm h) (.pair (Packet h W z) (Packet h W z)))

variable {F : Type} [Field F] {h n p W z : ℕ}

open Classical in
-- 读法：`Prepared` 的结果类型为 `Prop`。
def Prepared (F : Type) [Field F] (f : Val (input h n) → (Exterior h W z).obj) : Prop :=
  ∀ x, let y := f x
    (y.1 = true → Function.Bijective y.2.1) ∧
    Tagged.tag F h (word n) x () =
      if y.1 = true ∧ ∀ i, y.2.2.1 i = y.2.2.2 (Routing.inflate h y.2.1 i) then 1 else 0

-- 读法：在后续公式中，`System.latent` 是 `Format.pair (raw S.selector.pins) (Buffer h p z)` 的缩写。
abbrev System.latent (S : System F h p W z) :=
  Format.pair (raw S.selector.pins) (Buffer h p z)

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# 在每个槽位读取固定地址表

查表将远端位置和槽位转换为其在传输组内的地址。对每个比特只需进行一次并行间接读取。

**英文原文**

Reading a fixed address table at every slot

The table converts a remote site and slot into its address inside its
transport group. One simultaneous indirect read suffices for each bit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Install.BNet

open Coloring

-- 读法：对输入、输出的每组相容槽位编号，布尔位映射 `(fun (x : I × K → Bool) (z : I × J) => f (fun k => x (z.1, k)) z.2)` 均在 `F` 上有顶点数至多为 `(100000 * 2 ^ n * (1 + n) ^ 3 * (1 + Fintype.card J))` 的网络实现。
theorem table (F I K J : Type) [Field F] [Fintype I] [Fintype J] [Fintype K] (n : ℕ)
    (hi : Fintype.card I = 2 ^ n) (hk : Fintype.card K = n)
    (f : (K → Bool) → J → Bool) :
    BNet F (fun (x : I × K → Bool) (z : I × J) => f (fun k => x (z.1, k)) z.2)
      (100000 * 2 ^ n * (1 + n) ^ 3 * (1 + Fintype.card J)) := by
  classical
  let i : B n ≃ I := Fintype.equivOfCardEq (by simp [hi])
  let k : slots (word n) ≃ K := Fintype.equivOfCardEq (by simp [hk])
  let fill (x : I × K → Bool) (z : J × (B n ⊕ (B n × slots (word n)))) :=
    Sum.elim (fun l => f ((Control.decode n).symm l ∘ k.symm) z.1)
      (fun p => x (i p.1, k p.2)) z.2
  have dep : Depends fill 1 := by
    rintro ⟨j, l | ⟨l, b⟩⟩
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
    · exact ⟨{(i l, k b)}, by simp, fun _ _ e => e _ (by simp)⟩
  let e := (Equiv.prodComm J (B n)).trans (i.prodCongr (.refl J))
  have net := ((dep.bnet F).comp ((Control.read_net F n).copies J)).rename (.refl _) e
  convert net.mono (n := 100000 * 2 ^ n * (1 + n) ^ 3 * (1 + Fintype.card J)) (by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, card_slots, wd_word,
      hi, hk, localCost]
    ring_nf
    omega) using 1
  funext x ⟨l, j⟩
  change f (fun t => x (l, t)) j =
    f ((Control.decode n).symm (Control.decode n (fun r => x (i (i.symm l), k r))) ∘ k.symm) j
  simp [Function.comp_def]

end OAI.LinearAlgebra.MatrixExponent.Install.BNet
end

section
/-!
# 含隐变量的加权输出

为权重电路和输出电路分别复制外部比特与隐藏比特。取迹时只对隐藏比特求和一次。

**英文原文**

Weighted outputs with hidden variables

Duplicate the exterior and hidden bits for the weight and output
circuits. A trace sums over the hidden bits once.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring Install

variable {F : Type} [Field F] {m n : ℕ}

-- 读法：存在从 `.unit` 到 `a` 的网络，核为 `(fun _ _ => 1)`，顶点数为 `(wd a)`，系数取自 `F`。对 `a` 作归纳。
private theorem free (a : Wire) : Net F .unit a (fun _ _ => 1) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact .empty
  | pair a b ih hj =>
    change Net F .unit (.pair a b) _ (wd a + wd b)
    simpa only [one_mul] using (ih.par hj).pre (Rewire.unit' .unit)

-- 读法：存在 `v ≤ wd a + 2 * wd b + m + n`，存在从 `a` 到 `c` 的网络，核为 `(fun x y => ∑ z : Val b, if g (x, z) = y then f (x, z) else 0)`，顶点数为 `v`，系数取自 `F`。
private theorem project {a b c : Wire}
    {f : Val (.pair a b) → F} {g : Val (.pair a b) → Val c}
    (hf : Net F (.pair a b) .unit (fun x _ => f x) m) (hg : DNet F (.pair a b) c g n) :
    ∃ v ≤ wd a + 2 * wd b + m + n,
      Net F a c (fun x y => ∑ z : Val b, if g (x, z) = y then f (x, z) else 0) v := by
  obtain ⟨u, hu, H⟩ := DNet.dup F (.pair a b)
  obtain ⟨w, hw, G⟩ := hg
  have h := (H.comp (G.par hf)).post (.unit' c)
  have ht := ((h.par (free (F := F) b)).pre (.unit' _)).trace
  refine ⟨u + (w + m) + wd b, by simp only [wd] at hu; omega, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mul_one] using ht

-- 读法：`Weighted` 表示以下条件：`Weight F (f ∘ A.code.symm) m`。
def Weighted (F : Type) [Field F] (A : Format) (f : A.obj → F) (m : ℕ) : Prop :=
  Weight F (f ∘ A.code.symm) m

-- 读法：要证明的命题是 `Weighted F A (g ∘ f) (m + n)`。这里调用 `BNet.weight`。
theorem Weighted.pre {A D : Format} {f : A.obj → D.obj} {g : D.obj → F}
    (hg : Weighted F D g n) (hf : Circuit F A D f m) : Weighted F A (g ∘ f) (m + n) := by
  simpa only [Weighted, Function.comp_def, Equiv.symm_apply_apply] using BNet.weight hf hg

-- 读法：`names` 的取值由 `Fintype.equivOfCardEq (by simp)` 给出。
private noncomputable def names (I : Type) [Fintype I] : I ≃ slots (word (Fintype.card I)) :=
  Fintype.equivOfCardEq (by simp)

open Classical in
-- 读法：存在 `v ≤ wd (input h t) + 2 * L.width + m + n`，要证明的命题是 `G.Open F h t v s`。
theorem emit (G : Grid) {h t s : ℕ} (L : Format) [Fintype L.obj]
    {f : Val (input h t) × L.obj → F} {g : Val (input h t) × L.obj → G.Ports → Bool}
    (hf : Weighted F (.pair (.wire (input h t)) L) f m)
    (hg : Circuit F (.pair (.wire (input h t)) L) (raw G.Ports) g n)
    (hv : ∀ x z, f (x, z) ≠ 0 → G.Valid s (g (x, z)))
    (he : ∀ x, Tagged.tag F h (word t) x () = ∑ z, f (x, z) * G.close F (g (x, z))) :
    ∃ v ≤ wd (input h t) + 2 * L.width + m + n, G.Open F h t v s := by
  let a := input h t
  let b := word L.width
  let c := word (Fintype.card G.Ports)
  let i : L.pins ≃ slots b := names L.pins
  let j : G.Ports ≃ slots c := names G.Ports
  let e : Val b ≃ L.obj :=
    ((bits b).trans (Equiv.arrowCongr i.symm (.refl _))).trans L.code.symm
  let out (x : Val (.pair a b)) := (bits c).symm (g (x.1, e x.2) ∘ j.symm)
  have ho (x : Val (.pair a b)) : bits c (out x) ∘ j = g (x.1, e x.2) := by
    simp [out, Function.comp_def]
  let d := (Equiv.refl (slots a)).sumCongr i
  have eqn (x : Val (.pair a b)) :
      (Format.pair (.wire a) L).code.symm (bits (.pair a b) x ∘ d) = (x.1, e x.2) := by
    apply Prod.ext
    · exact (bits a).symm_apply_apply x.1
    · rfl
  -- 推导：从 `hf (.pair a b) d` 中取出 `u, hu, H`。
  obtain ⟨u, hu, H⟩ := hf (.pair a b) d
  have H' : Net F (.pair a b) .unit (fun x _ => f (x.1, e x.2)) u := by
    convert H using 1
    funext x _
    exact congrArg f (eqn x).symm
  have V : DNet F (.pair a b) c out n := by
    convert hg (.pair a b) c d j using 1
    funext x
    change _ = (bits c).symm (g ((Format.pair (.wire a) L).code.symm _) ∘ j.symm)
    rw [eqn]
  -- 推导：从 `project H' V` 中取出 `v, hle, hnet`。
  obtain ⟨v, hle, hnet⟩ := project H' V
  refine ⟨v, ?_, c, j, _, hnet, ?_, ?_⟩
  · simp only [a, b, wd_word] at hle
    omega
  · intro x y hy
    by_contra! ha
    apply hy
    apply Finset.sum_eq_zero
    intro z _
    split
    · rename_i hz
      by_contra! hn
      rw [← hz, ho] at ha
      exact ha (hv x _ hn)
    · rfl
  · intro x
    rw [he, ← e.sum_comp]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ho]

end OAI.LinearAlgebra.MatrixExponent.Transport
end

section
/-!
# 计算控制器及局部核的权重

**英文原文**

Evaluating the controller and the local kernel weights
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport.System
open Coloring Install

variable {F : Type} [Field F] {h p W z n m v : ℕ} (S : System F h p W z)

-- 读法：在后续公式中，`terminals` 是 `(Controls h p S.config).pair (Buffer h p z)` 的缩写。
abbrev terminals := (Controls h p S.config).pair (Buffer h p z)
-- 读法：在后续公式中，`frame` 是 `(Exterior h W z).pair S.terminals` 的缩写。
abbrev frame := (Exterior h W z).pair S.terminals
-- 读法：在后续公式中，`args` 是 `(Format.wire (input h n)).pair S.latent` 的缩写。
abbrev args (n : ℕ) := (Format.wire (input h n)).pair S.latent

-- 读法：`configure` 的取值由 `(prep a.1, S.dispatch ((prep a.1).2.1, S.selector.code.symm a.2.1), a.2.2)` 给出。
def configure (prep : Val (input h n) → (Exterior h W z).obj) (a : (S.args n).obj) :
    S.frame.obj :=
  (prep a.1, S.dispatch ((prep a.1).2.1, S.selector.code.symm a.2.1), a.2.2)

-- 读法：当 `x.1.1` 成立时取 `S.value x.2.1 x.1.2.2.1 x.1.2.2.2 x.2.2`，否则取 `0`。
def coeff (x : S.frame.obj) : F :=
  if x.1.1 then S.value x.2.1 x.1.2.2.1 x.1.2.2.2 x.2.2 else 0

-- 读法：在后续公式中，`before` 是 `(Exterior h W z).pair S.latent` 的缩写。
private abbrev before := (Exterior h W z).pair S.latent
-- 读法：在后续公式中，`call` 是 `(Perm h).pair S.selector` 的缩写。
private abbrev call := (Perm h).pair S.selector

-- 读法：在 `F` 上按格式 `(S.args n)`、`S.frame` 编码输入输出，映射 `(S.configure prep)` 的电路规模至多为 `(m + v + 20 * (S.frame.width + S.latent.width + S.call.width))`。
theorem configure_net {prep : Val (input h n) → (Exterior h W z).obj}
    (hf : Circuit F (.wire (input h n)) (Exterior h W z) prep m)
    (hd : Circuit F S.call (Controls h p S.config) S.dispatch v) :
    Circuit F (S.args n) S.frame (S.configure prep)
      (m + v + 20 * (S.frame.width + S.latent.width + S.call.width)) := by
  have init := hf.par (Circuit.id F S.latent)
  have get := Circuit.project (F := F) (A := S.before) (D := S.call)
    (f := fun x => (x.1.2.1, S.selector.code.symm x.2.1))
    (Sum.elim (fun i => .inl (.inr (.inl i))) (fun j => .inr (.inl j))) (by
      rintro x (i | j)
      · rfl
      · exact congrFun (S.selector.code.apply_symm_apply x.2.1) j)
  -- 推导：记下中间结论 `left`：`= Circuit.project (F`。
  have left := Circuit.project (F := F) (A := S.before) (D := Exterior h W z)
    (f := Prod.fst) Sum.inl (fun _ _ => rfl)
  have right := Circuit.project (F := F) (A := S.before) (D := Buffer h p z)
    (f := fun x => x.2.2) (fun i => .inr (.inr i)) (fun _ _ => rfl)
  apply (init.comp (left.pair ((get.comp hd).pair right))).mono
  simp only [Format.width_pair]
  omega

-- 读法：在后续公式中，`Queries` 是 `Unit ⊕ (Site h × KernelPins S.config p W z)` 的缩写。
private abbrev Queries := Unit ⊕ (Site h × KernelPins S.config p W z)

-- 读法：逐一匹配输入模式，例如 `.inl _`、`.inr (i, .inl j)`、`.inr (i, .inr (.inl j))`、`.inr (i, .inr (.inr (.inl j)))`。
private def source : S.Queries → S.frame.pins
  | .inl _ => .inl (.inl ())
  | .inr (i, .inl j) => .inr (.inl (i, .inl j))
  | .inr (i, .inr (.inl j)) => .inl (.inr (.inr (.inl (i, j))))
  | .inr (i, .inr (.inr (.inl j))) => .inl (.inr (.inr (.inr (i, j))))
  | .inr (i, .inr (.inr (.inr j))) => .inr (.inr (i, j))

omit [Field F] in
-- 读法：`Fintype.card S.Queries` 不超过 `S.frame.width`。
private theorem queries_le : Fintype.card S.Queries ≤ S.frame.width := by
  simp only [Queries, KernelPins, Format.width, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_unit, Fintype.card_fin]
  ring_nf
  omega

-- 读法：要证明的命题是 `Weighted F S.frame S.coeff (3 * S.frame.width + 16 + 2 ^ (h + 1) * m)`。
theorem coeff_net (hS : Weight F S.localWeight m) :
    Weighted F S.frame S.coeff (3 * S.frame.width + 16 + 2 ^ (h + 1) * m) := by
  have flag := Weight.dense F Unit (fun x => if x () then 1 else 0)
  have net := (flag.parallel (hS.prod (h + 1))).pull S.source
  have hw : S.frame.width + 2 * Fintype.card S.Queries + (8 * 2 ^ 1 + 2 ^ (h + 1) * m) ≤
      3 * S.frame.width + 16 + 2 ^ (h + 1) * m := by
    have := S.queries_le
    omega
  unfold Weighted
  convert net.mono hw using 1
  funext x
  simp only [ite_mul, one_mul, zero_mul, Function.comp_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Transport.System
end
