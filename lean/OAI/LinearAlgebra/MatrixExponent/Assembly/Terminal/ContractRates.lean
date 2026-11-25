-- 本文件所属证明环节：把一轮网络变换拆成可编码的宿主、端口、地址、控制和数据记录，拼装同一固定图上可复用的网络，估计附加容量与运输成本。
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound

/-!
# 配对终端连线的两个接触

增加一位来区分宿主自身与带编号的邻居。指向自身宿主的各位置分别保持不动，未使用的位置也包括在内。

**英文原文**

Pairing the two contacts of a terminal wire

One extra bit distinguishes self from a numbered neighbor.
Positions naming their own host, including unused positions,
are fixed individually.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

-- 读法：`hop` 的结果类型为 `Option (B d) ↪ B (d + 1)`。
def hop {d : ℕ} : Option (B d) ↪ B (d + 1) :=
  (⟨fun i => i.elim (0, 0) (fun j => (j, 1)), by
    rintro (_|i) (_|j) h
    · rfl
    · exact ((by decide : (0 : B 1) ≠ 1) (congrArg Prod.snd h)).elim
    · exact ((by decide : (1 : B 1) ≠ 0) (congrArg Prod.snd h)).elim
    · exact congrArg some (Prod.mk.inj h).1⟩ : Option (B d) ↪ B d × B 1).trans
      (Match.rowIndex d 1).symm.toEmbedding

-- 读法：`reverseHop` 的取值由 `(Format.addr (d + 1)).code.symm fun i => decide (∃ j, p j = true ∧ (Format.addr (d + 1)).code (hop (some j)) i = true)` 给出。
def reverseHop (d : ℕ) (p : B d → Bool) : B (d + 1) :=
  (Format.addr (d + 1)).code.symm fun i =>
    decide (∃ j, p j = true ∧ (Format.addr (d + 1)).code (hop (some j)) i = true)

-- 读法：`reverseHop d p` 等于 `hop (some j)`。这里调用 `Format.addr`。
private theorem reverse_of_unique {d : ℕ} {p : B d → Bool} (j : B d)
    (h : ∀ k, p k = true ↔ k = j) : reverseHop d p = hop (some j) := by
  unfold reverseHop
  apply (Format.addr (d + 1)).code.symm_apply_eq.mpr
  funext i
  simp [h]

variable {F : Type} (S : Scheme F) (r : S.format.obj)
local notation "idx" => Match.rowIndex S.m (S.d + 1)

-- 读法：在后续公式中，`Flags` 是 `Format.vec S.m (.vec S.d .bit)` 的缩写。
abbrev Flags := Format.vec S.m (.vec S.d .bit)
-- 读法：输入 `i j` 时返回 `decide ((r i).1 j = i)`。
def flags : (Flags S).obj := fun i j => decide ((r i).1 j = i)
-- 读法：在后续公式中，`contact` 是 `(idx).symm (v, hop i)` 的缩写。
abbrev contact (v : B S.m) (i : Option (B S.d)) := (idx).symm (v, hop i)

-- 读法：`extended` 的取值由 `let j := Match.rowIndex S.d 1 i if j.2 = 1 then (r v).1 j.1 else v` 给出。
def extended (v : B S.m) (i : B (S.d + 1)) :=
  let j := Match.rowIndex S.d 1 i
  if j.2 = 1 then (r v).1 j.1 else v

-- 读法：`extended S r v (hop none)` 等于 `v`。
theorem extended_self (v : B S.m) : extended S r v (hop none) = v := by
  change extended S r v ((Match.rowIndex _ _).symm (0, 0)) = v
  simp [extended]

-- 读法：`extended S r v (hop (some j))` 等于 `(r v).1 j`。
theorem extended_peer (v : B S.m) (j : B S.d) : extended S r v (hop (some j)) = (r v).1 j := by
  change extended S r v ((Match.rowIndex _ _).symm (j, 1)) = _
  simp only [extended, Equiv.apply_symm_apply, ite_true]

-- 读法：本声明给出 `perm` 的构造。
def perm (i : B (S.m + (S.d + 1))) :=
  let x := idx i
  let y := extended S r x.1 x.2
  (idx).symm (y, if y = x.1 then x.2 else reverseHop S.d (fun j => decide ((r y).1 j = x.1)))

-- 读法：`perm S r (contact S v none)` 等于 `contact S v none`。
theorem perm_self (v : B S.m) : perm S r (contact S v none) = contact S v none := by
  simp only [perm, contact, Equiv.apply_symm_apply, extended_self, ite_true]

variable (hr : Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) r)
include hr

-- 读法：`perm S r (contact S v (some i))` 等于 `contact S w (some j)`。这里调用 `reverse_of_unique`。
theorem perm_link (v w : B S.m) (i j : B S.d) (h : v ≠ w) (hv : (r v).1 i = w) (hw : (r w).1 j = v) :
    perm S r (contact S v (some i)) = contact S w (some j) := by
  have he := hr v i (hv.trans_ne h.symm)
  rw [hv] at he
  have eq : reverseHop S.d (fun l => decide ((r w).1 l = v)) = hop (some j) := by
    apply reverse_of_unique
    intro k
    rw [decide_eq_true_eq]
    exact ⟨fun h => he.unique h hw, fun h => h ▸ hw⟩
  simp only [perm, contact, Equiv.apply_symm_apply, extended_peer, hv, ite_eq_right h.symm, eq]

-- 读法：要证明的命题是 `Function.Involutive (perm S r)`。按 `extended S r v j = v` 成立与否分情况。
theorem perm_involutive : Function.Involutive (perm S r) := by
  intro i
  obtain ⟨⟨v, j⟩, rfl⟩ := (idx).symm.surjective i
  by_cases he : extended S r v j = v
  · have hh : perm S r ((idx).symm (v, j)) = (idx).symm (v, j) := by
      simp only [perm, Equiv.apply_symm_apply, he, ite_true]
    rw [hh, hh]
  let a := Match.rowIndex S.d 1 j
  have ht : a.2 = 1 := by
    by_contra hn
    exact he (ite_eq_right hn)
  have hj : j = hop (some a.1) := (Match.rowIndex S.d 1).eq_symm_apply.mpr (Prod.ext rfl ht)
  rw [hj, extended_peer] at he
  obtain ⟨k, hk, _⟩ := hr v a.1 he
  rw [hj]
  change perm S r (perm S r (contact S v (some a.1))) = _
  rw [perm_link S r hr _ _ _ k (Ne.symm he) rfl hk, perm_link S r hr _ _ _ _ he hk rfl]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 从同时给出的邻点标志得到反向地址

**英文原文**

A reverse address from simultaneous neighbor flags
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Install
open scoped Classical

-- 读法：在 `F` 上按格式 `(.vec d .bit)`、`.bit` 编码输入输出，映射 `(fun x => decide (∃ i, x i = true))` 的电路规模至多为 `(2 * 2 ^ d + 1)`。用函数外延性比较等号两侧在 `x u` 处的取值。
private theorem any_net (F : Type) [Field F] (d : ℕ) :
    Circuit F (.vec d .bit) .bit (fun x => decide (∃ i, x i = true)) (2 * 2 ^ d + 1) := by
  have h := (BNet.any F (B d)).rename (Equiv.prodUnique (B d) Unit).symm (.refl _)
  rw [Fintype.card_fin] at h
  unfold Circuit
  convert h using 1
  funext x u
  change decide (∃ i, x (i, ()) = true) = _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  rfl

-- 读法：在 `F` 上按格式 `(.vec d .bit)`、`(.addr (d + 1))` 编码输入输出，映射 `(reverseHop d)` 的电路规模至多为 `(100 * (2 ^ d) ^ 2)`。
theorem reverseNet (F : Type) [Field F] (d : ℕ) :
    Circuit F (.vec d .bit) (.addr (d + 1)) (reverseHop d) (100 * (2 ^ d) ^ 2) := by
  let X := Format.vec d .bit
  let Y := Format.vec d X
  let A := Format.addr (d + 1)
  have hd : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  let e : A.pins ↪ B d := (Fintype.equivFin A.pins).toEmbedding.trans
    (Fin.castLEEmb ((Format.width_addr _).le.trans hd))
  let mask (i j : B d) := Function.extend e (A.code (hop (some j))) (fun _ => false) i
  let send (x : X.obj) : Y.obj := fun i j => x j && mask i j
  let take (x : X.obj) : A.obj := A.code.symm (fun i => x (e i))
  have hs : Depends (Y.code ∘ send ∘ X.code.symm) 1 := by
    rintro ⟨i, j, t⟩
    exact ⟨{(j, ())}, by simp, fun _ _ h => congrArg (· && mask i j) (h (j, ()) (by simp))⟩
  have hr : Circuit F X A take (X.width + 2 * A.width) :=
    Circuit.project (fun i => (e i, ())) (fun x i => congrFun (A.code.apply_symm_apply _) i)
  let row (x : X.obj) := decide (∃ j, x j = true)
  -- 推导：记下中间结论 `ho`：`Circuit F Y X (fun x i => row (x i)) (2 ^ d * (2 * 2 ^ d + 1))`。
  have ho : Circuit F Y X (fun x i => row (x i)) (2 ^ d * (2 * 2 ^ d + 1)) :=
    Circuit.map _ (fun _ => any_net F d)
  have hm : Circuit F X Y send (X.width + 34 * Y.width) := hs.bnet F
  have eqn : take ∘ (fun x i => row (x i)) ∘ send = reverseHop d := by
    funext x
    apply congrArg A.code.symm
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [row, send, mask, e.injective.extend_apply, A]
  rw [← eqn]
  refine ((hm.comp ho).comp hr).mono ?_
  simp only [X, Y, A, Format.width_vec]
  rw [Format.width_bit, Format.width_addr, mul_one]
  -- 推导：记下中间结论 `hp`：`1 ≤ 2 ^ d`。
  have hp : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  nlinarith

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 检验一个候选传送

两组存储区都可以包含任意比特。对所有输入都保持精确的示性函数值，包括局部控制记录格式不正确的输入。

**英文原文**

Testing one proposed transfer

Both banks may contain arbitrary bits. Retain the exact indicator
on all inputs, including malformed local control records.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Rounds.Contraction
open scoped Classical

variable {F : Type} [Field F] (W : Prices F)
variable {m k k' V V' p w n : ℕ}
local notation "Z" => Fmt.payload m V k
local notation "X" => Fmt.payload m V' k'
local notation "C" => PeerLayout.S m V k m V' k' (2 ^ p)
local notation "U" => Payload.Script m m p w n

-- 读法：`checker` 的取值由 `(C).kernel F (Payload.Script.decode le_rfl z.1, z.2) x` 给出。
def checker (z : ((U).pair Z).obj) (x : (X).obj) : F :=
  (C).kernel F (Payload.Script.decode le_rfl z.1, z.2) x

-- 读法：要证明的命题是 `Kernel F u L ((U).pair Z) X checker (W.shipment (Z).width m V k m V' k' p w n)`。
theorem checker_net {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (hm : 1 ≤ m)
    (ht : 2 ^ p * ((max k k' + 1) * (2 ^ m + 2 ^ m)) < 2 ^ W.w) :
    Kernel F u L ((U).pair Z) X checker (W.shipment (Z).width m V k m V' k' p w n) := by
  let v := (Payload.Script.item w p n).width + W.w ^ W.power
  have hm' : m ≤ W.w := ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (((Nat.le_add_left _ _).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))).trans_lt ht)).le
  obtain ⟨a, ha, tag⟩ := W.tag m v hm hm' (Nat.le_add_left ..)
  have decode := Payload.Script.decode_net (L := L) (V := V) (k := k) (V' := V') (k' := k')
    (w := w) (n := n) hu (le_rfl : 2 ^ p ≤ 2 ^ p) tag tag (Nat.le_add_right _ _)
  have kernel : Kernel F u L ((C).control.pair Z) X ((C).kernel F)
      (W.transferCost m V k m V' k' p) := by
    -- 推导：记下中间结论 `h`：`= payload_kernel (K`。
    have h := payload_kernel (K := F) (L := L) m V k m V' k' (2 ^ p) hu ht W.tag
    simp only [payloadChannels] at h
    unfold PeerLayout.S PeerLayout.P Prices.transferCost
    exact h
  have go := (decode.par (Map.circuit (L := L) hu (Circuit.id F Z))).then_kernel kernel
  have hb : Payload.Script.cost m k m k' p w v a a ≤
      Payload.Script.cost m k m k' p w v (W.W * (2 ^ m * v)) (W.W * (2 ^ m * v)) := by
    unfold Payload.Script.cost; gcongr
  refine go.mono ?_
  rw [add_comm _ (4 * (Z).width)]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right hb _) _) _

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 在同一记录带上封闭两项检验与站点字典

**英文原文**

Closing the two checks and the station dictionary on a common tape
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Rounds.Contraction
open scoped Classical

variable {F : Type} [Field F] (S : Scheme F)

-- 读法：在后续公式中，`instruction` 是 `((Payload.Script S.m S.m p w n).pair (Payload.Script S.m S.m 0 w n)).pair (Dictionary.headers S V t)` 的缩写。
abbrev instruction (V t p w n : ℕ) :=
  ((Payload.Script S.m S.m p w n).pair (Payload.Script S.m S.m 0 w n)).pair (Dictionary.headers S V t)

-- 读法：`price` 的构造用到 `Fmt.payload`、`W.shipment`、`Dictionary.price`。
def price (W : Prices F) (S : Scheme F) (V t V' k' p w n : ℕ) :=
  let k := height S t
  let a := (Fmt.payload S.m V k).width
  W.shipment a S.m V k S.m V k p w n + W.shipment a S.m V k S.m V' k' 0 w n +
    Dictionary.price S V t + 64 * ((instruction S V t p w n).width + (Fmt.payload S.m V' k').width + a)

variable (V t V' k' p w n : ℕ)
local notation "J" => instruction S V t p w n
local notation "E" => Fmt.payload S.m V' k'
local notation "Z" => Fmt.payload S.m V (height S t)

-- 读法：`value` 的取值由 `∑ z : Tape S V t, checker (F := F) (x.1.1, z) z * checker (F := F) (x.1.2, z) y * Dictionary.weight S V t x.2 z` 给出。
def value (x : (J).obj) (y : (E).obj) :=
  ∑ z : Tape S V t, checker (F := F) (x.1.1, z) z * checker (F := F) (x.1.2, z) y *
    Dictionary.weight S V t x.2 z

-- 读法：要证明的命题是 `Kernel F u L ((J).pair E) (.wire .unit) (fun z _ => value S V t V' k' p w n z.1 z.2) (price W S V t V' k' p w n)`。这里调用 `Nat.mul_le_mul_left`。
theorem evaluate (W : Prices F) {u : ℕ} {L : Set (Table F)}
    (hu : 3 ≤ u) (hm : 1 ≤ S.m)
    (ht : 2 ^ p * ((max (height S t) k' + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w)
    (size : Dictionary.arity S t ≤ u) (label : Dictionary.label S t ∈ L) :
    Kernel F u L ((J).pair E) (.wire .unit)
      (fun z _ => value S V t V' k' p w n z.1 z.2) (price W S V t V' k' p w n) := by
  let k := height S t
  have hc : 2 ^ p * ((max k k + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w := by
    refine lt_of_le_of_lt ?_ ht
    rw [max_self]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.succ_le_succ (le_max_left ..)))
  -- 推导：记下中间结论 `hd`：`2 ^ 0 * ((max k k' + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w`。
  have hd : 2 ^ 0 * ((max k k' + 1) * (2 ^ S.m + 2 ^ S.m)) < 2 ^ W.w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.two_pow_pos _)) ht
  have left := checker_net (V := V) (V' := V) (w := w) (n := n) (L := L) W hu hm hc
  have right := checker_net (V := V) (V' := V') (w := w) (n := n) (L := L) W hu hm hd
  have station := Dictionary.realize (V := V) hu size label
  have h := Kernel.contract hu left right station
  unfold price
  dsimp only
  rw [Format.width_pair, Format.width_pair]
  exact h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 从原始控制行计算完整的字典记录头向量

**英文原文**

Computing the complete dictionary header vector from the original control rows
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header

open Coloring Dictionary
open scoped Classical
variable {F : Type} [Field F] (S : Scheme F) (V t : ℕ)

-- 读法：`arity` 的取值由 `(key S).width + (header S).width` 给出。
def arity := (key S).width + (header S).width
-- 读法：`mapLabel` 的取值由 `lookup F A B (fun x y => if f x = y then 1 else 0)` 给出。
private def mapLabel (A B : Format) (f : A.obj → B.obj) :=
  lookup F A B (fun x y => if f x = y then 1 else 0)

-- 读法：`label` 的取值由 `mapLabel (F:=F) (key S) (header S) (select S)` 给出。
def label := mapLabel (F:=F) (key S) (header S) (select S)

-- 读法：在后续公式中，`names` 是 `Format.vec S.m (.vec (n S) (key S))` 的缩写。
abbrev names := Format.vec S.m (.vec (n S) (key S))
-- 读法：在后续公式中，`lines` 是 `Format.vec S.m (line S)` 的缩写。
abbrev lines := Format.vec S.m (line S)
-- 读法：`rowCost` 的取值由 `4 * (S.format.width + 34 * (names S).width) + 2 ^ S.m * (2 ^ (n S) * (1 + (key S).width + (header S).width))` 给出。
def rowCost := 4 * (S.format.width + 34 * (names S).width) +
  2 ^ S.m * (2 ^ (n S) * (1 + (key S).width + (header S).width))

variable {S V t} {u v c : ℕ} {L : Set (Table F)}

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `S.format` 到 `(lines S)` 实现映射 `(row S)` 的开销至多为 `(rowCost S)`。这里调用 `Window.Tile.project_const`。
theorem rows_net (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L) :
    Map F u L S.format (lines S) (row S) (rowCost S) := by
  have a : Circuit F S.format (names S) (labels S) (S.format.width + 34 * (names S).width) := by
    apply Window.Tile.project_const
    rintro ⟨i, j, k|k⟩
    · exact .inl ⟨(i, .inr ((Match.rowIndex S.h S.k j).1, k)), fun _ => rfl⟩
    · exact .inr ⟨(Format.addr S.k).code (Match.rowIndex S.h S.k j).2 k, fun _ => rfl⟩
  have b : Map F u L (key S) (header S) (select S) (1 + (key S).width + (header S).width) :=
    Kernel.lookup ha hl
  exact (Map.circuit hu a).comp (Map.vec _ fun _ : B S.m => Map.vec _ fun _ : B (n S) => b)

-- 读法：映射 `f` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (0) * (100 + (δ)) ^ (2)` 为上界。
private theorem unary {A : Format} {δ : ℕ} (hw : A.width ≤ δ) (f : Bool → A.obj) :
    Cheap F 0 δ .bit A f 2 := by
  have dep : Install.Depends (A.code ∘ f ∘ Format.bit.code.symm) 1 := by
    intro i
    refine ⟨Finset.univ, le_rfl, fun x y he => ?_⟩
    rw [funext (fun j => he j (Finset.mem_univ _))]
  refine ⟨_, dep.bnet F, ?_⟩
  change 1 + A.width + (1 + 34 * A.width) ≤ _
  ring_nf
  omega

-- 读法：`scale` 的取值由 `wordSize S t + (header S).width` 给出。
def scale (S : Scheme F) (t : ℕ) := wordSize S t + (header S).width

-- 读法：映射 `(fun x => (length S t x, pack S x))` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ ((n S)) * (100 + ((scale S t))) ^ (50)` 为上界。
private theorem host :
    Cheap F (n S) (scale S t) (line S) (.pair (.addr (wordSize S t)) (line S))
      (fun x => (length S t x, pack S x)) 50 := by
  let δ := scale S t
  have hn : n S + 1 ≤ δ := by unfold δ scale wordSize; omega
  have he : S.e + t + 1 ≤ δ := by unfold δ scale wordSize; omega
  have hh : (header S).width ≤ δ := Nat.le_add_left _ _
  have hw : (header S).width ≤ 2 ^ 0 * (100 + δ) ^ 1 := by simp only [pow_zero, one_mul, pow_one]; omega
  have get := (Cheap.id F hw).fst
  have fl := get.comp (unary (F:=F) (A:=.addr 1) (δ:=δ) (by rw [Format.width_addr]; omega) flag)
  have sz := get.comp (unary (F:=F) (A:=.addr (S.e + t + 1)) (by rw [Format.width_addr]; exact he) (amount S t))
  have len := (Cheap.map _ fun _ : B (n S) => sz).comp ((cheap_total F (n S) (S.e + t + 1)).widen he)
  have σ := (Cheap.map _ fun _ : B (n S) => fl).comp ((cheap_order F (n S) 1).widen hn)
  have hd : (line S).width ≤ 2 ^ (n S) * (100 + δ) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have sorted := ((Cheap.id F hd).pair σ).comp (Cheap.lookup F (n S) δ (header S) (by omega) hh)
  exact (len.pair sorted).mono (by decide)

-- 读法：`localCost` 的取值由 `4 * (2 ^ S.m * (2 ^ (n S) * (100 + scale S t) ^ 50) + 3 * (source S t).width)` 给出。
def localCost (S : Scheme F) (t : ℕ) :=
  4 * (2 ^ S.m * (2 ^ (n S) * (100 + scale S t) ^ 50) + 3 * (source S t).width)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `S.format` 到 `(source S t)` 实现映射 `(paired S t)` 的开销至多为 `(rowCost S + localCost S t)`。这里调用 `Circuit.project`。
theorem paired_net (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L) :
    Map F u L S.format (source S t) (paired S t) (rowCost S + localCost S t) := by
  let D := Format.vec S.m (.pair (.addr (wordSize S t)) (line S))
  have hw : D.width = (source S t).width := by simp [D, source, Redistribute.input, mul_add]
  have unzip : Circuit F D (source S t) (fun x => (fun i => (x i).1, fun i => (x i).2))
      (D.width + 2 * (source S t).width) := by
    apply Circuit.project (Sum.elim (fun p => (p.1, .inl p.2)) (fun p => (p.1, .inr p.2)))
    rintro x (i|i) <;> rfl
  obtain ⟨s, hs, hb⟩ := host (S:=S) (t:=t)
  have hc := (Circuit.map _ (fun _ : B S.m => hs)).comp unzip
  have hle : s ≤ 2 ^ (n S) * (100 + scale S t) ^ 50 := by omega
  have hm := Nat.mul_le_mul_left (2 ^ S.m) hle
  exact (rows_net hu ha hl).comp ((Map.circuit hu hc).mono (n:=localCost S t) (by unfold localCost; omega))

-- 读法：`cost` 的构造用到 `Redistribute.cost`。
def cost (S : Scheme F) (V t v c : ℕ) := rowCost S + localCost S t +
    Redistribute.cost S.m (height S t) (wordSize S t) v c +
    4 * ((dest S V t).width + 2 * (headers S V t).width)

-- 读法：在 `F` 上使用表集 `L`、宽度参数 `u`，从 `S.format` 到 `(headers S V t)` 实现映射 `(eval S V t)` 的开销至多为 `(cost S V t v c)`。这里调用 `a.comp`。
theorem realize (hu : 3 ≤ u) (ha : arity S ≤ u) (hl : label S ∈ L)
    (ht : Radix.Tag F S.m v c) (hv : (line S).width ≤ v) :
    Map F u L S.format (headers S V t) (eval S V t) (cost S V t v c) := by
  have a := paired_net (t:=t) hu ha hl
  have b := Redistribute.realize (L:=L) (w:=wordSize S t) (k:=height S t) (V:=V)
    hu ht (line S) hv (fun _ => pad S)
  have d : Circuit F (dest S V t) (headers S V t) (cut S V t)
      ((dest S V t).width + 2 * (headers S V t).width) :=
    Circuit.project (fun i => ⟨i.1.1, pick S V t i.1, i.2⟩) (fun _ _ => rfl)
  exact (a.comp b).comp (Map.circuit hu d)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end

/-!
# 将记录头的成本计入宿主，数据成本与存储区容量成线性关系

**英文原文**

Header work is charged to hosts and the data charge is linear in bank capacity
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
open Coloring Dictionary

-- 读法：`137 * x + 1 + 13 * y + 12 * z + 52 * H * y + 4 * d ^ 50 + 10000 * H * (W + 1) * (y + 1)` 不超过 `R ^ 80`。
private theorem majorant (R x y H z d W : ℕ) (hR : 1000 ≤ R)
    (hx : x ≤ R) (hy : y ≤ R) (hh : H ≤ R) (hz : z ≤ R)
    (hd : d ≤ R) (hw : W + 1 ≤ R) :
    137 * x + 1 + 13 * y + 12 * z + 52 * H * y + 4 * d ^ 50 + 10000 * H * (W + 1) * (y + 1) ≤ R ^ 80 := by
  have hr : 0 < R := by omega
  have h₀ : 1 ≤ R ^ 50 := Nat.one_le_pow _ _ hr
  have h₁ : R ≤ R ^ 50 := Nat.le_pow (by decide)
  have h₂ : R ^ 2 ≤ R ^ 50 := Nat.pow_le_pow_right hr (by decide)
  have h₃ : R ^ 3 ≤ R ^ 50 := Nat.pow_le_pow_right hr (by decide)
  calc
    _ ≤ 137 * R + 1 + 13 * R + 12 * R + 52 * R * R + 4 * R ^ 50 + 10000 * R * R * (R + 1) := by gcongr
    _ = 1 + 162 * R + 10052 * R ^ 2 + 10000 * R ^ 3 + 4 * R ^ 50 := by ring
    _ ≤ 1000000 * R ^ 50 := by omega
    _ ≤ R ^ 2 * R ^ 50 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hR 2)
    _ = R ^ 52 := (pow_add R 2 50).symm
    _ ≤ R ^ 80 := Nat.pow_le_pow_right hr (by decide)

-- 读法：证明中先建立 `hg`，即 `c ≤ W * (M * (N * y + P + B))`。
private theorem account (A M N H x y z d W P B V v c D E Y : ℕ)
    (hn : 0 < N) (hv : v ≤ N * y + P) (hc : c ≤ W * (M * v))
    (hD : D ≤ H * (M * (N * y))) (hE : E ≤ D) (hY : Y ≤ H * (2 * V)) :
    4 * (A + 34 * (M * (N * x))) + M * (N * (1 + x + y)) +
      4 * (M * (N * d ^ 50) + 3 * (M * z + M * (N * y))) +
      10000 * H * (c + M * (v + B)) + 4 * (D + 2 * E) + 40 * (E + Y) ≤
    4 * A + (M * (P + B) + M * N) * (137 * x + 1 + 13 * y + 12 * z + 52 * H * y + 4 * d ^ 50 + 10000 * H * (W + 1) * (y + 1)) + 80 * H * V := by
  have hm := Nat.le_mul_of_pos_right M hn
  have hg : c ≤ W * (M * (N * y + P + B)) := hc.trans (by gcongr; omega)
  have he := hE.trans hD
  calc
    _ ≤ 4 * (A + 34 * (M * (N * x))) + M * (N * (1 + x + y)) +
      4 * (M * (N * d ^ 50) + 3 * (M * N * z + M * (N * y))) +
      10000 * H * (W * (M * (N * y + P + B)) + M * (N * y + P + B)) +
      4 * (H * (M * (N * y)) + 2 * (H * (M * (N * y)))) + 40 * (H * (M * (N * y)) + H * (2 * V)) := by gcongr
    _ ≤ _ := by ring_nf; omega

variable {F : Type} {S : Scheme F} {V t v c P W : ℕ}

-- 读法：结论为 `cost S V t v c + Dictionary.price S V t ≤ 4 * S.format.width + (2 ^ S.m * (P + (101 + S.m + wordSize S t) ^ 60) + 2 ^ (S.m + S.h + S.k))* (1000 + W + scale S t) ^ 80 + 80 * (height S t + 1) * V`。
theorem cost_bound (hv : v ≤ (line S).width + P) (hc : c ≤ W * (2 ^ S.m * v)) :
    cost S V t v c + Dictionary.price S V t ≤
      4 * S.format.width + (2 ^ S.m * (P + (101 + S.m + wordSize S t) ^ 60) + 2 ^ (S.m + S.h + S.k))*
        (1000 + W + scale S t) ^ 80 + 80 * (height S t + 1) * V := by
  have hu := account S.format.width (2 ^ S.m) (2 ^ (n S)) (height S t + 1)
    (key S).width (header S).width (wordSize S t) (100 + scale S t) W P
    ((101 + S.m + wordSize S t) ^ 60) V v c (dest S V t).width (headers S V t).width
    (Fmt.payload S.m V (height S t)).width (Nat.two_pow_pos _) (by simpa only [line, Format.width_vec] using hv) hc
    (by simpa only [line, Format.width_vec] using width_dest S V t)
    (width_headers S V t) (Fmt.width_payload ..)
  have hb := majorant (1000 + W + scale S t) (key S).width (header S).width (height S t + 1)
    (wordSize S t) (100 + scale S t) W (by omega)
    (by simp only [scale, key, header, Format.width_pair]; omega)
    (by unfold scale; omega) (by unfold scale wordSize height n; omega)
    (by unfold scale; omega) (by omega) (by omega)
  -- 推导：记下中间结论 `hn`：`2 ^ (S.m + S.h + S.k) = 2 ^ S.m * 2 ^ (n S)`。
  have hn : 2 ^ (S.m + S.h + S.k) = 2 ^ S.m * 2 ^ (n S) := by rw [add_assoc, pow_add]
  rw [hn]
  refine le_trans ?_ (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hb) _) _)
  simpa only [cost, Dictionary.price, rowCost, localCost, names, source, Redistribute.input, Redistribute.cost,
    Redistribute.budget, line, Format.width_pair, Format.width_vec, Format.width_addr] using hu

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Header
end

/-!
# 从地址比较矩阵中读取互为反向的接触

**英文原文**

Reading reciprocal contacts from a matrix of address comparisons
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F)
-- 读法：在后续公式中，`LinkGrid` 是 `(Perm (S.m + (S.d + 1))).pair (Flags S)` 的缩写。
abbrev LinkGrid := (Perm (S.m + (S.d + 1))).pair (Flags S)
-- 读法：`links` 的取值由 `(perm S r, flags S r)` 给出。
def links (r : S.format.obj) : (LinkGrid S).obj := (perm S r, flags S r)

namespace Links
local notation "m" => S.m
local notation "d" => S.d
local notation "idx" => Match.rowIndex m (d + 1)

-- 读法：在后续公式中，`Rows` 是 `Neighborhood.Rows m (d + 1)` 的缩写。
abbrev Rows := Neighborhood.Rows m (d + 1)
-- 读法：在后续公式中，`Mask` 是 `Neighborhood.Mask m (d + 1) (d + 1)` 的缩写。
abbrev Mask := Neighborhood.Mask m (d + 1) (d + 1)
-- 读法：在后续公式中，`Query` 是 `Format.vec m (.vec (d + 1) (.vec d .bit))` 的缩写。
abbrev Query := Format.vec m (.vec (d + 1) (.vec d .bit))
-- 读法：在后续公式中，`Reply` 是 `Format.vec m (.vec (d + 1) (.addr (d + 1)))` 的缩写。
abbrev Reply := Format.vec m (.vec (d + 1) (.addr (d + 1)))
-- 读法：在后续公式中，`Status` 是 `(Mask S).pair (Reply S)` 的缩写。
abbrev Status := (Mask S).pair (Reply S)
-- 读法：在后续公式中，`Data` 是 `(Rows S).pair (Status S)` 的缩写。
abbrev Data := (Rows S).pair (Status S)

-- 读法：输入 `v i j` 时返回 `x v i (hop (some j)) (hop none)`。
def query (x : (Mask S).obj) : (Query S).obj := fun v i j => x v i (hop (some j)) (hop none)
-- 读法：输入 `v i` 时返回 `reverseHop d (x v i)`。
def reply (x : (Query S).obj) : (Reply S).obj := fun v i => reverseHop d (x v i)
-- 读法：`status` 的取值由 `(x, reply S (query S x))` 给出。
def status (x : (Mask S).obj) : (Status S).obj := (x, reply S (query S x))
-- 读法：`data` 的取值由 `(x, status S (Neighborhood.maskRows x x))` 给出。
def data (x : (Rows S).obj) : (Data S).obj := (x, status S (Neighborhood.maskRows x x))
-- 读法：`self` 的取值由 `x.2.1 v (hop none) j (hop none)` 给出。
def self (x : (Data S).obj) (v : B m) (j : B (d + 1)) := x.2.1 v (hop none) j (hop none)

-- 读法：`finish` 的结果类型为 `(LinkGrid S).obj`。
def finish (x : (Data S).obj) : (LinkGrid S).obj :=
  (fun i =>
    let j := idx i
    (idx).symm (x.1 j.1 j.2, if self S x j.1 j.2 then j.2 else x.2.2 j.1 j.2),
   fun i j => self S x i (hop (some j)))

-- 读法：`finish S ∘ data S ∘ extended S` 等于 `links S`。用函数外延性比较等号两侧在 `r` 处的取值。
theorem correct : finish S ∘ data S ∘ extended S = links S := by
  funext r
  have a (i : B m) (j : B (d + 1)) : self S (data S (extended S r)) i j = decide (extended S r i j = i) := by
    simp only [self, data, status, Neighborhood.maskRows, extended_self]
  have b (i : B m) (j : B (d + 1)) :
      (data S (extended S r)).2.2 i j = reverseHop d (fun k => decide ((r (extended S r i j)).1 k = i)) := by
    apply congrArg (reverseHop d)
    funext k
    simp only [query, Neighborhood.maskRows, extended_self, extended_peer]
  apply Prod.ext
  · funext i
    simp only [Function.comp_apply, finish, links, perm, a, b, decide_eq_true_eq]
    rfl
  · funext i j
    simp only [Function.comp_apply, finish, links, flags, a, extended_peer]

variable [Field F]

-- 读法：在 `F` 上按格式 `S.format`、`(Rows S)` 编码输入输出，映射 `(extended S)` 的电路规模至多为 `(S.format.width + 34 * (Rows S).width)`。这里调用 `Window.Tile.project_const`。
theorem extend_net : Circuit F S.format (Rows S) (extended S) (S.format.width + 34 * (Rows S).width) := by
  apply Window.Tile.project_const
  rintro ⟨v, i, k⟩
  by_cases h : (Match.rowIndex S.d 1 i).2 = 1
  · refine .inl ⟨(v, .inl ((Match.rowIndex S.d 1 i).1, k)), fun r => ?_⟩
    change (Format.addr m).code (extended S r v i) k = _
    rw [extended, ite_eq_left h]
    rfl
  · refine .inr ⟨(Format.addr m).code v k, fun r => ?_⟩
    change (Format.addr m).code (extended S r v i) k = _
    rw [extended, ite_eq_right h]

-- 读法：在 `F` 上按格式 `(Mask S)`、`(Query S)` 编码输入输出，映射 `(query S)` 的电路规模至多为 `((Mask S).width + 2 * (Query S).width)`。使用 `Circuit.project` 给出的结论。
theorem query_net : Circuit F (Mask S) (Query S) (query S) ((Mask S).width + 2 * (Query S).width) :=
  Circuit.project (fun x => (x.1, x.2.1, hop (some x.2.2.1), hop none, x.2.2.2)) (fun _ _ => rfl)

-- 读法：在 `F` 上按格式 `(Data S)`、`(LinkGrid S)` 编码输入输出，映射 `(finish S)` 的电路规模至多为 `((Data S).width + 68 * (LinkGrid S).width)`。
theorem finish_net : Circuit F (Data S) (LinkGrid S) (finish S) ((Data S).width + 68 * (LinkGrid S).width) := by
  let A := Data S
  let C := LinkGrid S
  have he : Install.Depends (C.code ∘ finish S ∘ A.code.symm) 2 := by
    have pin (i : C.pins) (j : A.pins) (h : ∀ x, C.code (finish S x) i = A.code x j) :
        ∃ s : Finset A.pins, s.card ≤ 2 ∧ ∀ x y, (∀ l ∈ s, x l = y l) →
          (C.code ∘ finish S ∘ A.code.symm) x i = (C.code ∘ finish S ∘ A.code.symm) y i := by
      refine ⟨{j}, by simp, fun x y he => ?_⟩
      simp only [Function.comp_apply, h, Equiv.apply_symm_apply]
      exact he j (by simp)
    rintro (⟨i, t⟩|⟨j, k, ⟨⟩⟩)
    · let v := (idx i).1
      let w := (idx i).2
      -- 推导：从 `Match.append_pin m (d + 1) t` 中取出 `k, hk`。
      obtain ⟨k, hk⟩ := Match.append_pin m (d + 1) t
      cases k with
      | inl k =>
        exact pin _ (.inl (v, w, k)) (fun x => hk _ _)
      | inr k =>
        let j : A.pins := .inr (.inl (v, hop none, w, hop none, ()))
        let l : A.pins := .inr (.inr (v, w, k))
        have eq (x : A.obj) : C.code (finish S x) (.inl (i, t)) =
            if A.code x j then (Format.addr (d + 1)).code w k else A.code x l := by
          change (Format.addr _).code ((idx).symm (x.1 v w, if self S x v w then w else x.2.2 v w)) t = _
          rw [hk]
          change (Format.addr (d + 1)).code (if self S x v w then w else x.2.2 v w) k =
            if self S x v w then _ else _
          split <;> rfl
        refine ⟨{j, l}, Finset.card_le_two, fun x y h => ?_⟩
        simp only [Function.comp_apply, eq, Equiv.apply_symm_apply, h j (by simp), h l (by simp)]
    · exact pin _ (.inr (.inl (j, hop none, hop (some k), hop none, ()))) (fun _ => rfl)
  exact he.bnet F

end Links
end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 构造终端接触置换的成本

共用的掩码只比较宿主邻域内的地址。每个互反索引均由唯一命中的比较结果还原。

**英文原文**

Cost of constructing the terminal contact permutation

A shared mask compares only addresses in the host's neighborhood.
Recover each reciprocal index from the unique successful comparison.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
open Coloring Links
open scoped Classical

variable {F : Type} (S : Scheme F)

local notation "m" => S.m
local notation "d" => S.d
local notation "t" => (S.m + 2 ^ (S.d + 1))
local notation "W" => (2 ^ m * (100 + t) ^ 24)

-- 读法：`linkCost` 的取值由 `S.format.width + 512 * W` 给出。
def linkCost := S.format.width + 512 * W

-- 读法：`2 ^ m * (x * (y * z))` 不超过 `W`。这里调用 `Nat.mul_le_mul_left`。
private theorem product (x y z : ℕ) (hx : x ≤ 100 + t) (hy : y ≤ 100 + t) (hz : z ≤ 100 + t) :
    2 ^ m * (x * (y * z)) ≤ W := by
  apply Nat.mul_le_mul_left
  calc
    _ ≤ (100 + t) * ((100 + t) * (100 + t)) := Nat.mul_le_mul hx (Nat.mul_le_mul hy hz)
    _ = (100 + t) ^ 3 := by rw [pow_succ' (100 + t) 2, pow_two]
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by decide)

-- 读法：`(Query S).width ≤ W` 与 `(Reply S).width ≤ W ∧ (LinkGrid S).width ≤ 2 * W ∧ 2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)) ≤ 100 * W` 同时成立。
private theorem bounds :
    (Query S).width ≤ W ∧ (Reply S).width ≤ W ∧ (LinkGrid S).width ≤ 2 * W ∧
      2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)) ≤ 100 * W := by
  have hs : 2 ^ (d + 1) ≤ 100 + t := (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
  have hd : 2 ^ d ≤ 100 + t := (Nat.pow_le_pow_right (by decide) (Nat.le_succ d)).trans hs
  have h₁ : 1 ≤ 100 + t := (by decide : 1 ≤ 100).trans (Nat.le_add_right ..)
  have ha : m + (d + 1) ≤ 100 + t :=
    (Nat.add_le_add_left Nat.lt_two_pow_self.le m).trans (Nat.le_add_left ..)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Query, Format.width_vec, Format.width_vec, Format.width_vec, Format.width_bit]
    exact product S _ _ _ hs hd h₁
  · rw [Reply, Format.width_vec, Format.width_vec, Format.width_addr]
    simpa only [mul_one] using product S _ _ 1 hs ((Nat.le_add_left _ _).trans ha) h₁
  · rw [LinkGrid, Format.width_pair, Perm, Flags, Format.width_vec, Format.width_addr, Format.width_vec,
      Format.width_vec, Format.width_bit, pow_add, mul_assoc, two_mul]
    have hP := product S _ _ 1 hs ha h₁
    have hQ := product S _ _ 1 hd h₁ h₁
    simp only [mul_one] at hP hQ ⊢
    exact Nat.add_le_add hP hQ
  · rw [mul_left_comm (2 ^ (d + 1)) 100, mul_left_comm (2 ^ m) 100, pow_two]
    exact Nat.mul_le_mul_left 100 (product S _ _ _ hs hd hd)

-- 读法：在 `F` 上按格式 `A`、`(A.pair (B.pair C))` 编码输入输出，映射 `(fun x => (x, f (x, x), g (f (x, x))))` 的电路规模至多为 `(200 * w)`。
private theorem assemble [Field F] {A B C : Format} {f : (A.pair A).obj → B.obj}
    {g : B.obj → C.obj} {k l w : ℕ}
    (first : Circuit F (A.pair A) B f k) (next : Circuit F B C g l)
    (hk : (A.pair A).width + B.width + k ≤ w) (hl : l ≤ 104 * w) :
    Circuit F A (A.pair (B.pair C)) (fun x => (x, f (x, x), g (f (x, x)))) (200 * w) := by
  have h := Circuit.id F A
  refine (h.pair (((h.pair h).comp first).comp ((Circuit.id F B).pair next))).mono ?_
  rw [Format.width_pair] at hk
  omega

-- 读法：存在 `a`，`Circuit F ((Rows S).pair (Rows S)) (Mask S) (fun x => Neighborhood.maskRows x.1 x.2) a` 与 `((Rows S).pair (Rows S)).width + (Mask S).width + a ≤ W` 同时成立。
private theorem mask_net [Field F] : ∃ a,
    Circuit F ((Rows S).pair (Rows S)) (Mask S) (fun x => Neighborhood.maskRows x.1 x.2) a ∧
    ((Rows S).pair (Rows S)).width + (Mask S).width + a ≤ W :=
  Neighborhood.cheap_maskRows F (Nat.le_add_right m (2 ^ (d + 1)))
    (Nat.le_add_left (2 ^ (d + 1)) m) (Nat.le_add_left (2 ^ (d + 1)) m)

-- 读法：在 `F` 上按格式 `(.vec i (.vec j A))`、`(.vec i (.vec j B))` 编码输入输出，映射 `(fun x v y => f (x v y))` 的电路规模至多为 `(2 ^ i * (2 ^ j * c))`。使用 `Circuit.map` 给出的结论。
private theorem twice [Field F] {A B : Format} {f : A.obj → B.obj} {c : ℕ}
    (h : Circuit F A B f c) (i j : ℕ) :
    Circuit F (.vec i (.vec j A)) (.vec i (.vec j B)) (fun x v y => f (x v y)) (2 ^ i * (2 ^ j * c)) :=
  Circuit.map _ fun _ => Circuit.map _ fun _ => h

-- 读法：在 `F` 上按格式 `(Query S)`、`(Reply S)` 编码输入输出，映射 `(Links.reply S)` 的电路规模至多为 `(2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)))`。
private theorem r_net [Field F] : Circuit F (Query S) (Reply S) (Links.reply S) (2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2))) := by
  unfold Links.reply Query Reply
  exact twice (reverseNet F d) m (d + 1)

-- 读法：在 `F` 上按格式 `(Rows S)`、`(Links.Data S)` 编码输入输出，映射 `(Links.data S)` 的电路规模至多为 `(200 * W)`。
private theorem data_net [Field F] : Circuit F (Rows S) (Links.Data S) (Links.data S) (200 * W) := by
  obtain ⟨a, k, h⟩ := mask_net S
  have hl : (Mask S).width + 2 * (Query S).width + 2 ^ m * (2 ^ (d + 1) * (100 * (2 ^ d) ^ 2)) ≤ 104 * W := by
    obtain ⟨h₁, _, _, h₄⟩ := bounds S
    omega
  have h' := assemble k ((query_net S).comp (r_net S)) h hl
  simp only [Function.comp_apply] at h'
  unfold Links.data Links.status Links.Data Links.Status
  exact h'

-- 读法：在 `F` 上按格式 `S.format`、`(LinkGrid S)` 编码输入输出，映射 `(links S)` 的电路规模至多为 `(linkCost S)`。
theorem links_net [Field F] : Circuit F S.format (LinkGrid S) (links S) (linkCost S) := by
  rw [← correct]
  refine ((extend_net S).comp ((data_net S).comp (finish_net S))).mono ?_
  obtain ⟨_, _, h⟩ := mask_net S
  obtain ⟨_, h₂, h₃, _⟩ := bounds S
  rw [Format.width_pair] at h
  unfold linkCost
  rw [Links.Data, Format.width_pair, Links.Status, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal
end

/-!
# 终端收缩的统一成本尺度

宿主名称、站点标签和实际有效载荷各有独立系数。每个估计都对各系数域及各方案统一成立。

**英文原文**

Uniform cost scales of the terminal contraction

Host names, station labels and physical payloads have separate
coefficients. Each estimate is uniform over fields and schemes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open BatchDescent.Phase Rounds.Contraction

-- 读法：结构的字段包括 `F`、`S`、`W`、`V`、`t`。
structure Size where
  F : Type
  [field : Field F]
  S : Scheme F
  W : Prices F
  V : ℕ
  t : ℕ
  V' : ℕ
  k' : ℕ

attribute [instance] Size.field

namespace Size
variable (i : Size)

-- 读法：在后续公式中，`k` 是 `height i.S i.t` 的缩写。
abbrev k := height i.S i.t
-- 读法：在后续公式中，`w` 是 `max i.k i.k' + 1` 的缩写。
abbrev w := max i.k i.k' + 1
-- 读法：在后续公式中，`p` 是 `i.S.d + 1` 的缩写。
abbrev p := i.S.d + 1
-- 读法：在后续公式中，`n` 是 `i.S.spanRows` 的缩写。
abbrev n := i.S.spanRows
-- 读法：在后续公式中，`B` 是 `1000 + i.W.W + i.k + i.k'` 的缩写。
abbrev B := 1000 + i.W.W + i.k + i.k'
-- 读法：在后续公式中，`T` 是 `i.B + 2 ^ i.S.d + i.S.ℓ` 的缩写。
abbrev T := i.B + 2 ^ i.S.d + i.S.ℓ
-- 读法：在后续公式中，`M` 是 `i.T + i.S.m + i.W.w + i.W.w ^ i.W.power` 的缩写。
abbrev M := i.T + i.S.m + i.W.w + i.W.w ^ i.W.power
-- 读法：在后续公式中，`hosts` 是 `2 ^ i.S.m` 的缩写。
abbrev hosts := 2 ^ i.S.m
-- 读法：在后续公式中，`spans` 是 `i.hosts * 2 ^ i.n` 的缩写。
abbrev spans := i.hosts * 2 ^ i.n
-- 读法：在后续公式中，`volume` 是 `i.V + i.V'` 的缩写。
abbrev volume := i.V + i.V'
-- 读法：在后续公式中，`bound` 是 `i.hosts * i.M ^ K + i.spans * i.T ^ K + i.volume * i.B ^ K` 的缩写。
abbrev bound (K : ℕ) := i.hosts * i.M ^ K + i.spans * i.T ^ K + i.volume * i.B ^ K

-- 读法：`2` 不超过 `i.B`。
theorem b_two : 2 ≤ i.B := by unfold B; omega
-- 读法：`i.B` 不超过 `i.T`。通过传递性衔接 `Nat.le_add_right` 与 `Nat.le_add_right`。
theorem bt : i.B ≤ i.T := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
-- 读法：`i.T` 不超过 `i.M`。
theorem tm : i.T ≤ i.M := by unfold M; omega
-- 读法：`2` 不超过 `i.T`。使用 `i.b_two.trans` 给出的结论。
theorem t_two : 2 ≤ i.T := i.b_two.trans i.bt
-- 读法：`2` 不超过 `i.M`。使用 `i.t_two.trans` 给出的结论。
theorem m_two : 2 ≤ i.M := i.t_two.trans i.tm
end Size

-- 读法：在后续公式中，`Outer` 是 `Poly Size.B` 的缩写。
abbrev Outer := Poly Size.B
-- 读法：在后续公式中，`Short` 是 `Poly Size.T` 的缩写。
abbrev Short := Poly Size.T
-- 读法：在后续公式中，`Long` 是 `Poly Size.M` 的缩写。
abbrev Long := Poly Size.M
-- 读法：`Work` 的取值由 `∃ K, ∀ i, f i ≤ i.bound K` 给出。
def Work (f : Size → ℕ) := ∃ K, ∀ i, f i ≤ i.bound K

variable {f g : Size → ℕ}
-- 读法：要证明的命题是 `Short f`。使用 `h.grow` 给出的结论。
theorem Outer.short (h : Outer f) : Short f := h.grow Size.bt
-- 读法：要证明的命题是 `Long f`。使用 `h.grow` 给出的结论。
theorem Short.long (h : Short f) : Long f := h.grow Size.tm
-- 读法：要证明的命题是 `Long f`。使用 `h.short.long` 给出的结论。
theorem Outer.long (h : Outer f) : Long f := h.short.long

-- 读法：要证明的命题是 `Outer (fun _ => a)`。使用 `Poly.const` 给出的结论。
theorem num (a : ℕ) : Outer (fun _ => a) := Poly.const Size.b_two a
-- 读法：要证明的命题是 `Outer Size.k`。使用 `Poly.of_le` 给出的结论。
theorem k : Outer Size.k := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
-- 读法：要证明的命题是 `Outer Size.k'`。使用 `Poly.of_le` 给出的结论。
theorem k' : Outer Size.k' := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
-- 读法：要证明的命题是 `Outer Size.w`。使用 `Poly.of_le` 给出的结论。
theorem w : Outer Size.w := Poly.of_le Size.b_two fun i => by unfold Size.B Size.w; omega
-- 读法：要证明的命题是 `Outer (fun i => i.W.W)`。使用 `Poly.of_le` 给出的结论。
theorem rate : Outer (fun i => i.W.W) := Poly.of_le Size.b_two fun i => by unfold Size.B; omega
-- 读法：要证明的命题是 `Outer Size.n`。使用 `k.mono` 给出的结论。
theorem n : Outer Size.n := k.mono fun i => by unfold Size.k Size.n height Scheme.spanRows; omega
-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.S.d)`。使用 `Poly.of_le` 给出的结论。
theorem neighbors : Short (fun i => 2 ^ i.S.d) := Poly.of_le Size.t_two fun i => by unfold Size.T; omega
-- 读法：要证明的命题是 `Short (fun i => i.S.d)`。使用 `neighbors.of_exp` 给出的结论。
theorem d : Short (fun i => i.S.d) := neighbors.of_exp
-- 读法：要证明的命题是 `Short (fun i => i.S.ℓ)`。使用 `Poly.of_le` 给出的结论。
theorem labels : Short (fun i => i.S.ℓ) := Poly.of_le Size.t_two fun _ => Nat.le_add_left ..
-- 读法：要证明的命题是 `Short Size.p`。使用 `d.add` 给出的结论。
theorem p : Short Size.p := d.add (num 1).short
-- 读法：要证明的命题是 `Short (fun i => 2 ^ i.p)`。这里调用 `neighbors.mul`。
theorem links : Short (fun i => 2 ^ i.p) := by simpa only [Size.p, pow_succ] using neighbors.mul (num 2).short
-- 读法：要证明的命题是 `Long (fun i => i.S.m)`。使用 `Poly.of_le` 给出的结论。
theorem m : Long (fun i => i.S.m) := Poly.of_le Size.m_two fun i => by unfold Size.M; omega
-- 读法：要证明的命题是 `Long (fun i => i.W.w)`。使用 `Poly.of_le` 给出的结论。
theorem limit : Long (fun i => i.W.w) := Poly.of_le Size.m_two fun i => by unfold Size.M; omega
-- 读法：要证明的命题是 `Long (fun i => i.W.w ^ i.W.power)`。使用 `Poly.of_le` 给出的结论。
theorem threshold : Long (fun i => i.W.w ^ i.W.power) :=
  Poly.of_le Size.m_two fun i => by unfold Size.M; omega

namespace Work
-- 读法：要证明的命题是 `Work g`。
theorem mono (hf : Work f) (h : ∀ i, g i ≤ f i) : Work g :=
  let ⟨s, hs⟩ := hf
  ⟨s, fun i => (h i).trans (hs i)⟩

-- 读法：要证明的命题是 `Work (fun i => f i + g i)`。这里调用 `Nat.add_le_add`。
theorem add (hf : Work f) (hg : Work g) : Work (fun i => f i + g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨max s t + 1, fun i => (Nat.add_le_add (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_add_add_comm, add_add_add_comm (i.hosts * _ ^ s), ← mul_add, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.m_two ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.t_two ..)))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.b_two ..))

-- 读法：要证明的命题是 `Work (fun i => f i * g i)`。这里调用 `i.bt.trans`。
theorem mul (hf : Work f) (hg : Outer g) : Work (fun i => f i * g i) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg.bound
  refine ⟨s + t, fun i => (Nat.mul_le_mul (hs i) (ht i)).trans ?_⟩
  unfold Size.bound
  rw [add_mul, add_mul]
  simp only [mul_assoc, pow_add]
  gcongr
  · exact i.bt.trans i.tm
  · exact i.bt

-- 读法：要证明的命题是 `Work (fun i => g i * f i)`。使用 `hf.mul` 给出的结论。
theorem scale (hf : Work f) (hg : Outer g) : Work (fun i => g i * f i) :=
  (hf.mul hg).mono fun _ => (mul_comm ..).le

-- 读法：要证明的命题是 `Work (fun i => i.hosts * f i)`。
theorem hosts (hf : Long f) : Work (fun i => i.hosts * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))⟩

-- 读法：要证明的命题是 `Work (fun i => i.spans * f i)`。
theorem spans (hf : Short f) : Work (fun i => i.spans * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans ((Nat.le_add_left ..).trans (Nat.le_add_right ..))⟩

-- 读法：要证明的命题是 `Work (fun i => i.volume * f i)`。
theorem volume (hf : Outer f) : Work (fun i => i.volume * f i) :=
  let ⟨s, hs⟩ := hf.bound
  ⟨s, fun i => (Nat.mul_le_mul_left _ (hs i)).trans (Nat.le_add_left ..)⟩
end Work

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-!
# 构造终端字典并求值的统一上界

**英文原文**

Uniform bound for constructing and evaluating the terminal dictionary
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring

namespace Size
variable (i : Size)
-- 读法：在后续公式中，`v` 是 `(Header.line i.S).width + i.W.w ^ i.W.power` 的缩写。
abbrev v := (Header.line i.S).width + i.W.w ^ i.W.power
-- 读法：在后续公式中，`c` 是 `i.W.W * (2 ^ i.S.m * i.v)` 的缩写。
abbrev c := i.W.W * (2 ^ i.S.m * i.v)
-- 读法：在后续公式中，`header` 是 `Header.cost i.S i.V i.t i.v i.c` 的缩写。
abbrev header := Header.cost i.S i.V i.t i.v i.c
-- 读法：在后续公式中，`dictionary` 是 `Dictionary.price i.S i.V i.t` 的缩写。
abbrev dictionary := Dictionary.price i.S i.V i.t
-- 读法：在后续公式中，`inner` 是 `(Fmt.payload i.S.m i.V i.k).width` 的缩写。
abbrev inner := (Fmt.payload i.S.m i.V i.k).width
-- 读法：在后续公式中，`outer` 是 `(Fmt.payload i.S.m i.V' i.k').width` 的缩写。
abbrev outer := (Fmt.payload i.S.m i.V' i.k').width

-- 读法：`2 ^ (i.S.m + i.S.h + i.S.k)` 不超过 `i.spans`。这里调用 `Nat.mul_le_mul_left`。
theorem stations : 2 ^ (i.S.m + i.S.h + i.S.k) ≤ i.spans := by
  rw [add_assoc, pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))

end Size

-- 读法：要证明的命题是 `Work (fun i => i.S.format.width)`。这里调用 `Nat.add_le_add_left`。
theorem format : Work (fun i => i.S.format.width) := by
  refine ((Work.hosts (neighbors.long.mul m)).add (Work.spans labels)).mono fun i => ?_
  rw [Scheme.format, Fmt.width_rows, Format.width_addr, mul_add, ← mul_assoc (2 ^ i.S.m) (2 ^ i.S.h)]
  have he : 2 ^ i.S.h ≤ 2 ^ i.n := Nat.pow_le_pow_right (by decide) (by unfold Size.n Scheme.spanRows; omega)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)) _

-- 读法：要证明的命题是 `Work Size.inner`。这里调用 `Nat.mul_le_mul_right`。
theorem inner : Work Size.inner := by
  refine (Work.volume ((k.add (num 1)).mul (num 2))).mono fun i => ?_
  refine (Fmt.width_payload ..).trans ?_
  rw [← mul_assoc, mul_comm _ i.V]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

-- 读法：要证明的命题是 `Work Size.outer`。这里调用 `Nat.mul_le_mul_right`。
theorem outer : Work Size.outer := by
  refine (Work.volume ((k'.add (num 1)).mul (num 2))).mono fun i => ?_
  refine (Fmt.width_payload ..).trans ?_
  rw [← mul_assoc, mul_comm _ i.V']
  exact Nat.mul_le_mul_right _ (Nat.le_add_left ..)

-- 读法：要证明的命题是 `Outer (fun i => Header.wordSize i.S i.t)`。使用 `k.add` 给出的结论。
private theorem word : Outer (fun i => Header.wordSize i.S i.t) :=
  (k.add (num 1)).mono fun i => by unfold Header.wordSize Header.n Size.k height; omega

-- 读法：要证明的命题是 `Short (fun i => Header.scale i.S i.t)`。
private theorem scale : Short (fun i => Header.scale i.S i.t) := by
  have hk : Outer (fun i => i.S.k) := n.mono fun i => by unfold Size.n Scheme.spanRows; omega
  refine (word.short.add ((num 1).short.add (labels.add hk.short))).mono fun i => ?_
  simp only [Header.scale, Dictionary.header, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

-- 读法：要证明的命题是 `Work (fun i => i.header + i.dictionary)`。
theorem both : Work (fun i => i.header + i.dictionary) := by
  have factor := ((((num 1000).short.add rate.short).add scale).pow 80)
  have total := threshold.add ((((num 101).long.add m).add word.long).pow 60)
  have names := Work.hosts (total.mul (Short.long factor))
  have rows := Work.spans factor
  have bits := Work.volume ((num 80).mul (k.add (num 1)))
  refine (((format.scale (num 4)).add (names.add rows)).add bits).mono fun i => ?_
  refine (Header.cost_bound (S:=i.S) (V:=i.V) (t:=i.t) (v:=i.v) (c:=i.c)
    (P:=i.W.w ^ i.W.power) (W:=i.W.W) le_rfl le_rfl).trans ?_
  rw [add_mul, mul_assoc (2 ^ i.S.m), mul_comm _ i.V]
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ i.stations) _) _) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))

-- 读法：要证明的命题是 `Work Size.header`。使用 `both.mono` 给出的结论。
theorem header : Work Size.header := both.mono fun _ => Nat.le_add_right ..
-- 读法：要证明的命题是 `Work Size.dictionary`。使用 `both.mono` 给出的结论。
theorem dictionary : Work Size.dictionary := both.mono fun _ => Nat.le_add_left ..
-- 读法：要证明的命题是 `Work (fun i => (Dictionary.headers i.S i.V i.t).width)`。使用 `dictionary.mono` 给出的结论。
theorem headers : Work (fun i => (Dictionary.headers i.S i.V i.t).width) :=
  dictionary.mono fun i => by unfold Size.dictionary Dictionary.price; omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-!
# 终端收缩成本的统一上界

**英文原文**

Uniform terminal contraction cost
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring Rounds.Contraction

-- 读法：在后续公式中，`Size.instruction` 是 `Terminal.instruction i.S i.V i.t i.p i.w i.n` 的缩写。
abbrev Size.instruction (i : Size) := Terminal.instruction i.S i.V i.t i.p i.w i.n
-- 读法：在后续公式中，`Size.price` 是 `Terminal.price i.W i.S i.V i.t i.V' i.k' i.p i.w i.n` 的缩写。
abbrev Size.price (i : Size) := Terminal.price i.W i.S i.V i.t i.V' i.k' i.p i.w i.n

-- 读法：要证明的命题是 `Work (fun i => (Payload.Script i.S.m i.S.m (a i) i.w i.n).width)`。这里调用 `le_of_eq`。
private theorem script (a : Size → ℕ) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => (Payload.Script i.S.m i.S.m (a i) i.w i.n).width) := by
  have row := Work.hosts (Short.long (w.short.add (he.mul w.short)))
  have span := Work.spans (ha.add ((num 3).short.mul w.short))
  have peer := Work.hosts (he.long.mul (m.add ha.long))
  refine (((row.add span).scale (num 2)).add peer).mono fun i => ?_
  simp only [Payload.Script, PeerLayout.input, PeerLayout.lengths, Fragments.Entry, Intervals.span,
    Format.width_pair, Format.width_vec, Format.width_addr, Size.spans, Size.hosts, pow_add]
  rw [Format.width_addr]
  exact le_of_eq (by ring)

-- 读法：要证明的命题是 `Work (fun i => i.instruction.width)`。
theorem instruction : Work (fun i => i.instruction.width) := by
  have h := script Size.p p links
  have e := script (fun _ => 0) (num 0).short (num 1).short
  refine ((h.add e).add headers).mono fun i => ?_
  rw [Size.instruction, Terminal.instruction, Format.width_pair, Format.width_pair]

-- 读法：要证明的命题是 `Work (fun i => i.W.shipment i.inner i.S.m i.V i.k i.S.m (X i) (J i) (a i) i.w i.n)`。
private theorem shipping (X J a : Size → ℕ) (hx : ∀ i, X i ≤ i.volume)
    (hj : Outer J) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => i.W.shipment i.inner i.S.m i.V i.k i.S.m (X i) (J i) (a i) i.w i.n) := by
  obtain ⟨K, hK⟩ := Prices.shipment_le
  have b := (((num 1000).add rate).add k).add hj
  have s := (((Outer.short b).add ha).add w.short).add n.short
  have l := ((((Short.long s).add m).add m).add limit).add threshold
  have posts := (num 2).short.mul he
  have names := Work.hosts ((Short.long posts).mul (l.pow K))
  have rows := Work.spans (posts.mul (s.pow K))
  have bits := Work.volume ((num 2).mul (b.pow K))
  refine (((inner.scale (num 4)).add (names.add rows)).add bits).mono fun i => ?_
  refine (hK i.F i.W i.inner i.S.m i.V i.k i.S.m (X i) (J i) (a i) i.w i.n).trans ?_
  apply Nat.add_le_add
  · apply Nat.add_le_add_left
    unfold Size.spans Size.hosts
    exact le_of_eq (by ring)
  · have hv := Nat.add_le_add (show i.V ≤ i.volume from Nat.le_add_right ..) (hx i)
    rw [← Nat.mul_two] at hv
    exact (Nat.mul_le_mul_right _ hv).trans_eq (mul_assoc ..)

-- 读法：要证明的命题是 `Work Size.price`。
theorem price : Work Size.price := by
  have a := shipping Size.V Size.k Size.p (fun _ => Nat.le_add_right ..) k p links
  have b := shipping Size.V' Size.k' (fun _ => 0) (fun _ => Nat.le_add_left ..) k' (num 0).short (num 1).short
  exact (((a.add b).add dictionary).add (((instruction.add outer).add inner).scale (num 64)))

-- 读法：存在 `K`，对每个 `i : Size`，`i.header + i.price` 不超过 `2 ^ i.S.m * (i.M ^ K + 2 ^ i.n * i.T ^ K) + (i.V + i.V') * i.B ^ K`。
theorem total : ∃ K, ∀ i : Size, i.header + i.price ≤
    2 ^ i.S.m * (i.M ^ K + 2 ^ i.n * i.T ^ K) + (i.V + i.V') * i.B ^ K := by
  obtain ⟨K, hK⟩ := header.add price
  exact ⟨K, fun i => (hK i).trans_eq (by unfold Size.bound Size.spans Size.hosts Size.volume; ring)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end
