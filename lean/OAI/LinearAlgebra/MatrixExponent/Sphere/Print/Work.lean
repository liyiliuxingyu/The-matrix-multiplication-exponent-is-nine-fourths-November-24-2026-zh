-- 本文件所属证明环节：用带标记点的球面张量、能量分级与费米子融合重写局部连线；控制跨缝合移动、选择项、宽度和最终站点表的大小。
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price

/-!
用只读取各宿主短数据的规则构造下一张宿主图。

**英文原文**

Build the next host graph from a rule reading only short per-host data.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring History.Reset

-- 读法：在后续公式中，`Rule` 是 `(Info e).obj → B w → (Child.Suffix (hops e) w (degree e w)).obj` 的缩写。
abbrev Rule (e w : ℕ) := (Info e).obj → B w → (Child.Suffix (hops e) w (degree e w)).obj

-- 读法：`build` 的结果类型为 `(Child.Graph (m + w) (degree e w)).obj`。
def build {m e : ℕ} (w : ℕ) (f : Rule e w) (r : (Tape m e).obj) :
    (Child.Graph (m + w) (degree e w)).obj :=
  Child.build m (hops e) w (degree e w)
    ((prepare r).1, fun i => f ((prepare r).2 (Match.rowIndex m w i).1) (Match.rowIndex m w i).2)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-!
并行构造短掩码，在局部应用任意给定规则，再用父节点的导航行恢复完整的子节点地址。

**英文原文**

Construct the short masks in parallel, apply an arbitrary rule locally,
then recover full child addresses using the parent navigation rows.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring History.Reset
open scoped Classical
variable (F : Type) [Field F] {m e w t : ℕ}

-- 读法：`cost` 的取值由 `2 ^ m * (100 + m + 2 ^ (1 + 2 ^ e + 12 * (2 ^ e) ^ 3 + 2 ^ w)) ^ 220` 给出。
def cost (m e w : ℕ) := 2 ^ m * (100 + m + 2 ^ (1 + 2 ^ e + 12 * (2 ^ e) ^ 3 + 2 ^ w)) ^ 220

-- 读法：映射 `prepare` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (m) * (100 + (t)) ^ (210)` 为上界。这里调用 `Nat.mul_le_mul_left`。
private theorem prepare_net (ht : m + 2 ^ (hops e) ≤ t) :
    Cheap F m t (Tape m e) (Query m e) prepare 210 := by
  have hm : m ≤ t := (Nat.le_add_right _ _).trans ht
  have hq : 2 ^ (hops e) ≤ t := by omega
  have he : 2 ^ e ≤ t := (Nat.pow_le_pow_right (by decide) (by simp [hops])).trans hq
  have ha : (Tape m e).width ≤ 2 ^ m * (100 + t) ^ 2 := by
    simp only [Tape, Header, Neighborhood.Rows, Format.width_pair, Format.width_vec, Format.width_addr,
      ← mul_add]
    rw [Format.width_bit, mul_one]
    apply Nat.mul_le_mul_left
    have h := Nat.mul_le_mul he hm
    ring_nf at h ⊢
    omega
  have src := Cheap.id F ha
  have g := src.fst.comp ((Neighborhood.cheap F m e 1 (by decide)).widen ht)
  have one := (g.pair src.fst).comp (Neighborhood.cheap_maskRows F hm hq he)
  have two := (g.pair g).comp (Neighborhood.cheap_maskRows F hm hq hq)
  exact (g.pair (src.snd.pair (one.pair two).zip).zip).mono (by decide)

-- 读法：在后续公式中，`Suffix` 是 `Child.Suffix (hops e) w (degree e w)` 的缩写。
private abbrev Suffix (e w : ℕ) := Child.Suffix (hops e) w (degree e w)

-- 读法：输入 `i` 时返回 `f (x (Match.rowIndex m w i).1) (Match.rowIndex m w i).2`。
private def suffixes (f : Rule e w) (x : (Format.vec m (Info e)).obj) :
    (Format.vec (m + w) (Suffix e w)).obj :=
  fun i => f (x (Match.rowIndex m w i).1) (Match.rowIndex m w i).2

-- 读法：要证明的命题是 `Install.Depends ((Format.vec (m + w) (Suffix e w)).code ∘ suffixes f ∘ (Format.vec m (Info e)).code.symm) (Info e).width`。用函数外延性比较等号两侧在 `a` 处的取值。
private theorem suffixes_local (f : Rule e w) :
    Install.Depends ((Format.vec (m + w) (Suffix e w)).code ∘ suffixes f ∘
      (Format.vec m (Info e)).code.symm) (Info e).width := by
  rintro ⟨i, j⟩
  let p := (Match.rowIndex m w i).1
  refine ⟨Finset.univ.image (Prod.mk p), Finset.card_image_le, fun x y he => ?_⟩
  have h : (Format.vec m (Info e)).code.symm x p = (Format.vec m (Info e)).code.symm y p := by
    apply (Info e).code.injective
    funext a
    exact (congrFun ((Format.vec m (Info e)).code.apply_symm_apply x) (p, a)).trans
      ((he (p, a) (Finset.mem_image_of_mem _ (Finset.mem_univ a))).trans
        (congrFun ((Format.vec m (Info e)).code.apply_symm_apply y) (p, a)).symm)
  exact congrArg (fun v => (Suffix e w).code (f v (Match.rowIndex m w i).2) j) h

-- 读法：映射 `(suffixes f)` 的输入宽度、输出宽度与编码电路规模之和以 `2 ^ (m) * (100 + (t)) ^ (6)` 为上界。
private theorem suffixes_net (hi : 2 ^ (Info e).width ≤ t) (hd : 2 ^ (degree e w) ≤ t)
    (f : Rule e w) :
    Cheap F m t (.vec m (Info e)) (.vec (m + w) (Suffix e w)) (suffixes f) 6 := by
  let I := (Info e).width
  let D := 2 ^ w * (Suffix e w).width
  have hI : I ≤ t := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans hi
  have hL : Install.localCost I ≤ 18 * t := by
    change 2 ^ I ≤ t at hi
    rw [Install.localCost, pow_succ]
    omega
  -- 推导：记下中间结论 `hl`：`hops e + w ≤ t`。
  have hl : hops e + w ≤ t := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans hd
  have hw : 2 ^ w ≤ t :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_left w (hops e))).trans hd
  have hD : D ≤ t * (2 + t * (3 + t)) := by
    apply Nat.mul_le_mul hw
    simp only [Suffix, Child.Suffix, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [Format.width_bit, Format.width_addr (hops e + 1)]
    exact Nat.add_le_add_left (Nat.mul_le_mul hd (by omega)) _
  refine ⟨_, (suffixes_local f).bnet F, ?_⟩
  let A := Format.vec m (Info e)
  let B := Format.vec (m + w) (Suffix e w)
  change A.width + B.width + (A.width + Install.localCost I * B.width) ≤ _
  -- 推导：记下中间结论 `hb`：`B.width = 2 ^ m * D`。
  have hb : B.width = 2 ^ m * D := by rw [Format.width_vec, pow_add, mul_assoc]
  rw [hb, show A.width = 2 ^ m * I from Format.width_vec _ _]
  calc
    _ = 2 ^ m * (I + D + (I + Install.localCost I * D)) := by ring
    _ ≤ 2 ^ m * (t + t * (2 + t * (3 + t)) + (t + 18 * t * (t * (2 + t * (3 + t))))) := by gcongr
    _ ≤ _ := by apply Nat.mul_le_mul_left; ring_nf; omega

-- 读法：`Child.buildCost m (hops e) w (degree e w)` 不超过 `2 ^ m * (100 + t) ^ 6`。
private theorem assemble_cost (hm : m ≤ t) (hd : 2 ^ (degree e w) ≤ t) :
    Child.buildCost m (hops e) w (degree e w) ≤ 2 ^ m * (100 + t) ^ 6 := by
  have hl : hops e + w ≤ t := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans hd
  have he : m + w + degree e w + hops e = m + (degree e w + degree e w) := by unfold degree hops; omega
  rw [Child.buildCost, he, pow_add, pow_add]
  calc
    _ ≤ 1000 * (2 ^ m * (t * t)) * (2 + t) * (4 + t + t) := by gcongr <;> omega
    _ ≤ _ := by ring_nf; omega

-- 读法：在 `F` 上按格式 `(Tape m e)`、`(Child.Graph (m + w) (degree e w))` 编码输入输出，映射 `(build w f)` 的电路规模至多为 `(cost m e w)`。
theorem build_net {m e : ℕ} (w : ℕ) (f : Rule e w) :
    Circuit F (Tape m e) (Child.Graph (m + w) (degree e w)) (build w f) (cost m e w) := by
  let b := 1 + 2 ^ e + 12 * (2 ^ e) ^ 3 + 2 ^ w
  let t := m + 2 ^ b
  have hi : (Info e).width ≤ b := by
    refine (le_of_eq ?_).trans (Nat.le_add_right (1 + 2 ^ e + 12 * (2 ^ e) ^ 3) (2 ^ w))
    simp only [Info, comparisons, Format.width_pair, Format.width_vec, hops, mul_one, pow_succ]
    rw [Format.width_bit]
    ring
  have hd : degree e w ≤ b := by
    have := Nat.lt_pow_self (n := e) (by decide : 1 < 2)
    have := Nat.lt_pow_self (n := w) (by decide : 1 < 2)
    unfold degree b
    omega
  have grow {a : ℕ} (h : a ≤ b) : 2 ^ a ≤ t :=
    (Nat.pow_le_pow_right (by decide) h).trans (Nat.le_add_left _ _)
  -- 推导：记下中间结论 `ht`：`m + 2 ^ (hops e) ≤ t`。
  have ht : m + 2 ^ (hops e) ≤ t := Nat.add_le_add_left
    (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right _ _).trans hd)) m
  have prep := prepare_net F ht
  have args := prep.fst.pair (prep.snd.comp (suffixes_net F (grow hi) (grow hd) f))
  obtain ⟨n, hnet, hn⟩ := args.mono (d := 219) (by decide)
  have net := hnet.comp (Child.build_net F m (hops e) w (degree e w))
  apply net.mono
  have hh := (assemble_cost (m := m) (Nat.le_add_right m (2 ^ b)) (grow hd)).trans
    (Nat.mul_le_mul_left (2 ^ m) (Nat.pow_le_pow_right (by positivity : 0 < 100 + t) (by decide : 6 ≤ 219)))
  unfold cost
  rw [add_assoc 100]
  change n + _ ≤ 2 ^ m * (100 + t) ^ 220
  rw [show 220 = 219 + 1 from rfl, pow_succ, ← mul_assoc]
  exact (show n + _ ≤ (2 ^ m * (100 + t) ^ 219) * 2 by omega).trans
    (Nat.mul_le_mul_left _ ((by decide : 2 ≤ 100).trans (Nat.le_add_right _ _)))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-!
# 在同一电路中写入复制的前缀树记录及其图

**英文原文**

Writing replicated trie records and their graph on one circuit
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}
open Assembly.History.Reset
variable (slot : Part M D k d ↪ B w)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)

-- 读法：在后续公式中，`graphFmt` 是 `Child.Graph (m + w) (degree e w)` 的缩写。
abbrev graphFmt (m e w : ℕ) := Child.Graph (m + w) (degree e w)

-- 读法：本声明给出 `writeCost` 的构造。
def writeCost (m e h l w : ℕ) := cost m e w +
  100 * ((input m e h l).width + (output m e h l w).width + (labels m h l w).width +
    (Tape m e).width + (graphFmt m e w).width)

variable {h l : ℕ}
local notation "A" => input m e h l
local notation "D₁" => output m e h l w
local notation "L" => labels m h l w
local notation "G" => graphFmt m e w

-- 读法：要证明的命题是 `Install.Depends ((L).code ∘ label w ∘ (A).code.symm) 1`。对 `q` 分类讨论。
private theorem label_depends :
    Install.Depends ((L).code ∘ label w ∘ (A).code.symm) 1 := by
  rintro ⟨i, j, s⟩
  obtain ⟨q, hq⟩ := Match.append_pin l w s
  let p := Match.rowIndex m w i
  have eq (x : (A).pins → Bool) :
      ((L).code ∘ label w ∘ (A).code.symm) x (i, j, s) =
        Sum.elim (fun v => x (.inl (p.1, .inr (j, v)))) ((Format.addr w).code p.2) q := by
    refine (hq _ _).trans ?_
    cases q with
    | inl v => exact congrFun ((A).code.apply_symm_apply x) (.inl (p.1, .inr (j, v)))
    | inr _ => rfl
  cases q with
  | inl v =>
    refine ⟨{.inl (p.1, .inr (j, v))}, by simp, fun x y he => ?_⟩
    rw [eq, eq]
    exact he _ (by simp)
  | inr _ => exact ⟨∅, by simp, fun x y _ => (eq x).trans (eq y).symm⟩

variable (F : Type) [Field F]

-- 读法：在 `F` 上按格式 `(.pair G L)`、`D₁` 编码输入输出，映射 `join` 的电路规模至多为 `((Format.pair G L).width + 2 * (D₁).width)`。这里调用 `Circuit.project`。
private theorem join_net :
    Circuit F (.pair G L) D₁ join ((Format.pair G L).width + 2 * (D₁).width) := by
  let i : (D₁).pins → (Format.pair G L).pins
    | .inl (v, .inl j) => .inl (.inl (v, j))
    | .inl (v, .inr j) => .inr (v, j)
    | .inr (v, .inl j) => .inl (.inr (v, .inl j))
    | .inr (v, .inr (.inl j)) => .inl (.inr (v, .inr j))
    | .inr (v, .inr (.inr j)) => .inr (v, j)
  exact Circuit.project i (by rintro r (⟨v, j|j⟩ | ⟨v, j|j|j⟩) <;> rfl)

-- 读法：在 `F` 上按格式 `A`、`D₁` 编码输入输出，映射 `(write slot hD hd hc hb)` 的电路规模至多为 `(writeCost m e h l w)`。这里调用 `Circuit.project`。
theorem write_net : Circuit F A D₁ (write slot hD hd hc hb) (writeCost m e h l w) := by
  have prep : Circuit F A (Tape m e) tape ((A).width + 2 * (Tape m e).width) := by
    apply Circuit.project («A»:=A) (D:=Tape m e) (Sum.map (fun p => (p.1, .inl p.2)) id)
    rintro r (i|i) <;> rfl
  have head : Circuit F (Tape m e) G (graph slot hD hd hc hb) (cost m e w) :=
    build_net F w (record slot hD hd hc hb)
  have body : Circuit F A L (label w) ((A).width + 34 * (L).width) := label_depends.bnet F
  exact (((prep.comp head).pair body).comp (join_net F)).mono (by
    unfold writeCost
    rw [Format.width_pair (graphFmt m e w)]
    omega)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-!
# 终止球面配置的受控展开

**英文原文**

Controlled expansion of a terminal sphere configuration
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K N X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F r₀ t₀ Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K N S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I N P.Occupied P.grid.Seam Z X}
  {G : Record F r₀ t₀ P.Occupied P.grid.Seam K N}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option N → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

variable {tape : S.format.obj} {pres : S.Presentation tape P.diagram}

-- 读法：`release` 的结果类型为 `U.Release pres data status (fun x y => ∑ i, s.value j (Q.init x y i)) σ`。
/-- 所有配置共用一个解码器。其标量、对应项和精确物理表示都取自同一条终止记录带。

英文原文：All profiles share the same decoder. Their scalar, term and exact
physical presentation are drawn from a single terminal tape.
-/
def release (keeps : Keeps Q left right pres a.coord) (hn : Nonempty P.V)
    (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b c)
    (hr : r₀ = M * r) (ht : t₀ = M * t) (ha : r₀ = c * b) (hb : t₀ = c)
    (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hc : Input.terminalExponent g σ * D * T ≤ u * U.cap) (hz : depth σ D g j (c * b) < 2 ^ z) :
    U.Release pres data status (fun x y => ∑ i, s.value j (Q.init x y i)) σ := by
  apply Classical.choice
  subst r₀ t₀
  obtain ⟨G₀, B, hl, hr, cap⟩ := H.capacity bound sc ha hb hM hk hu hc hz
  have ke : Keeps Q B.rules.left B.rules.right pres a.coord := by rw [hl, hr]; exact keeps
  exact ⟨{
    I := Layout.Profile s.scene.cell s.scene.level
    finite := Input.FinalBounds.profileType _ _
    select := B.select
    coeff := Layout.Profile.sign
    term := B.term
    value := B.value
    bound := fun i => (cap i).1
    populated := fun i => B.populated i hn
    valid := B.score
    shows := fun i => B.shows i (cap i).2
    retains := fun i => B.retains i (B.frame i (cap i).2) rfl pres ke
    reciprocal := by
      intro v i hi
      simp only [H.graph] at hi ⊢
      exact H.parents.reciprocal v i hi
  }⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-!
# 加权输出程序的端口与价格

**英文原文**

Ports and price of the weighted printer
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open scoped Classical

variable {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h ℓ M r t q D k n u j z)

-- 读法：在后续公式中，`before` 是 `U.rows.pair ((Children.Header m d).pair Z)` 的缩写。
abbrev before (Z : Format) := U.rows.pair ((Children.Header m d).pair Z)
-- 读法：在后续公式中，`after` 是 `(U.rows.pair U.template.format).pair Z` 的缩写。
abbrev after (Z : Format) := (U.rows.pair U.template.format).pair Z
-- 读法：在后续公式中，`volume` 是 `2 ^ h * (2 ^ ((d + 1) * 1) * (ℓ + U.digits))` 的缩写。
abbrev volume := 2 ^ h * (2 ^ ((d + 1) * 1) * (ℓ + U.digits))

-- 读法：`printCost` 的构造用到 `p.fee`、`U.volume`、`U.digits`。
def printCost (p : Contraction.Prices F) (Z : Format) :=
  let a := p.fee (m + (d + 1) * 1) U.volume
  waveCost m d h 1 1 U.volume a U.volume a (.addr ℓ) (.addr U.digits) (.addr U.window.width) +
    4 * Children.writeCost m d h U.window.width U.childBits +
    100 * (U.rows.width + U.selectors.width + (Children.Header m d).width + Z.width + U.template.format.width)

-- 读法：`price` 的取值由 `U.printCost p Z + 4 * U.selectors.width` 给出。
def price (p : Contraction.Prices F) (Z : Format) := U.printCost p Z + 4 * U.selectors.width

-- 读法：`next` 的取值由 `((x.1, U.advance x.1 x.2.1 c), x.2.2)` 给出。
def next {Z : Format} (x : (U.before Z).obj) (c : U.selectors.obj) : (U.after Z).obj :=
  ((x.1, U.advance x.1 x.2.1 c), x.2.2)

omit [Finite K] in
-- 读法：`Processor.arity U.gate` 等于 `2 * U.window.width`。
theorem arity : Processor.arity U.gate = 2 * U.window.width := by
  simp only [Processor.arity, gate, weightTable, Assembly.lookup, wd_word, Format.width_addr, two_mul]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# 核验选择器带并输出相应的项及其权重

**英文原文**

Checking a selector tape and printing its term with its weight
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open scoped Classical

variable {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h ℓ M r t q D k n u j z)
  {Z : Format} (p : Contraction.Prices F) {s : ℕ} {L : Set (Table F)}
  (hu : 3 ≤ s) (hw : 2 * U.window.width ≤ s) (hm : m + (d + 1) * 1 ≤ p.w) (hk : U.gate ∈ L)

-- 读法：在后续公式中，`A` 是 `(U.before Z).pair U.selectors` 的缩写。
private abbrev A (Z : Format) := (U.before Z).pair U.selectors
-- 读法：在后续公式中，`Header` 是 `Children.Header m d` 的缩写。
private abbrev Header := Children.Header m d
-- 读法：在后续公式中，`Wave` 是 `Fmt.waveIn m d h (.addr ℓ) (.addr U.digits)` 的缩写。
private abbrev Wave := Fmt.waveIn m d h (.addr ℓ) (.addr U.digits)
-- 读法：在后续公式中，`Saved` 是 `U.rows.pair Z` 的缩写。
private abbrev Saved (Z : Format) := U.rows.pair Z
-- 读法：在后续公式中，`B₁` 是 `((Wave U).pair (Header (m:=m) (d:=d))).pair (Saved U Z)` 的缩写。
private abbrev B₁ (Z : Format) := ((Wave U).pair (Header (m:=m) (d:=d))).pair (Saved U Z)
-- 读法：在后续公式中，`B₂` 是 `U.template.format.pair (Saved U Z)` 的缩写。
private abbrev B₂ (Z : Format) := U.template.format.pair (Saved U Z)

-- 读法：`divide` 的取值由 `(((x.1.1, x.2), x.1.2.1), x.1.1, x.1.2.2)` 给出。
private def divide (x : (A U Z).obj) : (B₁ U Z).obj := (((x.1.1, x.2), x.1.2.1), x.1.1, x.1.2.2)
-- 读法：`packTerm` 的取值由 `((x.2.1, x.1), x.2.2)` 给出。
private def packTerm (x : (B₂ U Z).obj) : (U.after Z).obj := ((x.2.1, x.1), x.2.2)

omit [Finite K] in
-- 读法：在 `F` 上按格式 `(A U Z)`、`(B₁ U Z)` 编码输入输出，映射 `(divide U)` 的电路规模至多为 `((A U Z).width + 2 * (B₁ U Z).width)`。这里调用 `Circuit.project`。
private theorem divide_net : Circuit F (A U Z) (B₁ U Z) (divide U)
    ((A U Z).width + 2 * (B₁ U Z).width) := by
  let addr : (B₁ U Z).pins → (A U Z).pins
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr i)) => .inr i
    | .inl (.inr i) => .inl (.inr (.inl i))
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inl (.inr (.inr i))
  exact Circuit.project addr (by rintro x (((i|i)|i)|(i|i)) <;> rfl)

-- 读法：在 `F` 上按格式 `(B₂ U Z)`、`(U.after Z)` 编码输入输出，映射 `(packTerm U)` 的电路规模至多为 `((B₂ U Z).width + 2 * (U.after Z).width)`。这里调用 `Circuit.project`。
private theorem pack_net : Circuit F (B₂ U Z) (U.after Z) (packTerm U)
    ((B₂ U Z).width + 2 * (U.after Z).width) := by
  let addr : (U.after Z).pins → (B₂ U Z).pins
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr i) => .inl i
    | .inr i => .inr (.inr i)
  exact Circuit.project addr (by rintro x ((i|i)|i) <;> rfl)

include hu hw hm hk in
-- 读法：这里调用 `Nat.mul_le_mul_left`。
theorem computes {I : Type*} (x : I → (U.before Z).obj) (c : I → U.selectors.obj)
    (hr : ∀ i, Fmt.Reciprocal (.vec h (.addr ℓ)) (x i).1) :
    Computes F s L ((U.before Z).pair U.selectors) (U.after Z)
      (fun i => (x i, c i)) (fun i => U.next (x i) (c i)) (fun i => U.score (x i).1 (c i))
      (U.printCost p Z) := by
  let src (i : I) : (A U Z).obj := (x i, c i)
  have ha := p.access (L:=L) hu (by omega) hm U.volume
  have h₁ : (Format.vec h (Format.pair (.addr ℓ) (.addr U.digits))).width ≤ U.volume := by
    simp only [Format.width_vec, Format.width_pair, Format.width_addr]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  -- 推导：记下中间结论 `h₂`：`(Format.vec h (Fmt.view d 1 (.pair (.addr ℓ) (.addr U.digits)))).width ≤ U.volume`。
  have h₂ : (Format.vec h (Fmt.view d 1 (.pair (.addr ℓ) (.addr U.digits)))).width ≤ U.volume := by
    simp only [Fmt.view, Format.width_vec, Format.width_pair, Format.width_addr]
    exact le_rfl
  have hf : U.window.width + (Format.addr U.window.width).width ≤ s := by
    rw [Format.width_addr, ← two_mul]; exact hw
  have wave := computes_wave (D:=.addr U.window.width) hu (by decide : 0 < 1) (by decide : 0 < 1)
    ha ha h₁ h₂ (Surface.Local.Design.number U.window) U.tariff hf hk
    (fun i => ((x i).1, c i)) hr
  have start := Computes.of_map (L:=L) (x:=src) (Map.circuit hu (divide_net U)) (fun _ => rfl)
  have hdr := Computes.of_map (L:=L) (x:=fun i => (x i).2.1)
    (Map.circuit hu (Circuit.id F (Children.Header m d))) (fun _ => rfl)
  -- 推导：记下中间结论 `keep`：`= Computes.of_map (L`。
  have keep := Computes.of_map (L:=L) (x:=fun i => ((x i).1, (x i).2.2))
    (Map.circuit hu (Circuit.id F (Saved U Z))) (fun _ => rfl)
  have draw := Map.circuit (L:=L) hu (Children.write_net (m:=m) (h:=h) (l:=U.window.width)
    U.slot U.dyadic U.large U.chunks U.degree F)
  have print := (wave.par hdr).comp (Computes.of_map draw (fun _ => rfl))
  have together := start.comp (print.par keep)
  have net := together.comp (Computes.of_map (Map.circuit hu (pack_net U)) (fun _ => rfl))
  simp only [one_mul, mul_one] at net
  refine net.mono ?_
  unfold printCost
  simp only [A, B₁, B₂, Wave, Saved, Header, before, after, Fmt.waveIn, rows, selectors, childBits, Nat.mul_one, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# 对共享输出程序发出的各项求和

**英文原文**

Summing the terms emitted by a shared printer
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open scoped Classical

variable {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h ℓ M r t q D k n u j z)
    {Z : Format} (p : Contraction.Prices F) {s : ℕ} {L : Set (Table F)}

universe v
variable {x y : Wire} {I J : Type v}
  {f : I → Val x → Val y → F} {g : J → Val x → Val y → F}
  {X : I → Val x → Val y → (U.before Z).obj} {Y : J → Val x → Val y → (U.after Z).obj}

-- 读法：要证明的命题是 `Transforms F s L ⟨I, f, U.before Z, X⟩ ⟨J, g, U.after Z, Y⟩ (U.price p Z)`。
theorem transfer (A : Selected ⟨I, f, U.before Z, X⟩ ⟨J, g, U.after Z, Y⟩ U.selectors)
    (hu : 3 ≤ s) (hw : 2 * U.window.width ≤ s) (hm : m + (d + 1) * 1 ≤ p.w) (hk : U.gate ∈ L)
    (hr : ∀ i a b, Fmt.Reciprocal (.vec h (.addr ℓ)) (X i a b).1)
    (hv : ∀ i a b c, U.score (X i a b).1 c = ((A.index i).read c).elim 0 (A.scalar i))
    (he : ∀ i a b c, U.next (X i a b) ((A.index i).write c) = Y (A.next i c) a b) :
    Transforms F s L ⟨I, f, U.before Z, X⟩ ⟨J, g, U.after Z, Y⟩ (U.price p Z) := by
  let B := I × Val x × Val y × U.selectors.obj
  let data : B → (U.before Z).obj := fun i => X i.1 i.2.1 i.2.2.1
  let choice : B → U.selectors.obj := fun i => i.2.2.2
  obtain ⟨k, hk, eval⟩ := U.computes p hu hw hm hk data choice (fun i => hr i.1 i.2.1 i.2.2.1)
  refine Transforms.of_selector hu A hk fun i a b c t => ?_
  have eq := eval (i, a, b, c) t
  dsimp only [data, choice] at eq
  change k (X i a b, c) t = _
  rw [eq, hv]
  cases h : (A.index i).read c with
  | none => simp
  | some j =>
    rw [(A.index i).valid _ _ |>.mp h]
    exact congrArg (fun v => @ite F (v = t) (Classical.propDecidable _) (A.scalar i j) 0) (he i a b j)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
分别计算宿主寻址的成本和每个块都要负担的成本。

**英文原文**

Separate the cost of addressing hosts from the cost paid in every block.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds Surface.Local

-- 读法：`1 + a.Y + a.Y` 不超过 `a.Y ^ 4`。
private theorem spare (a : Rates) : 1 + a.Y + a.Y ≤ a.Y ^ 4 := by
  have hh := a.short
  calc
    _ ≤ a.Y ^ 2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

-- 读法：`a.Host 221 (Children.writeCost a.m d a.h l w)` 与 `a.Host 10 (Children.output a.m d a.h l w).width ∧ a.Host 2 (Children.Header a.m d).width` 同时成立。这里调用 `Rates.Row.hosts`。
private theorem write_bound (a : Rates) (d l w : ℕ)
    (hd : 2 ^ d ≤ a.Y) (hl : l + w ≤ a.Y) (hw : 2 ^ w ≤ a.Y)
    (hg : 2 ^ (Children.degree d w) ≤ a.Y) (hc : 2 ^ (1 + 2 ^ d + 12 * (2 ^ d) ^ 3 + 2 ^ w) ≤ a.Y) :
    a.Host 221 (Children.writeCost a.m d a.h l w) ∧
    a.Host 10 (Children.output a.m d a.h l w).width ∧ a.Host 2 (Children.Header a.m d).width := by
  have big := a.long
  have room := spare a
  have hr : a.Host 2 (Children.Header a.m d).width := by
    simp only [Children.Header, Format.width_vec, Format.width_pair]
    rw [Format.width_bit, mul_one]
    exact (Rates.Row.hosts (Rates.big (by omega : 1 + 2 ^ d ≤ a.X))).up (by decide)
  have hin : a.Host 6 (Children.input a.m d a.h l).width := by
    rw [Format.width_pair]
    exact (a.rows d (.addr l) hd (by rw [Format.width_addr]; omega)).plus hr
  have ht : a.Host 6 (Children.Tape a.m d).width := by
    apply le_trans _ hin
    simp only [Children.Tape, Children.input, Format.width_pair, Neighborhood.Rows,
      Format.width_vec, Format.width_addr]
    gcongr
    exact Nat.le_add_right ..
  have ht' : a.Host 5 (Children.labels a.m a.h l w).width := by
    simp only [Children.labels, Format.width_vec]
    rw [Format.width_addr]
    exact Rates.Row.fan (Rates.low (by omega : l + w ≤ a.Y ^ 4)) hw
  have graph : a.Host 4 (Children.graphFmt a.m d w).width := by
    -- 推导：记下中间结论 `h`：`= Rates.Row.fan ((Rates.big (a`。
    have h := Rates.Row.fan ((Rates.big (a := a) (by omega : 2 ≤ a.X)).plus
      ((Rates.big (a := a) (by omega : a.m + w + 2 ≤ a.X)).times hg)) hw
    apply le_trans _ h
    simp only [Children.graphFmt, History.Reset.Child.Graph, Neighborhood.Rows, Group.Flags,
      Format.width_pair, Format.width_vec]
    rw [Format.width_bit, Format.width_addr]
    exact le_of_eq (by ring)
  have hout : a.Host 10 (Children.output a.m d a.h l w).width := by
    have h := (graph.plus (ht'.scale 2)).up (by decide : 7 ≤ 10)
    apply le_trans _ h
    simp only [Children.output, Children.graphFmt, History.Reset.Child.Graph, Children.labels,
      Neighborhood.Rows, Format.width_pair, Format.width_vec, Format.width_addr]
    exact le_of_eq (by ring)
  have hcost : a.Host 220 (Children.cost a.m d w) :=
    Rates.Row.hosts (Rates.high (Nat.pow_le_pow_left (by omega) _))
  exact ⟨hcost.plus (((((hin.plus hout).plus ht').plus ht).plus graph).scale 100), hout, hr⟩

variable {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
  (U : Printer F K N m d h ℓ M r t q D k n u j z)

-- 读法：`U.price p Z` 不超过 `2 ^ m * X ^ 225 + 2 ^ (m + h) * Y ^ 225 + 100 * Z.width`。
/-- 未作改动的寄存器产生一项加性费用，与两种宽度预算均无关。

英文原文：The untouched register has an additive charge independent of both width budgets.
-/
theorem work_bound (p : Contraction.Prices F) (Z : Format) (X Y : ℕ)
    (hl : 1000 + 10 * m + 10 * Y ≤ X) (hw : 1 + p.w ^ p.power ≤ X)
    (hY : 10000 + 1 + p.W + U.window.width + U.labelBits + 2 ^ (d + 1) + 2 ^ U.childBits+
      2 ^ U.template.scheme.d + 2 ^ (1 + 2 ^ d + 12 * (2 ^ d) ^ 3 + 2 ^ U.childBits) ≤ Y) :
    U.price p Z ≤ 2 ^ m * X ^ 225 + 2 ^ (m + h) * Y ^ 225 + 100 * Z.width := by
  obtain ⟨hy, hW, hv, hL, hd, hc, hg, he⟩ :
      10000 ≤ Y ∧ 1 + p.W ≤ Y ∧ U.window.width ≤ Y ∧ U.labelBits ≤ Y ∧
      2 ^ (d + 1) ≤ Y ∧ 2 ^ U.childBits ≤ Y ∧ 2 ^ U.template.scheme.d ≤ Y ∧
      2 ^ (1 + 2 ^ d + 12 * (2 ^ d) ^ 3 + 2 ^ U.childBits) ≤ Y := by
    generalize 2 ^ (1 + 2 ^ d + 12 * (2 ^ d) ^ 3 + 2 ^ U.childBits) = b at hY ⊢
    generalize 2 ^ U.template.scheme.d = g,
      2 ^ U.childBits = c, 2 ^ (d + 1) = e at hY ⊢
    omega
  let a : Rates := ⟨m, h, X, Y, hy, hl⟩
  -- 推导：记下中间结论 `room`：`1 + Y + Y ≤ Y ^ 4`。
  have room : 1 + Y + Y ≤ Y ^ 4 := spare a
  have hd' : 2 ^ d ≤ Y := (Nat.pow_le_pow_right (by decide) (Nat.le_succ d)).trans hd
  have hn : 2 ^ ((d + 1) * 1) ≤ Y := by simpa using hd
  have hh : 2 ^ ((d + 1) * 1) * (ℓ + U.digits) ≤ Y := by
    rw [window_width] at hv
    exact (Nat.le_mul_of_pos_left _ (by positivity)).trans hv
  have hh' : ℓ + U.digits ≤ Y := (Nat.le_mul_of_pos_left _ (by positivity)).trans hh
  have vol : a.Row 4 U.volume := Rates.low (show 2 ^ ((d + 1) * 1) * (ℓ + U.digits) ≤ Y ^ 4 by omega)
  have fee := a.fee p _ _ hn hW hw vol
  have wave := a.wave d 1 1 _ _ _ _ (.addr ℓ) (.addr U.digits) (.addr U.window.width)
    hd' hn hn vol fee vol fee (by
      rw [Format.width_addr]
      change 1 + U.window.width + U.window.width ≤ Y ^ 4
      omega)
  -- 推导：从 `write_bound a d U.window.width U.childBits hd' hL hc hg he` 中取出 `write, out, header`。
  obtain ⟨write, out, header⟩ := write_bound a d U.window.width U.childBits hd' hL hc hg he
  have rows := a.rows d (.addr ℓ) hd' (by rw [Format.width_addr]; change ℓ ≤ Y ^ 4; omega)
  have sel : a.Host 4 U.selectors.width := by
    rw [selectors, Format.width_vec, Format.width_vec, Format.width_addr]
    exact Rates.Row.hosts (Rates.low (show U.digits ≤ Y ^ 4 by omega))
  have parts := (((rows.plus sel).plus header).plus out).scale 100
  have total := ((wave.plus (write.scale 4)).plus parts).plus (sel.scale 4)
  rw [pow_add]
  refine le_trans ?_ (Nat.add_le_add_right total (100 * Z.width))
  simp only [price, printCost]
  change _ ≤ _ + 4 * Children.writeCost m d h U.window.width U.childBits +
    100 * (U.rows.width + U.selectors.width + (Children.Header m d).width + U.template.format.width) +
    4 * U.selectors.width + 100 * Z.width
  dsimp only [a]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
