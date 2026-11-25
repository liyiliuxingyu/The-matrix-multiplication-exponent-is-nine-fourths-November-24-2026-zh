-- 本文件所属证明环节：在按编号保存寄存器的形式电路与记录已得到多项式集合的无除法模型之间双向转译，两者都允许免费读取输入和域常数，且转译保持算术成本。由此识别两种矩形指数，并证明权重截到非负部分不改变结果。
import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent

/-! # 两种无除法电路模型之间保持成本的转换

Integral 模型记录已得到的多项式集合，形式程序模型显式地给寄存器编号。两种模型都允许免费装载输入和域常数。 -/

namespace OAI.LinearAlgebra.SpectralBooks

open OAI.MatrixMultiplication.Arithmetic
open MatrixExponent

variable {F : Type*} [Field F] {i j k : ℕ}

-- 读法：在后续公式中，`Inputs` 是 `MatrixInput i k j` 的缩写。
-- Inputs 把 Integral 的 (行,列,内维) 改排为 MatrixInput 接受的 (行,内维,列)；Poly 指定同一组矩阵输入的多项式环。
private abbrev Inputs (i j k : ℕ) := MatrixInput i k j
-- 读法：在后续公式中，`Poly` 是 `Integral.Poly F i j k` 的缩写。
private abbrev Poly (F : Type*) [Field F] (i j k : ℕ) := Integral.Poly F i j k

-- 读法：存在 `T`，`Integral.Build (Integral.initial F i j k) p.cost T` 与 `Integral.initial F i j k ⊆ T ∧ ∀ t, registerPolynomial p t ∈ T` 同时成立。对 `p` 作归纳。
/-- 依次读取各个寄存器，便能用相同的成本把对应的多项式加入可用集合。 -/
private theorem program_build {r : ℕ} (p : Program F (Inputs i j k) r) :
    ∃ T, Integral.Build (Integral.initial F i j k) p.cost T ∧
      Integral.initial F i j k ⊆ T ∧ ∀ t, registerPolynomial p t ∈ T := by
  -- 对程序的长度作结构归纳。维护的集合含全部初始多项式，也含到目前为止每个寄存器的值。
  induction p with
  | nil => exact ⟨_, .nil, Set.Subset.rfl, fun t => t.elim0⟩
  | step p g ih =>
    obtain ⟨T, build, initial, values⟩ := ih
    -- 先抽出公共步骤：若新集合包含旧值和刚算出的一个值，Fin.cases 即可区分新寄存器与全部旧寄存器。
    have step (g : Gate F (Inputs i j k) _) {U : Set (Poly F i j k)}
        (h : Integral.Build (Integral.initial F i j k) (p.cost + g.cost) U)
        (old : T ⊆ U) (new : gatePolynomial g (registerPolynomial p) ∈ U) :
        ∃ V, Integral.Build (Integral.initial F i j k) (p.step g).cost V ∧
          Integral.initial F i j k ⊆ V ∧ ∀ t, registerPolynomial (p.step g) t ∈ V :=
      ⟨U, h, initial.trans old, Fin.cases new (fun t => old (values t))⟩
    -- 常数门和输入门免费，并且其值已经在初始集合里；每种二元算术门则对应 Integral.Build 增加一步。
    cases g with
    | constant c => exact step _ build Set.Subset.rfl (initial (.inl ⟨c, rfl⟩))
    | input x => exact step _ build Set.Subset.rfl (initial (.inr ⟨x, rfl⟩))
    | add x y =>
      exact step _ (build.add (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)
    | sub x y =>
      exact step _ (build.sub (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)
    | mul x y =>
      exact step _ (build.mul (values x) (values y)) (Set.subset_insert ..) (Set.mem_insert ..)

-- 读法：`CanRead` 表示以下条件：对每个 `s : Finset (Poly F i j k)`，由 `(↑s : Set _) ⊆ T` 推出 `∃ (r : ℕ) (p : Program F (Inputs i j k) r), p.cost = cost ∧ ∀ v ∈ s, ∃ t, registerPolynomial p t = v`。
/-- 即使初始可用的常数形成一个无限集，实际程序也只需要能同时读取任意给定的有限个元素。 -/
private def CanRead (T : Set (Poly F i j k)) (cost : ℕ) : Prop :=
  ∀ s : Finset (Poly F i j k), (↑s : Set _) ⊆ T →
    ∃ (r : ℕ) (p : Program F (Inputs i j k) r), p.cost = cost ∧
      ∀ v ∈ s, ∃ t, registerPolynomial p t = v

-- 读法：要证明的命题是 `CanRead (Integral.initial F i j k) 0`。
-- 初始集合中任一有限选择都能免费载入。对每个所取多项式选择一个成本为零的常数表达式或输入表达式。
private theorem read_initial : CanRead (Integral.initial F i j k) 0 := by
  classical
  intro s hs
  have load (v : s) : ∃ e : Expression F (Inputs i j k),
      e.cost = 0 ∧ expressionPolynomial e = v.val := by
    rcases hs v.property with ⟨c, hc⟩ | ⟨x, hx⟩
    · exact ⟨.constant c, rfl, hc⟩
    · exact ⟨.input x, rfl, hx⟩
  -- 把有限族表达式一次编译成一个程序。每个所需值都取得一个输出寄存器，总成本仍为零。
  choose e cost value using load
  let p := Expression.compileFamily e
  refine ⟨_, p.program, p.cost_eq.trans (by simp [cost]), ?_⟩
  intro v hv
  exact ⟨p.output ⟨v, hv⟩, (registerPolynomial_compileFamily e ⟨v, hv⟩).trans (value ⟨v, hv⟩)⟩

-- 读法：要证明的命题是 `CanRead (insert (op x y) T) (m + 1)`。
-- 从“所有有限选择可读”推出增加一个二元运算后的同类性质。这一条同时适用于加法、减法和乘法。
private theorem read_binary {T : Set (Poly F i j k)} {m : ℕ} (h : CanRead T m)
    {x y : Poly F i j k} (hx : x ∈ T) (hy : y ∈ T)
    (op : Poly F i j k → Poly F i j k → Poly F i j k)
    (gate : ∀ {r : ℕ}, Fin r → Fin r → Gate F (Inputs i j k) (Fin r))
    (cost : ∀ {r} (a b : Fin r), (gate a b).cost = 1)
    (value : ∀ {r} (a b : Fin r) (v : Fin r → Poly F i j k),
      gatePolynomial (gate a b) v = op (v a) (v b)) :
    CanRead (insert (op x y) T) (m + 1) := by
  classical
  intro s hs
  -- 需在旧集合中读取两个操作数及原请求中的其余值。新值从请求中暂时删去，防止误用尚未计算的结果。
  let need := insert x (insert y (s.erase (op x y)))
  have old : (↑need : Set _) ⊆ T := by
    intro v hv
    simp only [need, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hv
    rcases hv with rfl | rfl | ⟨hne, hin⟩
    · exact hx
    · exact hy
    · exact (hs hin).resolve_left hne
  -- 先运行能读取 need 的旧程序，找出 x、y 的寄存器，然后添加一扇成本为一的门。
  -- 推导：从 `h need old` 中取出 `r, p, hp, read`。
  obtain ⟨r, p, hp, read⟩ := h need old
  obtain ⟨a, ha⟩ := read x (by simp [need])
  obtain ⟨b, hb⟩ := read y (by simp [need])
  refine ⟨_, p.step (gate a b), by simp [hp, cost], ?_⟩
  intro v hv
  -- 若所求正是新值，读第 0 号寄存器；否则沿旧下标的 succ 读取原有的值。
  by_cases he : v = op x y
  · exact ⟨0, by rw [registerPolynomial_zero, value, ha, hb, he]⟩
  · obtain ⟨t, ht⟩ := read v (by simp [need, he, hv])
    exact ⟨t.succ, ht⟩

-- 读法：要证明的命题是 `CanRead T m`。对 `h` 作归纳。
-- 对集合型电路的推导归纳。空推导调用零成本装载；三种算术步骤分别代入相应运算及门。
private theorem read_build {T : Set (Poly F i j k)} {m : ℕ}
    (h : Integral.Build (Integral.initial F i j k) m T) : CanRead T m := by
  induction h with
  | nil => exact read_initial
  | add _ hx hy ih =>
    exact read_binary ih hx hy (· + ·) Gate.add (fun _ _ => rfl) (fun _ _ _ => rfl)
  | sub _ hx hy ih =>
    exact read_binary ih hx hy (· - ·) Gate.sub (fun _ _ => rfl) (fun _ _ _ => rfl)
  | mul _ hx hy ih =>
    exact read_binary ih hx hy (· * ·) Gate.mul (fun _ _ => rfl) (fun _ _ _ => rfl)

-- 读法：`Integral.Computes F i j k m` 与 `∃ p : MatrixAlgorithm F i k j, FormalCorrect p ∧ p.cost = m` 等价。
/-- Integral 电路依次使用行数、列数与内维数来排列尺寸参数。 -/
private theorem computes_iff {m : ℕ} : Integral.Computes F i j k m ↔
    ∃ p : MatrixAlgorithm F i k j, FormalCorrect p ∧ p.cost = m := by
  classical
  -- 两个方向都保留恰等的成本 m。一边从最终集合读出全部矩阵坐标，另一边把形式程序逐门变成集合的构造。
  constructor
  · rintro ⟨T, h, out⟩
    -- 所有输出位置有限，因此它们的输出多项式组成有限集合，可以直接应用 read_build。
    let s := Finset.univ.image (Integral.output F (i := i) (j := j) (k := k))
    obtain ⟨r, p, hp, read⟩ := read_build h s (by
      rintro v hv
      -- 推导：从 `Finset.mem_image.mp hv` 中取出 `q, _, rfl`。
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hv
      exact out q)
    -- 给每个输出位置选一个读出寄存器。hidx 保证这些寄存器中的多项式逐项等于要求的矩阵乘积坐标。
    have entry (q : Integral.Pos i j) :=
      read (Integral.output F q) (Finset.mem_image_of_mem _ (Finset.mem_univ q))
    choose idx hidx using entry
    exact ⟨⟨r, p, fun a b => idx (a, b)⟩, fun a b => hidx (a, b), hp⟩
  · rintro ⟨p, correct, rfl⟩
    -- 反过来对程序调用 program_build；形式正确性说明输出寄存器中已有的值就是 Integral.output 指定的多项式。
    obtain ⟨T, build, _, read⟩ := program_build p.program
    refine ⟨T, build, fun q => ?_⟩
    -- 推导：记下中间结论 `eq`：`registerPolynomial p.program (p.output q.1 q.2) = Integral.output F q`。
    have eq : registerPolynomial p.program (p.output q.1 q.2) = Integral.output F q :=
      correct q.1 q.2
    rw [← eq]
    exact read (p.output q.1 q.2)

-- 读法：`formalOmega F a b c` 等于 `Integral.exponent F c b a`。
/-- 把边权的顺序换算为矩阵维数的顺序之后，两个模型中的容许指数一致。 -/
theorem formalOmega_eq_integral (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c = Integral.exponent F c b a := by
  -- 两个指数都是容许实数集合的下确界。证明每个 τ 的成员资格等价，再对相等集合取下确界。
  unfold formalOmega Integral.exponent
  congr 1
  ext τ
  change FormalAdmissibleExponent F a b c τ ↔ Integral.Admissible F c b a τ
  constructor
  -- 从形式模型的每个见证程序提取其成本及 Integral.Computes 见证；常数 C 和对每个 n 的原成本界保持不变。
  · intro h ε hε
    -- 推导：从 `h ε hε` 中取出 `C, hC, bound`。
    obtain ⟨C, hC, bound⟩ := h ε hε
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨p, correct, cost⟩ := bound n hn
    exact ⟨p.cost, computes_iff.mpr ⟨p, correct, rfl⟩, cost⟩
  -- 从 Integral 模型的见证还原出成本恰为 m 的正确程序。因此逆向转换也保留原来的增长界。
  · intro h ε hε
    obtain ⟨C, hC, bound⟩ := h ε hε
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨m, hm, cost⟩ := bound n hn
    obtain ⟨p, correct, rfl⟩ := computes_iff.mp hm
    exact ⟨p, correct, cost⟩

-- 读法：`wireDimension n (max w 0)` 等于 `wireDimension n w`。这里调用 `Nat.le_antisymm`。
-- 当 n≥1 且 w≤0 时，0<n^w≤1，其向上取整为 1，正好与 w=0 的尺寸一致；非负 w 的情况直接成立。
private theorem wireDimension_max_zero {n : ℕ} (hn : 1 ≤ n) (w : ℝ) :
    wireDimension n (max w 0) = wireDimension n w := by
  rcases le_total 0 w with hw | hw
  · rw [max_eq_left hw]
  -- 现在处理 w≤0 的分支。正性给出取整结果至少为 1，指数单调性给出它至多为 1。
  rw [max_eq_right hw]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [wireDimension, Real.rpow_zero, Nat.ceil_one]
  apply Nat.le_antisymm (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _))
  apply Nat.ceil_le.mpr
  simpa using Real.rpow_le_rpow_of_exponent_le hn' hw

-- 读法：`formalOmega F a b c` 等于 `formalOmega F (max a 0) (max b 0) (max c 0)`。
/-- 在每一个容许的规模上，负权重与零权重经过向上取整后得到相同的维数。 -/
theorem formalOmega_max_zero (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c = formalOmega F (max a 0) (max b 0) (max c 0) := by
  unfold formalOmega
  congr 1
  ext τ
  change FormalAdmissibleExponent F a b c τ ↔
    FormalAdmissibleExponent F (max a 0) (max b 0) (max c 0) τ
  -- 沿两个方向传递任意容许指数的程序和界。唯一须改写之处是三条边的取整尺寸，由上一条引理逐一处理。
  constructor <;> intro h ε hε <;> obtain ⟨C, hC, bound⟩ := h ε hε <;>
    refine ⟨C, hC, fun n hn => ?_⟩
  · rw [wireDimension_max_zero hn a, wireDimension_max_zero hn b, wireDimension_max_zero hn c]
    exact bound n hn
  · have hp := bound n hn
    rw [wireDimension_max_zero hn a, wireDimension_max_zero hn b, wireDimension_max_zero hn c] at hp
    exact hp

end OAI.LinearAlgebra.SpectralBooks
