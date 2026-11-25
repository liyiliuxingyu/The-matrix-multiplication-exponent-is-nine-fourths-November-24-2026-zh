-- 本文件所属证明环节：研究三个方向有不同尺寸权重时的乘法指数，给出循环对称、域专化、下界刚性与显式上界，再将素数域的公式转回任意域。
-- 本模块汇集矩形指数的上界、调和阈值以下的等式、刚性二择一及从素域到任意域的推广。
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Face.Contact
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold.Square
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Strict
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior.Convert
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Entropy
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Lower

/-! # 任意域上的矩形矩阵乘法

指数的上界以及调和阈值以下整个区域内的公式均无须额外假设。对于刚性的二择一结论，谱方法还需要正接触的传播。 -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {a b c : ℝ}

-- 读法：`exponent F a b c` 不超过 `U a b c`。按 `a = 0 ∨ b = 0 ∨ c = 0` 成立与否分情况。
theorem upper (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c ≤ U a b c := by
  -- 某一权重为零时，分别代入指数和基准函数的坐标面公式。其余情形三个权重均严格为正。
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0
  · rw [coordinate_plane F ha hb hc h, U_plane ha hb hc h]
  push Not at h
  -- 选取较小的基域 K，靠扩域不变性把指数改写到 K。在该域上把已证的支撑和对角估计用于正权重。
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  rw [exponent_extension K F ha hb hc]
  exact upper_of_diagonal (support K) (diagonal K)
    (ha.lt_of_ne' h.1) (hb.lt_of_ne' h.2.1) (hc.lt_of_ne' h.2.2)

-- 读法：要证明的命题是 `Admissible F a b c (U a b c)`。
/-- 完整基准函数给出形式算术电路的成本上界，允许在复杂度指数上附加任意小的正余量。 -/
theorem arithmetic_upper (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Admissible F a b c (U a b c) := by
  -- 从指数本身不超过 U，推出任意 ε>0 都有实际成本界。选一个可达到的 s<U+ε，再把其容许性中的余量取为 U+ε−s。
  intro ε hε
  have h := lt_add_of_le_of_pos (upper F ha hb hc) hε
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt ⟨_, volume_admissible F ha hb hc⟩ h
  obtain ⟨C, hC, hprog⟩ := hs (U a b c + ε - s) (sub_pos.mpr hlt)
  refine ⟨C, hC, ?_⟩
  simpa only [show s + (U a b c + ε - s) = U a b c + ε by ring] using hprog

-- 读法：`exponent F a b c` 等于 `a + b`。这里调用 `le_antisymm`。
-- 当 c≤ab/(a+b) 时，基准函数的正部修正项为零；此时指数恰好是 a+b。
theorem flat (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hc' : c ≤ a * b / (a + b)) : exponent F a b c = a + b := by
  have h : (a + b) * c ≤ a * b := by
    rw [mul_comm]; exact (le_div_iff₀ (add_pos ha hb)).mp hc'
  -- 阈值条件也保证 c≤min(a,b)。因此在基准函数的分支中，c 正好可作最小权重。
  have hmin : c ≤ min a b := by apply le_min <;> nlinarith
  have hu := upper F ha.le hb.le hc
  simp only [U, ite_eq_left hmin, benchmark, max_eq_right (sub_nonpos.mpr h), zero_pow
    (by decide : 2 ≠ 0), zero_div, add_zero] at hu
  -- 上界简化为 a+b；基本的负载下界给出反向不等式，合成等式。
  exact le_antisymm hu ((le_max_left _ _).trans (bounds F ha.le hb.le hc).1)

-- 读法：`a * b / (a + b)` 不超过 `dual F a b`。这里调用 `le_min`。
-- 以 c=ab/(a+b) 作为对偶指数定义中的一个可取权重。它位于区间内，并且刚证的平坦区公式在该点成立。
theorem dual_lower (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) ≤ dual F a b := by
  have h : 0 ≤ a * b / (a + b) := by positivity
  have h' : a * b / (a + b) ≤ min a b := by
    apply le_min <;> rw [div_le_iff₀ (add_pos ha hb)] <;> nlinarith
  exact le_csSup ⟨min a b, fun _ hc => hc.1.2⟩ ⟨⟨h, h'⟩, flat F ha hb h le_rfl⟩

-- 读法：要证明的命题是 `Rigidity F`。
-- 假设各域上都满足接触传播，就能证明任意目标域的矩形刚性。
theorem rigidity (h : ∀ (K : Type) [Field K], Propagation (Prices K))
    (F : Type*) [Field F] : Rigidity F := by
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  -- 在较小域 K 上应用 rigidity_of_contact。对刚性的两个分支各自使用扩域不变性，把指数结论带回 F。
  rcases rigidity_of_contact (support K) (diagonal K) (h K) with hK | hK
  · left
    intro a b c ha hb hc
    rw [exponent_extension K F ha.le hb.le hc.le]
    exact hK a b c ha hb hc
  · right
    intro a b c ha hb hc hactive
    rw [exponent_extension K F ha.le hb.le hc.le]
    exact hK a b c ha hb hc hactive

-- 读法：存在 `(p : ℕ) (_ : Fact p.Prime)`，`exponent (ZMod p) a b c` 严格小于 `s`。这里调用 `exponent_lt_of_rank`。
/-- 固定任一矩形形状后，若有严格的指数改进，则它可以在某个素域中实现。 -/
theorem prime_specialization {F : Type*} [Field F] {s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : exponent F a b c < s) :
    ∃ (p : ℕ) (_ : Fact p.Prime), exponent (ZMod p) a b c < s := by
  -- 从严格的指数不等式提取有限尺寸 n 和对应秩上界 r，随后将这个秩上界特殊化到有限特征。
  obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
  obtain ⟨K, _, _, hK⟩ := specializeRank hr
  -- 取 p 为所得域 K 的特征。由于 p 是素数，K 是素域 ZMod p 的代数；通过扩域不变性将同一严格改进转至素域。
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  refine ⟨p, inferInstance, ?_⟩
  rw [← exponent_extension (ZMod p) K ha hb hc]
  exact exponent_lt_of_rank ha hb hc hn hK hs

-- 读法：`MatrixExponent.omega F = 9 / 4` 与 `Rigidity F` 同时成立。这里调用 `hp.ne`。
-- 如果每个素域都满足方阵等式和刚性，就可将两项结论一起推广到任意域。
theorem of_prime_fields
    (h : ∀ (p : ℕ) [Fact p.Prime], MatrixExponent.omega (ZMod p) = 9 / 4 ∧ Rigidity (ZMod p))
    (F : Type*) [Field F] : MatrixExponent.omega F = 9 / 4 ∧ Rigidity F := by
  have he (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      exponent F a b c = U a b c := by
    -- 正权重情形已有 U 的上界。假设某个 F 上有严格改进，特殊化将给出一个素域上的严格改进，而那里已知取等。
    refine le_antisymm (upper F ha.le hb.le hc.le) ?_
    by_contra! hlt
    obtain ⟨p, _, hp⟩ := prime_specialization ha.le hb.le hc.le hlt
    exact hp.ne (positive_shapes (h p).2 (h p).1 ha hb hc)
  -- 再代入三个单位权重，具体算出方阵指数。所有正权重均取等的结论也给出刚性命题的第一个分支。
  have hs := he 1 1 1 zero_lt_one zero_lt_one zero_lt_one
  norm_num [square, U, benchmark] at hs
  exact ⟨hs, Or.inl he⟩

-- 读法：`MatrixExponent.omega F = 9 / 4` 与 `Rigidity F` 同时成立。使用 `of_prime_fields` 给出的结论。
-- 每个素域都是有限域，故对一切有限域成立的结论也满足上一个推广定理的条件。
theorem of_finite_fields
    (h : ∀ (K : Type) [Field K] [Finite K], MatrixExponent.omega K = 9 / 4 ∧ Rigidity K)
    (F : Type*) [Field F] : MatrixExponent.omega F = 9 / 4 ∧ Rigidity F :=
  of_prime_fields (fun p _ => h (ZMod p)) F

end OAI.LinearAlgebra.MatrixExponent.Rectangle
