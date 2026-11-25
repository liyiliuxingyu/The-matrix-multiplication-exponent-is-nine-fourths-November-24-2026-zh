-- 本文件所属证明环节：在同一个列表宽度上固定压缩次数，反复压低每份网络的成本并控制副本数，证明初始上界、多列表下界和可迭代压缩不可能同时成立。
import OAI.LinearAlgebra.MatrixExponent.ListBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # 固定列表字长时的压缩迭代 -/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

-- 读法：`w ≤ Nat.clog 2 (listBits w)` 与 `Nat.clog 2 (listBits w) ≤ w ^ 2` 同时成立。
-- 对 w≥2，列表输入位数的以二为底的向上取整对数在 w 与 w² 之间。这使得关于对数的估计可换为关于字长的估计。
private theorem clog_bounds {w : ℕ} (hw : 2 ≤ w) :
    w ≤ Nat.clog 2 (listBits w) ∧ Nat.clog 2 (listBits w) ≤ w ^ 2 := by
  have h : 2 * w ≤ 2 ^ w := by
    -- 先归纳证明 2w≤2^w，用于上界。下界则直接来自 listBits w≥2^w 和向上取整对数的单调性。
    induction w, hw using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  constructor
  · have hh := Nat.clog_mono_right 2
      (show 2 ^ w ≤ listBits w from Nat.le_mul_of_pos_left _ (by omega))
    rwa [Nat.clog_pow 2 w (by decide)] at hh
  · apply le_trans (b := w + w) _ (by nlinarith)
    apply Nat.clog_le_of_le_pow
    rw [listBits, pow_add]
    exact Nat.mul_le_mul_right _ h

-- 读法：对每个 `ᶠ w : ℕ in atTop`，`2 ≤ w` 与 `C ≤ (w : ℝ) ∧ 4 ≤ (w : ℝ) ^ b ∧ (w : ℝ) ^ (3 : ℝ) ≤ (listBits w : ℝ) ^ (1 / 40 : ℝ)` 同时成立。
-- 把后面反复使用的“大字长”条件合并：C≤w、w 的正幂足够大，而且 listBits 的一个小正幂最终控制 w³。
private theorem large {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧ C ≤ (w : ℝ) ∧ 4 ≤ (w : ℝ) ^ b ∧
      (w : ℝ) ^ (3 : ℝ) ≤ (listBits w : ℝ) ^ (1 / 40 : ℝ) := by
  have ht : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- 最后一项使用指数函数支配任意固定次幂的渐近比较，增长率取 log(2)/40。
  have he := isLittleO_rpow_exp_pos_mul_atTop 3 (by positivity : 0 < Real.log 2 / 40)
  filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop C,
    ((tendsto_rpow_atTop hb).comp ht).eventually_ge_atTop 4,
    ht.eventually he.eventuallyLE] with w hw hC hb' he'
  refine ⟨hw, hC, hb', ?_⟩
  calc
    (w : ℝ) ^ (3 : ℝ) ≤ Real.exp (Real.log 2 / 40 * w) := by
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (w : ℝ) ^ (3 : ℝ)),
        Real.norm_of_nonneg (Real.exp_nonneg _)] using he'
    _ = ((2 : ℝ) ^ w) ^ (1 / 40 : ℝ) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast (show 2 ^ w ≤ listBits w from Nat.le_mul_of_pos_left _ (by omega))

-- 读法：`m * h ^ (-γ) + e * h ^ (σ / 4)` 不超过 `m * w ^ (-b)`。
/-- 下界允许在每一步收缩时吸收加性开销，从而不必等到最后一步再对几何级数作估计。 -/
private theorem absorb {w h e m γ σ b : ℝ} (hw : 1 ≤ w)
    (hh : w ≤ h) (hh' : h ≤ w ^ 2) (hm : 0 ≤ m) (he : 0 ≤ e)
    (hlarge : 4 ≤ w ^ b) (hb : 0 < b) (hg : 2 * b ≤ γ) (hs : 2 * b ≤ σ / 2)
    (hlower : e * w ^ σ ≤ 3 * m) :
    m * h ^ (-γ) + e * h ^ (σ / 4) ≤ m * w ^ (-b) := by
  have hw' : 0 < w := zero_lt_one.trans_le hw
  -- 第一项 m·h^(−γ) 至多是 m·w^(−2b)，因为 h≥w 且 γ≥2b。
  have hleft : m * h ^ (-γ) ≤ m * w ^ (-(2 * b)) :=
    mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_nonpos hw' hh (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hw (neg_le_neg hg))) hm
  -- 在加性项中先使用 h≤w²，再利用下界 e·w^σ≤3m，把输入位数 e 换为网络规模 m。
  -- 推导：记下中间结论 `hright`：`e * h ^ (σ / 4) ≤ 3 * m * w ^ (-(2 * b))`。
  have hright : e * h ^ (σ / 4) ≤ 3 * m * w ^ (-(2 * b)) := by
    calc
      _ ≤ e * (w ^ 2) ^ (σ / 4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hw'.le.trans hh) hh' (by linarith)) he
      _ = (e * w ^ σ) * w ^ (-(σ / 2)) := by
        rw [← Real.rpow_natCast_mul hw'.le, mul_assoc, ← Real.rpow_add hw']
        congr 2
        ring
      _ ≤ 3 * m * w ^ (-(σ / 2)) := mul_le_mul_of_nonneg_right hlower (by positivity)
      _ ≤ 3 * m * w ^ (-(2 * b)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw (neg_le_neg hs))
          (by positivity)
  calc
    -- 两项相加得到 4m·w^(−2b)。由 4≤w^b 吸收常数 4，每步净缩减因子便是 w^(−b)。
    _ ≤ 4 * (m * w ^ (-(2 * b))) := by linarith
    _ ≤ w ^ b * (m * w ^ (-(2 * b))) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = m * w ^ (-b) := by
      rw [mul_left_comm, ← Real.rpow_add hw', show b + -(2 * b) = -b by ring]

-- 读法：要证明的命题是 `False`。
/-- 先固定迭代次数，再选取字长。副本总数和每比特的规模上界各自至多额外引入 1/40 的指数。 -/
theorem incompatible {P : ℕ → ℕ → ℕ → Prop}
    (seed : Seed P) (lower : ManyList P) (compress : Compression P) : False := by
  -- 从三个假设中依次选出初始网络常数、下界指数 σ，以及将压缩输入余量定为 σ/4 后得到的改进指数 γ。
  obtain ⟨C, hseed⟩ := seed
  obtain ⟨σ, hs, hlower⟩ := lower
  obtain ⟨γ, hg, hcompress⟩ := compress (σ / 4) (by positivity)
  -- 择 b 为 γ 与 σ/2 中较小者的一半，使 absorb 所需的两条不等式同时成立。
  let b := min γ (σ / 2) / 2
  have hb : 0 < b := half_pos (lt_min hg (half_pos hs))
  have hbg : 2 * b ≤ γ := by dsimp [b]; linarith [min_le_left γ (σ / 2)]
  -- 推导：记下中间结论 `hbs`：`2 * b ≤ σ / 2`。
  have hbs : 2 * b ≤ σ / 2 := by dsimp [b]; linarith [min_le_right γ (σ / 2)]
  -- 先取 J 使 Jb>3，再设每轮容许的副本增长指数 δ=1/(40J)。因此 J 轮后副本总增长指数仍为 1/40。
  obtain ⟨J, hJ⟩ := exists_nat_gt (3 / b)
  have hstop : 3 < (J : ℝ) * b := (div_lt_iff₀ hb).mp hJ
  have hJpos : 0 < (J : ℝ) := lt_trans (by positivity) hJ
  let δ := (1 / 40 : ℝ) / J
  have hδ : 0 < δ := div_pos (by norm_num) hJpos
  -- 所有“充分大”的条件只涉及已经选定的参数；将它们的最终成立区间相交，一次选取共同的字长 w。
  obtain ⟨w, ⟨hw, hC, hbpow, hcube⟩, ⟨m₀, h₀, hm₀⟩, hl, hc⟩ :=
    ((large hb C).and (hseed.and (hlower.and (hcompress δ hδ)))).exists
  let n := listBits w
  let h : ℝ := Nat.clog 2 n
  -- 推导：记下中间结论 `hh`：`(w : ℝ) ≤ h`。
  have hh : (w : ℝ) ≤ h := by unfold h; exact_mod_cast (clog_bounds hw).1
  have hh' : h ≤ (w : ℝ) ^ 2 := by unfold h; exact_mod_cast (clog_bounds hw).2
  have hw₁ : 1 ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hw₀ : 0 < (w : ℝ) := zero_lt_one.trans_le hw₁
  have hn : 0 < n := by unfold n listBits; positivity
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  -- 归纳中始终保持 t≤n^(jδ)。因为 j≤J，所以 t≤n^(1/40)≤n，始终落在多列表下界的适用范围内。
  have copies {j t : ℕ} (hj : j ≤ J) (ht : (t : ℝ) ≤ (n : ℝ) ^ ((j : ℝ) * δ)) :
      (t : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    apply ht.trans (Real.rpow_le_rpow_of_exponent_le hn₁ ?_)
    calc
      _ ≤ (J : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ.le
      _ = 1 / 40 := by unfold δ; field_simp
  have within {t : ℕ} (ht : (t : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ)) : t ≤ n := by
    -- 推导：记下中间结论 `h`：`(n : ℝ) ^ (1 / 40 : ℝ) ≤ n`。
    have h : (n : ℝ) ^ (1 / 40 : ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 40 : ℝ) ≤ 1)
    exact_mod_cast ht.trans h
  -- 迭代的两个预算分别控制副本数与网络规模。第 j 步时，单位输入的规模至多为 w^(3−jb)。
  have iterate (j : ℕ) (hj : j ≤ J) :
      ∃ t m : ℕ, 1 ≤ t ∧ P w t m ∧ (t : ℝ) ≤ (n : ℝ) ^ ((j : ℝ) * δ) ∧
        (m : ℝ) ≤ (t : ℝ) * n * (w : ℝ) ^ (3 - j * b) := by
    induction j with
    -- 初始只有一个列表，规模至多为 Cnw²。由 w≥C 把常数吸收进指数，得到 nw³。
    | zero =>
      refine ⟨1, m₀, le_rfl, h₀, by simp, ?_⟩
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero, one_mul]
      calc
        _ ≤ C * (n : ℝ) * (w : ℝ) ^ 2 := hm₀
        _ ≤ (w : ℝ) * n * (w : ℝ) ^ 2 := by gcongr
        _ = (n : ℝ) * (w : ℝ) ^ (3 : ℝ) := by norm_num; ring
    | succ j ih =>
      -- 推导：记下中间结论 `hj'`：`j ≤ J`。
      have hj' : j ≤ J := Nat.le_of_succ_le hj
      obtain ⟨t, m, ht, hp, htj, hmj⟩ := ih hj'
      have ht' := copies hj' htj
      -- 先对当前 t 个列表应用下界，为稍后的 absorb 作准备。再分别估计 t 与每比特规模，核对输入满足压缩的规模条件。
      have hl' := hl t m ht (within ht') hp
      have hper : (w : ℝ) ^ (3 - j * b) ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_le hw₁ (sub_le_self _ (by positivity))).trans hcube
      -- 两个额外因子都至多为 n^(1/40)。将它们与输入规模的 n 相乘，恰得 n^(21/20)。
      have hsize : (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ) := by
        calc
          _ ≤ (t : ℝ) * n * (w : ℝ) ^ (3 - j * b) := hmj
          _ ≤ (n : ℝ) ^ (1 / 40 : ℝ) * n * (n : ℝ) ^ (1 / 40 : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right ht' hn₀.le) hper (by positivity) (by positivity)
          _ = (n : ℝ) ^ (21 / 20 : ℝ) := by
            rw [show (21 / 20 : ℝ) = 1 / 40 + 1 + 1 / 40 by norm_num,
              Real.rpow_add hn₀, Real.rpow_add hn₀, Real.rpow_one]
      -- 压缩产生 d 个副本及新的规模 m′。更新 t 为 t·d；副本的乘积估计使用 d≤n^δ。
      -- 推导：从 `hc t m ht hp hsize` 中取出 `d, m', hd, hdδ, hp', hm'`。
      obtain ⟨d, m', hd, hdδ, hp', hm'⟩ := hc t m ht hp hsize
      refine ⟨t * d, m', Nat.mul_pos ht hd, hp', ?_, ?_⟩
      · rw [Nat.cast_mul, Nat.cast_succ, add_mul, one_mul, Real.rpow_add hn₀]
        exact mul_le_mul htj hdδ (by positivity) (by positivity)
      · calc
          -- 对单位副本的规模应用 absorb 消掉加性开销，再把因子 w^(−b) 合入归纳指数，完成第 j+1 轮。
          _ ≤ (d : ℝ) * ((m : ℝ) * h ^ (-γ) + t * (n : ℝ) * h ^ (σ / 4)) := hm'
          _ ≤ (d : ℝ) * ((m : ℝ) * (w : ℝ) ^ (-b)) :=
            mul_le_mul_of_nonneg_left
              (absorb hw₁ hh hh' (by positivity) (by positivity) hbpow hb hbg hbs hl'.le)
              (by positivity)
          _ ≤ (d : ℝ) * ((t : ℝ) * n * (w : ℝ) ^ (3 - j * b) * (w : ℝ) ^ (-b)) := by gcongr
          _ = ((t * d : ℕ) : ℝ) * n * (w : ℝ) ^ (3 - (j.succ : ℝ) * b) := by
            rw [Nat.cast_mul, Nat.cast_succ, show 3 - ((j : ℝ) + 1) * b =
              (3 - (j : ℝ) * b) + -b by ring, Real.rpow_add hw₀]
            ring
  -- 在第 J 轮，指数 3−Jb 已经为负，故 m≤t·n；可是多列表下界要求 t·n·w^σ<3m。
  -- 推导：从 `iterate J le_rfl` 中取出 `t, m, ht, hp, htJ, hmJ`。
  obtain ⟨t, m, ht, hp, htJ, hmJ⟩ := iterate J le_rfl
  apply (hl t m ht (within (copies le_rfl htJ)) hp).not_ge
  have hfinal : (m : ℝ) ≤ (t : ℝ) * n := by
    apply hmJ.trans
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hw₁ (by linarith))
  -- 由于 w^σ≥3，刚得到的规模上界又推出 3m≤t·n·w^σ，与严格不等式矛盾。
  have hthree : 3 ≤ (w : ℝ) ^ σ := (by linarith : 3 ≤ (w : ℝ) ^ b).trans
    (Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith))
  calc
    3 * (m : ℝ) = (m : ℝ) * 3 := mul_comm _ _
    _ ≤ (t : ℝ) * n * (w : ℝ) ^ σ := mul_le_mul hfinal hthree (by norm_num) (by positivity)

end OAI.LinearAlgebra.MatrixExponent
