import OAI.LinearAlgebra.MatrixExponent.RationalCircuits

/-!
# 形式算术电路中的非标量乘除门

沿用上游的有理函数导线、初始导线和形式输出。每个加、减、乘、除门都令
总步数增加一；另一个计数器按论文引理 2.4 的规则记录非标量门。
是否为标量取决于导线代表的有理函数是否来自基域，因而消去后等于常数的
表达式也按常数处理。有限域上仍按形式有理函数恒等来判定。
-/

namespace OAI.LinearAlgebra.MatrixExponent

/-- 导线的值是基域元素在电路运算域中的像。 -/
def IsScalar (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] (x : K) : Prop :=
  ∃ c : F, algebraMap F K c = x

/-- `NonscalarBuild F S m q T` 从初始导线集 `S` 经 `m` 个门得到可用导线集
`T`，其中恰有 `q` 个非标量乘除门。导线可以重复使用，所有除数均须非零。 -/
inductive NonscalarBuild (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    (S : Set K) : ℕ → ℕ → Set K → Prop
  | nil : NonscalarBuild F S 0 0 S
  | add {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      NonscalarBuild F S (m + 1) q (insert (x + y) T)
  | sub {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      NonscalarBuild F S (m + 1) q (insert (x - y) T)
  -- 乘积只要有一个因子是标量，就保留原计数 q。
  | mulScalarLeft {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      IsScalar F x → NonscalarBuild F S (m + 1) q (insert (x * y) T)
  | mulScalarRight {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      IsScalar F y → NonscalarBuild F S (m + 1) q (insert (x * y) T)
  -- 商只按除数分类。除数非常数时，即使分子是零也要计数。
  | divScalar {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      y ≠ 0 → IsScalar F y → NonscalarBuild F S (m + 1) q (insert (x / y) T)
  | mul {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      ¬ IsScalar F x → ¬ IsScalar F y →
      NonscalarBuild F S (m + 1) (q + 1) (insert (x * y) T)
  | div {m q T x y} : NonscalarBuild F S m q T → x ∈ T → y ∈ T →
      y ≠ 0 → ¬ IsScalar F y →
      NonscalarBuild F S (m + 1) (q + 1) (insert (x / y) T)

/-- 忽略非标量门计数，逐步得到同一导线集和同一步数的上游电路。 -/
theorem NonscalarBuild.toBuild {F K : Type*} [Field F] [Field K] [Algebra F K]
    {S T : Set K} {m q : ℕ} (h : NonscalarBuild F S m q T) : Build S m T := by
  induction h with
  | nil => exact .nil
  | add _ hx hy ih => exact .add ih hx hy
  | sub _ hx hy ih => exact .sub ih hx hy
  | mulScalarLeft _ hx hy _ ih => exact .mul ih hx hy
  | mulScalarRight _ hx hy _ ih => exact .mul ih hx hy
  | divScalar _ hx hy hne _ ih => exact .div ih hx hy hne
  | mul _ hx hy _ _ ih => exact .mul ih hx hy
  | div _ hx hy hne _ ih => exact .div ih hx hy hne

/-- 非标量乘除门只占全部二元门的一部分。 -/
theorem NonscalarBuild.count_le {F K : Type*} [Field F] [Field K] [Algebra F K]
    {S T : Set K} {m q : ℕ} (h : NonscalarBuild F S m q T) : q ≤ m := by
  induction h <;> omega

/-- 反向逐门转录上游的计算。每遇乘除门，按导线是否为基域常数分类，
从而为原有门序列赋予非标量门计数。初始集、末态和总步数均得保留。 -/
theorem Build.exists_nonscalarBuild {K : Type*} [Field K] (F : Type*) [Field F] [Algebra F K]
    {S T : Set K} {m : ℕ} (h : Build S m T) : ∃ q, NonscalarBuild F S m q T := by
  classical
  induction h with
  | nil => exact ⟨0, .nil⟩
  | add _ hx hy ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨q, .add hq hx hy⟩
  | sub _ hx hy ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨q, .sub hq hx hy⟩
  | @mul m T x y _ hx hy ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hxs : IsScalar F x
    · exact ⟨q, .mulScalarLeft hq hx hy hxs⟩
    by_cases hys : IsScalar F y
    · exact ⟨q, .mulScalarRight hq hx hy hys⟩
    · exact ⟨q + 1, .mul hq hx hy hxs hys⟩
  | @div m T x y _ hx hy hne ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hys : IsScalar F y
    · exact ⟨q, .divScalar hq hx hy hne hys⟩
    · exact ⟨q + 1, .div hq hx hy hne hys⟩

/-- 某一形式电路在基域 `F` 上计算 `n` 阶矩阵乘法，并恰含 `q` 个非标量乘除门。
每个输出都是整个有理函数域中的恒等式。 -/
def ComputesNonscalar (F : Type*) [Field F] (n q : ℕ) : Prop :=
  ∃ (m : ℕ) (T : Set (Rat F n)), NonscalarBuild F (initial F n) m q T ∧
    ∀ p : Pos n, output F p ∈ T

/-- 在指定总步数下，带计数的形式化和原有 `Computes` 判定完全相容。 -/
theorem computes_iff_exists_nonscalarBuild (F : Type*) [Field F] (n m : ℕ) :
    Computes F n m ↔ ∃ (q : ℕ) (T : Set (Rat F n)), NonscalarBuild F (initial F n) m q T ∧
      ∀ p : Pos n, output F p ∈ T := by
  constructor
  · rintro ⟨T, hT, hout⟩
    obtain ⟨q, hq⟩ := Build.exists_nonscalarBuild F hT
    exact ⟨q, T, hq, hout⟩
  · rintro ⟨q, T, hq, hout⟩
    exact ⟨T, hq.toBuild, hout⟩

end OAI.LinearAlgebra.MatrixExponent
