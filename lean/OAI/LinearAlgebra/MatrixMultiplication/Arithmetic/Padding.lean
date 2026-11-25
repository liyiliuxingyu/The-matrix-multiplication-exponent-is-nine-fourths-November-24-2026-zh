-- 本文件所属证明环节：用零填充把小矩阵嵌入大矩阵，证明先填充再相乘给出原乘积的零填充。由此把大尺寸程序限制到小尺寸，并证明矩形可容许指数对内维参数的单调性。
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition

namespace OAI

/-!
域上的无除法算术程序及其运算次数。

**英文原文**

Division-free arithmetic programs over a field and their operation counts.
-/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

-- 读法：输入 `i j` 时返回 `if hi : i.val < a then if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0`。
def zeroPadMatrix {a b : ℕ} (A B : ℕ) (M : Matrix (Fin a) (Fin b) F) :
    Matrix (Fin A) (Fin B) F :=
  fun i j => if hi : i.val < a then
    if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

-- 读法：`zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j)` 等于 `M i j`。
@[simp] theorem zeroPadMatrix_castLE {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (M : Matrix (Fin a) (Fin b) F) (i : Fin a) (j : Fin b) :
    zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) = M i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

-- 读法：`(∑ j : Fin m, f j)` 等于 `∑ j : Fin n, f (Fin.castLE h j)`。这里调用 `Fin.ext`。
theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → F)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

-- 读法：`(zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k)` 等于 `(M * N) i k`。
theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin B,
        zeroPadMatrix A B M (Fin.castLE ha i) j *
          zeroPadMatrix B C N j (Fin.castLE hc k)) =
        ∑ j : Fin b,
          zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
            zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k) := by
      apply sum_fin_castLE_of_zero hb
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin b, M i j * N j k := by simp

-- 读法：逐一匹配以下输入模式：`.inl (i, j)`、`.inr (j, k)`。
def padSource {a b c A B C : ℕ} : MatrixInput A B C → MatrixInput a b c ⊕ F
  | .inl (i, j) => if hi : i.val < a then
      if hj : j.val < b then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (j, k) => if hj : j.val < b then
      if hk : k.val < c then .inl (.inr (⟨j.val, hj⟩, ⟨k.val, hk⟩)) else .inr 0
    else .inr 0

-- 读法：`(fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x))` 等于 `matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N)`。用函数外延性比较等号两侧在 `x` 处的取值。
theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk]

namespace MatrixAlgorithm

-- 读法：用字段 `registers`、`program`、`output` 构造 `MatrixAlgorithm F a b c`。
def pad {a b c A B C : ℕ} (ha : a ≤ A) (_hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : MatrixAlgorithm F a b c where
  registers := P.registers
  program := P.program.mapSource (padSource (a := a) (b := b) (c := c))
  output := fun i k => P.output (Fin.castLE ha i) (Fin.castLE hc k)

-- 读法：要证明的命题是 `(pad ha hb hc P).Correct`。用函数外延性比较等号两侧在 `i k` 处的取值。
theorem pad_correct {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : P.Correct) : (pad ha hb hc P).Correct := by
  intro M N
  funext i k
  change (P.program.mapSource (padSource (a := a) (b := b) (c := c))).eval
    (matrixInputs M N) (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = (M * N) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N)) (Fin.castLE ha i)) (Fin.castLE hc k)
  exact hentry.trans (zeroPadMatrix_mul ha hb hc M N i k)

-- 读法：`(pad ha hb hc P).cost` 等于 `P.cost`。使用 `Program.cost_mapSource` 给出的结论。
@[simp] theorem pad_cost_eq {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : (pad ha hb hc P).cost = P.cost :=
  Program.cost_mapSource (padSource (a := a) (b := b) (c := c)) P.program

-- 读法：存在 `Q : MatrixAlgorithm F a b c`，`Q.Correct` 与 `Q.cost ≤ P.cost` 同时成立。
theorem exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad ha hb hc P, pad_correct ha hb hc hP, (pad_cost_eq ha hb hc P).le⟩

end MatrixAlgorithm

-- 读法：要证明的命题是 `RectangularAdmissibleExponent F k τ`。
theorem RectangularAdmissibleExponent.mono_aspect {k l τ : ℝ}
    (h : RectangularAdmissibleExponent F l τ) (hkl : k ≤ l) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  obtain ⟨Q, hQ, hcostQ⟩ := MatrixAlgorithm.exists_restrict (le_refl n)
    (innerSize_mono hn hkl) (le_refl n) P hP
  exact ⟨Q, hQ, (Nat.cast_le.mpr hcostQ).trans hcost⟩

end MatrixMultiplication.Arithmetic

end

end OAI
