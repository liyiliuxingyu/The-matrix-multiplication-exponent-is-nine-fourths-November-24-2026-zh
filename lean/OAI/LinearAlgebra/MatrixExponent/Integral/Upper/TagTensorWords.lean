-- 本文件所属证明环节：在无除法的交换环模型中处理形式多项式、插值及上界构造；把域上的矩形指数结果提升到非平凡交换环。
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Separation
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Powers
import OAI.LinearAlgebra.TensorSpectrum.TagWords

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

/-!
# 系数张量构成的词与按匹配标签作出的限制

共享第一条腿的张量的幂对每个字各有一个分支。下文的重新分组保留全部系数，包括不同字之间的零系数。通过单射选取若干个字是一个实际局部限制。再对每个字所表示的实际张量积应用乘性。

**英文原文**

Coefficient tensor words and matched-label restrictions

Tensor powers of a shared-first-leg tensor have one branch for each word.
The regrouping below preserves all coefficients, including the zero
coefficients between different words. Selecting words by an injection is an
actual local restriction. Multiplicativity is then applied to the actual
tensor product represented by each word.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagTensorWords

variable {X Y Z : Type*}

-- 读法：当 `y.1 = z.1` 成立时取 `A y.1 x y.2 z.2`，否则取 `0`。
/-- 以任意有限类型作为标签且共享第一条腿的张量。

英文原文：A shared-first-leg tensor with an arbitrary finite label type.
-/
def sharedLabels {ι : Type*} [DecidableEq ι] (A : ι → Tensor O X Y Z) :
    Tensor O X (ι × Y) (ι × Z) :=
  fun x y z => if y.1 = z.1 then A y.1 x y.2 z.2 else 0

-- 读法：输入 `x y z` 时返回 `∏ j, B j (x j) (y j) (z j)`。
/-- 每个位置对应一个实际张量因子，所有位置彼此区分，并保留每个系数。

英文原文：One actual tensor factor per position, without identifying positions or
discarding any coefficients.
-/
def tensorWord {N : ℕ} (B : Fin N → Tensor O X Y Z) :
    Tensor O (Fin N → X) (Fin N → Y) (Fin N → Z) :=
  fun x y z => ∏ j, B j (x j) (y j) (z j)

-- 读法：`wordBranch` 的取值由 `tensorWord (fun j => A (w j))` 给出。
/-- 一个字指定每个张量位置采用哪一个分支。

英文原文：A word specifies which branch occupies each tensor position.
-/
def wordBranch {s N : ℕ} (A : Fin s → Tensor O X Y Z)
    (w : TagWords.Word s N) :
    Tensor O (Fin N → X) (Fin N → Y) (Fin N → Z) :=
  tensorWord (fun j => A (w j))

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`rfl` 构造 `((Fin N → ι) × (Fin N → U)) ≃ (Fin N → ι × U)`。
/-- 将一个标签字与一个坐标字重新配成由坐标对组成的字。

英文原文：Put a word of labels and a word of coordinates back into coordinate pairs.
-/
def joinCoordinates (N : ℕ) (ι U : Type*) :
    ((Fin N → ι) × (Fin N → U)) ≃ (Fin N → ι × U) where
  toFun p j := (p.1 j, p.2 j)
  invFun f := (fun j => (f j).1, fun j => (f j).2)
  left_inv p := by
    rcases p with ⟨a, b⟩
    rfl
  right_inv f := by
    funext j
    exact Prod.eta (f j)

-- 读法：用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 将整个张量幂的第二与第三坐标分别重新分组，所得正是由各个字分支组成的共享张量。

英文原文：Regrouping the second and third coordinates of the full tensor power
produces exactly the shared tensor of word branches.
-/
theorem power_shared_pullback {s N : ℕ} (A : Fin s → Tensor O X Y Z) :
    Tensor.pullback (Equiv.refl (Fin N → X))
      (joinCoordinates N (Fin s) Y) (joinCoordinates N (Fin s) Z)
      (Tensor.power (Separation.shared A) N) = sharedLabels (wordBranch A) := by
  classical
  funext x y z
  by_cases h : y.1 = z.1
  · simp only [Tensor.pullback, Equiv.refl_apply, Tensor.power,
      sharedLabels, ite_eq_left h, wordBranch, tensorWord]
    apply Finset.prod_congr rfl
    intro j hj
    simp [Separation.shared, joinCoordinates, congrFun h j]
  · have hex : ∃ j, y.1 j ≠ z.1 j := by
      by_contra hnone
      apply h
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    -- 推导：从 `hex` 中取出 `j, hj`。
    obtain ⟨j, hj⟩ := hex
    simp only [Tensor.pullback, Equiv.refl_apply, Tensor.power,
      sharedLabels, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Separation.shared, joinCoordinates, hj]

section Restriction

variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：要证明的命题是 `CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N) (sharedLabels (wordBranch (N := N) A))`。这里调用 `CoefficientTensor.Restricts.pullback`。
/-- 用三个显式坐标拉回实现这一重新分组。

英文原文：The regrouping is implemented by three actual coordinate pullbacks.
-/
theorem restricts_power_shared_words {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (sharedLabels (wordBranch (N := N) A)) := by
  rw [← power_shared_pullback]
  exact CoefficientTensor.Restricts.pullback _ _ _ _

-- 读法：`TensorClass.ofTensor (sharedLabels (wordBranch (N := N) A))` 等于 `TensorClass.ofTensor (Separation.shared A) ^ N`。
/-- 重新分组是可逆的，因此两个张量也给出同一个张量类。

英文原文：The regrouping is invertible, so it also identifies the tensor classes.
-/
theorem ofTensor_shared_words {s N : ℕ} (A : Fin s → Tensor O X Y Z) :
    TensorClass.ofTensor (sharedLabels (wordBranch (N := N) A)) =
      TensorClass.ofTensor (Separation.shared A) ^ N := by
  rw [← power_shared_pullback, TensorClass.ofTensor_pullback_equiv,
    TensorClass.ofTensor_power]

omit [Fintype X] [Fintype Y] [Fintype Z] in
-- 读法：要证明的命题是 `Tensor.pullback id (fun y : κ × Y => (e y.1, y.2)) (fun z : κ × Z => (e z.1, z.2)) (sharedLabels A) = sharedLabels (fun i => A (e i))`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 分支标签上的单射保持标签之间的相等性检验结果。

英文原文：An injection on branch labels preserves the equality test between labels.
-/
theorem shared_injective_pullback {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (A : ι → Tensor O X Y Z) (e : κ → ι) (he : Function.Injective e) :
    Tensor.pullback id (fun y : κ × Y => (e y.1, y.2))
      (fun z : κ × Z => (e z.1, z.2)) (sharedLabels A) =
      sharedLabels (fun i => A (e i)) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, sharedLabels, h]
  · have h' : e y.1 ≠ e z.1 := fun h' => h (he h')
    simp [Tensor.pullback, sharedLabels, h, h']

-- 读法：要证明的命题是 `CoefficientTensor.Restricts (sharedLabels A) (sharedLabels (fun i => A (e i)))`。这里调用 `CoefficientTensor.Restricts.pullback`。
/-- 选择任意一组相匹配的标签都给出一个实际的局部限制。

英文原文：Selecting any set of matched labels is an actual local restriction.
-/
theorem restricts_shared_injective {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (A : ι → Tensor O X Y Z) (e : κ → ι) (he : Function.Injective e) :
    CoefficientTensor.Restricts (sharedLabels A) (sharedLabels (fun i => A (e i))) := by
  rw [← shared_injective_pullback A e he]
  exact CoefficientTensor.Restricts.pullback _ _ _ _

-- 读法：要证明的命题是 `CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N) (Separation.shared (fun i => wordBranch A (e i)))`。用函数外延性比较等号两侧在 `x y z` 处的取值。
/-- 目标正是计入成本的分离构造所需的、以 `Fin M` 为标签类型的共享张量。标签映射可以枚举任意选定的字集合。

英文原文：This target uses the precise `Fin M` shared tensor accepted by the charged
separation construction. The label map may enumerate any selected word set.
-/
theorem restricts_power_shared_selected {s N M : ℕ}
    (A : Fin s → Tensor O X Y Z) (e : Fin M → TagWords.Word s N)
    (he : Function.Injective e) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (Separation.shared (fun i => wordBranch A (e i))) := by
  have h := (restricts_power_shared_words A).trans
    (restricts_shared_injective (wordBranch A) e he)
  have heq : sharedLabels (fun i => wordBranch A (e i)) =
      Separation.shared (fun i => wordBranch A (e i)) := by
    funext x y z
    by_cases hlabel : y.1 = z.1 <;>
      simp [sharedLabels, Separation.shared, hlabel]
  rw [← heq]
  exact h

-- 读法：这里调用 `restricts_power_shared_words`。
/-- 特别地，可以同时保留同一计数纤维中的所有字。

英文原文：In particular, the words in a count fiber can be retained together.
-/
theorem restricts_power_shared_fiber {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) (c : TagWords.CountVector s N) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (sharedLabels (fun w : {w // w ∈ TagWords.fiber c} => wordBranch A w.val)) := by
  exact (restricts_power_shared_words A).trans
    (restricts_shared_injective (wordBranch A) Subtype.val Subtype.val_injective)

-- 读法：要证明的命题是 `CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N) (Separation.shared (fun i => wordBranch A (e i).val))`。这里调用 `restricts_power_shared_selected`。
/-- 对一个计数纤维作任意有限枚举，都能给出计入成本的分离构造所需的精确输入，其重数等于选取的字数。

英文原文：Every finite enumeration of a count fiber provides the exact input needed
by charged separation, with multiplicity equal to the number of selected words.
-/
theorem restricts_power_shared_fiber_enumeration {s N M : ℕ}
    (A : Fin s → Tensor O X Y Z) (c : TagWords.CountVector s N)
    (e : Fin M ≃ {w // w ∈ TagWords.fiber c}) :
    CoefficientTensor.Restricts (Tensor.power (Separation.shared A) N)
      (Separation.shared (fun i => wordBranch A (e i).val)) := by
  exact restricts_power_shared_selected A (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective)

end Restriction

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `(Fin (N + 1) → U) ≃ U × (Fin N → U)`。
/-- 分离出第一个张量位置，保留其余各位置上的所有坐标。

英文原文：Split off the first tensor position, leaving every remaining coordinate.
-/
def headTailCoordinates (N : ℕ) (U : Type*) :
    (Fin (N + 1) → U) ≃ U × (Fin N → U) where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv p := by
    rcases p with ⟨u, f⟩
    rfl

section Character

variable [Fintype X] [Fintype Y] [Fintype Z]

-- 读法：`TensorClass.ofTensor (tensorWord B)` 等于 `∏ j, TensorClass.ofTensor (B j)`。对 `N` 作归纳。
/-- 系数张量字所属的类等于各因子所属类的乘积。证明使用显式可逆的坐标重新分组。

英文原文：The class of a coefficient tensor word is the product of the factor
classes. This is proved by actual invertible coordinate regroupings.
-/
theorem ofTensor_tensorWord {N : ℕ} (B : Fin N → Tensor O X Y Z) :
    TensorClass.ofTensor (tensorWord B) = ∏ j, TensorClass.ofTensor (B j) := by
  induction N with
  | zero =>
    rw [show (∏ j : Fin 0, TensorClass.ofTensor (B j)) = 1 by simp]
    change TensorClass.ofTensor (tensorWord B) =
      TensorClass.ofTensor TensorClass.unitTensor
    have heq : Tensor.pullback (Equiv.ofUnique (Fin 0 → X) PUnit)
        (Equiv.ofUnique (Fin 0 → Y) PUnit) (Equiv.ofUnique (Fin 0 → Z) PUnit)
        TensorClass.unitTensor = tensorWord B := by
      funext x y z
      simp [Tensor.pullback, tensorWord, TensorClass.unitTensor]
    rw [← heq]
    exact TensorClass.ofTensor_pullback_equiv _ _ _ _
  | succ N ih =>
    rw [Fin.prod_univ_succ, ← ih (fun j => B j.succ), TensorClass.ofTensor_mul]
    have heq : Tensor.pullback (headTailCoordinates N X)
        (headTailCoordinates N Y) (headTailCoordinates N Z)
        (Tensor.product (B 0) (tensorWord (fun j => B j.succ))) = tensorWord B := by
      funext x y z
      simp [Tensor.pullback, Tensor.product, tensorWord, headTailCoordinates,
        Fin.prod_univ_succ]
    rw [← heq]
    exact TensorClass.ofTensor_pullback_equiv _ _ _ _

-- 读法：`f (TensorClass.ofTensor (wordBranch A w))` 等于 `TagWords.wordWeight (fun i => f (TensorClass.ofTensor (A i))) w`。这里调用 `map_prod`。
/-- 特征标在字分支上的值等于各被选分支的特征标值的有限乘积，无须另加乘性假设。

英文原文：A character evaluates a word branch as the finite product of the values
of the chosen branches; there is no separate multiplicativity assumption.
-/
theorem map_wordBranch (f : TensorClass.Character) {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) (w : TagWords.Word s N) :
    f (TensorClass.ofTensor (wordBranch A w)) =
      TagWords.wordWeight (fun i => f (TensorClass.ofTensor (A i))) w := by
  unfold wordBranch TagWords.wordWeight
  rw [ofTensor_tensorWord]
  exact map_prod f.toHom _ _

-- 读法：`f (TensorClass.ofTensor (wordBranch A w))` 等于 `TagWords.countWeight (fun i => f (TensorClass.ofTensor (A i))) c`。这里调用 `TagWords.wordWeight_eq_of_mem_fiber`。
/-- 在一个固定的计数纤维中，每个字的特征标值相同。

英文原文：Every word in a fixed count fiber has the same character value.
-/
theorem map_wordBranch_of_mem_fiber (f : TensorClass.Character) {s N : ℕ}
    (A : Fin s → Tensor O X Y Z) {c : TagWords.CountVector s N}
    {w : TagWords.Word s N} (hw : w ∈ TagWords.fiber c) :
    f (TensorClass.ofTensor (wordBranch A w)) =
      TagWords.countWeight (fun i => f (TensorClass.ofTensor (A i))) c := by
  rw [map_wordBranch]
  exact TagWords.wordWeight_eq_of_mem_fiber _ hw

end Character

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper.TagTensorWords
