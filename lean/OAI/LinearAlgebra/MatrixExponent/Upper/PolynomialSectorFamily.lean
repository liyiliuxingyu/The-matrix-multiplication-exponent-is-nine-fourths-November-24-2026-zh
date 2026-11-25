-- 本文件所属证明环节：用多项式退化、带标签的张量分支、傅里叶或插值分离和张量幂构造矩阵乘法上界所需的显式张量限制。
import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialSectors
import OAI.LinearAlgebra.MatrixExponent.Upper.PolynomialWeightFamily

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum

/-!
# 三扇区退化的多项式见证

每个系数的次数都至多为一。其常数项给出共享第一输入的全部分区所组装的张量。对每个非零参数求值都得到原多项式张量的一个实际限制。这些显式性质足以进行插值，无须假设任意张量特征标保持拓扑极限。

**英文原文**

The polynomial witness for the three-sector degeneration

Every coefficient has degree at most one.  Its constant coefficient is the
entire shared-first-input sector assembly.  At each nonzero parameter the
evaluated tensor is an actual restriction of the original polynomial tensor.
These explicit facts support interpolation without assuming that an arbitrary
tensor character preserves topological limits.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper

-- 读法：`triplingPolynomialFamily` 的结果类型为 `Tensor (Polynomial Coeff) (Fin a) (TriplingY a h) (TriplingZ a h)`。
/-- 用后两条腿上各分区的完整基表示同一个对角退化族；第一输入保持原样。

英文原文：The same family as the diagonal degeneration, expressed in the complete
sector bases on the last two legs.  The first input is unchanged.
-/
def triplingPolynomialFamily (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Tensor (Polynomial Coeff) (Fin a) (TriplingY a h) (TriplingZ a h) :=
  Tensor.pullback id (triplingYEquiv a h ha hh) (triplingZEquiv a h ha hh)
    (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val))

-- 读法：`0` 不超过 `(0 : ℤ) + triplingYWeight a h y.val + triplingZWeight a h z.val`。这里调用 `tripling_weight_nonneg`。
private theorem tripling_source_weights_nonneg (a h : ℕ) (ha : 1 ≤ a)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1))
    (hc : polynomialTensor a (triplingWidth a h) x y z ≠ 0) :
    0 ≤ (0 : ℤ) + triplingYWeight a h y.val + triplingZWeight a h z.val := by
  have hs : x.val + y.val = z.val := by
    by_contra hn
    exact hc (by simp [polynomialTensor, hn])
  simpa using tripling_weight_nonneg ha x.isLt hs

-- 读法：`((0 : ℤ) + triplingYWeight a h y + triplingZWeight a h z).toNat` 不超过 `1`。
private theorem tripling_weights_toNat_le_one (a h y z : ℕ) :
    ((0 : ℤ) + triplingYWeight a h y + triplingZWeight a h z).toNat ≤ 1 := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> decide

-- 读法：`(triplingPolynomialFamily a h ha hh x y z).coeff 0` 等于 `triplingSectorTensor a h x y z`。
/-- 常数项在同一组共享的第一输入基下保留全部三个分支，也保留取值为零的跨分区系数。

英文原文：The constant coefficient retains all three branches, including their
vanishing cross-sector coefficients, in one shared first-input basis.
-/
theorem triplingPolynomialFamily_coeff_zero (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).coeff 0 = triplingSectorTensor a h x y z := by
  change (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val) x
      (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)).coeff 0 = _
  rw [weightedPolynomial_coeff_zero _ _ _ _ (tripling_source_weights_nonneg a h ha)]
  exact congrFun (congrFun (congrFun (triplingGraded_sector_assembly a h ha hh) x) y) z

-- 读法：`(triplingPolynomialFamily a h ha hh x y z).degree` 不超过 `(1 : ℕ)`。这里调用 `weightedPolynomial_degree_le`。
/-- 这个显式族的每个坐标的次数都至多为一，因此近似次数固定且有明确的界。

英文原文：There is no growing or unspecified approximation degree: every coordinate
of this explicit family has degree at most one.
-/
theorem triplingPolynomialFamily_degree_le (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).degree ≤ (1 : ℕ) := by
  exact weightedPolynomial_degree_le (polynomialTensor a (triplingWidth a h))
    (fun _ => 0) (fun y => triplingYWeight a h y.val)
    (fun z => triplingZWeight a h z.val) (D := 1)
    (fun _ y z _ => tripling_weights_toNat_le_one a h y.val z.val)
    x (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)

-- 读法：`(fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t)` 属于 `LocalTensor.orbit (polynomialTensor a (triplingWidth a h))`。
/-- 在每个非零参数处求值，都得到原源张量的一个精确限制。先作用对角映射，再用一对固定的局部映射重编分区索引，共享的第一输入上取恒等映射。

英文原文：Every nonzero evaluation is an exact restriction of the original source
tensor. The sector reindexing is one fixed pair of local maps, with identity
on the common first input, after the diagonal maps.
-/
theorem triplingPolynomialFamily_eval_mem_restrictionOrbit
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) {t : Coeff} (ht : t ≠ 0) :
    (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) ∈
      LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) := by
  classical
  let E : Tensor Coeff (Fin a) (Fin (triplingWidth a h))
      (Fin (a + triplingWidth a h - 1)) :=
    fun x y z => (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val) x y z).eval t
  -- 推导：记下中间结论 `hE`：`E ∈ LocalTensor.orbit (polynomialTensor a (triplingWidth a h))`。
  have hE : E ∈ LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) :=
    weightedPolynomial_eval_mem_restrictionOrbit _ _ _ _
      (tripling_source_weights_nonneg a h ha) ht
  have hr := LocalTensor.restrict_mem hE
    (fun (x' x : Fin a) => if x = x' then (1 : Coeff) else 0)
    (fun (y' : TriplingY a h) (y : Fin (triplingWidth a h)) =>
      if y = triplingYEquiv a h ha hh y' then (1 : Coeff) else 0)
    (fun (z' : TriplingZ a h) (z : Fin (a + triplingWidth a h - 1)) =>
      if z = triplingZEquiv a h ha hh z' then (1 : Coeff) else 0)
  have hp : Tensor.pullback (id : Fin a → Fin a)
      (triplingYEquiv a h ha hh) (triplingZEquiv a h ha hh) E =
      (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) := rfl
  rw [Tensor.pullback_eq_restrict] at hp
  simp only [id_eq] at hp
  rw [hp] at hr
  exact hr

end OAI.LinearAlgebra.MatrixExponent.Upper
