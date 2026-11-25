-- 本文件所属证明环节：在具有命名站点的张量半环中操作共享标签与连线，利用局部限制、运输和谱比较构造替换原布线的张量展开。
import OAI.LinearAlgebra.MatrixExponent.Spectral.Wire

/-!
# 同时满足多项连线需求时的局部表展开

**英文原文**

Local table expansions of simultaneous wire demands
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral
open Classical

-- 读法：`Packet` 的结果类型为 `Prop`。
/-- 每条需求腿都有一个具名比特，每个加数还可引入独立的供给比特。每张局部表只读取与其相接的比特。

英文原文：Each demand leg has a named bit. A summand may introduce independent
supply bits. Each local table reads only the incident bits.
-/
def Packet (K : Type) [Field K] {S E I : Type} {J : I → Type}
    [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]
    (D : E → S × S) (W : (i : I) → J i → S × S) : Prop :=
  ∃ f : (i : I) → S → (E → Bool) → (E → Bool) → (J i → Bool) → K,
    (∀ i v x y u x' y' u',
      (∀ e, (D e).1 = v → x e = x' e) →
      (∀ e, (D e).2 = v → y e = y' e) →
      (∀ e, (W i e).1 = v ∨ (W i e).2 = v → u e = u' e) →
      f i v x y u = f i v x' y' u') ∧
    ∀ x y, (if x = y then (1 : K) else 0) = ∑ i, ∑ u, ∏ v, f i v x y u

end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# 保留连线恒等式的局部因子

单个基本构件可以用存在性证明来选取。复合若干构件时需要实际的因子，因为派生表的标签只能依赖它自身的局部历史。

**英文原文**

Keeping the local factors of a wire identity

An existence proof can be used to choose a single basic gadget.
Composing gadgets needs the actual factors, since the label of a
derived table can only depend on its own local history.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
open Classical

variable {S E I : Type} {J : I → Type} [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]

-- 读法：结构的字段包括 `entry`、`local`、`eval`。
structure Rule (K : Type) [Field K] (D : E → S × S) (W : (i : I) → J i → S × S) where
  entry : (i : I) → S → (E → Bool) → (E → Bool) → (J i → Bool) → K
  local' : ∀ i v x y u x' y' u',
    (∀ e, (D e).1 = v → x e = x' e) →
    (∀ e, (D e).2 = v → y e = y' e) →
    (∀ e, (W i e).1 = v ∨ (W i e).2 = v → u e = u' e) →
    entry i v x y u = entry i v x' y' u'
  eval : ∀ x y, (if x = y then (1 : K) else 0) = ∑ i, ∑ u, ∏ v, entry i v x y u

variable {K : Type} [Field K] {D : E → S × S} {W : (i : I) → J i → S × S}

-- 读法：`rule` 的取值由 `⟨p.choose, p.choose_spec.1, p.choose_spec.2⟩` 给出。
def rule (p : Packet K D W) : Rule K D W := ⟨p.choose, p.choose_spec.1, p.choose_spec.2⟩

-- 读法：要证明的命题是 `Packet K D W`。
theorem Rule.packet (p : Rule K D W) : Packet K D W := ⟨p.entry, p.local', p.eval⟩

-- 读法：`Rule.congr` 的结果类型为 `Rule K D' W'`。
/-- 改变端点的记法，同时保留原来的因子数组。

英文原文：Change endpoint notation without transporting the factor array.
-/
def Rule.congr {W' : (i : I) → J i → S × S} {D' : E → S × S}
    (p : Rule K D W) (hd : D = D') (hw : W = W') : Rule K D' W' :=
  ⟨p.entry, by rw [← hd, ← hw]; exact p.local', p.eval⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end
