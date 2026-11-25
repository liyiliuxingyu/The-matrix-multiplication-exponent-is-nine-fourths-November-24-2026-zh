-- 本文件所属证明环节：编码二进制地址、桶中出现次序和记录秩，检验重复访问同一地址时的记录是否一致。
import OAI.LinearAlgebra.MatrixExponent.Lookup.Counter
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute

/-!
# 小端序二进制地址

**英文原文**

Little-endian binary addresses
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control

-- 读法：`Lookup.value h x` 严格小于 `2 ^ h`。对 `h` 作归纳。
theorem value_lt (h : ℕ) (x : Val (word h)) : Lookup.value h x < 2 ^ h := by
  induction h with
  | zero => simp [Lookup.value]
  | succ h ih =>
    obtain ⟨b, y⟩ := x
    have := ih y
    cases b <;> simp [Lookup.value, pow_succ] <;> omega

-- 读法：`(Lookup.value h)` 是单射。对 `h` 作归纳。
theorem value_injective (h : ℕ) : Function.Injective (Lookup.value h) := by
  induction h with
  | zero => exact fun _ _ _ => rfl
  | succ h ih =>
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    cases i <;> cases j <;> simp [Lookup.value] at he <;> first | omega | exact Prod.ext rfl (ih he)

-- 读法：用字段 `toFun`、`invFun`、`left_inv`、`right_inv` 构造 `Val (word w) ≃ Fin (2 ^ w)`。
def index (w : ℕ) : Val (word w) ≃ Fin (2 ^ w) where
  toFun k := ⟨Lookup.value w k, value_lt w k⟩
  invFun k := Lookup.bits w k
  left_inv k := value_injective w (Lookup.value_bits (value_lt w k))
  right_inv k := Fin.ext (Lookup.value_bits k.isLt)

-- 读法：`decode` 的取值由 `(bits (word w)).symm.trans (index w)` 给出。
def decode (w : ℕ) : (slots (word w) → Bool) ≃ Fin (2 ^ w) :=
  (bits (word w)).symm.trans (index w)

-- 读法：`read` 的取值由 `x (.inl (decode w (fun j => x (.inr (i, j)))))` 给出。
def read (w : ℕ) (x : Fin (2 ^ w) ⊕ (Fin (2 ^ w) × slots (word w)) → Bool) (i : Fin (2 ^ w)) : Bool :=
  x (.inl (decode w (fun j => x (.inr (i, j)))))

end OAI.LinearAlgebra.MatrixExponent.Control
