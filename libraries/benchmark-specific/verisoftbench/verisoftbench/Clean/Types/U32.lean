import Clean.Types.U32
import verisoftbench.Common.Nat.Basic
import verisoftbench.Common.Nat.Bitwise

/-!
Lemmas about `U32` from `Clean.Types.U32`.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]

namespace U32

omit [Fact (Nat.Prime p)] p_large_enough in
/--
If a U32 value is normalized, each of its byte components is less than `2^8`.
-/
lemma byte_bound_of_normalized {x : U32 (F p)} (x_norm : x.Normalized) :
    x.x0.val < 2^8 ∧ x.x1.val < 2^8 ∧ x.x2.val < 2^8 ∧ x.x3.val < 2^8 := by
  have h256 : (256 : ℕ) = 2^8 := by norm_num
  rcases x_norm with ⟨hx0, hx1, hx2, hx3⟩
  exact ⟨by simpa [h256] using hx0, by simpa [h256] using hx1,
         by simpa [h256] using hx2, by simpa [h256] using hx3⟩

omit [Fact (Nat.Prime p)] p_large_enough in
/--
Bitwise operation on two normalized U32 values decomposes into byte-level bitwise operations.
For any boolean function `f` (such as `|||`, `&&&`, `^^^`) with `f false false = false`,
`Nat.bitwise f` applied to the values of two normalized U32 values equals the byte-level
decomposition with Horner expansion by 256.
-/
lemma bitwise_componentwise (f : Bool → Bool → Bool)
    {x y : U32 (F p)} (x_norm : x.Normalized) (y_norm : y.Normalized) :
    f false false = false →
    Nat.bitwise f x.value y.value =
      Nat.bitwise f x.x0.val y.x0.val + 256 *
        (Nat.bitwise f x.x1.val y.x1.val + 256 *
          (Nat.bitwise f x.x2.val y.x2.val + 256 * Nat.bitwise f x.x3.val y.x3.val)) := by
  intro hfff
  rcases byte_bound_of_normalized x_norm with ⟨hx0_lt, hx1_lt, hx2_lt, hx3_lt⟩
  rcases byte_bound_of_normalized y_norm with ⟨hy0_lt, hy1_lt, hy2_lt, hy3_lt⟩
  have hxval : x.value = 2^8 * (x.x1.val + 2^8 * (x.x2.val + 2^8 * x.x3.val)) + x.x0.val := by
    rw [U32.value_horner x]
    ring
  have hyval : y.value = 2^8 * (y.x1.val + 2^8 * (y.x2.val + 2^8 * y.x3.val)) + y.x0.val := by
    rw [U32.value_horner y]
    ring
  rw [hxval, hyval]
  rw [Nat.bitwise_two_pow_mul_add f hfff 8 hx0_lt hy0_lt]
  have hX1 : x.x1.val + 2^8 * (x.x2.val + 2^8 * x.x3.val) = 2^8 * (x.x2.val + 2^8 * x.x3.val) + x.x1.val := by ring
  have hY1 : y.x1.val + 2^8 * (y.x2.val + 2^8 * y.x3.val) = 2^8 * (y.x2.val + 2^8 * y.x3.val) + y.x1.val := by ring
  rw [hX1, hY1]
  rw [Nat.bitwise_two_pow_mul_add f hfff 8 hx1_lt hy1_lt]
  have hX2 : x.x2.val + 2^8 * x.x3.val = 2^8 * x.x3.val + x.x2.val := by ring
  have hY2 : y.x2.val + 2^8 * y.x3.val = 2^8 * y.x3.val + y.x2.val := by ring
  rw [hX2, hY2]
  rw [Nat.bitwise_two_pow_mul_add f hfff 8 hx2_lt hy2_lt]
  have h256 : (256 : ℕ) = 2^8 := by norm_num
  calc
    2^8 * (2^8 * (2^8 * Nat.bitwise f x.x3.val y.x3.val + Nat.bitwise f x.x2.val y.x2.val) +
      Nat.bitwise f x.x1.val y.x1.val) + Nat.bitwise f x.x0.val y.x0.val
        = Nat.bitwise f x.x0.val y.x0.val + 2^8 * (Nat.bitwise f x.x1.val y.x1.val +
          2^8 * (Nat.bitwise f x.x2.val y.x2.val + 2^8 * Nat.bitwise f x.x3.val y.x3.val)) := by
      rw [nested_two_pow_mul_add 8]
    _ = Nat.bitwise f x.x0.val y.x0.val + 256 * (Nat.bitwise f x.x1.val y.x1.val +
        256 * (Nat.bitwise f x.x2.val y.x2.val + 256 * Nat.bitwise f x.x3.val y.x3.val)) := by
      simp [h256]

omit [Fact (Nat.Prime p)] p_large_enough in
/--
  Uniqueness of base-256 representation: if four bounded naturals (each < 256)
  have equal weighted sums, then they are componentwise equal.
-/
lemma base256_inj (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (h : a0 + a1 * 256 + a2 * 256^2 + a3 * 256^3 =
         b0 + b1 * 256 + b2 * 256^2 + b3 * 256^3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have h0 : a0 = b0 := by omega
  have h1 : a1 = b1 := by
    rw [h0] at h
    omega
  have h2 : a2 = b2 := by
    rw [h0, h1] at h
    omega
  have h3 : a3 = b3 := by
    rw [h0, h1, h2] at h
    omega
  exact ⟨h0, h1, h2, h3⟩

omit p_large_enough in
/--
  Extensionality principle for `U32 (F p)` from natural-number component equalities.
  If the `ZMod.val` of each corresponding limb is equal, then the U32 values are equal.
-/
lemma ext_of_val_eq (x y : U32 (F p))
    (h0 : x.x0.val = y.x0.val) (h1 : x.x1.val = y.x1.val)
    (h2 : x.x2.val = y.x2.val) (h3 : x.x3.val = y.x3.val) : x = y := by
  have h0' : x.x0 = y.x0 := ZMod.val_injective p h0
  have h1' : x.x1 = y.x1 := ZMod.val_injective p h1
  have h2' : x.x2 = y.x2 := ZMod.val_injective p h2
  have h3' : x.x3 = y.x3 := ZMod.val_injective p h3
  exact U32.ext h0' h1' h2' h3'

omit p_large_enough in
/--
  The value function is injective on normalized U32 values.
  If two normalized U32 values have the same natural-number value, they are equal.
-/
lemma value_injective_of_normalized (x y : U32 (F p))
    (hx : x.Normalized) (hy : y.Normalized) :
    x.value = y.value → x = y := by
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  rcases hy with ⟨hy0, hy1, hy2, hy3⟩
  intro hval
  unfold U32.value at hval
  have ⟨h0, h1, h2, h3⟩ :=
    base256_inj (x.x0.val) (x.x1.val) (x.x2.val) (x.x3.val)
      (y.x0.val) (y.x1.val) (y.x2.val) (y.x3.val)
      hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3 hval
  exact ext_of_val_eq x y h0 h1 h2 h3

end U32
