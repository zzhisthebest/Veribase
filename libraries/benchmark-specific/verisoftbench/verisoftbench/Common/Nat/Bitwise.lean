import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Lemmas about `Nat.bitwise` distributing over numbers split into chunks of size `2^n`.
-/

namespace Nat

/--
For any boolean function `f` with `f false false = false`, `Nat.bitwise f` distributes over
numbers split into chunks of size `2^n`. If `b, d < 2^n`, then:
`Nat.bitwise f (2^n * a + b) (2^n * c + d) = 2^n * Nat.bitwise f a c + Nat.bitwise f b d`
-/
lemma bitwise_two_pow_mul_add (f : Bool → Bool → Bool) (hfff : f false false = false) (n : ℕ)
    {a b c d : ℕ} (hb : b < 2^n) (hd : d < 2^n) :
    Nat.bitwise f (2^n * a + b) (2^n * c + d) =
    2^n * Nat.bitwise f a c + Nat.bitwise f b d := by
  have hbd_lt : Nat.bitwise f b d < 2^n := Nat.bitwise_lt_two_pow hb hd
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_bitwise hfff]
  rw [Nat.testBit_two_pow_mul_add a hb i, Nat.testBit_two_pow_mul_add c hd i]
  rw [Nat.testBit_two_pow_mul_add (Nat.bitwise f a c) hbd_lt i]
  rw [Nat.testBit_bitwise hfff b d i, Nat.testBit_bitwise hfff a c (i - n)]
  split_ifs
  · rfl
  · rfl

/--
Convenience specialization of `bitwise_two_pow_mul_add` for byte-sized chunks `2^8`.
-/
lemma bitwise_two_pow_8_mul_add (f : Bool → Bool → Bool) (hfff : f false false = false)
    {a b c d : ℕ} (hb : b < 2^8) (hd : d < 2^8) :
    Nat.bitwise f (2^8 * a + b) (2^8 * c + d) =
    2^8 * Nat.bitwise f a c + Nat.bitwise f b d :=
  bitwise_two_pow_mul_add f hfff 8 hb hd

/--
If two naturals are each less than `2^n`, their XOR is also less than `2^n`,
and casting the XOR to `ZMod p` preserves its natural number value when `2^n ≤ p`.
-/
lemma xor_val_cast_of_two_pow {p a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hp : 2 ^ n ≤ p) :
    ZMod.val ((a ^^^ b : ℕ) : ZMod p) = a ^^^ b := by
  have hxor : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb
  have hlt : a ^^^ b < p := lt_of_lt_of_le hxor hp
  rw [ZMod.val_cast_of_lt hlt]

/--
For byte values (a, b < 256), the `ZMod.val` of the XOR cast to `ZMod p` equals the XOR itself
when `256 ≤ p`.
-/
lemma xor_byte_val_cast {p a b : ℕ} (ha : a < 256) (hb : b < 256) (hp : 256 ≤ p) :
    ZMod.val ((a ^^^ b : ℕ) : ZMod p) = a ^^^ b :=
  xor_val_cast_of_two_pow (n := 8) ha hb hp

end Nat
