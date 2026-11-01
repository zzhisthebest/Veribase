import Mathlib
import general.Nat.Search
import general.Nat.Range

namespace Nat


/-! ### Hamming distance (bit-level) -/

/-- Hamming distance between two natural numbers: counts the number of differing bits.
Computed recursively by comparing the least significant bit of each number and
dividing by 2 to shift to the next bit. Equivalent to `popcount (a ^^^ b)` but
defined via structural recursion for use in termination proofs. -/
def hammingDist : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, Nat.succ b =>
      hammingDist 0 ((Nat.succ b) / 2) + (if 0 % 2 = (Nat.succ b) % 2 then 0 else 1)
  | Nat.succ a, 0 =>
      hammingDist ((Nat.succ a) / 2) 0 + (if (Nat.succ a) % 2 = 0 % 2 then 0 else 1)
  | Nat.succ a, Nat.succ b =>
      hammingDist ((Nat.succ a) / 2) ((Nat.succ b) / 2) +
        (if (Nat.succ a) % 2 = (Nat.succ b) % 2 then 0 else 1)
termination_by a b => a + b
decreasing_by
  · simpa using succ_div_two_lt b
  · simpa using succ_div_two_lt a
  · simpa using succ_div_two_add_lt a b


/-- Number of `1` bits in the binary representation of a natural number. -/
def popcount (n : Nat) : Nat :=
  (Nat.digits 2 n).count 1

/-- `Nat.popcount` of zero is zero. -/
lemma popcount_zero : popcount 0 = 0 := by
  simp [popcount]

/-- Count the number of set bits (popcount) in the lowest `bits` bits of a natural number.
Uses Finset to iterate over bit positions `[0, bits)` and count positions where `n.testBit i` is true.
Contrast with `Nat.popcount` which counts all bits using `Nat.digits 2 n`. -/
def popcountInRange (n : Nat) (bits : Nat) : Nat :=
  Finset.card (Finset.filter (fun i : Nat => n.testBit i) (Finset.range bits))

/-- `popcountInRange` of zero for any `bits` is zero. -/
lemma popcountInRange_zero (bits : Nat) : popcountInRange 0 bits = 0 := by
  simp [popcountInRange]

/-- `popcountInRange` with zero bits is always zero. -/
lemma popcountInRange_zero_bits (n : Nat) : popcountInRange n 0 = 0 := by
  simp [popcountInRange]

/-- `allOnesMask k` returns the natural number whose `k` least significant bits are all `1`.
    That is, `allOnesMask k = 2^k - 1`. -/
def allOnesMask (k : Nat) : Nat :=
  shiftLeft 1 k - 1

/-- Complement a natural number within its own bit width.
    Computes `allOnesMask (Nat.size n) - n`, which flips all bits of `n`
    up to its most significant set bit.
    For `n = 0`, returns `0` (the empty-width complement). -/
def complementWithinWidth (n : Nat) : Nat :=
  allOnesMask (size n) - n

/-- Every natural number is strictly less than `1 <<< Nat.size n` (i.e., `2 ^ bit-width`). -/
lemma lt_shiftLeft_one_size (n : Nat) : n < (1 : Nat) <<< Nat.size n := by
  simpa [Nat.shiftLeft_eq_mul_pow] using (Nat.size_le).mp (le_rfl (a := Nat.size n))

/-- The `i`-th bit of `2^i` is `true`. That is, `(1 <<< i).testBit i = true`. -/
lemma testBit_shiftLeft_one_self (i : Nat) : (1 <<< i).testBit i = true := by
  rw [Nat.testBit_shiftLeft]; simp

/-- If `i ≠ j`, then the `j`-th bit of `2^i` is `false`. -/
lemma testBit_shiftLeft_one_ne (i j : Nat) (h : i ≠ j) : (1 <<< i).testBit j = false := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : j ≥ i
  · simp [hle]
    have hsub_ne_zero : j - i ≠ 0 := by
      intro hzero; apply h; omega
    have h_one_bit : (1 : Nat).testBit (j - i) = false := by
      rcases Nat.exists_eq_succ_of_ne_zero hsub_ne_zero with ⟨n, hn⟩
      rw [hn, Nat.testBit_succ]
      simp
    simp [h_one_bit]
  · simp [hle]

/-- If `i < j`, then the `j`-th bit of `2^i` is `false`. -/
lemma testBit_shiftLeft_one_gt (i j : Nat) (h : i < j) : (1 <<< i).testBit j = false :=
  testBit_shiftLeft_one_ne i j (ne_of_lt h)

/-- If `j < i`, then the `j`-th bit of `2^i` is `false`. -/
lemma testBit_shiftLeft_one_lt (i j : Nat) (h : j < i) : (1 <<< i).testBit j = false :=
  testBit_shiftLeft_one_ne i j (Ne.symm (ne_of_lt h))

/-- The `k`-th bit of `m ||| (1 <<< k)` is always `true`. -/
lemma testBit_lor_shiftLeft_one (m k : Nat) : (m ||| (1 <<< k)).testBit k = true := by
  rw [Nat.testBit_lor, testBit_shiftLeft_one_self k, Bool.or_true]

/-- If `s ≠ k`, the `s`-th bit of `m ||| (1 <<< k)` equals the `s`-th bit of `m`. -/
lemma testBit_lor_shiftLeft_one_ne (m s k : Nat) (h : s ≠ k) : (m ||| (1 <<< k)).testBit s = m.testBit s := by
  rw [Nat.testBit_lor, testBit_shiftLeft_one_ne k s h.symm, Bool.or_false]

/-- If `x.testBit i` is `true`, then `2 ^ i ≤ x`.
This is the contrapositive of `Nat.testBit_lt_two_pow`. -/
lemma two_pow_le_of_testBit {x i : Nat} (h : x.testBit i) : 2 ^ i ≤ x := by
  by_contra! hlt
  have htest : x.testBit i = false := Nat.testBit_lt_two_pow hlt
  rw [h] at htest
  simp at htest

/-- If `2^k ≤ x < 2 * 2^k`, then the `k`-th bit of `x` is `true`.
This characterizes when the `k`-th bit is set in terms of the magnitude of `x`. -/
lemma testBit_true_of_lt_two_mul (x k : Nat) (hx1 : 2 ^ k ≤ x) (hx2 : x < 2 * (2 ^ k)) :
    x.testBit k = true := by
  set h := 2 ^ k
  have h_div : x / h = 1 := by
    apply Nat.div_eq_of_lt_le (by simpa [one_mul] using hx1)
    simpa using hx2
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, h_div]
  simp

/-- `(2^k - 1) &&& (2^k) = 0`. The bitwise AND of a mask of `k` ones with the `k`-th power
of two is always zero, since they have no overlapping set bits. -/
lemma land_two_pow_sub_one (k : Nat) : (2 ^ k - 1) &&& (2 ^ k) = 0 := by
  rw [Nat.and_two_pow]
  have hlt : 2 ^ k - 1 < 2 ^ k := by
    by_cases hk : k = 0
    · subst hk; decide
    · have hpos : 0 < 2 ^ k := by
        apply pow_pos (by decide : 0 < 2) k
      omega
  have hfalse : (2 ^ k - 1).testBit k = false :=
    Nat.testBit_eq_false_of_lt hlt
  simp [hfalse]

/-- Build a natural number from a predicate `p : Nat → Bool` over bit positions.
The first `bits` positions are considered; bits beyond `bits` are assumed 0.
This is a convenient wrapper around `Nat.ofBits` that accepts `Nat → Bool` instead of `Fin bits → Bool`. -/
def ofBitsFromPredicate (bits : Nat) (p : Nat → Bool) : Nat :=
  Nat.ofBits (fun (i : Fin bits) => p i.val)

/-- Interleave the bits of two `n`-bit values `a` and `b` into a `2*n`-bit word.
Even positions (0,2,4,...) get bits from `b`, odd positions (1,3,5,...) get bits from `a`. -/
def interleaveBits (n : Nat) (a b : Nat) : Nat :=
  Nat.ofBits (λ (i : Fin (2*n)) =>
    if i.val % 2 = 0 then Nat.testBit b (i.val / 2)
    else Nat.testBit a (i.val / 2)
  )

/-- The `interleaveBits` result is strictly less than `2^(2*n)`. -/
lemma interleaveBits_lt_two_pow (n a b : Nat) : interleaveBits n a b < 2 ^ (2 * n) := by
  dsimp [interleaveBits]
  exact Nat.ofBits_lt_two_pow _

/-- For `j < n`, the bit at position `2*j` (even) of `interleaveBits n a b` equals `Nat.testBit b j`. -/
lemma testBit_interleaveBits_even (n a b : Nat) (j : Nat) (hj : j < n) :
    Nat.testBit (interleaveBits n a b) (2 * j) = Nat.testBit b j := by
  dsimp [interleaveBits]
  have hpos : 2 * j < 2 * n := by omega
  rw [Nat.testBit_ofBits_lt _ (2 * j) hpos]
  have hmod : (2 * j) % 2 = 0 := by omega
  have hdiv : (2 * j) / 2 = j := by omega
  simp [hmod, hdiv]

/-- For `j < n`, the bit at position `2*j+1` (odd) of `interleaveBits n a b` equals `Nat.testBit a j`. -/
lemma testBit_interleaveBits_odd (n a b : Nat) (j : Nat) (hj : j < n) :
    Nat.testBit (interleaveBits n a b) (2 * j + 1) = Nat.testBit a j := by
  dsimp [interleaveBits]
  have hpos : 2 * j + 1 < 2 * n := by omega
  rw [Nat.testBit_ofBits_lt _ (2 * j + 1) hpos]
  have hmod : (2 * j + 1) % 2 = 1 := by omega
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simp [hmod, hdiv]


end Nat

namespace Nat

/-! ### Binary digit extraction (LSB-first)

`binaryBits` extracts the binary digits of a natural number, with the
least significant bit first. For example, `binaryBits 5 = [1, 0, 1]`
(5 in binary is 101, LSB-first gives 1, 0, 1).

This is a base-2 specialization that does not require a `1 < b` proof
argument, unlike the general `digitsInBase`. The LSB-first order makes
it natural for bitwise operations and recursive decomposition.
-/

/-- Binary digits of `n`, least significant bit first.
Returns `[]` for `n = 0`. -/
def binaryBits : Nat → List Nat
  | 0 => []
  | n+1 => ((n+1) % 2) :: binaryBits ((n+1) / 2)
termination_by n => n
decreasing_by
  apply Nat.div_lt_of_lt_mul
  omega

/-! ### Binary character at a specific bit position -/

/-- Returns the binary digit character (`'0'` or `'1'`) of `n` at bit position `i`
(0-indexed, least significant). Uses `Nat.testBit` for efficient bit extraction.

For example, `binaryCharAt 5 0 = '1'` (since 5 in binary is 101, LSB is 1),
`binaryCharAt 5 1 = '0'`, `binaryCharAt 5 2 = '1'`.

This is the `Char`-valued counterpart of `Nat.testBit`, and the inverse
direction of `Char.binaryDigitToNat` for `'0'`/`'1'` inputs. -/
def binaryCharAt (n i : Nat) : Char :=
  if n.testBit i then '1' else '0'

end Nat

namespace Nat

/-! ### Bit operations -/

/-- Bitwise AND is idempotent: `n &&& n = n`. -/

lemma land_self (n : Nat) : n.land n = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_land, Nat.land]

/-- Bitwise OR is idempotent: `n.lor n = n`. -/

lemma lor_self (n : Nat) : n.lor n = n := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h := Nat.testBit_lor n n k
  -- h : (n ||| n).testBit k = (n.testBit k || n.testBit k)
  change (n ||| n).testBit k = n.testBit k
  rw [h, Bool.or_self]

/-- Bitwise AND with zero on the right is zero: `n &&& 0 = 0`. -/

lemma land_zero_right (n : Nat) : n &&& 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_land, Nat.zero_testBit]

/-- Bitwise AND with zero on the left is zero: `0 &&& n = 0`. -/

lemma land_zero_left (n : Nat) : 0 &&& n = 0 := by
  rw [Nat.land_comm, land_zero_right]

/-- Bitwise OR with zero on the right is the identity: `n.lor 0 = n`. -/
lemma lor_zero_right (n : Nat) : n.lor 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.lor, Nat.bitwise, ih]

/-- Absorption law: `(a ||| x) &&& x = x`. Bitwise AND of `(a ∨ x)` with `x` gives `x`. -/
lemma land_lor_self_left (a x : Nat) : (a ||| x) &&& x = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_lor]
  by_cases hx : x.testBit i
  · simp [hx]
  · simp [hx]

/-- If `x > 0`, then `a ||| x > 0`. Bitwise OR with a positive number is positive. -/
lemma lor_pos_of_pos_right (a x : Nat) (hx : x > 0) : (a ||| x) > 0 := by
  by_contra! h
  have hzero : a ||| x = 0 := by omega
  have hx_zero : x = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hzero_bit : (a ||| x).testBit i = false := by rw [hzero, Nat.zero_testBit i]
    rw [Nat.testBit_lor] at hzero_bit
    rcases Bool.or_eq_false_iff.mp hzero_bit with ⟨_, hx_bit⟩
    simpa [Nat.zero_testBit i] using hx_bit
  omega

end Nat


