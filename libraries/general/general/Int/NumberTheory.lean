import Mathlib

namespace Int


/-! ### Competition prime modulus (Int version) -/

/-- The prime `10⁹ + 7` (1000000007) as an `Int`, commonly used as a modulus in competitive
programming. This is the `Int` counterpart of `Nat.primeMod1e9plus7`. -/
def primeMod1e9plus7 : Int := 1000000007



/-! ### Propositional integer primality -/

/-- Propositional specification of integer primality: `n > 1` and `n.toNat` is a prime natural
number. This is the `Prop` counterpart of `Int.isPrime` (the boolean version).
For nonnegative `n`, this is equivalent to `Nat.Prime n.toNat`, but the `n > 1` conjunct
excludes `0` and `1` (which have `toNat` values `0` and `1`, not prime) and negative integers
(which always map to non-prime `Nat` values by the primality definition). -/
def IsPrime (n : Int) : Prop :=
  n > 1 ∧ Nat.Prime n.toNat

/-! ### Boolean primality test -/

/-- Boolean primality test for `Int`. Returns `true` if `n` is a prime integer, i.e. `n > 1`
and `Nat.Prime n.toNat`. Uses `decide` to lift the `Prop`-level `Nat.Prime` to `Bool`. -/
def isPrime (n : Int) : Bool :=
  decide (n > 1 ∧ Nat.Prime n.toNat)

/-- `isPrime n` is true exactly when `n > 1` and `Nat.Prime n.toNat`. -/

lemma isPrime_iff (n : Int) : isPrime n ↔ n > 1 ∧ Nat.Prime n.toNat := by
  simp [isPrime]

/-! ### Trial-division primality helper -/

/-- Returns `true` if `n` has no integer divisor `d` with `2 ≤ d ≤ bound`.
The bound is given as a `Nat`. This is a helper for trial-division primality testing:
`hasNoDivisorUpTo n (Int.toNat (n - 1))` is equivalent to `Nat.Prime n.toNat` for `n ≥ 2`.
Contrast with `Nat.hasNoDivisorUpTo` which checks `Nat` divisors. -/
def hasNoDivisorUpTo (n : Int) : Nat → Bool
  | 0 => true
  | 1 => true
  | d+1 =>
    if n % ((d+1 : ℕ) : ℤ) = (0 : ℤ) then
      false
    else
      hasNoDivisorUpTo n d


end Int
