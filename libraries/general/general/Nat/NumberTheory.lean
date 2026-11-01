import Mathlib
import general.List.Range
import general.Nat.ArithmeticCore
import general.Nat.Range
import general.Nat.Representation
import general.Nat.Search

namespace Nat


/-! ### Counting multiples by either divisor (inclusion-exclusion) -/

/-- Count how many numbers ≤ `x` are divisible by either `a` or `b`,
using the inclusion-exclusion principle: count(a) + count(b) - count(lcm a b). -/
def countDivisibleEither (a b x : Nat) : Nat :=
  x / a + x / b - x / Nat.lcm a b

/-! ### Divisors -/

/-- Count the number of positive divisors of `n` (including 1 and `n` itself).
For `n = 0`, returns `0` (by convention, `Nat.divisors 0` is empty). -/
def countDivisors (n : Nat) : Nat := (Nat.divisors n).card

/-- Count the number of proper divisors of `n` (divisors `d` with `d < n`).
For `n = 0`, returns `0`. Uses mathlib's `Nat.properDivisors` under the hood. -/
def countProperDivisors (n : Nat) : Nat := (Nat.properDivisors n).card

/-- Sum of all proper divisors of `n` (positive divisors `d` with `d < n` and `n % d = 0`).
For `n = 0`, returns `0`. Uses mathlib's `Nat.properDivisors` under the hood.
For example, `sumProperDivisors 6 = 1 + 2 + 3 = 6` (perfect number),
and `sumProperDivisors 12 = 1 + 2 + 3 + 4 + 6 = 16`. -/
def sumProperDivisors (n : Nat) : Nat := (Nat.properDivisors n).sum id

/-! ### GCD and coprime -/

/-- After dividing `a` and `b` by their gcd, the resulting numbers are coprime
(gcd = 1). Requires the left argument to be positive, which guarantees the
gcd is nonzero. This is the `Nat` version of `Int.gcd_div_gcd_eq_one`. -/
lemma gcd_div_gcd_eq_one_of_pos_left {a b : Nat} (ha : 0 < a) : Nat.gcd (a / Nat.gcd a b) (b / Nat.gcd a b) = 1 := by
  have hgpos := Nat.gcd_pos_of_pos_left b ha
  have hcop := Nat.coprime_div_gcd_div_gcd hgpos
  rw [← Nat.coprime_iff_gcd_eq_one]
  exact hcop

/-- After dividing `a` and `b` by their gcd, the resulting numbers are coprime:
the gcd of the reduced pair equals 1. This is the more general version of
`gcd_div_gcd_eq_one_of_pos_left`, requiring only that the gcd is positive
(equivalently, not both `a` and `b` are zero) rather than requiring `0 < a`. -/
lemma gcd_div_gcd_eq_one (a b : ℕ) (hpos : 0 < Nat.gcd a b) : Nat.gcd (a / Nat.gcd a b) (b / Nat.gcd a b) = 1 :=
  Nat.Coprime.gcd_eq_one (Nat.coprime_div_gcd_div_gcd hpos)

/-! ### Competition prime modulus -/

/-- The prime `10⁹ + 7` (1000000007), commonly used as a modulus in competitive programming
to keep results within bounds. Adding this here avoids copying the magic number across problems. -/
def primeMod1e9plus7 : Nat := 1000000007

/-! ### Modular sum over a range -/

/-- Sum `f k` for `k = 0..limit`, applying modulo `modulus` at each step.
This is equivalent to `(∑_{k=0}^{limit} f k) % modulus` by repeated application
of `(a % m + b % m) % m = (a + b) % m`. -/
def sumMod (modulus : Nat) (f : Nat → Nat) (limit : Nat) : Nat :=
  (List.foldl (fun acc k => (acc + f k) % modulus) 0 (List.range (limit + 1)))

/-! ### Triangular numbers -/

/-- The nth triangular number: 0, 1, 3, 6, 10, ... = n*(n+1)/2 -/
def triangularNumber (n : Nat) : Nat := n * (n + 1) / 2


lemma triangularNumber_zero : triangularNumber 0 = 0 := rfl


lemma triangularNumber_one : triangularNumber 1 = 1 := rfl

lemma triangularNumber_nonneg (n : Nat) : 0 ≤ triangularNumber n := by
  unfold triangularNumber; omega

/-- The nth triangular number is at least n (holds for all n, strict for n ≥ 2). -/
lemma triangularNumber_ge_self (n : Nat) : triangularNumber n ≥ n := by
  unfold triangularNumber
  have hpos : 0 < 2 := by decide
  refine (Nat.le_div_iff_mul_le hpos).mpr ?_
  cases n with
  | zero => simp
  | succ n =>
    have hineq : 2 ≤ n.succ + 1 := by omega
    exact Nat.mul_le_mul_left n.succ hineq


/-! ### GCD operations -/

/-- Divide `n` by `gcd n k`. General helper for computing minimal periods:
for a string of length `n` and step size `k`, `divByGcd n k` gives the number of
distinct positions reached before cycling. -/
def divByGcd (n k : Nat) : Nat :=
  n / gcd n k


end Nat

/-! ### Divisibility padding -/

/-- Compute the padding length needed to make `n` divisible by `k`.
Returns `0` if `n % k = 0`, otherwise `k - n % k`.
For example, `padLenToDivBy 5 3 = 1` (since `5 + 1 = 6` is divisible by `3`). -/
def padLenToDivBy (n k : Nat) : Nat := if n % k = 0 then 0 else k - n % k

namespace Nat

/-! ### `isPrime` — Boolean version of `Nat.Prime`

A simple `Bool`-valued primality test, defined as `decide (Nat.Prime n)`.
This is a convenience wrapper for using `Nat.Prime` in list filters and
boolean computations without having to write `decide` inline. -/

/-- Boolean version of `Nat.Prime`: `isPrime n` is `true` iff `Nat.Prime n`. -/
def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

/-- `isPrime n` is equivalent to `Nat.Prime n`. -/

lemma isPrime_iff (n : Nat) : isPrime n ↔ Nat.Prime n := by
  simp [isPrime]

/-! ### `next_prime_ge` — smallest prime ≥ `n`

`next_prime_ge n` returns the smallest prime `p` such that `p ≥ n`.
If `n` itself is prime, `next_prime_ge n = n`; otherwise it returns
the smallest prime strictly greater than `n`.
Implemented via `Nat.find` on `Nat.exists_infinite_primes n`,
so this is a specification-level definition (noncomputable but always valid). -/

/-- Returns the smallest prime `p` satisfying `p ≥ n`.
Uses `Nat.find` on `Nat.exists_infinite_primes n`, which states
for every `n` there exists a prime `p` with `p ≥ n`. -/
def next_prime_ge (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes n)

/-- `next_prime_ge n` is prime. -/
lemma next_prime_ge_prime (n : ℕ) : Nat.Prime (next_prime_ge n) :=
  (Nat.find_spec (Nat.exists_infinite_primes n)).2

/-- `n ≤ next_prime_ge n`. -/
lemma next_prime_ge_ge (n : ℕ) : n ≤ next_prime_ge n :=
  (Nat.find_spec (Nat.exists_infinite_primes n)).1

/-! ### Boolean trial-division primality helper -/

/-- Returns `true` if `n` has no divisor `d` with `2 ≤ d ≤ bound`.
This is a helper for trial-division primality testing.
`hasNoDivisorUpTo n (n-1)` is equivalent to `Nat.Prime n` for `n ≥ 2`. -/
def hasNoDivisorUpTo (n : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | k+2 =>
    if n % (k+2) = 0 then false
    else hasNoDivisorUpTo n (k+1)

/-! ### `hasDivisor` — trial division over a configurable range `[lo, hi]`

A more general alternative to `hasNoDivisorUpTo`: checks whether `n` has a divisor `d`
with `lo ≤ d ≤ hi` by trial division. Requires `lo > 0` for the meaning to be correct
(avoiding the trivial divisor 0). -/

/-- Check whether `n` has a divisor `d` with `lo ≤ d ≤ hi` by trial division. -/
def hasDivisor (n lo hi : Nat) : Bool :=
  if lo > hi then false
  else if n % lo = 0 then true
  else hasDivisor n (lo+1) hi
termination_by hi + 1 - lo

/-- `hasDivisor n lo hi = false` iff no `d` in `[lo, hi]` divides `n`.
Requires `lo > 0` to exclude the trivial divisor 0. -/
lemma hasDivisor_false_iff (n lo hi : Nat) (hpos : lo > 0) :
    hasDivisor n lo hi = false ↔ ∀ d, lo ≤ d → d ≤ hi → ¬(d ∣ n) := by
  revert hpos
  induction lo, hi using hasDivisor.induct n with
  | case1 lo hi h_gt =>
    intro hpos
    unfold hasDivisor
    rw [if_pos h_gt]
    constructor
    · intro _; intro d hdlo hdhi; omega
    · intro _; rfl
  | case2 lo hi h_le h_mod0 =>
    intro hpos
    unfold hasDivisor
    rw [if_neg h_le, if_pos h_mod0]
    have hdiv : lo ∣ n := Nat.dvd_of_mod_eq_zero h_mod0
    constructor
    · intro h; simp at h
    · intro hall
      exfalso
      exact hall lo (le_refl lo) (by omega) hdiv
  | case3 lo hi h_le h_mod_ne ih =>
    intro hpos
    have h_not_div : ¬ (lo ∣ n) := by
      contrapose! h_mod_ne
      exact Nat.mod_eq_zero_of_dvd h_mod_ne
    unfold hasDivisor
    rw [if_neg h_le, if_neg h_mod_ne]
    have hpos_next : lo + 1 > 0 := by omega
    have ih_inst := ih hpos_next
    rcases ih_inst with ⟨h_ih_fwd, h_ih_bwd⟩
    constructor
    · intro h_false d hdlo hdhi
      rcases Nat.eq_or_lt_of_le hdlo with (rfl | hdgt)
      · exact h_not_div
      · exact h_ih_fwd h_false d (by omega) hdhi
    · intro hall
      apply h_ih_bwd
      intro d hdlo1 hdhi
      apply hall d (by omega) hdhi

/-- `hasDivisor n lo hi = true` iff there exists a `d` in `[lo, hi]` that divides `n`.
Requires `lo > 0` to exclude the trivial divisor 0. -/
lemma hasDivisor_true_iff (n lo hi : Nat) (hpos : lo > 0) :
    hasDivisor n lo hi = true ↔ ∃ d, lo ≤ d ∧ d ≤ hi ∧ d ∣ n := by
  revert hpos
  induction lo, hi using hasDivisor.induct n with
  | case1 lo hi h_gt =>
    intro hpos
    unfold hasDivisor
    rw [if_pos h_gt]
    constructor
    · intro h; simp at h
    · intro h_exists
      rcases h_exists with ⟨d, hdlo, hdhi, hdiv⟩
      omega
  | case2 lo hi h_le h_mod0 =>
    intro hpos
    unfold hasDivisor
    rw [if_neg h_le, if_pos h_mod0]
    have hdiv : lo ∣ n := Nat.dvd_of_mod_eq_zero h_mod0
    simp
    exact ⟨lo, by omega, by omega, hdiv⟩
  | case3 lo hi h_le h_mod_ne ih =>
    intro hpos
    have h_not_div : ¬ (lo ∣ n) := by
      contrapose! h_mod_ne
      exact Nat.mod_eq_zero_of_dvd h_mod_ne
    unfold hasDivisor
    rw [if_neg h_le, if_neg h_mod_ne]
    have hpos_next : lo + 1 > 0 := by omega
    have ih_inst := ih hpos_next
    rcases ih_inst with ⟨h_ih_fwd, h_ih_bwd⟩
    constructor
    · intro h
      rcases h_ih_fwd h with ⟨d, hlo1, hhi, hdiv⟩
      exact ⟨d, by omega, hhi, hdiv⟩
    · intro ⟨d, hdlo, hdhi, hdiv⟩
      rcases Nat.eq_or_lt_of_le hdlo with (rfl | hdgt)
      · exact (h_not_div hdiv).elim
      · apply h_ih_bwd
        exact ⟨d, by omega, hdhi, hdiv⟩

/-! ### `filterPrimes` — filter a list of naturals to only primes

Filters a `List Nat`, keeping only the elements that are prime.
Uses `decide` to bridge `Nat.Prime` (a `Prop`) to the `Bool` filter. -/

/-- Filter a list of natural numbers, keeping only the prime elements. -/
def filterPrimes (l : List Nat) : List Nat :=
  l.filter (λ x => decide (Nat.Prime x))

/-- Membership in `filterPrimes l` is equivalent to membership in `l` and being prime. -/

lemma mem_filterPrimes_iff {l : List Nat} {p : Nat} :
    p ∈ filterPrimes l ↔ p ∈ l ∧ Nat.Prime p := by
  dsimp [filterPrimes]
  simp

/-- Membership in `filterPrimes (List.rangeInclusive start fin)` reduces to
`Nat.Prime n ∧ start ≤ n ∧ n ≤ fin`. -/
lemma mem_filterPrimes_rangeInclusive_iff (start fin n : Nat) :
    n ∈ filterPrimes (List.rangeInclusive start fin) ↔ (Nat.Prime n ∧ start ≤ n ∧ n ≤ fin) := by
  rw [mem_filterPrimes_iff, List.mem_rangeInclusive_iff]
  tauto

/-! ### `filterPrimesUpTo` — primes ≤ n (via `List.range (n + 1)`) -/

/-- Return all primes `p` with `p ≤ n` (inclusive).
Equivalent to `filterPrimes (List.range (n + 1))`. For `n < 2`, returns the empty list
(since 0 and 1 are not prime).

See `primesUpTo` for the variant that explicitly starts from 2. -/
def filterPrimesUpTo (n : Nat) : List Nat :=
  filterPrimes (List.range (n + 1))

/-- Membership in `filterPrimesUpTo n` is equivalent to being prime and `p ≤ n`. -/

lemma mem_filterPrimesUpTo_iff {p n : Nat} :
    p ∈ filterPrimesUpTo n ↔ Nat.Prime p ∧ p ≤ n := by
  dsimp [filterPrimesUpTo]
  rw [mem_filterPrimes_iff, List.mem_range_succ_iff]
  exact and_comm

/-! ### `Nodup` and `Forall` for `filterPrimes` -/

/-- Filtering a `Nodup` list by primes preserves `Nodup`. -/
lemma nodup_filterPrimes (l : List Nat) (h : List.Nodup l) : List.Nodup (filterPrimes l) :=
  h.filter (λ x => decide (Nat.Prime x))

/-- Every element of `filterPrimes l` is prime.
This is the `List.Forall` version of `mem_filterPrimes_iff`. -/
lemma forall_prime_filterPrimes (l : List Nat) : List.Forall Nat.Prime (filterPrimes l) := by
  rw [List.forall_iff_forall_mem]
  intro p hp
  exact ((mem_filterPrimes_iff.mp hp).right)

/-- If `Nat.Prime p` and `p ≤ n`, then `p` belongs to `filterPrimes (List.range (n + 1))`.
This is the forward-direction convenience wrapper for `mem_filterPrimesUpTo_iff`. -/
lemma mem_filterPrimes_of_prime_le {n p : Nat} (hp : Nat.Prime p) (hp_le : p ≤ n) :
    p ∈ filterPrimes (List.range (n + 1)) :=
  (mem_filterPrimesUpTo_iff.mpr ⟨hp, hp_le⟩)

/-! ### `listPrimesInRange` — primes `p` with `start ≤ p ≤ end_`

A direct convenience def for filtering primes within a closed interval.
Equivalent to `filterPrimes (List.rangeInclusive start end_)` but uses
`List.range (end_ + 1)` with a combined `decide (Nat.Prime p ∧ start ≤ p)` filter. -/

/-- Return all primes `p` such that `start ≤ p ≤ end_`. -/
def listPrimesInRange (start end_ : Nat) : List Nat :=
  (List.range (end_ + 1)).filter (λ p => decide (Nat.Prime p ∧ start ≤ p))

/-- Membership in `listPrimesInRange`: `p` is in the list iff `p` is prime and `start ≤ p ≤ end_`. -/

lemma mem_listPrimesInRange_iff {p start end_ : Nat} :
    p ∈ listPrimesInRange start end_ ↔ Nat.Prime p ∧ start ≤ p ∧ p ≤ end_ := by
  dsimp [listPrimesInRange]
  rw [List.mem_filter, List.mem_range_succ_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨hle, ⟨hprime, hstart⟩⟩; exact ⟨hprime, hstart, hle⟩
  · rintro ⟨hprime, hstart, hle⟩; exact ⟨hle, ⟨hprime, hstart⟩⟩

/-! ### `primesUpTo` — primes ≤ n (starting from 2) -/

/-- Return all primes `p` with `2 ≤ p ≤ n`. Expressed as filtering `List.range' 2 (n-1)`
by `Nat.Prime`.
For `n < 2`, returns the empty list.

See `filterPrimes` for filtering an arbitrary list to its prime elements. -/
def primesUpTo (n : Nat) : List Nat :=
  List.filter (λ k => decide (Nat.Prime k)) (List.range' 2 (n-1))

/-- Membership in `primesUpTo n` is equivalent to being prime and `2 ≤ p ≤ n`. -/

lemma mem_primesUpTo_iff {p n : Nat} :
    p ∈ primesUpTo n ↔ Nat.Prime p ∧ 2 ≤ p ∧ p ≤ n := by
  dsimp [primesUpTo]
  rw [List.mem_filter]
  constructor
  · rintro ⟨hp_range, hp_dec⟩
    have hp_prime : Nat.Prime p := by simpa using hp_dec
    rcases List.mem_range'_bounds hp_range with ⟨hp_low, hp_high⟩
    exact ⟨hp_prime, hp_low, by omega⟩
  · rintro ⟨hp_prime, hp_low, hp_high⟩
    have hp_dec : decide (Nat.Prime p) = true := by simp [hp_prime]
    refine ⟨?_, hp_dec⟩
    apply List.mem_range'_of_bounds hp_low
    omega

/-! ### Primes in `Finset.range (n+1)` -/

/-- If `q` is prime and `q ≤ n`, then `q` belongs to the `Finset` of primes not exceeding `n`,
i.e. `q ∈ (Finset.range (n + 1)).filter Nat.Prime`.
This is a convenience lemma bridging `Nat.Prime` and `q ≤ n` to `Finset` membership. -/
lemma mem_range_prime_of_le {q n : ℕ} (hq_prime : Nat.Prime q) (hq_le_n : q ≤ n) :
    q ∈ (Finset.range (n + 1)).filter Nat.Prime :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hq_le_n), hq_prime⟩

/-- If `2 ≤ n`, then there exists at least one prime not exceeding `n` (namely `2`).
Thus `(Finset.range (n + 1)).filter Nat.Prime` is nonempty. -/
lemma range_prime_nonempty_of_two_le {n : ℕ} (hn2 : 2 ≤ n) :
    ((Finset.range (n + 1)).filter Nat.Prime).Nonempty :=
  ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hn2), Nat.prime_two⟩⟩

/-- The maximum element of `(Finset.range (n + 1)).filter Nat.Prime` is itself prime,
at most `n`, and is the greatest prime ≤ n. This characterizes the largest prime not
exceeding `n`. -/
lemma max_prime_filter_spec {n : ℕ}
    (hne : ((Finset.range (n + 1)).filter Nat.Prime).Nonempty) :
    Nat.Prime (((Finset.range (n + 1)).filter Nat.Prime).max' hne) ∧
    ((Finset.range (n + 1)).filter Nat.Prime).max' hne ≤ n ∧
    (∀ q : ℕ, Nat.Prime q → q ≤ n → q ≤ ((Finset.range (n + 1)).filter Nat.Prime).max' hne) := by
  set s := (Finset.range (n + 1)).filter Nat.Prime
  have h_greatest := Finset.isGreatest_max' s hne
  have hp_mem_finset : s.max' hne ∈ s := h_greatest.left
  have hp_ub : ∀ x ∈ s, x ≤ s.max' hne := by
    intro x hx
    exact h_greatest.right (by simpa using hx)
  rcases Finset.mem_filter.mp hp_mem_finset with ⟨hp_range, hp_prime⟩
  have hp_lt_succ : s.max' hne < n + 1 := Finset.mem_range.mp hp_range
  have hp_le_n : s.max' hne ≤ n := Nat.le_of_lt_succ hp_lt_succ
  refine ⟨hp_prime, hp_le_n, ?_⟩
  intro q hq_prime hq_le_n
  have hq_in_s : q ∈ s := by
    dsimp [s]
    exact mem_range_prime_of_le hq_prime hq_le_n
  exact hp_ub q hq_in_s

/-! ### Maximum element of `Nat.primesBelow n`

These are additional lemmas about mathlib's `Nat.primesBelow : Finset ℕ` — the set
of primes strictly less than `n`. They complement the existing API in
`Mathlib/NumberTheory/SmoothNumbers.lean`.
-/

/-- If `Nat.primesBelow n` is nonempty, its maximum element is prime, less than `n`, and
at least as large as any prime below `n`. This is the strict `<` variant of
`max_prime_filter_spec` (which uses `(Finset.range (n + 1)).filter Nat.Prime`, i.e. primes ≤ n). -/
lemma max_primesBelow_spec (n : Nat) (hne : (Nat.primesBelow n).Nonempty) :
    Nat.Prime ((Nat.primesBelow n).max' hne) ∧
    (Nat.primesBelow n).max' hne < n ∧
    (∀ q, Nat.Prime q ∧ q < n → q ≤ (Nat.primesBelow n).max' hne) := by
  have hp_mem : (Nat.primesBelow n).max' hne ∈ Nat.primesBelow n := Finset.max'_mem _ hne
  rcases (Nat.mem_primesBelow.mp hp_mem) with ⟨hp_lt, hp_prime⟩
  refine ⟨hp_prime, hp_lt, ?_⟩
  intro q ⟨hq_prime, hq_lt⟩
  have hq_mem : q ∈ Nat.primesBelow n := Nat.mem_primesBelow.mpr ⟨hq_lt, hq_prime⟩
  exact Finset.le_max' (Nat.primesBelow n) q hq_mem

/-! ### Small prime bounds -/

/-- Every prime is at least 2, so it cannot be less than 2.
This is a direct consequence of `Nat.Prime.one_lt`. -/
lemma not_prime_lt_two {p : Nat} (hp : Nat.Prime p) : ¬ p < 2 := by
  have hp1 : 1 < p := Nat.Prime.one_lt hp
  omega

/-- If a prime `p` is less than `3`, then it must be `2`.
This captures the fact that `2` is the only prime below `3`. Useful for
case analysis on small primes. -/
lemma prime_lt_3_eq_2 {p : Nat} (hp : Nat.Prime p) (hplt : p < 3) : p = 2 := by
  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  omega

/-! ### `Nat.minFac` lemmas for non-prime numbers -/

/-- If `2 ≤ n` and `n` is not prime, then `Nat.minFac n` is a prime divisor of `n`
strictly less than `n`. This bundles the three standard `Nat.minFac` lemmas into one. -/
lemma minFac_prime_dvd_lt_of_not_prime {n : Nat} (h_le : 2 ≤ n) (h_not_prime : ¬ Nat.Prime n) :
    Nat.Prime (Nat.minFac n) ∧ Nat.minFac n ∣ n ∧ Nat.minFac n < n := by
  have h_minFac_prime : Nat.Prime (Nat.minFac n) :=
    Nat.minFac_prime (by omega : n ≠ 1)
  have h_minFac_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have h_minFac_lt : Nat.minFac n < n :=
    (Nat.not_prime_iff_minFac_lt h_le).mp h_not_prime
  exact ⟨h_minFac_prime, h_minFac_dvd, h_minFac_lt⟩

/-! ### `sortedPrimeDivisors` — prime divisors of `n` sorted by `≤` -/

/-- Returns the list of all prime divisors of `n`, sorted in non-decreasing order.
Uses `Finset.range (n+1)` to bound the search, then filters for primes that divide `n`. -/
def sortedPrimeDivisors (n : Nat) : List Nat :=
  (Finset.filter (λ d => Nat.Prime d ∧ d ∣ n) (Finset.range (n+1))).sort (· ≤ ·)

/-! ### `primeDivisors` — prime divisors of `n` as a list

Returns the list of all prime divisors of `n`, each appearing at most once.
Uses `List.range (n + 1)` to bound the search, then filters for primes that divide `n`.
The result is automatically in non-decreasing order and has no duplicates.

Compare with `sortedPrimeDivisors` which uses `Finset` and explicit sorting. -/

/-- Returns a list of all prime divisors of `n`, each appearing at most once,
in non-decreasing order. -/
def primeDivisors (n : Nat) : List Nat :=
  List.filter (λ p => Nat.Prime p ∧ p ∣ n) (List.range (n + 1))

/-- If `p` is a member of `primeDivisors n`, then `p` is prime and divides `n`. -/

lemma mem_primeDivisors {n p : Nat} (h : p ∈ primeDivisors n) : Nat.Prime p ∧ p ∣ n := by
  unfold primeDivisors at h
  rcases List.mem_filter.1 h with ⟨_, hmem⟩
  simpa using hmem

/-- If `p` is prime, `p ∣ n`, and `0 < n`, then `p ∈ primeDivisors n`. -/
lemma mem_primeDivisors_of_prime_dvd {n p : Nat}
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hnpos : 0 < n) : p ∈ primeDivisors n := by
  unfold primeDivisors
  apply List.mem_filter.mpr
  have hp_le_n : p ≤ n := Nat.le_of_dvd hnpos hdvd
  refine ⟨by rw [List.mem_range]; omega, ?_⟩
  simp [hp, hdvd]

/-- `primeDivisors n` has no duplicate elements. -/
lemma nodup_primeDivisors (n : Nat) : List.Nodup (primeDivisors n) := by
  unfold primeDivisors
  exact List.Nodup.filter _ (List.nodup_range (n + 1))

/-- `primeDivisors n` is sorted in non-decreasing order. -/
lemma sorted_primeDivisors (n : Nat) : List.Sorted (· ≤ ·) (primeDivisors n) := by
  unfold primeDivisors
  exact List.Sorted.filter _ (List.sorted_le_range (n + 1))

/-! ### Largest prime factor -/

/-- Auxiliary function for `largestPrimeFactor`. Searches primes ≤ `cur` for the
largest prime divisor of `n`. Returns `0` if no prime ≤ `cur` divides `n`.
The search starts from `cur` and descends, so the first prime found is the largest. -/
def largestPrimeFactorAux (n cur : Nat) : Nat :=
  if hlt : cur < 2 then
    0
  else
    if h : Nat.Prime cur ∧ cur ∣ n then
      cur
    else
      largestPrimeFactorAux n (cur - 1)
termination_by cur
decreasing_by
  simp_wf
  omega

/-- Largest prime factor of a natural number `n`. Returns `0` if `n ≤ 1`. -/
def largestPrimeFactor (n : Nat) : Nat :=
  if n ≤ 1 then 0 else largestPrimeFactorAux n n

/-! ### Largest prime factor via `primeFactorsList`

`maxPrimeFactor` computes the largest prime factor of `m` by taking the maximum
of `Nat.primeFactorsList m`, defaulting to `2` when `m < 2`. This is a simpler
alternative to `largestPrimeFactor` (which uses a recursive search). -/

/-- For `m ≥ 2`, the prime factors list is nonempty. -/
lemma primeFactorsList_ne_nil_of_two_le {m : ℕ} (hm2 : 2 ≤ m) : Nat.primeFactorsList m ≠ [] := by
  intro h
  have h' := (Nat.primeFactorsList_eq_nil m).mp h
  have hm_ne_zero : m ≠ 0 := by omega
  have hm_ne_one : m ≠ 1 := by omega
  rcases h' with (h0 | h1)
  · exact hm_ne_zero h0
  · exact hm_ne_one h1

/-- Largest prime factor of `m`, computed as the maximum element of
`Nat.primeFactorsList m`. Defaults to `2` when `m < 2`. -/
def maxPrimeFactor (m : ℕ) : ℕ :=
  (Nat.primeFactorsList m).maximum.unbotD 2

/-! ### `primeFactorsList` dedup membership -/

/-- Membership in `(Nat.primeFactorsList n).dedup` is equivalent to being prime and dividing `n`.
Requires `n ≠ 0` (when `n = 0`, `primeFactorsList 0 = []`). -/
lemma mem_primeFactorsList_dedup_iff {n : Nat} (p : Nat) (hn : n ≠ 0) :
    p ∈ (Nat.primeFactorsList n).dedup ↔ Nat.Prime p ∧ p ∣ n := by
  rw [List.mem_dedup, Nat.mem_primeFactorsList hn]

/-! ### Factorization support and primality -/

/-- If `p` is in the support of `n.factorization`, then `p` is prime.
This bridges `Nat.factorization` support to `Nat.Prime` without going through `Nat.primeFactors`. -/
lemma prime_of_mem_support_factorization {n p : ℕ} (h : p ∈ (Nat.factorization n).support) :
    Nat.Prime p := by
  rw [Nat.support_factorization] at h
  exact Nat.prime_of_mem_primeFactors h

/-! ### `primeDivisorsSet` — prime divisors of `n` as a `Finset ℕ`

A `Finset` version of `primeDivisors`. While `primeDivisors` returns a `List ℕ`
(suitable for ordered iteration), this version returns a `Finset ℕ` which is canonical
for set operations such as `max'`, `min'`, and `filter`. It is equivalent to the
`Finset` underlying `sortedPrimeDivisors` (before sorting). -/

/-- The set of prime divisors of a natural number `n`, as a `Finset ℕ`. -/
def primeDivisorsSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ d => Nat.Prime d ∧ d ∣ n) (Finset.range (n+1))

/-- If `n ≥ 2`, then `primeDivisorsSet n` is nonempty (it contains at least one prime divisor). -/
lemma primeDivisorsSet_nonempty_of_ge_two (n : ℕ) (hn : 2 ≤ n) :
    (primeDivisorsSet n).Nonempty := by
  have hn_ne_one : n ≠ 1 := by omega
  rcases Nat.exists_prime_and_dvd hn_ne_one with ⟨p, hp_prime, hp_dvd⟩
  have hn_pos : 0 < n := by omega
  have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hp_dvd
  have hp_mem_range : p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  have hp_mem : p ∈ primeDivisorsSet n := by
    dsimp [primeDivisorsSet]
    apply Finset.mem_filter.mpr
    exact ⟨hp_mem_range, hp_prime, hp_dvd⟩
  exact ⟨p, hp_mem⟩

/-! ### `maxPrimeDivisor` — largest prime divisor of `n` (for `n ≥ 2`)

Takes the `2 ≤ n` hypothesis as an explicit argument, which guarantees
nonemptiness of `primeDivisorsSet n`. This avoids repeated `omega` proofs
at each use site. -/

/-- The largest prime divisor of `n ≥ 2`. Defined as the maximum element of `primeDivisorsSet n`. -/
def maxPrimeDivisor (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  (primeDivisorsSet n).max' (primeDivisorsSet_nonempty_of_ge_two n hn)

/-- `maxPrimeDivisor n hn` is prime. -/
lemma maxPrimeDivisor_prime {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime (maxPrimeDivisor n hn) := by
  unfold maxPrimeDivisor
  have hm := Finset.max'_mem _ (primeDivisorsSet_nonempty_of_ge_two n hn)
  rcases Finset.mem_filter.mp hm with ⟨_, h⟩
  exact h.1

/-- `maxPrimeDivisor n hn` divides `n`. -/
lemma maxPrimeDivisor_dvd {n : ℕ} (hn : 2 ≤ n) :
    maxPrimeDivisor n hn ∣ n := by
  unfold maxPrimeDivisor
  have hm := Finset.max'_mem _ (primeDivisorsSet_nonempty_of_ge_two n hn)
  rcases Finset.mem_filter.mp hm with ⟨_, h⟩
  exact h.2

/-! ### `maxPrimeDivisorOrOne` — largest prime divisor or 1

A convenience def that returns 1 when `n < 2` and the largest prime divisor otherwise.
This avoids the explicit `hn : 2 ≤ n` hypothesis, consolidating both cases into one. -/

/-- Return 1 if `n < 2`, otherwise the largest prime divisor of `n`. -/
def maxPrimeDivisorOrOne (n : ℕ) : ℕ :=
  if h : n < 2 then 1
  else maxPrimeDivisor n (by omega)

/-! ### `largestPrimeUpTo` — largest prime ≤ k (recursive)

A direct recursive function that returns the largest prime `≤ k`, or `-1`
if no such prime exists (i.e., for `k < 2`). Returns `Int` with `-1` as the
sentinel, consistent with `Nat.findMinWhere`.

For a `Finset`-based specification of the largest prime ≤ n, see
`max_prime_filter_spec` and `max_primesBelow_spec`. -/

/-- Returns the largest prime `≤ k`, or `-1` if no such prime exists.
For `k < 2`, returns `-1` since 0 and 1 are not prime.
For `k ≥ 2`, scans downward from `k` until a prime is found. -/
def largestPrimeUpTo : Nat → Int
  | 0 => (-1 : Int)
  | 1 => (-1 : Int)
  | k+2 =>
    if Nat.Prime (k+2) then
      ((k+2) : Int)
    else
      largestPrimeUpTo (k+1)

end Nat

namespace List

/-- Returns the list of all prime numbers strictly less than `n`. -/
def primesBelow (n : Nat) : List Nat :=
  (range n).filter Nat.Prime

/-- Membership in `primesBelow n` is equivalent to being prime and strictly less than `n`. -/

lemma mem_primesBelow_iff {p n : Nat} :
    p ∈ primesBelow n ↔ Nat.Prime p ∧ p < n := by
  dsimp [primesBelow]
  rw [mem_filter, mem_range, decide_eq_true_iff]
  exact and_comm

/-- `primesBelow n` is strictly sorted by `<`. Since `List.range n` is sorted by `<`
and the filter preserves the order, the primes below `n` are in increasing order. -/
lemma primesBelow_sorted (n : Nat) : (primesBelow n).Sorted (· < ·) := by
  dsimp [primesBelow]
  apply List.Sorted.filter
  exact List.sorted_lt_range _

end List

namespace Nat

/-- Counts the number of prime numbers strictly less than `n`.
Uses `List.primesBelow n` to compute the list, then takes its length.
Contrast with `Nat.countPrimesUpTo` (in `general.Nat`) which counts primes ≤ n (inclusive). -/
def countPrimesBelow (n : Nat) : Nat :=
  (List.primesBelow n).length


lemma countPrimesBelow_zero : countPrimesBelow 0 = 0 := by
  simp [countPrimesBelow, List.primesBelow]


lemma countPrimesBelow_one : countPrimesBelow 1 = 0 := by
  simp [countPrimesBelow, List.primesBelow, Nat.not_prime_zero]

end Nat

namespace Nat


/-! ### Prime counting -/

/-- Count the number of prime numbers `p` with `0 ≤ p ≤ n`. -/
def primeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun m => Nat.Prime m)).length

/-- The number of primes up to `n` is at most `n`. -/
lemma primeCount_le (n : Nat) : primeCount n ≤ n := by
  unfold primeCount
  induction' n with k ih
  · simp [Nat.not_prime_zero]
  · rw [List.range_succ]
    rw [List.filter_append]
    simp
    by_cases hp : Nat.Prime (k + 1)
    · simp [hp]; omega
    · simp [hp]; omega

/-- Recurrence for `primeCount`: adding 1 to the bound increases the count by one
if the new number is prime, otherwise leaves it unchanged. -/
lemma primeCount_succ (m : Nat) :
    primeCount (m + 1) = primeCount m + (if Nat.Prime (m + 1) then 1 else 0) := by
  unfold primeCount
  have hrange : List.range ((m + 1) + 1) = List.range (m + 1) ++ [m + 1] := by
    rw [List.range_succ]
  rw [hrange, List.filter_append, List.length_append]
  by_cases h : Nat.Prime (m + 1)
  · simp [h, primeCount]
  · simp [h, primeCount]

/-- `primeCount m` equals `Nat.count Nat.Prime (m + 1)`, bridging the List-based
and the `Nat.count`-based counting of primes. -/
lemma primeCount_eq_nat_count (m : Nat) :
    primeCount m = Nat.count Nat.Prime (m + 1) := by
  induction' m with k ih
  · unfold primeCount
    decide
  · rw [primeCount_succ k, ih, Nat.count_succ Nat.Prime (k+1)]

/-- The number of primes up to `0` is `0`. -/

lemma primeCount_zero : primeCount 0 = 0 := by
  unfold primeCount; simp [Nat.not_prime_zero]

/-- The number of primes up to `1` is `0`. -/

lemma primeCount_one : primeCount 1 = 0 := by
  unfold primeCount
  have hrange : List.range 2 = [0, 1] := by decide
  rw [hrange]
  simp [Nat.not_prime_zero, Nat.not_prime_one]

/-- `primeCount` is monotone: if `a ≤ b`, then `primeCount a ≤ primeCount b`. -/
lemma primeCount_monotone (a b : Nat) (h : a ≤ b) : primeCount a ≤ primeCount b := by
  induction' h with b h ih
  · rfl
  · rw [primeCount_succ b]
    have h_nonneg : 0 ≤ (if Nat.Prime (b + 1) then 1 else 0) := by
      split <;> omega
    omega

/-- If `k` (with `1 ≤ k`) is not prime, then the prime count doesn't change at `k`. -/
lemma primeCount_not_prime (k : Nat) (hk : 1 ≤ k) (hnp : ¬ Nat.Prime k) :
    primeCount k = primeCount (k - 1) := by
  have hksucc : k = (k - 1) + 1 := by omega
  rw [hksucc, primeCount_succ (k - 1)]
  have : (k - 1) + 1 = k := by omega
  rw [this]
  simp [hnp]

/-- The prime count increases by at most 1 when adding one to the bound.
For `1 ≤ k`, we have `primeCount k ≤ primeCount (k - 1) + 1`. -/
lemma primeCount_le_pred_add_one {k : Nat} (hk : 1 ≤ k) : primeCount k ≤ primeCount (k - 1) + 1 := by
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq, primeCount_succ (k - 1)]
  have : (k - 1) + 1 = k := by omega
  rw [this]
  split <;> omega

/-- The list of prime numbers strictly less than `n`.
For example, `Nat.primesBelowList 10 = [2, 3, 5, 7]`.
Contrast with `Nat.primesBelow : Finset ℕ` (from mathlib) and `Nat.primeCount n`
which returns the *count* of primes `≤ n`. -/
def primesBelowList (n : Nat) : List Nat :=
  List.filter (fun p : Nat => Nat.Prime p ∧ p < n) (List.range n)

/-- A number `p` belongs to `primesBelowList n` iff it is prime and strictly less than `n`. -/

lemma mem_primesBelowList_iff (p n : Nat) : p ∈ primesBelowList n ↔ Nat.Prime p ∧ p < n := by
  simp [primesBelowList, and_comm]

/-! ### Prime numbers up to `n` (inclusive) -/

/-- All prime numbers less than or equal to `n`, in increasing order.
This is the inclusive variant of `primesBelowList`, which returns primes strictly less than `n`. -/
def primesUpToList (n : Nat) : List Nat :=
  List.filter (fun p => decide (Nat.Prime p)) (List.range (n + 1))

/-- Membership in `primesUpToList n` is equivalent to being prime and `p ≤ n`. -/
lemma mem_primesUpToList_iff {n p : Nat} : p ∈ primesUpToList n ↔ Nat.Prime p ∧ p ≤ n := by
  dsimp [primesUpToList]
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp_lt_succ, hp_prime⟩
    have hp_prime' : Nat.Prime p := by simpa using hp_prime
    exact ⟨hp_prime', by omega⟩
  · rintro ⟨hp_prime, hp_le⟩
    refine ⟨by omega, ?_⟩
    simp [hp_prime]

/-- `primesUpToList n` has no duplicates. -/
lemma nodup_primesUpToList (n : Nat) : List.Nodup (primesUpToList n) := by
  dsimp [primesUpToList]
  exact List.Nodup.filter _ (List.nodup_range (n + 1))

/-- `primesUpToList n` is sorted in non-decreasing order. -/
lemma sorted_primesUpToList (n : Nat) : List.Sorted (· ≤ ·) (primesUpToList n) := by
  dsimp [primesUpToList]
  exact List.Sorted.filter _ (List.pairwise_le_range (n + 1))

/-! ### Primes in a closed interval (Finset-based) -/

/-- The set of prime numbers in the closed interval `[a, b]` (inclusive).
Unlike `primesUpToList` (which returns a `List`), this returns a `Finset`,
making it convenient for cardinality and membership queries.

Contrast with:
- `Nat.primesBelowList n` — primes *strictly less than* `n` (List)
- `Nat.primesUpToList n` — primes `≤ n` (List) -/
def primesInRange (a b : Nat) : Finset Nat :=
  (Finset.Icc a b).filter Nat.Prime

/-- Characterization of membership in `primesInRange a b`. -/

lemma mem_primesInRange_iff (a b n : Nat) :
    n ∈ primesInRange a b ↔ a ≤ n ∧ n ≤ b ∧ Nat.Prime n := by
  simp [primesInRange, Finset.mem_Icc, Finset.mem_filter, and_assoc]

/-- A prime in range is at least `a`. -/
lemma lower_le_of_mem_primesInRange (a b n : Nat) (h : n ∈ primesInRange a b) : a ≤ n :=
  ((mem_primesInRange_iff a b n).mp h).1

/-- A prime in range is at most `b`. -/
lemma le_of_mem_primesInRange (a b n : Nat) (h : n ∈ primesInRange a b) : n ≤ b :=
  ((mem_primesInRange_iff a b n).mp h).2.1

/-- A prime in range is prime. -/
lemma prime_of_mem_primesInRange (a b n : Nat) (h : n ∈ primesInRange a b) : Nat.Prime n :=
  ((mem_primesInRange_iff a b n).mp h).2.2

/-- The cardinality of `primesInRange a b` is at most `b + 1`. -/
lemma primesInRange_card_le (a b : Nat) : (primesInRange a b).card ≤ b + 1 := by
  rw [primesInRange]
  have hsub : Finset.Icc a b ⊆ Finset.range (b + 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hx.2)
  calc
    ((Finset.Icc a b).filter Nat.Prime).card ≤ (Finset.Icc a b).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range (b + 1)).card := Finset.card_le_card hsub
    _ = b + 1 := Finset.card_range _

/-! ### First `n` primes -/

/-- Generate the first `n` prime numbers, in increasing order.
Uses `fuel` as the maximum number of natural numbers to examine (for termination).
If `fuel` is too small to find `n` primes, returns a partial list.
For example, `Nat.firstPrimes 5 200 = [2, 3, 5, 7, 11]`. -/
def firstPrimes (n : Nat) (fuel : Nat := 10000) : List Nat :=
  collectFirstN Nat.Prime n fuel 2

/-- All primes in `firstPrimes n fuel` are less than `2 + fuel`. -/
lemma firstPrimes_elements_bound (n fuel : Nat) :
    ∀ p ∈ firstPrimes n fuel, p < 2 + fuel :=
  collectFirstN_elements_bound Nat.Prime n 2 fuel [] (by
    intro x h
    exfalso; exact List.not_mem_nil x h)

/-! ### Distinct prime factors from a list of numbers -/

/-- Compute the distinct prime factors of all numbers in a list.
Flattens `Nat.primeFactorsList` of each element and deduplicates.
For example, `distinctPrimeFactors [6, 10] = [2, 3, 5]` since
`6 = 2·3` and `10 = 2·5`. -/
def distinctPrimeFactors (nums : List Nat) : List Nat :=
  (nums.flatMap Nat.primeFactorsList).dedup

/-- A prime `p` belongs to `distinctPrimeFactors nums` iff it appears in the
prime factor list of some element of `nums`. -/
lemma mem_distinctPrimeFactors_iff (nums : List Nat) (p : Nat) :
    p ∈ distinctPrimeFactors nums ↔ ∃ n ∈ nums, p ∈ n.primeFactorsList := by
  simp [distinctPrimeFactors]

/-- `distinctPrimeFactors nums` is always `Nodup`. -/
lemma nodup_distinctPrimeFactors (nums : List Nat) : List.Nodup (distinctPrimeFactors nums) := by
  rw [distinctPrimeFactors]
  exact List.nodup_dedup _

end Nat

namespace Nat

/-! ### Next Prime -/

/-- For every natural number `p`, there exists a prime `q` strictly greater than `p`. -/
lemma exists_prime_gt (p : Nat) : ∃ q, p < q ∧ Nat.Prime q := by
  have hinf := Nat.exists_infinite_primes (p+1)
  rcases hinf with ⟨q, hq_ge, hq_prime⟩
  refine ⟨q, ?_, hq_prime⟩
  omega

/-- Returns the smallest prime strictly greater than `p`. -/
def nextPrime (p : Nat) : Nat :=
  Nat.find (exists_prime_gt p)

lemma nextPrime_spec (p : Nat) : p < nextPrime p ∧ Nat.Prime (nextPrime p) := by
  unfold nextPrime
  simpa using Nat.find_spec (exists_prime_gt p)

lemma nextPrime_min (p m : Nat) (hm : p < m ∧ Nat.Prime m) : nextPrime p ≤ m := by
  unfold nextPrime
  simpa using Nat.find_min' (exists_prime_gt p) hm

/-- There are no primes strictly between `p` and `nextPrime p`. -/
lemma no_prime_between_and_nextPrime (p : Nat) :
    ∀ m, p < m ∧ m < nextPrime p → ¬ Nat.Prime m := by
  intro m ⟨hm1, hm2⟩ hm_prime
  have h_next_le_m : nextPrime p ≤ m := nextPrime_min p m ⟨hm1, hm_prime⟩
  omega

/-- If there are no primes `k` with `a ≤ k < b`, then `Nat.count Nat.Prime` is
constant on `[a, b)`. This is the `Nat.count` analogue of `countPrimesUpTo_stable`. -/
lemma nat_count_prime_stable (a b : Nat) (hle : a ≤ b)
    (h_no_prime : ∀ k, a ≤ k → k < b → ¬ Nat.Prime k) :
    Nat.count Nat.Prime b = Nat.count Nat.Prime a := by
  revert h_no_prime
  induction' hle with b hle IH
  · intro; rfl
  · intro h_no_prime
    rw [Nat.count_succ Nat.Prime b]
    have h_not_prime_b : ¬ Nat.Prime b := h_no_prime b hle (Nat.lt_succ_self b)
    rw [if_neg h_not_prime_b, add_zero]
    apply IH
    intro k hk_le hk_lt
    apply h_no_prime k hk_le
    omega

/-- The count of primes up to `nextPrime p` equals the count up to `p` plus one,
using `Nat.count Nat.Prime` instead of the recursive `countPrimesUpTo`. -/
lemma nat_count_prime_nextPrime (m : Nat) :
    Nat.count Nat.Prime (nextPrime m + 1) = Nat.count Nat.Prime (m + 1) + 1 := by
  have hspec := nextPrime_spec m
  have hprime : Nat.Prime (nextPrime m) := hspec.2
  have hm1_le_np : m + 1 ≤ nextPrime m := by
    have h_lt : m < nextPrime m := hspec.1
    omega
  have h_no_prime_between : ∀ k, m + 1 ≤ k → k < nextPrime m → ¬ Nat.Prime k := by
    intro k hk_le hk_lt hk_prime
    have hm_lt_k : m < k := by omega
    have hle_next := nextPrime_min m k ⟨hm_lt_k, hk_prime⟩
    omega
  rw [Nat.count_succ Nat.Prime (nextPrime m), if_pos hprime]
  rw [nat_count_prime_stable (m + 1) (nextPrime m) hm1_le_np h_no_prime_between]

/-! ### Iterating `nextPrime` -/

/-- Iterate `nextPrime` `k` times starting from `start`.
`iterateNextPrime 3 5 = nextPrime (nextPrime (nextPrime 5))`. -/
def iterateNextPrime (k : Nat) (start : Nat) : Nat :=
  match k with
  | 0 => start
  | k'+1 => iterateNextPrime k' (nextPrime start)

/-- Iterating `nextPrime` preserves primality. -/
lemma iterateNextPrime_prime (k start : Nat) (hstart : Nat.Prime start) :
    Nat.Prime (iterateNextPrime k start) := by
  induction' k with k ih generalizing start
  · exact hstart
  · unfold iterateNextPrime
    apply ih
    exact (nextPrime_spec start).2

/-! ### Recursive Prime Counting -/

/-- Counts the number of prime numbers ≤ `m` using a recursive definition.
Equivalent to `Nat.primeCount` but defined recursively for easier induction proofs. -/
def countPrimesUpTo : Nat → Nat
  | 0 => 0
  | m+1 =>
    let cnt := countPrimesUpTo m
    if Nat.Prime (m+1) then cnt + 1 else cnt

lemma countPrimesUpTo_succ_not_prime (m : Nat) (h : ¬ Nat.Prime (m+1)) :
    countPrimesUpTo (m+1) = countPrimesUpTo m := by
  simp [countPrimesUpTo, h]

lemma countPrimesUpTo_succ_prime (m : Nat) (h : Nat.Prime (m+1)) :
    countPrimesUpTo (m+1) = countPrimesUpTo m + 1 := by
  simp [countPrimesUpTo, h]

lemma countPrimesUpTo_base : countPrimesUpTo 1 = 0 := by
  simp [countPrimesUpTo, Nat.not_prime_one]

lemma countPrimesUpTo_two : countPrimesUpTo 2 = 1 := by
  simp [countPrimesUpTo, Nat.prime_two, Nat.not_prime_one]

lemma countPrimesUpTo_stable {a b : Nat} (hle : a ≤ b)
    (hno_prime : ∀ m, a < m ∧ m ≤ b → ¬ Nat.Prime m) :
    countPrimesUpTo b = countPrimesUpTo a := by
  induction' b with b ih
  · have ha0 : a = 0 := by omega
    subst ha0; rfl
  · rcases Nat.eq_or_lt_of_le hle with (rfl | hlt)
    · rfl
    · have hle' : a ≤ b := by omega
      have hno' : ∀ m, a < m ∧ m ≤ b → ¬ Nat.Prime m := by
        intro m ⟨hm1, hm2⟩
        apply hno_prime m
        exact ⟨hm1, Nat.le_succ_of_le hm2⟩
      have ih_eq := ih hle' hno'
      have hnp : ¬ Nat.Prime (b+1) := hno_prime (b+1) ⟨by omega, le_rfl⟩
      rw [countPrimesUpTo_succ_not_prime b hnp, ih_eq]

/-- Counting primes up to `nextPrime p` gives exactly one more prime than counting up to `p`. -/
lemma countPrimesUpTo_nextPrime_eq_succ (p : Nat) :
    countPrimesUpTo (nextPrime p) = countPrimesUpTo p + 1 := by
  have h_next_spec : p < nextPrime p ∧ Nat.Prime (nextPrime p) := nextPrime_spec p
  have h_no_prime_between : ∀ m, p < m ∧ m < nextPrime p → ¬ Nat.Prime m :=
    no_prime_between_and_nextPrime p
  have hle_pred : p ≤ nextPrime p - 1 := by
    have hpos : 2 ≤ nextPrime p := Nat.Prime.one_lt h_next_spec.2
    omega
  have h_count_pred_eq : countPrimesUpTo (nextPrime p - 1) = countPrimesUpTo p := by
    apply countPrimesUpTo_stable hle_pred
    intro m ⟨hm1, hm2⟩
    have hm_lt_next : m < nextPrime p := by omega
    exact h_no_prime_between m ⟨hm1, hm_lt_next⟩
  have h_count_next : countPrimesUpTo (nextPrime p) = countPrimesUpTo (nextPrime p - 1) + 1 := by
    have heq : nextPrime p = (nextPrime p - 1) + 1 := by omega
    rw [heq]
    apply countPrimesUpTo_succ_prime (nextPrime p - 1)
    rw [← heq]
    exact h_next_spec.2
  rw [h_count_next, h_count_pred_eq]

/-- The number of primes up to `iterateNextPrime k start` is exactly `countPrimesUpTo start + k`,
assuming `start` is prime. -/
lemma iterateNextPrime_countPrimesUpTo (k start : Nat) (hstart : Nat.Prime start) :
    countPrimesUpTo (iterateNextPrime k start) = countPrimesUpTo start + k := by
  induction' k with k ih generalizing start
  · simp [iterateNextPrime]
  · unfold iterateNextPrime
    rw [ih (nextPrime start) ((nextPrime_spec start).2)]
    rw [countPrimesUpTo_nextPrime_eq_succ start]
    omega

end Nat
