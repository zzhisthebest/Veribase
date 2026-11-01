import Mathlib

namespace Specific

open _root_.List

namespace Nat

/-- If `x` is either `0` or `1` and `1 < n`, then `x < n`. -/
theorem zero_or_one_lt_of_one_lt {n x : Nat}
    (hx : x = 0 ∨ x = 1) (hn : 1 < n) : x < n := by
  cases hx with
  | inl hzero =>
      rw [hzero]
      exact Nat.lt_trans Nat.zero_lt_one hn
  | inr hone =>
      rw [hone]
      exact hn

/-- If `value < upper` in `Nat`, then both `value ≥ 0` (trivial via `Nat.zero_le`)
and `value < upper`. A convenient conjunction for proof contexts that
need non-negativity and the upper bound simultaneously. -/
theorem bounds_of_lt {value upper : Nat} (h : value < upper) :
    value ≥ 0 ∧ value < upper :=
  ⟨Nat.zero_le value, h⟩

/-- `max a b` is always one of the two arguments. -/
theorem max_eq_left_or_eq_right {a b : Nat} : max a b = a ∨ max a b = b := by
  rcases Nat.le_total a b with (h | h)
  · exact Or.inr (Nat.max_eq_right h)
  · exact Or.inl (Nat.max_eq_left h)

/-! ## Cyclic index

A common pattern in modular / periodic computations: given a `base` value, a
structural `offset`, and an `extra` adjustment, compute the cyclic index
modulo `modulus`. For example, computing a weekday index from year-term,
month-offset, and day-of-month. -/

/-- Compute a cyclic index: `(base + offset + extra) % modulus`.
Useful for indexing into a periodic structure (e.g., days of the week,
ring buffers) where multiple additive components contribute to the position. -/
def cyclicIndex (modulus base offset extra : Nat) : Nat :=
  (base + offset + extra) % modulus

/-! ## One-based cyclic indexing

A common pattern for 1-based cyclic computations (e.g., days of week 1-7):
given a 1-based `current` position, add `offset` and wrap around to stay
in `[1, modulus]`. Contrast with `cyclicIndex` which produces 0-based results. -/

/-- 1-based cyclic index: `((current + offset - 1) % modulus) + 1`.
The result is always in `[1, modulus]` when `0 < modulus`.
Useful for 1-based modular arithmetic where positions are counted from 1
(e.g., days of week, monthly scheduling, ring buffers with 1-based indexing). -/
def oneBasedCyclic (modulus current offset : Nat) : Nat :=
  ((current + offset - 1) % modulus) + 1

/-- `oneBasedCyclic` always stays within `[1, modulus]` when `0 < modulus`. -/
theorem oneBasedCyclic_bounds {modulus current offset : Nat} (hmod : 0 < modulus) :
    1 ≤ oneBasedCyclic modulus current offset ∧
      oneBasedCyclic modulus current offset ≤ modulus := by
  unfold oneBasedCyclic
  constructor
  · omega
  · have hmod' : (current + offset - 1) % modulus < modulus := Nat.mod_lt _ hmod
    omega

/-! ## Standard competitive programming modulus -/

/-- The standard competitive programming prime modulus `10^9 + 7` (= 1000000007).
Used pervasively across modular arithmetic problems. -/
def standardModulus : Nat := 1000000007

@[simp] theorem standardModulus_pos : 0 < standardModulus := by
  native_decide

/-! ## Threshold value

A generic threshold-based conditional: given a `Nat` threshold `t` and two
values `ltVal` (chosen when `n < t`) and `geVal` (chosen when `t ≤ n`),
return the appropriate value. -/

/-- Returns `ltVal` if `n < threshold`, otherwise returns `geVal`.
A generic threshold conditional for any output type `α`. -/
def thresholdValue {α : Type u} (threshold : Nat) (ltVal geVal : α) (n : Nat) : α :=
  if n < threshold then ltVal else geVal

theorem thresholdValue_eq_ltVal_of_lt {α : Type u} {threshold n : Nat} {ltVal geVal : α}
    (h : n < threshold) :
    thresholdValue threshold ltVal geVal n = ltVal := by
  simp [thresholdValue, h]

theorem thresholdValue_eq_geVal_of_le {α : Type u} {threshold n : Nat} {ltVal geVal : α}
    (h : threshold ≤ n) :
    thresholdValue threshold ltVal geVal n = geVal := by
  simp [thresholdValue, not_lt_of_ge h]

/-! ## Threshold flag (specialization of `thresholdValue` to `Nat` with `ltVal := 0`) -/

/-- Returns `0` if `n < threshold`, otherwise returns `value`.
A specialization of `thresholdValue` for `Nat` with `ltVal := 0`. -/
def thresholdFlag (threshold value n : Nat) : Nat :=
  thresholdValue threshold 0 value n

theorem thresholdFlag_eq_zero_of_lt {threshold value n : Nat} (h : n < threshold) :
    thresholdFlag threshold value n = 0 := by
  unfold thresholdFlag
  exact thresholdValue_eq_ltVal_of_lt h

theorem thresholdFlag_eq_value_of_le {threshold value n : Nat} (h : threshold ≤ n) :
    thresholdFlag threshold value n = value := by
  unfold thresholdFlag
  exact thresholdValue_eq_geVal_of_le h

/-! ## Absolute difference -/

/-- Absolute difference of two natural numbers: `absDiff a b` is the distance
between `a` and `b` on the number line. Defined as `a - b` when `a ≥ b`,
and `b - a` otherwise. -/
def absDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

/-! ## Interval length

The length of a closed integer interval `[start, finish]`, i.e. the number of
integers `k` such that `start ≤ k ∧ k ≤ finish`. Computed as `finish - start + 1`.
When `finish < start`, natural subtraction yields `0`, so the result is `1`. -/

/-- Length of a closed interval: `intervalLength start finish = finish - start + 1`.
This is the inclusive count of integers from `start` to `finish`. When
`finish < start`, natural subtraction caps at `0`, giving `1`. -/
def intervalLength (start finish : Nat) : Nat :=
  finish - start + 1

/-! ## Integer division midpoint / ceiling half -/

/-- The midpoint of a natural number, defined as `n / 2` (integer division,
rounding down). -/
def midpoint (n : Nat) : Nat := n / 2

/-- `midpoint n < n` when `2 ≤ n` (i.e. for all `n` except `0` and `1`,
integer division by 2 yields a strictly smaller number). -/
theorem midpoint_lt_self_of_two_le {n : Nat} (h : 2 ≤ n) : midpoint n < n := by
  unfold midpoint
  exact Nat.div_lt_self (by omega) (by omega)

/-- The ceiling of `n / 2`, i.e. the smallest integer `≥ n/2`. Defined as
`n / 2 + n % 2`. For even `n` this equals `n / 2`; for odd `n` this equals
`n / 2 + 1`. -/
def ceilHalf (n : Nat) : Nat :=
  n / 2 + n % 2

@[simp] lemma ceilHalf_one : ceilHalf 1 = 1 := by
  native_decide

@[simp] lemma ceilHalf_two : ceilHalf 2 = 1 := by
  native_decide

@[simp] lemma ceilHalf_three : ceilHalf 3 = 2 := by
  native_decide

lemma ceilHalf_pos_of_pos {n : Nat} (h : 0 < n) : 0 < ceilHalf n := by
  unfold ceilHalf
  omega

lemma ceilHalf_le_self (n : Nat) : ceilHalf n ≤ n := by
  unfold ceilHalf
  omega

/-- `ceilHalf n` can also be expressed as `(n + 1) / 2`, the standard
competitive-programming formula for ceiling division by two. -/
lemma ceilHalf_eq_succ_div_two (n : Nat) : ceilHalf n = (n + 1) / 2 := by
  unfold ceilHalf
  omega

/-- Ceil-half plus floor-half equals the original number: `⌈n/2⌉ + ⌊n/2⌋ = n`. -/
lemma ceilHalf_add_div_two (n : Nat) : ceilHalf n + n / 2 = n := by
  unfold ceilHalf
  omega

/-- `ceilHalf n` is always strictly less than `n + 1`.
This is the `(n+1)/2 < n+1` inequality commonly used in competitive-programming
bounds (e.g., flowerbed / seating problems). -/
lemma ceilHalf_lt_succ (n : Nat) : ceilHalf n < n + 1 := by
  rw [ceilHalf_eq_succ_div_two]
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-! ## Bitwise XOR -/

/-- XOR-ing a number with itself yields `0`, so `(x ^^^ x) ^^^ y` simplifies to `y`. -/
theorem xor_self_then (x y : Nat) : (x ^^^ x) ^^^ y = y := by
  rw [Nat.xor_self, Nat.zero_xor]

/-! ## Bounded result from candidate

A common pattern in optimization/search algorithms: given an optional
candidate value and an upper bound, return `-1` if no candidate exists,
or the minimum of the candidate and the bound (capped to the bound).

This is useful when a search may fail to find a valid result (sentinel `-1`)
but any result should never exceed a known maximum. -/

/-- Returns `-1` if `candidate` is `none`, otherwise `min n bound` (capped to `bound`).
The result is always an `Int` for compatibility with sentinel `-1`. -/
def boundedResultFromCandidate (candidate : Option Nat) (bound : Nat) : Int :=
  match candidate with
  | none => -1
  | some n => (Nat.min n bound : Int)

/-- The result is either `-1` or nonnegative. -/
theorem boundedResultFromCandidate_eq_neg_one_or_nonneg
    (candidate : Option Nat) (bound : Nat) :
    boundedResultFromCandidate candidate bound = -1 ∨
      boundedResultFromCandidate candidate bound ≥ 0 := by
  unfold boundedResultFromCandidate
  cases candidate with
  | none =>
      left
      rfl
  | some n =>
      right
      exact Int.ofNat_nonneg (Nat.min n bound)

/-- The result is always ≤ the bound. -/
theorem boundedResultFromCandidate_le_bound (candidate : Option Nat) (bound : Nat) :
    boundedResultFromCandidate candidate bound ≤ bound := by
  unfold boundedResultFromCandidate
  cases candidate with
  | none =>
      exact Int.le_trans (show (-1 : Int) ≤ 0 by decide) (Int.ofNat_nonneg _)
  | some n =>
      exact Int.ofNat_le.mpr (Nat.min_le_right n _)

/-! ## Option Nat to Int conversion

A common pattern: converting `Option Nat` to `Int`, using a fallback value
(usually `-1`) as a sentinel for "no result". Unlike `boundedResultFromCandidate`,
this function does not cap the value — it simply coerces `Nat` to `Int`. -/

/-- Returns `n` as an `Int` when `value? = some n`, otherwise returns `fallback`.
This is `Option.getD` generalized with a `Nat → Int` coercion. -/
def optionAsIntWith (value? : Option Nat) (fallback : Int) : Int :=
  match value? with
  | some n => n
  | none => fallback

@[simp] theorem optionAsIntWith_some (n : Nat) (fallback : Int) :
    optionAsIntWith (some n) fallback = (n : Int) := rfl

@[simp] theorem optionAsIntWith_none (fallback : Int) :
    optionAsIntWith none fallback = fallback := rfl

/-! ## Min-max ordering -/

/-- The minimum of two naturals is always ≤ their maximum. -/
theorem min_le_max (x y : Nat) :
    Nat.min x y ≤ Nat.max x y :=
  Nat.le_trans (Nat.min_le_left x y) (Nat.le_max_left x y)

/-! ## `min3` and `max3`: Three-way min and max

Common helpers for triple comparisons (e.g., RGB channels, ternary selections). -/

/-- Minimum of three natural numbers: `min a (min b c)`. -/
def min3 (a b c : Nat) : Nat :=
  min a (min b c)

/-- Maximum of three natural numbers: `max a (max b c)`. -/
def max3 (a b c : Nat) : Nat :=
  max a (max b c)

/-- `min3 a b c ≤ a`. -/
theorem min3_le_left (a b c : Nat) : min3 a b c ≤ a :=
  Nat.min_le_left a (min b c)

/-- `min3 a b c ≤ b`. -/
theorem min3_le_middle (a b c : Nat) : min3 a b c ≤ b :=
  Nat.le_trans (Nat.min_le_right a (min b c)) (Nat.min_le_left b c)

/-- `min3 a b c ≤ c`. -/
theorem min3_le_right (a b c : Nat) : min3 a b c ≤ c :=
  Nat.le_trans (Nat.min_le_right a (min b c)) (Nat.min_le_right b c)

/-- `a ≤ max3 a b c`. -/
theorem left_le_max3 (a b c : Nat) : a ≤ max3 a b c :=
  Nat.le_max_left a (max b c)

/-! ## Natural subtraction as `Int`

Truncated natural subtraction `x - amount` (result is `0` when `amount > x`),
cast to `Int`. Useful when subsequent arithmetic involves `Int` values. -/

/-- Truncated natural subtraction `x - amount` cast to `Int`.
Returns `0 : Int` when `amount > x`. -/
def natSubAsInt (x amount : Nat) : Int :=
  ((x - amount : Nat) : Int)

theorem natSubAsInt_nonneg (x amount : Nat) :
    0 ≤ natSubAsInt x amount := by
  unfold natSubAsInt
  omega

/-! ## Decimal digit characters and value conversion -/

/-- `Nat.digitChar (n % 10)` maps back to the numeric value `n % 10`
    when we subtract the character code of `'0'`.
    For example, `(Nat.digitChar 5).toNat - '0'.toNat = 5`. -/
lemma digitChar_mod_ten_val (n : Nat) :
    (Nat.digitChar (n % 10)).toNat - '0'.toNat = n % 10 := by
  have h : n % 10 < 10 := Nat.mod_lt n (by decide)
  interval_cases n % 10 <;> simp [Nat.digitChar]

/-- Converts a list of decimal digit characters to the `Nat` they represent.
    For example, `decimalValue ['1','2','3'] = 123`. -/
def decimalValue : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - '0'.toNat) * 10 ^ cs.length + decimalValue cs

/-- `decimalValue` is a left inverse of `Nat.toDigitsCore 10`:
    converting a number to decimal digit characters and then back yields
    the original number, appended with the given character suffix. -/
lemma toDigitsCore_decimalValue (fuel n : Nat) (h : n < fuel) (cs : List Char) :
    decimalValue (Nat.toDigitsCore 10 fuel n cs) =
      n * 10 ^ cs.length + decimalValue cs := by
  induction fuel generalizing n cs with
  | zero => omega
  | succ fuel ih =>
      simp only [Nat.toDigitsCore]
      by_cases hdiv : n / 10 = 0
      · have hnlt : n < 10 := by
          have hzero_or := (Nat.div_eq_zero_iff).mp hdiv
          omega
        simp [hdiv, decimalValue]
        change (Nat.digitChar (n % 10)).toNat - '0'.toNat = n
        rw [digitChar_mod_ten_val, Nat.mod_eq_of_lt hnlt]
      · simp [hdiv]
        have hrec : n / 10 < fuel := by
          have hnpos : 0 < n := Nat.pos_of_ne_zero (by
            intro hn
            simp [hn] at hdiv)
          have hlt_n : n / 10 < n := Nat.div_lt_self hnpos (by decide)
          exact Nat.lt_of_lt_of_le hlt_n (Nat.le_of_lt_succ h)
        rw [ih (n / 10) hrec (Nat.digitChar (n % 10) :: cs)]
        rw [decimalValue, digitChar_mod_ten_val]
        simp only [List.length_cons, Nat.pow_succ]
        have hdecomp : n / 10 * 10 + n % 10 = n := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod n 10)
        have harith :
            n / 10 * (10 ^ cs.length * 10) +
                n % 10 * 10 ^ cs.length =
              (n / 10 * 10 + n % 10) * 10 ^ cs.length := by
          ring
        rw [← Nat.add_assoc, harith, hdecomp]

/-- `Nat.toDigitsCore b fuel n ds` produces a non-empty list when either fuel remains
    (`0 < fuel`) or the accumulator is already non-empty (`ds ≠ []`).
    This guarantees that the digit list from `Nat.toDigitsCore` is never `[]`
    as long as it has fuel to work with or there is already content in the accumulator. -/
lemma toDigitsCore_ne_nil_of_fuel_or_acc {b : Nat} : ∀ fuel n (ds : List Char),
    0 < fuel ∨ ds ≠ [] → Nat.toDigitsCore b fuel n ds ≠ []
  | 0, _n, ds, h => by
      simp [Nat.toDigitsCore]
      exact h.resolve_left (by omega)
  | fuel + 1, n, ds, _h => by
      simp [Nat.toDigitsCore]
      split
      · simp
      · exact toDigitsCore_ne_nil_of_fuel_or_acc fuel (n / b)
          (Nat.digitChar (n % b) :: ds) (by simp)

/-! ## Digit sum

The sum of the digits of a natural number written in a given base. -/

/-- The sum of the digits of `n` when written in base `base`.
For example, `digitSum 10 123 = 6` (1 + 2 + 3). -/
def digitSum (base n : Nat) : Nat :=
  (Nat.digits base n).sum

/-! ## `Int` to `Option Nat` conversion

Unlike `Int.toNat` (which maps negatives to `0`), this function returns
`none` for negative integers, preserving the information that there was no
natural number counterpart. -/

/-- Converts an `Int` to `Option Nat`. Returns `some n` for non-negative
`Int.ofNat n`, and `none` for negative integers (`Int.negSucc _`). -/
def intToNat? : Int → Option Nat
  | Int.ofNat n => some n
  | Int.negSucc _ => none

@[simp] theorem intToNat?_ofNat (n : Nat) : intToNat? (Int.ofNat n) = some n := rfl

@[simp] theorem intToNat?_negSucc (n : Nat) : intToNat? (Int.negSucc n) = none := rfl

@[simp] theorem intToNat?_zero : intToNat? (0 : Int) = some 0 := rfl

/-! ## `Int` to `Nat` conversion lemmas -/

/-- If an `Int` is strictly positive, its `toNat` is nonzero. -/
theorem int_toNat_ne_zero_of_pos {value : Int} (hvalue : 0 < value) :
    value.toNat ≠ 0 := by
  omega

/-! ## Nonzero implies at least one -/

/-- If a natural number is nonzero, it is at least `1`. -/
theorem one_le_of_ne_zero {n : Nat} (h : n ≠ 0) : 1 ≤ n :=
  Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)

/-- For any `i : Nat`, `1 ≤ i + 1`. Useful for index bounds when
the index is used as an upper bound (e.g., span ≤ index + 1). -/
theorem one_le_succ (i : Nat) : 1 ≤ i + 1 :=
  Nat.succ_le_succ (Nat.zero_le i)

/-- For any `n : Nat`, `1 ≤ n + 2`. -/
theorem one_le_add_two (n : Nat) : 1 ≤ n + 2 :=
  Nat.succ_le_succ (Nat.zero_le (n + 1))

/-! ## Bounded by zero-or-one -/

/-- If a natural number is `0` or `1`, then it is `≤ 1`. -/
theorem le_one_of_eq_zero_or_one {n : Nat} (h : n = 0 ∨ n = 1) : n ≤ 1 := by
  rcases h with rfl | rfl <;> simp

end Nat

/-! ## Absolute difference on `Int`

The `Int` analogue of `Nat.absDiff`: the true mathematical distance between
two integers on the number line, `|a - b|`. -/

/-- Absolute distance between two integers: `absDist a b = |a - b|`. -/
def absDist (a b : Int) : Int :=
  abs (a - b)

@[simp] theorem absDist_self (a : Int) : absDist a a = 0 := by
  simp [absDist]

theorem absDist_nonneg (a b : Int) : 0 ≤ absDist a b :=
  abs_nonneg _

theorem absDist_comm (a b : Int) : absDist a b = absDist b a := by
  simp [absDist, abs_sub_comm]

theorem absDist_eq_zero_iff_eq (a b : Int) : absDist a b = 0 ↔ a = b := by
  simp [absDist, abs_eq_zero, sub_eq_zero]

end Specific
