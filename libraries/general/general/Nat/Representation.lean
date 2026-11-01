import Mathlib
import general.Char.Encoding
import general.Nat.ArithmeticCore

namespace Nat


/-! ### String representation in a given base -/

/-- Convert a natural number to its string representation in the given base.
    Uses `Nat.toDigits` to extract digits, then wraps them in a `String`. -/
def toDigitsString (base : Nat) (n : Nat) : String :=
  String.mk (Nat.toDigits base n)

/-- Convert a natural number to its binary string representation. -/
def toBin (n : Nat) : String := toDigitsString 2 n

/-- Convert `n` to its binary string, left-padded with `'0'` to length `k`.
If the binary representation already has length ≥ `k`, no extra padding is added. -/
def toBinPadded (k n : Nat) : String := (toBin n).leftpad k '0'

/-- Helper: produce `n` copies of the character `'0'` as a string. -/
private def repeatZero : Nat → String
  | 0 => ""
  | n+1 => "0" ++ repeatZero n

/-- Zero-pad `n` to at least `width` digits. Returns a string with leading zeros.
For example, `zeroPad 2 5 = "05"` and `zeroPad 2 42 = "42"`. -/
def zeroPad (width : Nat) (n : Nat) : String :=
  let s := toString n
  if s.length < width then
    repeatZero (width - s.length) ++ s
  else
    s



/-! ### Base-b string representation -/

/-- Convert a natural number to its base-`b` string representation using
`Nat.digits` (least-significant-digit first), then reversing and mapping digits to
uppercase characters (`0-9` → `'0'-'9'`, `10-35` → `'A'-'Z'`).
The result is most-significant-digit first. Zero yields `"0"`. -/
def toBaseString (n : Nat) (b : Nat) : String :=
  if n = 0 then
    "0"
  else
    let ds := Nat.digits b n
    let chars := List.map Char.digitCharUpper (List.reverse ds)
    String.mk chars

/-- Expansion of `Nat.toBaseString` when the input is non-zero. -/
lemma toBaseString_eq_of_ne_zero (n b : Nat) (hn : n ≠ 0) :
    Nat.toBaseString n b =
    String.mk (List.map Char.digitCharUpper (List.reverse (Nat.digits b n))) := by
  unfold Nat.toBaseString
  simp [hn]

/-- The `foldl` computation over the reversed base-`b` digits of `n` recovers `n`.
    Uses Horner's method: `foldl (fun acc d => acc * b + d) 0 (reverse (digits b n)) = n`. -/
lemma foldl_rev_digits_eq (b n : Nat) :
    List.foldl (fun acc d => acc * b + d) 0 (List.reverse (Nat.digits b n)) = n := by
  have h_aux : ∀ (ds : List Nat),
      List.foldl (fun acc d => acc * b + d) 0 (List.reverse ds) = Nat.ofDigits b ds := by
    intro ds
    induction' ds with d ds ih
    · simp
    · simp [List.reverse_cons, List.foldl_append, ih, Nat.ofDigits_cons]
      ring
  rw [h_aux, Nat.ofDigits_digits b n]


end Nat

namespace Nat


/-! ### Digits in a given base -/

/-- Sum of the digits of `n` in base `b`, computed via `Nat.digits`.
This is a convenience wrapper around `List.sum ∘ Nat.digits b`.
For `n = 0`, returns `0` (the digit sum of zero is zero).
For a recursively-defined alternative that handles `b ≤ 1`, see `sumDigits`.
For a proof-based termination version requiring `1 < b`, see `digitSumInBase`. -/
def digitsSum (b n : Nat) : Nat :=
  List.sum (Nat.digits b n)


lemma digitsSum_eq (b n : Nat) : digitsSum b n = List.sum (Nat.digits b n) := by
  simp [digitsSum]

/-- Convert a list of digits in base `b` (most significant digit first) to a natural number.
Uses Horner's method: `foldl (fun acc d => acc * b + d) 0`.
For binary, `ofDigitsMSB 2 [1, 0, 1] = 5`. This is the inverse of `digitsInBase`. -/
def ofDigitsMSB (b : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * b + d) 0

/--
Extract the list of digits of `n` in base `b` (where `b > 1`), most significant digit first.
Example: `digitsInBase 10 (by decide) 123 = [1,2,3]`
-/
def digitsInBase (b : Nat) (hb : 1 < b) : Nat → List Nat
  | 0 => []
  | n + 1 => digitsInBase b hb ((n + 1) / b) ++ [(n + 1) % b]
termination_by n => n
decreasing_by
  apply Nat.div_lt_self ?_ hb
  omega

/-- Decimal digits of `n`, most significant digit first. -/
def decimalDigits (n : Nat) : List Nat := digitsInBase 10 (by decide) n

/-- For `0 < n < b`, the digits of `n` in base `b` are just `[n]`. -/
lemma digitsInBase_single_digit {b n : Nat} (hb : 1 < b) (hnpos : 0 < n) (hn : n < b) :
    digitsInBase b hb n = [n] := by
  rcases Nat.exists_eq_succ_of_ne_zero hnpos.ne.symm with ⟨k, hk⟩
  subst hk
  simp [digitsInBase, Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn]

/-- For `0 < n < 10`, the decimal digits are just `[n]`. -/
lemma decimalDigits_single_digit {n : Nat} (hnpos : 0 < n) (hn : n < 10) :
    decimalDigits n = [n] :=
  digitsInBase_single_digit (by decide) hnpos hn

/-! ### Counting trailing zeros in a given base -/

/-- Count how many factors of `b` divide `n`, i.e. the number of trailing zeros
when `n` is written in base `b`. Requires `1 < b` for termination.
For example, `countTrailingZerosInBase 10 (by decide) 1200 = 2`. -/
def countTrailingZerosInBase (b : Nat) (hb : 1 < b) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % b = 0 then
      countTrailingZerosInBase b hb ((n + 1) / b) + 1
    else
      0
termination_by n => n
decreasing_by
  apply Nat.div_lt_self (Nat.zero_lt_succ _) hb

/-- Count how many factors of 10 divide `n`, i.e. the number of trailing zeros in decimal.
Specialization of `countTrailingZerosInBase` for base 10. -/
def countTrailingZeros (n : Nat) : Nat := countTrailingZerosInBase 10 (by decide) n

/-! ### Digit list with zero convention -/

/-- Decimal digits of `n`, most significant digit first, returning `[0]` for `n = 0`.
Unlike `decimalDigits` which returns `[]` for `0`. Uses an accumulator-based
tail-recursive implementation for O(n) complexity. -/
def digitList (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rec go (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else go (m / 10) ((m % 10) :: acc)
    go n []


theorem digitList_zero : digitList 0 = [0] := by
  unfold digitList; rfl

/-- Test whether a natural number's decimal digits read the same forwards and backwards.
Uses `digitList` to extract digits, then checks if the reversed list equals the original. -/
def isPalindrome (n : Nat) : Bool :=
  let d := digitList n
  decide (d.reverse = d)


theorem isPalindrome_zero : isPalindrome 0 := by
  simp [isPalindrome, digitList_zero]

/-- Binary representation of a natural number as a list of 0/1, most-significant bit first.
Uses an accumulator-based tail-recursive implementation. Returns `[]` for `n = 0`.
Contrast with `digitList` which returns `[0]` for `0` and uses base 10. -/
def toBinary (n : Nat) : List Nat :=
  let rec go (m : Nat) (acc : List Nat) : List Nat :=
    if h : m = 0 then acc
    else go (m / 2) ((m % 2) :: acc)
  go n []

/-- `toBinary` of zero is the empty list. -/

theorem toBinary_zero : toBinary 0 = [] := by
  simp [toBinary, toBinary.go]

/-- Extract the first (most significant) decimal digit of a natural number.
For example, `firstDigit 0 = 0`, `firstDigit 5 = 5`, `firstDigit 12345 = 1`. -/
def firstDigit (n : Nat) : Nat :=
  if n < 10 then n else firstDigit (n / 10)
termination_by n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

/-- Extract the i-th digit of `n` in base `b`, least significant digit first (position 0).
Example: `digit 10 12345 0 = 5`, `digit 10 12345 1 = 4`, etc.
For `b = 0`, the result is always 0 (degenerate). -/
def digit (b n i : Nat) : Nat := (n / (b ^ i)) % b

/-- The i-th base-b digit is strictly less than the base (when `b > 0`). -/
theorem digit_lt (b n i : Nat) (hb : 0 < b) : digit b n i < b := by
  unfold digit
  exact Nat.mod_lt _ hb

/-- The 0-th digit (least significant) in base `b` is just `n % b`. -/

lemma digit_zero (b n : Nat) : digit b n 0 = n % b := by
  unfold digit; simp

/-- Sum of the decimal digits of a natural number. -/
def digitSum : Nat → Nat
  | 0 => 0
  | n + 1 =>
    ((n + 1) % 10) + digitSum ((n + 1) / 10)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self
  · exact Nat.succ_pos _
  · decide


lemma digitSum_zero : digitSum 0 = 0 := by
  unfold digitSum; rfl

/-! ### Digital root -/

/-- Digital root of a natural number (base 10).
Returns the repeated sum of decimal digits until a single digit remains.
Formula: 0 for 0; otherwise `((n - 1) % 9) + 1`. -/
def digitalRoot (n : Nat) : Nat :=
  if n = 0 then 0 else ((n - 1) % 9) + 1


lemma digitalRoot_zero : digitalRoot 0 = 0 := rfl

/-! ### Digit sum of lists -/

/-- Sum of digit sums of all elements in a list.
`digitSumList [123, 45] = (1+2+3) + (4+5) = 15`. -/
def digitSumList (l : List Nat) : Nat :=
  (l.map digitSum).sum


theorem digitSumList_nil : digitSumList ([] : List Nat) = 0 := rfl

/-! ### Sum of squares of decimal digits -/

/-- Sum of squares of decimal digits of a natural number,
    computed recursively by extracting the last digit at each step.
    Terminates because `n / 10 < n` for all `n > 0`. -/
def sumSqDigits (n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let d := n % 10
    sumSqDigits (n / 10) + d * d
termination_by n
decreasing_by
  have hpos : 0 < n := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hpos (by norm_num)


theorem sumSqDigits_zero : sumSqDigits 0 = 0 := by
  simp [sumSqDigits]


theorem sumSqDigits_one : sumSqDigits 1 = 1 := by
  rw [sumSqDigits]
  simp [sumSqDigits_zero]

/-- For a single-digit natural number, `sumSqDigits n = n * n`. -/
theorem sumSqDigits_eq_mul_self_of_lt_10 {n : Nat} (h : n < 10) :
    sumSqDigits n = n * n := by
  by_cases hn : n = 0
  · subst hn; simp [sumSqDigits]
  · have hmod : n % 10 = n := Nat.mod_eq_of_lt h
    have hdiv : n / 10 = 0 := Nat.div_eq_of_lt h
    rw [sumSqDigits]
    simp [hn, hmod, hdiv, sumSqDigits_zero]

/-! ### Product of decimal digits -/

/-- Product of all decimal digits of a natural number.
If any digit is 0, the product is 0. Returns 0 for `n = 0`.
Uses a tail-recursive helper for efficiency. -/
def digitProduct (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ =>
    let rec go (x acc : Nat) : Nat :=
      if x = 0 then acc
      else
        let d := x % 10
        let acc' := if d = 0 then 0 else acc * d
        go (x / 10) acc'
    go n 1

/-- Compute the sum of digits of `n` when expressed in base `b`.
    Deliberately total: for degenerate bases `b = 0` or `b = 1`, returns
    reasonable values (0 or n) rather than diverging. -/
def sumDigits (b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if hb : 1 < b then
      (n + 1) % b + sumDigits b ((n + 1) / b)
    else
      if hb0 : b = 0 then 0 else n + 1
termination_by n => n
decreasing_by
  apply Nat.div_lt_self ?_ hb
  omega

/-- The digit sum in any base is zero when the input is zero. -/

theorem sumDigits_zero (b : Nat) : sumDigits b 0 = 0 := by
  unfold sumDigits
  rfl

/-! ### Sum of digits in a given base (proof-based termination) -/

/-- Sum of the digits of a natural number in a given base.
    Requires `base > 1` for termination.
    For example, `digitSumInBase 10 (by decide) 123 = 6`.

    This is a cleaner alternative to `sumDigits` for the `1 < base` case,
    taking the proof as an explicit argument rather than checking it at each
    recursive call. -/
def digitSumInBase (base : Nat) (hbase : 1 < base) : Nat → Nat
  | 0 => 0
  | n + 1 => ((n + 1) % base) + digitSumInBase base hbase ((n + 1) / base)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_succ _) hbase


lemma digitSumInBase_zero (base : Nat) (hbase : 1 < base) : digitSumInBase base hbase 0 = 0 := by
  unfold digitSumInBase; rfl

/-! ### Counting occurrences of a specific digit -/

/-- Count how many times digit `d` appears in the base-`b` representation of `n`.
Requires `1 < b` for termination. Returns `0` for `n = 0`.
For example:
- `countDigitInBase 10 (by decide) 1 12341 = 2` (two 1's in 12341)
- `countDigitInBase 2 (by decide) 1 10 = 2` (10 in binary is 1010, has two 1's) -/
def countDigitInBase (b : Nat) (hb : 1 < b) (d : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    (if (n + 1) % b = d then 1 else 0) + countDigitInBase b hb d ((n + 1) / b)
termination_by n
decreasing_by
  apply Nat.div_lt_self (Nat.zero_lt_succ _) hb

/-- Count how many times digit `1` appears in the decimal representation of `n`.
Specialization of `countDigitInBase` for base 10 and digit 1. -/
def countDigitOne (n : Nat) : Nat := countDigitInBase 10 (by decide) 1 n


theorem countDigitInBase_zero (b : Nat) (hb : 1 < b) (d : Nat) : countDigitInBase b hb d 0 = 0 := by
  simp [countDigitInBase]


theorem countDigitOne_zero : countDigitOne 0 = 0 := by
  simp [countDigitOne, countDigitInBase]

/-! ### Checking membership of a digit -/

/-- `containsDigit n d` is true when digit `d` appears in the decimal (base-10)
representation of `n`.
For example, `containsDigit 123 2` is true because `Nat.digits 10 123 = [1, 2, 3]`. -/
def containsDigit (n d : Nat) : Prop :=
  d ∈ Nat.digits 10 n

/-- For `n > 0`, the digits of `n` in base `b` (where `b > 1`) are nonempty. -/
lemma digitsInBase_nonempty (b : Nat) (hb : 1 < b) (n : Nat) (hpos : n > 0) :
    digitsInBase b hb n ≠ [] := by
  cases n with
  | zero => omega
  | succ k =>
    simp [digitsInBase]

/-- Check whether all digits of `n` in base `b` (where `b > 1`) are nonzero.
Returns `false` for `n = 0` (since `0` consists of digit `0`). -/
def noZeroDigitInBase (b : Nat) (hb : 1 < b) (n : Nat) : Bool :=
  n ≠ 0 && (digitsInBase b hb n).all (fun d => decide (d ≠ 0))

/-- Check if all digits in the base-`b` representation of `n` are either `0` or `1`.
Requires `hb : 2 ≤ b` for termination and semantic correctness.
For `b = 2`, this checks whether `n` is a "binary-only" number.
For `b = 3`, this is the key test for representing `n` as sum of distinct powers of 3. -/
def allDigitsZeroOrOne (b : Nat) (hb : 2 ≤ b) : Nat → Bool
  | 0 => true
  | n + 1 => if (n + 1) % b ≥ 2 then false
             else allDigitsZeroOrOne b hb ((n + 1) / b)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self (Nat.zero_lt_succ _)
  omega

/-- `ofDigitsMSB` and `digitsInBase` are inverses: converting a number to digits
in base `b` (where `b > 1`) and back via Horner's method recovers the original number. -/
lemma ofDigitsMSB_digitsInBase (b : Nat) (hb : 1 < b) (n : Nat) :
    Nat.ofDigitsMSB b (digitsInBase b hb n) = n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hzero : n = 0
  · subst hzero; simp [digitsInBase, Nat.ofDigitsMSB]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
    rcases Nat.exists_eq_succ_of_ne_zero hzero with ⟨k, hk⟩
    subst hk
    simp [digitsInBase, Nat.ofDigitsMSB]
    have h_ih : List.foldl (fun acc d => acc * b + d) 0
        (digitsInBase b hb ((k+1) / b)) = (k+1) / b := by
      rw [← Nat.ofDigitsMSB]
      exact ih ((k+1) / b) (Nat.div_lt_self (by omega) hb)
    rw [h_ih, mul_comm, Nat.div_add_mod (k+1) b]

/-! ### Maximum digit and digit fill -/

/-- Maximum digit in the base-`b` representation of `n`. Requires `1 < b` for termination.
For base 10, returns the largest decimal digit. -/
def maxDigitInBase (b : Nat) (hb : 1 < b) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let d := (n + 1) % b
    let m := maxDigitInBase b hb ((n + 1) / b)
    max d m
termination_by n => n
decreasing_by
  apply Nat.div_lt_self (Nat.succ_pos _) hb

/-- Maximum decimal digit of a natural number.
Specialization of `maxDigitInBase` for base 10. -/
def maxDigit (n : Nat) : Nat := maxDigitInBase 10 (by decide) n

/-- Fill every base-`b` digit position of `n` with digit `d`.
The result has the same number of digits as `n` in base `b`. Requires `1 < b` for termination. -/
def digitFillInBase (b : Nat) (hb : 1 < b) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (d * b) + digitFillInBase b hb d ((k + 1) / b)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self (Nat.succ_pos _) hb

/-- Fill every decimal digit position of `n` with digit `d`.
The result has the same number of digits as `n`.
Specialization of `digitFillInBase` for base 10. -/
def digitFill (d : Nat) (n : Nat) : Nat := digitFillInBase 10 (by decide) d n


theorem digitFill_zero (d : Nat) : digitFill d 0 = 0 := by
  simp [digitFill, digitFillInBase]

/-! ### Power of 10 -/

/-- `pow10 n = 10^n`. A specialized power function for base 10,
useful for decimal digit manipulation. -/
def pow10 : Nat → Nat
| 0 => 1
| (k+1) => 10 * pow10 k

/-! ### Counting digits in a given base -/

/-- Number of digits of `n` when expressed in base `b`.
Returns 1 when `n = 0`, otherwise computes `(Nat.digits b n).length`. -/
def numDigitsInBase (b : Nat) (n : Nat) : Nat :=
  if n = 0 then 1 else (Nat.digits b n).length

/-- Number of decimal digits of `n` (base 10). -/
def numDigits (n : Nat) : Nat := numDigitsInBase 10 n

/-! ### Recursive digit length -/

/-- Number of digits of `n` in base `b` (recursive definition, requires `1 < b` for termination).
More convenient for induction proofs than `numDigitsInBase`.
Returns `1` for `n = 0` (representing the digit `0`). -/
def digitLengthInBase (b : Nat) (hb : 1 < b) : Nat → Nat
| 0 => 1
| (n+1) =>
  if n + 1 < b then 1
  else 1 + digitLengthInBase b hb ((n + 1) / b)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self (Nat.succ_pos _) hb

/-- Number of decimal digits of `n` (base 10, recursive definition).
Equivalent to `numDigits n` but defined recursively for easier induction. -/
def digitLength (n : Nat) : Nat := digitLengthInBase 10 (by decide) n

/-! ### Concatenating numbers in a given base -/

/-- Concatenate two natural numbers in a given base.
    `concatNatInBase base h a b` places `b` after `a` in positional notation.
    For example, `concatNatInBase 10 (by decide) 12 345 = 12345`. -/
def concatNatInBase (base : Nat) (hbase : 1 < base) (a b : Nat) : Nat :=
  a * (base ^ digitLengthInBase base hbase b) + b

/-! ### Digit at a specific position -/

/-- Extract the digit at position `pos` (1-indexed from the left) of number `m` in base `b`.
Requires `1 < b` for `digitLengthInBase` to terminate.
Example: `digitAtPosInBase 10 (by decide) 12345 1 = 1`, `digitAtPosInBase 10 (by decide) 12345 5 = 5`. -/
def digitAtPosInBase (b : Nat) (hb : 1 < b) (m pos : Nat) : Nat :=
  let len := digitLengthInBase b hb m
  (m / (b ^ (len - pos))) % b

/-- Extract the decimal digit at position `pos` (1-indexed from the left) of number `m`.
Uses `pow10` for the power of 10 computation.
Example: `digitAtPos 12345 1 = 1`, `digitAtPos 12345 5 = 5`. -/
def digitAtPos (m pos : Nat) : Nat :=
  let len := digitLength m
  (m / pow10 (len - pos)) % 10

/-! ### Total decimal digits up to a number -/

/-- Sum of `digitLength k` for `k = 1` to `n`.
Returns the total number of decimal digits in the sequence `1, 2, ..., n`.
For `n = 0`, returns `0`. -/
def totalDigitsUpTo : Nat → Nat
| 0 => 0
| (k+1) => totalDigitsUpTo k + digitLength (k+1)

/-! ### Counting divisions by a base until zero -/

/-- Number of times `x` can be divided by `base` (with `base ≥ 2`) until reaching 0.
Provides the floor-logarithmic count: for `x > 0`, `divCount base hb x` returns the
smallest `k` such that `x / base^k = 0` (equivalently, `Nat.log base x + 1`).
For `x = 0`, returns `0` (no divisions needed to reach `0`).

The recursive definition is designed for easy induction in proofs. -/
def divCount (base : Nat) (hb : 1 < base) (x : Nat) : Nat :=
  match x with
  | 0 => 0
  | n + 1 => 1 + divCount base hb ((n + 1) / base)
termination_by x
decreasing_by
  apply Nat.div_lt_self (by omega) hb


lemma divCount_zero (base : Nat) (hb : 1 < base) : divCount base hb 0 = 0 := by
  rw [divCount]

lemma divCount_succ (base : Nat) (hb : 1 < base) (n : Nat) :
    divCount base hb (n + 1) = 1 + divCount base hb ((n + 1) / base) := by
  simp [divCount]

lemma divCount_eq_zero_iff (base : Nat) (hb : 1 < base) (x : Nat) :
    divCount base hb x = 0 ↔ x = 0 := by
  cases x with
  | zero => simp [divCount_zero]
  | succ n => simp [divCount_succ]

lemma divCount_pos_iff (base : Nat) (hb : 1 < base) (x : Nat) :
    0 < divCount base hb x ↔ x ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, divCount_eq_zero_iff]

lemma divCount_one (base : Nat) (hb : 1 < base) : divCount base hb 1 = 1 := by
  rw [divCount_succ, Nat.div_eq_of_lt hb, divCount_zero]

/-! ### Digit reversal in a given base -/

/-- Auxiliary function for `Nat.reverseDigitsInBase`: reverses the
base-`b` digits of `n` and appends them in front of `acc`. -/
def reverseDigitsInBaseAux (b : Nat) (hb : 1 < b) (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => reverseDigitsInBaseAux b hb ((k + 1) / b) (acc * b + (k + 1) % b)
termination_by n
decreasing_by
  apply Nat.div_lt_self (Nat.succ_pos _) hb

/-- Reverse the base-`b` digits of `n`.
For `b = 10`, this reverses the decimal digits:
`Nat.reverseDigitsInBase 10 (by decide) 12345 = 54321`. -/
def reverseDigitsInBase (b : Nat) (hb : 1 < b) (n : Nat) : Nat :=
  reverseDigitsInBaseAux b hb n 0

/-- Reverse the decimal digits of a natural number.
For example: `Nat.reverseDecimalDigits 12345 = 54321`.
This is a specialization of `reverseDigitsInBase` for base 10. -/
def reverseDecimalDigits (n : Nat) : Nat :=
  reverseDigitsInBase 10 (by decide) n


lemma reverseDigitsInBase_zero (b : Nat) (hb : 1 < b) : reverseDigitsInBase b hb 0 = 0 := by
  simp [reverseDigitsInBase, reverseDigitsInBaseAux]


lemma reverseDecimalDigits_zero : reverseDecimalDigits 0 = 0 := by
  exact reverseDigitsInBase_zero 10 (by decide)

/-! ### Bit reversal (fixed width) -/

/-- Helper: reverses the low `k` bits of `n` and appends them above `acc`.
`mirrorBitsAux n k acc` processes `k` bits of `n` (starting from LSB),
shifting `acc` left by `k` and filling the new low `k` positions with
the bits of `n` in reversed order.

Contrast with `reverseDigitsInBaseAux` which processes **all** digits of `n`
in a general base until `n = 0`. This function processes exactly `k` bits
regardless of whether `n` still has bits. -/
def mirrorBitsAux (n k acc : Nat) : Nat :=
  match k with
  | 0 => acc
  | k' + 1 => mirrorBitsAux (n / 2) k' (acc * 2 + n % 2)

end Nat

namespace Nat


/-! ### Lemmas about `numDigits` -/


lemma numDigits_zero : numDigits 0 = 1 := by
  unfold numDigits numDigitsInBase; rfl

/-- For a single-digit number (0 ≤ n < 10), the number of decimal digits is 1. -/
lemma numDigits_single_digit {n : Nat} (h : n < 10) : numDigits n = 1 := by
  unfold numDigits numDigitsInBase
  by_cases hn : n = 0
  · subst hn; rfl
  · simp [hn, Nat.digits_of_lt 10 n hn h]

/-- `numDigits` is always at least 1, even for 0 (which has 1 digit). -/
lemma numDigits_pos (n : Nat) : 1 ≤ numDigits n := by
  unfold numDigits numDigitsInBase
  split
  · omega
  · rename_i h
    have hnil : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr h
    have hlen : 0 < (Nat.digits 10 n).length := List.length_pos_iff.mpr hnil
    omega


/-! ### Decimal concatenation -/

/-- Decimal concatenation of two natural numbers: `concat a b` places `a` in front of `b`.
For example, `concat 12 345 = 12345`. -/
def concat (a b : Nat) : Nat :=
  a * (10 ^ numDigits b) + b


lemma concat_zero_left (b : Nat) : concat 0 b = b := by
  simp [concat]

lemma concat_zero_right (a : Nat) : concat a 0 = a * 10 := by
  simp [concat, numDigits_zero]


end Nat


namespace Nat

/-! ### Parsing natural numbers from character lists -/

/-- Consume leading digit characters and accumulate them into a natural number.
Returns the parsed number together with the remaining (unconsumed) characters.
Stops when a non-digit character is encountered.

This is an accumulator-based helper; `parseNatFromChars` is the top-level entry point. -/
def parseDigitsFromChars (n : Nat) : List Char → Nat × List Char
  | [] => (n, [])
  | c :: cs =>
    if c.isDigit then
      let d : Nat := c.toNat - '0'.toNat
      parseDigitsFromChars (n * 10 + d) cs
    else
      (n, c :: cs)

/-- Parse a natural number from the front of a character list.
Returns `some (n, rest)` where `n` is the parsed number and `rest` is the
remainder of the list, or `none` if the list is empty or does not start with a digit. -/
def parseNatFromChars (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | [] => none
  | c :: cs' =>
    if c.isDigit then
      let d : Nat := c.toNat - '0'.toNat
      let (n, rest) := parseDigitsFromChars d cs'
      some (n, rest)
    else
      none

/-- Convert a list of decimal digit characters to the corresponding natural number
by folding from the most significant digit first. Uses `Char.digitToNat` for
per-character conversion. No validation is performed — callers must ensure all
characters are decimal digits or accept that non-digit characters produce
(a still well-defined but semantically meaningless) numeric contribution.

This is the simple, non-validating companion to `parseNatFromChars` (which returns
`Option (Nat × List Char)` and stops at the first non-digit).

For example:
* `ofDigitChars ['1','2','3'] = 123`
* `ofDigitChars ['0'] = 0`
* `ofDigitChars [] = 0` -/
def ofDigitChars (cs : List Char) : Nat :=
  cs.foldl (λ acc c => acc * 10 + Char.digitToNat c) 0


lemma ofDigitChars_nil : ofDigitChars [] = 0 := rfl

/-! ### Division with offset -/

/-- If `total > 0` and `d ≥ 1`, then `(total + (d - 1)) / d > 0`.
This is a version of `Nat.div_pos` for the "ceiling-like" numerator `total + (d - 1)`. -/
lemma div_pos_of_pos_add_sub_one (total d : Nat) (hd : 1 ≤ d) (htotal : 0 < total) :
    0 < (total + (d - 1)) / d := by
  apply Nat.div_pos
  · omega
  · exact hd

/-! ### Square root -/

/-- If `n = k*k` (i.e. `n` is a perfect square), then `Nat.sqrt n = k`. -/
lemma sqrt_eq_of_sq_eq {k n : Nat} (h : n = k * k) : Nat.sqrt n = k := by
  rw [h]
  exact Nat.sqrt_eq k

end Nat
