import Mathlib

namespace Nat

/-! ### Digit sum in arbitrary base

These definitions compute the sum of digits of a natural number `n` in a given
base `k` (where `1 < k`). Two equivalent formulations are provided:

* `digitSumBase n k hk` — structurally recursive, convenient for reasoning.
* `sumDigits_specificDuplicate n k hk` — tail-recursive (via `sumDigitsAux`), efficient for computation.

The theorem `sumDigits_eq_digitSumBase` shows they are equal.
-/

/-- Tail-recursive accumulator for digit sum in base `k`. -/
def sumDigitsAux (k : Nat) (hk : 1 < k) (n acc : Nat) : Nat :=
  if h : n = 0 then acc
  else sumDigitsAux k hk (n / k) (acc + n % k)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) hk

/-- Sum of digits of `n` in base `k`, tail-recursively using `sumDigitsAux`. -/
def sumDigits_specificDuplicate (n k : Nat) (hk : 1 < k) : Nat :=
  sumDigitsAux k hk n 0

/-- Sum of digits of `n` in base `k`, simple structural recursion.
This is easier to reason about than the tail-recursive version. -/
def digitSumBase (n k : Nat) (hk : 1 < k) : Nat :=
  if hzero : n = 0 then 0
  else (n % k) + digitSumBase (n / k) k hk
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hk

/-- Tail-recursive `sumDigitsAux` equals the naive recursive `digitSumBase` plus the accumulator.
This holds for any proofs `hk`, `hk'` of `1 < k`. -/
theorem sumDigitsAux_eq_add (n k acc : Nat) (hk hk' : 1 < k) :
    sumDigitsAux k hk n acc = digitSumBase n k hk' + acc := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n IH =>
    rw [sumDigitsAux, digitSumBase]
    by_cases hzero : n = 0
    · simp [hzero]
    · simp [hzero]
      rw [IH (n / k) (Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hk) (acc + n % k)]
      omega

/-- The tail-recursive `sumDigits_specificDuplicate` agrees with the naive `digitSumBase`. -/
theorem sumDigits_eq_digitSumBase (n k : Nat) (hk hk' : 1 < k) :
    sumDigits_specificDuplicate n k hk = digitSumBase n k hk' := by
  unfold sumDigits_specificDuplicate
  rw [sumDigitsAux_eq_add n k 0 hk hk', add_zero]

/-! ### Digit count in arbitrary base

`digitCountBase n k hk d` counts how many times the digit `d` appears in the
base-`k` representation of `n`. For example, `digitCountBase 11233 10 (by norm_num) 3 = 2`
because the digit `3` appears twice in `11233`.

This is the counting counterpart to `digitSumBase` and follows the same
structural recursion pattern. Useful for problems involving digit frequency
analysis (e.g., LeetCode 2578 "Split With Minimum Sum"). -/

/-- Count how many times digit `d` appears in the base-`k` representation of `n`.
Requires `1 < k` (base must be at least 2). -/
def digitCountBase (n k : Nat) (hk : 1 < k) (d : Nat) : Nat :=
  if hzero : n = 0 then 0
  else (if n % k = d then 1 else 0) + digitCountBase (n / k) k hk d
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hk

/-! ### Digit square sum

`digitSqSumBase n b hb` computes the sum of the squares of the digits of `n` in
base `b` (where `1 < b`). This is the core step in the Happy Number problem
(LeetCode 202): replace `n` by the sum of squares of its digits.

`digitSqSum n` is the specialization to decimal (base 10). -/

/-- Sum of squares of digits of `n` in base `b`, requiring `1 < b`.
Computes ∑ dᵢ² where dᵢ are the digits of `n` in base `b`.
This is the "happy number" step: replace n by the sum of squares of its digits. -/
def digitSqSumBase (n b : Nat) (hb : 1 < b) : Nat :=
  if hzero : n = 0 then 0
  else (n % b) * (n % b) + digitSqSumBase (n / b) b hb
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hb

/-- Sum of squares of decimal (base 10) digits of `n`.
Equivalent to `digitSqSumBase n 10 (by norm_num)`. -/
def digitSqSum (n : Nat) : Nat :=
  if hzero : n = 0 then 0
  else (n % 10) * (n % 10) + digitSqSum (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by norm_num)

/-- `digitSqSum n` equals `digitSqSumBase` specialized to base 10. -/
theorem digitSqSum_eq_digitSqSumBase (n : Nat) :
    digitSqSum n = digitSqSumBase n 10 (by norm_num) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digitSqSum, digitSqSumBase]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      exact ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num))

/-! ### Digit product

`digitProductBase n b hb` computes the product of the digits of `n` in base `b`
(where `1 < b`). The product of no digits (when `n = 0`) is `1`, the
multiplicative identity.

`digitProduct_specificDuplicate n` is the specialization to decimal (base 10).
-/

/-- Product of digits of `n` in base `b`, requiring `1 < b`.
The product of no digits (when `n = 0`) is `1` (the multiplicative identity). -/
def digitProductBase (n b : Nat) (hb : 1 < b) : Nat :=
  if hzero : n = 0 then 1
  else (n % b) * digitProductBase (n / b) b hb
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hb

/-- Product of decimal (base 10) digits of `n`.
Equivalent to `digitProductBase n 10 (by norm_num)`. -/
def digitProduct_specificDuplicate (n : Nat) : Nat :=
  if hzero : n = 0 then 1
  else (n % 10) * digitProduct_specificDuplicate (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by norm_num)

/-- `digitProduct_specificDuplicate n` equals `digitProductBase` specialized to base 10. -/
theorem digitProduct_eq_digitProductBase (n : Nat) :
    digitProduct_specificDuplicate n = digitProductBase n 10 (by norm_num) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digitProduct_specificDuplicate, digitProductBase]
    split_ifs with hzero
    · rfl
    · apply congrArg (fun x => (n % 10) * x)
      exact ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by norm_num))

/-! ### Digit list decomposition

`digitListBase n b hb` decomposes `n` into its list of digits in base `b`
(most significant digit first), requiring `1 < b`. For example,
`digitListBase 123 10 (by norm_num) = [1,2,3]`.

`decimalDigits_specificDuplicate n` is the specialization to base 10:
`decimalDigits_specificDuplicate 123 = [1,2,3]`.
-/

/-- Decompose `n` into its list of digits in base `b`, most significant digit first.
Requires `hbase : 1 < b` (base must be at least 2). -/
def digitListBase (n b : Nat) (hbase : 1 < b) : List Nat :=
  if n < b then
    [n]
  else
    digitListBase (n / b) b hbase ++ [n % b]
termination_by n
decreasing_by
  have hpos : 0 < n := by omega
  exact Nat.div_lt_self hpos hbase

/-- Decompose `n` into its list of decimal digits (base 10), most significant digit first.
For example, `decimalDigits_specificDuplicate 123 = [1,2,3]`. -/
def decimalDigits_specificDuplicate (n : Nat) : List Nat :=
  if n < 10 then
    [n]
  else
    decimalDigits_specificDuplicate (n / 10) ++ [n % 10]
termination_by n
decreasing_by
  have hpos : 0 < n := by omega
  exact Nat.div_lt_self hpos (by omega)

/-! ### Decimal digit sum (simple recursion)

`sumOfDigits n` returns the sum of the decimal digits of `n`.
Unlike `digitSumBase` (base-parameterized, terminates at `n = 0`), this uses
base case `n < 10`, making it convenient for termination proofs in
digital-root-like recurrences.

For example, `sumOfDigits 1234 = 10` because `1 + 2 + 3 + 4 = 10`.
`sumOfDigits 0 = 0`, `sumOfDigits 5 = 5`.
-/

/-- Sum of decimal digits of `n`. Returns single-digit numbers as-is.
Uses base case `n < 10`, so `sumOfDigits n = n` for `n < 10`. -/
def sumOfDigits (n : Nat) : Nat :=
  if n < 10 then
    n
  else
    (n % 10) + sumOfDigits (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- For `n ≥ 10`, the sum of its decimal digits is strictly less than `n`.
This is the key decreasing lemma for termination of digital root and similar
repeated-digit-sum recursions. -/
lemma sumOfDigits_lt {n : Nat} (hn : 10 ≤ n) : sumOfDigits n < n := by
  induction' n using Nat.strong_induction_on with m ih
  unfold sumOfDigits
  have hm10 : ¬ m < 10 := by omega
  simp [hm10]
  have hsum_lt : sumOfDigits (m / 10) < 10 * (m / 10) := by
    by_cases hq : m / 10 < 10
    · unfold sumOfDigits; simp [hq]; omega
    · have hdiv_lt_m : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
      have h_ih := ih (m / 10) hdiv_lt_m (by omega)
      omega
  have h_eq := Nat.div_add_mod m 10
  omega

/-! ### Digital root

The digital root (also called the "repeated digital sum") of a non-negative
integer `n` is the single-digit value obtained by iteratively summing its
decimal digits until only one digit remains. It can be computed either
recursively (by this definition) or directly via the formula `n % 9` with
special case `n = 0 → 0`.
-/

/-- Digital root of `n` computed by repeatedly taking the decimal digit sum
until a single digit remains. For example, `digitRoot 1234 = 1`
(because `1+2+3+4 = 10`, then `1+0 = 1`). -/
def digitRoot (n : Nat) : Nat :=
  if h : n < 10 then
    n
  else
    digitRoot (sumOfDigits n)
termination_by n
decreasing_by
  exact sumOfDigits_lt (by omega)

/-! ### Maximum digit

`maxDigitBase n k hk` computes the maximum digit of `n` when written in base `k`
(requiring `1 < k`). For example, `maxDigitBase 2734 10 (by norm_num) = 7`.

`maxDigit_specificDuplicate n` is the base-10 specialization, equivalent to
`maxDigitBase n 10 (by norm_num)`. It uses base case `n < 10`, so
`maxDigit_specificDuplicate n = n` for `n < 10`.

These are used in problems that group elements by their maximum digit
(e.g., LeetCode 2815 "Max Pair Sum With Equal Max Digit"). -/

/-- Maximum digit of `n` in base `k`, where `1 < k`.
Uses base case `n < k` — when `n` is a single digit in base `k`, the max digit is `n` itself.
For each recursive step, compares `n % k` (least significant digit) with the max of `n / k`. -/
def maxDigitBase (n k : Nat) (hk : 1 < k) : Nat :=
  if hlt : n < k then n else
    let prev := maxDigitBase (n / k) k hk
    let d := n % k
    if d > prev then d else prev
termination_by n
decreasing_by
  have hpos : 0 < n := by
    have : k ≤ n := by omega
    omega
  exact Nat.div_lt_self hpos hk

/-- Maximum decimal digit of `n`. Equivalent to `maxDigitBase n 10 (by norm_num)`.
For example, `maxDigit_specificDuplicate 2734 = 7`. Like `sumOfDigits`, uses base case `n < 10`. -/
def maxDigit_specificDuplicate (n : Nat) : Nat :=
  if n < 10 then n else
    let prev := maxDigit_specificDuplicate (n / 10)
    let d := n % 10
    if d > prev then d else prev
termination_by n
decreasing_by
  have hpos : 0 < n := by omega
  exact Nat.div_lt_self hpos (by omega)

/-- `maxDigit_specificDuplicate n` in base 10 equals `maxDigitBase` specialized to `k = 10`. -/
theorem maxDigit_eq_maxDigitBase (n : Nat) :
    maxDigit_specificDuplicate n = maxDigitBase n 10 (by norm_num) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold maxDigit_specificDuplicate maxDigitBase
    by_cases hn : n < 10
    · simp [hn]
    · simp [hn]
      have h_div : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      rw [ih (n / 10) h_div]

/-- For any `n`, `maxDigit_specificDuplicate n < 10`. The maximum digit of a decimal number is always
a single digit. -/
lemma maxDigit_lt_10 (n : Nat) : maxDigit_specificDuplicate n < 10 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold maxDigit_specificDuplicate
    by_cases hn : n < 10
    · simp [hn]
    · simp [hn]
      have h_prev : maxDigit_specificDuplicate (n / 10) < 10 := ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
      have h_mod : n % 10 < 10 := Nat.mod_lt _ (by omega)
      by_cases hd : n % 10 > maxDigit_specificDuplicate (n / 10)
      · simp [hd]
        exact h_mod
      · simp [hd]
        exact h_prev

/-- For any `n` and base `k` with `1 < k`, `maxDigitBase n k hk < k`.
The maximum digit of `n` in base `k` is always a single digit in base `k`. -/
lemma maxDigitBase_lt (n k : Nat) (hk : 1 < k) : maxDigitBase n k hk < k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold maxDigitBase
    by_cases hn : n < k
    · simp [hn]
    · simp [hn]
      have hpos : 0 < n := by omega
      have h_prev : maxDigitBase (n / k) k hk < k :=
        ih (n / k) (Nat.div_lt_self hpos hk)
      by_cases hd : n % k > maxDigitBase (n / k) k hk
      · simp [hd]
        exact Nat.mod_lt _ (by omega)
      · simp [hd]
        exact h_prev

/-- The maximum digit of `n` is at most `n`, with equality when `n < 10`. -/
lemma maxDigit_le_n (n : Nat) : maxDigit_specificDuplicate n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold maxDigit_specificDuplicate
    by_cases hn : n < 10
    · simp [hn]
    · simp [hn]
      have hpos : 0 < n := by omega
      have h_prev : maxDigit_specificDuplicate (n / 10) ≤ n :=
        Nat.le_trans (ih (n / 10) (Nat.div_lt_self hpos (by decide))) (Nat.div_le_self n 10)
      have h_mod : n % 10 ≤ n :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt n (by decide : 0 < 10)) (by omega))
      by_cases hd : n % 10 > maxDigit_specificDuplicate (n / 10)
      · simp [hd]
        exact h_mod
      · simp [hd]
        exact h_prev

/-! ### Nonzero digit count in arbitrary base

`nonzeroDigitCountBase n k hk` counts how many nonzero digits appear in the
base-`k` representation of `n`. Unlike `digitCountBase` (which counts occurrences
of a *specific* digit), this counts *all* digits that are not zero.

For example, `nonzeroDigitCountBase 30507 10 (by norm_num) = 4` because the digits
are `3,0,5,0,7` and only the zeros are skipped.
`nonzeroDigitCountBase 0 k hk = 0` (the number zero has no digits in this convention).

`countNonzeroDigits n` is the base-10 specialization. -/

/-- Count of nonzero digits in the base-`k` representation of `n`, requiring `1 < k`.
Returns `0` for `n = 0`. -/
def nonzeroDigitCountBase (n k : Nat) (hk : 1 < k) : Nat :=
  if hzero : n = 0 then 0
  else nonzeroDigitCountBase (n / k) k hk + (if n % k = 0 then 0 else 1)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hk

/-- Count of nonzero decimal (base-10) digits of `n`.
Equivalent to `nonzeroDigitCountBase n 10 (by norm_num)`. -/
def countNonzeroDigits (n : Nat) : Nat := nonzeroDigitCountBase n 10 (by norm_num)

/-! ### Place value component decomposition

`placeValueComponents n k hk pos` decomposes `n` into its place-value components
in base `k`. Each component is `d * k ^ e` where `d` is a nonzero digit and `e`
is the exponent (starting from `pos` for the least significant digit, increasing as
we move to more significant positions). Zero digits are omitted from the output list.

For example, `placeValueComponents 123 10 (by norm_num) 0 = [100, 20, 3]`.

The `pos` parameter (usually `0`) is the exponent applied to the least significant
digit; for decomposing a tail of a larger number, pass a higher exponent. -/

/-- Decompose `n` into a list of `nonzeroDigit * k ^ exponent` values, most
significant first. Zero digits are omitted. The `pos` parameter is the exponent
for the least significant digit (typically `0`). -/
def placeValueComponents (n k : Nat) (hk : 1 < k) (pos : Nat) : List Nat :=
  if hzero : n = 0 then
    []
  else
    let rest := placeValueComponents (n / k) k hk (pos + 1)
    let digit := n % k
    if digit = 0 then
      rest
    else
      rest ++ [digit * k ^ pos]
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) hk

/-! ### Fold over non-zero decimal digits

`foldNonZeroDigits f init n` performs a right-fold over the non-zero decimal digits
of `n` (least significant to most significant), applying `f d` to the accumulator
for each non-zero digit `d`. Zero digits are skipped entirely.

This is a very general combinator: by choosing different `f` and `init`, you get:

* `sumNonZeroDigits n` — sum of non-zero digits
* `concatNonZeroDigits n` — concatenation of non-zero digits (removing zeros)
* `countNonzeroDigits n` — count of non-zero digits (already provided above)

The specialized forms `sumNonZeroDigits` and `concatNonZeroDigits` are provided
with their accumulator-based auxiliary definitions. The equivalence lemmas
`foldNonZeroDigits_sum_eq` and `foldNonZeroDigits_concat_eq` show that these
specialized forms are indeed instances of the general fold.
-/

/-- If `n ≠ 0`, then `n / 10 < n`. A base-10 analog of `div_two_lt_of_ne_zero`,
useful for termination proofs of decimal-digit recursions. -/
lemma div_ten_lt {n : Nat} (hn : n ≠ 0) : n / 10 < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- Right-fold over the non-zero decimal digits of a natural number,
from least significant digit to most significant. Skips zero digits.
For each non-zero digit `d`, applies `f d` to the accumulator.

For example, `foldNonZeroDigits (λ d a => a * 10 + d) 0 10203 = 123`. -/
def foldNonZeroDigits (f : Nat → α → α) (init : α) (n : Nat) : α :=
  if n = 0 then
    init
  else
    let d := n % 10
    if d = 0 then
      foldNonZeroDigits f init (n / 10)
    else
      foldNonZeroDigits f (f d init) (n / 10)
termination_by n
decreasing_by
  all_goals
    apply Nat.div_lt_self
    · omega
    · decide

/-- Tail-recursive sum of non-zero decimal digits. `sumNonZeroDigitsAux m acc`
processes `m` digit by digit, adding each non-zero digit `d` to `acc`. -/
def sumNonZeroDigitsAux (m acc : Nat) : Nat :=
  if m = 0 then
    acc
  else
    let d := m % 10
    if d = 0 then
      sumNonZeroDigitsAux (m / 10) acc
    else
      sumNonZeroDigitsAux (m / 10) (acc + d)
termination_by m
decreasing_by
  all_goals
    apply Nat.div_lt_self
    · omega
    · decide

/-- Sum of non-zero decimal digits of `n`.
For example, `sumNonZeroDigits 10203 = 6` (1 + 2 + 3 = 6). -/
def sumNonZeroDigits (n : Nat) : Nat :=
  sumNonZeroDigitsAux n 0

/-- Tail-recursive concatenation of non-zero decimal digits.
`concatNonZeroDigitsAux m place acc` processes `m` digit by digit, building the
result in `acc`. `place` tracks the current position multiplier (1, 10, 100, …).
Zero digits are skipped; non-zero digits are multiplied by `place` and added to `acc`. -/
def concatNonZeroDigitsAux (m place acc : Nat) : Nat :=
  if m = 0 then
    acc
  else
    let d := m % 10
    if d = 0 then
      concatNonZeroDigitsAux (m / 10) place acc
    else
      concatNonZeroDigitsAux (m / 10) (place * 10) (acc + d * place)
termination_by m
decreasing_by
  all_goals
    apply Nat.div_lt_self
    · omega
    · decide

/-- Concatenate the **non-zero** decimal digits of `n` in their original order,
removing all zero digits. For example, `concatNonZeroDigits 10203 = 123`. -/
def concatNonZeroDigits (n : Nat) : Nat :=
  concatNonZeroDigitsAux n 1 0

/-- `foldNonZeroDigits` with `(λ d a => a + d)` (sum mode) equals
`sumNonZeroDigitsAux`. This shows that `sumNonZeroDigitsAux` is an instance
of the general fold combinator. -/
lemma foldNonZeroDigits_sum_eq (m acc : Nat) :
    foldNonZeroDigits (λ d a => a + d) acc m = sumNonZeroDigitsAux m acc := by
  revert acc
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro acc
    unfold foldNonZeroDigits sumNonZeroDigitsAux
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm]
      by_cases h0 : m % 10 = 0
      · simp [h0]
        exact ih (m / 10) (div_ten_lt hm) acc
      · simp [h0]
        exact ih (m / 10) (div_ten_lt hm) (acc + m % 10)

/-- `foldNonZeroDigits` with a pair accumulator (concatenation mode) equals
`concatNonZeroDigitsAux`. This shows that `concatNonZeroDigitsAux` is an instance
of the general fold combinator. -/
lemma foldNonZeroDigits_concat_eq (m place acc : Nat) :
    (foldNonZeroDigits (λ d (p, a) => (p * 10, a + d * p)) (place, acc) m).2 =
    concatNonZeroDigitsAux m place acc := by
  revert place acc
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro place acc
    unfold foldNonZeroDigits concatNonZeroDigitsAux
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm]
      by_cases h0 : m % 10 = 0
      · simp [h0]
        exact ih (m / 10) (div_ten_lt hm) place acc
      · simp [h0]
        exact ih (m / 10) (div_ten_lt hm) (place * 10) (acc + (m % 10) * place)

end Nat
