import Mathlib

namespace Nat

/-- The standard prime modulus `10^9 + 7` (1,000,000,007) used throughout competitive
programming and LeetCode problems. This is a prime number commonly chosen because
it is large enough to avoid overflow in languages with 32-bit integers while still
being prime, making modular inverses well-defined. -/
def primeMod : Nat := 1000000007

/-- `primeMod = 10^9 + 7` is positive: `0 < primeMod`.
This is essential for using `Nat.mod_lt` and other division lemmas
that require a positive modulus. -/
lemma primeMod_pos : 0 < primeMod := by
  unfold primeMod; decide

/-- Ceiling division of natural numbers: `ceilDiv_specificDuplicate num den = ⌈num / den⌉`.
Uses the standard formula `(num + den - 1) / den` which is correct for all `num : ℕ`
when `den > 0`. This is commonly used in competitive programming to compute how many
"strikes" or "rounds" are needed when each round subtracts `den` from `num`.
Note: `ceilDiv_specificDuplicate 0 den = 0` for any `den` (including `den = 0` where it degenerates to `0`).
-/
def ceilDiv_specificDuplicate (num den : Nat) : Nat :=
  (num + den - 1) / den

/-! ### CeilDiv theorems -/

/-! ### Parity and modular arithmetic lemmas -/

/-- If `n` is odd (`n % 2 = 1`), then `(n * k) % 2 = k % 2`.
This is because `n ≡ 1 mod 2`, so `n * k ≡ 1 * k ≡ k mod 2`.
Useful for reasoning about the parity of products when one factor is odd. -/
lemma odd_mul_mod_two {n k : Nat} (hn_odd : n % 2 = 1) : (n * k) % 2 = k % 2 := by
  calc
    (n * k) % 2 = ((n % 2) * (k % 2)) % 2 := by rw [Nat.mul_mod]
    _ = (1 * (k % 2)) % 2 := by rw [hn_odd]
    _ = (k % 2) % 2 := by simp
    _ = k % 2 := Nat.mod_mod _ _

/-- `d * ceilDiv_specificDuplicate a d ≥ a` when `d > 0`. This is the fundamental property of ceiling
division: the ceiling-division result times the divisor is at least the numerator. -/
lemma ceilDiv_mul_ge (a d : Nat) (hd : 0 < d) : d * ceilDiv_specificDuplicate a d ≥ a := by
  unfold ceilDiv_specificDuplicate
  have hpos : 1 ≤ a + d := by
    have : 1 ≤ d := by omega
    omega
  have hsub_add : (a + d - 1) + 1 = a + d := Nat.sub_add_cancel hpos
  have hineq : (a + d - 1) + 1 ≤ d * (((a + d - 1) / d) + 1) := by
    have h := Nat.lt_mul_div_succ (a + d - 1) hd
    omega
  rw [hsub_add] at hineq
  have hmul : d * (((a + d - 1) / d) + 1) = d * ((a + d - 1) / d) + d := by ring
  rw [hmul] at hineq
  exact Nat.le_of_add_le_add_right hineq

/-- If `d * k ≥ a` with `d > 0`, then `ceilDiv_specificDuplicate a d ≤ k`. This is the converse direction:
any upper bound on the product gives an upper bound on the ceiling division. -/
lemma ceilDiv_le_of_mul_ge (a d k : Nat) (hd : 0 < d) (h : d * k ≥ a) : ceilDiv_specificDuplicate a d ≤ k := by
  unfold ceilDiv_specificDuplicate
  by_contra! hc
  have h_not_lt : ¬ ((a + d - 1) / d < k + 1) := by
    intro hlt
    have : (a + d - 1) / d ≤ k := by omega
    omega
  rw [Nat.div_lt_iff_lt_mul hd (x := a + d - 1) (y := k + 1)] at h_not_lt
  have hge : (k + 1) * d ≤ a + d - 1 := by omega
  have hmul_eq : (k + 1) * d = k * d + d := by ring
  rw [hmul_eq] at hge
  have hsum_pos : 0 < a + d := by omega
  have h_lt : a + d - 1 < a + d := Nat.sub_lt hsum_pos (by omega)
  rw [Nat.mul_comm d k] at h
  have hsum : k * d + d ≥ a + d := add_le_add_right h d
  have h_contra : k * d + d < a + d := lt_of_le_of_lt hge h_lt
  have h_not : ¬ (k * d + d < a + d) := not_lt.mpr hsum
  exact h_not h_contra

/-- If `1 ≤ a ≤ d` and `d > 0`, then `ceilDiv_specificDuplicate a d = 1`. This captures the useful special
case where the numerator is between 1 and the denominator (inclusive). -/
lemma ceilDiv_eq_one_of_le (a d : Nat) (ha : 1 ≤ a) (had : a ≤ d) (hd : 0 < d) : ceilDiv_specificDuplicate a d = 1 := by
  unfold ceilDiv_specificDuplicate
  apply Nat.div_eq_of_lt_le
  · have : a + d ≥ d + 1 := by omega
    omega
  · have : a + d - 1 < d + d := by omega
    omega

/-- Minimum of three natural numbers: `min3_specificDuplicate a b c = min (min a b) c`. -/
def min3_specificDuplicate (a b c : Nat) : Nat := min (min a b) c

/-- Expresses `min` as an `if`-then-else on the reversed comparison `y < x`.
This is useful for converting between `min`-based code and explicit `if` expressions
that appear in competitive programming solutions (e.g., when `scanMin` is matched
against a spec that uses `if cur < prev then cur else prev`). -/
lemma min_eq_if_lt [LinearOrder α] (x y : α) : min x y = if y < x then y else x := by
  by_cases h : y < x
  · simp [min_eq_right (le_of_lt h), h]
  · have hle : x ≤ y := not_lt.mp h
    simp [min_eq_left hle, h]

/-- Expresses `min` as an `if`-then-else on the natural comparison `a < b`.
This is the direct analogue of `max_eq_if` for `min`: `min a b = if a < b then a else b`.
While `min_eq_if_lt` uses the reversed comparison `y < x`, this lemma uses the
natural order `a < b`, making it easier to rewrite `min` to `if` in many contexts. -/
lemma min_eq_if [LinearOrder α] (a b : α) : min a b = if a < b then a else b := by
  by_cases h : a < b
  · simp [h, min_eq_left (le_of_lt h)]
  · have hle : b ≤ a := not_lt.mp h
    simp [h, min_eq_right hle]

/-- Expresses `max` as an `if`-then-else on `a ≥ b`.
This is the dual of `min_eq_if_lt`: while `min` uses `y < x` for the condition,
`max` uses `a ≥ b`. Useful for converting between `max`-based code and explicit `if`
expressions, and for rewriting `max` to `if` in postcondition proofs. -/
lemma max_eq_if [LinearOrder α] (a b : α) : max a b = if a ≥ b then a else b := by
  by_cases h : a ≥ b
  · rw [max_eq_left h, if_pos h]
  · rw [max_eq_right (le_of_not_ge h), if_neg h]

/-! ### Division/decreasing lemmas -/

/-- For nonzero `n`, `n / 2 < n`. This specializes `Nat.div_lt_self` to divisor 2,
providing a convenient termination lemma for divide-by-2 recursions.
Unlike a version requiring `1 < n`, this needs only `n ≠ 0`, so it works for `n = 1` as well. -/
lemma div_two_lt_of_ne_zero {n : Nat} (h : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- `m - (op + 1) < m - op` when `op < m`. A decreasing lemma useful for
termination proofs when the measure is `m - op` and `op` increments by 1.
For example, `m - (op + 1) < m - op` shows the recursive argument shrinks. -/
lemma sub_succ_lt_sub_of_lt_specificDuplicate {op m : Nat} (h : op < m) : m - (op + 1) < m - op := by
  omega

/-- `(a + 1) - (b + 1) < (a + 1) - b` when `b ≤ a`. A decreasing lemma for
termination proofs where the measure is `(a + 1) - b` and `b` increments by 1.
This is the `succ`-shifted variant of `sub_succ_lt_sub_of_lt_specificDuplicate`: applying that lemma
with `op := b`, `m := a+1` and `h : b < a+1` (which follows from `b ≤ a`). -/
lemma succ_sub_succ_lt_succ_sub_of_le {a b : Nat} (h : b ≤ a) : (a + 1) - (b + 1) < (a + 1) - b :=
  sub_succ_lt_sub_of_lt_specificDuplicate (Nat.lt_succ_of_le h)

/-- `n - 1 < n` when `1 < n`. A common decreasing lemma for termination proofs
in recursive functions that decrement by 1. This is a specialized form of
`Nat.sub_lt` for the case where the subtracted amount is 1. -/
lemma sub_one_lt_of_one_lt {n : Nat} (h : 1 < n) : n - 1 < n := by
  omega

/-- When `0 < b` and `b ≤ a`, we have `(a - b) + b < a + b`. This is a decreasing lemma
for termination proofs of functions that recurse by subtracting the smaller from the larger
(e.g., the subtractive Euclidean algorithm). The basis of the proof is
`Nat.sub_add_cancel hle` which gives `(a - b) + b = a`. -/
lemma sub_add_lt_add_of_pos {a b : Nat} (hb_pos : 0 < b) (hle : b ≤ a) : (a - b) + b < a + b := by
  have h_eq : (a - b) + b = a := Nat.sub_add_cancel hle
  omega

/-- When `0 < a` and `a ≤ b`, we have `a + (b - a) < a + b`. This is a decreasing lemma
for termination proofs of functions that recurse by subtracting the smaller from the larger
(the dual of `sub_add_lt_add_of_pos` for the symmetric branch).
The basis of the proof is `Nat.add_sub_cancel' hle` which gives `a + (b - a) = b`. -/
lemma add_sub_lt_add_of_pos {a b : Nat} (ha_pos : 0 < a) (hle : a ≤ b) : a + (b - a) < a + b := by
  have h_eq : a + (b - a) = b := Nat.add_sub_cancel' hle
  omega

/-! ### Decimal digit reversal

These functions reverse the decimal digits of a natural number, returning `-1`
as a sentinel if the reversed value exceeds a given bound at any intermediate step.
This is the core operation behind LeetCode's "Reverse Integer" problem (LC 7),
where the bound is `2147483647 = 2^31 - 1` (the 32-bit signed integer max).

Generalized from `bounded_reverse_aux` and `bounded_reverse` (LC 3783). -/

/-- Tail-recursive helper for `decimalReverse`: accumulates the reversed decimal digits
of `x` into `acc`, checking that no intermediate value exceeds `bound`.
Returns `-1 : Int` on overflow, otherwise the fully reversed number as `Int`. -/
def decimalReverseAux (bound : Nat) (x acc : Nat) : Int :=
  if x = 0 then
    (acc : Int)
  else
    let next := acc * 10 + x % 10
    if next > bound then
      -1
    else
      decimalReverseAux bound (x / 10) next
termination_by x

/-- Reverses the decimal digits of `x`, returning `-1 : Int` if the reversed value
exceeds `bound`. Equivalent to `decimalReverseAux bound x 0`. -/
def decimalReverse (bound : Nat) (x : Nat) : Int :=
  decimalReverseAux bound x 0

/-- Specialization of `decimalReverse` for the standard 32-bit signed integer bound
`2^31 - 1 = 2147483647`, commonly used in LeetCode problems. -/
def reverseDecimal32 (x : Nat) : Int :=
  decimalReverse 2147483647 x

/-- Specialization of `decimalReverseAux` for the standard 32-bit signed integer bound.
Useful as a reference specification for verified implementations. -/
def reverseDecimal32Aux (x acc : Nat) : Int :=
  decimalReverseAux 2147483647 x acc

/-! ### Nat-valued decimal digit reversal

These are the `Nat`-valued counterparts of `decimalReverseAux` and `decimalReverse`.
Instead of returning `-1 : Int` on overflow, the `Nat` versions return `0` as the
overflow sentinel. This is useful when working entirely within `Nat` (e.g., u32
overflow scenarios where the sentinel value is `0`). -/

/-- Tail-recursive helper for `decimalReverseNat`: reverses the decimal digits of `x`
into `acc`, checking that no intermediate value exceeds `bound`. Returns `0` on overflow
(instead of `-1 : Int` as in `decimalReverseAux`), otherwise the fully reversed `Nat`. -/
def decimalReverseAuxNat (bound : Nat) (x acc : Nat) : Nat :=
  if x = 0 then
    acc
  else
    let next := acc * 10 + x % 10
    if next > bound then
      0
    else
      decimalReverseAuxNat bound (x / 10) next
termination_by x

/-- Reverses the decimal digits of `x`, returning `0` if the reversed value exceeds `bound`.
This is the `Nat`-valued counterpart of `decimalReverse`. -/
def decimalReverseNat (bound : Nat) (x : Nat) : Nat :=
  decimalReverseAuxNat bound x 0

/-- Count the number of decimal digits of `n` that satisfy the predicate `p`.
For example, `countDigits (λ d => d = 4 ∨ d = 7) 447` returns `3`. -/
def countDigits (p : Nat → Bool) (n : Nat) : Nat :=
  if h : n = 0 then
    0
  else
    let d := n % 10
    let prev := countDigits p (n / 10)
    if p d then prev + 1 else prev
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

/-- Count the number of indices `i < n` where `p i` is `false`.
`countFalseUpTo p n = |{i < n | ¬ p i}|`.
Useful for counting elements that fail to satisfy a predicate over a prefix,
e.g., "how many rows are clean (no strawberry)" in CF 330A. -/
def countFalseUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let rest := countFalseUpTo p k
      if p k then rest else rest + 1

/-- `countFalseUpTo p k ≤ k` — the count of false indices never exceeds the total number
of indices. -/
lemma countFalseUpTo_le (p : Nat → Bool) (k : Nat) : countFalseUpTo p k ≤ k := by
  induction k with
  | zero => simp [countFalseUpTo]
  | succ k ih =>
      unfold countFalseUpTo
      split
      · exact Nat.le_trans ih (Nat.le_succ k)
      · exact Nat.succ_le_succ ih

/-- Count the number of indices `i < n` where `p i` is `true`.
`countTrueUpTo p n = |{i < n | p i}|`.
This is the dual of `countFalseUpTo`:
`countTrueUpTo p k + countFalseUpTo p k = k`. -/
def countTrueUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => countTrueUpTo p k + (if p k then 1 else 0)

/-- Recursive step for `countTrueUpTo`: unfolds the definition at `k+1`. -/
lemma countTrueUpTo_succ (p : Nat → Bool) (k : Nat) :
    countTrueUpTo p (k + 1) = countTrueUpTo p k + (if p k then 1 else 0) := rfl

/-- `countTrueUpTo p k ≤ countTrueUpTo p (k+1)` — the count is monotone. -/
lemma countTrueUpTo_le_succ (p : Nat → Bool) (k : Nat) :
    countTrueUpTo p k ≤ countTrueUpTo p (k + 1) := by
  rw [countTrueUpTo_succ]
  omega

/-- Count the number of natural numbers `n` in `[low, high]` (inclusive) for which
`p n` is true. For example, `countSatisfying_specificDuplicate 2 5 (λ n => n % 2 = 0) = 2` (for `n = 2, 4`).

When `low = 0`, this equals `countTrueUpTo p (high+1)`. When `high < low`, returns `0`.
Generalized from `count_satisfying` (LeetCode 2843). -/
def countSatisfying_specificDuplicate (low high : Nat) (p : Nat → Bool) : Nat :=
  if high < low then
    0
  else if hz : high = 0 then
    (if p 0 then 1 else 0)
  else
    countSatisfying_specificDuplicate low (high - 1) p + (if p high then 1 else 0)
termination_by high
decreasing_by
  simp_wf
  exact Nat.pos_of_ne_zero hz

/-- Count the number of natural numbers `k` in `[left, n]` (inclusive) for which
`p k` is true. Unlike `countSatisfying_specificDuplicate`, which recurses decreasing on `high`, this version
recurses increasing on `n`, making it convenient for forward-induction proofs.

`countSatisfyingPred p left 0 = 0`, and for `n = curr'+1`:
if `left > curr'+1`, returns `0` (bound not yet reached); otherwise adds `1` if `p (curr'+1)`
is true to the count of the previous step.

Generalized from `count_satisfying_pred` (LeetCode 762). -/
def countSatisfyingPred (p : Nat → Bool) (left : Nat) : Nat → Nat
  | 0 => 0
  | curr' + 1 =>
    if left > curr' + 1 then
      0
    else
      countSatisfyingPred p left curr' + (if p (curr' + 1) then 1 else 0)

/-- When `left > n`, the interval `[left, n]` is empty, so `countSatisfyingPred` returns `0`. -/
lemma countSatisfyingPred_of_gt {p : Nat → Bool} {left n : ℕ} (h : left > n) :
    countSatisfyingPred p left n = 0 := by
  induction' n with m ih
  · rfl
  · conv => lhs; unfold countSatisfyingPred
    rw [if_pos h]

/-- Forward-step recurrence: when `left ≤ n + 1`, the count up to `n+1` equals
the count up to `n` plus `1` if `p (n+1)` is true, `0` otherwise. -/
lemma countSatisfyingPred_succ_of_le {p : Nat → Bool} {left n : ℕ} (h : left ≤ n + 1) :
    countSatisfyingPred p left (n + 1) = countSatisfyingPred p left n + (if p (n + 1) then 1 else 0) := by
  have h_not_gt : ¬ left > n + 1 := by omega
  conv => lhs; unfold countSatisfyingPred
  rw [if_neg h_not_gt]

/-! ### Counting value occurrences in a sequence prefix

`countValInPrefix a v n` counts how many times the value `v` appears among
`a 0, a 1, …, a (n-1)`. Returns an `Int` for compatibility with integer arithmetic.

Unlike `countTrueUpTo`, which uses a `Bool` predicate, this directly tests equality
of each term in the sequence against a target value. This is the sequence-indexed
analog of `List.countPz` that operates on a `Nat → α` function rather than a `List α`.
-/

/-- Count occurrences of value `v` in the first `n` terms of sequence `a`.
`countValInPrefix a v n = |{i < n | a i = v}|`, as an `Int`. -/
def countValInPrefix {α : Type} [DecidableEq α] (a : Nat → α) (v : α) (n : Nat) : Int :=
  match n with
  | 0 => 0
  | k + 1 =>
    let prev := countValInPrefix a v k
    if a k = v then prev + 1 else prev
termination_by n

/-! ### 1-indexed predicate counting

`countPred_specificDuplicate p n` counts how many `m` with `1 ≤ m ≤ n` satisfy `p m = true`.
This is a 1-indexed variant of `countTrueUpTo`:
`countPred_specificDuplicate p n = countTrueUpTo (λ i => p (i+1)) n`.
-/

/-- Count of natural numbers `m` where `1 ≤ m ≤ n` and `p m` holds. -/
def countPred_specificDuplicate (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i+1 => countPred_specificDuplicate p i + (if p (i+1) then 1 else 0)

/-- Recursive step for `countPred_specificDuplicate`: unfolding at `i+1`. -/
lemma countPred_succ_specificDuplicate (p : Nat → Bool) (i : Nat) :
    countPred_specificDuplicate p (i+1) = countPred_specificDuplicate p i + (if p (i+1) then 1 else 0) := rfl

/-- For `i > 0`, `countPred_specificDuplicate p i = countPred_specificDuplicate p (i-1) + (if p i then 1 else 0)`.
This provides a backward-step formulation. -/
lemma countPred_step (p : Nat → Bool) (i : Nat) (hpos : i > 0) :
    countPred_specificDuplicate p i = countPred_specificDuplicate p (i-1) + (if p i then 1 else 0) := by
  cases i
  · omega
  · rename_i j
    have : (j+1 : Nat) - 1 = j := by omega
    rw [this, countPred_succ_specificDuplicate]

/-- `countPred_specificDuplicate` is monotone: if `a ≤ b`, then `countPred_specificDuplicate p a ≤ countPred_specificDuplicate p b`. -/
lemma countPred_monotone (p : Nat → Bool) {a b : Nat} (h : a ≤ b) :
    countPred_specificDuplicate p a ≤ countPred_specificDuplicate p b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
      rw [countPred_succ_specificDuplicate p _]
      omega

/-- Relationship between 0-indexed `countTrueUpTo` and 1-indexed `countPred_specificDuplicate`:
`countPred_specificDuplicate p n = countTrueUpTo (λ i => p (i+1)) n`. -/
lemma countPred_eq_countTrueUpTo_shift (p : Nat → Bool) (n : Nat) :
    countPred_specificDuplicate p n = countTrueUpTo (λ i => p (i+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countPred_succ_specificDuplicate, countTrueUpTo_succ, ih]

/-! ### `countDown` — tail-recursive predicate counting with accumulator

`countDown pred k acc` counts how many numbers in `{1, …, k}` satisfy `pred`,
descending from `k` to `1`, while accumulating into `acc`. This is a tail-recursive
formulation of `countPred_specificDuplicate pred k + acc`. The descending order makes it convenient for
proofs and code that processes indices from `k` downwards, complementing the
upward-recursing `countPred_specificDuplicate`.

Generalized from `countDesc` (LeetCode 829). -/

/-- Tail-recursive accumulator-based count: `countDown pred k acc` counts how many
of `1, 2, …, k` satisfy `pred`, starting from `k` and descending to `1`, adding
each result into `acc`. Equivalent to `countPred_specificDuplicate pred k + acc`. -/
def countDown (pred : Nat → Bool) (k acc : Nat) : Nat :=
  match k with
  | 0 => acc
  | k'+1 => countDown pred k' (acc + (if pred k then 1 else 0))

@[simp] lemma countDown_zero (pred : Nat → Bool) (acc : Nat) : countDown pred 0 acc = acc := rfl

lemma countDown_succ (pred : Nat → Bool) (k acc : Nat) :
    countDown pred (k+1) acc = countDown pred k (acc + (if pred (k+1) then 1 else 0)) := rfl

/-- Accumulator separation lemma: the accumulator can be factored out as addition.
`countDown pred k acc = countDown pred k 0 + acc`. -/
lemma countDown_add (pred : Nat → Bool) (k acc : Nat) :
    countDown pred k acc = countDown pred k 0 + acc := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    simp [countDown, countDown_succ]
    rw [ih (acc + (if pred (k+1) then 1 else 0)), ih ((if pred (k+1) then 1 else 0))]
    omega

/-- `countDown` is equivalent to `countPred_specificDuplicate` shifted by the accumulator:
`countDown pred k acc = countPred_specificDuplicate pred k + acc`. -/
lemma countDown_eq_countPred_add (pred : Nat → Bool) (k acc : Nat) :
    countDown pred k acc = countPred_specificDuplicate pred k + acc := by
  induction k generalizing acc with
  | zero => simp [countPred_specificDuplicate]
  | succ k ih =>
    rw [countDown_succ, countPred_succ_specificDuplicate]
    rw [ih (acc + (if pred (k+1) then 1 else 0))]
    omega

/-! ### `countWhere_specificDuplicate` — Prop-based predicate counting

`countWhere_specificDuplicate p n` counts how many `k` with `1 ≤ k ≤ n` satisfy the `Prop` predicate `p`.
This is the `Prop`-based variant of `countPred_specificDuplicate` (which uses `Bool`).
The `Decidable` typeclass instance makes it computable while keeping the flexibility
of using `Prop` predicates directly (e.g., `countWhere_specificDuplicate (λ k => d ∣ k) n`). -/

/-- Count numbers `k` from 1 to `n` (inclusive) that satisfy predicate `p : Nat → Prop`.
`countWhere_specificDuplicate p n = |{k | 1 ≤ k ≤ n ∧ p k}|`. -/
def countWhere_specificDuplicate (p : Nat → Prop) [∀ k, Decidable (p k)] : Nat → Nat
  | 0 => 0
  | n+1 => (if p (n+1) then 1 else 0) + countWhere_specificDuplicate p n

@[simp]
theorem countWhere_succ (p : Nat → Prop) [∀ k, Decidable (p k)] (n : Nat) :
    countWhere_specificDuplicate p (n+1) = (if p (n+1) then 1 else 0) + countWhere_specificDuplicate p n := rfl

/-! ### `countUpTo_specificDuplicate` — 0-indexed predicate counting returning `Int`

`countUpTo_specificDuplicate p n` counts how many `k` with `0 ≤ k < n` satisfy `p k`.
Returns `0` for `n = 0`. Unlike `countWhere_specificDuplicate` (which is 1-indexed and returns `ℕ`),
`countUpTo_specificDuplicate` uses 0-indexed logic and returns `Int`, making it convenient for
competitive-programming problems where the count is used in `Int` arithmetic.

Formally: `countUpTo_specificDuplicate p n = |{k | 0 ≤ k < n ∧ p k}|` (as `Int`). -/

/-- Count how many `k` with `0 ≤ k < n` satisfy `p k`. Returns `Int`.
`countUpTo_specificDuplicate p 0 = 0`, `countUpTo_specificDuplicate p (n+1) = countUpTo_specificDuplicate p n + (if p n then 1 else 0)`. -/
def countUpTo_specificDuplicate (p : Nat → Prop) [DecidablePred p] : Nat → Int
  | 0 => 0
  | n+1 => countUpTo_specificDuplicate p n + (if p n then 1 else 0)

/-- Characterization lemma: if a function `f : Nat → Int` satisfies the recurrence
`f 0 = 0` and `f (n+1) = f n + (if p n then 1 else 0)`, then `f` equals `countUpTo_specificDuplicate p`.
This is the uniqueness principle: any function obeying the same step relation as
`countUpTo_specificDuplicate` must be equal to it. Useful for proving equivalence of different
implementations of the same counting logic. -/
lemma countUpTo_eq_of_step {p : Nat → Prop} [DecidablePred p] {f : Nat → Int}
    (h0 : f 0 = 0)
    (hstep : ∀ n, f (n + 1) = f n + (if p n then 1 else 0)) :
    ∀ n, f n = countUpTo_specificDuplicate p n := by
  intro n
  induction n with
  | zero =>
      simpa [countUpTo_specificDuplicate] using h0
  | succ n ih =>
      rw [hstep n, ih]
      simp [countUpTo_specificDuplicate]

/-! ### Divisor counting

`countDivisorsUpTo n k` counts how many divisors `n` has in `{1, ..., k}`.
This is a specialization of `countPred_specificDuplicate` to the divisibility predicate `λ d => n % d = 0`,
useful in problems where you need to count divisors up to a bound (e.g., "count numbers
with exactly 3 divisors", "count numbers with exactly 4 divisors"). -/

/-- Count how many divisors `n` has in `{1, ..., k}`.
`countDivisorsUpTo n k = |{d | 1 ≤ d ≤ k ∧ d ∣ n}|`. -/
def countDivisorsUpTo (n : Nat) (k : Nat) : Nat :=
  countPred_specificDuplicate (λ d => n % d = 0) k

@[simp] lemma countDivisorsUpTo_zero (n : Nat) : countDivisorsUpTo n 0 = 0 := rfl

/-- Recursive step for `countDivisorsUpTo`:
`countDivisorsUpTo n (k+1) = countDivisorsUpTo n k + (if n % (k+1) = 0 then 1 else 0)`. -/
lemma countDivisorsUpTo_succ (n k : Nat) :
    countDivisorsUpTo n (k+1) = countDivisorsUpTo n k + (if n % (k+1) = 0 then 1 else 0) := by
  simp [countDivisorsUpTo, countPred_succ_specificDuplicate]

/-- Exclusive prefix sum over natural numbers:
`prefixSum_specificDuplicate term n = ∑_{i=0}^{n-1} term i`.
`prefixSum_specificDuplicate term 0 = 0`. -/
def prefixSum_specificDuplicate {α : Type _} [AddMonoid α] (term : Nat → α) : Nat → α
  | 0 => 0
  | i + 1 => prefixSum_specificDuplicate term i + term i

@[simp] lemma prefixSum_zero {α : Type _} [AddMonoid α] (f : Nat → α) : prefixSum_specificDuplicate f 0 = 0 := rfl

lemma prefixSum_succ {α : Type _} [AddMonoid α] (f : Nat → α) (n : Nat) :
    prefixSum_specificDuplicate f (n + 1) = prefixSum_specificDuplicate f n + f n := rfl

/-- Sum `f` over indices `j` with `start ≤ j < stop`.
Returns `0` if `stop ≤ start`. Generalized from `sum_over_indices` in LeetCode 42
("Trapping Rain Water") to any `AddMonoid` target type. -/
def sumRange_specificDuplicate {α : Type _} [AddMonoid α] (f : Nat → α) (start stop : Nat) : α :=
  if stop ≤ start then 0 else f start + sumRange_specificDuplicate f (start + 1) stop
termination_by stop - start

/-- Inclusive prefix sum over natural numbers:
`inclusivePrefixSum term n = ∑_{i=0}^{n} term i`.
Differs from `prefixSum_specificDuplicate` in that the final term `term n` is included. -/
def inclusivePrefixSum {α : Type _} [AddMonoid α] (term : Nat → α) : Nat → α
  | 0 => term 0
  | i + 1 => inclusivePrefixSum term i + term (i + 1)

/-- Inclusive prefix minimum scan over natural numbers: `scanMin f n = min_{i=0}^{n} f i`.
That is, the minimum of `f 0`, `f 1`, …, `f n`.
`scanMin f 0 = f 0`; `scanMin f (n+1) = min (scanMin f n) (f (n+1))`.
This is the `min` analog of `inclusivePrefixSum`. -/
def scanMin {α : Type _} [LinearOrder α] (f : Nat → α) : Nat → α
  | 0 => f 0
  | n + 1 => min (scanMin f n) (f (n + 1))

/-- Inclusive prefix maximum scan over natural numbers: `scanMax f n = max_{i=0}^{n} f i`.
That is, the maximum of `f 0`, `f 1`, …, `f n`.
`scanMax f 0 = f 0`; `scanMax f (n+1) = max (f (n+1)) (scanMax f n)`.
This is the `max` analog of `scanMin`. -/
def scanMax {α : Type _} [LinearOrder α] (f : Nat → α) : Nat → α
  | 0 => f 0
  | n + 1 => max (f (n + 1)) (scanMax f n)

/-- If every value `f i` for `i ≤ hi` is bounded above by `bound`, then
`scanMax f hi` is also bounded above by `bound`. -/
lemma scanMax_le_of_forall_le {α : Type _} [LinearOrder α] (f : Nat → α) (bound : α) {hi : Nat}
    (hf : ∀ i, i ≤ hi → f i ≤ bound) : scanMax f hi ≤ bound := by
  induction hi with
  | zero =>
      simpa [scanMax] using hf 0 (by omega)
  | succ hi ih =>
      simp [scanMax]
      constructor
      · exact hf (hi + 1) (by omega)
      · exact ih (fun i hi_i => hf i (by omega))

/-- For any `i ≤ hi`, `f i` is bounded above by the prefix max `scanMax f hi`. -/
lemma le_scanMax_of_le {α : Type _} [LinearOrder α] (f : Nat → α) {i hi : Nat} (h : i ≤ hi) :
    f i ≤ scanMax f hi := by
  induction hi generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      simp [scanMax]
  | succ hi ih =>
      by_cases hlast : i = hi + 1
      · subst i
        simp [scanMax, le_max_left]
      · have hle : i ≤ hi := by omega
        exact le_trans (ih hle) (by simp [scanMax, le_max_right])

/-! ### `foldMin` — exclusive prefix minimum with sentinel

`foldMin f sentinel n` computes `min(sentinel, f 0, f 1, …, f (n-1))`.
Unlike `scanMin` (which is inclusive and uses `f 0` as the base), `foldMin`
allows an explicit sentinel that signifies "no valid value found". This is
common in competitive programming where a sentinel like `list.length + 1`
indicates an impossible result.

Generalized from `min_len_prefix` (LeetCode 3095, 3360). -/

/-- Fold `min` over `f 0, …, f (n-1)` with an initial sentinel.
`foldMin f sentinel n = min(sentinel, min_{i < n} f i)`. -/
def foldMin {α : Type _} [LinearOrder α] (f : Nat → α) (sentinel : α) : Nat → α
  | 0 => sentinel
  | n+1 => min (foldMin f sentinel n) (f n)

@[simp] theorem foldMin_zero {α : Type _} [LinearOrder α] (f : Nat → α) (sentinel : α) :
    foldMin f sentinel 0 = sentinel := rfl

theorem foldMin_succ {α : Type _} [LinearOrder α] (f : Nat → α) (sentinel : α) (n : Nat) :
    foldMin f sentinel (n+1) = min (foldMin f sentinel n) (f n) := rfl

/-- `foldMin f sentinel n ≤ sentinel` — the fold never exceeds the initial sentinel.
This follows because `min a b ≤ a` at each step. -/
theorem foldMin_le_sentinel {α : Type _} [LinearOrder α] (f : Nat → α) (sentinel : α) (n : Nat) :
    foldMin f sentinel n ≤ sentinel := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldMin_succ]
    exact le_trans (min_le_left _ _) ih

/-- For any `i < n`, the fold is ≤ `f i` — `foldMin` is a lower bound for all
values in the range. -/
theorem foldMin_le_of_lt {α : Type _} [LinearOrder α] (f : Nat → α) (sentinel : α)
    {i n : Nat} (h : i < n) : foldMin f sentinel n ≤ f i := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rw [foldMin_succ]
    by_cases hi : i = n
    · subst i; exact min_le_right _ _
    · have hi_lt_n : i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hi
      exact le_trans (min_le_left _ _) (ih hi_lt_n)

/-- Maximum of `f i` for `i` in `{1, …, n}`. Returns `0` when `n = 0`.
`maxOverRange_specificDuplicate f 0 = 0`; `maxOverRange_specificDuplicate f (n+1) = max (maxOverRange_specificDuplicate f n) (f (n+1))`.
This is a 1-indexed variant of `scanMax` with a `0` default instead of `f 0`.
Unlike `scanMax`, this does not evaluate `f 0` at all, so it is safe even when
`f 0` is not defined. -/
def maxOverRange_specificDuplicate (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxOverRange_specificDuplicate f n) (f (n + 1))

@[simp] lemma maxOverRange_zero (f : Nat → Nat) : maxOverRange_specificDuplicate f 0 = 0 := rfl

lemma maxOverRange_succ_specificDuplicate (f : Nat → Nat) (n : Nat) :
    maxOverRange_specificDuplicate f (n + 1) = max (maxOverRange_specificDuplicate f n) (f (n + 1)) := rfl

lemma maxOverRange_le {f : Nat → Nat} {i n : Nat} (hpos : 1 ≤ i) (hle : i ≤ n) :
    f i ≤ maxOverRange_specificDuplicate f n := by
  induction n with
  | zero =>
    omega
  | succ n ih =>
    rw [maxOverRange_succ_specificDuplicate]
    by_cases h_last : i = n + 1
    · subst i; exact le_max_right _ _
    · have hle_n : i ≤ n := by omega
      exact le_trans (ih hle_n) (le_max_left _ _)

/-! ### Maximum over an arbitrary natural-number range

`maxInRange f lo hi` computes the maximum value of `f i` for `i` in the closed
interval `[lo, hi]`. Returns `0` when `lo > hi` (empty range). This generalizes
`maxOverRange_specificDuplicate` — which is 1-indexed and `Nat`-only — to any `LinearOrder` type
with `Zero`, and to any lower bound `lo`. -/

/-- Maximum of `f i` for `i ∈ [lo, hi]`. Returns `0` for an empty range (`lo > hi`). -/
def maxInRange {α : Type} [LinearOrder α] [Zero α] (f : Nat → α) (lo hi : Nat) : α :=
  if lo > hi then
    (0 : α)
  else if lo = hi then
    f hi
  else
    max (f hi) (maxInRange f lo (hi - 1))
termination_by hi

/-- Step lemma for `Nat.maxInRange`: when `lo < hi`, the maximum over `[lo, hi]`
is the max of `f hi` and the maximum over `[lo, hi-1]`. -/
lemma maxInRange_step {α : Type} [LinearOrder α] [Zero α] (f : Nat → α) (lo hi : Nat) (h : lo < hi) :
    maxInRange f lo hi = max (f hi) (maxInRange f lo (hi - 1)) := by
  rw [maxInRange]
  have hnotgt : ¬ (lo > hi) := by omega
  have hnoteq : lo ≠ hi := by omega
  simp [hnotgt, hnoteq]

/-! ### Exclusive prefix max (0-indexed)

`prefixMax_specificDuplicate f n = max_{i=0}^{n-1} f i` uses the same exclusive-prefix convention as
`prefixSum_specificDuplicate`. Unlike `scanMax` (inclusive, uses `f 0` as base) and `maxOverRange_specificDuplicate`
(1-indexed, `Nat`-only), this works for any `LinearOrder` type with `Zero`.

Example: `prefixMax_specificDuplicate (λ i => [3,1,4][i]!) 3 = max 3 (max 1 0) = 3`. -/

/-- Exclusive prefix maximum: `prefixMax_specificDuplicate f n` is the maximum of `f 0, …, f (n-1)`.
Returns `0` when `n = 0`. Generalized from `list_prefix_max` (LeetCode 1725). -/
def prefixMax_specificDuplicate {α : Type _} [LinearOrder α] [Zero α] (f : Nat → α) : Nat → α
  | 0 => 0
  | n+1 => max (f n) (prefixMax_specificDuplicate f n)

@[simp] theorem prefixMax_zero {α : Type _} [LinearOrder α] [Zero α] (f : Nat → α) :
    prefixMax_specificDuplicate f 0 = 0 := rfl

/-- Recurrence for `prefixMax_specificDuplicate`: `prefixMax_specificDuplicate f (n+1) = max (f n) (prefixMax_specificDuplicate f n)`. -/
theorem prefixMax_succ {α : Type _} [LinearOrder α] [Zero α] (f : Nat → α) (n : Nat) :
    prefixMax_specificDuplicate f (n+1) = max (f n) (prefixMax_specificDuplicate f n) := rfl

/-- For any `i < n`, `f i ≤ prefixMax_specificDuplicate f n`. This is the individual-value bound:
the exclusive prefix max is an upper bound for every value in the prefix.
Generalized from `best_prefix_with` bound lemmas (LeetCode 2760). -/
lemma le_prefixMax_of_lt {α : Type _} [LinearOrder α] [Zero α] (f : Nat → α) {i n : Nat} (h : i < n) :
    f i ≤ prefixMax_specificDuplicate f n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rw [prefixMax_succ]
    by_cases hi : i = n
    · subst i; exact le_max_left _ _
    · have hi_lt : i < n := by omega
      exact le_trans (ih hi_lt) (le_max_right _ _)

/-- If every value `f i` for `i < n` is bounded above by `bound`, and `0 ≤ bound`
(to cover the `n = 0` base case where `prefixMax_specificDuplicate f 0 = 0`), then `prefixMax_specificDuplicate f n ≤ bound`.
This is the core boundedness property of prefix maxima, generalized from
`best_prefix_with_le_of_bound` (LeetCode 2760). -/
lemma prefixMax_le_of_forall_lt {α : Type _} [LinearOrder α] [Zero α] (f : Nat → α) (bound : α) {n : Nat}
    (h_nonneg : (0 : α) ≤ bound) (hf : ∀ i, i < n → f i ≤ bound) : prefixMax_specificDuplicate f n ≤ bound := by
  induction n with
  | zero =>
    simp [prefixMax_specificDuplicate]
    exact h_nonneg
  | succ n ih =>
    rw [prefixMax_succ]
    exact max_le (hf n (Nat.lt_succ_self n))
      (ih (fun i hi => hf i (Nat.lt_of_lt_of_le hi (Nat.le_succ n))))

/-! ### Exclusive prefix argmax (0-indexed)

`prefixArgMax val key n` returns the key `key j` where `j < n` maximizes `val j`,
breaking ties by choosing the smaller key. This is the argmax counterpart of
`prefixMax_specificDuplicate`: while `prefixMax_specificDuplicate val n` tells you the maximum value in `[0, n)`,
`prefixArgMax` tells you which key attains it.

Tie-breaking by smaller key makes the result deterministic and corresponds to the
common convention of "return the smallest index" in competitive-programming problems
(e.g., LeetCode 2432 "The Employee That Worked on the Longest Task").

Generalized from `prefixArgMax` in LeetCode 2432. -/

/-- Exclusive prefix argmax: returns the key `key j` where `j < n` maximizes `val j`,
breaking ties by choosing the smaller key. Returns `key 0` when `n = 0`.
Uses `[Zero α]` for the initial maximum, matching the `prefixMax_specificDuplicate` convention. -/
def prefixArgMax {α β : Type} [LinearOrder α] [LinearOrder β] [Zero α]
    (val : Nat → α) (key : Nat → β) : Nat → β
  | 0 => key 0
  | n+1 =>
    let cur_val := val n
    let cur_key := key n
    let prev_key := prefixArgMax val key n
    let prev_max := prefixMax_specificDuplicate val n
    if cur_val > prev_max then
      cur_key
    else if cur_val < prev_max then
      prev_key
    else if cur_key < prev_key then
      cur_key
    else
      prev_key

@[simp] theorem prefixArgMax_zero {α β : Type} [LinearOrder α] [LinearOrder β] [Zero α]
    (val : Nat → α) (key : Nat → β) : prefixArgMax val key 0 = key 0 := rfl

/-- Sum of `f i` for `i` from `1` to `n` (inclusive).
`sumOneTo f 0 = 0`, `sumOneTo f (n+1) = sumOneTo f n + f (n+1)`.
This is a 1-indexed variant of `prefixSum_specificDuplicate`; equivalent to `prefixSum_specificDuplicate (fun i => f (i+1)) n`. -/
def sumOneTo {α : Type _} [AddMonoid α] (f : Nat → α) : Nat → α
  | 0 => 0
  | n + 1 => sumOneTo f n + f (n + 1)

@[simp] lemma sumOneTo_zero {α : Type _} [AddMonoid α] (f : Nat → α) : sumOneTo f 0 = 0 := rfl

lemma sumOneTo_succ {α : Type _} [AddMonoid α] (f : Nat → α) (n : Nat) :
    sumOneTo f (n + 1) = sumOneTo f n + f (n + 1) := rfl

/-- `sumOneTo` can be expressed in terms of `prefixSum_specificDuplicate` by shifting indices by 1. -/
lemma sumOneTo_eq_prefixSum_shift {α : Type _} [AddMonoid α] (f : Nat → α) (n : Nat) :
    sumOneTo f n = prefixSum_specificDuplicate (fun i => f (i + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumOneTo, prefixSum_specificDuplicate, ih]

/-- Sums `contrib k` for `k = 1, 2, ..., n`. Equivalent to `sumOneTo`, but with the
new term added on the left: `sum_contrib contrib (n+1) = contrib (n+1) + sum_contrib contrib n`.
This specific recursion pattern (head-first) is convenient for proofs where the head term
needs to be extracted first, complementing `sumOneTo` which appends the new term on the right.

Generalized from `sum_contrib` in LeetCode 2652 "Sum Multiples". -/
def sum_contrib (contrib : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => contrib (n + 1) + sum_contrib contrib n

@[simp] lemma sum_contrib_zero (contrib : Nat → Nat) : sum_contrib contrib 0 = 0 := rfl

lemma sum_contrib_succ (contrib : Nat → Nat) (n : Nat) :
    sum_contrib contrib (n + 1) = contrib (n + 1) + sum_contrib contrib n := rfl

/-- `sum_contrib` is equivalent to `sumOneTo` (modulo `add_comm`).
Both sum `contrib k` for `k = 1..n`, only differing in whether the new term is placed on the left
(`sum_contrib`) or right (`sumOneTo`). In `Nat` (and any commutative monoid) they agree. -/
lemma sum_contrib_eq_sumOneTo (contrib : Nat → Nat) (n : Nat) :
    sum_contrib contrib n = sumOneTo contrib n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum_contrib_succ, sumOneTo_succ, ih, add_comm]

/-! ### Congruence lemmas for prefix sums

If two functions `f` and `g` are pointwise equal on `Nat`, their prefix sums are equal.
These lemmas are useful for rewriting under sum expressions when function definitions
are unfolded or substituted. -/

/-- Congruence lemma for `prefixSum_specificDuplicate`: if `f n = g n` for all `n`, then
`prefixSum_specificDuplicate f n = prefixSum_specificDuplicate g n`. -/
lemma prefixSum_congr {α : Type _} [AddMonoid α] (f g : Nat → α) (h : ∀ n, f n = g n) (n : Nat) :
    prefixSum_specificDuplicate f n = prefixSum_specificDuplicate g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixSum_specificDuplicate, ih, h n]

/-- Congruence lemma for `sumOneTo`: if `f n = g n` for all `n`, then
`sumOneTo f n = sumOneTo g n`. -/
lemma sumOneTo_congr {α : Type _} [AddMonoid α] (f g : Nat → α) (h : ∀ n, f n = g n) (n : Nat) :
    sumOneTo f n = sumOneTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumOneTo, ih, h (n + 1)]

/-- Congruence lemma for `inclusivePrefixSum`: if `f n = g n` for all `n`, then
`inclusivePrefixSum f n = inclusivePrefixSum g n`. -/
lemma inclusivePrefixSum_congr {α : Type _} [AddMonoid α] (f g : Nat → α) (h : ∀ n, f n = g n) (n : Nat) :
    inclusivePrefixSum f n = inclusivePrefixSum g n := by
  induction n with
  | zero => simp [inclusivePrefixSum, h 0]
  | succ n ih => simp [inclusivePrefixSum, ih, h (n + 1)]

/-- Recursively sums `f i` for `i` from 2 to `n`. Returns 0 for n ≤ 2.
This is a building block for recurrence relations over triangular/polygonal numbers. -/
def sumStep (f : Nat → Nat) : Nat → Nat
  | 0 | 1 | 2 => 0
  | n+1 => sumStep f n + f n

/-- Sum of `i*(i+1)` for `i` from 2 to `n-1`. Used in minimum triangulation weight problems.
Equals `sumStep (fun n => n*(n+1)) n`. -/
def triangulationSum : Nat → Nat
  | 0 | 1 | 2 => 0
  | n+1 => triangulationSum n + n * (n + 1)

/-- The last digit of `k*m` in base `b` arithmetic: `(k * m) % b`.
For base 10 this gives the standard decimal last digit of the product. -/
def lastDigitBase (b k m : Nat) : Nat := (k * m) % b

/-- Sum of `lastDigitBase b (k+1) m` for `k` in `range b`.
This is the sum over one full cycle, since `lastDigitBase` repeats every `b` terms:
`lastDigitBase b (k+b) m = lastDigitBase b k m`. -/
def lastDigitCycleSum (b m : Nat) : Nat :=
  (Finset.range b).sum fun k => lastDigitBase b (k+1) m

/-- Prefix sum: `lastDigitPrefixSum b rem m` = ∑_{k=1}^{rem} lastDigitBase b k m.
This sums the first `rem` values of the last-digit sequence. -/
def lastDigitPrefixSum (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | rem+1, m => lastDigitPrefixSum b rem m + lastDigitBase b (rem+1) m

/-- Efficient computation of ∑_{k=1}^{t} ((k * m) % b), using the period `b` of
`lastDigitBase b k m`. The sum is decomposed into full cycles plus a prefix remainder.
This is the core computation in the "Book Reading" problem (CF 1213C). -/
def sumLastDigitsBase (b t m : Nat) : Nat :=
  (t / b) * lastDigitCycleSum b m + lastDigitPrefixSum b (t % b) m

lemma lastDigitBase_add_base (b k m : Nat) : lastDigitBase b (k + b) m = lastDigitBase b k m := by
  unfold lastDigitBase
  rw [add_mul, Nat.add_mod]
  simp

lemma lastDigitPrefixSum_succ (b rem m : Nat) :
    lastDigitPrefixSum b (rem + 1) m = lastDigitPrefixSum b rem m + lastDigitBase b (rem + 1) m := by
  simp [lastDigitPrefixSum]

lemma lastDigitPrefixSum_zero (b m : Nat) : lastDigitPrefixSum b 0 m = 0 := by
  simp [lastDigitPrefixSum]

/-- If `(a : ℤ) * 2 ≤ (b : ℤ)` for natural numbers `a`, `b`, then `a ≤ b` in `ℕ`.
Useful for converting integer inequalities back to natural number comparisons
when the factor 2 provides enough margin. -/
lemma le_of_int_two_mul_le {a b : ℕ} (h : (a : ℤ) * 2 ≤ (b : ℤ)) : a ≤ b := by
  have ha : (0 : ℤ) ≤ (a : ℤ) := Nat.cast_nonneg _
  have h' : (a : ℤ) ≤ (b : ℤ) := by omega
  exact Nat.cast_le.mp h'

/-- If `bound = 2^width` and both `a` and `b` are less than `bound`,
then `a ^^^ b < bound`. This is a convenient wrapper around `Nat.xor_lt_two_pow`
for when the bound is given as an explicit constant rather than `2^n`. -/
lemma xor_lt_of_lt_power_bound {bound width a b : Nat}
    (hbound : bound = 2 ^ width) (ha : a < bound) (hb : b < bound) :
    a ^^^ b < bound := by
  subst bound
  exact Nat.xor_lt_two_pow ha hb

/-- Sum of quotient and remainder: `quot_add_rem d n = n / d + n % d`.
For a number `n` expressed in base `d`, the remainder `n % d` is the least significant digit,
and the quotient `n / d` shifts right by one digit. Repeating this decomposition extracts
all digits; `quot_add_rem` captures a single step of this process.
Commonly used in digit-sum and digit-manipulation problems (e.g., CF 1999A). -/
def quot_add_rem (d n : Nat) : Nat :=
  n / d + n % d

/-! ### `min` arithmetic lemmas -/

/-- For any `x, y : ℕ`, `x + min x y ≤ 2 * x`. This follows from `min x y ≤ x`. -/
lemma add_min_le_two_mul (x y : Nat) : x + min x y ≤ 2 * x := by
  have h : min x y ≤ x := Nat.min_le_left x y
  omega

/-- For any `x, y : ℕ`, `min x y ≤ 2 * x`. This is a corollary of `min_le_left` and `x ≤ 2*x`. -/
lemma min_le_two_mul_left (x y : Nat) : min x y ≤ 2 * x := by
  have hx : x ≤ 2 * x := by omega
  exact Nat.le_trans (Nat.min_le_left x y) hx

/-- The "strong pair" condition equivalence: `max x y - min x y ≤ min x y` iff `max x y ≤ 2 * min x y`.
In other words, the maximum is at most twice the minimum exactly when the difference
between the maximum and minimum is at most the minimum. Useful for bounding problems
where a pair's values must be within a factor of 2 of each other. -/
lemma max_sub_min_le_min_iff_max_le_two_mul_min (x y : Nat) :
    max x y - min x y ≤ min x y ↔ max x y ≤ 2 * min x y := by
  omega

/-- Absolute difference of two natural numbers: `|a - b|` computed via conditional subtraction.
In `Nat`, subtraction truncates at 0, so `|a - b|` is `a - b` when `a ≥ b`, else `b - a`. -/
def abs_diff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a

theorem abs_diff_comm (a b : Nat) : abs_diff a b = abs_diff b a := by
  unfold abs_diff
  by_cases h : a ≥ b
  · by_cases h' : b ≥ a
    · have heq : a = b := Nat.le_antisymm h' h
      subst heq
      rfl
    · simp [h, h']
  · have h' : b ≥ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [h, h']

theorem abs_diff_self (a : Nat) : abs_diff a a = 0 := by
  unfold abs_diff; simp

/-- `abs_diff a b` is equal to `max a b - min a b`. This provides an alternative
formulation using `max` and `min` that is often more convenient for `omega` and
algebraic manipulations. Since `max a b ≥ min a b`, the subtraction is always
safe (non-truncating) in `Nat`. -/
theorem abs_diff_eq_max_sub_min (a b : Nat) : abs_diff a b = max a b - min a b := by
  unfold abs_diff
  by_cases h : a ≥ b
  · simp [max_eq_left h, min_eq_right h, h]
  · have h' : b ≥ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [max_eq_right h', min_eq_left h', h]

/-! ### Chunk-based counting

The functions and theorems in this section process a flat sequence (of total `length`)
as a collection of fixed-size chunks. Each chunk has size `size`; chunk `i` covers
indices `[size*i, size*i + size)`. A chunk is "complete" when it lies entirely within
`length`, i.e., `size*i + size ≤ length`.

This pattern is common in competitive programming problems where input is split into
rows of `k` elements per row, and each row must be processed independently.
-/

/-- Counts how many complete chunks of size `size` satisfy predicate `p`,
for chunks indexed `0` through `k-1`. The precondition `h_bound : size * k ≤ length`
ensures all chunk starting positions are within the total length.

A chunk `i` is "complete" when `size * i + size ≤ length`. The predicate `p` is only
evaluated on complete chunks and receives a proof of completeness as its second argument.

Example: for `size = 3`, `length = 9`, and a predicate that checks the sum of three
elements, `countChunks 3 9 p 3 h` counts how many of the 3 rows satisfy the predicate. -/
def countChunks (size length : Nat) (p : (i : Nat) → size * i + size ≤ length → Bool)
    (k : Nat) (h_bound : size * k ≤ length) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 =>
    have h_row : size * k' + size ≤ length := by
      simpa [Nat.mul_succ] using h_bound
    have h_rec : size * k' ≤ length := by omega
    countChunks size length p k' h_rec + (if p k' h_row then 1 else 0)

/-- Congruence lemma for `countChunks`: if two predicates agree on all complete chunks,
the counts are equal. -/
lemma countChunks_congr (size length : Nat)
    (p₁ p₂ : (i : Nat) → size * i + size ≤ length → Bool)
    (k : Nat) (h_bound : size * k ≤ length)
    (h : ∀ i (hrow : size * i + size ≤ length), p₁ i hrow = p₂ i hrow) :
    countChunks size length p₁ k h_bound = countChunks size length p₂ k h_bound := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [countChunks]
    have h_row : size * k + size ≤ length := by
      simpa [Nat.mul_succ] using h_bound
    have h_rec : size * k ≤ length := by omega
    rw [ih h_rec]
    simp [h k h_row]

/-- Uniqueness / induction lemma for `countChunks`: any function `f`
satisfying the same base case and recurrence as `countChunks` is equal to it.

This is useful for proving that two different implementations of chunk-based counting
compute the same result. Provide the base case `f 0 = 0` and the step case
`f (k+1) = f k + (if p k then 1 else 0)` to conclude `f = countChunks`. -/
lemma countChunks_eq_of_succ (size length : Nat)
    (p : (i : Nat) → size * i + size ≤ length → Bool)
    (f : (k : Nat) → size * k ≤ length → Nat)
    (h_zero : f 0 (by omega) = 0)
    (h_succ : ∀ k (h_bound : size * (k + 1) ≤ length),
      f (k + 1) h_bound =
        f k (by
          have h_row : size * k + size ≤ length := by
            simpa [Nat.mul_succ] using h_bound
          omega) +
          (if p k (by
            simpa [Nat.mul_succ] using h_bound) then 1 else 0))
    (k : Nat) (h_bound : size * k ≤ length) :
    f k h_bound = countChunks size length p k h_bound := by
  induction k with
  | zero => simpa [countChunks] using h_zero
  | succ k ih =>
    have h_row : size * k + size ≤ length := by
      simpa [Nat.mul_succ] using h_bound
    have h_rec : size * k ≤ length := by omega
    rw [countChunks, h_succ k h_bound, ih h_rec]

/-! ### Bit operations -/

/-- Check whether the `k`-th bit of `n` is set (i.e., equals `1`).
Uses the shift-and-mask formulation `((n >>> k) &&& 1 = 1)`, which is the natural
expression in imperative/competitive programming contexts.
Equivalent to `Nat.testBit n k`. -/
def bit_is_set (n k : Nat) : Bool := ((n >>> k) &&& 1 = 1)

/-- Count the number of bit positions in `[0, bits_done)` where `x` and `y` differ.
This computes the partial Hamming distance: `bitDiffCount x y k = popCount ((x ^^^ y) % 2^k)`.
Equivalent to `∑_{j < bits_done} (if x.testBit j ≠ y.testBit j then 1 else 0)`. -/
def bitDiffCount (x y bits_done : Nat) : Nat :=
  match bits_done with
  | 0 => 0
  | bits_done' + 1 =>
    bitDiffCount x y bits_done' + (if x.testBit bits_done' ≠ y.testBit bits_done' then 1 else 0)

@[simp] lemma bitDiffCount_zero (x y : Nat) : bitDiffCount x y 0 = 0 := rfl

lemma bitDiffCount_succ (x y n : Nat) :
    bitDiffCount x y (n + 1) = bitDiffCount x y n + (if x.testBit n ≠ y.testBit n then 1 else 0) :=
  rfl

lemma bitDiffCount_comm (x y n : Nat) : bitDiffCount x y n = bitDiffCount y x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [bitDiffCount_succ, ih, ne_comm]

lemma bitDiffCount_self (x n : Nat) : bitDiffCount x x n = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [bitDiffCount_succ, ih]

/-- Count how many of the first `len` bits (positions `0` through `len-1`) of `mask` are set to `1`.
This is the prefix population count: `countOnesPrefix mask len = popCount (mask % 2^len)`.
Equivalent to `bitDiffCount mask 0 len` and `countTrueUpTo (λ j => mask.testBit j) len`. -/
def countOnesPrefix (mask : Nat) (len : Nat) : Nat :=
  match len with
  | 0 => 0
  | len' + 1 => countOnesPrefix mask len' + (if mask.testBit len' then 1 else 0)

@[simp] lemma countOnesPrefix_zero (mask : Nat) : countOnesPrefix mask 0 = 0 := rfl

lemma countOnesPrefix_succ (mask len : Nat) :
    countOnesPrefix mask (len + 1) = countOnesPrefix mask len + (if mask.testBit len then 1 else 0) :=
  rfl

lemma countOnesPrefix_le_len (mask len : Nat) : countOnesPrefix mask len ≤ len := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [countOnesPrefix_succ]
    have hbit : (if mask.testBit len then 1 else 0) ≤ 1 := by
      split <;> omega
    have : countOnesPrefix mask len + (if mask.testBit len then 1 else 0) ≤ len + 1 := by
      omega
    simpa [add_comm] using this

/-- Population count (Hamming weight): the number of `1` bits in the binary representation of `n`.
For example, `popCount 6 = 2` because `6 = 110₂`.
Recursively computes `(n % 2) + popCount (n / 2)`.
Note: this duplicates the mathlib `Nat.popCount` for compatibility with pre-existing definitions
in competitive programming solutions that use this exact recursive form. -/
def popCount (n : Nat) : Nat :=
  if n = 0 then 0 else (n % 2) + popCount (n / 2)
termination_by n

/-- Bit length of `n` (zero-based convention): returns `0` for `n = 0`, otherwise `1 + bit_length (n / 2)`.
For `n > 0`, this equals the number of bits needed to represent `n` in binary.
This differs from `Nat.bitLen` which returns `1` for `n = 0`.
For example, `bit_length 5 = 3` because `5 = 101₂`. -/
def bit_length (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + bit_length (n / 2)
termination_by n

/-- Tail-recursive helper for `popCount`. Computes `popCount x + acc` by repeatedly
dividing `x` by 2 and accumulating the least significant bits (`x % 2`) into `acc`.
This formulation is convenient for proving popcount properties by induction
when the recursion needs to preserve an accumulator invariant, e.g.,
`popCountAux (a + b) acc = popCountAux a (popCountAux b acc)`. -/
def popCountAux (x : Nat) (acc : Nat) : Nat :=
  if h : x = 0 then
    acc
  else
    popCountAux (x / 2) (acc + x % 2)
termination_by x
decreasing_by
  simp_wf
  have hpos : 0 < x := Nat.pos_of_ne_zero h
  omega

@[simp]
lemma popCountAux_zero (acc : Nat) : popCountAux 0 acc = acc := by
  unfold popCountAux; simp

lemma popCountAux_ne_zero (x acc : Nat) (hx : x ≠ 0) :
    popCountAux x acc = popCountAux (x / 2) (acc + x % 2) := by
  rw [popCountAux]
  simp [hx]

/-- `popCountAux` is equivalent to `popCount x + acc`.
This bridges the tail-recursive formulation with the standard `popCount`. -/
lemma popCountAux_eq_popCount_add (x acc : Nat) : popCountAux x acc = popCount x + acc := by
  revert acc
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro acc
    rw [popCountAux]
    split
    · simp [popCount, *]
    · rename_i hx
      rw [popCount]
      simp [hx]
      rw [ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)) (acc + x % 2)]
      omega

/-- Non-accumulator tail-recursive population count. Equivalent to `popCount`.
`popCountTailRec x = popCount x`. -/
def popCountTailRec (x : Nat) : Nat := popCountAux x 0

@[simp]
lemma popCountTailRec_eq_popCount (x : Nat) : popCountTailRec x = popCount x := by
  simp [popCountTailRec, popCountAux_eq_popCount_add]

/-- Count how many set bits of `n` need to be cleared (1→0) to obtain `k`.
Returns `-1` if it's impossible because `k` has a set bit where `n` has a zero.
In bitwise terms: if `k & ~n ≠ 0` (i.e., `k` is not a submask of `n`), returns `-1`;
otherwise returns the number of bit positions where `n` has 1 and `k` has 0 —
that is, `popCount (n & ~k)`.

This is an Int-valued variant that combines a feasibility check with a counting result,
commonly used in problems where only 1→0 bit flips are allowed.
Generalized from `min_changes_aux` (LeetCode 3226). -/
def countBitsToClear (n k : Nat) : Int :=
  if n = 0 ∧ k = 0 then
    0
  else if k % 2 = 1 ∧ n % 2 = 0 then
    -1
  else
    let tail := countBitsToClear (n / 2) (k / 2)
    if tail < 0 then
      -1
    else if n % 2 = 1 ∧ k % 2 = 0 then
      tail + 1
    else
      tail
termination_by n + k

/-! ### Bounded linear search

`findFrom p fuel start` finds the smallest `x` in `[start, start+fuel]` such that `p x` is true.
If no such `x` exists, returns `start+fuel`.

This is the natural-number analog of a `List.find` scanning forward within a bounded range.
Useful in problems where you need to find the next element satisfying a predicate,
such as finding the next beautiful year (CF 271A). -/

/-- Bounded linear search from a starting point.
`findFrom p fuel start` finds the smallest `x` in `[start, start+fuel]` such that `p x` is true.
If no such `x` exists, returns `start+fuel`. -/
def findFrom (p : Nat → Bool) (fuel start : Nat) : Nat :=
  match fuel with
  | 0 => start
  | fuel+1 =>
    if p start then start else findFrom p fuel (start+1)

/-- `start ≤ findFrom p fuel start` — the search never goes backwards. -/
lemma findFrom_ge_start (p : Nat → Bool) (fuel start : Nat) : start ≤ findFrom p fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    unfold findFrom
    split
    · rfl
    · have : start ≤ start+1 := by omega
      have h_ih := ih (start+1)
      exact Nat.le_trans this h_ih

/-- `findFrom p fuel start ≤ start + fuel` – the search never overshoots past `start + fuel`. -/
lemma findFrom_le_add_fuel (p : Nat → Bool) (fuel start : Nat) : findFrom p fuel start ≤ start + fuel := by
  induction fuel generalizing start with
  | zero => simp [findFrom]
  | succ fuel ih =>
    simp [findFrom]
    by_cases h : p start = true
    · simp [h]
    · simp [h]
      have h := ih (start + 1)
      omega

/-- `findFrom` stays within `[start, start + fuel]`. -/
lemma findFrom_range (p : Nat → Bool) (fuel start : Nat) :
    start ≤ findFrom p fuel start ∧ findFrom p fuel start ≤ start + fuel :=
  ⟨findFrom_ge_start _ _ _, findFrom_le_add_fuel _ _ _⟩

/-- If there exists `s` in `[start, start + fuel]` with `p s = true`,
then `p (findFrom p fuel start) = true`. -/
lemma findFrom_satisfies (p : Nat → Bool) (fuel start : Nat)
    (h_exists : ∃ s, start ≤ s ∧ s ≤ start + fuel ∧ p s = true) : p (findFrom p fuel start) = true := by
  induction fuel generalizing start with
  | zero =>
    rcases h_exists with ⟨s, hs₁, hs₂, hs₃⟩
    have hs_eq : s = start := by omega
    subst hs_eq
    simp [findFrom, hs₃]
  | succ fuel ih =>
    rcases h_exists with ⟨s, hs₁, hs₂, hs₃⟩
    simp [findFrom]
    by_cases h : p start = true
    · simp [h]
    · simp [h]
      have hs_ne : s ≠ start := by
        intro heq; subst heq; rw [hs₃] at h; simp at h
      have hs_ge_succ : start + 1 ≤ s := by omega
      have h_exists' : ∃ s, start + 1 ≤ s ∧ s ≤ (start + 1) + fuel ∧ p s = true := by
        refine ⟨s, hs_ge_succ, ?_, hs₃⟩
        omega
      exact ih (start + 1) h_exists'

/-- If there exists `s` in `[start, start + fuel]` with `p s = true`,
then for all `s` in `[start, findFrom p fuel start - 1]`, `p s = false`.
In other words, `findFrom` returns the first index satisfying `p`. -/
lemma findFrom_minimal (p : Nat → Bool) (fuel start : Nat)
    (h_exists : ∃ s, start ≤ s ∧ s ≤ start + fuel ∧ p s = true) :
    ∀ s, start ≤ s → s < findFrom p fuel start → p s = false := by
  induction fuel generalizing start with
  | zero =>
    rcases h_exists with ⟨s, hs₁, hs₂, hs₃⟩
    have hs_eq : s = start := by omega
    subst hs_eq
    simp [findFrom]
    intro s' hs'₁ hs'₂
    omega
  | succ fuel ih =>
    rcases h_exists with ⟨s, hs₁, hs₂, hs₃⟩
    simp [findFrom]
    by_cases h : p start = true
    · simp [h]
      intro s' hs'₁ hs'₂
      omega
    · simp [h]
      have hs_ne : s ≠ start := by
        intro heq; subst heq; rw [hs₃] at h; simp at h
      have hs_ge_succ : start + 1 ≤ s := by omega
      have h_exists' : ∃ s, start + 1 ≤ s ∧ s ≤ (start + 1) + fuel ∧ p s = true := by
        refine ⟨s, hs_ge_succ, ?_, hs₃⟩
        omega
      intro s' hs'₁ hs'₂
      by_cases hs'_eq : s' = start
      · rw [hs'_eq]
        match h_eq : p start with
        | true => simp [h_eq] at h
        | false => rfl
      · have hs'_ge_succ : start + 1 ≤ s' := by omega
        exact ih (start + 1) h_exists' s' hs'_ge_succ hs'₂

/-- For any `m` in `[start, findFrom p fuel start)`, `p m = false`.
Unlike `findFrom_minimal`, this lemma does not require an existence hypothesis
(`∃ s, ..., p s = true`). It works even when no element in the range satisfies `p`,
in which case `findFrom` returns `start + fuel` (or `start` when `fuel = 0`). -/
lemma findFrom_false_before (p : Nat → Bool) :
    ∀ fuel start m : Nat,
      m < findFrom p fuel start →
      start ≤ m →
      p m = false
  | 0, start, m, hlt, hle => by
      simp [findFrom] at hlt
      omega
  | fuel + 1, start, m, hlt, hle => by
      simp only [findFrom] at hlt
      by_cases hstart : p start = true
      · simp [hstart] at hlt; omega
      · simp [hstart] at hlt
        by_cases hm : m = start
        · subst m; simpa using hstart
        · have hnext : start + 1 ≤ m := by omega
          exact findFrom_false_before p fuel (start + 1) m hlt hnext

/-- Combined specification for `findFrom` when the predicate is known to hold at the
upper bound. Under the assumptions that `P` is false before `start` and true at
`start + n`, `findFrom P n start` returns the first index where `P` holds in `[start, start + n]`.

This packages both `findFrom_satisfies` and `findFrom_false_before` into a single
conjunction for the common case where the existence of a satisfying element at
the upper bound is known (e.g., binary search or bounded scan with a guaranteed solution). -/
lemma findFrom_spec_with_bound (P : Nat → Bool) (start n : Nat)
    (h_lt : ∀ k < start, P k = false)
    (h_bound : P (start + n) = true) :
    P (findFrom P n start) = true ∧
    ∀ k < findFrom P n start, P k = false := by
  induction n generalizing start with
  | zero =>
    have h_find : findFrom P 0 start = start := rfl
    rw [h_find]
    have hP : P start = true := by
      simpa [add_comm] using h_bound
    exact ⟨hP, h_lt⟩
  | succ n ih =>
    have h_find : findFrom P (n + 1) start = (if P start then start else findFrom P n (start + 1)) := rfl
    rw [h_find]
    by_cases hP : P start = true
    · have h_val : (if P start then start else findFrom P n (start + 1)) = start := by simp [hP]
      rw [h_val]
      exact ⟨hP, h_lt⟩
    · have hP_false : P start = false := by
        cases h : P start
        · rfl
        · exfalso; exact hP h
      have h_val : (if P start then start else findFrom P n (start + 1)) =
          findFrom P n (start + 1) := by simp [hP_false]
      rw [h_val]
      have h_lt' : ∀ k < start + 1, P k = false := by
        intro k hk
        have hk_le : k ≤ start := by omega
        rcases Nat.eq_or_lt_of_le hk_le with (rfl | hk')
        · exact hP_false
        · exact h_lt k hk'
      have h_bound' : P ((start + 1) + n) = true := by
        have : (start + 1) + n = start + (n + 1) := by omega
        rw [this]
        exact h_bound
      exact ih (start + 1) h_lt' h_bound'

/-! ### Backward bounded search (find largest satisfying index)

`findMaxSatisfying p n` finds the largest `k ≤ n` such that `p k = true`,
scanning backwards from `n`. If no `k ≤ n` satisfies `p`, returns `0`.

This is the dual of `findFrom`: while `findFrom` finds the smallest index satisfying `p`
by scanning forwards, `findMaxSatisfying` finds the largest index satisfying `p` by
scanning backwards. Common in problems where you need the longest prefix/segment
satisfying a property (e.g., longest subarray with bounded difference). -/

/-- Find the largest `k ≤ n` such that `p k = true`. Returns `0` if no such `k` exists. -/
def findMaxSatisfying (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if p (n + 1) then
      n + 1
    else
      findMaxSatisfying p n

/-- Correctness specification for `findMaxSatisfying`:
the result `k` satisfies `k ≤ n`, `k = 0 ∨ p k = true`, and for all `m > k` with `m ≤ n`,
`p m = false`. -/
theorem findMaxSatisfying_spec (p : Nat → Bool) (n : Nat) :
    (let k := findMaxSatisfying p n
    k ≤ n ∧ (k = 0 ∨ p k = true) ∧
    (∀ m, k < m → m ≤ n → p m = false)) := by
  induction' n with n ih
  · refine ⟨by rfl, Or.inl rfl, ?_⟩
    intro m hm h0
    omega
  · unfold findMaxSatisfying
    split
    · rename_i h_has
      refine ⟨by omega, Or.inr h_has, ?_⟩
      intro m hm hmn
      omega
    · rename_i h_no
      have hp_false : p (n + 1) = false := by simpa using h_no
      rcases ih with ⟨hkle, hk_cases, hk_max⟩
      refine ⟨le_trans hkle (by omega), ?_, ?_⟩
      · rcases hk_cases with (hk0 | hk_ex)
        · exact Or.inl hk0
        · exact Or.inr hk_ex
      · intro m hm hmn
        by_cases hm_eq : m = n + 1
        · subst hm_eq
          exact hp_false
        · have hm_le_n : m ≤ n := by omega
          exact hk_max m hm hm_le_n

/-- If `m ≤ n` and `p m = true`, then `m ≤ findMaxSatisfying p n`.
In other words, any satisfying index up to `n` is bounded above by the result. -/
lemma findMaxSatisfying_ge_of_satisfies (p : Nat → Bool) (n m : Nat) (hmn : m ≤ n) (hp : p m = true) :
    m ≤ findMaxSatisfying p n := by
  induction' n with n ih generalizing m
  · -- n = 0, so m = 0
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  · unfold findMaxSatisfying
    by_cases hmn' : m ≤ n
    · -- m ≤ n, use IH
      have h_ih : m ≤ findMaxSatisfying p n := ih m hmn' hp
      split
      · -- p (n+1) = true, result is n+1, so m ≤ n+1
        omega
      · -- p (n+1) = false, result is findMaxSatisfying p n
        exact h_ih
    · -- m = n + 1
      have hm_eq : m = n + 1 := by omega
      subst hm_eq
      rw [hp]
      simp

/-! ### `Option`-returning backward search

`findLatest p n` finds the largest `k` such that `1 ≤ k ≤ n` and `p k = true`,
returning `Option Nat`. It returns `none` if no such `k` exists, and `some k` otherwise.
This is a cleaner variant of `findMaxSatisfying` that uses `Option` for proper
"not found" semantics instead of sentinel values. -/

/-- Find the largest `k` such that `1 ≤ k ≤ n` and `p k = true`.
Returns `some k` if found, `none` otherwise. -/
def findLatest (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    if p (n + 1) then
      some (n + 1)
    else
      findLatest p n

/-- Correctness specification for `findLatest` with a boolean predicate `p`.
Either `findLatest p n = none` (meaning `p k = false` for all `k` with `1 ≤ k ≤ n`), or
`findLatest p n = some r` where `1 ≤ r ≤ n`, `p r = true`, and for all `k > r`
with `k ≤ n`, `p k = false`. -/
theorem findLatest_spec (p : Nat → Bool) (n : Nat) :
    (findLatest p n = none ∨
     ∃ r, findLatest p n = some r ∧ 1 ≤ r ∧ r ≤ n ∧ p r = true ∧ (∀ k, r < k → k ≤ n → p k = false)) ∧
    (findLatest p n = none → ∀ k, 1 ≤ k → k ≤ n → p k = false) := by
  induction n with
  | zero =>
    unfold findLatest
    exact ⟨by left; rfl, λ _ k hk1 hk2 => by omega⟩
  | succ n ih =>
    unfold findLatest
    by_cases hc : p (n + 1)
    · rw [if_pos hc]
      refine ⟨?_, ?_⟩
      · right; exact ⟨n + 1, rfl, by omega, by omega, hc, λ k hk1 hk2 => by omega⟩
      · intro h_contra; exact Option.noConfusion h_contra
    · rw [if_neg hc]
      rcases ih with ⟨h_cases, h_none⟩
      refine ⟨?_, ?_⟩
      · rcases h_cases with (h | h)
        · left; exact h
        · right
          rcases h with ⟨r, hr_eq, h1, h2, hPr, h_no⟩
          refine ⟨r, hr_eq, h1, ?_, hPr, ?_⟩
          · omega
          · intro k hk1 hk2
            rcases Nat.eq_or_lt_of_le hk2 with (rfl | hk_lt)
            · simpa using hc
            · have : k ≤ n := by omega
              exact h_no k hk1 this
      · intro h_res_none k hk1 hk2
        rcases Nat.eq_or_lt_of_le hk2 with (rfl | hk_lt)
        · simpa using hc
        · have : k ≤ n := by omega
          exact h_none h_res_none k hk1 this

/-- Extracts the specification from `findLatest_spec` when the result is `some r`.
Given `findLatest p n = some r`, we obtain `1 ≤ r`, `r ≤ n`, `p r = true`,
and `p k = false` for all `r < k ≤ n`. -/
lemma findLatest_some_spec {p : Nat → Bool} {n r : Nat} (h_eq : findLatest p n = some r) :
    1 ≤ r ∧ r ≤ n ∧ p r = true ∧ (∀ k, r < k → k ≤ n → p k = false) := by
  have h_spec := findLatest_spec p n
  rcases h_spec with ⟨h_cases, _⟩
  rcases h_cases with (h_none' | h_some)
  · rw [h_none'] at h_eq; injection h_eq
  · rcases h_some with ⟨r', hr'_eq, h1, h2, hPr, h_no⟩
    rw [h_eq] at hr'_eq
    have h_r_eq : r = r' := by injection hr'_eq
    subst h_r_eq
    exact ⟨h1, h2, hPr, h_no⟩

/-- Correctness specification for `findLatest` bridging to a `Prop` predicate `P`.
Useful when the property of interest is expressed as a `Prop` rather than a `Bool`.
The hypothesis `hP` relates the boolean check to `P`. -/
theorem findLatest_spec_prop {p : Nat → Bool} {P : Nat → Prop} (n : Nat)
    (hP : ∀ k, 1 ≤ k → k ≤ n → (p k = true ↔ P k)) :
    (findLatest p n = none ∨
     ∃ r, findLatest p n = some r ∧ 1 ≤ r ∧ r ≤ n ∧ P r ∧ (∀ k, r < k → k ≤ n → ¬ P k)) ∧
    (findLatest p n = none → ∀ k, 1 ≤ k → k ≤ n → ¬ P k) := by
  have h_spec := findLatest_spec p n
  rcases h_spec with ⟨h_cases, h_none⟩
  refine ⟨?_, ?_⟩
  · rcases h_cases with (h_none' | h_some)
    · left; exact h_none'
    · rcases h_some with ⟨r, hr_eq, h1, h2, hr_bool, h_no⟩
      have hPr : P r := ((hP r h1 h2).mp hr_bool)
      right; refine ⟨r, hr_eq, h1, h2, hPr, ?_⟩
      intro k hk1 hk2
      intro hPk
      have h_p_true : p k = true := ((hP k (by omega) (by omega)).mpr hPk)
      have h_p_false : p k = false := h_no k hk1 hk2
      rw [h_p_true] at h_p_false
      exact Bool.noConfusion h_p_false
  · intro h_none_res k hk1 hk2
    have h_bool_false : p k = false := h_none h_none_res k hk1 hk2
    have hP_iff := hP k hk1 hk2
    intro hPk
    have h_bool_true : p k = true := hP_iff.mpr hPk
    rw [h_bool_false] at h_bool_true
    exact Bool.noConfusion h_bool_true

/-- Bit length of a natural number: the minimum number of bits needed to represent `n`
in binary. Returns 1 for `n = 0` (representing the digit "0" as a single bit).
For `n > 0`, this is `Nat.log2 n + 1`. -/
def bitLen (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 1 + bitLen (n / 2)
termination_by n

/-- Bitwise complement of `n` within the given bit `width`.
`bitCompl width n = (2 ^ width - 1) - n`, i.e. flip all bits of `n` when using `width` bits. -/
def bitCompl (width n : Nat) : Nat := (2 ^ width) - 1 - n

/-- Bitwise complement of `n` using its natural bit length.
`bitwiseComplement n = (2 ^ bitLen n) - 1 - n`.
This flips all bits of `n` within its minimal binary representation.
For example, `bitwiseComplement 5 = 2` (since 5 = 101₂, complement = 010₂ = 2). -/
def bitwiseComplement (n : Nat) : Nat := bitCompl (bitLen n) n

/-- The `k`-th "all ones" number: `allOnes k = 2^k - 1`.
These are numbers whose binary representation consists of `k` ones:
0, 1, 3, 7, 15, 31, … (0, 1, 11, 111, 1111, 11111 in binary).

`allOnes 0 = 0`, and for `k ≥ 0`, `allOnes (k+1) = 2 * allOnes k + 1`.

This is the fundamental building block for `nextAllOnes` (which finds the next
all-ones number ≥ n) and `bitCompl` (which uses `2^width - 1` = `allOnes width`).

Generalized from `monobit_value` (LeetCode 3827). -/
def allOnes : Nat → Nat
  | 0 => 0
  | k+1 => 2 * allOnes k + 1

@[simp] lemma allOnes_zero : allOnes 0 = 0 := rfl

lemma allOnes_succ (k : Nat) : allOnes (k+1) = 2 * allOnes k + 1 := rfl

/-- The smallest number of the form `2 ^ k - 1` that is ≥ `n`, for any `n : ℕ`.
Numbers of the form `2^k - 1` have all bits set to `1` in binary (i.e., they are
"all-ones" numbers: 1, 3, 7, 15, 31, …). `nextAllOnes n` returns the next such
number that is at least `n`, computed as `2 ^ (Nat.log2 n + 1) - 1`.

For example:
- `nextAllOnes 0 = 1` (since `2^1 - 1 = 1`)
- `nextAllOnes 1 = 1` (since `1 = 2^1 - 1`)
- `nextAllOnes 2 = 3` (since `2^2 - 1 = 3`)
- `nextAllOnes 5 = 7` (since `2^3 - 1 = 7`)
- `nextAllOnes 7 = 7` (already an all-ones number)

Generalized from `next_all_set_bits` (LeetCode 3370). -/
def nextAllOnes (n : Nat) : Nat :=
  2 ^ (Nat.log2 n + 1) - 1

/-! ### Bounded universal quantifier

`allRange p start count` returns `true` iff `p k = true` for all `k`
in `[start, start + count)`. This is the boolean ∀ analog of `findFrom`:
while `findFrom` searches for the first `k` satisfying `p`, `allRange` checks
that *all* `k` in the range satisfy `p`. Useful in problems where every element
of a range must pass a check (e.g., "all levels from 1 to n are passable").

If `count = 0`, returns `true` (vacuously). -/

/-- Bounded universal boolean quantifier over a range of natural numbers.
`allRange p start count` checks whether `p k = true` for all `k` with
`start ≤ k < start + count`. -/
def allRange (p : Nat → Bool) (start count : Nat) : Bool :=
  match count with
  | 0 => true
  | count' + 1 => p start && allRange p (start + 1) count'

/-- Check if a predicate holds for all `i < n`. Returns `true` iff `p i = true` for every `i < n`.
This is a specialized version of `allRange` with `start = 0`: `forallLt p n = allRange p 0 n`.
Provides a direct recursive definition for easier induction. -/
def forallLt (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 => p n' && forallLt p n'

/-- `forallLt p n` is true iff `p i` is true for all `i < n`. -/
lemma forallLt_iff (p : Nat → Bool) (n : Nat) :
    forallLt p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero =>
    simp [forallLt]
  | succ n ih =>
    simp [forallLt, ih]
    constructor
    · rintro ⟨hp, h_forall⟩ i hi
      have : i < n ∨ i = n := by omega
      rcases this with (hi' | rfl)
      · exact h_forall i hi'
      · exact hp
    · intro h
      constructor
      · exact h n (by omega)
      · intro i hi
        exact h i (by omega)

/-- `allRange p start count` is true iff `p (start + k)` is true for all `k < count`. -/
lemma allRange_iff (p : Nat → Bool) (start count : Nat) :
    allRange p start count = true ↔ ∀ k, k < count → p (start + k) = true := by
  induction' count with count ih generalizing start
  · simp [allRange]
  · simp [allRange]
    constructor
    · rintro ⟨h_start, h_rest⟩ k hk
      by_cases hk_zero : k = 0
      · subst hk_zero; exact h_start
      · have ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk_zero
        subst hjk
        have hj_lt : j < count := Nat.lt_of_succ_lt_succ hk
        have h_eq : p (start + (j + 1)) = p ((start + 1) + j) := by
          simp [add_comm, add_left_comm, add_assoc]
        rw [h_eq]
        exact ((ih (start + 1)).mp h_rest) j hj_lt
    · intro H
      constructor
      · exact H 0 (by omega)
      · apply (ih (start + 1)).mpr
        intro k hk
        have : start + (k + 1) = (start + 1) + k := by omega
        rw [← this]
        exact H (k + 1) (by omega)

/-! ### 1-indexed universal boolean quantifier

`allOneTo p n` returns `true` iff `p k = true` for all `k` with `1 ≤ k ≤ n`.
This is the 1-indexed variant of `forallLt` and can be expressed as `allRange p 1 n`.
The direct recursive definition is convenient for induction and structurally matches
the common pattern `∀ v, 1 ≤ v → v ≤ n → P v` (e.g., LeetCode 2206 "Divide Array Into
Equal Pairs", CF problems with bounded range checks). -/

/-- Check that `p k = true` for all `k` with `1 ≤ k ≤ n`.
`allOneTo p 0 = true` (vacuously true).
Generalized from `all_satisfy_range` (LeetCode 2206). -/
def allOneTo (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => p (n+1) && allOneTo p n

/-- `allOneTo p n` is true iff `p v` is true for all `v` with `1 ≤ v ≤ n`. -/
lemma allOneTo_iff (p : Nat → Bool) (n : Nat) :
    allOneTo p n = true ↔ (∀ v, 1 ≤ v → v ≤ n → p v = true) := by
  induction n with
  | zero =>
    constructor
    · intro h v h1 hle
      have hzero : v = 0 := Nat.eq_zero_of_le_zero hle
      subst hzero
      omega
    · intro h; rfl
  | succ n ih =>
    constructor
    · intro h
      dsimp [allOneTo] at h
      simp at h
      rcases h with ⟨hcv, hrest⟩
      intro v h1 hle
      have hcases : v ≤ n ∨ v = n+1 := by omega
      rcases hcases with (hle' | heq)
      · exact (ih.mp hrest) v h1 hle'
      · subst heq; exact hcv
    · intro h
      have hcv : p (n+1) = true := h (n+1) (by omega) (le_refl _)
      have hrest : ∀ v, 1 ≤ v → v ≤ n → p v = true := by
        intro v h1' hle'
        exact h v h1' (Nat.le_succ_of_le hle')
      have hrest' : allOneTo p n = true := ih.mpr hrest
      dsimp [allOneTo]
      simp [hcv, hrest']

/-! ### K-th element search

`findKth p bound k i cur` finds the `k`-th natural number (1-indexed) in the inclusive
range `[i, bound]` satisfying predicate `p`. `cur` is the count of matches found among
numbers `< i`. Returns `some i` if the k-th match is found, `none` if fewer than `k`
matches exist in `[i, bound]`.

This is a "select by ordinal position" search: while `findFrom` finds the *first* match,
`findKth` finds the *k-th* match. Common in problems like "k-th factor" (LC 1492)
or "k-th beautiful number". -/

/-- Find the `k`-th natural number (1-indexed) in the inclusive range `[i, bound]`
satisfying predicate `p`. `cur` is the count of matches found among numbers `< i`.
Returns `some i` if the k-th match is found, `none` if fewer than `k` matches exist
in `[i, bound]`. -/
def findKth (p : Nat → Bool) (bound k i cur : Nat) : Option Nat :=
  if h : i ≤ bound then
    if p i then
      let cur' := cur + 1
      if hk : cur' = k then
        some i
      else
        findKth p bound k (i+1) cur'
    else
      findKth p bound k (i+1) cur
  else
    none
termination_by (bound + 1) - i
decreasing_by
  all_goals omega

/-! ### Lower-bound and divisibility predicate

`le_and_dvd` checks whether a value is at least a lower bound and divisible by a divisor.
This combines two common constraints in contest problems: a minimum value requirement
and a divisibility/multiplicity condition (e.g., CF 4A "Watermelon" where `4 ≤ w ∧ 2 ∣ w`). -/

/-- Boolean predicate: `le_and_dvd lower divisor value` returns `true` iff
`lower ≤ value ∧ divisor ∣ value`. Useful for checking candidate values against
combined lower-bound and divisibility constraints. -/
def le_and_dvd (lower divisor value : Nat) : Bool :=
  decide (lower ≤ value ∧ divisor ∣ value)

/-! ### Resource-allocation combinator

`minPairMinSumDiv a b k = min (min a b) ((a + b) / k)` computes the minimum of
the pairwise minimum of `a` and `b` and their sum divided by `k`.
This pattern appears in resource-allocation problems where a quantity is bounded both
by individual limits (`min a b`) and by the total limit averaged over `k` (`(a + b) / k`).
For example, with `k = 3`, it gives the maximum number of teams that can be formed
from two groups (each team needs at least one from each group and three people total). -/

/-- `minPairMinSumDiv a b k = min (min a b) ((a + b) / k)`.
Bounded both by individual minimum and total-averaged sum. -/
def minPairMinSumDiv (a b k : Nat) : Nat :=
  min (min a b) ((a + b) / k)

/-- `minPairMinSumDiv a b k ≤ a` — the result is bounded above by the first argument. -/
lemma minPairMinSumDiv_le_fst (a b k : Nat) : minPairMinSumDiv a b k ≤ a := by
  dsimp [minPairMinSumDiv]
  have h1 : min (min a b) ((a + b) / k) ≤ min a b := Nat.min_le_left _ _
  have h2 : min a b ≤ a := Nat.min_le_left _ _
  exact le_trans h1 h2

/-! ### Pair sum divisibility

`pairSumDivisible a b d` checks whether the sum `a + b` is divisible by `d`.
This is a reusable predicate for counting pairs whose sum satisfies a congruence
condition, commonly used in problems like "Pairs of Songs With Total Durations
Divisible by 60" (LC 1010) and similar divisibility-based pair-counting problems. -/

/-- `(a + b) % d = 0` as a boolean predicate. -/
def pairSumDivisible (a b d : Nat) : Bool := (a + b) % d = 0

/-! ### Prime predicate

`isPrime_specificDuplicate n` tests whether `n` is prime as a `Bool`, using `Nat.Prime`.
This bridges the `Prop`-based `Nat.Prime` to `Bool` via `decide`, making it
usable in `if` conditions and boolean filters (e.g., `Finset.filter isPrime_specificDuplicate`). -/

/-- Boolean predicate: `isPrime_specificDuplicate n` returns `true` iff `n` is a prime number. -/
def isPrime_specificDuplicate (n : Nat) : Bool :=
  decide (Nat.Prime n)

/-! ### Proper divisor predicate

`isProperDivisor` checks whether a number is a proper divisor of another:
`x` is a proper divisor of `n` when `1 ≤ x < n` and `x` divides `n`.
This is a boolean version of the standard number-theoretic concept, useful
in combinatorial game problems (e.g., LeetCode 1025 "Divisor Game") where
moves consist of choosing a proper divisor. -/

/-- Boolean predicate: `isProperDivisor n x` returns `true` iff `x` is a proper
positive divisor of `n` (i.e., `1 ≤ x`, `x < n`, and `x ∣ n`). -/
def isProperDivisor (n x : Nat) : Bool :=
  decide (1 ≤ x ∧ x < n ∧ x ∣ n)

/-- `isProperDivisor n x` implies `0 < x`. -/
lemma isProperDivisor.pos_of {n x : Nat} (h : isProperDivisor n x = true) : 0 < x := by
  unfold isProperDivisor at h
  have h' := of_decide_eq_true h
  rcases h' with ⟨hle, _, _⟩
  omega

/-- `isProperDivisor n x` implies `x < n`. -/
lemma isProperDivisor.lt_of {n x : Nat} (h : isProperDivisor n x = true) : x < n := by
  unfold isProperDivisor at h
  have h' := of_decide_eq_true h
  rcases h' with ⟨_, hlt, _⟩
  exact hlt

/-- `isProperDivisor n x` implies `x ∣ n`. -/
lemma isProperDivisor.dvd_of {n x : Nat} (h : isProperDivisor n x = true) : x ∣ n := by
  unfold isProperDivisor at h
  have h' := of_decide_eq_true h
  rcases h' with ⟨_, _, h_dvd⟩
  exact h_dvd

/-! ### Proper divisor sum

`sumProperDivisorsUpTo n k` recursively sums all proper divisors of `n` that are ≤ `k`.
When `k = n - 1`, this computes the aliquot sum (sum of all proper divisors), which
is the key computation in perfect-number problems (LC 507 "Perfect Number") and
amicable-number problems.

Uses `isProperDivisor` internally: a proper divisor `d` of `n` satisfies `1 ≤ d < n` and `d ∣ n`.
The recursion terminates on `k`, scanning downward from `k` to `0`. -/

/-- Sum all proper divisors of `n` that are ≤ `k`.
`sumProperDivisorsUpTo n (n-1)` equals the aliquot sum of `n`. -/
def sumProperDivisorsUpTo (n k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 =>
    if isProperDivisor n (k' + 1) then
      (k' + 1) + sumProperDivisorsUpTo n k'
    else
      sumProperDivisorsUpTo n k'
termination_by k

/-! ### Digit sum and product

`digitSumBounded n d` computes the sum of the last `d` decimal digits of `n`.
`digitProductBounded n d` computes the product of the last `d` decimal digits of `n`.
`digitSum_specificDuplicate n` computes the full decimal digit sum of `n` (as an `Int`).
`decimalDigitSum n` computes the full decimal digit sum of `n` (as a `Nat`).

These are building blocks for problems where the digits of a number need to be
individually manipulated (e.g., LeetCode 1281 "Subtract the Product and Sum of Digits").
-/

/-- Sum of the last `digits` decimal digits of `n`.
For example, `digitSumBounded 12345 3 = 12` because `3 + 4 + 5 = 12`.
The recursion terminates on the digit count, not on `n`, making proofs simpler:
each step extracts one digit via `n % 10` and recurses on `n / 10` with one fewer digit. -/
def digitSumBounded (n : Nat) : Nat → Int
  | 0 => 0
  | digits+1 => (n % 10 : Int) + digitSumBounded (n / 10) digits

/-- Product of the last `digits` decimal digits of `n`.
For example, `digitProductBounded 12345 3 = 60` because `3 * 4 * 5 = 60`.
Like `digitSumBounded`, the recursion terminates on the digit count. -/
def digitProductBounded (n : Nat) : Nat → Int
  | 0 => 1
  | digits+1 => (n % 10 : Int) * digitProductBounded (n / 10) digits

/-- Sum of all decimal digits of `n`.
Uses `digitSumBounded` with a bound equal to the number of decimal digits of `n`
(`Nat.log 10 n + 1`), which is sufficient to cover all digits.
For `n ≤ 100000` this matches the common "bounded to 6" pattern seen in LeetCode problems. -/
def digitSum_specificDuplicate (n : Nat) : Int := digitSumBounded n (Nat.log 10 n + 1)

/-- Sum of all decimal digits of `n`, as a `Nat`. Recurses by extracting the last digit
via `n % 10` and recursing on `n / 10`. Returns `0` for `n = 0`.
For example, `decimalDigitSum 12345 = 15` because `1 + 2 + 3 + 4 + 5 = 15`.
This is the simplest `Nat → Nat` decimal digit sum; see `digitSum_specificDuplicate` for the `Int`-valued version,
`digitSumBounded` for the bounded-digit-count version, and `Nat/DigitSum` for
base-parameterized versions. -/
def decimalDigitSum (n : Nat) : Nat :=
  if h : n = 0 then 0
  else (n % 10) + decimalDigitSum (n / 10)
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-! ### Decimal digit at a given place value

`digitAt n place` extracts the decimal digit of `n` at a given place value `place`.
For example, `digitAt 1234 100 = 2` (the hundreds digit) and
`digitAt 1234 1 = 4` (the units digit).

The computation is `(n / place) % 10`; the divisor `place` is typically `1, 10, 100, …`.
This is effectively extracting the digit in a hardcoded base-10 representation
using a divisor rather than the more direct positional-index approach.
-/

/-- Extract the decimal digit of `n` at divisor `place`: `digitAt n place = (n / place) % 10`.
For example, `digitAt 1234 100 = 2` and `digitAt 1234 1 = 4`.
Typically `place` is a power of ten (`1, 10, 100, …`). -/
def digitAt (n place : Nat) : Nat := (n / place) % 10

/-- Count the number of decimal digits of `n`. Returns `1` for `n = 0`
(since `0` is a single digit).
For example, `digitCount 0 = 1`, `digitCount 5 = 1`, `digitCount 123 = 3`.
This is a simpler variant of `countDigits` that counts all digits unconditionally;
for all `n`, `digitCount n = Nat.log 10 n + 1`. -/
def digitCount (n : Nat) : Nat :=
  if n < 10 then 1
  else 1 + digitCount (n / 10)
termination_by n

/-- Remove all trailing zeros from the decimal representation of `n`.
For example, `stripTrailingZeros 1200 = 12`, `stripTrailingZeros 0 = 0`,
`stripTrailingZeros 5 = 5`.

Useful for normalizing numbers after operations that may introduce trailing zeros,
such as lexicographic ordering or digit manipulation. -/
def stripTrailingZeros (n : Nat) : Nat :=
  if n % 10 = 0 ∧ n ≠ 0 then
    stripTrailingZeros (n / 10)
  else
    n
termination_by n

/-! ### Minimum predicate with default

`leastNatOrZero p` returns the least natural number `k` such that `p k` holds,
or `0` if no such number exists. This is a default-valued version of `Nat.find`,
commonly used in competitive programming when the result must be a valid natural
number even when no witness exists. -/

/-- The least natural number satisfying `p`, or `0` if no number satisfies `p`.
This is a default-valued version of `Nat.find`.
Example: `leastNatOrZero (fun k => k > 3)` = `4`. -/
noncomputable def leastNatOrZero (p : Nat → Prop) : Nat := by
  classical
  exact if h : ∃ k, p k then Nat.find h else 0

/-- If `p m` holds and `p` has at least one witness, then `leastNatOrZero p ≤ m`.
This is the minimum property: `leastNatOrZero` finds the smallest witness. -/
lemma leastNatOrZero_min (p : Nat → Prop) (h : ∃ k, p k) {m : Nat} (hm : p m) :
    leastNatOrZero p ≤ m := by
  classical
  simp only [leastNatOrZero, dif_pos h]
  exact Nat.find_min' h hm

/-! ### `findGreatest` case analysis

`Nat.findGreatest P bound` finds the largest `k ≤ bound` such that `P k` holds,
or returns `0` if no such `k` exists. The following lemma provides a convenient
case split on the result. -/

/-- The result of `Nat.findGreatest P bound` is either `0` or satisfies `P`.
This is a convenient case-analysis lemma: any nonzero result of `findGreatest`
must satisfy the predicate (by `Nat.findGreatest_of_ne_zero`), while a zero
result may occur when no `k ≤ bound` satisfies `P`. -/
lemma findGreatest_eq_zero_or_property {P : ℕ → Prop} [DecidablePred P] {bound : ℕ} :
    let result := findGreatest P bound
    result = 0 ∨ P result := by
  intro result
  by_cases hzero : result = 0
  · exact Or.inl hzero
  · exact Or.inr (Nat.findGreatest_of_ne_zero (P := P) rfl hzero)

/-! ### `maxSatisfyingLength` — largest index ≤ bound satisfying a Bool predicate

`maxSatisfyingLength bound satisfies` finds the largest `k ≤ bound` such that
`satisfies k = true`. This is a convenience wrapper around `Nat.findGreatest`
that handles the `Bool` → `Prop` conversion automatically via `= true`.

Unlike `findMaxSatisfying`, which scans backward from a given `n`, this uses
the built-in `Nat.findGreatest` and takes an explicit `bound` argument.
Both compute the same result for the same predicate and bound. -/

/-- The largest `len ≤ bound` such that `satisfies len = true`, or `0` if no
such `len` exists. Wraps `Nat.findGreatest (fun len => satisfies len = true) bound`. -/
def maxSatisfyingLength (bound : Nat) (satisfies : Nat → Bool) : Nat :=
  Nat.findGreatest (fun len => satisfies len = true) bound

/-- If `len ≤ bound` and `satisfies len = true`, then
`len ≤ maxSatisfyingLength bound satisfies`. -/
lemma maxSatisfyingLength_is_max {satisfies : Nat → Bool} (bound len : Nat)
    (hlen : len ≤ bound) (hmatch : satisfies len = true) :
    len ≤ maxSatisfyingLength bound satisfies := by
  by_contra hnot
  have hlt : maxSatisfyingLength bound satisfies < len := Nat.lt_of_not_ge hnot
  have hg := (Nat.findGreatest_eq_iff (P := fun n => satisfies n = true)
    (k := bound) (m := maxSatisfyingLength bound satisfies)).1 rfl
  exact (hg.2.2 hlt hlen) hmatch

/-! ### `Nat.find` as an `Int`

These lemmas bridge `Nat.find` (which returns a `Nat`) to `Int` for use in
contexts where arithmetic operations or comparisons are done in `ℤ`. -/

/-- If `P` has a witness in `Nat`, then `(Nat.find hex : ℤ)` is nonnegative,
satisfies `P`, and is a minimal `Int` among all natural-number witnesses.
This bundles the three core properties of `Nat.find` — the specification, the
minimality, and the nonnegativity of the integer cast — into a single lemma,
useful when the rest of the proof works in `ℤ`. -/
lemma nat_find_int_minimizer {P : Nat → Prop} [DecidablePred P] (hex : ∃ n, P n) :
    0 ≤ ((Nat.find hex : Nat) : Int) ∧
      P (Nat.find hex) ∧
      ∀ n : Nat, P n → ((Nat.find hex : Nat) : Int) ≤ (n : Int) := by
  refine ⟨by exact_mod_cast Nat.zero_le (Nat.find hex), Nat.find_spec hex, ?_⟩
  intro n hn
  exact_mod_cast Nat.find_min' hex hn

/-- If the least witness of `p` is positive, then its predecessor does not satisfy `p`.
This follows from the minimality property of `Nat.find`: `Nat.find h - 1` is strictly
less than `Nat.find h`, so `Nat.find_min` applies. -/
lemma find_prev_minimal {p : Nat → Prop} [DecidablePred p] (h : ∃ k, p k) (hpos : 0 < Nat.find h) :
    ¬p (Nat.find h - 1) := by
  apply Nat.find_min h
  omega

/-- The minimality property of `Nat.find` specialized to `≥` predicates, returning `<` instead of `¬ ≥`.
Given `hex : ∃ r, f r ≥ n`, for any `r < Nat.find hex`, we have `f r < n`.
This is a convenient reformulation of `Nat.find_min` that avoids the double negation
`¬ (f r ≥ n)` and directly gives a strict inequality. -/
lemma find_min_lt {f : Nat → α} [LinearOrder α] {n : α} (hex : ∃ r, f r ≥ n) (r : Nat)
    (hr : r < Nat.find hex) : f r < n := by
  have h_not_ge : ¬ (f r ≥ n) := Nat.find_min hex hr
  exact lt_of_not_ge h_not_ge

/-- If there exists an `n` such that `p n` holds, but `p 0` does not hold,
then `1 ≤ Nat.find h_exists`. In other words, the minimal witness is at least 1.
This is useful when the first candidate (0) is known not to satisfy the predicate,
so the search for the minimal witness can skip it. -/
lemma find_one_le {p : ℕ → Prop} [DecidablePred p] (h_exists : ∃ n, p n) (h0 : ¬ p 0) :
    1 ≤ Nat.find h_exists := by
  have hpos : 0 < Nat.find h_exists := by
    by_contra! H
    have hzero : Nat.find h_exists = 0 := by omega
    have hp0 : p 0 := by simpa [hzero] using Nat.find_spec h_exists
    exact h0 hp0
  omega

/-! ### Subtraction and addition lemmas

These lemmas connect subtraction and addition for natural numbers,
common in proofs where indices are bounded by subtraction or where
sums are bounded by combining subtraction inequalities. -/

/-- If `1 ≤ a`, then `1 + b - a ≤ b`.
In `Nat`, subtraction truncates at 0. When `a ≤ 1 + b`, this is `(1 + b) - a ≤ b`;
when `a > 1 + b`, the LHS is `0` and the inequality is trivial.
Useful for bounding intermediate terms in arithmetic computations
(e.g., proving an upper bound on `2 * (1 + n/2 - f (n/2))`). -/
lemma one_add_sub_le_of_one_ge {a b : Nat} (ha : 1 ≤ a) : 1 + b - a ≤ b := by omega

/-- If `b < bound`, then `b - a ≤ bound`. -/
lemma sub_le_of_lt {a b bound : Nat} (hb : b < bound) : b - a ≤ bound :=
  (Nat.sub_le b a).trans (Nat.le_of_lt hb)

/-- `n - 1 - b ≤ n`. This is the composition of two `Nat.sub_le` bounds:
`n - 1 - b ≤ n - 1 ≤ n`. Useful when `b` is an index and `n` is a list length,
so `n - 1 - b` is always bounded by the length. -/
lemma sub_sub_le (n b : Nat) : n - 1 - b ≤ n := by
  have h1 : n - 1 - b ≤ n - 1 := Nat.sub_le (n - 1) b
  have h2 : n - 1 ≤ n := Nat.sub_le n 1
  exact Nat.le_trans h1 h2

/-- If `a ≤ b` as natural numbers, then `0 ≤ (b : ℤ) - (a : ℤ)`.
This connects the natural-number ordering to the nonnegativity of
the difference when both values are cast to `ℤ`. Useful for proving
lower bounds on integer results derived from natural-number comparisons. -/
lemma sub_nonneg_of_nat_le {a b : Nat} (h : a ≤ b) : 0 ≤ (b : ℤ) - (a : ℤ) := by
  omega

/-- For any natural numbers `a, b`, `(b : ℤ) - (a : ℤ) ≤ (b : ℤ)`.
Since `(a : ℤ) ≥ 0`, subtracting it never increases the value.
Useful for proving upper bounds on integer results derived from
natural-number subtraction. -/
lemma sub_le_left_of_nat {a b : Nat} : (b : ℤ) - (a : ℤ) ≤ (b : ℤ) := by
  omega

/-! ### Decimal digit reversal

Reversing the decimal digits of a natural number. The core is a tail-recursive
accumulator-based helper `reverseDigitsAux`, wrapped by `reverseDigits` which
initializes the accumulator to `0`.

This is used in problems like "reverse integer" (LC 7), "palindrome number" (LC 9),
and "a number after a double reversal" (LC 2119).
-/

/-- Tail-recursive helper for `reverseDigits`. Computes the reverse of `n`'s decimal
digits with accumulator `acc`. At each step, the least significant digit of `n` is
extracted via `n % 10` and prepended to the accumulator via `acc * 10 + n % 10`,
while `n` is shifted right via `n / 10`.

Example: `reverseDigitsAux 123 0 = 321`. -/
def reverseDigitsAux (n acc : Nat) : Nat :=
  if h : n = 0 then acc
  else reverseDigitsAux (n / 10) (acc * 10 + n % 10)
termination_by n
decreasing_by
  have hn : 0 < n := Nat.pos_of_ne_zero h
  exact Nat.div_lt_self hn (by decide)

/-- Reverse the decimal digits of `n`. For example, `reverseDigits 123 = 321`,
`reverseDigits 100 = 1` (leading zeros are dropped), `reverseDigits 0 = 0`. -/
def reverseDigits (n : Nat) : Nat :=
  reverseDigitsAux n 0

/-! ### Nat.sqrt lemmas with ℤ cast

These lemmas bridge `Nat.sqrt` bounds to `ℤ`, useful when working with integer
arithmetic on natural-number square roots (e.g., in LeetCode bulb-switch problems). -/

/-- For any `n : ℕ`, the square of `Nat.sqrt n` cast to `ℤ` is ≤ `n` cast to `ℤ`.
This lifts `Nat.sqrt_le n` from `ℕ` to `ℤ` via `mod_cast`, also distributing the
cast over multiplication. -/
lemma sqrt_mul_self_le_int_cast {n : ℕ} : (Nat.sqrt n : ℤ) * (Nat.sqrt n : ℤ) ≤ (n : ℤ) := by
  have h := Nat.sqrt_le n
  calc
    (Nat.sqrt n : ℤ) * (Nat.sqrt n : ℤ) = ((Nat.sqrt n * Nat.sqrt n : ℕ) : ℤ) := by simp
    _ ≤ (n : ℤ) := by exact mod_cast h

/-! ### Power-of-base check

`isPowerOfBase base n` checks whether `n` is an exact power of `base`.
Uses the identity: `n` is a power of `base` (for `base > 1`, `n > 0`) iff
`n = base ^ Nat.log base n`. This is a sharp boolean test: for `n = 0`, returns
`false` (since `0^0 = 1 ≠ 0`); for `n = 1`, returns `true` for any `base`
(since `base^0 = 1`).

Generalized from `spec_is_power_of_three` (LeetCode 326 "Power of Three"). -/

/-- Check if `n` is an exact power of `base`: `n = base ^ k` for some `k`.
Uses `Nat.log` for efficient computation: `n` is a power of `base` iff
`n == base ^ Nat.log base n`. -/
def isPowerOfBase (base n : Nat) : Bool :=
  n == base ^ Nat.log base n

/-! ### Iterative Fibonacci

These functions compute Fibonacci numbers using a tail-recursive (iterative)
approach with two accumulators `a` and `b`. Starting with `a = 0, b = 1`, the
function `fibIter 0 1 n` returns the nth Fibonacci number (with the convention
`F(0) = 0, F(1) = 1`).

Generalized from `fib_iter` in LeetCode 509 "Fibonacci Number".
-/

/-- Iterative (tail-recursive, two-accumulator) Fibonacci:
`fibIter a b n` computes `a * F(n) + b * F(n+1)` where `F(0) = 0, F(1) = 1`
and `F(n+2) = F(n) + F(n+1)`. In particular, `fibIter 0 1 n = F(n)`. -/
def fibIter (a b : Nat) : Nat → Nat
  | 0 => a
  | n+1 => fibIter b (a + b) n

@[simp] lemma fibIter_zero (a b : Nat) : fibIter a b 0 = a := rfl

lemma fibIter_succ (a b n : Nat) : fibIter a b (n + 1) = fibIter b (a + b) n := rfl

/-! ### Integer bounds as `ℕ` constants

These mirror the `Int.i32*` / `Int.i64*` bounds from `general/Int/Bounded.lean`,
lifted to `ℕ`. They are convenient when the bound is used in `Nat`-typed
preconditions (e.g., `1 ≤ a ∧ a ≤ i32Max`). -/

/-- Maximum value of a signed 32-bit integer, as a `Nat` (same value as `Int.i32Max`).
Equivalent to `2^31 - 1`. -/
def i32Max : Nat := 2147483647

/-! ### Binary search midpoint

The safe midpoint formula `lo + (hi - lo) / 2` avoids overflow compared to
the naive `(lo + hi) / 2`. These lemmas bound the midpoint within `[lo, hi]`
when `lo ≤ hi`. For `Int`-valued versions, see `Int.mid_lt_right` and
`Int.lt_mid_left`. -/

/-- The safe binary search midpoint: `lo + (hi - lo) / 2`.
This avoids integer overflow in languages with fixed-width integers,
though in Lean's `Nat` it's equivalent to `(lo + hi) / 2` when `lo ≤ hi`. -/
def midPoint (lo hi : Nat) : Nat := lo + (hi - lo) / 2

/-- In binary search, the midpoint `midPoint lo hi` is at most `hi`
when `lo ≤ hi`. -/
lemma midPoint_le_hi (lo hi : Nat) (h : lo ≤ hi) : midPoint lo hi ≤ hi := by
  unfold midPoint
  omega

/-- The midpoint `midPoint lo hi` is always at least `lo`. -/
lemma lo_le_midPoint (lo hi : Nat) : lo ≤ midPoint lo hi := by
  unfold midPoint
  omega

end Nat
