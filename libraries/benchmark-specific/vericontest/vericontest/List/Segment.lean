import Mathlib

open List

/-!
# Segment operations on lists

Operations that compute values over index ranges `[start, stop)` of a list,
including segment extraction, segment maximum, and related theorems.
-/

namespace List

/-! ### Slice extraction -/

/-- Extract a contiguous slice_specificDuplicate from a list. `slice_specificDuplicate xs start stop` returns elements
at indices `i` where `start ≤ i` and `i < stop`.

Equivalent to `(xs.take stop).drop start`. For `start ≥ stop`, returns `[]`.
This generalizes `sublist_slice` from LeetCode 2913 to any type. -/
def slice_specificDuplicate {α : Type u} (xs : List α) (start stop : Nat) : List α :=
  (xs.take stop).drop start

/-- When `start = 0`, `slice_specificDuplicate xs 0 stop = xs.take stop`. -/
@[simp]
lemma slice_zero (xs : List α) (stop : Nat) : slice_specificDuplicate xs 0 stop = xs.take stop := by
  simp [slice_specificDuplicate]

/-- When `start ≥ stop`, `slice_specificDuplicate xs start stop = []`. -/
lemma slice_of_ge (xs : List α) (start stop : Nat) (h : start ≥ stop) : slice_specificDuplicate xs start stop = [] := by
  unfold slice_specificDuplicate
  apply List.drop_eq_nil_of_le
  have htake_len : (xs.take stop).length ≤ stop :=
    List.length_take_le stop xs
  exact le_trans htake_len h

/-! ### Segment maximum -/

/-- The maximum value in the segment `[start, stop)` of a list, using `default` for empty segments.
`segmentMax default s start stop` computes the maximum of `(s[start]?).getD default` through
`(s[stop-1]?).getD default` (inclusive). Returns `default` if `start ≥ stop` (empty segment).

This is the segment analogue of `prefixMax_specificDuplicate` and `suffixMax_specificDuplicate`, and generalizes the
`spec_max` pattern (LeetCode 1299) to any `LinearOrder` type with an explicit default. -/
def segmentMax [LinearOrder α] (default : α) (s : List α) (start stop : Nat) : α :=
  if start ≥ stop then
    default
  else
    let cur := (s[start]?).getD default
    if stop - start = 1 then
      cur
    else
      max cur (segmentMax default s (start + 1) stop)
termination_by stop - start
decreasing_by
  simp_wf
  omega

/-- When `start ≥ stop`, the segment is empty and `segmentMax` returns `default`. -/
@[simp]
lemma segmentMax_of_ge_start_stop [LinearOrder α] (default : α) (s : List α) (start stop : Nat)
    (h : start ≥ stop) : segmentMax default s start stop = default := by
  unfold segmentMax; simp [h]

/-- When the segment has exactly one element (`stop - start = 1`), `segmentMax` returns that element
(or `default` if out of bounds via `getD`). -/
lemma segmentMax_single [LinearOrder α] (default : α) (s : List α) (start stop : Nat)
    (h_start_lt : start < stop) (h_one : stop - start = 1) :
    segmentMax default s start stop = (s[start]?).getD default := by
  unfold segmentMax
  simp [Nat.not_le.mpr h_start_lt, h_one]

/-! ### Cons-shift lemma for segmentMax -/

/-- Shifting the list by one (dropping the head `x`) and adjusting both bounds by `+1`
preserves `segmentMax`. That is, the maximum in `(x :: xs)[start+1 .. stop)` equals
the maximum in `xs[start .. stop)`.

This is the key structural lemma for `segmentMax` on cons lists and directly generalizes
`summary_cons_shift` from LeetCode 1299. -/
theorem segmentMax_cons_shift [LinearOrder α] (default : α) (x : α) (xs : List α) (start stop : Nat)
    (h_start : start ≤ stop) (h_stop : stop ≤ xs.length) :
    segmentMax default (x :: xs) (start + 1) (stop + 1) = segmentMax default xs start stop := by
  by_cases h_eq : start = stop
  · subst stop
    unfold segmentMax
    simp
  have h_start_lt : start < stop := by omega
  induction h : stop - start using Nat.strong_induction_on generalizing start stop with
  | h n ih =>
      conv_lhs => unfold segmentMax
      conv_rhs => unfold segmentMax
      have h_start' : start + 1 < stop + 1 := by omega
      simp only [Nat.not_le.mpr h_start', Nat.not_le.mpr h_start_lt, ↓reduceIte]
      have h_access : ((x :: xs)[start + 1]?).getD default = (xs[start]?).getD default := by
        simp only [List.getElem?_cons_succ]
      rw [h_access]
      by_cases h_one : stop - start = 1
      · have h_one' : (stop + 1) - (start + 1) = 1 := by omega
        simp only [h_one, h_one', ↓reduceIte]
      · have h_one' : (stop + 1) - (start + 1) ≠ 1 := by omega
        simp only [h_one, h_one', ↓reduceIte]
        have hrec := ih (stop - (start + 1)) (by omega) (start + 1) stop
          (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [hrec]

/-! ### Range sum with `ℤ` indices

`segmentSum_specificDuplicate` (in `general.List`) computes segment sums via `(start, len)` with `ℕ` indices.
`rangeSum` below is the `ℤ`-indexed counterpart: it sums over `[start, e)` and returns
`0` for out-of-bounds or empty ranges. `ℤ` indices allow natural handling of `left - 1`
and similar offsets common in competitive programming. -/

/-- Sum of elements in the range `[start, e)` of a list, using `ℤ` indices.
Returns `0` if `start ≥ e` (empty range) or if all indices are out of bounds.
Out-of-bounds elements contribute `0` via `getD`.

See `List.segmentSum_specificDuplicate` for the `ℕ`-indexed `(start, len)` version. -/
def rangeSum {α : Type} [AddMonoid α] (s : List α) (start : ℤ) (e : ℤ) : α :=
  if start < e then
    (s[start.toNat]?).getD 0 + rangeSum s (start + 1) e
  else 0
termination_by (e - start).toNat

/-! ### All subarray sums -/

/-- All contiguous subarray sums starting at index `start` with end positions from `e`
to the end of `nums`. When called with `e = start + 1`, this generates the sums of all
subarrays that start at `start` (with lengths 1, 2, …, up to the list bound). -/
def subarraySumsFrom {α : Type} [AddMonoid α] (nums : List α) (start : ℤ) (e : ℤ) : List α :=
  if start < e ∧ e ≤ (nums.length : ℤ) then
    rangeSum nums start e :: subarraySumsFrom nums start (e + 1)
  else []
termination_by ((nums.length : ℤ) + 1 - e).toNat

/-- All contiguous subarray sums of `nums`, in order of increasing start index.
`allSubarraySums_specificDuplicate nums i` generates the sums of all subarrays whose start index is
`≥ i`. Call with `i = 0` to obtain every contiguous subarray sum. -/
def allSubarraySums_specificDuplicate {α : Type} [AddMonoid α] (nums : List α) (i : ℤ) : List α :=
  if i < (nums.length : ℤ) then
    subarraySumsFrom nums i (i + 1) ++ allSubarraySums_specificDuplicate nums (i + 1)
  else []
termination_by ((nums.length : ℤ) - i).toNat

/-! ### Inclusive range sum via `getD`

`sumFromTo s start stop` computes `∑_{k=start}^{stop} (s[k]?).getD 0` —
the sum of elements at indices `start` through `stop` (inclusive), using `getD 0`
for safe out-of-bounds access. Returns `0` when `start > stop`.

This is the recursive, `getD`-based counterpart of `sumSlice` and `sublistSum`,
providing an alternative implementation strategy for range-summation proofs and
algorithms that need to reason about the sum element-by-element (e.g., DP
recurrences over intervals). -/

/-- Sum of elements from index `start` to `stop` (inclusive) using `getD 0`.
`sumFromTo s start stop = ∑_{k=start}^{stop} (s[k]?).getD 0`.
Returns `0` when `start > stop`. -/
def sumFromTo {α : Type} [AddCommMonoid α] (s : List α) (start stop : Nat) : α :=
  if start ≤ stop then
    (s[start]?).getD 0 + sumFromTo s (start + 1) stop
  else
    0
termination_by stop + 1 - start
decreasing_by
  omega

/-- Sum of elements in the inclusive range `[left, right]` of list `l`:
`inclusiveSum l left right = ∑_{i=left}^{right} l[i]` (or fewer elements if the list is
shorter than `right + 1`).

Implemented via `drop`-then-`take` for direct use of `List.sum` lemmas:
`inclusiveSum l left right = ((l.drop left).take (right - left + 1)).sum`.

This is the inclusive-range analogue of `segmentSum_specificDuplicate` (which uses `(start, len)`)
and `sumFromTo` (which uses `getD`-based recursion). Equivalent to
`segmentSum_specificDuplicate l left (right - left + 1)`.

Note: due to `Nat` subtraction, `right - left` is `0` when `left > right`, so
the behavior may be unexpected in that case. Use `sumFromTo` if you need a
well-defined result for `left > right` (returns `0`). -/
def inclusiveSum {α : Type u} [AddCommMonoid α] (l : List α) (left right : ℕ) : α :=
  ((l.drop left).take (right - left + 1)).sum

/-! ### Range predicates -/

/-- `allInRange_specificDuplicate xs lo hi` asserts that every element of `xs` lies between `lo` and `hi`
inclusive, i.e., `lo ≤ x ∧ x ≤ hi` for all `x ∈ xs`.

This is a reusable list predicate that generalizes the precondition pattern from
LeetCode 2032 ("Two Out of Three") where three input lists must each contain values
only in `[1, 100]`. -/
def allInRange_specificDuplicate {α : Type u} [Preorder α] (xs : List α) (lo hi : α) : Prop :=
  ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi

end List
