import Mathlib

open List

/-!
# Stride-based summation over lists

`sumStrideAt` computes the sum of elements at evenly-spaced (strided) positions
in a list, starting from a given coordinate offset. This is useful for summing
interleaved data, e.g., extracting and summing one component from a flat list
of multi-component tuples.

## Parity-index summation

`sumByParity` sums elements whose index within a range `[start, stop)` has a given
parity modulo 2. `sumEvenIdx` and `sumOddIdx` are specializations for even/odd indices.
These are building blocks for algorithms that need to compute sums over parity classes,
e.g., LeetCode 1664 "Ways to Make a Fair Array" and similar prefix-parity problems.
-/

namespace List

/-- Sum of `min x bound` over a list: `∑_{x ∈ values} min x bound`.
For each element `x` in `values`, caps it at `bound` (taking the minimum with `bound`)
and then sums. Returns `0` for the empty list. -/
def sumMinCapped {α : Type} [LinearOrder α] [AddMonoid α] (values : List α) (bound : α) : α :=
  match values with
  | [] => 0
  | x :: xs => min x bound + sumMinCapped xs bound

/-! ### Range sum

`sumRange_specificDuplicate l lo hi` computes the sum of elements in the half-open range `[lo, hi)` of `l`.
Out-of-bounds access returns `0`. This is the basic building block for segment sums,
prefix sums, and sliding-window computations. -/

/-- Sum of elements in the half-open range `[lo, hi)` of list `l`:
`sumRange_specificDuplicate l lo hi = ∑_{i=lo}^{hi-1} l[i]` where out-of-bounds access returns `0`.
Returns `0` if `lo ≥ hi`. -/
def sumRange_specificDuplicate [AddCommMonoid α] (l : List α) (lo hi : ℕ) : α :=
  if lo < hi then
    (l[lo]?).getD 0 + sumRange_specificDuplicate l (lo + 1) hi
  else
    0
termination_by hi - lo

/-- Alternate version of `sumRange_specificDuplicate` that recurses on the right bound `hi` (decrementing)
instead of the left bound `lo`. Computes `∑_{i=lo}^{hi-1} (l[i]?).getD 0`.
Equivalent to `sumRange_specificDuplicate l lo hi`. Useful when extending ranges on the right side:
`sumRangeRight l lo (hi + 1) = sumRangeRight l lo hi + (l[hi]?).getD 0`. -/
def sumRangeRight [AddCommMonoid α] (l : List α) (lo hi : ℕ) : α :=
  if lo ≥ hi then
    0
  else
    sumRangeRight l lo (hi - 1) + (l[hi - 1]?).getD 0
termination_by hi
decreasing_by
  omega

/-- When `lo ≥ hi`, the range is empty and `sumRangeRight` returns `0`. -/
@[simp]
lemma sumRangeRight_eq_zero_of_ge [AddCommMonoid α] (l : List α) (lo hi : ℕ) (h : lo ≥ hi) :
    sumRangeRight l lo hi = 0 := by
  unfold sumRangeRight; simp [h]

/-- Extending the right bound by 1: `sumRangeRight l lo (hi + 1) = sumRangeRight l lo hi + (l[hi]?).getD 0`
when `lo ≤ hi`. This is the key unfolding lemma for right-recursing range sums. -/
lemma sumRangeRight_succ [AddCommMonoid α] (l : List α) (lo hi : ℕ) (hlo : lo ≤ hi) :
    sumRangeRight l lo (hi + 1) = sumRangeRight l lo hi + (l[hi]?).getD 0 := by
  have h_not_ge : ¬ (lo ≥ hi + 1) := by omega
  conv =>
    lhs
    unfold sumRangeRight
  simp [h_not_ge, Nat.add_sub_cancel]

/-- Sum over a single-element range: `sumRangeRight l k (k + 1) = (l[k]?).getD 0`. -/
lemma sumRangeRight_single [AddCommMonoid α] (l : List α) (k : ℕ) :
    sumRangeRight l k (k + 1) = (l[k]?).getD 0 := by
  rw [sumRangeRight_succ l k k (Nat.le_refl k), sumRangeRight_eq_zero_of_ge l k k (Nat.le_refl k),
    zero_add]

/-- `sumRangeRight l 0 n` equals the sum of the first `n` elements (`l.take n`). -/
lemma sumRangeRight_eq_take_sum [AddCommMonoid α] (l : List α) (n : ℕ) (hn : n ≤ l.length) :
    sumRangeRight l 0 n = (l.take n).sum := by
  induction' n with n ih
  · simp [sumRangeRight_eq_zero_of_ge l 0 0 (Nat.le_refl 0)]
  · have hn' : n ≤ l.length := by omega
    have hn_lt : n < l.length := by omega
    rw [sumRangeRight_succ l 0 n (by omega), ih hn']
    have htake : (l.take (n + 1)).sum = (l.take n).sum + (l[n]?).getD 0 := by
      rw [List.take_succ]
      simp [hn_lt]
    rw [← htake]

/-- `sumRangeRight` over the entire list equals `l.sum`. -/
@[simp]
lemma sumRangeRight_eq_sum [AddCommMonoid α] (l : List α) :
    sumRangeRight l 0 l.length = l.sum := by
  rw [sumRangeRight_eq_take_sum l l.length (Nat.le_refl _), List.take_length]

/-! ### Sliding window sum

`windowSum_specificDuplicate l start len` computes the sum of `len` consecutive elements starting at
index `start` in list `l`. This is the `(start, len)` convention (as opposed to the
`(lo, hi)` half-open range convention used by `sumRange_specificDuplicate`). Out-of-bounds access
returns `0` via `getD`. -/

/-- Sum of `len` elements starting at index `start` in list `l`:
`windowSum_specificDuplicate l start len = ∑_{i=start}^{start+len-1} l[i]` where out-of-bounds access
returns `0`. Returns `0` if `len = 0`.
Equivalent to `sumRange_specificDuplicate l start (start + len)`. -/
def windowSum_specificDuplicate [AddCommMonoid α] (l : List α) (start len : ℕ) : α :=
  if len = 0 then
    0
  else
    (l[start]?).getD 0 + windowSum_specificDuplicate l (start + 1) (len - 1)
termination_by len

/-- The base case: a window of length `0` sums to `0`. -/
@[simp]
lemma windowSum_zero [AddCommMonoid α] (l : List α) (start : ℕ) : windowSum_specificDuplicate l start 0 = 0 := by
  unfold windowSum_specificDuplicate; simp

/-- Connecting `windowSum_specificDuplicate` to `sumRange_specificDuplicate`: `windowSum_specificDuplicate l start len = sumRange_specificDuplicate l start (start + len)`. -/
lemma windowSum_eq_sumRange [AddCommMonoid α] (l : List α) (start len : ℕ) :
    windowSum_specificDuplicate l start len = sumRange_specificDuplicate l start (start + len) := by
  induction len generalizing start with
  | zero => simp [windowSum_specificDuplicate, sumRange_specificDuplicate]
  | succ len ih =>
    unfold windowSum_specificDuplicate
    simp
    rw [sumRange_specificDuplicate]
    have h_lt : start < start + len.succ := by omega
    simp [h_lt]
    rw [ih]
    have : (start + 1) + len = start + len.succ := by omega
    rw [this]

/-! ### Parity-index sum over a range -/

/-- Sum of elements at indices congruent to `parity` modulo 2 in the half-open range
`[start, stop)` of list `s`. Out-of-bounds access returns `0` (the identity of
the `AddCommMonoid`).

This is the general version; `sumEvenIdx` and `sumOddIdx` are specializations
for parity 0 (even) and parity 1 (odd). -/
def sumByParity [AddCommMonoid α] (s : List α) (parity : ℕ) (start : ℕ) (stop : ℕ) : α :=
  if h : start < stop then
    if start % 2 = parity then
      (s[start]?).getD 0 + sumByParity s parity (start + 1) stop
    else
      sumByParity s parity (start + 1) stop
  else
    0
termination_by stop - start

/-- Sum of elements at even indices (0, 2, 4, …) in the half-open range `[start, stop)` of list `s`.
Specialization of `sumByParity` with parity 0.
Equivalent to `(dropOddElements (s.drop start).take (stop-start)).sum`. -/
def sumEvenIdx [AddCommMonoid α] (s : List α) (start : ℕ) (stop : ℕ) : α :=
  sumByParity s 0 start stop

/-- Sum of elements at odd indices (1, 3, 5, …) in the half-open range `[start, stop)` of list `s`.
Specialization of `sumByParity` with parity 1.
Equivalent to `(dropEvenElements (s.drop start).take (stop-start)).sum`. -/
def sumOddIdx [AddCommMonoid α] (s : List α) (start : ℕ) (stop : ℕ) : α :=
  sumByParity s 1 start stop

/-- When the element at index `i` is removed from `s`, the elements that end up at even
positions are:
- before `i`: the even-indexed elements (positions 0, 2, 4, … < i remain at even positions)
- after `i`: the odd-indexed elements (positions i+1, i+3, … shift left by 1, becoming even)

This computes the sum of elements that would be at even positions after removing `s[i]`.
Useful for "fair array" problems (LeetCode 1664) and similar reindexing-after-removal
computations. -/
def sumEvenAfterRemoval [AddCommMonoid α] (s : List α) (i : ℕ) : α :=
  sumEvenIdx s 0 i + sumOddIdx s (i + 1) s.length

/-- Sum of elements at stride-spaced positions in a list:
`sumStrideAt default stride coord values n = ∑_{k=0}^{n-1} values[stride·k + coord]`
where out-of-bounds access returns `default`.

This is useful for summing every `stride`-th element starting from offset `coord`,
e.g., extracting and summing one component from a flat interleaved vector of
3-component tuples (where `stride = 3` and `coord ∈ {0,1,2}` selects the component). -/
def sumStrideAt {α : Type _} [AddCommMonoid α] (default : α) (stride : Nat) (coord : Nat)
    (values : List α) : Nat → α
  | 0 => 0
  | k + 1 => (values[(stride * k + coord)]?).getD default + sumStrideAt default stride coord values k

/-! ### Even-index sum

`evenIndexSum l` computes the sum of elements at even-numbered (0-based) positions
in the list `l`. For example, `evenIndexSum [a, b, c, d] = a + c`.

This is defined by structural pattern matching, not by indexing, which makes
it convenient for structural induction proofs. -/

/-- Sum of elements at even (0-based) indices in the list.
`evenIndexSum [a,b,c,d] = a + c`. Uses pattern matching for convenient induction. -/
def evenIndexSum {α : Type} [AddMonoid α] : List α → α
  | [] => 0
  | [x] => x
  | x :: _ :: xs => x + evenIndexSum xs

/-! ### Sum lower bound for nonempty lists of positive elements -/

/-- If a list of integers is nonempty and every element is at least `1`, then the sum
is at least `1`. This is a simple but useful lower bound for reasoning about sums
where each element contributes at least 1. -/
lemma sum_ge_one_of_nonempty_of_all_ge_one {l : List ℤ} (h_ne : l ≠ [])
    (h_ge : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.sum := by
  induction' l with h t ih
  · contradiction
  · simp [List.sum_cons]
    have hh : 1 ≤ h := h_ge h (by simp)
    have ht_nonneg : 0 ≤ t.sum :=
      List.sum_nonneg (λ x hx => by
        have hx_ge_one := h_ge x (List.mem_cons_of_mem h hx)
        omega)
    omega

/-! ### Filtered prefix sum

`sumFiltered xs pred n` sums the elements of `xs` at indices `i < n` where `pred i`
holds. Out-of-bounds access returns `0` (via `Inhabited` default). This captures the
common pattern of iterating over a prefix and accumulating only values meeting some
condition. -/

/-- Sum of elements at indices < n that satisfy `pred` in list `xs`.
`sumFiltered xs pred n = ∑_{i=0}^{n-1} (if pred i then xs[i]! else 0)`.
This pattern appears in problems that filter a list by an index predicate
before summing (e.g., "sum of good numbers", "sum if condition holds"). -/
def sumFiltered {α : Type} [Inhabited α] [AddCommMonoid α] (xs : List α) (pred : Nat → Bool) : Nat → α
  | 0 => 0
  | n+1 => sumFiltered xs pred n + (if pred n then xs[n]! else 0)

@[simp]
lemma sumFiltered_zero {α : Type} [Inhabited α] [AddCommMonoid α] (xs : List α) (pred : Nat → Bool) :
    sumFiltered xs pred 0 = 0 := rfl

/-! ### Subarray sum

`subSum l i len` computes the sum of `len` contiguous elements starting at index `i`
in list `l`, defined as `((l.drop i).take len).sum`. This is the `(start, length)`
convention (as opposed to the `(lo, hi)` half-open range convention used by `sumRange_specificDuplicate`).

The `(start, length)` representation is convenient for inductive proofs that extend the
subarray length one element at a time (see `subSum_snoc`). -/

/-- Sum of `len` contiguous elements starting at index `i` in list `l`:
`subSum l i len = ((l.drop i).take len).sum`. Returns `0` if `len = 0`.
This is the `(start, length)` convention for subarray sums, in contrast to
`sumRange_specificDuplicate l lo hi` which uses the `(lo, hi)` half-open range convention. -/
def subSum {α : Type _} [AddCommMonoid α] (l : List α) (i len : Nat) : α :=
  ((l.drop i).take len).sum

/-- A singleton `subSum` (length 1) returns the element at the start index:
`subSum l i 1 = l[i]` when `i < l.length`. -/
lemma subSum_one {α : Type _} [AddCommMonoid α] (l : List α) (i : Nat) (h : i < l.length) :
    subSum l i 1 = l.get ⟨i, h⟩ := by
  unfold subSum; simp [h]

/-- Extending `subSum` by one element:
`subSum l i (len+1) = subSum l i len + l[i+len]` when `i + len < l.length`.
This is the key inductive lemma for expanding a subarray sum rightward. -/
lemma subSum_snoc {α : Type _} [AddCommMonoid α] (l : List α) (i len : Nat) (h : i + len < l.length) :
    subSum l i (len + 1) = subSum l i len + (l.get ⟨i + len, h⟩) := by
  unfold subSum
  have h_len : len < (l.drop i).length := by
    simp; omega
  rw [sum_take_succ (l.drop i) len h_len]
  simp

/-! ### Half-open range sum via `drop`/`take`

`subSumRange l lo hi` is the sum of elements in the half-open range `[lo, hi)` of `l`,
defined as `((l.drop lo).take (hi - lo)).sum`. This is the `(lo, hi)` half-open range
analogue of `subSum l lo (hi - lo)`, often more convenient when both bounds are known. -/

/-- Sum of elements in the half-open range `[lo, hi)` of list `l`, defined via `drop`/`take`:
`subSumRange l lo hi = ((l.drop lo).take (hi - lo)).sum`.
This is the `(lo, hi)` convention; compare `subSum l lo (hi - lo)` which is equivalent
but uses the `(start, len)` convention. Returns `0` when `hi ≤ lo` (empty range). -/
def subSumRange {α : Type _} [AddCommMonoid α] (l : List α) (lo hi : Nat) : α :=
  ((l.drop lo).take (hi - lo)).sum

/-- When `lo = 0`, `subSumRange l 0 hi` equals the sum of the first `hi` elements:
`subSumRange l 0 hi = (l.take hi).sum`. -/
@[simp]
lemma subSumRange_zero_to_hi {α : Type _} [AddCommMonoid α] (l : List α) (hi : Nat) :
    subSumRange l 0 hi = (l.take hi).sum := by
  simp [subSumRange]

/-- `subSumRange l (i+1) l.length` equals the sum of the suffix starting at `i+1`:
`subSumRange l (i+1) l.length = (l.drop (i+1)).sum`. -/
lemma subSumRange_succ_to_len {α : Type _} [AddCommMonoid α] (l : List α) (i : Nat) :
    subSumRange l (i+1) l.length = (l.drop (i+1)).sum := by
  rw [subSumRange]
  have h : (l.drop (i+1)).take (l.length - (i+1)) = l.drop (i+1) := by
    apply List.take_of_length_le
    rw [List.length_drop]
  rw [h]

end List
