import Mathlib
import vericontest.List

open List

/-!
# Prefix sum lemmas, suffix sum, and first-prefix search

Extends `List.prefixSum_specificDuplicate` with structural lemmas (cons, add, drop) and a
function to find the first position where the prefix sum reaches a target.

`findFirstPrefixSum arr target` returns the smallest `n` (1-indexed) such that
`prefixSum_specificDuplicate arr n = target`, or `none` if no such prefix exists.

Also defines `suffixSum_specificDuplicate` — the sum of elements from index `i` to the end of a list
— which is the natural suffix counterpart of `prefixSum_specificDuplicate`.
-/

namespace List

/-! ### `suffixSum_specificDuplicate` — sum from an index to the end of a list -/

/-- The suffix sum of a list from index `i` to the end.
`suffixSum_specificDuplicate piles i = ∑_{j=i}^{piles.length-1} piles[j]`, or `0` if `i ≥ piles.length`.
This is the suffix counterpart of `prefixSum_specificDuplicate` and generalizes the suffix sum pattern
from leetcode 1140 (Stone Game II) and similar competitive programming tasks. -/
def suffixSum_specificDuplicate {α : Type} [AddCommMonoid α] (piles : List α) (i : Nat) : α :=
  if h : i < piles.length then
    piles.get ⟨i, h⟩ + suffixSum_specificDuplicate piles (i + 1)
  else
    0
termination_by piles.length - i
decreasing_by
  omega

/-! ### Structural lemmas for `prefixSum_specificDuplicate` -/

/-- The prefix sum of a cons list at `n+1` is `x + prefixSum_specificDuplicate xs n`. -/
lemma prefixSum_cons_specificDuplicate {α : Type _} [AddMonoid α] (x : α) (xs : List α) (n : Nat) :
    prefixSum_specificDuplicate (x :: xs) (n + 1) = x + prefixSum_specificDuplicate xs n := by
  simp [prefixSum_specificDuplicate, sum_cons]

/-- Splitting a prefix sum:
`prefixSum_specificDuplicate arr (a + b) = prefixSum_specificDuplicate arr a + prefixSum_specificDuplicate (arr.drop a) b`. -/
lemma prefixSum_add {α : Type _} [AddMonoid α] (arr : List α) (a b : Nat) :
    prefixSum_specificDuplicate arr (a + b) = prefixSum_specificDuplicate arr a + prefixSum_specificDuplicate (arr.drop a) b := by
  rw [prefixSum_specificDuplicate, prefixSum_specificDuplicate, prefixSum_specificDuplicate, take_add, sum_append]

/-- When `a ≤ b`, the prefix sum up to `b` can be decomposed as the prefix sum up to `a`
plus the prefix sum of the dropped part from `a` to `b`. -/
lemma prefixSum_drop_of_le {α : Type _} [AddMonoid α] (arr : List α) (a b : Nat) (hle : a ≤ b) :
    prefixSum_specificDuplicate arr a + prefixSum_specificDuplicate (arr.drop a) (b - a) = prefixSum_specificDuplicate arr b := by
  calc
    prefixSum_specificDuplicate arr a + prefixSum_specificDuplicate (arr.drop a) (b - a) = prefixSum_specificDuplicate arr (a + (b - a)) := by
      rw [prefixSum_add arr a (b - a)]
    _ = prefixSum_specificDuplicate arr b := by rw [Nat.add_sub_cancel' hle]

/-! ### First prefix with a given sum -/

/-- Find the first index `n` (1-indexed, i.e., `1 ≤ n`) such that
`prefixSum_specificDuplicate arr n = target`. Returns `none` if no prefix sums to `target`. -/
def findFirstPrefixSum {α : Type _} [AddCommGroup α] [DecidableEq α] (arr : List α) (target : α) : Option Nat :=
  match arr with
  | [] => none
  | x :: xs =>
    if x = target then
      some 1
    else
      match findFirstPrefixSum xs (target - x) with
      | none => none
      | some n => some (n + 1)

/-- If `findFirstPrefixSum arr target = some n`, then
`prefixSum_specificDuplicate arr n = target` and `1 ≤ n`. -/
lemma findFirstPrefixSum_some_spec {α : Type _} [AddCommGroup α] [DecidableEq α]
    (arr : List α) (target : α) (n : Nat)
    (h : findFirstPrefixSum arr target = some n) : prefixSum_specificDuplicate arr n = target ∧ 1 ≤ n := by
  induction arr generalizing target n with
  | nil => simp [findFirstPrefixSum] at h
  | cons x xs ih =>
    unfold findFirstPrefixSum at h
    by_cases h_eq : x = target
    · simp [h_eq] at h; subst h
      refine ⟨?_, by omega⟩
      simp [prefixSum_specificDuplicate, h_eq]
    · simp [h_eq] at h
      cases hf : findFirstPrefixSum xs (target - x) with
      | none => simp [hf] at h
      | some k =>
        simp [hf] at h
        have hn_eq : n = k + 1 := by simpa using h.symm
        subst hn_eq
        rcases ih (target - x) k hf with ⟨hsum_k, hk⟩
        have hsum_n : prefixSum_specificDuplicate (x :: xs) (k + 1) = target := by
          rw [prefixSum_cons_specificDuplicate, hsum_k]
          abel
        exact ⟨hsum_n, by omega⟩

/-! ### Prefix sum of adjacent absolute differences

`adjacentAbsDiffPrefixSum xs n = ∑_{k=0}^{n-1} |xs.getD (k+1) 0 - xs.getD k 0|`.
This computes the prefix sum of the absolute differences of adjacent elements,
i.e., the "array value" of the prefix. Returns `0` for `n = 0`.

This pattern appears in problems like LeetCode 1330 ("Reverse Subarray to Maximize
Array Value"), where the value of an array is the sum of absolute differences of
adjacent elements, and computing prefix sums of this value is essential for
efficiently computing the effect of reversing a subarray. -/
def adjacentAbsDiffPrefixSum {α : Type _} [LinearOrderedAddCommGroup α] (xs : List α) : ℕ → α
  | 0 => 0
  | m+1 => adjacentAbsDiffPrefixSum xs m + |xs.getD (m + 1) 0 - xs.getD m 0|

@[simp]
lemma adjacentAbsDiffPrefixSum_zero {α : Type _} [LinearOrderedAddCommGroup α] (xs : List α) :
    adjacentAbsDiffPrefixSum xs 0 = 0 := rfl

lemma adjacentAbsDiffPrefixSum_succ {α : Type _} [LinearOrderedAddCommGroup α] (xs : List α) (n : ℕ) :
    adjacentAbsDiffPrefixSum xs (n + 1) =
    adjacentAbsDiffPrefixSum xs n + |xs.getD (n + 1) 0 - xs.getD n 0| := rfl

/-! ### Alternating prefix sum

`alternatingPrefixSum s n` computes the alternating sum of the first `n` elements of `s`:
even-indexed elements are added, odd-indexed elements are subtracted.
For example, `alternatingPrefixSum [a₀, a₁, a₂, a₃] 3 = a₀ - a₁ + a₂`.
When `n` is out of bounds, the index-access `(s[i]?).getD 0` returns `0`.
Works for any `AddGroup` (`ℤ`, `ℚ`, `ℝ`, etc.). -/

/-- Alternating sum of the first `end_idx` elements of a list.
Even-indexed elements (0, 2, 4, …) are added; odd-indexed elements (1, 3, 5, …)
are subtracted. Out-of-bounds indices contribute 0 via `(s[i]?).getD 0`.
Equivalent to the alternating sum of `s.take end_idx`. -/
def alternatingPrefixSum [AddGroup α] (s : List α) (end_idx : Nat) : α :=
  match end_idx with
  | 0 => 0
  | i+1 =>
    let x := (s[i]?).getD 0
    alternatingPrefixSum s i + (if i % 2 = 0 then x else -x)

@[simp]
lemma alternatingPrefixSum_zero [AddGroup α] (s : List α) :
    alternatingPrefixSum s 0 = 0 := rfl

lemma alternatingPrefixSum_succ [AddGroup α] (s : List α) (i : Nat) :
    alternatingPrefixSum s (i + 1) =
    alternatingPrefixSum s i + (if i % 2 = 0 then (s[i]?).getD 0 else -(s[i]?).getD 0) := rfl

/-! ### `prefixSumGetD` — simple prefix sum via `getD`

`prefixSumGetD s default n` computes `∑_{i=0}^{n-1} (s[i]?).getD default`.
Returns `0` for `n = 0`. This is the simplest prefix-sum-over-safe-access
pattern and forms the basis for the more specialized variants below
(`adjacentAbsDiffPrefixSum`, `alternatingPrefixSum`).

This pattern appears in problems like LeetCode 453 ("Minimum Moves to Equal
Array Elements") and similar prefix-sum-based competitive programming tasks. -/

/-- Simple prefix sum using `getD` for safe index access.
`prefixSumGetD s d n = ∑_{i=0}^{n-1} (s[i]?).getD d`, returns `0` for `n = 0`. -/
def prefixSumGetD [AddMonoid α] (s : List α) (default : α) : Nat → α
  | 0 => 0
  | n+1 => prefixSumGetD s default n + (s[n]?).getD default

@[simp]
lemma prefixSumGetD_zero [AddMonoid α] (s : List α) (d : α) :
    prefixSumGetD s d 0 = 0 := rfl

lemma prefixSumGetD_succ [AddMonoid α] (s : List α) (d : α) (n : Nat) :
    prefixSumGetD s d (n+1) = prefixSumGetD s d n + (s[n]?).getD d := rfl

end List
