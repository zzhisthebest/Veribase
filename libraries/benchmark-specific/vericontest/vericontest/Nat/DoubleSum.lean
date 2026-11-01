import Mathlib

namespace Nat

/-!
# Recursive row and double sums over rectangular index ranges

`rowSum f i n` computes `∑_{j=0}^{n-1} f i j` recursively,
and `doubleSum f m n` computes `∑_{i=0}^{m-1} ∑_{j=0}^{n-1} f i j` recursively.

These are computable, structurally recursive versions of the corresponding
`Finset` sums, and come with recurrence lemmas (`_zero`, `_succ`) and
equivalence lemmas to the `Finset` formulations.

This pattern generalizes the inner/outer sum helpers from problems involving
double-sum computations over list elements (e.g., LeetCode 1862 "Sum of Floored Pairs").
-/

/-- Sum of `f i j` for `j = 0` to `n-1`. A recursive, computable version of `∑_{j < n} f i j`. -/
def rowSum (f : ℕ → ℕ → ℕ) (i n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 => rowSum f i k + f i k
termination_by n

/-- Double sum `∑_{i=0}^{m-1} ∑_{j=0}^{n-1} f i j`. A recursive, computable version. -/
def doubleSum (f : ℕ → ℕ → ℕ) (m n : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | k + 1 => doubleSum f k n + rowSum f k n
termination_by m

@[simp]
lemma rowSum_zero (f : ℕ → ℕ → ℕ) (i : ℕ) : rowSum f i 0 = 0 := by
  simp [rowSum]

lemma rowSum_succ (f : ℕ → ℕ → ℕ) (i n : ℕ) :
    rowSum f i (n + 1) = rowSum f i n + f i n := by
  simp [rowSum]

@[simp]
lemma doubleSum_zero (f : ℕ → ℕ → ℕ) (n : ℕ) : doubleSum f 0 n = 0 := by
  simp [doubleSum]

lemma doubleSum_succ (f : ℕ → ℕ → ℕ) (m n : ℕ) :
    doubleSum f (m + 1) n = doubleSum f m n + rowSum f m n := by
  simp [doubleSum]

/-- `rowSum` expressed as a standard `Finset` sum. -/
lemma rowSum_eq_finset_sum (f : ℕ → ℕ → ℕ) (i n : ℕ) :
    rowSum f i n = ∑ j ∈ Finset.range n, f i j := by
  induction' n with k ih
  · simp [rowSum]
  · rw [rowSum_succ, Finset.sum_range_succ, ih]

/-- `doubleSum` expressed as a nested `Finset` sum. -/
lemma doubleSum_eq_finset_sum (f : ℕ → ℕ → ℕ) (m n : ℕ) :
    doubleSum f m n = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j := by
  induction' m with k ih
  · simp [doubleSum]
  · rw [doubleSum_succ, Finset.sum_range_succ, ih, rowSum_eq_finset_sum]

end Nat
