import Mathlib

/-! # Combinatorics

General combinatorial counting functions: counting bounded integer compositions,
dice-roll ways, and related recurrences.
-/

/-- Number of ways to write `target` as a sum of exactly `n` values drawn from `values`.
That is, `|{(f₁,…,fₙ) : each fᵢ ∈ values ∧ ∑_{i=1}^{n} fᵢ = target}|`.

The base case `n = 0` gives 1 for `target = 0` (empty sum) and 0 otherwise.
The recursive case sums over each possible first value `f ∈ values`,
counting the number of ways to make the remaining sum `target - f` with `n-1` values.

Examples (represented via their specialization):
- With `values = Finset.Icc 1 k`, this counts the number of ways to roll `n` dice
  with `k` faces each to achieve sum `target`.
- With `values = {a, b}`, this counts compositions into exactly `n` parts
  each being `a` or `b`. -/
def countWays (n : ℕ) (values : Finset ℤ) (target : ℤ) : ℤ :=
  match n with
  | 0 => if target = 0 then 1 else 0
  | n' + 1 =>
    ∑ f ∈ values, countWays n' values (target - f)
