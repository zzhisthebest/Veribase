import Mathlib

namespace Nat

/-! ### Triangular numbers (recursive definition)

The `n`-th triangular number `T_n = 0 + 1 + 2 + … + n = n*(n+1)/2`.
This module defines triangular numbers via the recursive summation form
`triangularNumber_specificDuplicate 0 = 0`, `triangularNumber_specificDuplicate (k+1) = triangularNumber_specificDuplicate k + (k+1)`,
which is convenient for induction proofs.

For the closed-form version on `Int`, see `Int.triangularNumber_specificDuplicate` in `general.Int`.
-/

/-- The `n`-th triangular number defined recursively:
`triangularNumber_specificDuplicate 0 = 0`, `triangularNumber_specificDuplicate (k+1) = triangularNumber_specificDuplicate k + (k+1)`.
This is the sum `0 + 1 + 2 + … + n`, equal to `n*(n+1)/2`. -/
def triangularNumber_specificDuplicate : ℕ → ℕ
  | 0 => 0
  | k + 1 => triangularNumber_specificDuplicate k + (k + 1)

end Nat
