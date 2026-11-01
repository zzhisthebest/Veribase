import Mathlib
import vericontest.List

open List

/-!
# Maximum non-adjacent sum (House Robber DP)

Given a list, compute the maximum sum of a subset of elements
where no two selected elements are adjacent in the original list.

This implements the classic dynamic programming recurrence:
* `dp[0] = a[0]` (or `0` if the list is empty / index out of bounds)
* `dp[1] = max(a[0], a[1])`
* `dp[i] = max(dp[i-1], dp[i-2] + a[i])`  for `i ≥ 2`

The element type `α` requires `AddMonoid` (for `+` and `0`) and `Max` (for `max`).
Generalized from `rob_spec` (LeetCode 198 "House Robber").
-/

namespace List

variable {α : Type} [AddMonoid α] [Max α]

/-- The DP table for the maximum non-adjacent sum up to index `i`.
`maxNonadjacentSumAux a i` computes the optimal value considering
elements `a[0]` through `a[i]` (inclusive). -/
def maxNonadjacentSumAux (a : List α) : ℕ → α
  | 0 => (a[0]?).getD 0
  | 1 =>
    let n0 := (a[0]?).getD 0
    let n1 := (a[1]?).getD 0
    max n0 n1
  | i+2 =>
    let skip := maxNonadjacentSumAux a (i+1)
    let take := maxNonadjacentSumAux a i + (a[i+2]?).getD 0
    max take skip

end List
