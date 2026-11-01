import Mathlib

namespace Int

/-! ### Multiplication table entry counting

`mulTableCountUpTo m n x i` counts how many entries in the first `i` rows of an
`m`×`n` multiplication table are ≤ `x`. For each row `j` (1 ≤ j ≤ i), the count of
entries ≤ `x` is `min n (x / j)`, since entries in row `j` are `j*1, j*2, …, j*n`
and `j*k ≤ x ↔ k ≤ x/j`.

The function returns 0 when any of `i ≤ 0`, `m ≤ 0`, `n ≤ 0`, or `x < 0`.
This is the core combinatorial count behind "Kth Smallest Number in Multiplication Table"
(LeetCode 668) and similar problems.

Example: in a 3×3 table, entries ≤ 4 are {1,2,2,3,3,4} (6 entries).
`mulTableCountUpTo 3 3 4 3 = 6`.
-/

/-- Counts entries ≤ `x` in the first `i` rows of an `m`×`n` multiplication table.
For each row `j`, the number of columns `k` with `j*k ≤ x` is `min n (x/j)`.
The total is the prefix sum `∑_{j=1}^{i} min(n, x / j)`. -/
def mulTableCountUpTo (m n x i : Int) : Int :=
  if i ≤ 0 ∨ m ≤ 0 ∨ n ≤ 0 ∨ x < 0 then
    0
  else
    mulTableCountUpTo m n x (i - 1) + min n (x / i)
termination_by i.toNat

/-- Counts all entries ≤ `x` in the full `m`×`n` multiplication table.
Equivalent to `mulTableCountUpTo m n x m`. -/
def mulTableCountLE (m n x : Int) : Int :=
  mulTableCountUpTo m n x m

end Int
