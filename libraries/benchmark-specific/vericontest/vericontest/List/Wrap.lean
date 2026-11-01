import Mathlib

open List

/-!
# Circular (wrap-around) list access

Utilities for treating a list as a circular buffer: indexed access with `ℤ` indices
that wrap around modulo the list length, and summation over wrapped segments.

These generalize the patterns from LeetCode 1652 ("Defuse the Bomb") and similar
circular-array problems.
-/

namespace List

/-- Circular (wrap-around) indexed access to a list using an `ℤ` index.
`getWrappingD xs idx default` returns the element at logical position `idx`, treating
the list as circular (modulo `xs.length`). If the list is empty, returns `default`.
Otherwise returns `xs.getD ((idx % xs.length).toNat) default`.

This generalizes the `getElemWrap` pattern from LeetCode 1652. -/
def getWrappingD {α : Type u} (xs : List α) (idx : Int) (default : α) : α :=
  let n := xs.length
  if n = 0 then default
  else xs.getD (((idx % (n : Int)).toNat)) default

/-- Sum of `count` elements starting from circular position `start` in a list,
using `getWrappingD` for wrap-around access. If `count ≤ 0`, returns `0`.

This generalizes the `sumWrap` pattern from LeetCode 1652 ("Defuse the Bomb"),
where a circular array is summed over a sliding window. -/
def sumWrapping {α : Type u} [AddMonoid α] (xs : List α) (start count : Int) : α :=
  if count ≤ 0 then 0
  else getWrappingD xs start 0 + sumWrapping xs (start + 1) (count - 1)
termination_by count.toNat

end List
