import Mathlib

open List

/-!
# Prefix Filter — filtering a prefix of a list by a sentinel value

`prefixFilterNe sentinel nums n` returns the sublist of `nums[0..n)` consisting of
elements not equal to `sentinel`. This is used in stack/sentinel-based algorithms
where certain values are "markers" that should be excluded from the result.

Equivalently, `prefixFilterNe sentinel nums n = (nums.take n).filter (· ≠ sentinel)`.
-/

namespace List

/-- Collect elements from the prefix `nums[0..end_)` that are not equal to `sentinel`.
The order of elements is preserved. Equivalent to `(nums.take end_).filter (· ≠ sentinel)`. -/
def prefixFilterNe {α : Type} [DecidableEq α] (sentinel : α) (nums : List α) (end_ : Nat) : List α :=
  match end_ with
  | 0 => []
  | n+1 =>
    let prev := prefixFilterNe sentinel nums n
    if let some x := nums[n]? then
      if x = sentinel then prev else prev ++ [x]
    else
      prev
termination_by end_

/-- The length of `prefixFilterNe sentinel nums end_` is at most `end_`.
This holds because each recursive step adds at most one element to the result. -/
lemma prefixFilterNe_length_le {α : Type} [DecidableEq α] (sentinel : α) (nums : List α) (end_ : Nat) :
    (prefixFilterNe sentinel nums end_).length ≤ end_ := by
  induction end_ with
  | zero => simp [prefixFilterNe]
  | succ n ih =>
    simp (config := {zeta := true}) [prefixFilterNe]
    cases h : nums[n]? with
    | none => simp [ih, Nat.le_succ_of_le]
    | some x =>
      by_cases hx : x = sentinel
      · simp [hx, ih, Nat.le_succ_of_le]
      · simp [hx, ih, List.length_append, Nat.le_succ_of_le]

end List
