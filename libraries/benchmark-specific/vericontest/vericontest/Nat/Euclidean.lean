import Mathlib
import vericontest.Nat

namespace Nat

/-- Counts the number of subtraction steps in the subtractive Euclidean algorithm.
Starting from `(a, b)`, at each step subtract the smaller from the larger.
When either operand becomes 0, the recursion stops.

This is the length of the subtraction chain: `subtractionChainSteps a b` is the number
of subtractions needed until one operand reaches 0, following the pattern
if `b ≤ a` then `(a - b, b)` else `(a, b - a)`.

For example, `subtractionChainSteps 6 4 = 3` because:
`(6,4) → (2,4) → (2,2) → (0,2)`, which is 3 steps. -/
def subtractionChainSteps (a b : Nat) : Nat :=
  if hz : a = 0 ∨ b = 0 then
    0
  else if hle : b ≤ a then
    1 + subtractionChainSteps (a - b) b
  else
    1 + subtractionChainSteps a (b - a)
termination_by a + b
decreasing_by
  · have hb_ne_zero : b ≠ 0 := fun h => hz (Or.inr h)
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
    exact sub_add_lt_add_of_pos hb_pos hle
  · have ha_ne_zero : a ≠ 0 := fun h => hz (Or.inl h)
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_ne_zero
    exact add_sub_lt_add_of_pos ha_pos (Nat.le_of_not_ge hle)

end Nat
