import Mathlib

namespace Nat

/-- Stern's diatomic sequence (also known as the fusc function or the Stern-Brocot sequence).
Defined by the recurrence:
- `stern 0 = 0`
- `stern 1 = 1`
- For `n ≥ 2`: `stern n = stern (n/2)` when `n` is even,
  and `stern n = stern (n/2) + stern (n/2 + 1)` when `n` is odd.

This is OEIS A002487 and appears in LeetCode 1646 "Get Maximum in Generated Array".
The sequence begins: 0, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4, ... -/
def stern (k : Nat) : Nat :=
  if k = 0 then 0
  else if k = 1 then 1
  else
    let r := stern (k / 2)
    if k % 2 == 0 then r
    else r + stern (k / 2 + 1)
termination_by k
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · rename_i _ _ h_not_even
    have hmod_one : k % 2 = 1 := by
      have h_cases := Nat.mod_two_eq_zero_or_one k
      rcases h_cases with (h | h)
      · have : (k % 2 == 0) = true := by simp [h]
        exact absurd this h_not_even
      · exact h
    have hdivpos : 0 < k / 2 := Nat.div_pos (by omega) (by omega)
    have hdivadd := Nat.div_add_mod k 2
    rw [hmod_one] at hdivadd
    omega

end Nat
