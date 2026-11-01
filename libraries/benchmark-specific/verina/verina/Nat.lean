import Mathlib

namespace Specific

namespace Nat

/-- If `x` is either `0` or `1` and `1 < n`, then `x < n`. -/
theorem zero_or_one_lt_of_one_lt {n x : Nat}
    (hx : x = 0 ∨ x = 1) (hn : 1 < n) : x < n := by
  cases hx with
  | inl hzero =>
      rw [hzero]
      exact Nat.lt_trans Nat.zero_lt_one hn
  | inr hone =>
      rw [hone]
      exact hn

/-- `max a b` is always one of the two arguments. -/
theorem max_eq_left_or_eq_right {a b : Nat} : max a b = a ∨ max a b = b := by
  rcases Nat.le_total a b with (h | h)
  · exact Or.inr (Nat.max_eq_right h)
  · exact Or.inl (Nat.max_eq_left h)

/-- If `a = b`, then both `a - b = 0` and `b - a = 0`. Useful for
verification conditions that check equality in both subtraction directions. -/
theorem sub_zero_pair_of_eq {a b : Nat} (h : a = b) : a - b = 0 ∧ b - a = 0 := by
  subst h; simp

end Nat

end Specific
