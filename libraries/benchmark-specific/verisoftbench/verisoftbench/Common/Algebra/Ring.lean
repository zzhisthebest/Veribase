import Mathlib.Algebra.Ring.Basic

/-!
# Ring algebra lemmas

General-purpose lemmas about rings.
-/

/-- If `a * x = 0` and `b * y = 0` and `(a + b) * (x + y) - z = 0`, then `a * y + b * x = z`. -/
lemma expand_mul_add_sub_eq {α : Type} [Ring α] {a b x y z : α}
    (h_ax : a * x = 0) (h_by : b * y = 0) (h_mul_sub : (a + b) * (x + y) - z = 0) :
    a * y + b * x = z := by
  have h_expanded : (a + b) * (x + y) = a * x + a * y + b * x + b * y := by
    calc
      (a + b) * (x + y) = a * (x + y) + b * (x + y) := by rw [add_mul]
      _ = (a * x + a * y) + (b * x + b * y) := by simp [mul_add]
      _ = a * x + a * y + b * x + b * y := by simp [add_assoc]
  rw [h_expanded] at h_mul_sub
  rw [h_ax, h_by] at h_mul_sub
  simp at h_mul_sub
  exact sub_eq_zero.mp h_mul_sub

/--
If one of `a` or `x` is zero, and `a * y + b * x = z`, then either `b * x = z` or `a * y = z`.
This is useful for case-splitting on a sum-of-products equality when one factor is known to be zero.
-/
lemma disj_of_mul_zero_or_and_sum {α : Type} [Ring α] {a b x y z : α}
    (h_zero_or : a = 0 ∨ x = 0) (h_sum : a * y + b * x = z) : b * x = z ∨ a * y = z := by
  rcases h_zero_or with (ha | hx)
  · rw [ha, zero_mul] at h_sum; simp at h_sum; left; exact h_sum
  · rw [hx, mul_zero] at h_sum; simp at h_sum; right; exact h_sum
