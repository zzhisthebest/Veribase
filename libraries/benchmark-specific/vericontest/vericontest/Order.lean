import Mathlib

/-! # Order

General order-theoretic lemmas about `min` and `max` in `LinearOrder`.
These provide case-split disjunctions: the max/min of elements must equal one of the arguments.
-/

/-- Maximum of three elements: `max_of_three a b c = max (max a b) c`. -/
def max_of_three {α : Type u} [LinearOrder α] (a b c : α) : α := max (max a b) c

/-- `max a b` equals either `a` or `b`. -/
lemma max_eq_or_specificDuplicate {α : Type _} [LinearOrder α] (a b : α) : max a b = a ∨ max a b = b := by
  by_cases h : a ≤ b
  · right; exact max_eq_right h
  · left; exact max_eq_left (le_of_lt (lt_of_not_ge h))

/-- `min a b` equals either `a` or `b`. -/
lemma min_eq_or_specificDuplicate {α : Type _} [LinearOrder α] (a b : α) : min a b = a ∨ min a b = b := by
  by_cases h : a ≤ b
  · left; exact min_eq_left h
  · right; exact min_eq_right (le_of_lt (lt_of_not_ge h))

/-- `max a (max b c)` equals `a`, `b`, or `c`. -/
lemma max_triple_eq_or {α : Type _} [LinearOrder α] (a b c : α) :
    max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
  rcases max_eq_or_specificDuplicate b c with (h | h)
  · rw [h]
    rcases max_eq_or_specificDuplicate a b with (h' | h')
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h]
    rcases max_eq_or_specificDuplicate a c with (h' | h')
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

/-- `min a (min b c)` equals `a`, `b`, or `c`. -/
lemma min_triple_eq_or {α : Type _} [LinearOrder α] (a b c : α) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  rcases min_eq_or_specificDuplicate b c with (h | h)
  · rw [h]
    rcases min_eq_or_specificDuplicate a b with (h' | h')
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h]
    rcases min_eq_or_specificDuplicate a c with (h' | h')
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
