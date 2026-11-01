import Mathlib

open List

/-!
# Counting adjacent pair comparisons

`countAdjacentDecreasing s start` counts how many adjacent pairs `(s[i], s[i+1])` for
`i ≥ start` are strictly decreasing (`s[i] > s[i+1]`).

`countAdjacentIncreasing s start` counts how many adjacent pairs `(s[i], s[i+1])` for
`i ≥ start` are strictly increasing (`s[i] < s[i+1]`).

These are the building blocks for verifying list monotonicity: a list is nondecreasing iff
`countAdjacentDecreasing s 0 = 0`, and nonincreasing iff `countAdjacentIncreasing s 0 = 0`.

Generalized from `count_inc_violations` and `count_dec_violations` in LeetCode 896
("Monotonic Array"), generalized from `List ℤ` to any `LinearOrder α`.
-/

namespace List

/-- Counts how many adjacent pairs `(s[i], s[i+1])` from index `start` onward
are strictly decreasing (`s[i] > s[i+1]`). This is the number of violations
of the nondecreasing property starting from position `start`.

Generalized from `count_inc_violations` (LeetCode 896). -/
def countAdjacentDecreasing {α : Type} [LinearOrder α] (s : List α) (start : ℕ) : ℕ :=
  if h : start + 1 < s.length then
    have h_start : start < s.length := by omega
    (if s.get ⟨start + 1, h⟩ < s.get ⟨start, h_start⟩ then 1 else 0) +
    countAdjacentDecreasing s (start + 1)
  else
    0
termination_by s.length - start
decreasing_by
  omega

/-- Counts how many adjacent pairs `(s[i], s[i+1])` from index `start` onward
are strictly increasing (`s[i] < s[i+1]`). This is the number of violations
of the nonincreasing property starting from position `start`.

Generalized from `count_dec_violations` (LeetCode 896). -/
def countAdjacentIncreasing {α : Type} [LinearOrder α] (s : List α) (start : ℕ) : ℕ :=
  if h : start + 1 < s.length then
    have h_start : start < s.length := by omega
    (if s.get ⟨start, h_start⟩ < s.get ⟨start + 1, h⟩ then 1 else 0) +
    countAdjacentIncreasing s (start + 1)
  else
    0
termination_by s.length - start
decreasing_by
  omega

/-! ### Shift lemma

When the list is extended with an element at the front (`a :: tail`), the count starting
from `start + 1` on the cons equals the count starting from `start` on the tail.
This is because index `start + 1` in `a :: tail` corresponds to index `start` in `tail`. -/

/-- Shifting lemma for `countAdjacentDecreasing`: prepending an element shifts all
indices by 1, so the count from `start + 1` on `a :: tail` equals the count from
`start` on `tail`. -/
lemma countAdjacentDecreasing_shift {α : Type} [LinearOrder α]
    (a : α) (tail : List α) (start : ℕ) :
    countAdjacentDecreasing (a :: tail) (start + 1) = countAdjacentDecreasing tail start := by
  induction hn : tail.length - start using Nat.strong_induction_on generalizing start with
  | h n ih =>
    conv_lhs => rw [countAdjacentDecreasing]
    conv_rhs => rw [countAdjacentDecreasing]
    simp only [List.length_cons, Nat.add_lt_add_iff_right, List.get_eq_getElem,
      List.getElem_cons_succ]
    split
    · rename_i h
      congr 1
      exact ih (tail.length - (start + 1)) (by omega) (start + 1) rfl
    · rfl

/-- Shifting lemma for `countAdjacentIncreasing`: prepending an element shifts all
indices by 1, so the count from `start + 1` on `a :: tail` equals the count from
`start` on `tail`. -/
lemma countAdjacentIncreasing_shift {α : Type} [LinearOrder α]
    (a : α) (tail : List α) (start : ℕ) :
    countAdjacentIncreasing (a :: tail) (start + 1) = countAdjacentIncreasing tail start := by
  induction hn : tail.length - start using Nat.strong_induction_on generalizing start with
  | h n ih =>
    conv_lhs => rw [countAdjacentIncreasing]
    conv_rhs => rw [countAdjacentIncreasing]
    simp only [List.length_cons, Nat.add_lt_add_iff_right, List.get_eq_getElem,
      List.getElem_cons_succ]
    split
    · rename_i h
      congr 1
      exact ih (tail.length - (start + 1)) (by omega) (start + 1) rfl
    · rfl

/-! ### Recursion unfolding at zero

These lemmas unfold the count definitions at `start = 0` for a list of the form
`a :: b :: rest`, expressing the count as a head comparison plus the count on the tail. -/

/-- Unfolding `countAdjacentDecreasing` at index 0 for a list with at least two elements. -/
lemma countAdjacentDecreasing_zero_cons_cons {α : Type} [LinearOrder α]
    (a b : α) (rest : List α) :
    countAdjacentDecreasing (a :: b :: rest) 0 =
    (if b < a then 1 else 0) + countAdjacentDecreasing (b :: rest) 0 := by
  conv =>
    lhs
    unfold countAdjacentDecreasing
    simp
  rw [countAdjacentDecreasing_shift a (b :: rest) 0]

/-- Unfolding `countAdjacentIncreasing` at index 0 for a list with at least two elements. -/
lemma countAdjacentIncreasing_zero_cons_cons {α : Type} [LinearOrder α]
    (a b : α) (rest : List α) :
    countAdjacentIncreasing (a :: b :: rest) 0 =
    (if a < b then 1 else 0) + countAdjacentIncreasing (b :: rest) 0 := by
  conv =>
    lhs
    unfold countAdjacentIncreasing
    simp
  rw [countAdjacentIncreasing_shift a (b :: rest) 0]

end List
