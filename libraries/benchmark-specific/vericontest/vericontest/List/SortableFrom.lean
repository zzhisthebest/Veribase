import Mathlib

open List

/-! ### Stateful sortable predicate

This module provides predicates for checking whether a list is "sortable" under a
left-to-right reduction operation. The core operation `next_state` computes a new state
from a previous value and the current element: if `prev ≤ x`, the remainder `x - prev`
carries forward; otherwise the state resets to `0`.

This pattern appears in problems like CF 2060D, where adjacent elements can be reduced
by subtraction when the left element is ≤ the right element.

The module provides three equivalent views of the same property:
* `sortable_from` — recursive `Prop` (structural induction)
* `sortable_condition` — index-based `Prop` (positional access)
* `indexed_sortable` — generic abstraction parameterized by an arbitrary
  "remaining" function, proved equivalent to `sortable_condition` for cons lists
  via `indexed_sortable_cons_iff`.
-/

/-- The single-step state transition: if `prev ≤ x`, the new state is `x - prev`
(the remainder after reduction); otherwise it is `0` (the value is fully consumed). -/
def next_state {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α] (prev x : α) : α :=
  if prev ≤ x then x - prev else 0

namespace List

/-- Compute the remaining value at position `i` in `xs` starting from initial value `prev`.
This iterates `next_state` through the list: `remaining_from prev xs i` gives the state
after processing the first `i` elements. -/
def remaining_from {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α] (prev : α) : List α → Nat → α
  | [], _ => 0
  | x :: _, 0 => next_state prev x
  | x :: xs, i + 1 => remaining_from (next_state prev x) xs i

/-- A list `xs` is sortable from `prev` if each element is ≥ the state computed from
previous elements. This is defined recursively: `prev ≤ x` and the tail is sortable
from the updated state `next_state prev x`. -/
def sortable_from {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α] (prev : α) : List α → Prop
  | [] => True
  | x :: xs => prev ≤ x ∧ sortable_from (next_state prev x) xs

/-- Boolean version of `sortable_from`. Returns `true` if the list is sortable from `prev`. -/
def can_sort_aux {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α] (prev : α) : List α → Bool
  | [] => true
  | x :: xs =>
    (prev ≤ x) && can_sort_aux (next_state prev x) xs

/-- Indexed version of `sortable_from`: `sortable_condition prev xs` asserts that for
every index `i < xs.length`, the head comparison (for `i = 0`) or the remaining-from
comparison (for `i > 0`) holds against `xs[i]`. -/
def sortable_condition {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α]
    (prev : α) (xs : List α) : Prop :=
  ∀ i (h : i < xs.length),
    match i with
    | 0 => prev ≤ xs.get ⟨0, h⟩
    | j + 1 => remaining_from prev xs j ≤ xs.get ⟨j + 1, h⟩

/-- `indexed_sortable remaining a` asserts that for each adjacent pair `(i, i+1)` in `a`,
the "remaining" value at position `i` (computed by `remaining`) is ≤ the element at `i+1`.
This abstracts the sortable condition over an arbitrary remaining-value function. -/
def indexed_sortable {α : Type} [LE α]
    (remaining : ∀ (a : List α) (i : Nat), i < a.length → α)
    (a : List α) : Prop :=
  ∀ i (h : i + 1 < a.length),
    remaining a i (Nat.lt_of_succ_lt h) ≤ a.get ⟨i + 1, h⟩

/-- `sortable_from` and `sortable_condition` are equivalent ways of expressing
the same property. -/
lemma sortable_from_iff_condition {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α]
    (prev : α) (xs : List α) :
    sortable_from prev xs ↔ sortable_condition prev xs := by
  induction xs generalizing prev with
  | nil => simp [sortable_from, sortable_condition]
  | cons x xs ih =>
    constructor
    · intro h i hi
      cases i with
      | zero => exact h.1
      | succ j =>
        have hj : j < xs.length := by simpa using hi
        have htail := (ih (prev := next_state prev x)).mp h.2 j hj
        cases j <;> simpa [sortable_condition, remaining_from] using htail
    · intro h
      constructor
      · exact h 0 (by simp)
      · apply (ih (prev := next_state prev x)).mpr
        intro i hi
        have h' := h (i + 1) (by simpa using hi)
        cases i <;> simpa [sortable_condition, remaining_from] using h'

/-- For a cons list `prev :: xs`, `indexed_sortable` with a `remaining` function that
agrees with `remaining_from` at non-zero indices is equivalent to `sortable_condition`. -/
lemma indexed_sortable_cons_iff {α : Type} [LE α] [Sub α] [Zero α] [DecidableLE α]
    (remaining : ∀ (a : List α) (i : Nat), i < a.length → α)
    (prev : α) (xs : List α)
    (remaining_zero : ∀ h : 0 < (prev :: xs).length,
      remaining (prev :: xs) 0 h = prev)
    (remaining_succ : ∀ (i : Nat) (h : i + 1 < (prev :: xs).length),
      remaining (prev :: xs) (i + 1) h = remaining_from prev xs i) :
    indexed_sortable remaining (prev :: xs) ↔ sortable_condition prev xs := by
  constructor
  · intro h i hi
    cases i with
    | zero =>
      have h0 := h 0 (by simpa using hi)
      rw [remaining_zero] at h0
      simpa using h0
    | succ j =>
      have hj : j + 1 < (prev :: xs).length := by
        simp only [List.length_cons] at hi ⊢
        omega
      have hj' : j + 2 < (prev :: xs).length := by
        simp only [List.length_cons] at hi ⊢
        omega
      have hs := h (j + 1) hj'
      rw [remaining_succ] at hs
      simpa using hs
  · intro h i hi
    cases i with
    | zero =>
      have h0 := h 0 (by simpa using hi)
      rw [remaining_zero]
      simpa using h0
    | succ j =>
      have hj : j + 1 < (prev :: xs).length := by
        simp only [List.length_cons] at hi ⊢
        omega
      have hc := h (j + 1) (by simpa using hi)
      rw [remaining_succ]
      simpa using hc

end List
