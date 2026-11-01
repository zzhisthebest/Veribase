import Mathlib

open List

/-!
# Non-decreasing lists

`is_non_decreasing` is a structural recursive predicate that holds when a list's
elements are non-decreasing: each element is `≤` the next. It is equivalent to
`List.Sorted (· ≤ ·)` but uses explicit pattern matching for convenient structural
induction proofs, and works with any `LE` type.

This module generalizes the `is_non_decreasing` predicate from LeetCode 665
("Non-decreasing Array") from `List Int` to any `LE α` type.
-/

namespace List

/-- `is_non_decreasing l` holds if `l` is non-decreasing: for every adjacent pair,
the first element is `≤` the second.
- `is_non_decreasing []` is `True`
- `is_non_decreasing [a]` is `True`
- `is_non_decreasing (a :: b :: l)` is `a ≤ b ∧ is_non_decreasing (b :: l)` -/
def is_non_decreasing {α : Type} [LE α] : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ is_non_decreasing (b :: rest)

/-- Characterization of `is_non_decreasing` on a list with at least two elements. -/
lemma is_non_decreasing_cons_cons_iff {α : Type} [LE α] {a b : α} {l : List α} :
    is_non_decreasing (a :: b :: l) ↔ a ≤ b ∧ is_non_decreasing (b :: l) := by
  simp [is_non_decreasing]

/-- If `a :: v :: rest` is non-decreasing, then replacing `v` with `a`
yields a non-decreasing list. This is useful when we want to "lower" a
value to match its predecessor while preserving sortedness.

For example, if `[1, 5, 6]` is non-decreasing, then `[1, 1, 6]` is also
non-decreasing because `1 ≤ 5` and `5 ≤ 6` implies `1 ≤ 6` by transitivity. -/
lemma is_non_decreasing_aa_of_av {α : Type} [Preorder α] {a v : α} {rest : List α}
    (h : is_non_decreasing (a :: v :: rest)) : is_non_decreasing (a :: a :: rest) := by
  rcases (is_non_decreasing_cons_cons_iff.mp h) with ⟨ha_le_v, hrest⟩
  have ha_rest_nd : is_non_decreasing (a :: rest) := by
    cases rest with
    | nil => simp [is_non_decreasing]
    | cons c cs =>
      rcases (is_non_decreasing_cons_cons_iff.mp hrest) with ⟨hv_le_c, hcs⟩
      have ha_le_c : a ≤ c := le_trans ha_le_v hv_le_c
      rw [is_non_decreasing_cons_cons_iff]
      exact ⟨ha_le_c, hcs⟩
  rw [is_non_decreasing_cons_cons_iff]
  exact ⟨le_refl a, ha_rest_nd⟩

end List
