import Mathlib

open List

/-!
# `maxOver_specificDuplicate` — maximum of a mapped function over a list

`maxOver_specificDuplicate f l` computes `max_{x ∈ l} f x`, returning `0` for the empty list.
For a singleton `[a]`, returns `f a` directly (without comparing to `0`).
For longer lists, takes `max` of `f a` and the result on the tail.

This pattern appears in problems like CF 276A ("Lunch Rush"), where the goal
is to find the maximum of `f x` over all elements `x` in a list.
-/

namespace List

variable {α β : Type _} [LinearOrder β] [Zero β]

/-- Compute the maximum of `f a` over all `a ∈ l`. Returns `0` for the empty list.
For a singleton `[a]`, returns `f a` directly; for longer lists, recursively takes `max`. -/
def maxOver_specificDuplicate (f : α → β) : List α → β
  | [] => 0
  | [a] => f a
  | a :: as => max (f a) (maxOver_specificDuplicate f as)

/-- For every element `x ∈ l`, `maxOver_specificDuplicate f l` is at least `f x`. -/
lemma maxOver_ge_mem (f : α → β) (l : List α) (x : α) (hx : x ∈ l) :
    maxOver_specificDuplicate f l ≥ f x := by
  induction' l with a as ih generalizing x
  · exfalso; exact List.not_mem_nil x hx
  · simp at hx
    rcases hx with (h_eq | hx_as)
    · subst h_eq
      cases' as with a' as'
      · unfold maxOver_specificDuplicate; exact le_refl _
      · unfold maxOver_specificDuplicate; exact le_max_left _ _
    · cases' as with a' as'
      · exfalso; exact List.not_mem_nil x hx_as
      · have h_ih := ih x hx_as
        unfold maxOver_specificDuplicate
        exact le_trans h_ih (le_max_right _ _)

/-- If `l` is nonempty, then `maxOver_specificDuplicate f l` equals `f x` for some `x ∈ l`. -/
lemma maxOver_eq_mem (f : α → β) (l : List α) (hne : l ≠ []) :
    ∃ x ∈ l, maxOver_specificDuplicate f l = f x := by
  induction' l with a as ih
  · exfalso; exact hne rfl
  · by_cases h_as_ne : as = []
    · subst h_as_ne
      refine ⟨a, by simp, ?_⟩
      unfold maxOver_specificDuplicate; rfl
    · have h_ih := ih h_as_ne
      rcases h_ih with ⟨x, hx, h_eq⟩
      cases' as with a' as'
      · contradiction
      · unfold maxOver_specificDuplicate
        by_cases hle : f a ≤ maxOver_specificDuplicate f (a' :: as')
        · rw [max_eq_right hle]
          refine ⟨x, List.mem_cons_of_mem _ hx, h_eq⟩
        · have hle' : maxOver_specificDuplicate f (a' :: as') ≤ f a := le_of_not_ge hle
          rw [max_eq_left hle']
          refine ⟨a, by simp, rfl⟩

/-! ### `maxMap` — maximum of `f a` over `a ∈ l` with custom default and decoupled types

`maxMap default f l` computes `max_{x ∈ l} f x`, returning `default` when `l` is empty.
Unlike `maxOver_specificDuplicate`, this version parameterizes the default value and decouples the list
element type from the result type (`f : β → α` with list `List β`).
It also only requires `Max α` rather than `LinearOrder α + Zero α`. -/

/-- Maximum of `f a` over `a ∈ l`, returning `default` when `l` is empty.
For a singleton `[x]`, returns `f x` directly. For longer lists, takes `max`. -/
def maxMap {α β : Type _} [Max α] (default : α) (f : β → α) : List β → α
  | [] => default
  | x :: [] => f x
  | x :: y :: xs => max (f x) (maxMap default f (y :: xs))

/-- For every element `x ∈ l`, `maxMap default f l` is at least `f x`. -/
lemma le_maxMap_of_mem {α β : Type _} [LinearOrder α] {default : α} {f : β → α}
    {x : β} {xs : List β} (hmem : x ∈ xs) : f x ≤ maxMap default f xs := by
  induction xs with
  | nil => simp at hmem
  | cons head xs ih =>
      cases xs with
      | nil =>
          rw [List.mem_singleton] at hmem
          subst x
          simp [maxMap]
      | cons next rest =>
          rw [List.mem_cons] at hmem
          rw [maxMap]
          rcases hmem with hmem | hmem
          · subst x
            exact le_max_left _ _
          · exact le_trans (ih hmem) (le_max_right _ _)

/-- If `l` is nonempty, then `maxMap default f l` equals `f x` for some `x ∈ l`. -/
lemma exists_maxMap_eq_of_ne_nil {α β : Type _} [LinearOrder α] {default : α} {f : β → α}
    {xs : List β} (hne : xs ≠ []) : ∃ x, x ∈ xs ∧ f x = maxMap default f xs := by
  induction xs with
  | nil => contradiction
  | cons head xs ih =>
      cases xs with
      | nil =>
          refine ⟨head, by simp, ?_⟩
          simp [maxMap]
      | cons next rest =>
          have htail_ne : next :: rest ≠ [] := by simp
          rcases ih htail_ne with ⟨bestTail, hbestMem, hbestEq⟩
          by_cases hle : maxMap default f (next :: rest) ≤ f head
          · refine ⟨head, by simp, ?_⟩
            simp [maxMap, max_eq_left hle]
          · refine ⟨bestTail, by simp [hbestMem], ?_⟩
            have hhead_le : f head ≤ maxMap default f (next :: rest) :=
              le_of_not_ge hle
            simp [maxMap, hbestEq, max_eq_right hhead_le]

/-! ### `listMaxWith` — maximum with default always included

`listMaxWith default f l` computes `max {default, f x | x ∈ l}`. Unlike `maxMap`,
this always includes the default value in the maximum comparison — even for singleton
and empty lists. The recursion is uniform (no special singleton case), which makes
inductive proofs simpler.

For example, `listMaxWith 1 Int.toNat piles` computes the maximum element of a list
of positive integers, with a guaranteed lower bound of 1. -/

/-- Maximum of `f a` over `a ∈ l`, always including `default` in the comparison.
`listMaxWith d f [] = d` and `listMaxWith d f (x :: xs) = max (f x) (listMaxWith d f xs)`.
For singleton `[x]`, returns `max (f x) default` (cf. `maxMap` which returns `f x`). -/
def listMaxWith (default : Nat) (f : α → Nat) : List α → Nat
  | [] => default
  | x :: xs => max (f x) (listMaxWith default f xs)

/-- The default value is never larger than `listMaxWith`: `default ≤ listMaxWith default f xs`. -/
lemma default_le_listMaxWith (default : Nat) (f : α → Nat) (xs : List α) :
    default ≤ listMaxWith default f xs := by
  induction xs with
  | nil => simp [listMaxWith]
  | cons x xs ih =>
      simp only [listMaxWith]
      exact le_trans ih (Nat.le_max_right _ _)

/-- For every element `x ∈ xs`, `f x` is at most `listMaxWith default f xs`. -/
lemma le_listMaxWith_of_mem {default : Nat} {f : α → Nat} {xs : List α} {x : α}
    (hx : x ∈ xs) : f x ≤ listMaxWith default f xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [listMaxWith]
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact le_trans (ih hx) (Nat.le_max_right _ _)

/-- Upper bound for `listMaxWith`: if `default ≤ b` and every `f x ≤ b` for `x ∈ xs`,
then `listMaxWith default f xs ≤ b`. -/
lemma listMaxWith_le_of_forall_le {default b : Nat} {f : α → Nat} {xs : List α}
    (hdefault : default ≤ b) (hall : ∀ x ∈ xs, f x ≤ b) : listMaxWith default f xs ≤ b := by
  induction xs with
  | nil =>
      simpa [listMaxWith] using hdefault
  | cons x xs ih =>
      simp only [listMaxWith]
      apply max_le
      · exact hall x (by simp)
      · apply ih
        intro y hy
        exact hall y (by simp [hy])

/-! ### `maxBySecond` — pair with maximum second component

`maxBySecond l` returns the pair in `l` with the largest second component.
Returns `(0, 0)` for the empty list. Ties are broken in favor of the earlier element.
This pattern recurs in window-maximization algorithms (e.g., LeetCode 674) where
candidate windows are represented as `(start, length)` pairs and the longest valid
window is found by maximizing the second component. -/

/-- Find the pair in `l` with the maximum second component.
Returns `(0, 0)` for the empty list. On ties, the earlier element in the list is returned
(since `p.2 < q.2 then q else p` keeps `p` when `p.2 = q.2` or `p.2 > q.2`). -/
def maxBySecond : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | p :: ps =>
      let q := maxBySecond ps
      if p.2 < q.2 then q else p

/-- If the input list is nonempty, `maxBySecond` returns an element of that list. -/
lemma maxBySecond_mem_of_ne_nil {xs : List (ℕ × ℕ)} (hxs : xs ≠ []) :
    maxBySecond xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons p ps ih =>
      by_cases hlt : p.2 < (maxBySecond ps).2
      · simp [maxBySecond, hlt]
        right
        exact ih (by
          intro hps
          subst hps
          simp [maxBySecond] at hlt)
      · simp [maxBySecond, hlt]

/-- For every pair `p` in `xs`, `p.2 ≤ (maxBySecond xs).2`. -/
lemma snd_le_maxBySecond_of_mem {p : ℕ × ℕ} {xs : List (ℕ × ℕ)} (hp : p ∈ xs) :
    p.2 ≤ (maxBySecond xs).2 := by
  induction xs with
  | nil => simp at hp
  | cons x xs ih =>
      by_cases hlt : x.2 < (maxBySecond xs).2
      · simp [maxBySecond, hlt] at hp ⊢
        rcases hp with hp | hp
        · subst hp
          exact Nat.le_of_lt hlt
        · exact ih hp
      · simp [maxBySecond, hlt] at hp ⊢
        rcases hp with hp | hp
        · subst hp
          rfl
        · exact Nat.le_trans (ih hp) (Nat.le_of_not_gt hlt)

end List
