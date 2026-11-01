import Mathlib

open List

namespace List

/-! ### List combinatorics: generating all lists of a given length

`listsOfLengthFrom` generates all lists of a given length `n` whose elements
are drawn from a pool `values`. This is the `n`-fold cartesian product of
`values` with itself, producing `|values|ⁿ` lists.

`listsOfLengthOver` is the specialization to `Nat` values in the range `[0, hi)`.
-/

/-- Generates all lists of length `n` whose elements come from `values`.
This is equivalent to the `n`-fold cartesian product of `values` with itself,
producing `|values|ⁿ` lists. For example,
`listsOfLengthFrom [0,1] 2` = `[[0,0],[0,1],[1,0],[1,1]]`. -/
def listsOfLengthFrom {α : Type} (values : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 =>
      values.flatMap fun x =>
        (listsOfLengthFrom values n).map fun xs => x :: xs

/-- Generates all lists of length `n` with elements in `[0, hi)`.
`listsOfLengthOver n hi = listsOfLengthFrom (List.range hi) n`. -/
def listsOfLengthOver (n hi : Nat) : List (List Nat) :=
  listsOfLengthFrom (List.range hi) n

/-- If `xs ∈ listsOfLengthFrom values n`, then `xs.length = n`. -/
lemma length_of_mem_listsOfLengthFrom {α : Type} {values : List α} {n : Nat} {xs : List α}
    (hxs : xs ∈ listsOfLengthFrom values n) :
    xs.length = n := by
  induction n generalizing xs with
  | zero =>
      simpa [listsOfLengthFrom] using hxs
  | succ n ih =>
      simp only [listsOfLengthFrom, List.mem_flatMap, List.mem_map] at hxs
      rcases hxs with ⟨x, _hx, ys, hys, rfl⟩
      simp [ih hys]

/-- If `xs ∈ listsOfLengthOver n hi`, then `xs.length = n`. -/
lemma length_of_mem_listsOfLengthOver {hi n : Nat} {xs : List Nat}
    (hxs : xs ∈ listsOfLengthOver n hi) :
    xs.length = n := by
  simpa [listsOfLengthOver] using
    (length_of_mem_listsOfLengthFrom (values := List.range hi) (n := n) (xs := xs) hxs)

/-- If every element of `xs` is in `values`, then `xs` belongs to the list of all
lists of length `xs.length` drawn from `values`. This is the completeness direction
of `listsOfLengthFrom`: any list whose elements are all in `values` is generated. -/
lemma mem_listsOfLengthFrom_of_all_mem {α : Type} {values : List α} {xs : List α}
    (hall : ∀ x ∈ xs, x ∈ values) :
    xs ∈ listsOfLengthFrom values xs.length := by
  induction xs with
  | nil =>
      simp [listsOfLengthFrom]
  | cons head tail ih =>
      have hhead : head ∈ values := hall head (by simp)
      have htail_all : ∀ x ∈ tail, x ∈ values := by
        intro x hx
        exact hall x (by simp [hx])
      simp only [length_cons, listsOfLengthFrom, List.mem_flatMap, List.mem_map]
      exact ⟨head, hhead, tail, ih htail_all, rfl⟩

/-- If every element of `xs` is in `values` and `xs.length = n`, then `xs`
belongs to `listsOfLengthFrom values n`. This combines `mem_listsOfLengthFrom_of_all_mem`
with a given length equality. -/
lemma mem_listsOfLengthFrom_of_all_mem_of_length {α : Type} {values : List α}
    {n : Nat} {xs : List α} (hlen : xs.length = n)
    (hall : ∀ x ∈ xs, x ∈ values) :
    xs ∈ listsOfLengthFrom values n := by
  simpa [hlen] using mem_listsOfLengthFrom_of_all_mem (values := values) (xs := xs) hall

end List
