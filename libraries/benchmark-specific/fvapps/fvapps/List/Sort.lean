import Mathlib.Data.List.Sort

namespace Specific

open _root_.List

namespace List

/-! ## Sortedness predicate (Bool-based)

A computable, `Bool`-valued predicate checking whether a list is sorted in
non-decreasing order according to a `LE` instance. For the `Prop`-based
version, see `List.Sorted`. -/

/-- Returns `true` if the list is sorted (non-decreasing) according to `≤`.
Singleton and empty lists are considered sorted. -/
def isSorted [LE α] [DecidableRel (fun a b : α => a ≤ b)] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => decide (x ≤ y) && isSorted (y :: xs)

/-- Returns `true` if the list is pairwise sorted according to the `Bool`-valued
relation `le`.  Singleton and empty lists are trivially sorted.  This generalizes
`isSorted` (which uses `≤` from a `LE` instance) to any custom comparison predicate. -/
def sortedBy {α : Type} (le : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => le x y && sortedBy le (y :: rest)

/-! ## General-purpose `Bool`-based sort

A `Bool`-based wrapper around `List.mergeSort`. Unlike `List.sort` (which
requires a `DecidableRel` instance), this version accepts an explicit `Bool`
comparison predicate, which is often more convenient in computational contexts. -/

/-- Sort a list using merge sort with a `Bool`-valued comparison predicate.
The resulting list is stable and runs in `O(n log n)` time. -/
def sortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  xs.mergeSort le

/-! ## Sorting by descending `Nat` score -/

/-- Sort a list by descending `Nat` score. -/
def sortByDescending {α : Type} (score : α → Nat) (l : List α) : List α :=
  insertionSort (fun a b : α => score b ≤ score a) l

/-- Sort a list of natural numbers in descending order. -/
def sortDesc (l : List Nat) : List Nat :=
  sortByDescending id l

/-- The result of `sortByDescending` is sorted by the descending score. -/
theorem sortByDescending_sorted {α : Type} (score : α → Nat) (l : List α) :
    Sorted (fun a b : α => score b ≤ score a) (sortByDescending score l) := by
  let rel : α → α → Prop := fun a b => score b ≤ score a
  haveI : IsTotal α rel := ⟨fun a b => Nat.le_total (score b) (score a)⟩
  haveI : IsTrans α rel := ⟨fun _ _ _ hab hbc => Nat.le_trans hbc hab⟩
  simpa [sortByDescending] using
    sorted_insertionSort rel l

/-- Membership is preserved by `sortByDescending`. -/
theorem mem_sortByDescending_of_mem {α : Type} (score : α → Nat) {x : α} {l : List α}
    (h : x ∈ l) : x ∈ sortByDescending score l := by
  simpa [sortByDescending] using
    ((mem_insertionSort (fun a b : α => score b ≤ score a)).2 h)

/-- `sortByDescending` preserves list length. -/
theorem length_sortByDescending {α : Type} (score : α → Nat) (l : List α) :
    (sortByDescending score l).length = l.length := by
  simp [sortByDescending]

/-- In a sorted list, the score of any element is ≤ the score of the head. -/
theorem score_le_head_score_of_mem_sorted_desc {α : Type} {score : α → Nat}
    {head x : α} {tail : List α}
    (hSorted : Sorted (fun a b : α => score b ≤ score a) (head :: tail))
    (hMem : x ∈ head :: tail) : score x ≤ score head := by
  cases hMem with
  | head => exact Nat.le_refl (score head)
  | tail _ hTail => exact rel_of_sorted_cons hSorted x hTail

/-! ## Bool-based insertion sort

Unlike `Mathlib.Data.List.Sort.insertionSort` which uses a `DecidableRel`, this
version takes an explicit `Bool`-valued comparison predicate. This is useful in
computational contexts where a `DecidableRel` instance is not available or
where an explicit comparison function is more natural. -/

/-- Insert element `x` into a list already sorted by the `Bool`-valued
predicate `le`. The element is placed before the first existing element `y`
for which `le x y` is `true`. -/
def insertSortedBy {α : Type u} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if le x y then
        x :: y :: ys
      else
        y :: insertSortedBy le x ys

/-- Sort a list using insertion sort with a `Bool`-valued comparison
predicate. This is a `Bool`-based variant of `List.insertionSort` that avoids
the need for `DecidableRel` instances. -/
def insertionSortBy {α : Type u} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertSortedBy le x (insertionSortBy le xs)

@[simp] theorem insertSortedBy_nil {α : Type u} (le : α → α → Bool) (x : α) :
    insertSortedBy le x [] = [x] :=
  rfl

@[simp] theorem insertionSortBy_nil {α : Type u} (le : α → α → Bool) :
    insertionSortBy le ([] : List α) = [] :=
  rfl

/-! ## Prop-based merge sort

Unlike `sortBy` which accepts a `Bool`-valued comparison predicate, `mergeSortByRel`
accepts a `Prop`-valued relation with a `Decidable` instance. Theorems about it
require the relation to be a total order. -/

/-- Sort a list using merge sort, driven by a `Prop`-valued relation `r`.
The relation must be decidable for all pairs. -/
def mergeSortByRel {α : Type u} (r : α → α → Prop)
    [∀ a b, Decidable (r a b)] (xs : List α) : List α :=
  xs.mergeSort (fun a b => decide (r a b))

/-- `mergeSortByRel` is idempotent when `r` is a total order (transitive,
antisymmetric, total). Applying it twice is the same as applying it once. -/
theorem mergeSortByRel_idempotent {α : Type u} (r : α → α → Prop)
    [∀ a b, Decidable (r a b)]
    (hTrans : ∀ {a b c}, r a b → r b c → r a c)
    (hAntisymm : ∀ {a b}, r a b → r b a → a = b)
    (hTotal : ∀ a b, r a b ∨ r b a) (xs : List α) :
    mergeSortByRel r (mergeSortByRel r xs) = mergeSortByRel r xs := by
  letI : IsTotal α r := ⟨hTotal⟩
  letI : IsTrans α r := ⟨fun _ _ _ hab hbc => hTrans hab hbc⟩
  letI : IsAntisymm α r := ⟨fun _ _ hab hba => hAntisymm hab hba⟩
  exact _root_.List.mergeSort_eq_self r (_root_.List.sorted_mergeSort' r xs)

/-! ## Merge two sorted lists

`mergeBy le xs ys` merges two lists assumed to be sorted by the `Bool`-valued
comparison predicate `le`, producing a single sorted list. This is a standard
merge step used in merge sort and related algorithms. -/

/-- Merge two lists according to a `Bool`-based comparison predicate `le`.
The input lists are assumed to be sorted by `le`, and the result is sorted by `le`.
This is a stable merge: when `le x y` is `false` and `le y x` is `false`, the
element from `xs` comes first. -/
def mergeBy {α : Type u} (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if le x y then
      x :: mergeBy le xs' (y :: ys')
    else
      y :: mergeBy le (x :: xs') ys'
termination_by xs.length + ys.length

/-! ## Sort by rank

Sort a list by a ranking function: `sortByRank rank xs` sorts `xs` according to
the order induced by `rank`. Elements are compared by their rank values:
`a` precedes `b` when `rank a ≤ rank b`.

This generalizes `sortByDescending` (which is specialized to `Nat` scores in
descending order) to any codomain with a `LE` instance and provides theorems
about sortedness, idempotence, length preservation, and membership preservation. -/

/-- `rankedLe rank a b` holds when `rank a ≤ rank b`. This lifts an order
from the codomain of `rank` to its domain. -/
def rankedLe {α β : Type} [LE β] (rank : α → β) (a b : α) : Prop :=
  rank a ≤ rank b

/-- `rankedLe` is decidable when the codomain's `≤` is decidable. -/
instance rankedLeDecidableRel {α β : Type} [LE β] [DecidableLE β] (rank : α → β) :
    DecidableRel (rankedLe rank) := fun a b =>
  inferInstanceAs (Decidable (rank a ≤ rank b))

/-- `rankedLe` is total when the codomain is a `LinearOrder`. -/
instance rankedLeIsTotal {α β : Type} [LinearOrder β] (rank : α → β) :
    IsTotal α (rankedLe rank) where
  total a b := le_total (rank a) (rank b)

/-- `rankedLe` is transitive when the codomain is a `Preorder`. -/
instance rankedLeIsTrans {α β : Type} [Preorder β] (rank : α → β) :
    IsTrans α (rankedLe rank) where
  trans _ _ _ := le_trans

/-- Sort a list using a ranking function. Elements are compared by their
rank values: `a` precedes `b` when `rank a ≤ rank b`. Uses insertion sort. -/
def sortByRank {α β : Type} [LE β] [DecidableLE β] (rank : α → β) (items : List α) :
    List α :=
  items.insertionSort (rankedLe rank)

@[simp]
theorem sortByRank_nil {α β : Type} [LE β] [DecidableLE β] (rank : α → β) :
    sortByRank rank [] = [] := rfl

/-- The result of `sortByRank` is sorted according to `rankedLe rank`. -/
theorem sortByRank_sorted {α β : Type} [LinearOrder β]
    (rank : α → β) (items : List α) :
    List.Sorted (rankedLe rank) (sortByRank rank items) := by
  unfold sortByRank
  exact List.sorted_insertionSort (rankedLe rank) items

/-- `sortByRank` is idempotent: sorting an already-sorted-by-rank list
does nothing. -/
theorem sortByRank_idempotent {α β : Type} [LinearOrder β] (rank : α → β) (items : List α) :
    sortByRank rank (sortByRank rank items) = sortByRank rank items :=
  List.Sorted.insertionSort_eq (sortByRank_sorted rank items)

@[simp]
theorem length_sortByRank {α β : Type} [LE β] [DecidableLE β]
    (rank : α → β) (items : List α) :
    (sortByRank rank items).length = items.length :=
  List.length_insertionSort (rankedLe rank) items

@[simp]
theorem mem_sortByRank_iff {α β : Type} [LE β] [DecidableLE β]
    (rank : α → β) (items : List α) (item : α) :
    item ∈ sortByRank rank items ↔ item ∈ items :=
  List.mem_insertionSort (r := rankedLe rank)

end List

end Specific
