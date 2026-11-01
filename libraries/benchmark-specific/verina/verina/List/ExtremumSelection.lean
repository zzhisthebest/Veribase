import Mathlib.Data.List.Basic
import verina.List.Sort

namespace Specific

open _root_.List

namespace List

/-! ## Maximum/Extremum selection over lists -/

/-- Maximum `Nat` score in a list, with `0` for an empty list. -/
def listMaxBy {α : Type} (score : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => max (score x) (listMaxBy score xs)

/-- Maximum of a list of natural numbers, with `0` for an empty list. -/
def listMax : List Nat → Nat :=
  listMaxBy id

@[simp] theorem listMaxBy_nil {α : Type} (score : α → Nat) : listMaxBy score [] = 0 := rfl

@[simp] theorem listMax_nil : listMax ([] : List Nat) = 0 := rfl

@[simp] theorem listMax_singleton (n : Nat) : listMax [n] = n := by simp [listMax, listMaxBy]

/-- The maximum score is bounded by any upper bound of all scores. -/
theorem listMaxBy_le_of_forall_mem {α : Type} (score : α → Nat) (l : List α)
    {bound : Nat} (h : ∀ x, x ∈ l → score x ≤ bound) :
    listMaxBy score l ≤ bound := by
  induction l with
  | nil => simp [listMaxBy]
  | cons x xs ih =>
      simp [listMaxBy, h x (by simp),
        ih (fun z hz => h z (by simp [hz]))]

/-- The maximum of a list of naturals is bounded by any upper bound. -/
theorem listMax_le_of_forall_mem (l : List Nat) {bound : Nat}
    (h : ∀ x, x ∈ l → x ≤ bound) : listMax l ≤ bound :=
  listMaxBy_le_of_forall_mem id l h

/-- The maximum score is at most the score of the head in a sorted list. -/
theorem listMaxBy_le_head_of_sorted_permutation {α : Type} (score : α → Nat)
    {l : List α} {head : α} {tail : List α}
    (hSort : sortByDescending score l = head :: tail) :
    listMaxBy score l ≤ score head :=
  listMaxBy_le_of_forall_mem score l (fun x hx => by
    have hMemSort : x ∈ sortByDescending score l :=
      mem_sortByDescending_of_mem score hx
    rw [hSort] at hMemSort
    exact score_le_head_score_of_mem_sorted_desc
      (by simpa [hSort] using sortByDescending_sorted score l) hMemSort)

/-! ## Minimum over lists -/

/-- Minimum `Nat` score in a list, with a customizable default for the empty list. -/
def listMinByD (default : Nat) (score : α → Nat) : List α → Nat
  | [] => default
  | x :: xs => xs.foldl (fun best item => Nat.min best (score item)) (score x)

/-- Minimum of a list of natural numbers, with a customizable default for the empty list. -/
def listMinD (default : Nat) : List Nat → Nat :=
  listMinByD default id

/-- Minimum of a list of natural numbers, with `0` for an empty list. -/
def listMin : List Nat → Nat :=
  listMinD 0

@[simp] theorem listMinByD_nil {α : Type} (default : Nat) (score : α → Nat) :
    listMinByD default score [] = default := rfl

@[simp] theorem listMinByD_singleton {α : Type} (default : Nat) (score : α → Nat) (x : α) :
    listMinByD default score [x] = score x := by
  simp [listMinByD]

@[simp] theorem listMinD_nil (default : Nat) : listMinD default [] = default := by
  simp [listMinD]

@[simp] theorem listMin_nil : listMin ([] : List Nat) = 0 := rfl

@[simp] theorem listMinD_singleton (default x : Nat) : listMinD default [x] = x := by
  simp [listMinD]

@[simp] theorem listMin_singleton (x : Nat) : listMin [x] = x := by
  simp [listMin, listMinD]

/-- `listMinD` with duplicate elements returns the element. -/
theorem listMinD_duplicate (default x : Nat) :
    listMinD default [x, x] = x := by
  simp [listMinD, listMinByD]

end List

end Specific
