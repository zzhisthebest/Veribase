import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Mapping over a natural number range -/

/-- Map a function `f` over `[0, ..., count-1]`, producing a list of length `count`.
This is equivalent to `(range count).map f`. -/
def rangeMap {α : Type u} (count : Nat) (f : Nat → α) : List α :=
  (range count).map f

@[simp]
theorem rangeMap_length {α : Type u} (count : Nat) (f : Nat → α) :
    (rangeMap count f).length = count := by
  simp [rangeMap]

/-! ## Range from a starting offset -/

/-- Produces the list `[start, start+1, ..., start+count-1]`. -/
def rangeFrom (start : Nat) (count : Nat) : List Nat :=
  rangeMap count (fun i => start + i)

@[simp] theorem rangeFrom_length (start count : Nat) : (rangeFrom start count).length = count := by
  simp [rangeFrom]

end List

end Specific
