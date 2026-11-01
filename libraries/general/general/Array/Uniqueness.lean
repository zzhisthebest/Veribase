import Mathlib
import general.List.Membership

namespace Array


/-! ### Unique elements — elements appearing exactly once -/

/-- Filter an array to retain only elements that appear exactly once.
Delegates to `List.uniqueElems` on the underlying list of `arr`.
This is the array counterpart of `List.uniqueElems`. -/
def uniqueElems {α : Type} [BEq α] (arr : Array α) : List α :=
  List.uniqueElems arr.toList



/-! ### Duplicate detection (early-exit) -/

/-- Check if element at index `i` has a duplicate at index `j` or later.
This is a helper for `anyDuplicatePairFrom`.
The outer loop should guarantee `i < arr.size`, but this function is safe
regardless: `arr[i]!` uses a default value when `i` is out of bounds. -/
def anyDuplicateOfAt {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (i j : Nat) : Bool :=
  if h_j : j < arr.size then
    if h_ne : j ≠ i then
      if arr[i]! = arr[j]! then
        true
      else
        anyDuplicateOfAt arr i (j + 1)
    else
      anyDuplicateOfAt arr i (j + 1)
  else
    false
termination_by arr.size - j

/-- Check if any element starting from index `i` onward has a duplicate
elsewhere in the array. Returns `true` if a duplicate pair exists,
`false` otherwise. -/
def anyDuplicatePairFrom {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (i : Nat) : Bool :=
  if h_i : i < arr.size then
    if anyDuplicateOfAt arr i 0 then
      true
    else
      anyDuplicatePairFrom arr (i + 1)
  else
    false
termination_by arr.size - i

/-- Check if an array contains any duplicate elements.
Returns `true` if there exist distinct indices `i`, `j`
with `arr[i] = arr[j]`, `false` otherwise. -/
def hasDuplicate {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) : Bool :=
  anyDuplicatePairFrom arr 0

/-- Specification for `hasDuplicate`: returns `true` iff there exist distinct indices
`i < arr.size` and `j < arr.size` such that `arr[i]! = arr[j]!`. -/
theorem hasDuplicate_iff {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) :
    (hasDuplicate arr = true) ↔ (∃ i j, i < arr.size ∧ j < arr.size ∧ i ≠ j ∧ arr[i]! = arr[j]!) := by
  have inner (i j : Nat) : anyDuplicateOfAt arr i j = true ↔
      ∃ k, j ≤ k ∧ k < arr.size ∧ k ≠ i ∧ arr[i]! = arr[k]! := by
    induction h : arr.size - j using Nat.strong_induction_on generalizing j with
    | h n ih =>
      rw [anyDuplicateOfAt]
      by_cases hj : j < arr.size
      · rw [dif_pos hj]
        have hn : arr.size - (j+1) < n := by omega
        have hr := ih _ hn (j+1) rfl
        have advance (hb : ¬ (j ≠ i ∧ arr[i]! = arr[j]!)) :
            (∃ k, j+1 ≤ k ∧ k < arr.size ∧ k ≠ i ∧ arr[i]! = arr[k]!) ↔
            (∃ k, j ≤ k ∧ k < arr.size ∧ k ≠ i ∧ arr[i]! = arr[k]!) := by
          constructor
          · rintro ⟨k, hk, hs, hn, he⟩; exact ⟨k, by omega, hs, hn, he⟩
          · rintro ⟨k, hk, hs, hn, he⟩
            refine ⟨k, ?_, hs, hn, he⟩
            by_contra hbad
            have : k = j := by omega
            subst k
            exact hb ⟨hn, he⟩
        by_cases hne : j ≠ i
        · rw [dif_pos hne]
          by_cases he : arr[i]! = arr[j]!
          · rw [if_pos he]
            exact iff_of_true rfl ⟨j, le_rfl, hj, hne, he⟩
          · rw [if_neg he, hr]
            exact advance (by tauto)
        · rw [dif_neg hne, hr]
          exact advance (by tauto)
      · rw [dif_neg hj]
        simp only [Bool.false_eq_true, false_iff, not_exists]
        rintro k ⟨hk, hs, _, _⟩; omega
  have outer (i : Nat) : anyDuplicatePairFrom arr i = true ↔
      ∃ j k, i ≤ j ∧ j < arr.size ∧ k < arr.size ∧ j ≠ k ∧ arr[j]! = arr[k]! := by
    induction h : arr.size - i using Nat.strong_induction_on generalizing i with
    | h n ih =>
      rw [anyDuplicatePairFrom]
      by_cases hi : i < arr.size
      · rw [dif_pos hi]
        have hn : arr.size - (i+1) < n := by omega
        have hr := ih _ hn (i+1) rfl
        by_cases hd : anyDuplicateOfAt arr i 0 = true
        · simp only [hd, ↓reduceIte, true_iff]
          obtain ⟨k, _, hk, hne, he⟩ := (inner i 0).mp hd
          exact ⟨i, k, le_rfl, hi, hk, Ne.symm hne, he⟩
        · have hf : anyDuplicateOfAt arr i 0 = false := by
            cases hb : anyDuplicateOfAt arr i 0 <;> simp_all
          simp only [hf, Bool.false_eq_true, ↓reduceIte, hr]
          constructor
          · rintro ⟨j, k, hj, hs, hk, hn, he⟩; exact ⟨j, k, by omega, hs, hk, hn, he⟩
          · rintro ⟨j, k, hj, hs, hk, hn, he⟩
            refine ⟨j, k, ?_, hs, hk, hn, he⟩
            by_contra hbad
            have : j = i := by omega
            subst j
            exact hd ((inner i 0).mpr ⟨k, Nat.zero_le _, hk, Ne.symm hn, he⟩)
      · rw [dif_neg hi]
        simp only [Bool.false_eq_true, false_iff, not_exists]
        rintro j k ⟨hj, hs, _, _, _⟩; omega
  simpa [hasDuplicate] using outer 0


end Array
