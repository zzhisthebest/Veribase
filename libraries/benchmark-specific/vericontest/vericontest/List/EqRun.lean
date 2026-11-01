import Mathlib

open List

/-!
# Equal-value run lengths in lists

`runLenFrom` computes the length of the maximal contiguous prefix of a list
where every element equals a given `value`. This is the "equal-value run from start"
pattern: count how many leading elements match `value`.

`longestRun` computes the length of the longest contiguous run of `value`
anywhere in the list (not necessarily at the start).
-/

namespace List

/-! ### Prefix equal-value run length -/

/-- Length of the maximal contiguous prefix of `nums` where every element equals `value`.
Returns `0` for the empty list. For `x :: xs`, if `x = value`, the run extends by 1;
otherwise returns `0` (the run stops immediately).

Example: `runLenFrom [1, 1, 2, 1] 1 = 2`, `runLenFrom [1, 1, 2, 1] 2 = 0`. -/
def runLenFrom {α : Type} [DecidableEq α] (nums : List α) (value : α) : Nat :=
  match nums with
  | [] => 0
  | x :: xs => if x = value then 1 + runLenFrom xs value else 0

/-- `runLenFrom nums value` never exceeds the length of the list. -/
lemma runLenFrom_le_length {α : Type} [DecidableEq α] (nums : List α) (value : α) :
    runLenFrom nums value ≤ nums.length := by
  induction' nums with x xs ih
  · rfl
  · unfold runLenFrom
    split
    · simp; omega
    · simp

/-! ### Longest equal-value run anywhere in the list -/

/-- Length of the longest contiguous run of `value` anywhere in `nums`
(not necessarily at the start).

For `x :: xs`, computes `max (runLenFrom (x :: xs) value) (longestRun xs value)`.
Returns `0` for the empty list. -/
def longestRun {α : Type} [DecidableEq α] (nums : List α) (value : α) : Nat :=
  match nums with
  | [] => 0
  | _ :: xs => max (runLenFrom nums value) (longestRun xs value)

/-- `longestRun nums value` never exceeds the length of the list. -/
lemma longestRun_le_length {α : Type} [DecidableEq α] (nums : List α) (value : α) :
    longestRun nums value ≤ nums.length := by
  induction' nums with x xs ih
  · simp [longestRun]
  · have h_longest : longestRun (x :: xs) value = max (runLenFrom (x :: xs) value) (longestRun xs value) := rfl
    rw [h_longest]
    have h_len : (x :: xs).length = xs.length + 1 := by simp
    rw [h_len]
    apply max_le
    · have h := runLenFrom_le_length (x :: xs) value
      simpa [h_len] using h
    · omega

/-- If `value` appears in `nums`, then `longestRun nums value ≥ 1`. -/
lemma longestRun_pos_of_mem {α : Type} [DecidableEq α] (nums : List α) (value : α) (h : value ∈ nums) :
    1 ≤ longestRun nums value := by
  induction' nums with x xs ih
  · simp at h
  · have h_longest : longestRun (x :: xs) value = max (runLenFrom (x :: xs) value) (longestRun xs value) := rfl
    rw [h_longest]
    simp at h
    rcases h with (h_eq | hx)
    · rw [h_eq]
      have h_run : 1 ≤ runLenFrom (x :: xs) x := by
        unfold runLenFrom; simp
      have h_le_max : runLenFrom (x :: xs) x ≤ max (runLenFrom (x :: xs) x) (longestRun xs x) :=
        Nat.le_max_left _ _
      omega
    · have h_ih := ih hx
      have h_le_max : longestRun xs value ≤ max (runLenFrom (x :: xs) value) (longestRun xs value) :=
        Nat.le_max_right _ _
      omega

end List
