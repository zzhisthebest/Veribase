import Mathlib

open List

/-!
# Increasing run lengths in lists

`incRunLenEndingAt` computes the length of the maximal strictly increasing
contiguous run that ends at a given index. `incRunLenStartingAt` computes the
length of such a run starting at a given index (within a bound `n`).
`maxIncRunLenUpto` computes the maximum of `incRunLenEndingAt` over a prefix of indices.

These definitions appear in DP solutions to Codeforces problems like CF 447C
("Penguin and Lucky Ticket"), where the answer depends on the longest increasing
run that can be obtained by changing at most one element.
-/

namespace List

/-! ### Definitions -/

/-- Length of the maximal strictly increasing contiguous run that *ends* at index `j`.
For `j = 0`, always returns `1` (a singleton run).
For `j > 0`, if `s.getD j fallback > s.getD (j-1) fallback`, extends the previous
run by 1; otherwise, starts a new run of length 1.

Uses `List.getD` with an explicit `fallback` for out-of-bounds access. -/
def incRunLenEndingAt {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) : Nat :=
  match j with
  | 0 => 1
  | j'+1 =>
    if s.getD (j'+1) fallback > s.getD j' fallback then
      incRunLenEndingAt fallback s j' + 1
    else
      1

/-- Length of the maximal strictly increasing contiguous run that *starts* at index `j`,
considering only indices `< n`. Returns `1` if `j+1 ≥ n` or if the values at `j` and `j+1`
are not strictly increasing.

Uses `List.getD` with an explicit `fallback` for out-of-bounds access. -/
def incRunLenStartingAt {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) (n : Nat) : Nat :=
  if h : j + 1 < n then
    if s.getD j fallback < s.getD (j+1) fallback then
      incRunLenStartingAt fallback s (j+1) n + 1
    else
      1
  else
    1
termination_by n - j
decreasing_by
  omega

/-- Maximum value of `incRunLenEndingAt fallback s i` over all `i ∈ {0, …, j}`.
This is the cumulative maximum of prefix increasing run lengths. -/
def maxIncRunLenUpto {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) : Nat :=
  match j with
  | 0 => incRunLenEndingAt fallback s 0
  | j'+1 => max (incRunLenEndingAt fallback s (j'+1)) (maxIncRunLenUpto fallback s j')

/-! ### Basic lemmas about `incRunLenEndingAt` -/

/-- The increasing run length ending at any index is at least 1
(any single element forms a trivial increasing run). -/
lemma incRunLenEndingAt_ge_one {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) :
    1 ≤ incRunLenEndingAt fallback s j := by
  induction j with
  | zero => unfold incRunLenEndingAt; omega
  | succ j ih =>
    unfold incRunLenEndingAt
    split
    · omega
    · omega

/-- `incRunLenEndingAt fallback s j ≤ j + 1` — the run can contain at most
all elements from index 0 up to index `j` inclusive. -/
lemma incRunLenEndingAt_le_succ {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) :
    incRunLenEndingAt fallback s j ≤ j + 1 := by
  induction j with
  | zero => unfold incRunLenEndingAt; omega
  | succ j ih =>
    unfold incRunLenEndingAt
    split
    · omega
    · omega

/-- For in-bounds indices, `incRunLenEndingAt` is bounded by the list length. -/
lemma incRunLenEndingAt_le_length {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat)
    (h : j < s.length) : incRunLenEndingAt fallback s j ≤ s.length := by
  have h_succ : incRunLenEndingAt fallback s j ≤ j + 1 :=
    incRunLenEndingAt_le_succ fallback s j
  omega

/-! ### Lemmas about `maxIncRunLenUpto` -/

/-- `maxIncRunLenUpto` is always at least 1. -/
lemma maxIncRunLenUpto_ge_one {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat) :
    1 ≤ maxIncRunLenUpto fallback s j := by
  induction j with
  | zero => unfold maxIncRunLenUpto; exact incRunLenEndingAt_ge_one fallback s 0
  | succ j ih =>
    unfold maxIncRunLenUpto
    exact le_trans ih (le_max_right _ _)

/-- `maxIncRunLenUpto` is bounded by the list length for in-bounds indices. -/
lemma maxIncRunLenUpto_le_length {α : Type u} [LinearOrder α] (fallback : α) (s : List α) (j : Nat)
    (h : j < s.length) : maxIncRunLenUpto fallback s j ≤ s.length := by
  induction j with
  | zero =>
    unfold maxIncRunLenUpto
    exact incRunLenEndingAt_le_length fallback s 0 h
  | succ j ih =>
    unfold maxIncRunLenUpto
    have h_j_succ : j.succ < s.length := h
    have h_j : j < s.length := by omega
    apply max_le
    · exact incRunLenEndingAt_le_length fallback s j.succ h_j_succ
    · exact ih h_j

/-! ### Strictly increasing prefix via structural recursion

These definitions compute the length of the longest strictly increasing prefix
of a list (`inc_prefix_len`) and the longest strictly increasing contiguous
subarray / run (`max_inc_run`) using structural recursion on the list (rather than
index-based access via `getD`). They are parameterized by an `LT` instance
with a decidable relation, so they work for any type with a decidable `(<)`. -/

section

variable {α : Type} [LT α] [DecidableRel ((· < ·) : α → α → Prop)]

/-- Length of the longest strictly increasing prefix of a list.
Returns `1` for a singleton list, `0` for the empty list.
For `x :: y :: rest`, if `x < y` then the prefix extends through `y`, so
the result is `inc_prefix_len (y :: rest) + 1`; otherwise it's `1`. -/
def inc_prefix_len : List α → Nat
  | [] => 0
  | [_] => 1
  | x :: y :: rest =>
    if x < y then inc_prefix_len (y :: rest) + 1
    else 1

/-- Maximum length of a strictly increasing contiguous subarray / run.
Recursively computes `max (inc_prefix_len (x :: rest)) (max_inc_run rest)`. -/
def max_inc_run : List α → Nat
  | [] => 0
  | x :: rest =>
    max (inc_prefix_len (x :: rest)) (max_inc_run rest)

lemma inc_prefix_len_le_length (xs : List α) : inc_prefix_len xs ≤ xs.length := by
  induction xs with
  | nil => simp [inc_prefix_len]
  | cons x xs ih =>
    match xs with
    | [] => simp [inc_prefix_len]
    | y :: rest =>
      simp [inc_prefix_len]
      split
      · rename_i hlt
        calc
          inc_prefix_len (y :: rest) + 1 ≤ (y :: rest).length + 1 := Nat.add_le_add_right ih 1
          _ = (x :: y :: rest).length := by simp
      · omega

lemma inc_prefix_len_ge_one (xs : List α) (hxs : xs ≠ []) : 1 ≤ inc_prefix_len xs := by
  induction xs with
  | nil => contradiction
  | cons x xs =>
    match xs with
    | [] => simp [inc_prefix_len]
    | y :: rest => simp [inc_prefix_len]; split <;> omega

end

end List
