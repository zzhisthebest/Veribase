import Mathlib
import general.String.CharacterStatistics
import general.List.DynamicProgramming

namespace List

/-! # Edit Distance (Levenshtein Distance)

The Levenshtein edit distance between two lists: the minimum number of
single-element insertions, deletions, or substitutions needed to transform
one list into the other.

This module provides:
- `List.editDistance` for any `[DecidableEq α]` lists
- `String.editDistance` as the string wrapper
-/

/-- Levenshtein edit distance between two lists.
Each edit operation (insert, delete, substitute) costs 1.
Two equal elements at the same position cost 0.

For example:
* `editDistance "kitten".data "sitting".data = 3`
* `editDistance "abc".data "abc".data = 0`
* `editDistance "".data "abc".data = 3` -/
def editDistance [DecidableEq α] : List α → List α → Nat
  | [], t => t.length
  | s, [] => s.length
  | sHead :: sTail, tHead :: tTail =>
      if sHead = tHead then
        editDistance sTail tTail
      else
        let del := editDistance sTail (tHead :: tTail) + 1
        let ins := editDistance (sHead :: sTail) tTail + 1
        let sub := editDistance sTail tTail + 1
        Nat.min del (Nat.min ins sub)

/-! ### DP matrix computation

The functions below provide an efficient dynamic-programming implementation
of the Levenshtein distance. Instead of the exponential recursive definition,
they build the DP matrix row by row in O(n*m) time. -/

/-- A single step in the Levenshtein DP matrix: computes the cost of aligning `c1` with `c2`
given the three neighboring cells (`up`, `left`, `diag`).
If `c1 = c2`, the cost is `diag` (no edit needed);
otherwise the cost is `1 + min(up, left, diag)`. -/
def editDistanceStep {α : Type u} [DecidableEq α] (c1 c2 : α) (up left diag : Nat) : Nat :=
  if c1 = c2 then diag else 1 + Nat.min (Nat.min up left) diag

/-- Compute one row of the Levenshtein DP matrix.
Given the current character `c1` from the first list, the previous row `prevRow`,
and the second list `l2`, produces the new row of DP values. -/
def editDistanceRow {α : Type u} [DecidableEq α] (c1 : α) (prevRow : List Nat) (l2 : List α) : List Nat :=
  match prevRow with
  | [] => []
  | prev0 :: prevRest =>
    let left0 : Nat := prev0 + 1
    let rec go (xs : List α) (ps : List Nat) (left diag : Nat) (acc : List Nat) : List Nat :=
      match xs, ps with
      | [], _ => left0 :: acc.reverse
      | c2 :: ts, up :: psTail =>
        let cur := editDistanceStep c1 c2 up left diag
        go ts psTail cur up (cur :: acc)
      | _ :: _, [] =>
        left0 :: acc.reverse
    go l2 prevRest left0 prev0 []

/-- Compute the Levenshtein distance between two lists using the DP matrix algorithm
(row-by-row iteration). This is more efficient than the recursive `editDistance` for
larger inputs because it avoids exponential branching.

The algorithm initializes the first row as `[0, 1, 2, ..., l2.length]` and then
iterates through each character of `l1`, updating the row using `editDistanceRow`.
The final answer is the last element of the final row. -/
def editDistanceDP {α : Type u} [DecidableEq α] (l1 l2 : List α) : Nat :=
  let initRow : List Nat := List.range (l2.length + 1)
  let rec go (l1 : List α) (prev : List Nat) : Nat :=
    match l1 with
    | [] => prev.getLast?.getD 0
    | c1 :: t1 =>
      let newPrev := editDistanceRow c1 prev l2
      go t1 newPrev
  go l1 initRow

end List

namespace String

/-- Levenshtein edit distance between two strings.
This is the minimum number of single-character insertions, deletions,
or substitutions needed to transform `s` into `t`.

For example:
* `editDistance "kitten" "sitting" = 3`
* `editDistance "abc" "abc" = 0`
* `editDistance "" "abc" = 3` -/
def editDistance (s t : String) : Nat :=
  List.editDistance s.data t.data

end String

namespace String

/-! ## Edit distance -/

/--
Checks whether two strings are one edit distance apart
(insert/delete/replace exactly one character).
-/
def isOneEditDistance (s t : String) : Bool :=
  List.isOneEditDistance s.data t.data

end String
