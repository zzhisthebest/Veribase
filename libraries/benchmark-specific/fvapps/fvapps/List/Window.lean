import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## List window and slice (sublist extraction)

A window is a contiguous sublist identified by `start` position and `len` length.
-/

/-- Extract a window from `xs` starting at index `start` with length `len`.
`listWindow xs start len` returns `(xs.take (start + len)).drop start`. -/
def listWindow {α : Type u} (xs : List α) (start len : Nat) : List α :=
  (xs.take (start + len)).drop start

/-- Extract a slice from `xs` starting at index `start` with length `len`.
`slice xs start len = (xs.drop start).take len`.
Equivalent to `listWindow xs start len`. -/
def slice {α : Type u} (xs : List α) (start len : Nat) : List α :=
  (xs.drop start).take len

/-- Get a contiguous sublist from index `i` to index `j` (inclusive).
`sublist xs i j = slice xs i (j - i + 1)`. -/
def sublist {α : Type u} (xs : List α) (i j : Nat) : List α :=
  slice xs i (j - i + 1)

end List

end Specific
