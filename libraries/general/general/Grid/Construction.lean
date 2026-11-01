import general.Grid.Regions

namespace Grid

/-! ### Mapping over grid indices -/

/-- Map a function over all valid indices of a (possibly ragged) list of lists.
For each row `ri < grid.length` and column `ci < rowLen ri`, applies `f ri ci`. -/
def indicesMap (grid : List (List α)) (f : Nat → Nat → β) : List (List β) :=
  (List.range grid.length).map (fun ri =>
    let rowLen := ((grid[ri]?).getD []).length
    (List.range rowLen).map (fun ci => f ri ci))


lemma length_indicesMap (grid : List (List α)) (f : Nat → Nat → β) :
    (indicesMap grid f).length = grid.length := by
  unfold indicesMap
  simp

lemma getElem_indicesMap (grid : List (List α)) (f : Nat → Nat → β) (i : Nat)
    {h : i < (indicesMap grid f).length} :
    (indicesMap grid f)[i] =
    (List.range (((grid[i]?).getD []).length)).map (fun j => f i j) := by
  have hi : i < grid.length := by
    rw [← length_indicesMap grid f]
    exact h
  unfold indicesMap
  have hi_map : i < (((List.range grid.length).map (fun ri =>
    let rowLen := ((grid[ri]?).getD []).length
    (List.range rowLen).map (fun ci => f ri ci))).length) := by
    simp [hi]
  rw [List.getElem_map (h := hi_map)]
  have hi_range : i < (List.range grid.length).length := by
    simpa using hi
  rw [List.getElem_range i hi_range]

/-! ### Tabulating a grid from a generating function -/

/-- Create an `m × n` rectangular grid by applying `f i j` to every cell `(i, j)`.
This is the 2D generalization of `tabulateNat` from `general/List`.
`tabulate m n f` produces a list of `m` rows, each of length `n`,
where the cell at row `i`, column `j` equals `f i j`. -/
def tabulate {α : Type} (m n : Nat) (f : Nat → Nat → α) : List (List α) :=
  (List.range m).map (λ i => (List.range n).map (λ j => f i j))

/-- The outer list of `tabulate m n f` has length `m`. -/

theorem length_tabulate {α : Type} (m n : Nat) (f : Nat → Nat → α) :
    (tabulate m n f).length = m := by
  simp [tabulate]

/-- For `i < m`, the `i`-th row of `tabulate m n f` has length `n`. -/
theorem length_row_tabulate {α : Type} (m n : Nat) (f : Nat → Nat → α) (i : Nat) (hi : i < m) :
    ((tabulate m n f).getD i []).length = n := by
  unfold tabulate
  have hlen : i < ((List.range m).map (λ i' => (List.range n).map (λ j => f i' j))).length := by
    simp [hi]
  rw [List.getD_eq_getElem _ _ hlen]
  simp

end Grid

