import Mathlib
import general.Nat.Distances
import general.List.Sort

namespace Grid

/-! ### 2D grid representation using `List (List α)` -/

/-- Number of columns in a grid. Returns the length of the first row,
or `0` for an empty grid. Equivalent to `(grid.headD []).length`. -/

def numCols {α : Type u} (grid : List (List α)) : Nat :=
  (grid.headD []).length

/-- Extract the row at index `i` from a 2D grid.
Returns `[]` if `i` is out of bounds. -/
def getRow {α : Type u} (grid : List (List α)) (i : Nat) : List α :=
  (grid[i]?).getD []

/-- Extract the column at index `j` from a 2D grid.
Uses `default` for missing elements. -/
def getCol {α : Type} [Inhabited α] (grid : List (List α)) (j : Nat) : List α :=
  grid.map (fun r => (r[j]?).getD default)

/-! ### Theorems about `getRow` -/

/-- `getRow` within bounds returns the i-th element. -/
theorem getRow_eq_get {α : Type} (grid : List (List α)) (i : Nat) (h : i < grid.length) :
    getRow grid i = grid[i] := by
  unfold getRow
  have : grid[i]? = some (grid[i]) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨h, rfl⟩
  simp [this]

/-- `getRow` of an out-of-bounds index returns `[]`. -/
theorem getRow_eq_nil_of_ge {α : Type} (grid : List (List α)) (i : Nat) (h : grid.length ≤ i) :
    getRow grid i = [] := by
  unfold getRow
  have : grid[i]? = none := by
    rw [List.getElem?_eq_none_iff]
    exact h
  simp [this]

/-! ### Theorems about `getCol` -/

/-- Length of a column equals the number of rows. -/

theorem length_getCol {α : Type} [Inhabited α] (grid : List (List α)) (j : Nat) :
    (getCol grid j).length = grid.length := by
  unfold getCol
  simp

/-- Safe access to a cell in a 2D grid; returns `some v` when both indices are in‑range. -/
def cell {α : Type u} (grid : List (List α)) (i j : Nat) : Option α :=
  grid[i]? >>= fun row => row[j]?

/-- Check if a cell in a 2D grid satisfies predicate `p`.
Returns `false` when either index is out of bounds.
Generalization of `cellIsOneB` to arbitrary predicates on `α`. -/
def cellSatisfies {α : Type u} (grid : List (List α)) (p : α → Bool) (i j : Nat) : Bool :=
  match cell grid i j with
  | some v => p v
  | none => false

/-- Access a cell in a 2D grid with a default value.
Returns `default` when either index is out of bounds.
Generalization of `matrixGet` from `Nat` to any type `α`. -/
def getCellD {α : Type u} (default : α) (grid : List (List α)) (i j : Nat) : α :=
  (grid[i]?).bind (fun row => row[j]?) |>.getD default

/-- When the inner `bind` expression yields `some v`, `getCellD` returns `v`
(regardless of the default value, since the cell was found). -/
theorem getCellD_eq_of_bind_eq_some {α : Type u} (grid : List (List α)) (d : α) (i j : Nat) (v : α)
    (h : (grid[i]?).bind (fun row => row[j]?) = some v) : getCellD d grid i j = v := by
  simp [getCellD, h]

/-- If the row index is out of bounds, `getCellD` returns the default value. -/
lemma getCellD_eq_default_of_ge_length {α : Type u} {default : α} {grid : List (List α)} {i j : Nat}
    (h : grid.length ≤ i) : getCellD default grid i j = default := by
  unfold getCellD
  have hget : grid[i]? = none := by
    rw [List.getElem?_eq_none_iff]
    exact h
  simp [hget]

/-- Access a cell in a 2D grid with a default value.
Uses `List.getD` for both the row access and the cell access, with `[]` as the
default for a missing row. Semantically equivalent to `getCellD default grid i j`
but with the grid as the first argument.

`listGet2D grid defaultVal i j = (grid.getD i []).getD j defaultVal` -/
def listGet2D {α : Type} (grid : List (List α)) (defaultVal : α) (i j : Nat) : α :=
  (grid.getD i []).getD j defaultVal

/-- `listGet2D` is equivalent to `getCellD` with the argument order swapped.
This connects the `getD`-based and `Option`-based formulations of 2D grid access. -/
lemma listGet2D_eq_getCellD {α : Type} (grid : List (List α)) (d : α) (i j : Nat) :
    listGet2D grid d i j = getCellD d grid i j := by
  simp [listGet2D, getCellD, List.getD]
  cases grid[i]? <;> simp

/-- Access a cell in a 2D grid, returning `0` for out-of-bounds via `[OfNat α 0]`.
Convenience form of `getCellD 0 grid i j`. -/
def getCellZero [OfNat α 0] (grid : List (List α)) (r c : Nat) : α :=
  getCellD 0 grid r c

/-! ### Column slice sum -/

/-- Sum of `k` elements in column `c` of a grid, starting at row `r`.
Uses `getCellZero` for OOB entries (which return `0`).
Generalized to any `AddCommMonoid α`. -/
def colSliceSum [AddCommMonoid α] [OfNat α 0] (grid : List (List α)) (c r k : Nat) : α :=
  (List.range k).map (λ i => getCellZero grid (r + i) c) |>.sum

/-! ### Rectangular grid predicate -/

/-- A grid is rectangular with `n` columns if every row has length `n`. -/
def Rectangular {α : Type u} (grid : List (List α)) (n : Nat) : Prop :=
  ∀ row ∈ grid, row.length = n

/-- A grid is rectangular when all rows have the same length (existential form).
Equivalent to `∃ n, Rectangular grid n`. -/
def isRectangular {α : Type u} (grid : List (List α)) : Prop :=
  ∃ n, Rectangular grid n

/-- `isRectangular` is equivalent to the existential of `Rectangular`. -/
theorem isRectangular_iff_exists_Rectangular {α : Type u} (grid : List (List α)) :
    isRectangular grid ↔ ∃ n, Rectangular grid n := by
  simp [isRectangular]

/-- A grid is *rectangular* when it is non-empty and all its rows
have the same length. This is a common precondition for functions that
treat a `List (List α)` as a 2D matrix. Note that rows are allowed to be
empty (yielding a 0-column matrix).

Unlike `isRectangular`, this requires `grid ≠ []`. Unlike `Rectangular`,
this does not require knowing the row length `n` in advance — instead it
uses a pairwise comparison of row lengths. -/
def IsRectangular (grid : List (List α)) : Prop :=
  grid ≠ [] ∧ ∀ r₁ ∈ grid, ∀ r₂ ∈ grid, r₁.length = r₂.length

/-! ### Square grid predicate -/

/-- A grid is square when the number of rows equals the number of columns.
That is, every row has length `grid.length`. Generalization of the `square` precondition
found in many LeetCode grid problems (e.g., shortest bridge, island perimeter).
Unlike the original problem-specific version, this does not require `grid.length ≥ 2`. -/
def isSquare {α : Type u} (grid : List (List α)) : Prop :=
  Rectangular grid grid.length

/-- A square grid is rectangular. -/
theorem isSquare.isRectangular {α : Type u} {grid : List (List α)} (h : isSquare grid) :
    isRectangular grid :=
  ⟨grid.length, h⟩

/-- A square grid has all rows of length equal to the grid length.
This is the expanded form matching the original `∀ i < grid.length, (grid[i]!).length = grid.length`
pattern, expressed safely via `getRow`. -/
theorem isSquare.row_length_eq {α : Type} (grid : List (List α)) (h : isSquare grid)
    (i : Nat) (hi : i < grid.length) : (getRow grid i).length = grid.length := by
  unfold isSquare at h
  have hmem : grid[i] ∈ grid := List.getElem_mem hi
  have hrow := h (grid[i]) hmem
  have hget := getRow_eq_get grid i hi
  calc
    (getRow grid i).length = (grid[i]).length := by rw [hget]
    _ = grid.length := hrow

/-- Decidable `Bool` version: check whether all rows in a grid have the same length.
Returns `true` for the empty grid. Unlike `Rectangular`, does not require knowing the
row length in advance. -/
def rowsSameLen {α : Type u} (grid : List (List α)) : Bool :=
  match grid with
  | [] => true
  | row :: rest => rest.all (fun r => r.length = row.length)


end Grid
