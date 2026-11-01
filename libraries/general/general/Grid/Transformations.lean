import general.Grid.Core

namespace Grid

/-! ### Matrix transformations (transpose, rotate) -/

/-- Transpose a rectangular grid: rows become columns and vice versa.
The result has `(grid.headD []).length` rows and `grid.length` columns.
Uses `[Inhabited α]` for `!` indexing (always in-bounds for rectangular grids). -/
def transpose {α : Type} [Inhabited α] (grid : List (List α)) : List (List α) :=
  let n := grid.length
  let m := (grid.headD []).length
  (List.range m).map fun j => (List.range n).map fun i => (grid[i]!)[j]!

/-- Rotate a grid 90 degrees clockwise.
For each column index `j`, collect the `j`-th element of each row (top to bottom),
then reverse. Equivalent to `transpose grid` followed by reversing each row.
The result has `(grid.head!).length` rows and `grid.length` columns. -/
def rotate {α : Type} [Inhabited α] (grid : List (List α)) : List (List α) :=
  match grid with
  | [] => []
  | row :: _ =>
    let n := row.length
    (List.range n).map fun j =>
      (grid.map fun r => r[j]!).reverse

/-- The number of rows in the transposed grid equals the number of columns
in the original grid. -/
theorem transpose_length {α : Type} [Inhabited α] (grid : List (List α)) :
    (transpose grid).length = (grid.headD []).length := by
  unfold transpose
  simp

/-- When the grid is nonempty, the number of rows in the rotated grid equals
the length of the first row of the original grid. -/
theorem rotate_length {α : Type} [Inhabited α] (grid : List (List α)) (h_nonempty : grid ≠ []) :
    (rotate grid).length = (grid.head!).length := by
  unfold rotate
  cases grid with
  | nil => exact absurd rfl h_nonempty
  | cons row _ => simp

/-! ### Rotate with explicit default value (no `Inhabited` constraint) -/

/-- Rotate a square matrix 90 degrees clockwise, using a `default` value
to fill positions that fall outside the matrix bounds.

Unlike `Grid.rotate`, this does not require `[Inhabited α]` and uses
safe indexing (`getD` instead of `!`). The result is an `n × n` matrix
where `n = m.length` and cell `(i, j)` is `m[n-1-j][i]` (or `default`
when the original cell is absent). -/
def rotate90 (default : α) (m : List (List α)) : List (List α) :=
  let n := m.length
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      match m[n - 1 - j]? with
      | some row => (row[i]?).getD default
      | none => default

/-- The number of rows in a `rotate90`-rotated matrix equals the number of rows
in the original matrix. -/

theorem rotate90_length (default : α) (m : List (List α)) :
    (rotate90 default m).length = m.length := by
  unfold rotate90
  simp

/-- Reaching a rotation of `k` times via `Function.iterate` preserves the row count. -/
theorem rotate90_iterate_length (default : α) (m : List (List α)) (k : ℕ) :
    ((rotate90 default)^[k] m).length = m.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', rotate90_length, ih]

/-- When a nonempty grid has a nonempty first row, rotating it and looking at
the first row gives a list whose length equals the number of rows in the original grid. -/
theorem rotate_headD_length {α : Type} [Inhabited α] (grid : List (List α)) (h_nonempty : grid ≠ [])
    (h_headlen : (grid.head!).length > 0) : ((rotate grid).headD []).length = grid.length := by
  cases grid with
  | nil => contradiction
  | cons row rows =>
    cases row with
    | nil => simp at h_headlen
    | cons a as => simp [rotate, List.range_succ_eq_map]

end Grid
