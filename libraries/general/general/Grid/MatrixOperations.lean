import general.Grid.Construction

namespace Grid

/-! ### Matrix multiplication -/

/-- Dot product of two lists, multiplying pairwise and summing.
Elements beyond the shorter list's length are ignored via `zip`. -/
def dotProduct {α : Type} [Semiring α] (r1 r2 : List α) : α :=
  (r1.zip r2).map (fun (a, b) => a * b) |>.sum

/-- Generic matrix multiplication via dot-product of each row of `mat1` with each column of `mat2`.
Uses `Grid.getCol` for column extraction (out-of-bounds entries default to `0` via `Inhabited` from `Zero`).
Requires `Inhabited α` for safe column indexing; implied by `Semiring α` which provides `Zero α`. -/
def matrixMul {α : Type} [Semiring α] [Inhabited α] (mat1 mat2 : List (List α)) : List (List α) :=
  let numCols := ((mat2.head?).getD []).length
  mat1.map (fun row =>
    (List.range numCols).map (fun j =>
      dotProduct row (getCol mat2 j)))

/-- The number of rows in the product matrix equals the number of rows in `mat1`. -/

theorem length_matrixMul {α : Type} [Semiring α] [Inhabited α] (mat1 mat2 : List (List α)) :
    (matrixMul mat1 mat2).length = mat1.length := by
  simp [matrixMul]

end Grid

