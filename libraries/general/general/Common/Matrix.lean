import Mathlib

namespace Matrix

/-! ### Element access -/

/-- Get the `i`-th row of a matrix, given a proof that `i` is in bounds.
This is a safe wrapper around `List.get` with a `Fin` index. -/

def getRow (matrix : List (List α)) (i : Nat) (hi : i < matrix.length) : List α :=
  matrix.get ⟨i, hi⟩

/-- Get the element at row `i`, column `j` of a 2D list (list-of-lists),
or `none` if either index is out of bounds. -/
def getElem? (m : List (List α)) (i j : Nat) : Option α :=
  m[i]? >>= fun row => row[j]?

/-- When all rows of a matrix have length `n`, and `i < M.length`, `j < n`, then
`getElem? M i j` is not `none`. This is the key safety lemma: element access under
these preconditions always succeeds. -/
lemma getElem?_ne_none_of_all_length_eq {α : Type} {M : List (List α)} {n i j : Nat}
    (h_len : ∀ row, row ∈ M → row.length = n) (hi : i < M.length) (hj : j < n) :
    getElem? M i j ≠ none := by
  intro h_eq
  have h_row : M[i]? = some (M.get ⟨i, hi⟩) := List.getElem?_eq_getElem hi
  have h_row_len : (M.get ⟨i, hi⟩).length = n := h_len (M.get ⟨i, hi⟩) (List.getElem_mem hi)
  have hj' : j < (M.get ⟨i, hi⟩).length := by rwa [h_row_len]
  unfold getElem? at h_eq
  rw [h_row] at h_eq
  -- h_eq: (some (M.get ...) >>= fun row => row[j]?) = none
  have h_bind : (some (M.get ⟨i, hi⟩) >>= fun row => row[j]?) = (M.get ⟨i, hi⟩)[j]? := by simp
  rw [h_bind] at h_eq
  have h_get_eq : (M.get ⟨i, hi⟩)[j]? = some ((M.get ⟨i, hi⟩).get ⟨j, hj'⟩) :=
    List.getElem?_eq_getElem hj'
  rw [h_get_eq] at h_eq
  simp at h_eq

/-! ### Matrix transpose -/

/-- Transpose a matrix represented as `List (List α)`. The number of columns is determined
by the length of the first row; missing elements in shorter rows are filled with `0`.
Returns `[]` for an empty matrix. -/
def transposeList {α : Type _} [OfNat α 0] (matrix : List (List α)) : List (List α) :=
  match matrix with
  | [] => []
  | firstRow :: _ =>
    List.ofFn (fun (i : Fin firstRow.length) => matrix.map fun row => row.getD (i.val) 0)

/-- Accessing the transposed matrix at `(j,i)` equals accessing the original at `(i,j)`.
This lemma uses `getD` for safe out-of-bounds fallback and requires `Inhabited α`
to provide a `default` value.

The expression `(List.range n).map (getColumn matrix)` constructs the transpose
of `matrix` with `n` columns (the length of the first row). -/
lemma getD_transpose_getD_eq [Inhabited α] (matrix : List (List α)) (i j : Nat)
    (hi : i < matrix.length) (hj : j < (matrix.headD []).length) :
    (((List.range (matrix.headD []).length).map
      (fun k => matrix.map (fun row => row.getD k default))).getD j []).getD i default
    = (matrix.getD i []).getD j default := by
  set n := (matrix.headD []).length with hn
  have hjlen : j < ((List.range n).map (fun k => matrix.map (fun row => row.getD k default))).length := by
    simpa [hn] using hj
  rw [List.getD_eq_getElem _ _ hjlen]
  rw [List.getElem_map, List.getElem_range]
  have hilen : i < (matrix.map (fun row => row.getD j default)).length := by
    simpa using hi
  rw [List.getD_eq_getElem _ _ hilen]
  rw [List.getElem_map]
  congr 1
  rw [List.getD_eq_getElem _ _ hi]

/-! ### Column extraction -/

/-- Extract the `j`-th column of a matrix represented as `List (List α)`.
Rows that are too short (length ≤ `j`) contribute `default` as padding. -/
def getColumn {α : Type} [Inhabited α] (M : List (List α)) (j : Nat) : List α :=
  M.map (fun row => row.getD j default)

/-! ### Matrix rotation -/

/-- Rotate a matrix represented as `List (List α)` 90 degrees clockwise.
Reverses the rows then transposes: `rotate matrix = transpose (reverse matrix)`.

This works for rectangular matrices of any dimension and any element type.
For example, `[[a,b],[c,d]]` becomes `[[c,a],[d,b]]`. -/
def rotate {α : Type _} (matrix : List (List α)) : List (List α) :=
  List.transpose (matrix.reverse)

/-- Rotate a square matrix 90 degrees clockwise in-place (functional style: returns a new matrix).
Works for any element type. The input matrix is assumed to be square (n × n), where `n = matrix.size`.
Each row `matrix[i]` must also have size `n` for correct results.

The formula: `result[i][j] = old[n-1-j][i]`. -/
def rotate90 {α : Type} [Inhabited α] (matrix : Array (Array α)) : Array (Array α) :=
  Array.ofFn (λ (i : Fin matrix.size) =>
    Array.ofFn (λ (j : Fin matrix.size) =>
      ((matrix[matrix.size - 1 - j.val]!)[i.val]!)))

/-! ### Element-wise matrix combination -/

/-- Element-wise combination of two matrices (represented as `List (List α)` and
`List (List β)`) using a binary function `f : α → β → γ`. The result is a matrix
of type `List (List γ)` whose entries are `f A[i][j] B[i][j]`.

If the matrices have different dimensions, the result has the dimensions of the shorter
matrix (standard `zipWith` behavior on both the outer and inner levels).

```lean
example : Matrix.zipWith (· + ·) [[1,2],[3,4]] [[5,6],[7,8]] = [[6,8],[10,12]] := rfl
``` -/
def zipWith {α β γ : Type} (f : α → β → γ) (A : List (List α)) (B : List (List β)) : List (List γ) :=
  List.zipWith (List.zipWith f) A B

/-- Element-wise addition of two matrices over an `Add` type.
This is a specialization of `zipWith` with addition. -/
def matrixAdd {α : Type} [Add α] (A B : List (List α)) : List (List α) :=
  zipWith (· + ·) A B

/-- If all rows of `A` have length `L` and all rows of `B` have length `L`, then
all rows of `zipWith f A B` also have length `L`. This lemma uses `mem_zipWith_mp`
to decompose membership in the zipped result back to the original rows. -/
lemma zipWith_row_length_eq {α β γ : Type} (f : α → β → γ)
    (A : List (List α)) (B : List (List β)) (L : Nat)
    (hA : ∀ row ∈ A, row.length = L) (hB : ∀ row ∈ B, row.length = L) :
    ∀ row ∈ zipWith f A B, row.length = L := by
  induction A generalizing B with
  | nil => simp [zipWith]
  | cons a as ih =>
    cases B with
    | nil => simp [zipWith]
    | cons b bs =>
      intro row hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp [hA a (by simp), hB b (by simp)]
      · exact ih bs (fun r h => hA r (by simp [h])) (fun r h => hB r (by simp [h])) row hr

/-! ### Matrix multiplication modulo a modulus -/

/-- Matrix multiplication of `dim × dim` matrices modulo `modM`.
Uses `Array (Array Nat)` as the matrix representation, with `!`-indexing.
The result matrix `C = A × B` has entries
`C[i][j] = (Σₖ A[i][k] * B[k][j]) % modM`.

This is a general-purpose implementation for computing modular matrix
products, commonly used in competitive programming for linear recurrence
problems (e.g., exponentiation of transformation matrices). -/
def matMulOfDim (dim modM : Nat) (A B : Array (Array Nat)) : Array (Array Nat) :=
  ((List.range dim).map (fun i =>
      ((List.range dim).map (fun j =>
          (List.range dim).foldl (fun acc k =>
              let a := ((A[i]!)[k]!)
              let b := ((B[k]!)[j]!)
              (acc + (a * b) % modM) % modM
            ) 0
        )).toArray
    )).toArray

/-! ### Matrix multiplication over a semiring -/

/-- Compute the product of two `N × N` matrices over any semiring, represented as
`List (List α)`. The entry at position `(i, j)` of the result is the dot product of
row `i` of `m1` and column `j` of `m2`:

`C[i][j] = Σ_{k < N} A[i][k] * B[k][j]`

Missing rows are treated as `[]` and missing elements within a row are treated as `0`
(via `getD` defaults). -/
def mul {α : Type _} [Semiring α] (N : Nat) (m1 : List (List α)) (m2 : List (List α)) : List (List α) :=
  (List.range N).map (fun i =>
    (List.range N).map (fun j =>
      (List.range N).foldl (fun acc k => acc + ((m1.getD i []).getD k 0) * ((m2.getD k []).getD j 0)) 0))

end Matrix
