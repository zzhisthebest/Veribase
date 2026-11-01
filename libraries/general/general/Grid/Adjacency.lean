import general.Grid.Transformations

namespace Grid

/-! ### Orthogonal neighbors -/

/-- Four-directional neighbors of position `(i, j)` within an `m × n` grid.
The four directions are up `(i-1, j)`, down `(i+1, j)`, left `(i, j-1)`, right `(i, j+1)`.
Only positions within bounds (`0 ≤ i' < m`, `0 ≤ j' < n`) are included.
This is the pure index version – see `neighborsWhere` for value‑filtered neighbors. -/
def neighbors (m n i j : Nat) : List (Nat × Nat) :=
  let up    := if i = 0       then [] else [(i - 1, j)]
  let down  := if i + 1 < m   then [(i + 1, j)] else []
  let left  := if j = 0       then [] else [(i, j - 1)]
  let right := if j + 1 < n   then [(i, j + 1)] else []
  up ++ down ++ left ++ right

/-- Four-directional neighbors of position `(i, j)` within an `m × n` grid,
    filtered to only include cells whose value in `grid` matches `pred`.
    The four directions are up `(i-1, j)`, down `(i+1, j)`, left `(i, j-1)`, right `(i, j+1)`. -/
def neighborsWhere {α : Type u} (grid : List (List α)) (pred : α → Bool) (i j m n : Nat) :
    List (Nat × Nat) :=
  (neighbors m n i j).filter (fun p =>
    match cell grid p.1 p.2 with
    | some x => pred x
    | none   => false)

/-! ### Direction vectors -/

/-- The eight cardinal and diagonal directions as `(dx, dy)` displacements.
Useful for grid traversal problems (chess king moves, flood fill, etc.). -/
def directions8 : List (Int × Int) :=
  [(1, 0), (-1, 0), (0, 1), (0, -1),
   (1, 1), (-1, -1), (1, -1), (-1, 1)]

/-! ### Bounds checking -/

/-- Check whether integer coordinates `(r, c)` are inside a `rows × cols` grid
anchored at `(0, 0)`. Returns `true` iff `0 ≤ r < rows` and `0 ≤ c < cols`. -/
def inBounds (rows cols : Int) (r c : Int) : Bool :=
  (0 : Int) ≤ r && r < rows && (0 : Int) ≤ c && c < cols

/-! ### Grid adjacency -/

/-- Two positions `(i₁, j₁)` and `(i₂, j₂)` are orthogonal-adjacent if they share an edge
in a 2D grid, i.e., they differ by exactly 1 in one coordinate and are equal in the other.
This is the 4-connected (von Neumann) neighborhood relation. -/
def Adjacent (i₁ j₁ i₂ j₂ : Nat) : Prop :=
  (i₁ = i₂ ∧ (j₁ = j₂ + 1 ∨ j₂ = j₁ + 1)) ∨
  (j₁ = j₂ ∧ (i₁ = i₂ + 1 ∨ i₂ = i₁ + 1))

/-- Convenience form of `Grid.Adjacent` for `Nat × Nat` pairs.
`adjacent p q` is the 4-connected (von Neumann) adjacency, i.e., `p` and `q` differ by
exactly 1 in one coordinate and are equal in the other. -/
abbrev adjacent (p q : Nat × Nat) : Prop :=
  Adjacent p.1 p.2 q.1 q.2

/-- Replace cells in a 2D grid where `pred i j` returns true with `replace`.
Uses `List.mapIdx` internally for indexed traversal. -/
def mapCells {α : Type} (pred : Nat → Nat → Bool) (replace : α) (grid : List (List α)) : List (List α) :=
  grid.mapIdx (fun i row =>
    row.mapIdx (fun j cell =>
      if pred i j then replace else cell))

theorem length_mapCells {α : Type} (pred : Nat → Nat → Bool) (replace : α) (grid : List (List α)) :
    (mapCells pred replace grid).length = grid.length := by
  unfold mapCells
  simp [List.length_mapIdx]

private lemma getElem_mapIdx {α β : Type} [Inhabited α] [Inhabited β] (l : List α) (f : Nat → α → β) (i : Nat) (hi : i < l.length) :
    (l.mapIdx f)[i]! = f i l[i]! := by
  induction' l with x xs ih generalizing i f
  · simp at hi
  · cases i
    · simp
    · rename_i i
      have hi' : i < xs.length := by
        simpa using hi
      have h := ih (fun j => f (j+1)) i hi'
      simp at h ⊢
      exact h

theorem length_mapCells_row {α : Type} [Inhabited α] (pred : Nat → Nat → Bool) (replace : α) (grid : List (List α))
    (i : Nat) (hi : i < grid.length) :
    (mapCells pred replace grid)[i]!.length = (grid[i]!).length := by
  have h := getElem_mapIdx grid (fun i row => row.mapIdx (fun j cell => if pred i j then replace else cell)) i hi
  unfold mapCells
  have h' : (grid.mapIdx (fun i row => row.mapIdx (fun j cell => if pred i j then replace else cell)))[i]!
          = (grid[i]!).mapIdx (fun j cell => if pred i j then replace else cell) := by
    simpa using h
  simp [h', List.length_mapIdx]

/-- In a non-empty grid, the head row's length computed via `head?.map List.length` equals the length of the
first row accessed directly. Useful for relating precondition `n` computations to actual row lengths. -/
lemma head_length_eq_first_row_len (grid : List (List α)) (h_nonempty : 0 < grid.length) :
    (grid.head?.map List.length).getD 0 = (grid[0]!).length := by
  cases grid
  · simp at h_nonempty
  · simp

end Grid
