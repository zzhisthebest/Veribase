import general.Grid.Adjacency

namespace Grid

/-! ### Manhattan distance on `Nat × Nat` -/

/-- Manhattan distance between two points on the `Nat × Nat` grid. -/
def manhattan (p q : Nat × Nat) : Nat :=
  Nat.absDiff p.1 q.1 + Nat.absDiff p.2 q.2

theorem manhattan_self (p : Nat × Nat) : manhattan p p = 0 := by
  simp [manhattan, Nat.absDiff]

theorem manhattan_nonneg (p q : Nat × Nat) : 0 ≤ manhattan p q := by
  unfold manhattan
  exact add_nonneg (Nat.zero_le _) (Nat.zero_le _)

/-- Manhattan distance from an unpacked source point `(x, y)` to a paired target point `p`.
Convenience form of `manhattan` where the first point is given as separate coordinates. -/
def manhattanTo (x y : Nat) (p : Nat × Nat) : Nat := manhattan (x, y) p

/-- Manhattan distance between two points given as four separate `Nat` coordinates.
`manhattanDistNat x₁ y₁ x₂ y₂ = |x₁ - x₂| + |y₁ - y₂|`.
Convenience form of `Grid.manhattan` for fully unpacked coordinates. -/
def manhattanDistNat (x₁ y₁ x₂ y₂ : Nat) : Nat :=
  Nat.absDiff x₁ x₂ + Nat.absDiff y₁ y₂

theorem manhattanDistNat_self (x y : Nat) : manhattanDistNat x y x y = 0 := by
  simp [manhattanDistNat, Nat.absDiff]

theorem manhattanDistNat_comm (x₁ y₁ x₂ y₂ : Nat) :
    manhattanDistNat x₁ y₁ x₂ y₂ = manhattanDistNat x₂ y₂ x₁ y₁ := by
  simp [manhattanDistNat, Nat.absDiff_comm, add_comm]

theorem manhattanDistNat_nonneg (x₁ y₁ x₂ y₂ : Nat) : 0 ≤ manhattanDistNat x₁ y₁ x₂ y₂ := by
  simp [manhattanDistNat]

theorem manhattanDistNat_eq_manhattan (x₁ y₁ x₂ y₂ : Nat) :
    manhattanDistNat x₁ y₁ x₂ y₂ = manhattan (x₁, y₁) (x₂, y₂) := by
  simp [manhattanDistNat, manhattan]

/-! ### Chebyshev distance on `Nat × Nat` -/

/-- Chebyshev distance (L∞ distance) between points `(a, c)` and `(b, d)` on the ℕ×ℕ grid,
using separate coordinates and `Nat.dist` for absolute difference. -/
def chebyshevDistNat (a b c d : Nat) : Nat := max (Nat.dist a b) (Nat.dist c d)

/-! ### Manhattan distance on `Int × Int` -/

/-- Manhattan distance (L1 distance) between two integer points.
`|x₁ - x₂| + |y₁ - y₂|`, computed via `Int.natAbs`. -/
def manhattanDist (p q : Int × Int) : Nat :=
  Int.natAbs (p.1 - q.1) + Int.natAbs (p.2 - q.2)

theorem manhattanDist_self (p : Int × Int) : manhattanDist p p = 0 := by
  simp [manhattanDist]

theorem manhattanDist_comm (p q : Int × Int) : manhattanDist p q = manhattanDist q p := by
  unfold manhattanDist
  have hx : Int.natAbs (p.1 - q.1) = Int.natAbs (q.1 - p.1) := by
    rw [show p.1 - q.1 = -(q.1 - p.1) by ring, Int.natAbs_neg]
  have hy : Int.natAbs (p.2 - q.2) = Int.natAbs (q.2 - p.2) := by
    rw [show p.2 - q.2 = -(q.2 - p.2) by ring, Int.natAbs_neg]
  rw [hx, hy]

/-! ### Chebyshev distance on `Int × Int` -/

/-- Chebyshev distance (chessboard / L∞ distance) between two integer points.
The minimum number of king moves to travel between two squares on a chessboard,
i.e., `max(|x₁ - x₂|, |y₁ - y₂|)`. -/
def chebyshevDist (p q : Int × Int) : Nat :=
  Nat.max (Int.natAbs (p.1 - q.1)) (Int.natAbs (p.2 - q.2))

theorem chebyshevDist_self (p : Int × Int) : chebyshevDist p p = 0 := by
  simp [chebyshevDist]

theorem chebyshevDist_comm (p q : Int × Int) : chebyshevDist p q = chebyshevDist q p := by
  unfold chebyshevDist
  have hx : Int.natAbs (p.1 - q.1) = Int.natAbs (q.1 - p.1) := by
    rw [show p.1 - q.1 = -(q.1 - p.1) by ring, Int.natAbs_neg]
  have hy : Int.natAbs (p.2 - q.2) = Int.natAbs (q.2 - p.2) := by
    rw [show p.2 - q.2 = -(q.2 - p.2) by ring, Int.natAbs_neg]
  rw [hx, hy]

/-- Total Chebyshev distance along consecutive pairs in a list of integer points.
This is `List.pathSum chebyshevDist` specialized to `Int × Int` points. -/
def totalDist : List (Int × Int) → Nat := List.pathSum chebyshevDist

/-! ### Squared Euclidean distance -/

/--
Squared Euclidean distance between two 2D points `(x1, y1)` and `(x2, y2)`.
Works over any `Ring α` (e.g., `Int`, `ℚ`, `ℝ`, `ℂ`).
-/
def sqDist {α : Type} [Ring α] (x1 y1 x2 y2 : α) : α :=
  (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)

/--
Squared Euclidean distance between two points in `α × α`, general over any `Ring α`.
This is the paired-argument form of `sqDist`:
`sqDistPair p q = sqDist p.1 p.2 q.1 q.2`.
-/
def sqDistPair {α : Type} [Ring α] (p q : α × α) : α :=
  let dx := p.1 - q.1
  let dy := p.2 - q.2
  dx * dx + dy * dy


theorem sqDistPair_eq_sqDist {α : Type} [Ring α] (p q : α × α) :
    sqDistPair p q = sqDist p.1 p.2 q.1 q.2 := rfl

/--
Squared Euclidean distance between two `Nat × Nat` points, using `Nat.absDiff` for
safe subtraction (since `Nat` is not a `Ring`). Equivalent to `(dx)² + (dy)²` where
`dx = |p.1 - q.1|` and `dy = |p.2 - q.2|`.
-/
def sqDistNat (p q : Nat × Nat) : Nat :=
  let dx := Nat.absDiff p.1 q.1
  let dy := Nat.absDiff p.2 q.2
  dx * dx + dy * dy

/-- `sqDistNat` is symmetric: `sqDistNat p q = sqDistNat q p`. -/
theorem sqDistNat_comm (p q : Nat × Nat) : sqDistNat p q = sqDistNat q p := by
  simp [sqDistNat, Nat.absDiff_comm p.1 q.1, Nat.absDiff_comm p.2 q.2]

/-- The distance from a point to itself is zero. -/
theorem sqDistNat_self (p : Nat × Nat) : sqDistNat p p = 0 := by
  simp [sqDistNat, Nat.absDiff]

end Grid
