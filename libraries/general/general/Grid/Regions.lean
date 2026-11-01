import general.Grid.Distances

namespace Grid

/-! ### Folding over a rectangular range -/

/-- Fold a binary function `f i j` over all `(i,j)` in the rectangle `0..m-1 × 0..n-1`.
The outer loop iterates `i` from `0` to `m-1`, and for each `i` the inner loop iterates
`j` from `0` to `n-1`, applying `f i j acc` at each cell. -/
def foldRange {α : Type} (m n : Nat) (f : Nat → Nat → α → α) (init : α) : α :=
  (List.range m).foldl (fun acc i =>
    (List.range n).foldl (fun acc' j => f i j acc') acc) init

/-- Folding over a 0-height rectangle is a no-op. -/

lemma foldRange_zero_n {α : Type} (n : Nat) (f : Nat → Nat → α → α) (init : α) :
    foldRange 0 n f init = init := by
  simp [foldRange]

/-- Folding over a 0-width rectangle is a no-op. -/

lemma foldRange_m_zero {α : Type} (m : Nat) (f : Nat → Nat → α → α) (init : α) :
    foldRange m 0 f init = init := by
  simp [foldRange]

/-- Folding over a 1×1 rectangle applies `f 0 0` to the initial accumulator. -/
lemma foldRange_one_one {α : Type} (f : Nat → Nat → α → α) (init : α) :
    foldRange 1 1 f init = f 0 0 init := by
  simp [foldRange, List.range_succ]

/-! ### Submatrix prefix sum from top-left -/

/-- Sum of all elements in the submatrix from `(0, 0)` to `(i, j)` (inclusive)
of a grid represented as `List (List α)`. Uses `getCellD` with zero as a default
for safe out-of-bounds access; cells outside the grid contribute `0` to the sum. -/
def submatrixTopLeftSum {α : Type} [AddCommMonoid α] (grid : List (List α)) (i j : Nat) : α :=
  foldRange (i + 1) (j + 1) (fun p q acc => acc + getCellD (0 : α) grid p q) 0

/-! ### Matrix sum -/

/-- Sum all cells of an `m × n` matrix, given a cell-value function `f r c`.
Defined as a `@[reducible]` shorthand for `foldRange m n (fun r c acc => acc + f r c) 0`. -/
@[reducible]
def matrixSum (m n : Nat) (f : Nat → Nat → Nat) : Nat :=
  foldRange m n (fun r c acc => acc + f r c) 0

/-! ### Rectangle area -/

/-- Area of an axis-aligned rectangle given by bottom-left `(x1, y1)` and top-right
`(x2, y2)`. Works over any `Ring α`. -/
@[reducible]
def rectArea {α : Type} [Ring α] (x1 y1 x2 y2 : α) : α :=
  (x2 - x1) * (y2 - y1)

/-- Length of the overlap of two 1D intervals `[a1, a2]` and `[b1, b2]`.
Returns zero when the intervals do not overlap. -/
def segmentOverlap {α : Type} [LinearOrderedAddCommGroup α] (a1 a2 b1 b2 : α) : α :=
  max 0 (min a2 b2 - max a1 b1)

/-- The overlap length of two intervals is always nonnegative. -/
theorem segmentOverlap_nonneg {α : Type} [LinearOrderedAddCommGroup α] (a1 a2 b1 b2 : α) :
    0 ≤ segmentOverlap a1 a2 b1 b2 := by
  unfold segmentOverlap
  exact le_max_left _ _

/-- `segmentOverlap` is symmetric: swapping the two intervals gives the same result. -/
theorem segmentOverlap_symm {α : Type} [LinearOrderedAddCommGroup α] (a1 a2 b1 b2 : α) :
    segmentOverlap a1 a2 b1 b2 = segmentOverlap b1 b2 a1 a2 := by
  unfold segmentOverlap
  simp [min_comm, max_comm]

/-- When the rectangle is valid (`x1 ≤ x2` and `y1 ≤ y2`), its area is nonnegative. -/
theorem rectArea_nonneg {α : Type} [LinearOrderedRing α] (x1 y1 x2 y2 : α) (hx : x1 ≤ x2)
    (hy : y1 ≤ y2) : 0 ≤ rectArea x1 y1 x2 y2 := by
  unfold rectArea
  have hx' : 0 ≤ x2 - x1 := sub_nonneg.mpr hx
  have hy' : 0 ≤ y2 - y1 := sub_nonneg.mpr hy
  exact mul_nonneg hx' hy'

/-- Total area of the union of two axis-aligned rectangles, given by bottom-left corners
`(ax1, ay1)`, `(bx1, by1)` and top-right corners `(ax2, ay2)`, `(bx2, by2)`.
The union area is `area(A) + area(B) - area(A ∩ B)`.
Works over any `LinearOrderedRing α` (e.g., `ℤ`, `ℚ`, `ℝ`). -/
def totalAreaTwoRects {α : Type} [LinearOrderedRing α]
    (ax1 ay1 ax2 ay2 bx1 by1 bx2 by2 : α) : α :=
  rectArea ax1 ay1 ax2 ay2 + rectArea bx1 by1 bx2 by2 -
    segmentOverlap ax1 ax2 bx1 bx2 * segmentOverlap ay1 ay2 by1 by2

end Grid

