import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Mapping over a natural number range -/

/-- Map a function `f` over `[0, ..., count-1]`, producing a list of length `count`.
This is equivalent to `(range count).map f`. -/
def rangeMap {α : Type u} (count : Nat) (f : Nat → α) : List α :=
  (range count).map f

@[simp]
theorem rangeMap_length {α : Type u} (count : Nat) (f : Nat → α) :
    (rangeMap count f).length = count := by
  simp [rangeMap]

/-! ## Range from a starting offset -/

/-- Produces the list `[start, start+1, ..., start+count-1]`. -/
def rangeFrom (start : Nat) (count : Nat) : List Nat :=
  rangeMap count (fun i => start + i)

@[simp] theorem rangeFrom_length (start count : Nat) : (rangeFrom start count).length = count := by
  simp [rangeFrom]

/-! ## Range from an integer offset -/

/-- Produces the list `[start, start+1, ..., start+count-1]` for an integer `start`. -/
def rangeFromInt (start : Int) (count : Nat) : List Int :=
  (range count).map (fun n => start + Int.ofNat n)

@[simp] theorem rangeFromInt_length (start : Int) (count : Nat) : (rangeFromInt start count).length = count := by
  simp [rangeFromInt]

/-! ## Interleaved pair mapping over a range -/

/-- Given `f g : Nat → α` and a count `k`, produces
`[f 0, g 0, f 1, g 1, …, f (k-1), g (k-1)]`.
That is, it maps both `f` and `g` over the range `[0, …, k-1]` and interleaves
the results by appending each pair `[f i, g i]` in order. -/
def rangePairMap {α : Type u} (f g : Nat → α) : Nat → List α
  | 0 => []
  | k + 1 => rangePairMap f g k ++ [f k, g k]

@[simp]
theorem rangePairMap_length {α : Type u} (f g : Nat → α) (k : Nat) :
    (rangePairMap f g k).length = 2 * k := by
  induction k with
  | zero => simp [rangePairMap]
  | succ k ih => simp [rangePairMap, ih, Nat.mul_succ]

/-! ## One-based range

`rangeOneTo n` produces the list `[1, 2, ..., n]`. This is a common shorthand
for 1-indexed ranges, equivalent to `rangeFrom 1 n`. -/

/-- The list `[1, 2, ..., n]`. Returns `[]` when `n = 0`. -/
def rangeOneTo (n : Nat) : List Nat :=
  rangeFrom 1 n

@[simp] theorem rangeOneTo_length (n : Nat) : (rangeOneTo n).length = n := by
  simp [rangeOneTo]

/-! ## Sum over `[1, …, n]` -/

/-- Sum of `f i` for `i` from `1` to `n` inclusive:
`sumOneToN f n = f 1 + f 2 + … + f n`.
Computed via `foldl` over `List.range n` for efficiency (avoids building an
intermediate list of mapped values). -/
def sumOneToN (f : Nat → Nat) (n : Nat) : Nat :=
  (range n).foldl (fun acc i => acc + f (i + 1)) 0

@[simp] theorem sumOneToN_zero (f : Nat → Nat) : sumOneToN f 0 = 0 := rfl

theorem sumOneToN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i, f i = g i) :
    sumOneToN f n = sumOneToN g n := by
  simp [sumOneToN, h]

/-! ## Sum over `[0, …, limit-1]` -/

/-- Sum of `f i` for `i` from `0` to `limit-1` inclusive:
`sumNatRange limit f = f 0 + f 1 + … + f (limit-1)`.
Computed via `foldl` over `List.range limit` for efficiency. -/
def sumNatRange (limit : Nat) (f : Nat → Nat) : Nat :=
  (range limit).foldl (fun total index => total + f index) 0

@[simp] theorem sumNatRange_zero (f : Nat → Nat) : sumNatRange 0 f = 0 := rfl

/-! ## Mapping over 1-indexed range -/

/-- Maps `f` over `[1, 2, ..., n]`.
`rangeMap1 n f = [f 1, f 2, ..., f n]`.
Equivalent to `(rangeOneTo n).map f`. -/
def rangeMap1 {α : Type u} (n : Nat) (f : Nat → α) : List α :=
  (range n).map (fun i => f (i + 1))

/-! ## Arithmetic sequence with swapped adjacent pairs -/

/-- For an arithmetic progression `a_i = start + step * i`, produces the list
`[a_0 + 1, a_0, a_1 + 1, a_1, …, a_{count-1} + 1, a_{count-1}]`.
In each consecutive pair, the larger element comes first.

Example: `arithSeqSwappedPairs 1 2 3 = [2, 1, 4, 3, 6, 5]`. -/
def arithSeqSwappedPairs (start step count : Nat) : List Nat :=
  rangePairMap (fun i => start + step * i + 1) (fun i => start + step * i) count

end List

end Specific
