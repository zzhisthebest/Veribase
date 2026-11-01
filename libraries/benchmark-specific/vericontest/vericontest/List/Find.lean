import Mathlib

open List

namespace List

/-! ### `findNextIndex` — next index satisfying a predicate

`findNextIndex p xs start` finds the smallest index `i ≥ start` such that `p xs[i]`
holds. If no such index exists within the bounds of `xs`, it returns the smallest
out-of-bounds index `≥ start` (i.e., the first index `≥ start` with `¬ (i < xs.length)`).

This generalizes `find_next_nonzero` (from LeetCode 2511) — which searches for the next
non-zero `Int` in a list — to an arbitrary decidable predicate on any type.

The three main theorems characterize the behavior:
* `findNextIndex_ge_start`: the result is always ≥ `start`
* `findNextIndex_eq_self_of_satisfies`: stops immediately if `p` holds at `start`
* `findNextIndex_succ_of_not_satisfies`: recurses if `p` does not hold at `start` -/

/-- Find the smallest index `i ≥ start` such that `p xs[i]` holds.
If no such index exists in bounds, returns the smallest out-of-bounds index `≥ start`. -/
def findNextIndex {α : Type} (p : α → Prop) [∀ a, Decidable (p a)] (xs : List α) (start : Nat) : Nat :=
  if h : start < xs.length then
    if h' : p xs[start] then
      start
    else
      findNextIndex p xs (start + 1)
  else
    start
termination_by xs.length - start
decreasing_by
  exact Nat.sub_lt_sub_left h (Nat.lt_succ_self start)

/-- `findNextIndex` never returns an index smaller than `start`. -/
theorem findNextIndex_ge_start {α : Type} (p : α → Prop) [∀ a, Decidable (p a)] (xs : List α) (start : Nat) :
    start ≤ findNextIndex p xs start := by
  apply WellFounded.induction ((measure (fun start => xs.length - start)).wf) start
  intro start IH
  unfold findNextIndex
  split <;> rename_i h
  · split <;> rename_i h'
    · exact Nat.le_refl start
    · have hge := IH (start + 1) (Nat.sub_lt_sub_left h (Nat.lt_succ_self start))
      omega
  · exact Nat.le_refl start

/-- If `start` is in bounds and `p xs[start]` holds, `findNextIndex` returns `start`. -/
theorem findNextIndex_eq_self_of_satisfies {α : Type} (p : α → Prop) [∀ a, Decidable (p a)] (xs : List α) (start : Nat)
    (h_bound : start < xs.length) (h_sat : p xs[start]) : findNextIndex p xs start = start := by
  rw [findNextIndex]
  simp [h_bound, h_sat]

/-- If `start` is in bounds and `p xs[start]` does NOT hold,
`findNextIndex` recurses on `start + 1`. -/
theorem findNextIndex_succ_of_not_satisfies {α : Type} (p : α → Prop) [∀ a, Decidable (p a)] (xs : List α) (start : Nat)
    (h_bound : start < xs.length) (h_not : ¬ p xs[start]) : findNextIndex p xs start = findNextIndex p xs (start + 1) := by
  rw [findNextIndex]
  simp [h_bound, h_not]

/-! ### `firstIdxWhere` — first index where a Bool predicate holds

`firstIdxWhere p xs` wraps `List.findIdx? p xs` by extracting the index from
`some i`, or returning `0` if `findIdx?` returns `none`. This provides a total
`Nat`-valued result (no `Option`), convenient for arithmetic contexts where
the default `0` is harmless (e.g., the caller has a proof that a matching element
exists, or `0`-injection does not affect the computation).

For the `DecidableEq`-based element search version, see `findIdxOf`. -/

/-- Returns the first index `i` where `p xs[i]` holds, or `0` if no element satisfies `p`.
Wraps `List.findIdx?` by unwrapping `some i` or defaulting to `0`. -/
def firstIdxWhere (p : α → Bool) (xs : List α) : Nat :=
  match List.findIdx? p xs with
  | some i => i
  | none => 0

/-- If the predicate `p` holds at index `i`, then `List.findIdx? p xs` returns
`some (firstIdxWhere p xs)`. This connects the `Option`-based API to the total `Nat` API:
when a match exists, `firstIdxWhere` extracts exactly the index `findIdx?` returns. -/
theorem firstIdxWhere_findIdx (p : α → Bool) (xs : List α) (i : Fin xs.length)
    (hi : p (xs[i]) = true) : List.findIdx? p xs = some (firstIdxWhere p xs) := by
  unfold firstIdxWhere
  cases hf : List.findIdx? p xs with
  | none =>
    have hnone := (List.findIdx?_eq_none_iff (p := p) (xs := xs)).mp hf
    have hmem : xs[i] ∈ xs := List.get_mem _ _
    have hfalse := hnone (xs[i]) hmem
    rw [hi] at hfalse
    simp at hfalse
  | some j =>
    simp

/-! ### `lastIdxWhere` — last index where a Bool predicate holds

`lastIdxWhere p xs` finds the last index satisfying predicate `p` by searching
`xs.reverse`. Returns `0` if no element satisfies `p`.

The formula: `lastIdxWhere p xs = xs.length - 1 - (findIdx? p xs.reverse)`,
with `0` when `findIdx?` returns `none`. -/

/-- Returns the last index `i` where `p xs[i]` holds, or `0` if no element satisfies `p`.
Searches via `List.findIdx?` on `xs.reverse` and converts the result from the reversed
index space to the forward index space. -/
def lastIdxWhere (p : α → Bool) (xs : List α) : Nat :=
  let n := xs.length
  match List.findIdx? p xs.reverse with
  | some i => n - 1 - i
  | none => 0

end List
