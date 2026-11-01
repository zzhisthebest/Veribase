import Mathlib

open List

/-! ### Prefix minimum and second-smallest scanning

This module provides operations for computing prefix minima and finding the
smallest element strictly greater than a given threshold in a list. The core
operation `chooseSmallestGt` selects the smaller of a new candidate and a
previous best, both strictly exceeding a given minimum. `scanSmallestAbove`
then scans a list from left to right using this operation.

`IsSmallestAbove` is the specification property: `v` is the smallest element
in the first `n` positions that exceeds `m`.

This pattern appears in problems like CF 22A ("Second Order Statistics"),
where the goal is to find the second smallest distinct value in a sequence.
-/

namespace List

/-! ### `chooseSmallestGt` — selecting the smallest value above a threshold -/

/-- Given a minimum value `min_val`, a candidate `cur`, and a previous best `prev`,
  returns the smaller of `cur` and the value in `prev` that is strictly greater than `min_val`.
  If `cur ≤ min_val`, returns `prev` unchanged. -/
def chooseSmallestGt {α : Type} [LinearOrder α] [Inhabited α] (min_val cur : α) (prev : Option α) : Option α :=
  if cur > min_val then
    match prev with
    | none => some cur
    | some v => if cur < v then some cur else some v
  else prev

/-! ### `scanSmallestAbove` — scanning for the smallest element above a threshold -/

/-- Scans the first `k` elements of `a` and returns the smallest element strictly greater
  than `min_val`, or `none` if no such element exists. -/
def scanSmallestAbove {α : Type} [LinearOrder α] [Inhabited α] (a : List α) (min_val : α) : Nat → Option α
  | 0 => none
  | i+1 => chooseSmallestGt min_val (a[i]!) (scanSmallestAbove a min_val i)

@[simp]
lemma scanSmallestAbove_zero {α : Type} [LinearOrder α] [Inhabited α] (a : List α) (m : α) :
    scanSmallestAbove a m 0 = none := rfl

/-- The successor case of `scanSmallestAbove`: processing the next element uses
  `chooseSmallestGt` to decide whether the current element at index `k` is a better
  candidate for the smallest-above value so far. -/
lemma scanSmallestAbove_succ {α : Type} [LinearOrder α] [Inhabited α]
    (a : List α) (m : α) (k : Nat) :
    scanSmallestAbove a m (k+1) = chooseSmallestGt m (a[k]!) (scanSmallestAbove a m k) := rfl

/-! ### `minPrefix` — prefix minimum via indexed access -/

/-- The minimum of the first `k+1` elements of `xs` (indices `0` through `k`).
  `minPrefix xs 0 = xs[0]!`, and for `k > 0`,
  `minPrefix xs (k+1) = min (minPrefix xs k) (xs[k+1]!)`.

  This is the index-based counterpart to `foldlMin`; it works on prefixes rather than
  entire lists. Requires `Inhabited α` for the `!` out-of-bounds sentinel. -/
def minPrefix {α : Type _} [LinearOrder α] [Inhabited α] (xs : List α) : Nat → α
  | 0 => xs[0]!
  | n+1 => min (minPrefix xs n) (xs[n+1]!)

/-! ### `maxPrefix` — prefix maximum via indexed access -/

/-- The maximum of a prefix of `a` up to index `n`. Specifically:
  `maxPrefix a n` computes the maximum of `a[0]!` through `a[n-1]!` (for `n ≥ 1`),
  and `a[0]!` for `n = 0`.

  Requires `Inhabited α` for the `!` out-of-bounds sentinel. -/
def maxPrefix {α : Type _} [LinearOrder α] [Inhabited α] (a : List α) : Nat → α
  | 0 => a[0]!
  | 1 => a[0]!
  | k + 2 =>
    let m := maxPrefix a (k + 1)
    let cur := a[k + 1]!
    if cur > m then cur else m

/-- `maxPrefix` is uniquely determined by its recurrence: any function `f` satisfying
  the same base cases (`f 0 = f 1 = a[0]!`) and step relation
  (`f (k+2) = max (a[k+1]!) (f (k+1))`) equals `maxPrefix a` for all `n`. -/
lemma maxPrefix_eq_of_recurrence {α : Type _} [LinearOrder α] [Inhabited α]
    (a : List α) (f : Nat → α)
    (h_zero : f 0 = a[0]!)
    (h_one : f 1 = a[0]!)
    (h_step : ∀ k, f (k + 2) =
      if a[k + 1]! > f (k + 1) then a[k + 1]! else f (k + 1)) (n : Nat) :
    maxPrefix a n = f n := by
  induction n with
  | zero => exact h_zero.symm
  | succ n ih =>
    cases n with
    | zero => exact h_one.symm
    | succ n =>
      simp only [maxPrefix]
      rw [ih, h_step]

/-! ### `maxPrefixGetD` — `getD`-based prefix maximum

`maxPrefixGetD nums n` computes `max(nums[0]?.getD 0, …, nums[n-1]?.getD 0)`.
The base case `n = 0` returns `(nums[0]?).getD 0`, collapsing the empty and
singleton cases. This is the `getD`-based counterpart to `maxPrefix` (which uses
`!` and `Inhabited`), and differs from `prefixMax_specificDuplicate` in the main `List.lean`
(which returns `0` for `n = 0`). Useful when negative values are possible and
`0` is not a safe sentinel.

This pattern appears in problems like LeetCode 2640 ("Find the Score of All
Prefixes of an Array"), where the running maximum of a prefix is needed with
safe indexing. -/

/-- Prefix maximum via `getD 0`. `maxPrefixGetD nums n` returns the maximum of
`nums[0]?.getD 0` through `nums[n-1]?.getD 0`, collapsing `n=0` and `n=1`
to both return `(nums[0]?).getD 0`. Requires `LinearOrder` and `Zero`. -/
def maxPrefixGetD {α : Type} [LinearOrder α] [Zero α] (nums : List α) : Nat → α
  | 0 => (nums[0]?).getD 0
  | n+1 => max (maxPrefixGetD nums n) ((nums[n]?).getD 0)

@[simp]
lemma maxPrefixGetD_zero {α : Type} [LinearOrder α] [Zero α] (nums : List α) :
    maxPrefixGetD nums 0 = (nums[0]?).getD 0 := rfl

@[simp]
lemma maxPrefixGetD_succ {α : Type} [LinearOrder α] [Zero α] (nums : List α) (n : ℕ) :
    maxPrefixGetD nums (n + 1) = max (maxPrefixGetD nums n) ((nums[n]?).getD 0) := rfl

/-! ### `minPrefixGetD` — `getD`-based prefix minimum

`minPrefixGetD nums n` computes `min(nums[0]?.getD 0, …, nums[n-1]?.getD 0)`.
The base case `n = 0` returns `(nums[0]?).getD 0`, collapsing the empty and
singleton cases. This is the `getD`-based counterpart to `minPrefix` (which uses
`!` and `Inhabited`), and the `min`-analogue of `maxPrefixGetD`. Useful when
negative values are possible and `0` is not a safe sentinel.

This pattern appears in problems like LeetCode 3502 ("Minimum Cost to Reach Every
Position"), where the running minimum of a prefix is needed with safe indexing. -/

/-- Prefix minimum via `getD 0`. `minPrefixGetD nums n` returns the minimum of
`nums[0]?.getD 0` through `nums[n-1]?.getD 0`, collapsing `n=0` and `n=1`
to both return `(nums[0]?).getD 0`. Requires `LinearOrder` and `Zero`. -/
def minPrefixGetD {α : Type} [LinearOrder α] [Zero α] (nums : List α) : Nat → α
  | 0 => (nums[0]?).getD 0
  | n+1 => min (minPrefixGetD nums n) ((nums[n]?).getD 0)

@[simp]
lemma minPrefixGetD_zero {α : Type} [LinearOrder α] [Zero α] (nums : List α) :
    minPrefixGetD nums 0 = (nums[0]?).getD 0 := rfl

@[simp]
lemma minPrefixGetD_succ {α : Type} [LinearOrder α] [Zero α] (nums : List α) (n : ℕ) :
    minPrefixGetD nums (n + 1) = min (minPrefixGetD nums n) ((nums[n]?).getD 0) := rfl

/-- Collapsing the first two elements of a list via `min` commutes with
`minPrefixGetD` (shifted by one). This follows from associativity of `min`:
`minPrefixGetD (x :: y :: zs) (n+2) = min x (min y (minPrefixGetD zs n))`
and `minPrefixGetD ((min x y) :: zs) (n+1) = min (min x y) (minPrefixGetD zs n)`,
which are equal since `min (min x y) z = min x (min y z)`. -/
lemma minPrefixGetD_min_cons {α : Type} [LinearOrder α] [Zero α]
    (x y : α) (zs : List α) (n : Nat) :
    minPrefixGetD ((min x y) :: zs) (n + 1) = minPrefixGetD (x :: y :: zs) (n + 2) := by
  induction' n with k ih
  · simp [minPrefixGetD, min_comm]
  · have hk1 : k.succ + 1 = k + 2 := by omega
    have hk2 : k.succ + 2 = k + 3 := by omega
    rw [hk1, hk2]
    rw [minPrefixGetD_succ (n := k + 1), minPrefixGetD_succ (n := k + 2)]
    have hget : (((min x y) :: zs)[k + 1]?).getD 0 = ((x :: y :: zs)[k + 2]?).getD 0 := by simp
    rw [ih, hget]

/-! ### `minPrefixSentinel` — prefix minimum with a sentinel for the empty prefix

`minPrefixSentinel s sentinel oobVal n` computes `min(sentinel, (s[0]?).getD oobVal, …, (s[n-1]?).getD oobVal)`.
Unlike `minPrefixGetD` (which returns `(s[0]?).getD 0` for `n = 0`), this function returns
`sentinel` for the empty prefix, making it suitable when `0` or another neutral value is
desired as the base case.

Uses a three-case recursion (`0`, `1`, `n+2`) to correctly handle the initial step without
double-counting the first element.

This pattern appears in problems like LeetCode 453 ("Minimum Moves to Equal Array
Elements"), where the minimum of all array elements is needed with safe `getD` access
and a zero sentinel for the empty prefix. -/

/-- Prefix minimum with a configurable sentinel value for the empty prefix (`n = 0`).
`minPrefixSentinel s sentinel oobVal n` returns the minimum of `sentinel` and
`(s[0]?).getD oobVal, …, (s[n-1]?).getD oobVal`. For `n = 1`, returns `(s[0]?).getD oobVal`
directly (not `min sentinel …`), matching the convention that the 1-element prefix is
the first element itself. -/
def minPrefixSentinel [LinearOrder α] (s : List α) (sentinel oobVal : α) : Nat → α
  | 0 => sentinel
  | 1 => (s[0]?).getD oobVal
  | n+2 => min (minPrefixSentinel s sentinel oobVal (n+1)) ((s[n+1]?).getD oobVal)

@[simp]
lemma minPrefixSentinel_zero [LinearOrder α] (s : List α) (sentinel oobVal : α) :
    minPrefixSentinel s sentinel oobVal 0 = sentinel := rfl

@[simp]
lemma minPrefixSentinel_one [LinearOrder α] (s : List α) (sentinel oobVal : α) :
    minPrefixSentinel s sentinel oobVal 1 = (s[0]?).getD oobVal := rfl

lemma minPrefixSentinel_succ_succ [LinearOrder α] (s : List α) (sentinel oobVal : α) (n : Nat) :
    minPrefixSentinel s sentinel oobVal (n+2) =
    min (minPrefixSentinel s sentinel oobVal (n+1)) ((s[n+1]?).getD oobVal) := rfl

/-! ### `IsSmallestAbove` — specification for the smallest-above property -/

/-- `IsSmallestAbove xs n m v` asserts that `v` is the smallest value in the first `n`
  positions of `xs` that is strictly greater than `m`. Formally:

  1. There exists an index `i < n` with `xs[i]! = v` and `v > m` (existence), and
  2. For every index `j < n`, either `xs[j]! ≤ m` or `xs[j]! ≥ v` (minimality). -/
def IsSmallestAbove {α : Type _} [LinearOrder α] [Inhabited α] (xs : List α) (n : Nat) (m v : α) : Prop :=
  (∃ i : Nat, i < n ∧ xs[i]! = v ∧ v > m) ∧
  (∀ j : Nat, j < n → xs[j]! ≤ m ∨ xs[j]! ≥ v)

end List
