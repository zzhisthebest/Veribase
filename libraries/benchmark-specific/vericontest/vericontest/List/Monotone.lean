import Mathlib

open List

/-!
# Longest monotonic contiguous subarray

`longestMonotonicRunLen` computes the length of the longest contiguous subarray that is
either strictly increasing or strictly decreasing. It uses a single-pass linear-time algorithm
that tracks both the increasing and decreasing run lengths ending at the current element.

This is the core algorithm from LeetCode 3105 ("Longest Strictly Increasing or Strictly
Decreasing Subarray"), generalized to any `LinearOrder` type.
-/

namespace List

/-! ### Definitions -/

/-! ## Strictly increasing segments

A predicate `isStrictlyIncreasingBounded s start len` asserts that the contiguous
subsegment of `s` of length `len` beginning at index `start` is strictly increasing.
The "bounded" qualifier refers to the use of `Fin`-indexed quantification, which
is decidable for finite lists (unlike unbounded `∀ j : Nat` quantification).

`adjacentPairAtBounded s a k` further requires that two adjacent segments of length `k`
(starting at `a` and `a+k`) are both strictly increasing. This pattern appears in
problems that look for two adjacent "nice" subarrays. -/

/-- `isStrictlyIncreasingBounded nums start len` holds when the subsegment of `nums`
from index `start` of length `len` is strictly increasing: each element is strictly
less than the next within the segment.

Uses `Fin`-indexed quantification (hence "bounded") for decidable predicates.
For `Nat`-indexed quantification, see the dual `isStrictlyIncreasingUnbounded` variant
(not currently in general). -/
def isStrictlyIncreasingBounded {α : Type} [LT α] [Inhabited α]
    (nums : List α) (start len : Nat) : Prop :=
  1 ≤ len ∧ start + len ≤ nums.length ∧
  ∀ (j : Fin (start + len)), start ≤ j.val → j.val + 1 < start + len →
    nums[j.val]! < nums[j.val + 1]!

/-- `adjacentPairAtBounded nums a k` holds when the two adjacent subsegments
`nums[a .. a+k)` and `nums[a+k .. a+2*k)` are both strictly increasing. -/
def adjacentPairAtBounded {α : Type} [LT α] [Inhabited α]
    (nums : List α) (a k : Nat) : Prop :=
  1 ≤ k ∧ a + 2 * k ≤ nums.length ∧
  isStrictlyIncreasingBounded nums a k ∧
  isStrictlyIncreasingBounded nums (a + k) k

/-! ### Run-length computations -/

/-- Auxiliary fold that computes the length of the longest monotonic (strictly increasing
or strictly decreasing) contiguous subarray.

At each step:
- `ni` is the length of the strictly increasing run ending at the current element
- `nd` is the length of the strictly decreasing run ending at the current element
- `best` is the maximum run length seen so far
- `prev` is the previous element value (used for comparison)

When the current element `x` is greater than `prev`, the increasing run extends (`ni + 1`)
and the decreasing run resets to `1`. Symmetrically, when `x < prev`, the decreasing run
extends. When `x = prev`, both runs reset to `1`.

Generalized from the `helper` function in LeetCode 3105. -/
def longestMonotonicRunLenAux {α : Type} [LinearOrder α] (best ni nd : Nat) (prev : α) :
    List α → Nat
  | [] => best
  | x :: xs =>
    let ni' := if x > prev then ni + 1 else 1
    let nd' := if x < prev then nd + 1 else 1
    let best' := max best (max ni' nd')
    longestMonotonicRunLenAux best' ni' nd' x xs

/-- Length of the longest contiguous strictly monotonic (increasing or decreasing)
subarray in `nums`. Returns `0` for the empty list.

Uses a single-pass linear-time algorithm that tracks both increasing and decreasing
run lengths simultaneously, taking the best at each step.

Example: `longestMonotonicRunLen [1, 4, 3, 3, 2] = 2`
(the longest monotonic runs are `[1, 4]` with length 2, and `[3, 2]` also length 2).

Generalized from `longest_monotonic_subarray` in LeetCode 3105. -/
def longestMonotonicRunLen {α : Type} [LinearOrder α] (nums : List α) : Nat :=
  match nums with
  | [] => 0
  | x :: xs => longestMonotonicRunLenAux 1 1 1 x xs

/-! ### Properties of the auxiliary function -/

/-- The auxiliary function always returns a value at least as large as the initial `best`. -/
lemma longestMonotonicRunLenAux_ge_best {α : Type} [LinearOrder α] (best ni nd : Nat) (prev : α)
    (xs : List α) : best ≤ longestMonotonicRunLenAux best ni nd prev xs := by
  induction xs generalizing best ni nd prev with
  | nil => simp [longestMonotonicRunLenAux]
  | cons x xs ih =>
    unfold longestMonotonicRunLenAux
    have hbest' : best ≤ max best (max (if x > prev then ni + 1 else 1) (if x < prev then nd + 1 else 1)) :=
      le_max_left _ _
    have hrec := ih (max best (max (if x > prev then ni + 1 else 1) (if x < prev then nd + 1 else 1)))
                   (if x > prev then ni + 1 else 1)
                   (if x < prev then nd + 1 else 1)
                   x
    exact le_trans hbest' hrec

/-! ### Basic properties of `longestMonotonicRunLen` -/

/-- For a singleton list, the longest monotonic run length is `1`. -/
@[simp]
lemma longestMonotonicRunLen_singleton {α : Type} [LinearOrder α] (x : α) :
    longestMonotonicRunLen [x] = 1 := by
  simp [longestMonotonicRunLen, longestMonotonicRunLenAux]

/-- For the empty list, the longest monotonic run length is `0`. -/
@[simp]
lemma longestMonotonicRunLen_nil {α : Type} [LinearOrder α] :
    longestMonotonicRunLen ([] : List α) = 0 := by
  simp [longestMonotonicRunLen]

/-- For a nonempty list, the longest monotonic run length is at least `1`. -/
lemma longestMonotonicRunLen_ge_one {α : Type} [LinearOrder α] {xs : List α} (h : xs ≠ []) :
    1 ≤ longestMonotonicRunLen xs := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    rw [longestMonotonicRunLen]
    exact longestMonotonicRunLenAux_ge_best 1 1 1 x xs

/-- The longest monotonic run length is bounded by the list length. -/
lemma longestMonotonicRunLen_le_length {α : Type} [LinearOrder α] (xs : List α) :
    longestMonotonicRunLen xs ≤ xs.length := by
  have bound : ∀ (ys : List α) (best ni nd k : Nat) (prev : α),
      best ≤ k → ni ≤ k → nd ≤ k →
      longestMonotonicRunLenAux best ni nd prev ys ≤ k + ys.length := by
    intro ys
    induction ys with
    | nil =>
      intro best ni nd k prev hb hi hd
      simpa [longestMonotonicRunLenAux] using hb
    | cons x ys ih =>
      intro best ni nd k prev hb hi hd
      simp only [longestMonotonicRunLenAux]
      have hn : (if x > prev then ni + 1 else 1) ≤ k + 1 := by split <;> omega
      have hm : (if x < prev then nd + 1 else 1) ≤ k + 1 := by split <;> omega
      have h := ih (max best (max (if x > prev then ni + 1 else 1)
        (if x < prev then nd + 1 else 1)))
        (if x > prev then ni + 1 else 1) (if x < prev then nd + 1 else 1)
        (k + 1) x (by omega) hn hm
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h
  cases xs with
  | nil => simp [longestMonotonicRunLen]
  | cons x xs =>
    simpa [longestMonotonicRunLen, Nat.add_comm] using
      bound xs 1 1 1 1 x (by omega) (by omega) (by omega)

/-! ### Segmented strict monotonicity predicates

`strictlyRisesUntil s peak` asserts that `s` is strictly increasing up to
(and including) index `peak`: for all `a < b ≤ peak`, `s[a] < s[b]`.

`strictlyFallsFrom s peak` asserts that `s` is strictly decreasing from
(and including) index `peak` onwards: for all `peak ≤ a < b`, `s[a] > s[b]`.

Together these predicates describe a "mountain" shape: the list rises to a
peak and then falls away. They are parameterized over any `LT α` order and
use `Fin`-indexed quantification over the list's domain for decidability. -/

/-- `strictlyRisesUntil s peak` holds when `s` is strictly increasing on the
prefix up to index `peak`: for all `a < b ≤ peak` (where `a, b` are valid
`Fin` indices of `s`), we have `s[a] < s[b]`.

Uses `Fin`-indexed `List.get` which is safe since the indices are bounded by
`n = s.length`. -/
def strictlyRisesUntil {α : Type u} [LT α] (s : List α) (peak : Nat) : Prop :=
  let n := s.length
  ∀ (a b : Fin n), (a : Nat) < (b : Nat) → (b : Nat) ≤ peak → s.get a < s.get b

/-- `strictlyFallsFrom s peak` holds when `s` is strictly decreasing on the
suffix starting at index `peak`: for all `peak ≤ a < b` (where `a, b` are valid
`Fin` indices of `s`), we have `s[a] > s[b]`.

The complement of `strictlyRisesUntil` for the downward side of a peak. -/
def strictlyFallsFrom {α : Type u} [LT α] (s : List α) (peak : Nat) : Prop :=
  let n := s.length
  ∀ (a b : Fin n), peak ≤ (a : Nat) → (a : Nat) < (b : Nat) → s.get a > s.get b

end List
