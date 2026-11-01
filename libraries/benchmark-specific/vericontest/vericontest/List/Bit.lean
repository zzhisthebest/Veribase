import Mathlib

open List

namespace List

/-! ### Bit counting on lists

These functions operate on `List Nat` and involve bit-level operations
(`Nat.testBit`, `<<<`, `|||`). They are the list-level counterparts of the
bit operations in `general/Nat.lean` (e.g., `bitDiffCount`, `countOnesPrefix`).

`countBit` counts how many elements of a list have a given bit set,
generalizing the single-integer `Nat.countOnesPrefix` to a list of integers.

`kOr` computes the bitwise OR of all bit positions where at least `k`
elements have that bit set — this is the classic "K-or" algorithm
(LeetCode 2917).
-/

/-- Count how many elements of `nums` have bit `bit` set to `1`.
`countBit nums bit = |{ x ∈ nums | Nat.testBit x bit }|`.
This is the list-level counterpart of `Nat.countOnesPrefix`, which counts
bits within a single integer. -/
def countBit (nums : List Nat) (bit : Nat) : Nat :=
  nums.countP (fun x => Nat.testBit x bit)

/-- Compute the bitwise OR of all bit positions from `bit` (inclusive) to
`maxBit` (exclusive) where at least `k` numbers in `nums` have that bit set.

`kOr nums k maxBit bit = ⋁_{pos ∈ [bit, maxBit)} { 1 <<< pos | countBit nums pos ≥ k }`

Common use: `kOr nums k 32 0` computes the K-or for 32-bit integers.
Returns `0` when `bit ≥ maxBit`. -/
def kOr (nums : List Nat) (k : Nat) (maxBit : Nat) (bit : Nat) : Nat :=
  if bit < maxBit then
    let add := if countBit nums bit ≥ k then 1 <<< bit else 0
    add ||| kOr nums k maxBit (bit + 1)
  else
    0
termination_by maxBit - bit
decreasing_by
  omega

/-! ### XOR operations on lists

`xorAll_specificDuplicate nums` folds bitwise XOR over a list with initial value `0`.
`xorPrefix nums len` computes the XOR of the first `len` elements.

These are building blocks for problems involving XOR queries over list prefixes,
such as LeetCode 2997 "Minimum Number of Operations to Make Array XOR Equal to K".
-/

/-- XOR fold over a list with initial value `0`: `xorAll_specificDuplicate nums = ⋁_{x ∈ nums} x`.
Since XOR has `0` as identity, `xorAll_specificDuplicate [] = 0`. -/
def xorAll_specificDuplicate (nums : List Nat) : Nat :=
  nums.foldl (· ^^^ ·) 0

/-- XOR of the first `len` elements of `nums`:
`xorPrefix nums len = xorAll_specificDuplicate (nums.take len)`. -/
def xorPrefix (nums : List Nat) (len : Nat) : Nat :=
  (nums.take len).foldl (· ^^^ ·) 0

/-- Folding XOR from an initial accumulator equals the accumulator XOR'd with the
zero-init fold. This captures the commutativity/associativity of XOR in the `foldl`
context: `(foldl (· ^^^ ·) init l) = init ^^^ (foldl (· ^^^ ·) 0 l)`. -/
theorem foldl_xor_eq_xor_foldl_zero (l : List Nat) (init : Nat) :
    l.foldl (· ^^^ ·) init = init ^^^ (l.foldl (· ^^^ ·) 0) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    have h_init : (x :: xs).foldl (· ^^^ ·) init = xs.foldl (· ^^^ ·) (init ^^^ x) := rfl
    have h_zero : (x :: xs).foldl (· ^^^ ·) 0 = xs.foldl (· ^^^ ·) x := by
      simp
    rw [h_init, h_zero, ih (init ^^^ x), ih x, Nat.xor_assoc]

@[simp]
theorem xorAll_cons (x : Nat) (xs : List Nat) : xorAll_specificDuplicate (x :: xs) = x ^^^ xorAll_specificDuplicate xs := by
  unfold xorAll_specificDuplicate
  have h : (x :: xs).foldl (· ^^^ ·) 0 = xs.foldl (· ^^^ ·) x := by simp
  rw [h, foldl_xor_eq_xor_foldl_zero xs x]

theorem xorAll_append (a b : List Nat) : xorAll_specificDuplicate (a ++ b) = (xorAll_specificDuplicate a) ^^^ (xorAll_specificDuplicate b) := by
  unfold xorAll_specificDuplicate
  rw [List.foldl_append]
  rw [foldl_xor_eq_xor_foldl_zero b]

end List
