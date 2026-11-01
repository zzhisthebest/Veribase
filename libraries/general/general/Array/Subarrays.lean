import Mathlib

namespace Array


/-! ### Subarray start indices -/

/-- All candidate start indices for a subarray of length `len` in an array of size `n`.
That is, `[0, 1, ..., n - len]` (empty if `len > n`, since `n - len = 0` and `range 1 = [0]`). -/
def subarrayStartIndices (n len : Nat) : List Nat :=
  List.range (n - len + 1)




/-! ### Subarray slice extraction -/

/-- Extract a contiguous slice `arr[i..j]` (inclusive) as a `List`.
Returns `[]` if the bounds are invalid (i.e., `i > j` or `j ≥ arr.size`).
Uses `List.ofFn` to construct the slice from index `i` to index `j`.

This is the fundamental building block for subarray operations; higher-level
operations like `subarraySum` and `subarrayGcd` fold over the extracted range. -/
def subarraySlice {α : Type} [Inhabited α] (arr : Array α) (i j : Nat) : List α :=
  if i ≤ j ∧ j < arr.size then
    List.ofFn (fun (k : Fin (j - i + 1)) => arr[i + k.val]!)
  else
    []

/-! ### Subarray sum -/

/-- Sum of a contiguous subarray `arr[start..start+len-1]`.
Uses `arr[i]!` (unsafe indexing); callers must ensure `start + len ≤ arr.size`. -/
def subarraySum {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (start len : Nat) : α :=
  (List.range len).foldl (fun acc k => acc + arr[start + k]!) 0

theorem subarraySum_one {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (start : Nat) :
    subarraySum arr start 1 = arr[start]! := by
  unfold subarraySum
  have h : List.range 1 = [0] := by decide
  rw [h]
  simp

/-- Prefix sum: the sum of the first `n` elements of the array.
Returns `0` when `n = 0`. Defined as `subarraySum arr 0 n`.
Consistent with `List.prefixSum`. -/
def prefixSum {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (n : Nat) : α :=
  subarraySum arr 0 n

/-- Sum of a contiguous subarray `arr[lo..hi]` (inclusive).
This is a convenience wrapper around `subarraySum` that takes
inclusive lower/upper bounds instead of `(start, len)`.

Equivalent to `subarraySum arr lo (hi - lo + 1)`.
When `hi < lo`, `hi - lo` underflows to `0` (Nat truncated subtraction),
so the result is `arr[lo]!`. -/
def rangeSum {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (lo hi : Nat) : α :=
  subarraySum arr lo (hi - lo + 1)

/-- Sum of a contiguous subarray `arr[lo..<hi]` (lo inclusive, hi exclusive).
Half-open interval style: sums elements from index `lo` up to but not including `hi`.
When `hi ≤ lo`, the sum is `0`.

Equivalent to `subarraySum arr lo (hi - lo)`. -/
def subarraySumRange {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (lo hi : Nat) : α :=
  subarraySum arr lo (hi - lo)

/-- Sum of a single-element half-open subarray `arr[lo..<lo+1]` is `arr[lo]!`. -/
theorem subarraySumRange_singleton {α : Type} [AddMonoid α] [Inhabited α]
    (arr : Array α) (lo : Nat) : subarraySumRange arr lo (lo + 1) = arr[lo]! := by
  unfold subarraySumRange
  have h : (lo + 1) - lo = 1 := by omega
  rw [h]
  exact subarraySum_one arr lo

/-- `subarraySumRange` and `subarraySum` agree: `subarraySumRange arr lo hi = subarraySum arr lo (hi - lo)`. -/
theorem subarraySumRange_eq_subarraySum {α : Type} [AddMonoid α] [Inhabited α]
    (arr : Array α) (lo hi : Nat) : subarraySumRange arr lo hi = subarraySum arr lo (hi - lo) := rfl

/-! ### Fold over a contiguous range — the general building block

`foldRange f init arr i j` folds a binary operation `f` over the contiguous subarray
`arr[i..j]` (inclusive), starting with `init`. Returns `init` if `¬ i ≤ j`.

This is the general primitive underlying `subSum`, `maxInSubarray`, `subarrayGcd`,
`segmentXor`, `countInRange`, and other range-fold operations. Each of those
specializations fixes `f` and `init` for a specific operation (addition, max,
gcd, xor, counting, etc.). -/
def foldRange {α : Type} [Inhabited α] (f : α → α → α) (init : α) (A : Array α) (i j : Nat) : α :=
  if h : i ≤ j then
    (List.range (j + 1 - i)).foldl (fun acc k => f acc (A[i + k]!)) init
  else init

/-! ### Inclusive subarray sum (returns `0` on empty range) -/

/-- Sum of a contiguous subarray from index `i` to `j` (inclusive).
Returns `0` when `j < i`.

Unlike `rangeSum`, which underflows to `arr[lo]!` when `hi < lo` due to Nat
truncated subtraction, `subSum` explicitly returns `0` for empty ranges.
This makes it the natural choice for maximum-subarray and similar algorithms
where the candidate range may be empty. -/
def subSum {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (i j : Nat) : α :=
  (List.range (j + 1 - i)).foldl (fun acc k => acc + arr[i + k]!) 0

/-- A single-element subarray `arr[i..i]` is just `arr[i]!`. -/
theorem subSum_single {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (i : Nat)
    (hi : i < arr.size) : subSum arr i i = arr[i]! := by
  unfold subSum
  have hsub : i + 1 - i = 1 := by omega
  rw [hsub]
  have hrange : List.range 1 = [0] := by decide
  rw [hrange]
  simp

/-- Extending the subarray one step to the right:
`subSum arr i (j+1) = subSum arr i j + arr[j+1]!`. -/
theorem subSum_succ {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (i j : Nat)
    (hij : i ≤ j) (hj : j + 1 < arr.size) :
    subSum arr i (j+1) = subSum arr i j + arr[j+1]! := by
  unfold subSum
  have h_range_succ : (j+1)+1 - i = ((j+1 - i : Nat).succ) := by omega
  rw [h_range_succ]
  rw [List.range_succ]
  rw [List.foldl_append]
  simp
  have h_add : i + (j+1 - i) = j+1 := by omega
  rw [h_add]

/-- When the end index `j` is before the start index `i`, the subarray is empty and the sum is `0`. -/
theorem subSum_eq_zero_of_j_lt_i {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (i j : Nat)
    (h : j < i) : subSum arr i j = 0 := by
  unfold subSum
  have hsub : j + 1 - i = 0 := by omega
  rw [hsub]
  simp

/-- Extend a suffix sum from `k-1` to `k` (requires `0 < k`).
This lemma decomposes `subSum arr a k` into `subSum arr a (k-1) + arr[k]!`,
useful for induction proofs about subarray sums. -/
theorem subSum_extend {α : Type} [AddMonoid α] [Inhabited α] (arr : Array α) (a k : Nat)
    (ha_le : a ≤ k) (hk_pos : 0 < k) (hk_lt : k < arr.size) :
    subSum arr a k = subSum arr a (k-1) + arr[k]! := by
  by_cases ha_eq : a = k
  · rw [ha_eq]
    rw [subSum_single arr k hk_lt]
    have hzero : subSum arr k (k-1) = 0 := by
      apply subSum_eq_zero_of_j_lt_i; omega
    rw [hzero]
    simp
  · have ha_le' : a ≤ k-1 := by omega
    have hsucc : (k-1)+1 = k := by omega
    rw [← hsucc, subSum_succ arr a (k-1) ha_le' (by omega), hsucc]

/-! ### Subarray product — the multiplicative counterpart of `subSum`

`subarrayProduct arr i j` computes the product of `arr[i]! * arr[i+1]! * ... * arr[j]!`.
Returns `1` (the multiplicative identity) when `j < i`.
Uses `arr[i]!` (unsafe indexing); callers must ensure `j < arr.size` for meaningful results.

This is the product analog of `subSum` (which is additive) and follows the same
inclusive-range design pattern. -/

/-- Product of a contiguous subarray from index `i` to `j` (inclusive).
Returns `1` when `j < i` (empty product = multiplicative identity).
Generalized to any `Monoid α` with an `Inhabited` instance. -/
def subarrayProduct {α : Type} [Monoid α] [Inhabited α] (arr : Array α) (i j : Nat) : α :=
  (List.range (j + 1 - i)).foldl (fun acc k => acc * arr[i + k]!) 1

/-! ### Subarray XOR -/

/-- XOR of a contiguous subarray `arr[start..start+len-1]`.
Uses `arr[i]!` (unsafe indexing); callers must ensure `start + len ≤ arr.size`.
The XOR-of-subarray counterpart of `subarraySum`. -/
def segmentXor (arr : Array Nat) (start len : Nat) : Nat :=
  (List.range len).foldl (fun acc k => Nat.xor acc (arr[start + k]!)) 0

/-- XOR all elements in an array, with `0` as the identity element.
This is the whole-array counterpart of `segmentXor`. -/
def xorAll (arr : Array Nat) : Nat :=
  arr.foldl Nat.xor 0


end Array
