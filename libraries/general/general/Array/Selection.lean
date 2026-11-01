import general.Array.Aggregation
import general.Array.Access

namespace Array

/-! ### Maximum forward difference (max profit in a single pass) -/

/-- Auxiliary function for `maxForwardDiff`: scans the array from left to right,
tracking the minimum value seen (`minPrice`) and the best forward difference
(`bestProfit = max_{i<j} arr[j] - arr[i]` among processed elements).

`remaining` counts how many elements remain to process (decreasing),
so the next element to process is at index `arr.size - (remaining + 1)`. -/
def maxForwardDiffAux (arr : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, bestProfit => bestProfit
  | remaining+1, minPrice, bestProfit =>
    let i := arr.size - (remaining+1)
    if h : i < arr.size then
      let x := arr[i]!
      maxForwardDiffAux arr remaining (min minPrice x) (max bestProfit (x - minPrice))
    else
      maxForwardDiffAux arr remaining minPrice bestProfit

/-- Compute the maximum difference `arr[j] - arr[i]` where `i < j`,
or `0` if the array has fewer than 2 elements (or if all differences are non-positive).
This is the classic "best time to buy and sell stock" single-pass algorithm:
scan left-to-right, tracking `minPrice` and `maxProfit = max(0, price - minPrice)`. -/
def maxForwardDiff (arr : Array Nat) : Nat :=
  if h : arr.size > 0 then
    maxForwardDiffAux arr (arr.size - 1) (arr[0]!) 0
  else 0

/-! ### Max profit step function — `Int` prices, `Nat` profit

This is the `Int`-based counterpart of `maxForwardDiffAux` (which is `Nat`-based).
It provides the pure step function for the classic "best time to buy and sell stock"
algorithm: tracking the running minimum price and the best profit seen so far,
where profit is clipped to zero (`Nat`). -/

/-- A single step of the max-profit computation: given a new `price` and the
current `minPrice` and `best` profit, returns the updated `(minPrice, best)`.
This is a pure function reusable with any fold over price sequences.

`maxProfitStep price minPrice best = (min price minPrice, Nat.max best (price - minPrice).toNat)` -/
def maxProfitStep (price minPrice : Int) (best : Nat) : Int × Nat :=
  let profit := price - minPrice
  (min price minPrice, Nat.max best profit.toNat)

/-- Compute the maximum profit from a single buy-sell transaction on an array of
`Int`-valued stock prices. Returns `max_{0≤i<j<n} max(0, prices[j] - prices[i])`.
This is the classic "Best Time to Buy and Sell Stock" single-pass algorithm,
using `maxProfitStep` as the step function in a fold.

Returns `0` if the array is empty or no profit is possible. -/
def maxProfitArray (prices : Array Int) : Nat :=
  if h : prices.size = 0 then 0 else
  let initMin := prices[0]!
  (prices.foldl (fun (acc : Int × Nat) (p : Int) =>
    maxProfitStep p acc.1 acc.2) (initMin, 0)).2

/-- When extending the scan from `k` to `k+1` processed elements,
the bound on all pairwise forward differences is updated to
`max bestProfit (arr[k]! - minPrice)`.

Given that among the first `k` elements, all forward differences are bounded by `bestProfit`,
and `minPrice` is ≤ every element among the first `k`,
this lemma shows that among the first `k+1` elements, all forward differences
are bounded by `max bestProfit (arr[k]! - minPrice)`. -/
lemma maxForwardDiff_step_bound (arr : Array Nat) (k minPrice bestProfit : Nat)
    (h_best_max : ∀ j l, j < l → l < k → (arr[j]! < arr[l]! → arr[l]! - arr[j]! ≤ bestProfit))
    (h_min_le : ∀ j, j < k → minPrice ≤ arr[j]!) :
    ∀ j l, j < l → l < k+1 → (arr[j]! < arr[l]! → arr[l]! - arr[j]! ≤ max bestProfit ((arr[k]!) - minPrice)) := by
  intro j l hjl hl_succ hlt
  by_cases hlk : l < k
  · have h_le := h_best_max j l hjl hlk hlt
    have h_max_le : bestProfit ≤ max bestProfit (arr[k]! - minPrice) := by simp
    omega
  · have heq : l = k := by omega
    have hjk : j < k := by omega
    have hmin_j : minPrice ≤ arr[j]! := h_min_le j hjk
    have h_sub_le : (arr[k]!) - (arr[j]!) ≤ (arr[k]!) - minPrice :=
      Nat.sub_le_sub_left hmin_j (arr[k]!)
    have h_max_le : (arr[k]!) - minPrice ≤ max bestProfit ((arr[k]!) - minPrice) := by simp
    rw [heq]
    omega

end Array

namespace Array

/-! ### Array maximum via `foldl max` -/

/-- Fold an array by taking the element-wise maximum, starting from `init`.
Generalized to any type with `Max`. This is the general building block
for array-maximum computations; see also `arrayMax` for the common case
where `init` is the first element. -/
def foldMaxOf {α : Type} [Max α] (arr : Array α) (init : α) : α :=
  arr.foldl (fun acc x => max acc x) init

/-- Compute the maximum element of an array by folding `max` from the left,
using the first element (or `default` if empty) as the initial accumulator.
Generalized to any `LinearOrder α` with an `Inhabited` instance. -/
def arrayMax {α : Type} [LinearOrder α] [Inhabited α] (xs : Array α) : α :=
  xs.foldl max xs[0]!

/-! ### Array min/max via simultaneous fold -/

/-- Fold over an array, simultaneously accumulating the minimum and maximum values seen so far.
Generalized to any type `α` with a `LinearOrder` and `Inhabited`.
The fold is a single pass that updates both `min_val` and `max_val` at each element.
This is more efficient than calling `arrayMin` and `arrayMax` separately
since it traverses the array only once. -/
def foldMinMax {α : Type u} [LinearOrder α] [Inhabited α] (arr : Array α) (i : Nat) (min_val max_val : α) : Prod α α :=
  if h : i < arr.size then
    foldMinMax arr (i + 1) (min min_val (arr[i]!)) (max max_val (arr[i]!))
  else
    (min_val, max_val)

/-- Find both the minimum and maximum elements in a non-empty array in a single pass.
Returns a pair `(min, max)`. The array must have at least one element;
behavior on empty arrays is well-defined (returns `(default, default)`)
but semantically meaningless. -/
def arrayMinMax {α : Type u} [LinearOrder α] [Inhabited α] (arr : Array α) : Prod α α :=
  let first := arr[0]!
  foldMinMax arr 1 first first

/-! ### Maximum of a projected value -/

/-- The maximum of `f` applied to each element of `arr`. Returns 0 for the empty array. -/
def maxOf {α : Type} (f : α → Nat) (arr : Array α) : Nat :=
  (arr.map f).foldl Nat.max 0

/-- Every element of the array is ≤ `arrayMax`. For any index `k < xs.size`,
`xs[k]! ≤ arrayMax xs`. This is the array counterpart of `List.foldl_max_ge_all`. -/
lemma arrayMax_ge_all {α : Type} [LinearOrder α] [Inhabited α] (xs : Array α) (k : Nat)
    (hk : k < xs.size) : xs[k]! ≤ arrayMax xs := by
  unfold arrayMax
  rw [← Array.foldl_toList]
  have h_mem : xs[k]! ∈ xs.toList := by
    have := Array.getElem_mem_toList xs k hk
    simpa [LawfulGetElem.getElem!_def, hk] using this
  simpa using List.foldl_max_ge_all xs[0]! xs.toList (xs[k]!) h_mem

/-- Maximum element in a contiguous slice of an array `a[i..j]` (inclusive),
starting from `init` as the default. When the range is empty (`j < i` in `Nat`
subtraction), returns `init`. Uses `!`-indexing; callers should ensure
`i` and `j` are in bounds for meaningful results. -/
def maxInSubarray [LinearOrder α] [Inhabited α] (init : α) (a : Array α) (i j : Nat) : α :=
  (List.range (j + 1 - i)).foldl (fun acc d => max acc (a[i + d]!)) init

/-! ### Sliding window maximum -/

/-- Maximum value in a window of length `k` starting at index `i` in array `arr`.
Uses `List.foldl max` with `arr[i]!` as the initial accumulator.

Generalizes over any `α` with `LinearOrder α` and `Inhabited α` (matching the
existing `Array.maxInSubarray`). For `k = 0`, returns `arr[i]!`. -/
def windowMax (arr : Array α) [LinearOrder α] [Inhabited α] (i k : Nat) : α :=
  List.foldl max arr[i]! (List.map (fun j => arr[i + j]!) (List.range k))

/-- Sliding window maximum: given an array `arr` and window size `k` (with `0 < k`),
compute the maximum value in every contiguous subarray of length `k`.

Returns `List α` with one entry per window position (from left to right),
so the result length is `arr.size - k + 1` (or `0` if `arr.size < k`).

Generalized from `Array Int` to any `α` with `LinearOrder α` and `Inhabited α`. -/
def slidingWindowMax (arr : Array α) [LinearOrder α] [Inhabited α] (k : Nat) (hk : 0 < k) : List α :=
  let n := arr.size
  if n < k then
    []
  else
    List.ofFn (fun (i : Fin (n - k + 1)) => windowMax arr i.val k)

/-! ### `maxInSlice` — maximum value in a slice

`maxInSlice` computes the maximum in a contiguous slice `arr[start..start+len)`
by folding `max` over `List.range len` directly (no intermediate mapped list).
This is equivalent to `windowMax`; the difference is that `maxInSlice` requires
only `[Max α]` (not `[LinearOrder α]`), making it more general. -/

/-- Maximum value in a slice of `arr` from index `start` of length `len`.
Uses a direct fold over `List.range len` (no intermediate mapped list).
For `len = 0`, returns `arr[start]!`.

This is equivalent to `windowMax` but uses only `[Max α]` instead of `[LinearOrder α]`,
making it applicable to any type with a `Max` instance. -/
def maxInSlice (arr : Array α) (start len : Nat) [Max α] [Inhabited α] : α :=
  (List.range len).foldl (fun mx j => max mx (arr[start + j]!)) (arr[start]!)

/-- `maxInSlice` expressed as `List.foldl max` over mapped array values,
which matches the implementation style of `windowMax`. -/
lemma maxInSlice_eq_foldl_map {α : Type _} [Max α] [Inhabited α]
    (arr : Array α) (start len : Nat) :
    arr.maxInSlice start len = List.foldl max (arr[start]!)
      (List.map (fun j => arr[start + j]!) (List.range len)) := by
  simpa [Array.maxInSlice] using (List.foldl_map (fun j => arr[start + j]!) max (List.range len) (arr[start]!)).symm

/-- `windowMax` and `maxInSlice` are equivalent. -/
lemma windowMax_eq_maxInSlice (arr : Array α) [LinearOrder α] [Inhabited α] (i k : Nat) :
    windowMax arr i k = arr.maxInSlice i k := by
  rw [windowMax, (maxInSlice_eq_foldl_map arr i k).symm]

end Array


namespace Array

/-! ### Argmax — index of maximum value -/

/-- Find the index of the maximum value in `arr[0..n)`.
Returns `0` if all values are 0 (ties broken by first occurrence). -/
def argmax (arr : Array Nat) (n : Nat) : Nat :=
  let initVal : Nat × Nat := (0, 0)
  let (_, maxIdx) :=
    (List.range n).foldl
      (fun best i =>
        let cnt := arr[i]!
        if cnt > best.1 then (cnt, i) else best)
      initVal
  maxIdx

/-! ### Find index of maximum element (generic over `LinearOrder`) -/

/-- Find the index of the maximum element in `a[0..sz)`, searching from index `i`
    and tracking the current best index `cur`. Ties are broken by choosing the
    earlier index (the update only happens when `a[i]! > a[cur]!`).
    Generalized to any `LinearOrder α` with an `Inhabited` instance.

    `findMaxIdxAux a i cur sz` searches from index `i` up to (but not including) `sz`. -/
def findMaxIdxAux {α : Type} [LinearOrder α] [Inhabited α] (a : Array α) (i cur sz : Nat) : Nat :=
  if h : i < sz then
    let cur' := if a[i]! > a[cur]! then i else cur
    findMaxIdxAux a (i + 1) cur' sz
  else
    cur
termination_by sz - i
decreasing_by
  omega

/-- Find the index of the maximum element in array `a`, breaking ties by choosing
    the earlier index. This is the wrapper that starts the search from the beginning
    of the array. Generalized to any `LinearOrder α` with an `Inhabited` instance.

    This is the generic counterpart of `Array.argmax`, which is `Nat`-specific
    and returns `0` when all values are zero. -/
def findMaxIdx {α : Type} [LinearOrder α] [Inhabited α] (a : Array α) : Nat :=
  findMaxIdxAux a 0 0 a.size

/-! ### `indexOfMaxAux` — find index of maximum by scanning to end of array

This is an alternative to `findMaxIdxAux` with a simpler signature: it always scans
to `arr.size` (no explicit `sz` parameter) and tracks only the current-max index
`maxIdx` rather than separately tracking `cur` and `sz`.

The loop invariant (for the proofs) is that all elements before `i` are ≤ `arr[maxIdx]!`,
and all elements before `maxIdx` are < `arr[maxIdx]!`. -/

/-- Scan `arr` from index `i` to the end, tracking the index `maxIdx` of the maximum seen so far.
Works for any linearly ordered inhabited element type. Ties are broken by keeping the
earlier index. -/
def indexOfMaxAux {α : Type} [LinearOrder α] [Inhabited α] (arr : Array α) (i maxIdx : Nat) : Nat :=
  if h : i < arr.size then
    if hlt : arr[maxIdx]! < arr[i]! then
      indexOfMaxAux arr (i+1) i
    else
      indexOfMaxAux arr (i+1) maxIdx
  else
    maxIdx
termination_by arr.size - i
decreasing_by
  · exact Nat.sub_succ_lt_self arr.size i h
  · exact Nat.sub_succ_lt_self arr.size i h

/-- Every element is ≤ the element at the result index of `indexOfMaxAux`.
Given that `maxIdx` is in bounds and all elements before `i` are ≤ `arr[maxIdx]!`,
the result index `indexOfMaxAux arr i maxIdx` points to a value that is ≥ every element
in the array. -/
lemma indexOfMaxAux_ge_all {α : Type} [LinearOrder α] [Inhabited α]
    (arr : Array α) (i maxIdx : Nat) (hm : maxIdx < arr.size)
    (hle : ∀ j, j < i → arr[j]! ≤ arr[maxIdx]!) :
    ∀ j, j < arr.size → arr[j]! ≤ arr[indexOfMaxAux arr i maxIdx]! := by
  rw [indexOfMaxAux]
  split
  · next hi =>
    split
    · next hgt =>
      apply indexOfMaxAux_ge_all arr (i+1) i hi
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact (hle j hj).trans (le_of_lt hgt)
      · exact le_rfl
    · next hngt =>
      apply indexOfMaxAux_ge_all arr (i+1) maxIdx hm
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact hle j hj
      · exact le_of_not_gt hngt
  · next hi => intro j hj; exact hle j (by omega)
termination_by arr.size - i
decreasing_by all_goals omega

/-- All elements before the result index of `indexOfMaxAux` are strictly smaller
than the element at that index. This is the "strictness" counterpart of
`indexOfMaxAux_ge_all`: not only is the result a maximum, but every earlier element
is *strictly* less. -/
lemma indexOfMaxAux_lt_before {α : Type} [LinearOrder α] [Inhabited α]
    (arr : Array α) (i maxIdx : Nat) (hm : maxIdx < arr.size)
    (hle : ∀ j, j < i → arr[j]! ≤ arr[maxIdx]!)
    (hlt : ∀ j, j < maxIdx → arr[j]! < arr[maxIdx]!) :
    ∀ j, j < indexOfMaxAux arr i maxIdx → arr[j]! < arr[indexOfMaxAux arr i maxIdx]! := by
  rw [indexOfMaxAux]
  split
  · next hi =>
    split
    · next hgt =>
      apply indexOfMaxAux_lt_before arr (i+1) i hi
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
        · exact (hle j hj).trans (le_of_lt hgt)
        · exact le_rfl
      · intro j hj; exact (hle j hj).trans_lt hgt
    · next hngt =>
      apply indexOfMaxAux_lt_before arr (i+1) maxIdx hm
      · intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
        · exact hle j hj
        · exact le_of_not_gt hngt
      · exact hlt
  · exact hlt
termination_by arr.size - i
decreasing_by all_goals omega

end Array



namespace Array


/-! ### Distinct values as a Finset -/

/-- The distinct values of an array, collected as a `Finset`.
Maps each index `i < arr.size` to `arr[i]` and deduplicates via `Finset.image`. -/
def distinctVals {α : Type _} [DecidableEq α] (arr : Array α) : Finset α :=
  ((Finset.univ : Finset (Fin arr.size)).image fun i : Fin arr.size => arr[i])

/-! ### Triple products — set of all products of three distinct elements -/

/-- The Finset of all products `nums[i]! * nums[j]! * nums[k]!` for strictly increasing indices
`i < j < k`. Uses `Fin.increasingTriples` for efficient enumeration of exactly `C(n,3)` triples.
Generalized to any `α` with `Mul`, `DecidableEq`, and `Inhabited`. -/
def tripleProducts {α : Type _} [Mul α] [DecidableEq α] [Inhabited α] (nums : Array α) : Finset α :=
  (Fin.increasingTriples nums.size).image (fun ((i, j, k) : Fin nums.size × Fin nums.size × Fin nums.size) =>
    nums[i]! * nums[j]! * nums[k]!)

/-! ### Check whether any distinct pair of indices satisfies a predicate -/

/-- Check whether any distinct pair of indices in `arr` satisfies
a binary predicate `f` on the array elements.

This is a common pattern in LeetCode problems that ask
"does there exist a pair of distinct indices i, j such that ...?" -/
def anyPairDistinct {α : Type} [Inhabited α] (arr : Array α) (f : α → α → Bool) : Bool :=
  (List.range arr.size).any (λ i =>
    (List.range arr.size).any (λ j =>
      i != j && f (arr[i]!) (arr[j]!)))

/-- Relates `anyPairDistinct` to the natural existential statement:
there exist distinct indices `i`, `j` such that `f` holds on the corresponding elements. -/
theorem anyPairDistinct_iff {α : Type} [Inhabited α] (arr : Array α) (f : α → α → Bool) :
    (anyPairDistinct arr f = true) ↔
    (∃ i < arr.size, ∃ j < arr.size, i ≠ j ∧ f (arr[i]!) (arr[j]!) = true) := by
  simp [anyPairDistinct, List.any_eq_true, List.mem_range]


end Array

namespace Array

/-! ### Absolute difference between projected elements -/

/-- The absolute difference between `f a[i]` and `f a[j]` as a `Nat`,
where `f` projects array elements to `Int` coordinates.
Useful for coordinate geometry (e.g., computing `|xᵢ - xⱼ|`) and any scenario
where array elements carry an `Int`-valued coordinate or weight. -/
def absDiffBy {α : Type} [Inhabited α] (a : Array α) (f : α → Int) (i j : Nat) : Nat :=
  Int.natAbs (f a[i]! - f a[j]!)

/-- `absDiffBy` is symmetric: `absDiffBy a f i j = absDiffBy a f j i`. -/
lemma absDiffBy_comm {α : Type} [Inhabited α] (a : Array α) (f : α → Int) (i j : Nat) :
    absDiffBy a f i j = absDiffBy a f j i := by
  unfold absDiffBy
  have h : f a[i]! - f a[j]! = -(f a[j]! - f a[i]!) := by ring
  rw [h, Int.natAbs_neg]

/-- Self-distance is zero: `absDiffBy a f i i = 0`. -/
lemma absDiffBy_self {α : Type} [Inhabited α] (a : Array α) (f : α → Int) (i : Nat) :
    absDiffBy a f i i = 0 := by
  unfold absDiffBy
  have h : f a[i]! - f a[i]! = 0 := by ring
  rw [h, Int.natAbs_zero]

end Array
