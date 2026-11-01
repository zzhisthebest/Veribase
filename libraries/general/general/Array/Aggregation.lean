import Mathlib
import general.List.Filter
import general.Array.Access

namespace Array



/-! ### Count strings with a given prefix -/

/-- Count how many strings in an `Array String` have `pref` as a prefix.
Equivalent to `Array.countWhere strings (pref.isPrefixOf ·)`. -/
def countPrefix (strings : Array String) (pref : String) : Nat :=
  (Array.filter (pref.isPrefixOf ·) strings).size





/-! ### Counting occurrences of a specific value via Finset -/

/-- Count how many times a value `x` appears in `arr` using a Finset of matching indices.
This is the Finset-based counterpart of `Array.count` (which is foldl-based).
Useful when Finset cardinality reasoning is preferred for proofs
(e.g., `Finset.one_lt_card` for establishing at least two occurrences).

Generalized to any type `α` with `DecidableEq` and `Inhabited`. -/
def countOcc {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (x : α) : Nat :=
  ((Finset.range arr.size).filter (λ i => arr[i]! = x)).card

/-! ### Counting occurrences across a 2D array (board pattern) -/

/-- Count how many times a value `x` appears across all rows of a 2D array.
Sums `row.count x` over every row. This is the generalized, efficient counterpart
of the `countChar` pattern frequently found in board-game problems
(TicTacToe, Connect Four, Boggle, etc.).

For counting in a flat 1D array, use `Array.count` (from std). -/
def count2D [BEq α] (board : Array (Array α)) (x : α) : Nat :=
  board.foldl (fun acc row => acc + row.count x) 0

/-! ### Counting elements satisfying a predicate -/

/-- Count the number of elements in an array that satisfy a Boolean predicate.
Polymorphic over the element type `α`. -/
def countWhere {α : Type} (as : Array α) (p : α → Bool) : Nat :=
  (as.toList.filter p).length

/-- Count the number of elements in an array satisfying a decidable `Prop` predicate.
This is the `Prop` counterpart of `countWhere` (which works with `Bool` predicates).
Uses `foldl` over the array to count matching elements. -/
def countPred {α : Type} (p : α → Prop) [DecidablePred p] (arr : Array α) : Nat :=
  arr.foldl (fun acc a => if p a then acc + 1 else acc) 0

/-- Count elements in `nums` that are `≥ x`. -/
def countGE (nums : Array Nat) (x : Nat) : Nat :=
  countPred (fun a => a ≥ x) nums

/-! ### Filter membership and size -/

/-- If an element is in `arr.filter p`, then `p` holds for that element.
This is the converse of `Array.mem_filter` — instead of requiring both `x ∈ arr` and `p x`
to prove `x ∈ arr.filter p`, this extracts `p x` from the membership. -/
lemma mem_filter_imp_pred {α : Type _} (arr : Array α) (p : α → Bool) (x : α) (h : x ∈ arr.filter p) :
    p x := by
  rw [← Array.mem_toList, Array.toList_filter] at h
  rcases List.mem_filter.mp h with ⟨_, hp⟩
  exact hp

/-- The size of `arr.filter p` plus the size of `arr.filter (¬ p)` equals the size of `arr`.
This is the array counterpart of `List.length_filter_add_filter_not`. -/
lemma size_filter_add_filter_not {α : Type _} (arr : Array α) (p : α → Bool) :
    (arr.filter p).size + (arr.filter (λ x => !(p x))).size = arr.size := by
  have h := List.length_filter_add_filter_not arr.toList p
  have h1 : (arr.filter p).size = (List.filter p arr.toList).length := by
    rw [← Array.length_toList, Array.toList_filter]
  have h2 : (arr.filter (λ x => !(p x))).size = (List.filter (λ x => !(p x)) arr.toList).length := by
    rw [← Array.length_toList, Array.toList_filter]
  have h3 : arr.size = arr.toList.length := by rw [Array.length_toList]
  rw [h1, h2, h3, h]

/-- If an element is retrieved from a filtered array via `!`, the predicate holds.
Given an index `i` within bounds of `arr.filter p`, the element at that index satisfies `p`. -/
lemma get_filter_elem_pred {α : Type _} [Inhabited α] (arr : Array α) (p : α → Bool) (i : Nat)
    (hi : i < (arr.filter p).size) : p ((arr.filter p)[i]!) := by
  have h := getElem!_eq_getElem (arr.filter p) i hi
  rw [h]
  have hmem : (arr.filter p)[i]'(hi) ∈ arr.filter p := Array.getElem_mem hi
  exact mem_filter_imp_pred arr p _ hmem

/-- Elements of a filtered array satisfy the filter predicate. This is the safe `getElem`
counterpart of `get_filter_elem_pred` — it uses `(arr.filter p)[i]` (which requires a
bounds proof `hlt`) instead of `[i]!`, and does not require `Inhabited`. -/
lemma filter_getElem_pred {α : Type _} (a : Array α) (p : α → Bool) (i : Nat)
    (hlt : i < (a.filter p).size) : p ((a.filter p)[i]) = true := by
  have hmem : (a.filter p)[i] ∈ a.filter p := Array.getElem_mem hlt
  exact (Array.mem_filter.mp hmem).2

/-- Counting elements ≥ 0 gives the total size, since every `Nat` is ≥ 0. -/
lemma countGE_zero (nums : Array Nat) : countGE nums 0 = nums.size := by
  unfold countGE countPred
  simp only
  rw [← Array.foldl_toList, Array.size_eq_length_toList]
  have foldl_add_one (l : List Nat) (b : Nat) :
      (l.foldl (fun acc a => if a ≥ 0 then acc + 1 else acc) b) = b + l.length := by
    induction' l with x xs ih generalizing b
    · rfl
    · rw [List.foldl_cons, List.length_cons]
      have hx : x ≥ 0 := Nat.zero_le x
      simp [hx, ih]
      omega
  rw [foldl_add_one nums.toList 0, zero_add]

/-! ### Count elements NOT satisfying a predicate -/

/-- Count the number of elements in `arr` that do NOT satisfy predicate `p`,
    using a left fold with initial count `init`. This is the internal foldl-based
    implementation; prefer `countWhereNot` for the common zero-init case. -/
def countWhereNotAux {α : Type} (arr : Array α) (p : α → Bool) (init : Nat) : Nat :=
  arr.foldl (fun acc x => if p x then acc else acc + 1) init

/-- Count the number of elements in `arr` that do NOT satisfy predicate `p`,
    starting from zero. This is the complement of `countWhere`:
    `countWhereNot arr p = arr.size - countWhere arr p` (when `init = 0`). -/
def countWhereNot {α : Type} (arr : Array α) (p : α → Bool) : Nat :=
  countWhereNotAux arr p 0

/-- `countWhereNotAux` over an empty array returns the initial count unchanged. -/

lemma countWhereNotAux_empty {α : Type} (p : α → Bool) (init : Nat) :
    countWhereNotAux #[] p init = init := rfl

/-- `countWhereNot` over an empty array returns zero. -/

lemma countWhereNot_empty {α : Type} (p : α → Bool) : countWhereNot #[] p = 0 := rfl

/-- `countWhereNot` over a singleton array: returns 0 if `p x` is true (element is
    "kept"), and 1 if `p x` is false (element is "not kept"). -/

lemma countWhereNot_singleton {α : Type} (p : α → Bool) (x : α) :
    countWhereNot #[x] p = (if p x then 0 else 1) := rfl

/-! ### Count smaller elements relative to an index -/

/-- Count how many indices `j > i` in `arr` have `arr[j]! < arr[i]!`.
This is the "count smaller numbers after self" pattern,
commonly used in array comparison and inversion-count problems. -/
def countSmallerAfter (arr : Array Nat) (i : Nat) : Nat :=
  ((Finset.range arr.size).filter (fun idx => i < idx ∧ arr[idx]! < arr[i]!)).card

/-! ### Count elements in a subrange -/

/-- Count the number of elements in `arr[l..r]` (inclusive) that satisfy predicate `p`.
Uses `arr[i]!` (unsafe indexing); callers must ensure `l ≤ r` and `r < arr.size`
for meaningful results. When `l > r`, the range is empty and returns `0`. -/
def countInRange {α : Type} [Inhabited α] (arr : Array α) (p : α → Bool) (l r : Nat) : Nat :=
  (List.range (r + 1 - l)).foldl (fun acc i => if p (arr[l + i]!) then acc + 1 else acc) 0

/-! ### Mismatch count — count positions where two arrays differ -/

/-- Count the number of positions where `a` and `b` differ.
Both arrays are assumed to have the same size (only indices up to `a.size` are checked).
Generalized from `Nat` to any `DecidableEq` type with an `Inhabited` instance.
This is the `Array` counterpart of `List.countMismatches`. -/
def countMismatches {α : Type} [DecidableEq α] [Inhabited α] (a b : Array α) : Nat :=
  (List.range a.size).foldl (fun acc i => if a[i]! = b[i]! then acc else acc + 1) 0

/-! ### `Array.count` lemmas — occurrence count of a specific value -/

/-- If `Array.count x a = 1`, then `x` is a member of `a`.
A convenience lemma combining `Array.count_pos_iff.mp` with `omega`. -/
lemma mem_of_count_one {α : Type} [DecidableEq α] (a : Array α) (x : α) (h : Array.count x a = 1) :
    x ∈ a := by
  have hpos : 0 < Array.count x a := by omega
  exact (Array.count_pos_iff.mp hpos)

/-- If `List.count x as.toList > 0`, then `x ∈ as`.
This bridges `List.count` positivity on the underlying list to `Array` membership,
and is useful when reasoning about counts computed via `List.count` on `toList`. -/
lemma mem_of_toList_count_pos {α : Type} [DecidableEq α] (as : Array α) (x : α)
    (hpos : 0 < List.count x as.toList) : x ∈ as := by
  have h : x ∈ as.toList := ((List.count_pos_iff (a := x) (l := as.toList)).mp hpos)
  rw [← Array.mem_toList]
  exact h


end Array

namespace Array

/-! # Prefix and suffix sum of arrays

This module defines operations for computing the sum of elements in
prefixes and suffixes of an array, with respect to an index.

These are used in problems that require comparing sums on the left
and right of a pivot index (e.g., LeetCode 724 "Find Pivot Index").
-/

/-- Sum of elements before index `i` (exclusive): `nums[0] + ... + nums[i-1]`.
Returns `0` when `i = 0`. Uses `Array.toList` to avoid requiring `Inhabited α`. -/
def sumLeft (nums : Array α) (i : Nat) [AddMonoid α] : α :=
  ((Array.toList nums).take i).foldl (fun acc x => acc + x) 0

/-- Sum of elements after index `i` (exclusive): `nums[i+1] + ... + nums[n-1]`.
Returns `0` when `i ≥ nums.size - 1`. Uses `Array.toList` to avoid requiring `Inhabited α`. -/
def sumRight (nums : Array α) (i : Nat) [AddMonoid α] : α :=
  ((Array.toList nums).drop (i+1)).foldl (fun acc x => acc + x) 0

lemma sumLeft_zero (nums : Array α) [AddMonoid α] : sumLeft nums 0 = 0 := by
  simp [sumLeft]

lemma sumRight_nil (i : Nat) [AddMonoid α] : sumRight (#[] : Array α) i = 0 := by
  simp [sumRight]

end Array

namespace Array


/-! ### GCD of all elements -/

/-- Compute the GCD of all elements in an array using `Nat.gcd` with foldl.
The GCD of an empty array is 0 (since `gcd 0 n = n`, this gives the identity value). -/
def gcd (arr : Array Nat) : Nat :=
  arr.foldl Nat.gcd 0

/-- GCD of a contiguous subarray `arr[start..start+len-1]`.
Uses `arr[i]!` (unsafe indexing); callers must ensure `start + len ≤ arr.size`.
Returns `0` when `len = 0` (the identity for `Nat.gcd`). -/
def subarrayGcd (arr : Array Nat) (start len : Nat) : Nat :=
  (List.range len).foldl (fun acc k => Nat.gcd acc (arr[start + k]!)) 0

/-- GCD of a contiguous subarray `arr[lo..hi]` (inclusive).
Convenience wrapper around `subarrayGcd` taking inclusive bounds.
When `hi < lo`, the result is `arr[lo]!` (since `hi - lo` underflows to `0`
and `subarrayGcd arr lo 1 = arr[lo]!`). -/
def rangeGcd (arr : Array Nat) (lo hi : Nat) : Nat :=
  subarrayGcd arr lo (hi - lo + 1)


end Array


namespace Array

/-! ### Pairwise index distances between occurrences of values -/

/-- Compute the set of all pairwise absolute distances between indices `i`, `j` in `arr`
    where `arr[i]` equals `x` and `arr[j]` equals `y`. -/
def pairwiseIdxDistances {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (x y : α) : Finset Nat :=
  let idxs := Finset.range arr.size
  Finset.image (λ (p : Nat × Nat) => Nat.dist p.1 p.2)
    (Finset.filter (λ (p : Nat × Nat) =>
      arr[p.1]! = x ∧ arr[p.2]! = y)
      (Finset.product idxs idxs))

lemma pairwiseIdxDistances_spec {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (x y : α) (d : Nat) :
    d ∈ pairwiseIdxDistances arr x y ↔
    ∃ i j, (i < arr.size ∧ j < arr.size ∧ arr[i]! = x ∧ arr[j]! = y) ∧ d = Nat.dist i j := by
  unfold pairwiseIdxDistances
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨i, j⟩, hmem, hd⟩
    rcases Finset.mem_filter.mp hmem with ⟨hmem_prod, ⟨hwi, hwj⟩⟩
    rcases Finset.mem_product.mp hmem_prod with ⟨hi_mem, hj_mem⟩
    have hi : i < arr.size := Finset.mem_range.mp hi_mem
    have hj : j < arr.size := Finset.mem_range.mp hj_mem
    refine ⟨i, j, ⟨hi, hj, hwi, hwj⟩, hd.symm⟩
  · intro h
    rcases h with ⟨i, j, ⟨hi, hj, hwi, hwj⟩, hd⟩
    subst hd
    apply Finset.mem_image.mpr
    refine ⟨(i, j), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩,
      And.intro hwi hwj⟩

/-! ### Counting equal pairs in subarrays -/

/-- Count unordered pairs `(i, j)` with `l ≤ i < j < r` such that `arr[i]! = arr[j]!`.
This is the number of "equal-element pairs" in the subarray `arr[l..r)`.
Uses `!`-indexing; callers must ensure `r ≤ arr.size` for meaningful results
(out-of-bounds indices return `default`, which may accidentally equal in-bounds values). -/
def countEqualPairsInRange {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (l r : Nat) : Nat :=
  (((Finset.range r).product (Finset.range r)).filter
    (fun p : Nat × Nat =>
      l ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < r ∧ arr[p.1]! = arr[p.2]!)).card

/-- Count subarrays `[l, r)` of `arr` that contain at least `k` equal-element pairs.
That is, the number of index pairs `(l, r)` with `0 ≤ l < r ≤ arr.size` such that
`countEqualPairsInRange arr l r ≥ k`. -/
def countSubarraysWithThreshold {α : Type} [DecidableEq α] [Inhabited α] (arr : Array α) (k : Nat) : Nat :=
  let n := arr.size
  (((Finset.range n).product (Finset.range (n + 1))).filter
    (fun lr : Nat × Nat => lr.1 < lr.2 ∧ k ≤ countEqualPairsInRange arr lr.1 lr.2)).card

/-! ### Count subarrays satisfying an index predicate -/

/-- Count all contiguous subarray index pairs `(i, j)` with `0 ≤ i ≤ j < arr.size`
where the predicate `p i j` holds.

This is the Array counterpart of `List.countSubarraysWhereIdx`.
For example, to count subarrays whose sum equals `k`, use:
`countSubarraysWhere arr (fun i j => Array.subSum arr i j = k)`. -/
def countSubarraysWhere (arr : Array α) (p : Nat → Nat → Bool) : Nat :=
  let n := arr.size
  (List.range n).foldl
    (fun acc i =>
      acc + (List.range (n - i)).foldl
        (fun acc' offset =>
          let j := i + offset
          if p i j then acc' + 1 else acc')
        0)
    0

/-- Unfold lemma for `countSubarraysWhere`. Expands the definition for rewriting. -/
lemma countSubarraysWhere_eq (arr : Array α) (p : Nat → Nat → Bool) :
    countSubarraysWhere arr p =
    (List.range arr.size).foldl
      (fun acc i =>
        acc + (List.range (arr.size - i)).foldl
          (fun acc' offset => if p i (i + offset) then acc' + 1 else acc')
          0)
      0 := rfl

/-- `countSubarraysWhere` on an empty array returns `0`. -/
lemma countSubarraysWhere_empty {α : Type} (p : Nat → Nat → Bool) :
    countSubarraysWhere (#[] : Array α) p = 0 := by
  simp [countSubarraysWhere]

end Array

