import Mathlib

open List

/-! ### Sortedness lemmas

Lemmas about `List.Pairwise`, `List.Sorted`, and related sortedness properties.
-/

namespace List

/-- If `l` is pairwise ordered by `decide (f a ≤ f b) = true`, then for any `i < j`
with both indices in bounds, `f (l[i]) ≤ f (l[j])`.

This bridges from a `Bool`-valued `Pairwise` condition (common when sorting with
`mergeSort` using a `decide`-based comparator) to a `Prop`-valued comparison on the
projected values. -/
lemma pairwise_f_le_getElem {β α : Type} [LinearOrder α] (f : β → α) (l : List β)
    (h : l.Pairwise (fun a b => decide (f a ≤ f b) = true))
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) : f (l[i]) ≤ f (l[j]) :=
  have h_pw := (List.pairwise_iff_getElem.mp h) i j hi hj hij
  of_decide_eq_true h_pw

/-- Decompose a `Sorted` cons: if `a :: as` is sorted by `R`, then `R a b` holds for
every `b ∈ as`, and `as` itself is sorted by `R`. -/
lemma sorted_cons_imp {α : Type} {R : α → α → Prop} (a : α) (as : List α) (h : Sorted R (a :: as)) :
    (∀ b ∈ as, R a b) ∧ Sorted R as := by
  simpa using h

/-- In a descending-sorted (`≥`) list `x :: y :: z :: rest`, any element `v` that is
strictly greater than `z` must be either `x` or `y`. This follows because all elements
in `rest` are `≤ z` by sortedness.

This lemma is useful when the first three elements of a descending-sorted list have
been peeled off and you need to characterize what elements can exceed the third. -/
lemma mem_eq_x_or_y_of_gt_z {α : Type} [LinearOrder α] {x y z : α} {rest : List α}
    (h_sorted : List.Sorted (· ≥ ·) (x :: y :: z :: rest))
    (v : α) (hv : v ∈ (x :: y :: z :: rest)) (hv_gt_z : v > z) : v = x ∨ v = y := by
  simp at hv
  rcases hv with (hv|hv|hv|hv)
  · left; exact hv
  · right; exact hv
  · exfalso; exact lt_irrefl z (hv ▸ hv_gt_z)
  · have hz_ge_v : z ≥ v :=
      List.rel_of_sorted_cons (h_sorted.of_cons.of_cons) v hv
    exfalso; exact not_lt.mpr hz_ge_v hv_gt_z

/-- In a list sorted by `≤`, for any indices `i ≤ j` with `j` in bounds,
`L[i]! ≤ L[j]!`. This bridges mathlib's `Sorted.rel_get_of_le` (which works with
`List.get` and `Fin` indices) to `getElem!`-based total access, which is the
convention used across general for index-based reasoning. -/
lemma sorted_getElem!_le {α : Type} [Inhabited α] [Preorder α] {L : List α}
    (h_sorted : List.Sorted (· ≤ ·) L) (i j : Nat) (h_i_le_j : i ≤ j) (h_j_lt : j < L.length) :
    L[i]! ≤ L[j]! := by
  have hi_lt : i < L.length := by omega
  have h_fin_le : (⟨i, hi_lt⟩ : Fin L.length) ≤ (⟨j, h_j_lt⟩ : Fin L.length) := by
    simpa using h_i_le_j
  have h_res : (L.get ⟨i, hi_lt⟩) ≤ (L.get ⟨j, h_j_lt⟩) :=
    h_sorted.rel_get_of_le h_fin_le
  have h_get_i : L.get ⟨i, hi_lt⟩ = L[i]! := by
    simp [List.getElem?_eq_getElem hi_lt]
  have h_get_j : L.get ⟨j, h_j_lt⟩ = L[j]! := by
    simp [List.getElem?_eq_getElem h_j_lt]
  rw [h_get_i, h_get_j] at h_res
  exact h_res

/-! ### `chain_decide` — decidable non-decreasing adjacent-pair check

`chain_decide` is a `Bool`-valued predicate that checks whether every adjacent pair
in a list satisfies `a ≤ b`. It returns `true` for empty and singleton lists (vacuously),
and for `x :: y :: xs`, checks `decide (x ≤ y) && chain_decide (y :: xs)`.

This is the `decide`-based computational counterpart of `List.Chain' (· ≤ ·)`. -/

/-- Decidable check that every adjacent pair in the list satisfies `a ≤ b`.
Returns `true` for `[]` and singleton lists. For `x :: y :: xs`, checks
`decide (x ≤ y) && chain_decide (y :: xs)`.

This is equivalent to `allAdjacentPairs_specificDuplicate (fun a b => decide (a ≤ b)) xs` (see `allAdjacentPairs_specificDuplicate`
in `general.List`). -/
def chain_decide {α : Type} [LE α] [DecidableLE α] : List α → Bool
  | [] => true
  | _ :: [] => true
  | x :: y :: xs => decide (x ≤ y) && chain_decide (y :: xs)

end List

/-! ### Sorting pairs by the second component

`sortBySndDesc` sorts a list of pairs (`α × β`) by the second component in
descending order. This is a convenience wrapper around `List.mergeSort` with a
`decide`-based comparator on the second projection.

This pattern is common in competitive programming when elements have associated
values (e.g., indices paired with scores/weights) and need to be processed in
descending order of those values.
-/

namespace List

/-- Sort a list of pairs by the second component in descending order.
Equivalent to `l.mergeSort (λ a b => decide (a.2 ≥ b.2))`. -/
def sortBySndDesc {α β : Type} [LinearOrder β] (l : List (α × β)) : List (α × β) :=
  l.mergeSort (λ a b => decide (a.2 ≥ b.2))

/-- Sort a list of pairs by the second component in non-decreasing order using `insertionSort`.
Equivalent to `l.insertionSort (λ a b => a.2 ≤ b.2)`.
This is the ascending counterpart of `sortBySndDesc` (which sorts descending with `mergeSort`).
Uses `insertionSort` for stable sorting: pairs with equal second components retain
their relative order from the input list.
Generalized from `sortPairsBySnd` patterns across LeetCode problems (e.g., LC 611). -/
def sortBySnd {α β : Type} [LE β] [DecidableRel (· ≤ · : β → β → Prop)] (l : List (α × β)) : List (α × β) :=
  List.insertionSort (λ a b => a.2 ≤ b.2) l

/-- `sortBySnd l` is a permutation of `l`. -/
lemma sortBySnd_perm {α β : Type} [LE β] [DecidableRel (· ≤ · : β → β → Prop)] (l : List (α × β)) :
    List.Perm (sortBySnd l) l := by
  unfold sortBySnd
  exact List.perm_insertionSort (λ a b => a.2 ≤ b.2) l

/-- Sort a list of pairs by the first component in non-decreasing order.
Equivalent to `l.mergeSort (λ a b => decide (a.1 ≤ b.1))`.

This is the dual of `sortBySndDesc` for the first projection, and the ascending
counterpart. Useful when pairs carry a primary key in the first component
(e.g., `(interval_start, original_index)` pairs sorted by start time). -/
def sortByFst {α β : Type} [LinearOrder α] (l : List (α × β)) : List (α × β) :=
  l.mergeSort (λ a b => decide (a.1 ≤ b.1))

/-- Applying `sortByFst` produces a list that is `Pairwise`-ordered by the first
component via the `decide`-based comparator: for any consecutive `p`, `q` in the result,
`decide (p.1 ≤ q.1) = true`. This follows from `List.sorted_mergeSort` with
transitivity and totality of `≤` on the first projection. -/
lemma sortByFst_sorted {α β : Type} [LinearOrder α] (pairs : List (α × β)) :
    List.Pairwise (fun (p q : α × β) => decide (p.1 ≤ q.1) = true) (sortByFst pairs) := by
  unfold sortByFst
  apply List.sorted_mergeSort
  · intro a b c h_ab h_bc
    simp at h_ab h_bc ⊢
    exact le_trans h_ab h_bc
  · intro a b
    have h := le_total a.1 b.1
    rcases h with (hle | hge)
    · simp [hle]
    · simp [hge]

/-! ### Sorting indices by element values

`sortedIndicesBy xs r` returns the indices of `xs` sorted according to the comparator `r`
on the elements at those indices. It is `mergeSort` of `[0, ..., xs.length-1]` using
`r xs[i]! xs[j]!` as the comparison key.

This pattern is common in competitive programming when you need to rearrange elements
based on a sorting key while keeping track of original positions
(e.g., LeetCode 1968 "Array With Elements Not Equal to Average of Neighbors"). -/

/-- Sort the indices `[0, ..., xs.length-1]` by comparing the elements at those indices
via `r`. The result is a permutation of `List.range xs.length` sorted under the key
`r xs[i]! xs[j]!`. -/
def sortedIndicesBy {α : Type} [Inhabited α] (xs : List α)
    (r : α → α → Prop) [DecidableRel r] : List ℕ :=
  (List.range xs.length).mergeSort (fun i j => decide (r xs[i]! xs[j]!))

/-- `sortedIndicesBy xs r` is a permutation of `List.range xs.length`. -/
lemma sortedIndicesBy_perm_range {α : Type} [Inhabited α] (xs : List α)
    (r : α → α → Prop) [DecidableRel r] :
    sortedIndicesBy xs r ~ List.range xs.length := by
  exact List.mergeSort_perm (List.range xs.length) (fun i j => decide (r xs[i]! xs[j]!))

/-- Every index in `sortedIndicesBy xs r` is less than `xs.length`. -/
lemma sortedIndicesBy_mem_lt {α : Type} [Inhabited α] {xs : List α}
    {r : α → α → Prop} [DecidableRel r] {i : ℕ} (hi : i ∈ sortedIndicesBy xs r) :
    i < xs.length := by
  have hmem : i ∈ List.range xs.length := (sortedIndicesBy_perm_range xs r).subset hi
  simpa using (List.mem_range.mp hmem)

/-- `sortedIndicesBy xs r` is sorted by the comparator `r` on the underlying elements,
provided the comparator is transitive and total on elements at in-bounds indices. -/
lemma sortedIndicesBy_sorted {α : Type} [Inhabited α] (xs : List α)
    (r : α → α → Prop) [DecidableRel r]
    (htrans : ∀ a b c : ℕ, r xs[a]! xs[b]! → r xs[b]! xs[c]! → r xs[a]! xs[c]!)
    (htotal : ∀ a b : ℕ, r xs[a]! xs[b]! ∨ r xs[b]! xs[a]!) :
    (sortedIndicesBy xs r).Sorted (fun i j => r xs[i]! xs[j]!) := by
  have htransBool :
      ∀ a b c : ℕ,
        decide (r xs[a]! xs[b]!) = true →
        decide (r xs[b]! xs[c]!) = true →
        decide (r xs[a]! xs[c]!) = true := by
    intro a b c hab hbc
    exact decide_eq_true (htrans a b c (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have htotalBool :
      ∀ a b : ℕ,
        (decide (r xs[a]! xs[b]!) || decide (r xs[b]! xs[a]!)) = true := by
    intro a b
    rw [Bool.or_eq_true]
    rcases htotal a b with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
  have hsorted := List.sorted_mergeSort htransBool htotalBool (List.range xs.length)
  exact hsorted.imp (fun h => of_decide_eq_true h)

/-! ### Sorted range predicate

`isSortedRange s lo hi` asserts that the sublist `s[lo..hi)` is sorted in non-decreasing
order. This is the `Prop`-valued counterpart of the decidable `chain_decide` (above),
specialized to a consecutive range of indices rather than the entire list.
-/

/-- `isSortedRange s lo hi` means: for all `i, j` with `lo ≤ i < j < hi`, `s[i]! ≤ s[j]!`.
If `lo ≥ hi`, the condition is vacuously true. -/
def isSortedRange {α : Type} [Inhabited α] [LE α] (s : List α) (lo hi : ℕ) : Prop :=
  ∀ (i j : ℕ), lo ≤ i → i < j → j < hi → s[i]! ≤ s[j]!

/-- The consecutive-pair property implies `isSortedRange`: if every adjacent pair in
`[lo, hi)` is non-decreasing, then the entire range is sorted (non-decreasing for all pairs).
Requires transitivity of `≤` (hence `Preorder`). -/
theorem isSortedRange_of_consecutive_le {α : Type} [Inhabited α] [Preorder α]
    (s : List α) (lo hi : ℕ)
    (h : ∀ m, lo ≤ m → m + 1 < hi → s[m]! ≤ s[m+1]!) :
    isSortedRange s lo hi := by
  intro i j hi_lo hi_lt hj_hi
  induction' j with j ih
  · omega
  · have hj_lt_hi : j < hi := by omega
    by_cases hi_eq_j : i = j
    · subst hi_eq_j
      have hi_succ_lt_hi : i + 1 < hi := by omega
      exact h i hi_lo hi_succ_lt_hi
    · have hi_lt_j : i < j := by omega
      have h_ij : s[i]! ≤ s[j]! := ih hi_lt_j hj_lt_hi
      have h_jj1 : s[j]! ≤ s[j+1]! := h j (by omega) (by omega)
      simpa [Nat.succ_eq_add_one] using le_trans h_ij h_jj1

/-! ### `sortByRelation` / `sortedByLe` — sorting by a relation / by `≤`

`sortByRelation r xs` sorts `xs` using merge sort with comparator `r` (a `Prop`-valued
decidable relation). `sortedByLe xs` is the specialization to the `≤` order on any
`LinearOrder α`. These are thin wrappers around `List.mergeSort` that use `decide` to
bridge `Prop` relations to `Bool` comparators. The associated theorems
`sortedByLe_sorted` and `sortedByLe_perm` guarantee that the result is sorted and
is a permutation of the input. -/

/-- Sort a list by a decidable relation `r` using merge sort.
Takes a `Prop`-valued relation and converts it to a `Bool`-valued comparator via `decide`. -/
def sortByRelation {α : Type} (r : α → α → Prop) [DecidableRel r] (xs : List α) : List α :=
  xs.mergeSort (fun a b => decide (r a b))

/-- Sort a list by the `≤` order, using merge sort.
For any `LinearOrder α`, this produces a `≤`-sorted permutation of `xs`. -/
def sortedByLe {α : Type} [LinearOrder α] (xs : List α) : List α :=
  sortByRelation (fun a b : α => a ≤ b) xs

/-- `sortedByLe xs` is a permutation of `xs`. -/
lemma sortedByLe_perm {α : Type} [LinearOrder α] (xs : List α) :
    (sortedByLe xs).Perm xs := by
  simpa [sortedByLe, sortByRelation] using
    (List.mergeSort_perm xs (fun a b : α => decide (a ≤ b)))

/-- `sortedByLe xs` is sorted in non-decreasing (`≤`) order. -/
lemma sortedByLe_sorted {α : Type} [LinearOrder α] (xs : List α) :
    List.Sorted (· ≤ ·) (sortedByLe xs) := by
  simpa [sortedByLe, sortByRelation] using
    (List.sorted_mergeSort' (· ≤ ·) xs)

/-! ### `isSortedBetween` — sortedness on ℤ-bounded intervals with a default value

`isSortedBetween a lo hi defaultValue` asserts that for all integer indices
`i, j` with `lo ≤ i < j < hi`, the elements `a[i']?.getD defaultValue` and
`a[j']?.getD defaultValue` are non-decreasing, where `i' = Int.toNat i`.

This differs from `isSortedRange` (above) in two ways:
1. It uses `ℤ` bounds instead of `ℕ`, which simplifies reasoning about
   negative bounds (they collapse to `0` via `Int.toNat`).
2. It takes an explicit `defaultValue` argument rather than requiring
   `Inhabited α`.
-/

/-- `isSortedBetween a lo hi defaultValue` means: for all `i, j : ℤ` with
`lo ≤ i < j < hi`, `a[Int.toNat i]?.getD defaultValue ≤ a[Int.toNat j]?.getD defaultValue`. -/
def isSortedBetween {α : Type} [LE α] (a : List α) (lo hi : ℤ) (defaultValue : α) : Prop :=
  ∀ (i j : ℤ), lo ≤ i → i < j → j < hi →
    (a[Int.toNat i]?.getD defaultValue) ≤ (a[Int.toNat j]?.getD defaultValue)

/-- If a list `a` is `Sorted` by `≤`, then it is `isSortedBetween` from `0` to its length,
for any default value. -/
theorem isSortedBetween_of_sorted {α : Type} [LinearOrder α] (a : List α)
    (defaultValue : α) (hsort : List.Sorted (· ≤ ·) a) :
    isSortedBetween a 0 (a.length : ℤ) defaultValue := by
  intro i j hi hij hj
  have hi0 : 0 ≤ i := hi
  have hi' : Int.toNat i < a.length := by
    have hival := Int.toNat_of_nonneg hi
    omega
  have hj0 : 0 ≤ j := by omega
  have hj' : Int.toNat j < a.length := by
    have hjval := Int.toNat_of_nonneg hj0
    omega
  have hpair := (List.pairwise_iff_getElem.mp hsort)
    (Int.toNat i) (Int.toNat j) hi' hj' (by omega)
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
  exact hpair

/-! ### `insertSorted_specificDuplicate` — insertion sort building block

`insertSorted_specificDuplicate x s` inserts `x` into the list `s` at the correct position to maintain
sortedness (non-decreasing `≤` order), assuming `s` is already sorted. This is the
single-element insertion step of the insertion sort algorithm.

Unlike mathlib's `List.orderedInsert r a` (which takes an explicit relation parameter),
`insertSorted_specificDuplicate` is specialized to the `≤` order from a `LE` instance, making it more
ergonomic for the common case of sorting by the natural order.

The companion lemma `insertSorted_perm_specificDuplicate` guarantees that insertion produces a permutation
of `x :: s`. -/

/-- Insert `x` into `s` at the position that maintains sortedness (non-decreasing `≤`).
If `x` is `≤` the head of `s`, it becomes the new head; otherwise, we recurse. -/
def insertSorted_specificDuplicate {α : Type u} [LE α] [DecidableRel (· ≤ · : α → α → Prop)] (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted_specificDuplicate x ys

/-- `insertSorted_specificDuplicate x s` is a permutation of `x :: s`. This is the key correctness
property: inserting `x` into `s` produces a list with the same multiset of elements
as `x :: s`. -/
lemma insertSorted_perm_specificDuplicate {α : Type u} [LE α] [DecidableRel (· ≤ · : α → α → Prop)] (x : α) :
    ∀ s : List α, (insertSorted_specificDuplicate x s).Perm (x :: s) := by
  intro s
  induction s with
  | nil => simp [insertSorted_specificDuplicate]
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp [insertSorted_specificDuplicate, hxy]
      · rw [show insertSorted_specificDuplicate x (y :: ys) = y :: insertSorted_specificDuplicate x ys by
          simp [insertSorted_specificDuplicate, hxy]]
        exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

end List
