import Mathlib
import general.List.Membership
import general.List.Sequences
import general.List.Pairs

namespace List

/-! ### Strict monotonicity of a list -/

/-- A list is strictly monotone (strictly increasing) if adjacent elements satisfy `<`.
Uses `List.Pairwise` which checks the relation for every adjacent pair.
For `Nat` and `Int`, this means each element is strictly less than the next. -/
def StrictMono (l : List α) [LT α] : Prop :=
  l.Pairwise (· < ·)

/-! ### Strictly increasing / decreasing list predicates

Both `Bool`-valued (for computation) and `Prop`-valued (for specification) predicates
that a list is strictly increasing or strictly decreasing. The `Bool` versions use
`decide` for decidability. The `spec` lemmas connect the `Bool` and `Prop` versions. -/

/-- List is strictly increasing (as `Bool`). Generalised to any type with a decidable `<` relation. -/
def strictlyIncreasingBool {α : Type} [LT α] [∀ a b : α, Decidable (a < b)] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => decide (x < y) && strictlyIncreasingBool (y :: xs)

/-- List is strictly decreasing (as `Bool`). Generalised to any type with a decidable `<` relation. -/
def strictlyDecreasingBool {α : Type} [LT α] [∀ a b : α, Decidable (a < b)] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => decide (x > y) && strictlyDecreasingBool (y :: xs)

/-- Strictly increasing list (as `Prop`). Generalised to any type with a `<` relation. -/
def StrictlyIncreasing {α : Type} [LT α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => (x < y) ∧ StrictlyIncreasing (y :: xs)

/-- Strictly decreasing list (as `Prop`). Generalised to any type with a `<` relation. -/
def StrictlyDecreasing {α : Type} [LT α] : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => (x > y) ∧ StrictlyDecreasing (y :: xs)

lemma strictlyIncreasingBool_spec {α : Type} [LT α] [∀ a b : α, Decidable (a < b)] (l : List α) :
    strictlyIncreasingBool l = true ↔ StrictlyIncreasing l := by
  induction l with
  | nil => simp [strictlyIncreasingBool, StrictlyIncreasing]
  | cons x xs ih =>
    cases xs with
    | nil => simp [strictlyIncreasingBool, StrictlyIncreasing]
    | cons y ys =>
      simp [strictlyIncreasingBool, StrictlyIncreasing, decide_eq_true_iff,
        Bool.and_eq_true_eq_eq_true_and_eq_true, ih]

lemma strictlyDecreasingBool_spec {α : Type} [LT α] [∀ a b : α, Decidable (a < b)] (l : List α) :
    strictlyDecreasingBool l = true ↔ StrictlyDecreasing l := by
  induction l with
  | nil => simp [strictlyDecreasingBool, StrictlyDecreasing]
  | cons x xs ih =>
    cases xs with
    | nil => simp [strictlyDecreasingBool, StrictlyDecreasing]
    | cons y ys =>
      simp [strictlyDecreasingBool, StrictlyDecreasing, decide_eq_true_iff,
        Bool.and_eq_true_eq_eq_true_and_eq_true, ih]

/-! ### `uniqueSorted` — sorted and deduplicated list -/

/-- Produce a sorted, deduplicated list from `l` using the comparison function `r`
(which returns `true` when its first argument should precede its second).
Equivalent to `(l.dedup).mergeSort r`. -/
def uniqueSorted {α : Type _} [DecidableEq α] (r : α → α → Bool) (l : List α) : List α :=
  (l.dedup).mergeSort r

/-- `uniqueSorted r l` has no duplicates. -/
lemma nodup_uniqueSorted {α : Type _} [DecidableEq α] (r : α → α → Bool) (l : List α) :
    List.Nodup (uniqueSorted r l) := by
  rw [uniqueSorted, List.nodup_mergeSort]
  exact List.nodup_dedup l

/-- `uniqueSorted r l` contains exactly the distinct elements of `l`:
`a ∈ uniqueSorted r l` iff `a ∈ l`. -/
lemma mem_uniqueSorted_iff {α : Type _} [DecidableEq α] (r : α → α → Bool) (l : List α) (a : α) :
    a ∈ uniqueSorted r l ↔ a ∈ l := by
  simp [uniqueSorted, List.mem_dedup]

/-! ### `sortedDedup` — sort into ascending order and remove duplicates -/

/-- Sort a list into ascending order and remove duplicates.
This is a convenience wrapper around `(l.dedup).mergeSort (fun a b => decide (a ≤ b))`,
equivalent to `uniqueSorted (fun a b => decide (a ≤ b)) l`. -/
def sortedDedup {α : Type} [LinearOrder α] (l : List α) : List α :=
  l.dedup.mergeSort (fun a b => decide (a ≤ b))

/-- `sortedDedup l` is sorted in ascending order. -/
lemma sortedDedup_sorted {α : Type} [LinearOrder α] (l : List α) :
    List.Sorted (· ≤ ·) (sortedDedup l) := by
  simp [sortedDedup, List.sorted_mergeSort']

/-- `sortedDedup l` has no duplicate elements. -/
lemma sortedDedup_nodup {α : Type} [LinearOrder α] (l : List α) : List.Nodup (sortedDedup l) := by
  rw [sortedDedup, List.nodup_mergeSort]
  exact List.nodup_dedup l

/-- `a ∈ sortedDedup l` iff `a ∈ l`. -/
lemma mem_sortedDedup_iff {α : Type} [LinearOrder α] (l : List α) (a : α) :
    a ∈ sortedDedup l ↔ a ∈ l := by
  simp [sortedDedup, List.mem_dedup]

/-- `sortedDedup` equals `uniqueSorted` with the standard `≤` comparator. -/
lemma sortedDedup_eq_uniqueSorted {α : Type} [LinearOrder α] (l : List α) :
    sortedDedup l = uniqueSorted (fun a b => decide (a ≤ b)) l := rfl

/-! ### `dedup` with `take` -/

/-- Taking the first `n` elements of the deduplicated list yields a nodup list. -/
lemma nodup_dedup_take {α : Type} [DecidableEq α] (l : List α) (n : Nat) :
    (l.dedup.take n).Nodup :=
  (List.nodup_dedup l).sublist (List.take_sublist _ _)

/-- If `a` belongs to the first `n` distinct elements of `l`, then `a ∈ l`. -/
lemma mem_of_mem_dedup_take {α : Type} [DecidableEq α] (l : List α) (n : Nat) (a : α)
    (h : a ∈ l.dedup.take n) : a ∈ l :=
  List.mem_dedup.mp (List.mem_of_mem_take h)

/-- The length of `l.dedup.take n` is at most `n`. -/
lemma length_dedup_take_le {α : Type} [DecidableEq α] (l : List α) (n : Nat) :
    (l.dedup.take n).length ≤ n := by
  rw [List.length_take]
  exact inf_le_left

end List

namespace List

/-! # Non-decreasing list predicate (boolean version)

This module provides a computable test for whether a list is sorted in
non-decreasing order (each element is ≤ the next), and connects it to the
`List.Pairwise` propositional version.
-/

/-- Boolean check: is a list non-decreasing (each element ≤ the next)?
Uses `zip` with `drop 1` to compare adjacent elements pairwise. -/
def isNonDecreasingB {α : Type} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (l : List α) : Bool :=
  (l.zip (l.drop 1)).all (fun p => p.1 ≤ p.2)

/-- If a list is `Pairwise (· ≤ ·)`, then `isNonDecreasingB` returns `true`.
This connects the propositional pairwise ordering to the boolean test. -/
lemma pairwise_le_implies_isNonDecreasingB {α : Type} [LE α] [DecidableEq α]
    [DecidableRel ((· ≤ ·) : α → α → Prop)] (l : List α) (h : List.Pairwise (· ≤ ·) l) :
    isNonDecreasingB l = true := by
  induction' l with x l ih
  · simp [isNonDecreasingB]
  · cases' l with y rest
    · simp [isNonDecreasingB]
    · cases h with
      | cons h_head h_tail =>
        have hxy : x ≤ y := h_head y (by simp)
        have ih' : isNonDecreasingB (y :: rest) = true := ih h_tail
        have ih'_prop : ∀ p ∈ (y :: rest).zip rest, p.1 ≤ p.2 := by
          unfold isNonDecreasingB at ih'
          have h_drop' : (y :: rest).drop 1 = rest := by simp
          rw [h_drop'] at ih'
          rw [List.all_eq_true] at ih'
          simpa using ih'
        unfold isNonDecreasingB
        simp
        exact And.intro hxy (fun a b hab => ih'_prop (a, b) hab)

/-! ### `sortedLeBool` — pattern-matching boolean sorted check

This is an alternative to `isNonDecreasingB` (zip-based) and `sortedB` (`decide`-based).
The pattern-matching definition is convenient for structural induction proofs.
Generalized to any ordered type with decidable `≤`. -/

/-- Boolean check: is a list sorted in non-decreasing order (each element ≤ the next)?
Uses pattern matching for direct structural induction. -/
def sortedLeBool [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: rs => decide (x ≤ y) && sortedLeBool (y :: rs)

/-- If every element of `l` is ≤ `x` and `l` is sorted, then appending `[x]` preserves sortedness. -/
lemma sortedLeBool_append_singleton (l : List Nat) (x : Nat)
    (h : sortedLeBool l = true) (h_bound : ∀ y ∈ l, y ≤ x) :
    sortedLeBool (l ++ [x]) = true := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    cases ys with
    | nil =>
      have hyx : y ≤ x := h_bound y (by simp)
      have hdec : decide (y ≤ x) = true := by
        rw [decide_eq_true_iff]; exact hyx
      simp [sortedLeBool, hdec]
    | cons z zs =>
      have h_sorted_yz_zs : sortedLeBool (y :: z :: zs) = true := h
      unfold sortedLeBool at h_sorted_yz_zs
      have hyz_hzs := Bool.and_eq_true_iff.mp h_sorted_yz_zs
      rcases hyz_hzs with ⟨hyz, hzs_sorted⟩
      have h_bound_zs : ∀ w ∈ (z :: zs), w ≤ x := by
        intro w hw
        apply h_bound w
        exact List.mem_cons_of_mem y hw
      have ih_res : sortedLeBool ((z :: zs) ++ [x]) = true := ih hzs_sorted h_bound_zs
      have h_eq : ((z :: zs) ++ [x]) = (z :: (zs ++ [x])) := rfl
      rw [h_eq] at ih_res
      dsimp [sortedLeBool]
      rw [hyz, ih_res]
      rfl

/-- `List.range n` is sorted according to `sortedLeBool`. -/
lemma sortedLeBool_range (n : Nat) : sortedLeBool (List.range n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ]
    apply sortedLeBool_append_singleton (List.range n) n ih
    intro y hy
    have hy_range : y < n := List.mem_range.mp hy
    omega

/-- If `sortedLeBool (y :: ys) = true`, then every element of `ys` is ≥ `y`. -/
lemma sortedLeBool_implies_ge_first (y : Nat) (ys : List Nat) (h : sortedLeBool (y :: ys) = true) :
    ∀ z ∈ ys, y ≤ z := by
  induction ys generalizing y with
  | nil => intro z hz; exfalso; exact List.not_mem_nil z hz
  | cons z zs ih =>
    intro w hw
    unfold sortedLeBool at h
    have hand := Bool.and_eq_true_iff.mp h
    rcases hand with ⟨hyz, hzs⟩
    rcases List.mem_cons.mp hw with (rfl | hw')
    · rw [decide_eq_true_iff] at hyz; exact hyz
    · have hyz_val : y ≤ z := by
        rw [decide_eq_true_iff] at hyz; exact hyz
      have hz_le_w : z ≤ w := ih z hzs w hw'
      exact Nat.le_trans hyz_val hz_le_w

/-- Prepending `x` to a sorted list `l` preserves sortedness provided `x ≤` every element of `l`. -/
lemma sortedLeBool_cons_of_sortedLeBool_and_le (x : Nat) (l : List Nat)
    (h_sorted_l : sortedLeBool l = true) (h_le : ∀ z ∈ l, x ≤ z) :
    sortedLeBool (x :: l) = true := by
  cases l with
  | nil => rfl
  | cons z zs =>
    have hxz : x ≤ z := h_le z (by simp)
    have hxz_dec : decide (x ≤ z) = true := by
      rw [decide_eq_true_iff]; exact hxz
    simp [sortedLeBool, hxz_dec, h_sorted_l]

/-- Filtering a sorted list preserves sortedness. -/
lemma sortedLeBool_filter (l : List Nat) (p : Nat → Bool) (h : sortedLeBool l = true) :
    sortedLeBool (l.filter p) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      by_cases hpx : p x
      · simp [hpx, sortedLeBool]
      · simp [hpx, sortedLeBool]
    | cons y ys =>
      unfold sortedLeBool at h
      have hand := Bool.and_eq_true_iff.mp h
      rcases hand with ⟨hxy, hys⟩
      have hxy_val : x ≤ y := by
        rw [decide_eq_true_iff] at hxy; exact hxy
      by_cases hpx : p x
      · simp [hpx]
        have ih_ys : sortedLeBool ((y :: ys).filter p) = true := ih hys
        apply sortedLeBool_cons_of_sortedLeBool_and_le x ((y :: ys).filter p) ih_ys
        intro z hz
        have hz_mem : z ∈ (y :: ys) := List.mem_of_mem_filter hz
        rcases List.mem_cons.mp hz_mem with (rfl | hz_ys)
        · exact hxy_val
        · have hy_le_z : y ≤ z := sortedLeBool_implies_ge_first y ys hys z hz_ys
          exact Nat.le_trans hxy_val hy_le_z
      · simp [hpx]
        exact ih hys

/-! ### Append properties of `Pairwise (· ≤ ·)` lists

When a non-decreasing list is split as `as ++ x :: bs`, elements in `as` are
strictly less than `x` and elements in `bs` are strictly greater than `x`, provided
the combined list has no duplicates. These lemmas are useful for binary search
and sorted insertion proofs. -/

/-- In a list `as ++ x :: bs` that is `Pairwise (· ≤ ·)` and `Nodup`,
every element of `as` is strictly less than `x`. -/
lemma all_lt_of_append_pairwise_le {α : Type _} [LinearOrder α] [DecidableEq α]
    (as bs : List α) (x : α)
    (hpairwise : List.Pairwise (· ≤ ·) (as ++ x :: bs))
    (hnodup : (as ++ x :: bs).Nodup) :
    ∀ a ∈ as, a < x := by
  rcases List.pairwise_append.mp hpairwise with ⟨_, _, h_cross⟩
  rcases List.pairwise_append.mp hnodup with ⟨_, _, h_cross_ne⟩
  intro a ha
  have hle : a ≤ x := h_cross a ha x (by simp)
  have hne : a ≠ x := h_cross_ne a ha x (by simp)
  exact lt_of_le_of_ne hle hne

/-- In a list `as ++ x :: bs` that is `Pairwise (· ≤ ·)` and `Nodup`,
every element of `bs` is strictly greater than `x`. -/
lemma all_gt_of_append_pairwise_le {α : Type _} [LinearOrder α] [DecidableEq α]
    (as bs : List α) (x : α)
    (hpairwise : List.Pairwise (· ≤ ·) (as ++ x :: bs))
    (hnodup : (as ++ x :: bs).Nodup) :
    ∀ b ∈ bs, x < b := by
  rcases List.pairwise_append.mp hpairwise with ⟨_, h_rest_pairwise, _⟩
  rcases List.pairwise_append.mp hnodup with ⟨_, h_rest_nodup, _⟩
  cases h_rest_pairwise with
  | cons hx_le_all _ =>
    cases h_rest_nodup with
    | cons hx_ne_all _ =>
      intro b hb
      have hle : x ≤ b := hx_le_all b hb
      have hne : x ≠ b := hx_ne_all b hb
      exact lt_of_le_of_ne hle hne

/-! ### Equivalence with `List.Pairwise` -/

/-- `sortedLeBool l = true` iff `l` is pairwise non-decreasing (`List.Pairwise (· ≤ ·) l`).
This connects the boolean decidable test to the propositional pairwise ordering. -/
lemma sortedLeBool_eq_true_iff [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (l : List α) :
    sortedLeBool l = true ↔ List.Pairwise (· ≤ ·) l := by
  constructor
  · intro h
    induction l with
    | nil => exact List.Pairwise.nil
    | cons a l ih =>
      cases l with
      | nil => exact List.pairwise_singleton _ _
      | cons b l =>
        unfold sortedLeBool at h
        simp at h
        rcases h with ⟨hab, hrest⟩
        have hpair_rest : List.Pairwise (· ≤ ·) (b :: l) := ih hrest
        rcases (List.pairwise_cons.mp hpair_rest) with ⟨h_rest_forall, h_rest_pair⟩
        have h_forall : ∀ a' ∈ (b :: l), a ≤ a' := by
          intro a' ha'
          cases ha' with
          | head l => exact hab
          | tail _ ha'l =>
            have hba' : b ≤ a' := h_rest_forall a' ha'l
            exact le_trans hab hba'
        exact List.Pairwise.cons h_forall hpair_rest
  · intro h
    induction l with
    | nil => rfl
    | cons a l ih =>
      rcases (List.pairwise_cons.mp h) with ⟨h_forall, h_pair⟩
      cases l with
      | nil => rfl
      | cons b l =>
        have hab : a ≤ b := h_forall b (by simp)
        have hrest : sortedLeBool (b :: l) = true := ih h_pair
        unfold sortedLeBool
        simp [hab, hrest]

end List

namespace List

/-! ### Counting position-wise differences between two lists -/

/-- `count_diffs l1 l2` counts the number of corresponding positions where `l1` and `l2` differ.
Returns `0` for lists of unequal length (the mismatch tail is ignored). -/
def count_diffs [DecidableEq α] (l1 l2 : List α) : Nat :=
  match l1, l2 with
  | [], [] => 0
  | c1 :: t1, c2 :: t2 => (if c1 = c2 then 0 else 1) + count_diffs t1 t2
  | _, _ => 0

/-- A list has zero differences with itself. -/

lemma count_diffs_self [DecidableEq α] (l : List α) : count_diffs l l = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    unfold count_diffs
    simp [ih]

/-! ### `differs_at_most` — lists differ in at most `n` positions -/

/-- `differs_at_most n l1 l2` iff `l1` and `l2` have the same length and differ
in at most `n` positions (as measured by `count_diffs`). -/
def differs_at_most [DecidableEq α] (n : Nat) (l1 l2 : List α) : Prop :=
  (length l1 = length l2) ∧ count_diffs l1 l2 ≤ n

/-- A list differs from itself in at most `n` positions, for any `n`. -/
lemma differs_at_most_self [DecidableEq α] {n : Nat} (l : List α) : differs_at_most n l l := by
  unfold differs_at_most
  have h := count_diffs_self l
  exact And.intro rfl (by rw [h]; exact Nat.zero_le n)

/-! ### Checking if two lists differ by exactly one element -/

/-- `differ_by_one l1 l2` is true iff `l1` and `l2` have the same length and differ
in exactly one position. -/
def differ_by_one [DecidableEq α] (l1 l2 : List α) : Bool :=
  l1.length == l2.length && count_diffs l1 l2 == 1

/-- A list does not differ from itself by one element. -/

lemma differ_by_one_self [DecidableEq α] (l : List α) : differ_by_one l l = false := by
  unfold differ_by_one
  simp [count_diffs_self l]

/-! ### Lexicographic comparison -/

/-- Compare two lists lexicographically using the `<` relation from a `LinearOrder`.
    Returns `true` iff the first list is strictly smaller than the second list. -/
def ltList [LinearOrder α] : List α → List α → Bool
| [], [] => false
| [], _::_ => true
| _::_, [] => false
| c₁ :: t₁, c₂ :: t₂ =>
    if c₁ = c₂ then
      ltList t₁ t₂
    else
      decide (c₁ < c₂)

end List

namespace List


/-! ### Counting ordered pairs satisfying a predicate -/

/-- Count all ordered pairs `(i, j)` with `i < j` in the list `xs` where the boolean predicate `p`
holds on the `i`-th and `j`-th elements. The index-based formulation avoids needing
a `DecidableEq` on `α`.

For example:
* `countOrderedPairs (fun a b => a == b) [1, 2, 1] = 0` (no equal pairs with i < j)
* `countOrderedPairs (fun a b => a < b) [1, 3, 2] = 2` ((1,3) and (1,2) at indices (0,1) and (0,2))
* `countOrderedPairs (fun a b => a < b) [3, 1, 2] = 1` (only (1,2) at index pair (1,2)) -/
def countOrderedPairs {α : Type} [Inhabited α] (p : α → α → Bool) (xs : List α) : Nat :=
  let n := xs.length
  (List.range n).foldl (fun acc i =>
    acc + ((List.range n).filter (fun j =>
      i < j ∧ p (xs[i]?.iget) (xs[j]?.iget))).length) 0

/-! ### Pair sorting: first component ascending, second descending on ties -/

/-- Comparator for `α × β`: sort by first component ascending,
    and for equal first components, by second component descending.
    Useful for interval problems where longer intervals (greater second component)
    should come first when start times are the same. -/
def pairCmpFstAscSndDesc {α β : Type} [LinearOrder α] [LinearOrder β] (a b : α × β) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else b.2 ≤ a.2

/-- Sort a list of pairs by first component ascending;
    ties are broken by second component descending.
    This is a common preprocessing step in interval covering / greedy scheduling problems. -/
def sortPairsFstAsc {α β : Type} [LinearOrder α] [LinearOrder β] (pairs : List (α × β)) : List (α × β) :=
  List.mergeSort pairs pairCmpFstAscSndDesc

/-! ### Interval overlap check -/

/-- Check whether all intervals in a list are pairwise non-overlapping.
Two intervals `(a, b)` and `(c, d)` do not overlap if `b < c` or `d < a`.
Self-comparisons are trivially accepted (each interval does not overlap itself). -/
def intervalsNonOverlapping (ints : List (Nat × Nat)) : Bool :=
  ints.all (fun i =>
    ints.all (fun j =>
      i = j || decide (i.2 < j.1) || decide (j.2 < i.1)))


end List

namespace List

/-! ### Lexicographic order lemmas -/

/-- If `l₁` is a prefix of `l₂`, then `l₁ ≤ l₂` in lexicographic order. -/
lemma prefix_le {α : Type} [LinearOrder α] {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₁ ≤ l₂ := by
  rcases h with ⟨t, ht⟩
  subst ht
  induction l₁ with
  | nil =>
    by_cases ht' : t = []
    · subst ht'; rfl
    · have : [] < t := by
        rcases t with _ | ⟨x, xs⟩
        · contradiction
        · exact Lex.nil
      exact le_of_lt this
  | cons a l₁ ih =>
    exact cons_le_cons a ih

/-- Taking a prefix of a list yields a list ≤ the original in lexicographic order. -/
lemma take_le {α : Type} [LinearOrder α] (l : List α) (n : Nat) : l.take n ≤ l :=
  prefix_le (List.take_prefix n l)

/-- Taking the prefix of a drop yields the same drop, when the take length
covers the remaining length: `(l.drop i).take (l.length - i) = l.drop i`. -/
lemma take_drop_eq_drop {α : Type} (l : List α) (i : Nat) :
    (l.drop i).take (l.length - i) = l.drop i := by
  apply List.take_of_length_le
  simp [List.length_drop]

/-- `take (min l.length n) l = take n l`: since `take` safely truncates at the list
length, taking the minimum of length and n is equivalent to just taking n. -/
lemma take_min_length {α : Type} (l : List α) (n : Nat) : l.take (min l.length n) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left (by omega : l.length ≤ n)]
    have hsz : l.length ≤ n := by omega
    simp [List.take_of_length_le hsz]

/-- If `n ≤ l.length`, then `n ≤ (l.take n).length`. This is the inequality-direction
corollary of `List.length_take_of_le`. -/
lemma le_length_take_of_le {α : Type} {l : List α} {n : ℕ} (h : n ≤ l.length) :
    n ≤ (l.take n).length :=
  (List.length_take_of_le h).ge

/-- If `l.drop idx` is maximal among drops before `l.length`, then any drop is ≤ it.
Useful for suffix-comparison problems where a maximal suffix is identified. -/
lemma drop_le_of_drop_max {α : Type} [LinearOrder α] (l : List α) (idx i' : Nat)
    (h_spec : ∀ j < l.length, l.drop j ≤ l.drop idx) : l.drop i' ≤ l.drop idx := by
  by_cases hi'_lt : i' < l.length
  · exact h_spec i' hi'_lt
  · have hi'_ge : l.length ≤ i' := by omega
    have h_drop_nil : l.drop i' = [] := List.drop_eq_nil_of_le hi'_ge
    rw [h_drop_nil]
    cases h : l.drop idx with
    | nil => rfl
    | cons a as => exact le_of_lt List.Lex.nil

/-! ### Drop lemmas -/

/-- If `List.drop i l = []`, then `l.length ≤ i`.
This is the converse of `List.drop_eq_nil_of_le`. -/
lemma length_le_of_drop_eq_nil {α : Type} (l : List α) (i : Nat) (h : List.drop i l = []) :
    l.length ≤ i := by
  by_contra! h_lt
  have h_len_drop : (List.drop i l).length = l.length - i := List.length_drop i l
  have h_pos : 0 < l.length - i := Nat.sub_pos_of_lt h_lt
  rw [← h_len_drop] at h_pos
  rw [h] at h_pos
  simp at h_pos

/-- If `List.drop i l = x :: rest`, then `i < l.length`. -/
lemma length_lt_of_drop_eq_cons {α : Type} (l : List α) (i : Nat) (x : α) (rest : List α)
    (h : List.drop i l = x :: rest) : i < l.length := by
  by_cases h_lt : i < l.length
  · exact h_lt
  · exfalso
    have h_drop_empty : List.drop i l = [] := List.drop_eq_nil_of_le (by omega)
    rw [h_drop_empty] at h
    simp at h

/-- If `List.drop i l = x :: rest`, then `rest = List.drop (i + 1) l`. -/
lemma drop_succ_of_drop_eq_cons {α : Type} (l : List α) (i : Nat) (x : α) (rest : List α)
    (h : List.drop i l = x :: rest) : rest = List.drop (i + 1) l := by
  calc
    rest = (x :: rest).drop 1 := by simp
    _ = (List.drop i l).drop 1 := by rw [h]
    _ = List.drop (i + 1) l := by simp

/-- If `lst.drop pos = y :: ys`, then `lst[pos]? = some y`.
This is the `getElem?` version; see also `getElem!_of_drop_eq_cons` for the inhabited variant. -/
lemma getElem?_of_drop_eq_cons {α : Type} (lst : List α) (pos : Nat) (y : α) (ys : List α)
    (h : lst.drop pos = y :: ys) : lst[pos]? = some y := by
  calc
    lst[pos]? = lst[pos + 0]? := by simp
    _ = (lst.drop pos)[0]? := by rw [List.getElem?_drop lst pos 0]
    _ = some y := by rw [h]; simp

/-- If the dropped suffix is non-empty (has positive length), then `pos` is within bounds. -/
lemma pos_lt_length_of_drop_ne_nil {α : Type} (lst : List α) (pos : Nat)
    (h : (lst.drop pos).length > 0) : pos < lst.length := by
  have h_len_drop : (lst.drop pos).length = lst.length - pos :=
    List.length_drop pos lst
  rw [h_len_drop] at h
  omega

/-- In a non-empty drop, the first element of the drop equals the element at the drop index:
`(l.drop i)[0]! = l[i]!` when `i < l.length`. -/
lemma getElem_drop_zero_eq_getElem {α : Type} [Inhabited α] (l : List α) (i : Nat) (hi : i < l.length) :
    (l.drop i)[0]! = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  simp [hi]

/-- If `l.drop pos = x :: xs` and `pos < l.length`, then the element at `pos` is `x`.
That is, dropping `pos` elements from `l` yields a list starting with `x`, so `l[pos]! = x`. -/
lemma getElem!_of_drop_eq_cons {α : Type u} [Inhabited α] {l : List α} {pos : Nat} {x : α} {xs : List α}
    (h_drop : l.drop pos = x :: xs) (h_pos_len : pos < l.length) : l[pos]! = x := by
  have h_opt : l[pos]? = some x :=
    calc
      l[pos]? = (l.drop pos)[0]? := by
        simpa using (List.getElem?_drop l pos 0).symm
      _ = (x :: xs)[0]? := by rw [h_drop]
      _ = some x := by simp
  have h_elem : l[pos] = x := by
    have hsome := List.getElem?_eq_getElem h_pos_len
    rw [hsome] at h_opt
    simpa using h_opt
  rw [getElem!_eq_getElem_of_lt h_pos_len, h_elem]

end List
