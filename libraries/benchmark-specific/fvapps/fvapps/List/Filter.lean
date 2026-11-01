import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix

namespace Specific

open _root_.List

namespace List

/-! ## Filter and count operations

Theorems about `filter` with `DecidablePred` (Prop-based predicates), and
the `countWhere` utility that counts elements satisfying a predicate.
-/

/-- Filter returns `[]` iff no element satisfies the predicate.
Variant of `List.filter_eq_nil` for `DecidablePred`. -/
theorem filter_eq_nil_of_forall_not {α : Type u} {p : α → Prop} [DecidablePred p]
    {xs : List α} :
    (∀ x ∈ xs, ¬ p x) → xs.filter p = [] := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      have hx : ¬ p x := h x (by simp)
      have hxs : ∀ y ∈ xs, ¬ p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- Filter returns the whole list iff every element satisfies the predicate.
Variant of `List.filter_eq_self` for `DecidablePred`. -/
theorem filter_eq_self_of_forall {α : Type u} {p : α → Prop} [DecidablePred p]
    {xs : List α} :
    (∀ x ∈ xs, p x) → xs.filter p = xs := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      have hx : p x := h x (by simp)
      have hxs : ∀ y ∈ xs, p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-! ### `countWhere`: count elements satisfying a decidable predicate -/

/-- Count how many elements of a list satisfy a decidable predicate.
Equivalent to `List.countP` but works with `Prop` (via `DecidablePred`)
instead of `Bool`. -/
def countWhere {α : Type u} (p : α → Prop) [DecidablePred p] (xs : List α) : Nat :=
  (xs.filter p).length

/-- `countWhere` unfolds to `(filter p xs).length`. -/
theorem countWhere_eq_filter_length {α : Type u} (p : α → Prop) [DecidablePred p]
    (xs : List α) :
    countWhere p xs = (xs.filter p).length := by
  rfl

/-- Recursive unfolding of `countWhere` on `x :: xs`. -/
@[simp]
theorem countWhere_cons {α : Type u} (p : α → Prop) [DecidablePred p]
    (x : α) (xs : List α) :
    countWhere p (x :: xs) = (if p x then 1 else 0) + countWhere p xs := by
  by_cases h : p x
  · simp [countWhere, h, Nat.add_comm]
  · simp [countWhere, h]

/-- Recursive unfolding of `countWhere` on `[]`. -/
@[simp]
theorem countWhere_nil {α : Type u} (p : α → Prop) [DecidablePred p] :
    countWhere p [] = 0 := by
  simp [countWhere]

/-- The count is at most the length of the list. -/
theorem countWhere_le_length {α : Type u} (p : α → Prop) [DecidablePred p]
    (xs : List α) :
    countWhere p xs ≤ xs.length := by
  unfold countWhere
  exact List.length_filter_le (fun x : α => decide (p x)) xs

/-- The count is always nonnegative. -/
theorem countWhere_nonneg {α : Type u} (p : α → Prop) [DecidablePred p]
    (xs : List α) :
    0 ≤ countWhere p xs := by
  exact Nat.zero_le _

/-- Bounds for `countWhere`: it is between `0` and the list length, inclusive. -/
theorem countWhere_bounds {α : Type u} (p : α → Prop) [DecidablePred p]
    (xs : List α) :
    0 ≤ countWhere p xs ∧ countWhere p xs ≤ xs.length := by
  exact ⟨countWhere_nonneg p xs, countWhere_le_length p xs⟩

/-- If no element satisfies the predicate, the count is zero. -/
theorem countWhere_eq_zero_of_forall_not {α : Type u} {p : α → Prop}
    [DecidablePred p] {xs : List α} :
    (∀ x ∈ xs, ¬ p x) → countWhere p xs = 0 := by
  intro h
  simp [countWhere, filter_eq_nil_of_forall_not h]

/-- If every element satisfies the predicate, the count equals the length. -/
theorem countWhere_eq_length_of_forall {α : Type u} {p : α → Prop}
    [DecidablePred p] {xs : List α} :
    (∀ x ∈ xs, p x) → countWhere p xs = xs.length := by
  intro h
  simp [countWhere, filter_eq_self_of_forall h]

/-- `countWhere` is invariant under list reversal. -/
theorem countWhere_reverse {α : Type u}
    (p : α → Prop) [DecidablePred p] (xs : List α) :
    countWhere p xs.reverse = countWhere p xs := by
  simp [countWhere, List.filter_reverse, List.length_reverse]

/-! ### Filtering replicated lists -/

/-- If `¬ p x`, then filtering `replicate n x` with `p` returns `[]`. -/
theorem filter_replicate_eq_nil_of_not {α : Type u} (n : Nat) (x : α)
    (p : α → Prop) [DecidablePred p] (h : ¬ p x) :
    (List.replicate n x).filter p = [] := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, h, ih]

/-! ### Bool predicate filter lemmas -/

/-- If there exists an element in the list that satisfies the predicate,
then filtering the list produces a non-empty result. -/
theorem filter_ne_nil_of_exists {α : Type} {p : α → Bool}
    {xs : List α} (h : ∃ x, x ∈ xs ∧ p x) : xs.filter p ≠ [] := by
  intro hnil
  rcases h with ⟨x, hmem, hp⟩
  have hxfilter : x ∈ xs.filter p := List.mem_filter.mpr ⟨hmem, hp⟩
  rw [hnil] at hxfilter
  cases hxfilter

/-- `filter p xs ≠ []` iff there exists an element in `xs` satisfying `p`.
This is the bidirectional version, combining `filter_ne_nil_of_exists` with its converse. -/
theorem filter_ne_nil_iff_exists {α : Type} {p : α → Bool} {xs : List α} :
    xs.filter p ≠ [] ↔ ∃ x, x ∈ xs ∧ p x := by
  constructor
  · intro hne
    have := List.exists_mem_of_ne_nil (xs.filter p) hne
    rcases this with ⟨x, hx⟩
    have hmem := List.mem_filter.mp hx
    exact ⟨x, hmem.1, hmem.2⟩
  · exact filter_ne_nil_of_exists

/-- If `p x = true` for all `x ∈ l`, then `l.filter p = l`.
Convenience wrapper around `List.filter_eq_self` using `∀ x ∈ l` syntax. -/
theorem filter_eq_self_of_forall_true {α : Type _} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  rw [List.filter_eq_self]
  exact h

/-- If `p x = false` for all `x ∈ l`, then `l.filter p = []`.
Convenience wrapper around `List.filter_eq_nil_iff` using `∀ x ∈ l` syntax. -/
theorem filter_eq_nil_of_forall_false {α : Type _} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  rw [h x hx]
  simp

/-- `countWhere` distributes over list concatenation. -/
theorem countWhere_append {α : Type u} (p : α → Prop) [DecidablePred p]
    (xs ys : List α) :
    countWhere p (xs ++ ys) = countWhere p xs + countWhere p ys := by
  simp [countWhere]

/-- If `p x` holds, then `countWhere p (replicate n x) = n`. -/
theorem countWhere_replicate_of_true {α : Type u} (p : α → Prop) [DecidablePred p]
    {x : α} (h : p x) (n : Nat) : countWhere p (List.replicate n x) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, countWhere_cons]
      simp [h, ih, Nat.add_comm]

/-- If `¬ p x`, then `countWhere p (replicate n x) = 0`. -/
theorem countWhere_replicate_of_false {α : Type u} (p : α → Prop) [DecidablePred p]
    {x : α} (h : ¬ p x) (n : Nat) : countWhere p (List.replicate n x) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, countWhere_cons]
      simp [h, ih]

/-- `countWhere` is invariant under a mapping `f` that preserves the predicate. -/
theorem countWhere_map_eq_self {α : Type u} (p : α → Prop) [DecidablePred p]
    (f : α → α) (xs : List α) (h : ∀ x, p (f x) ↔ p x) :
    countWhere p (xs.map f) = countWhere p xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [countWhere_cons, h x, ih]

/-! ### `countInRange`: count numbers in `[0, limit)` satisfying a predicate -/

/-- Count how many `i` in `[0, limit)` satisfy `p i`.
Equivalent to `countWhere p (range limit)`. -/
def countInRange (limit : Nat) (p : Nat → Prop) [DecidablePred p] : Nat :=
  ((range limit).filter p).length

/-- The count of elements satisfying `p` in `[0, limit)` is bounded by `limit`. -/
lemma countInRange_le (limit : Nat) (p : Nat → Prop) [DecidablePred p] :
    countInRange limit p ≤ limit := by
  unfold countInRange
  calc
    ((range limit).filter p).length ≤ (range limit).length :=
      List.length_filter_le _ _
    _ = limit := by simp

/-! ### `filterMapIf`: filter by a `Prop` predicate then map

`filterMapIf p f xs` filters `xs` keeping only elements satisfying `p`,
then maps `f` over the result. This combines `filter` + `map` in a single
traversal (though the definition uses separate filter and map for simplicity).
It is useful when `p` is a `Prop` predicate (via `DecidablePred`), whereas
`List.filter` expects a `Bool` predicate. -/

/-- Filter a list by a `Prop` predicate `p`, then map `f` over the surviving
elements. Equivalent to `(xs.filter p).map f` but in one pass. -/
def filterMapIf {α β : Type u} (p : α → Prop) [DecidablePred p] (f : α → β) :
    List α → List β
  | [] => []
  | x :: xs =>
      if p x then f x :: filterMapIf p f xs else filterMapIf p f xs

@[simp] theorem filterMapIf_nil {α β : Type u} (p : α → Prop) [DecidablePred p]
    (f : α → β) : filterMapIf p f [] = [] := rfl

/-! ## `keepEndsFilterMiddle`: filter interior elements while preserving boundaries

`keepEndsFilterMiddle keep xs` keeps the first and last elements of `xs` unchanged,
and filters the remaining (interior) elements by the boolean predicate `keep`.
For lists of length 0 or 1, the list is returned unchanged. -/

/-- Keep the first and last elements, filter the interior by `keep`.
For a list `x :: y :: rest`, the result is `x :: ((y :: rest).dropLast.filter keep) ++ [last]`. -/
def keepEndsFilterMiddle {α : Type} (keep : α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      x :: (((y :: rest).dropLast.filter keep) ++
        [(y :: rest).getLast (by simp)])

/-- The result of `keepEndsFilterMiddle` is no longer than the input. -/
theorem length_keepEndsFilterMiddle_le {α : Type} (keep : α → Bool) (xs : List α) :
    (keepEndsFilterMiddle keep xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [keepEndsFilterMiddle]
  | cons c rest =>
      cases rest with
      | nil => simp [keepEndsFilterMiddle]
      | cons d rest =>
          simp [keepEndsFilterMiddle]
          have h := List.length_filter_le keep (d :: rest).dropLast
          have hdrop : (d :: rest).dropLast.length ≤ rest.length := by
            cases rest <;> simp
          omega

/-- If every element of `xs` satisfies `keep`, then `keepEndsFilterMiddle keep xs = xs`. -/
theorem keepEndsFilterMiddle_eq_self_of_forall {α : Type} {keep : α → Bool}
    {xs : List α} (h : ∀ x, x ∈ xs → keep x = true) :
    keepEndsFilterMiddle keep xs = xs := by
  cases xs with
  | nil => simp [keepEndsFilterMiddle]
  | cons c rest =>
      cases rest with
      | nil => simp [keepEndsFilterMiddle]
      | cons d rest =>
          have hfilter :
              (d :: rest).dropLast.filter keep = (d :: rest).dropLast := by
            apply List.filter_eq_self.2
            intro x hx
            have hmem : x ∈ c :: d :: rest := by
              have hmem' : x ∈ d :: rest := List.mem_of_mem_dropLast hx
              exact List.mem_cons_of_mem c hmem'
            exact h x hmem
          rw [keepEndsFilterMiddle, hfilter]
          exact congrArg (fun tail => c :: tail) (List.dropLast_append_getLast (by simp))

/-- The last element of `keepEndsFilterMiddle keep xs` (accessed via `getD`)
equals the last element of `xs`. -/
theorem keepEndsFilterMiddle_last_getD {α : Type} [Inhabited α]
    (keep : α → Bool) (xs : List α) :
    (keepEndsFilterMiddle keep xs).getD (keepEndsFilterMiddle keep xs).length.pred default =
      xs.getD xs.length.pred default := by
  cases xs with
  | nil => simp [keepEndsFilterMiddle]
  | cons c rest =>
      cases rest with
      | nil => simp [keepEndsFilterMiddle]
      | cons d rest =>
          simp [keepEndsFilterMiddle]
          rw [List.getLast_eq_getElem]
          simp

/-! ### `filter_eq_nil_of_not_mem`: filter by equality with a non-member -/

/-- If `x` is not in `xs`, then filtering `xs` for elements equal to `x` returns `[]`.
This is a convenience specialization of `List.filter_eq_nil_iff`. -/
theorem filter_eq_nil_of_not_mem {α : Type u} [DecidableEq α]
    {xs : List α} {x : α} (hx : x ∉ xs) :
    xs.filter (fun y => y = x) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro y hy
  have hyne : y ≠ x := by
    intro hyx
    exact hx (by simpa [hyx] using hy)
  simp [hyne]

/-! ### `countWhere` with disjoint predicates -/

/-- If two predicates `p` and `q` are disjoint (no element can satisfy both), then the
sum of their counts in any list is bounded by the list length. This captures the
intuition that disjoint properties cannot share list elements, so counting them
independently cannot exceed the total number of elements available. -/
theorem countWhere_pair_le_length_of_disjoint {α : Type u}
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hdisjoint : ∀ x, p x → q x → False) (xs : List α) :
    countWhere p xs + countWhere q xs ≤ xs.length := by
  induction xs with
  | nil =>
      simp [countWhere]
  | cons x xs ih =>
      simp [countWhere_cons]
      by_cases hp : p x
      · by_cases hq : q x
        · exact False.elim (hdisjoint x hp hq)
        · simp [hp, hq]
          omega
      · by_cases hq : q x
        · simp [hp, hq]
          omega
        · simp [hp, hq]
          omega

/-! ### `filterNot`: keep elements that do NOT satisfy a `Prop` predicate

`filterNot p xs` keeps elements of `xs` where `¬ p x` holds. Unlike `List.filter`
(which uses `Bool` predicates), this is defined for `Prop` predicates via `DecidablePred`.
It is equivalent to `xs.filter fun x => ¬ p x`. -/

/-- `filterNot p xs` returns the elements of `xs` where `p` does NOT hold.
`p` is a `Prop` predicate with `[DecidablePred p]`. -/
def filterNot {α : Type u} (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  xs.filter fun x => ¬ p x

/-- If `x ∈ xs` and `¬ p x`, then `x ∈ filterNot p xs`. -/
theorem mem_filterNot_of_mem_of_not {α : Type u} {p : α → Prop} [DecidablePred p]
    {xs : List α} {x : α} :
    x ∈ xs → ¬ p x → x ∈ filterNot p xs := by
  intro hx hNot
  unfold filterNot
  simp [hx, hNot]

/-- If `x ∈ filterNot p xs`, then `¬ p x`. -/
theorem not_of_mem_filterNot {α : Type u} {p : α → Prop} [DecidablePred p]
    {xs : List α} {x : α} :
    x ∈ filterNot p xs → ¬ p x := by
  intro hx
  unfold filterNot at hx
  simpa using (List.mem_filter.mp hx).2

end List

end Specific
