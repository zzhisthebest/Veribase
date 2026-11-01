import Mathlib
import general.Common.Order
import general.Common.Pair
import general.List.Ordering

namespace List

/-! ### `take` on descending sorted lists -/

/-- In a list sorted descending (`List.Pairwise (· ≥ ·) l`), for any element `x`
in the list and any element `y` among the first `k` elements, either `x ≤ y` or
`x` itself is already among the first `k`. This characterizes the first `k` elements
as the `k` largest elements of the list. -/
lemma take_descending_cases {α : Type u} [LinearOrder α] {l : List α}
    (h_sorted : List.Pairwise (· ≥ ·) l) {k : Nat} :
    ∀ x ∈ l, ∀ y ∈ l.take k, x ≤ y ∨ x ∈ l.take k := by
  induction l generalizing k with
  | nil =>
    intro x hx
    exfalso; exact List.not_mem_nil x hx
  | cons a as ih =>
    rcases List.pairwise_cons.mp h_sorted with ⟨ha_ge_as, h_sorted_as⟩
    by_cases hk0 : k = 0
    · subst hk0
      intro x hx y hy
      simp at hy
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      intro x hx y hy
      cases List.mem_cons.mp hx with
      | inl hx_eq =>
        rw [hx_eq]
        right
        have htake : (a::as).take k = a :: as.take (k-1) := by
          simpa using List.take_cons hk_pos
        rw [htake]
        exact List.mem_cons_self a (as.take (k-1))
      | inr hx_as =>
        have htake : (a::as).take k = a :: as.take (k-1) := by
          simpa using List.take_cons hk_pos
        rw [htake] at hy
        match List.mem_cons.mp hy with
        | Or.inl hy_eq =>
          rw [hy_eq]
          have hax : a ≥ x := ha_ge_as x hx_as
          left; exact hax
        | Or.inr hy_take =>
          rcases ih h_sorted_as x hx_as y hy_take with (hle | hmem)
          · left; exact hle
          · right
            rw [htake]
            exact List.mem_cons_of_mem a hmem

/-! ### `filter_not_mem_image` — filter elements whose image is not in another list's image -/

/-- Filter `xs` keeping only elements whose image under `f` does not appear in the image
of `ys` under `f`. This is a set-difference-like operation parameterized by a function:
`filter_not_mem_image f xs ys` keeps `x ∈ xs` such that `f x ∉ f '' ys`.

For example, `filter_not_mem_image Char.toLower ["Ab", "Cd"] ["ab", "Ef"] = ["Cd"]`
because `"Ab".toLower` equals `"ab"` which is in the image of `["ab", "Ef"]`, but `"Cd".toLower` is not. -/
def filter_not_mem_image [DecidableEq β] (f : α → β) (xs ys : List α) : List α :=
  let ysImage := ys.map f
  xs.filter (λ x => f x ∉ ysImage)

/-- If `xs` has no duplicates, then `filter_not_mem_image f xs ys` also has no duplicates.
This follows directly from `List.Nodup.filter`. -/
lemma nodup_filter_not_mem_image [DecidableEq β] (f : α → β) {xs ys : List α} (h : List.Nodup xs) :
    List.Nodup (filter_not_mem_image f xs ys) :=
  List.Nodup.filter (λ x => f x ∉ ys.map f) h

/-! ### `mem_take_of_sorted_lt_of_exists_le` — sorted list membership in prefix -/

/-- If a list `l` is strictly sorted by `<`, element `a` is in `l`, and there exists
some `x` in the first `n` elements of `l` with `a ≤ x`, then `a` must also be in the
first `n` elements. This is a key lemma for showing that when a list is sorted, the
presence of a greater-or-equal element in the prefix forces the element itself to be
in the prefix. -/
lemma mem_take_of_sorted_lt_of_exists_le {α : Type} [LinearOrder α] {l : List α} {a : α} {n : Nat}
    (h_sorted : List.Sorted (· < ·) l) (h_mem : a ∈ l)
    (h_exists : ∃ x ∈ l.take n, a ≤ x) : a ∈ l.take n := by
  rcases h_exists with ⟨x, hx_take, ha_le_x⟩
  by_cases h : a ∈ l.take n
  · exact h
  · have h_drop : a ∈ l.drop n := by
      have h_append : a ∈ l.take n ++ l.drop n := by
        rw [List.take_append_drop n l]
        exact h_mem
      rw [List.mem_append] at h_append
      rcases h_append with (h' | h_drop)
      · exact absurd h' h
      · exact h_drop
    have h_lt : x < a := h_sorted.rel_of_mem_take_of_mem_drop hx_take h_drop
    exact absurd ha_le_x (not_le_of_lt h_lt)

/-! ### `take_nonempty_of_mem_of_pos` — nonempty `take` from nonempty list -/

/-- If a list contains an element `x` and we take `k > 0` elements, the result is nonempty.
This is useful when we need to extract a witness from a `take`-prefix of a nonempty list. -/
lemma take_nonempty_of_mem_of_pos {α : Type u} (l : List α) (x : α) (hx : x ∈ l) (k : Nat) (hk : 0 < k) :
    l.take k ≠ [] := by
  have hlen_pos : 0 < l.length := List.length_pos_of_mem hx
  have hlen_take : (l.take k).length = min k l.length := List.length_take k l
  by_contra h_empty
  have hlen0 : (l.take k).length = 0 := by simp [h_empty]
  rw [hlen_take] at hlen0
  omega

end List

namespace List

/-! ### `qsort` — stable quicksort parameterized by a Boolean less-than comparator -/

/-- Stable quicksort on any type, parameterized by a Boolean less-than comparator.
Uses well-founded recursion on list length to ensure termination. -/
def qsort {α : Type} (lt : α → α → Bool) (l : List α) : List α :=
  WellFounded.fix (InvImage.wf (fun l : List α => l.length) Nat.lt_wfRel.wf) (fun l IH =>
    match l with
    | [] => []
    | x :: xs =>
      let smaller := xs.filter (fun y => lt y x)
      let greaterEq := xs.filter (fun y => !lt y x)
      have h_smaller : smaller.length < (x :: xs).length := by
        dsimp [smaller]
        have hle := List.length_filter_le (fun y => lt y x) xs
        omega
      have h_greaterEq : greaterEq.length < (x :: xs).length := by
        dsimp [greaterEq]
        have hle := List.length_filter_le (fun y => !lt y x) xs
        omega
      IH smaller h_smaller ++ (x :: IH greaterEq h_greaterEq)
  ) l

/-! ### `map` then `mergeSort` — interaction of map with merge sort -/

/-- Sorting after mapping preserves sortedness: `(l.map f).mergeSort (· ≤ ·)` is sorted. -/
lemma map_mergeSort_sorted {α β : Type} [LinearOrder β] (f : α → β) (l : List α) :
    Sorted (· ≤ · : β → β → Prop) ((l.map f).mergeSort (· ≤ ·)) :=
  sorted_mergeSort' (r := (· ≤ · : β → β → Prop)) (l.map f)

/-- The length of `(l.map f).mergeSort (· ≤ ·)` equals the length of `l`. -/
lemma map_mergeSort_length {α β : Type} [LinearOrder β] (f : α → β) (l : List α) :
    ((l.map f).mergeSort (· ≤ ·)).length = l.length := by
  rw [length_mergeSort, length_map]

/-- If `x` is in `l`, then `f x` is in the sorted result of `(l.map f).mergeSort (· ≤ ·)`. -/
lemma mem_map_mergeSort_of_mem {α β : Type} [LinearOrder β] (f : α → β) {l : List α} {x : α}
    (h : x ∈ l) : f x ∈ (l.map f).mergeSort (· ≤ ·) :=
  mem_mergeSort.mpr (mem_map_of_mem f h)

/-- If `y` is in `(l.map f).mergeSort (· ≤ ·)`, then `y` is in `l.map f`. -/
lemma mem_of_map_mergeSort {α β : Type} [LinearOrder β] (f : α → β) {l : List α} {y : β}
    (h : y ∈ (l.map f).mergeSort (· ≤ ·)) : y ∈ l.map f :=
  mem_mergeSort.mp h

/-! ### `mergeSort` with `decide (· ≤ ·)` on `LinearOrder` — boolean mergeSort sortedness -/

/-- On a `LinearOrder`, merging-sorting a list with the Boolean comparator
`fun a b => decide (a ≤ b)` yields a list sorted by `(· ≤ ·)` in the `Prop` sense.

This bridges the `Bool`-based `List.sorted_mergeSort` (which produces
`Pairwise (fun a b => decide (a ≤ b) = true)`) with the `Prop`-based `Sorted (· ≤ ·)`. -/
lemma mergeSort_decide_le_sorted {α : Type u} [LinearOrder α] (l : List α) :
    Sorted (· ≤ ·) (l.mergeSort (fun a b => decide (a ≤ b))) := by
  let cmp (a b : α) : Bool := decide (a ≤ b)
  have h_pairwise : Pairwise (fun a b => cmp a b = true) (l.mergeSort cmp) :=
    List.sorted_mergeSort (le := cmp) (decide_le_trans (α := α)) (decide_le_total (α := α)) l
  have h_imp : Pairwise (· ≤ ·) (l.mergeSort cmp) :=
    Pairwise.imp (fun {a b} h => of_decide_eq_true h) h_pairwise
  simpa [cmp] using h_imp

/-- Sorting with `mergeSort` by a projection `f : α → β` yields a list that is sorted
by the induced relation `(fun a b => f a ≤ f b)`. This generalizes `mergeSort_decide_le_sorted`
(which sorts by `≤` on `α` itself, corresponding to `f := id`) by allowing the ordering to be
defined through a projection into any `LinearOrder`ed type.

For example, to sort a list of pairs by their first component, use
`mergeSort_sorted_by_projection Prod.fst l`. -/
lemma mergeSort_sorted_by_projection {α β : Type u} [LinearOrder β] (f : α → β) (l : List α) :
    Sorted (fun a b : α => f a ≤ f b) (l.mergeSort (fun a b => decide (f a ≤ f b))) := by
  have h_sorted_pairwise : Pairwise (fun a b => decide (f a ≤ f b) = true)
      (l.mergeSort (fun a b => decide (f a ≤ f b))) := by
    apply sorted_mergeSort ?_ ?_ l
    · intro a b c h1 h2
      have h1' : f a ≤ f b := of_decide_eq_true h1
      have h2' : f b ≤ f c := of_decide_eq_true h2
      exact decide_eq_true (le_trans h1' h2')
    · intro a b
      rcases le_total (f a) (f b) with (h | h)
      · rw [decide_eq_true h]; simp
      · rw [decide_eq_true h]; simp
  simpa [Sorted] using h_sorted_pairwise.imp (fun h_eq => of_decide_eq_true h_eq)

/-! ### `mergeSort` with `decide (f · ≥ f ·)` — descending projection sort -/

/-- Sorting with `mergeSort` by a descending projection `f : α → β` yields a list that is
`Sorted` by the induced descending relation `(fun a b => f a ≥ f b)`. This is the descending
counterpart of `mergeSort_sorted_by_projection`. -/
lemma mergeSort_sorted_desc_by_projection {α β : Type} [LinearOrder β] (f : α → β) (l : List α) :
    Sorted (fun a b : α => f a ≥ f b) (l.mergeSort (fun a b => decide (f a ≥ f b))) := by
  have h_sorted_pairwise : Pairwise (fun a b => decide (f a ≥ f b) = true)
      (l.mergeSort (fun a b => decide (f a ≥ f b))) := by
    apply List.sorted_mergeSort ?_ ?_ l
    · intro a b c h1 h2
      rw [decide_eq_true_iff] at h1 h2
      have h : f a ≥ f c := le_trans h2 h1
      exact decide_eq_true h
    · intro a b
      rcases le_total (f a) (f b) with (h | h)
      · simp [decide_eq_true h]
      · simp [decide_eq_true h]
  simpa [Sorted] using h_sorted_pairwise.imp (fun h_eq => of_decide_eq_true h_eq)

/-! ### `sortedBoolBy` — boolean sortedness predicate -/

/-- `sortedBoolBy R l` is `true` iff every adjacent pair `(a, b)` in `l` satisfies `R a b = true`.
This is a fully computable sortedness check suitable for `Bool` postconditions. -/
def sortedBoolBy {α : Type} (R : α → α → Bool) (l : List α) : Bool :=
  (l.zip l.tail).all (fun p => R p.1 p.2)

/-- If `l` is `List.Pairwise` ordered by `R` (as `R a b = true`), then `sortedBoolBy R l = true`. -/
lemma pairwise_imp_sortedBoolBy {α : Type} {R : α → α → Bool} {l : List α}
    (h : List.Pairwise (fun a b => R a b = true) l) : sortedBoolBy R l = true := by
  induction h with
  | nil => rfl
  | @cons a l hall h_tail ih =>
    cases l with
    | nil =>
      unfold sortedBoolBy; simp
    | cons b l' =>
      have hab : R a b = true := hall b (by simp)
      calc
        sortedBoolBy R (a :: b :: l') = (R a b && sortedBoolBy R (b :: l')) := by
          unfold sortedBoolBy; simp
        _ = true := by simp [hab, ih]

/-- If `l` is `List.Sorted` by a `Prop` relation `R` with `DecidableRel`, then
`sortedBoolBy (fun a b => decide (R a b)) l = true`. This bridges the `Prop`-based
`Sorted R` to the `Bool`-based sortedness check. Together with `pairwise_of_decide`
(which goes the other direction), this provides a full equivalence between
`Sorted R` and `sortedBoolBy (fun a b => decide (R a b)) = true`. -/
lemma sorted_imp_sortedBoolBy_of_decide {α : Type} {R : α → α → Prop} [DecidableRel R] {l : List α}
    (h : l.Sorted R) : sortedBoolBy (fun a b => decide (R a b)) l = true :=
  pairwise_imp_sortedBoolBy (h.imp (fun {_ _} hR => decide_eq_true hR))

/-- If `le` is a transitive and total boolean relation, then `mergeSort` with `le`
produces a list that is `sortedBoolBy le`. This wraps `List.sorted_mergeSort` with
`pairwise_imp_sortedBoolBy` to convert the `Pairwise` result into the `sortedBoolBy` form. -/
lemma sortedBoolBy_mergeSort {α : Type} {le : α → α → Bool}
    (h_trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (h_total : ∀ a b, (le a b || le b a) = true) (l : List α) :
    sortedBoolBy le (l.mergeSort le) = true := by
  have h_pw : List.Pairwise (fun a b => le a b = true) (l.mergeSort le) :=
    List.sorted_mergeSort h_trans h_total l
  exact pairwise_imp_sortedBoolBy h_pw

/-! ### `pairwise_of_decide` — convert `decide`-wrapped `Pairwise` to `Prop` `Pairwise` -/

/-- If a list is `List.Pairwise` ordered by `fun a b => decide (R a b) = true` where `R`
has a `DecidableRel` instance, then it is also `List.Pairwise R` in the `Prop` sense. -/
lemma pairwise_of_decide {α : Type} {R : α → α → Prop} [DecidableRel R] {l : List α}
    (h : List.Pairwise (fun a b => decide (R a b) = true) l) : List.Pairwise R l := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons a l' hall h_tail ih =>
    apply List.Pairwise.cons
    · intro a' ha'
      have hdec := hall a' ha'
      exact of_decide_eq_true hdec
    · exact ih

/-! ### `mergeSort_properties` — permutation + sortedness + length for arbitrary transitive/total `R` -/

/-- For a transitive, total, decidable relation `R` on `α`,
`List.mergeSort` with `R` returns a permutation that is sorted by `R` and preserves length.

This combines `List.mergeSort_perm`, `List.sorted_mergeSort`, and `List.length_mergeSort`
into a single triple, bridging the `Bool`-based mergeSort output to the `Prop`-based `Sorted R`. -/
lemma mergeSort_properties {α : Type u} {R : α → α → Prop} [DecidableRel R]
    (h_trans : ∀ a b c, R a b → R b c → R a c)
    (h_total : ∀ a b, R a b ∨ R b a) (l : List α) :
    List.Perm l (List.mergeSort l (fun a b => decide (R a b))) ∧
    List.Sorted R (List.mergeSort l (fun a b => decide (R a b))) ∧
    (List.mergeSort l (fun a b => decide (R a b))).length = l.length := by
  have h_trans_decide : ∀ a b c, decide (R a b) = true → decide (R b c) = true → decide (R a c) = true := by
    intro a b c h1 h2
    have ha : R a b := by simpa using h1
    have hb : R b c := by simpa using h2
    have hac : R a c := h_trans a b c ha hb
    simpa
  have h_total_decide : ∀ a b, (decide (R a b) || decide (R b a)) = true := by
    intro a b
    rcases h_total a b with (h | h)
    · simp [h]
    · simp [h]
  have h_perm : List.Perm l (List.mergeSort l (fun a b => decide (R a b))) :=
    (List.mergeSort_perm l (fun a b => decide (R a b))).symm
  have h_pairwise : List.Pairwise (fun a b => decide (R a b) = true)
      (List.mergeSort l (fun a b => decide (R a b))) :=
    List.sorted_mergeSort h_trans_decide h_total_decide l
  have h_sorted : List.Sorted R (List.mergeSort l (fun a b => decide (R a b))) := by
    have h_pw_R : List.Pairwise R (List.mergeSort l (fun a b => decide (R a b))) :=
      h_pairwise.imp (fun {a b} h => of_decide_eq_true h)
    exact h_pw_R
  have h_length : (List.mergeSort l (fun a b => decide (R a b))).length = l.length :=
    List.length_mergeSort l
  exact And.intro h_perm (And.intro h_sorted h_length)

/-! ### `sorted_mergeSort_pred` — bridge `Bool` comparator to `Prop` sortedness

If a `Bool` comparator `cmp` is transitive, total, and equivalent on each pair
to a `Prop` relation `R`, then `mergeSort` with `cmp` produces a list `Sorted` by `R`.

This generalizes `List.sorted_mergeSort` (which yields `Pairwise (cmp a b = true)`)
to the `Prop` world via the equivalence `h_iff`. Unlike `mergeSort_properties` which works
through `DecidableRel`/`decide`, this works with any `Bool` comparator directly. -/

theorem sorted_mergeSort_pred {α : Type} (cmp : α → α → Bool) (R : α → α → Prop)
    (h_trans : ∀ (a b c), cmp a b = true → cmp b c = true → cmp a c = true)
    (h_total : ∀ a b, (cmp a b || cmp b a) = true)
    (h_iff : ∀ a b, cmp a b = true ↔ R a b)
    (l : List α) : List.Sorted R (List.mergeSort l cmp) := by
  have h_sorted := List.sorted_mergeSort h_trans h_total l
  have h_imp : List.Pairwise R (List.mergeSort l cmp) :=
    h_sorted.imp (fun {a b} h => (h_iff a b).mp h)
  simpa [List.Sorted] using h_imp

/-! ### `mergeSort` combined with `take` — length and membership -/

/-- The length of `((l.mergeSort r).take k).mergeSort r'` is `k ⊓ l.length`. -/
lemma length_mergeSort_take_mergeSort_eq_inf {α : Type} {r r' : α → α → Bool} (l : List α) (k : Nat) :
    (((l.mergeSort r).take k).mergeSort r').length = k ⊓ l.length := by
  calc
    (((l.mergeSort r).take k).mergeSort r').length = ((l.mergeSort r).take k).length := List.length_mergeSort _
    _ = k ⊓ (l.mergeSort r).length := List.length_take k _
    _ = k ⊓ l.length := by rw [List.length_mergeSort l]

/-- If `a` is in `((l.mergeSort r).take k).mergeSort r'`, then `a` is in `l`. -/
lemma mem_mergeSort_take_mergeSort_of_mem {α : Type} {r r' : α → α → Bool} {l : List α} {k : Nat} {a : α}
    (h : a ∈ ((l.mergeSort r).take k).mergeSort r') : a ∈ l := by
  have ha_taken : a ∈ ((l.mergeSort r).take k) := (List.mem_mergeSort (le := r')).mp h
  have ha_sorted : a ∈ l.mergeSort r := List.mem_of_mem_take ha_taken
  exact (List.mem_mergeSort (le := r)).mp ha_sorted

/-- If `a` is in the first `k` elements of `mergeSort cmp xs`, then `a ∈ xs`. -/
lemma mem_take_mergeSort {α : Type} (xs : List α) (cmp : α → α → Bool) (k : Nat) (a : α)
    (h : a ∈ (xs.mergeSort cmp).take k) : a ∈ xs :=
  List.mem_mergeSort.mp (List.mem_of_mem_take h)

/-- Length of the first `k` elements from `mergeSort`. -/
lemma length_take_mergeSort_eq_min {α : Type} (xs : List α) (cmp : α → α → Bool) (k : Nat) :
    ((xs.mergeSort cmp).take k).length = Nat.min k xs.length := by
  have h_sort_len : (xs.mergeSort cmp).length = xs.length :=
    (List.mergeSort_perm xs cmp).length_eq
  rw [List.length_take, h_sort_len]

/-! ### `insertionSort_sorted_and_perm` — combined sortedness + permutation -/

/-- `insertionSort r xs` is both `List.Sorted r` and a permutation of `xs`. -/
lemma insertionSort_sorted_and_perm {α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    (xs : List α) : List.Sorted r (xs.insertionSort r) ∧ List.Perm (xs.insertionSort r) xs := by
  constructor
  · exact List.sorted_insertionSort r xs
  · exact List.perm_insertionSort r xs

/-- `insertionSort r l` preserves the list length and produces a `Pairwise r` list. -/
lemma insertionSort_pairwise_and_length {α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    (l : List α) : (List.insertionSort r l).length = l.length ∧ (List.insertionSort r l).Pairwise r := by
  constructor
  · simp
  · exact List.sorted_insertionSort r l

/-! ### `nodup_insertionSort` — insertion sort preserves `Nodup` -/

/-- If `l` has no duplicates, then `l.insertionSort r` also has no duplicates.
This follows from the fact that `insertionSort r l` is a permutation of `l`. -/
lemma nodup_insertionSort {α : Type u} {r : α → α → Prop} [DecidableRel r] {l : List α} (h : l.Nodup) :
    (List.insertionSort r l).Nodup :=
  ((List.perm_insertionSort r l).nodup_iff.mpr h)

/-- Sorting a list with a total, transitive relation preserves `Nodup` on any mapped component,
because `insertionSort` produces a permutation and `Nodup` is preserved under permutation. -/
lemma nodup_map_insertionSort {α β : Type} [DecidableEq β] {r : α → α → Prop}
    [DecidableRel r] [IsTotal α r] [IsTrans α r]
    (f : α → β) (l : List α) (h_nodup : Nodup (l.map f)) :
    Nodup ((insertionSort r l).map f) := by
  have h_perm : List.Perm (insertionSort r l) l := List.perm_insertionSort r l
  have h_map : List.Perm ((insertionSort r l).map f) (l.map f) := List.Perm.map f h_perm
  exact (List.Perm.nodup_iff h_map).mpr h_nodup

/-! ### `sorted_map_of_sorted_pullback` — map preserves sortedness for pullback relations -/

/-- If a list is sorted by the pullback of `R` along `f`, then its image under `f` is sorted by `R`.
This generalizes `sorted_map_fst` (which is specialized to `Prod.fst`) to any function `f`. -/
lemma sorted_map_of_sorted_pullback {α β : Type} {R : β → β → Prop} (f : α → β) {l : List α}
    (h : Sorted (fun a b => R (f a) (f b)) l) : Sorted R (l.map f) :=
  h.map (f := f) (fun _ _ hpq => hpq)

/-! ### `insertionSort_map_sorted` — insertionSort + map preserves sortedness -/

/-- `insertionSort` with a comparison function derived from `f : α → β` followed by `map f`
yields a list sorted by `≤` on `β`. This is the `insertionSort` counterpart of
`mergeSort_sorted_by_projection`. -/
lemma insertionSort_map_sorted {α β : Type} [LE β] [IsTotal β (· ≤ ·)] [IsTrans β (· ≤ ·)]
    [DecidableRel (· ≤ · : β → β → Prop)] (f : α → β) (l : List α)
    [DecidableRel (fun a b : α => f a ≤ f b)] :
    Sorted (· ≤ ·) ((List.insertionSort (fun a b => f a ≤ f b) l).map f) := by
  haveI : IsTotal α (fun a b => f a ≤ f b) := IsTotal.pullback f
  haveI : IsTrans α (fun a b => f a ≤ f b) := IsTrans.pullback f
  have h_sorted : Sorted (fun a b => f a ≤ f b) (List.insertionSort (fun a b => f a ≤ f b) l) :=
    List.sorted_insertionSort (fun a b => f a ≤ f b) l
  exact sorted_map_of_sorted_pullback f h_sorted

/-! ### `insertionSort_proj_spec` — length + membership + sortedness by projection

For a total, transitive `≤` on `β`, sorting `l` via `insertionSort` by the pullback relation
`(fun a b => proj a ≤ proj b)` yields a list that has the same length as `l`, contains only
elements of `l`, and is sorted by `proj`: for any indices `i < j`,
`proj (result.get i) ≤ proj (result.get j)`. -/

/-- `insertionSort` by a projection `proj : α → β` preserves length, membership, and
yields a list sorted by `proj` (via `Fin`-based element access). -/
theorem insertionSort_proj_spec {α β : Type u} [LE β] [DecidableRel ((· ≤ ·) : β → β → Prop)]
    [h_trans : IsTrans β (· ≤ ·)] [h_total : IsTotal β (· ≤ ·)] (proj : α → β) (l : List α) :
    (l.insertionSort (λ a b : α => proj a ≤ proj b)).length = l.length ∧
    (∀ x, x ∈ l.insertionSort (λ a b : α => proj a ≤ proj b) → x ∈ l) ∧
    (∀ (i j : Fin (l.insertionSort (λ a b : α => proj a ≤ proj b)).length), i.1 < j.1 →
      proj ((l.insertionSort (λ a b : α => proj a ≤ proj b)).get i) ≤
      proj ((l.insertionSort (λ a b : α => proj a ≤ proj b)).get j)) := by
  set r := λ a b : α => proj a ≤ proj b with hr
  haveI : IsTrans α r :=
    ⟨λ a b c h₁ h₂ => h_trans.trans (proj a) (proj b) (proj c) h₁ h₂⟩
  haveI : IsTotal α r :=
    ⟨λ a b => h_total.total (proj a) (proj b)⟩
  have h_len : (l.insertionSort r).length = l.length :=
    List.length_insertionSort r l
  have h_sorted : List.Sorted r (l.insertionSort r) :=
    List.sorted_insertionSort r l
  refine ⟨h_len, ?_, ?_⟩
  · intro x hx
    rw [List.mem_insertionSort r] at hx
    exact hx
  · intro i j hij
    exact h_sorted.rel_get_of_lt (a := i) (b := j) hij

/-! ### `insertBy` and `sortBy` — insertion sort with a `Bool` comparator

These provide a generic insertion sort parameterized by a `Bool`-valued comparator,
simpler to use in algorithmic contexts than `insertionSort` which requires `DecidableRel`,
`IsTotal`, and `IsTrans` instances. -/

/-- Generic insertion of `x` into a list already sorted by `cmp : α → α → Bool`. -/
def insertBy {α : Type} (cmp : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | a :: as =>
    if cmp x a then x :: a :: as
    else a :: insertBy cmp x as

/-- Generic insertion sort using `cmp : α → α → Bool` as the comparator. -/
def sortBy {α : Type} (cmp : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy cmp x (sortBy cmp xs)

/-! ### Membership lemmas for `insertBy` and `sortBy` -/

lemma mem_insertBy {α : Type} (cmp : α → α → Bool) (x y : α) (l : List α) :
    y ∈ insertBy cmp x l ↔ y = x ∨ y ∈ l := by
  induction l generalizing x y with
  | nil => simp [insertBy]
  | cons a as IH =>
    simp [insertBy]
    split
    · simp
    · simp [IH]
      constructor
      · rintro (h | h | h)
        · right; left; exact h
        · left; exact h
        · right; right; exact h
      · rintro (h | h | h)
        · right; left; exact h
        · left; exact h
        · right; right; exact h

lemma mem_sortBy {α : Type} (cmp : α → α → Bool) (l : List α) (w : α) :
    w ∈ sortBy cmp l ↔ w ∈ l := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs IH =>
    simp [sortBy, mem_insertBy, IH]

/-! ### Length lemmas for `insertBy` and `sortBy` -/

/-- Inserting an element via `insertBy` adds exactly one to the list length,
regardless of the comparator result. This generalizes `insertByCount_length`. -/
lemma insertBy_length {α : Type} (cmp : α → α → Bool) (x : α) (l : List α) :
    (insertBy cmp x l).length = l.length + 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons q qs ih =>
      unfold insertBy
      split <;> simp [ih]

/-- Sorting a list with `sortBy` preserves the list length.
This generalizes `sortedByCount_length`. -/
lemma sortBy_length {α : Type} (cmp : α → α → Bool) (l : List α) :
    (sortBy cmp l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p ps' ih =>
      unfold sortBy
      rw [insertBy_length cmp p (sortBy cmp ps')]
      simp [ih]

/-- Taking the first `n` elements from a `sortBy`-sorted list has length
`Nat.min n l.length`. This combines `List.length_take` with `sortBy_length`. -/
lemma length_take_sortBy {α : Type} (cmp : α → α → Bool) (l : List α) (n : Nat) :
    ((sortBy cmp l).take n).length = Nat.min n l.length := by
  rw [List.length_take, sortBy_length]

/-! ### Perm lemmas for `insertBy` and `sortBy` -/

/-- Inserting an element via `insertBy` yields a list that is a permutation of `x :: l`.
In other words, `insertBy` preserves the multiset of elements
(it just rearranges them into sorted position). -/
lemma insertBy_perm {α : Type} (cmp : α → α → Bool) (x : α) (l : List α) :
    List.Perm (insertBy cmp x l) (x :: l) := by
  induction l generalizing x with
  | nil => simp [insertBy]
  | cons a as IH =>
    simp [insertBy]
    split
    · rfl
    · have h : List.Perm (a :: insertBy cmp x as) (a :: x :: as) :=
        List.Perm.cons a (IH x)
      have hswap : List.Perm (a :: x :: as) (x :: a :: as) :=
        List.Perm.swap x a as
      exact List.Perm.trans h hswap

/-- `sortBy` returns a permutation of the input list.
Sorting rearranges elements but does not add or remove any. -/
lemma sortBy_perm {α : Type} (cmp : α → α → Bool) (l : List α) :
    List.Perm (sortBy cmp l) l := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs IH =>
    simp [sortBy]
    have h_ins : List.Perm (insertBy cmp x (sortBy cmp xs)) (x :: sortBy cmp xs) :=
      insertBy_perm cmp x (sortBy cmp xs)
    have h_cons : List.Perm (x :: sortBy cmp xs) (x :: xs) :=
      List.Perm.cons x IH
    exact List.Perm.trans h_ins h_cons

/-! ### Nodup lemmas for `insertBy` and `sortBy` -/

lemma nodup_insertBy {α : Type} (cmp : α → α → Bool) (x : α) (l : List α) (h : l.Nodup)
    (hx : x ∉ l) : (insertBy cmp x l).Nodup := by
  induction l generalizing x with
  | nil => simp [insertBy]
  | cons a as IH =>
    rcases (List.nodup_cons.mp h) with ⟨ha_not_mem, h_as_nodup⟩
    dsimp [insertBy]
    by_cases h_cmp : cmp x a
    · rw [if_pos h_cmp]
      refine List.Nodup.cons ?_ (List.Nodup.cons ha_not_mem h_as_nodup)
      intro hmem
      rcases List.mem_cons.mp hmem with (rfl | h_as')
      · exact hx (by simp)
      · exact hx (List.mem_cons_of_mem a h_as')
    · rw [if_neg h_cmp]
      have hx_not_as : x ∉ as := fun hx_as' => hx (List.mem_cons_of_mem a hx_as')
      have ha_not_mem_insert : a ∉ insertBy cmp x as := by
        rw [mem_insertBy]
        intro hor
        rcases hor with (rfl | ha_as)
        · exact hx (by simp)
        · exact ha_not_mem ha_as
      refine List.Nodup.cons ha_not_mem_insert (IH x h_as_nodup hx_not_as)

lemma nodup_sortBy {α : Type} (cmp : α → α → Bool) (l : List α) (h : l.Nodup) :
    (sortBy cmp l).Nodup := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs IH =>
    rcases (List.nodup_cons.mp h) with ⟨hx_nmem, hxs_nd⟩
    simp [sortBy]
    apply nodup_insertBy cmp x (sortBy cmp xs) (IH hxs_nd)
    intro hx_sort
    apply hx_nmem
    rw [← mem_sortBy cmp xs x]
    exact hx_sort

/-! ### `Pairwise` lemmas

`pairwise_getElem` gives the fundamental direction of `List.pairwise_iff_getElem`:
if `l` is `Pairwise R`, then `R (l[i]) (l[j])` for all `i < j` within bounds.
Unlike `pairwise_getElem!_of_lt`, this version uses `l[i]` (requiring the in-bounds
proof `hi` as an explicit argument) and thus does NOT need `[Inhabited α]`.

`pairwise_getD` bridges `List.Pairwise R l` to the `getD` accessor:
if a list is pairwise-related by `R`, then its elements at indices `i < j`
satisfy `R (l.getD i d) (l.getD j d)`. -/

/-- If `l` is pairwise `R`, then `R (l[i]) (l[j])` holds for all `i < j` within bounds. -/
theorem pairwise_getElem {α : Type u} {R : α → α → Prop} {l : List α}
    (h : List.Pairwise R l) : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
    i < j → R (l[i]) (l[j]) :=
  List.pairwise_iff_getElem.mp h

lemma pairwise_getD {α : Type} (R : α → α → Prop) (l : List α) (default : α)
    (h : List.Pairwise R l) (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    R (l.getD i default) (l.getD j default) := by
  have h_pairwise_get := (List.pairwise_iff_get (R := R) (l := l)).mp h
  have h_val := h_pairwise_get ⟨i, hi⟩ ⟨j, hj⟩ hij
  have h_getD_i : l.getD i default = l.get ⟨i, hi⟩ := by
    unfold List.getD; simp [hi]
  have h_getD_j : l.getD j default = l.get ⟨j, hj⟩ := by
    unfold List.getD; simp [hj]
  rw [h_getD_i, h_getD_j]
  exact h_val

/-- If a list is `Pairwise` related by a boolean relation `R` (expressed as `R a b = true`),
then `getElem!` access preserves the relation: for any `i < j` with `i, j < l.length`,
`R (l[i]!) (l[j]!) = true`. This is the `Bool` + `getElem!` variant of `pairwise_getD`,
convenient for verified algorithms that use `Bool` comparators. -/
lemma pairwise_getElem_of_bool {α : Type} [Inhabited α] (R : α → α → Bool) (l : List α)
    (hp : List.Pairwise (fun a b => R a b = true) l)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    R (l[i]!) (l[j]!) = true := by
  have h_pairwise_get := (List.pairwise_iff_get (R := fun a b => R a b = true)).mp hp
  have h_val := h_pairwise_get ⟨i, hi⟩ ⟨j, hj⟩ hij
  simpa [getElem!_pos l i hi, getElem!_pos l j hj] using h_val

/-- If a list is `Pairwise` related by a boolean relation `R` (expressed as `R a b = true`),
then for any `Fin` indices `i < j`, `R (l.get i) (l.get j) = true`.
This is the `Fin` + `get` variant of `pairwise_getElem_of_bool`,
which uses `Nat` indices and `getElem!`. -/
lemma pairwise_get_of_bool {α : Type} (R : α → α → Bool) (l : List α)
    (h : List.Pairwise (fun a b => R a b = true) l) (i j : Fin l.length) (h_lt : i < j) :
    R (l.get i) (l.get j) = true := by
  rw [List.pairwise_iff_get] at h
  exact h i j h_lt

/-- If a list is `Pairwise` related by a `Prop` relation `R`, then for any `i < j` with
`i, j < l.length`, `R (l[i]!) (l[j]!)`. This is the `Prop` + `getElem!` variant of
`pairwise_getD`, convenient when using the `l[i]!` notation with `[Inhabited α]`. -/
lemma pairwise_getElem!_of_lt {α : Type} [Inhabited α] {R : α → α → Prop} {l : List α}
    (h : List.Pairwise R l) {i j : Nat} (hij : i < j) (hi : i < l.length) (hj : j < l.length) :
    R (l[i]!) (l[j]!) := by
  have hpair := (List.pairwise_iff_get (R := R) (l := l)).mp h
  have hfin_ij : (⟨i, hi⟩ : Fin l.length) < (⟨j, hj⟩ : Fin l.length) := hij
  have hget := hpair ⟨i, hi⟩ ⟨j, hj⟩ hfin_ij
  simpa [getElem!_pos l i hi, getElem!_pos l j hj] using hget

/-- If `xs` is `Pairwise R`, then for the first `k` elements, every element in the prefix
    relates via `R` to every element not in the prefix. This is a structural consequence
    of the `Pairwise` definition: each element relates to every element that comes after it. -/
lemma take_le_of_pairwise {α : Type} (xs : List α) (R : α → α → Prop) (k : Nat)
    (h : List.Pairwise R xs) : ∀ s ∈ xs.take k, ∀ t ∈ xs, t ∉ xs.take k → R s t := by
  induction xs generalizing k with
  | nil => intro s hs; simp at hs
  | cons x xs' ih =>
    rw [List.pairwise_cons] at h
    rcases h with ⟨h_head, h_tail⟩
    cases k with
    | zero => intro s hs; simp at hs
    | succ k =>
      rw [List.take_succ_cons]
      intro s hs t ht ht_not
      simp only [List.mem_cons] at hs ht
      rcases hs with (rfl | hs_mem)
      · rcases ht with (rfl | ht_mem)
        · exfalso; apply ht_not; simp
        · exact h_head t ht_mem
      · rcases ht with (rfl | ht_mem)
        · exfalso; apply ht_not; simp
        · have ht_not_take : t ∉ xs'.take k := by
            intro hmem; apply ht_not; simp [hmem]
          exact ih k h_tail s hs_mem t ht_mem ht_not_take

/-- If a list is `List.Sorted r` and `i < j` are valid indices, then `r (l[i]!) (l[j]!)`.
This is the `Sorted` + `getElem!` variant of `pairwise_getD`, using the convenient
`l[i]!` notation (which requires `[Inhabited α]`). -/
lemma sorted_lt_idx {α : Type} [Inhabited α] {r : α → α → Prop} {l : List α} (h_sorted : List.Sorted r l)
    {i j : Nat} (hij : i < j) (hi : i < l.length) (hj : j < l.length) : r (l[i]!) (l[j]!) := by
  have h_pairwise := ((List.pairwise_iff_getElem (R := r)).mp h_sorted) i j hi hj hij
  rw [getElem!_pos l i hi, getElem!_pos l j hj]
  exact h_pairwise

/-- If a list is `List.Sorted r` and `i+1 < l.length`, then adjacent elements satisfy
`r (l[i]!) (l[i+1]!)`. This is a convenience specialization of `sorted_lt_idx` for the
common case of consecutive indices, requiring only `i+1 < l.length` (which implies
`i < l.length`). -/
lemma sorted_adjacent {α : Type} [Inhabited α] {r : α → α → Prop} {l : List α}
    (h_sorted : List.Sorted r l) (i : Nat) (hi : i + 1 < l.length) : r (l[i]!) (l[i + 1]!) := by
  have hi_lt : i < l.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi)
  exact sorted_lt_idx h_sorted (Nat.lt_succ_self i) hi_lt hi

/-- If a list is `List.Sorted r` and `i < j` are valid indices, then
`r (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩)`.  This is the `Sorted` + `get` (no `Inhabited`)
variant of `sorted_lt_idx`, which uses `getElem!` and requires `[Inhabited α]`. -/
lemma sorted_get_of_lt {α : Type} {r : α → α → Prop} {l : List α} (h_sorted : List.Sorted r l)
    {i j : Nat} (hij : i < j) (hi : i < l.length) (hj : j < l.length) :
    r (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩) := by
  have h_pairwise_get := (List.pairwise_iff_get (R := r)).mp h_sorted
  exact h_pairwise_get ⟨i, hi⟩ ⟨j, hj⟩ hij

/-- If a list is `Sorted` by relation `R`, then for `i < j` both within bounds,
the `getD` values (with default `d`) are related by `R`. This is the `Sorted` + `getD`
variant of `pairwise_getD`, which requires no `[Inhabited α]` instance (unlike `sorted_lt_idx`
which uses `getElem!`). -/
lemma sorted_getD_rel {α : Type _} (R : α → α → Prop) {l : List α}
    (h_sorted : l.Sorted R) (d : α) {i j : Nat} (hij : i < j)
    (hi : i < l.length) (hj : j < l.length) : R (l.getD i d) (l.getD j d) := by
  rw [List.getD_eq_getElem l d hi, List.getD_eq_getElem l d hj]
  let a : Fin l.length := ⟨i, hi⟩
  let b : Fin l.length := ⟨j, hj⟩
  have hab : a < b := hij
  have hrel := h_sorted.rel_get_of_lt hab
  simpa using hrel

lemma insertBy_pairwise {α : Type} (cmp : α → α → Bool) (R : α → α → Prop)
    (h_cmp_iff : ∀ a b, cmp a b ↔ R a b)
    (h_trans : ∀ a b c, R a b → R b c → R a c)
    (h_total : ∀ a b, ¬ cmp a b → cmp b a)
    (x : α) (l : List α) (h : List.Pairwise R l) :
    List.Pairwise R (insertBy cmp x l) := by
  induction l generalizing x with
  | nil => simp [insertBy]
  | cons a as IH =>
    rcases List.pairwise_cons.mp h with ⟨ha_ge, h_pairwise⟩
    dsimp [insertBy]
    by_cases h_cmp : cmp x a
    · rw [if_pos h_cmp]
      have hx_ge_a : R x a := (h_cmp_iff x a).mp h_cmp
      have h_all_x : ∀ b ∈ (a :: as), R x b := by
        intro b hb
        rcases List.mem_cons.mp hb with (rfl | hb_as)
        · exact hx_ge_a
        · exact h_trans x a b hx_ge_a (ha_ge b hb_as)
      refine List.Pairwise.cons h_all_x (List.Pairwise.cons ha_ge h_pairwise)
    · rw [if_neg h_cmp]
      have h_cmp_rev : cmp a x := h_total x a h_cmp
      have ha_ge_x : R a x := (h_cmp_iff a x).mp h_cmp_rev
      have h_all_a : ∀ b ∈ insertBy cmp x as, R a b := by
        intro b hb
        rcases (mem_insertBy cmp x b as).mp hb with (rfl | hb_as)
        · exact ha_ge_x
        · exact ha_ge b hb_as
      refine List.Pairwise.cons h_all_a (IH x h_pairwise)

lemma sortBy_pairwise {α : Type} (cmp : α → α → Bool) (R : α → α → Prop)
    (h_cmp_iff : ∀ a b, cmp a b ↔ R a b)
    (h_trans : ∀ a b c, R a b → R b c → R a c)
    (h_total : ∀ a b, ¬ cmp a b → cmp b a)
    (l : List α) : List.Pairwise R (sortBy cmp l) := by
  induction l with
  | nil => simp [sortBy]
  | cons x xs IH =>
    simp [sortBy]
    exact insertBy_pairwise cmp R h_cmp_iff h_trans h_total x (sortBy cmp xs) IH

/-! ### `insertBy_all_rel` — lower-bound preservation for `insertBy`

If an element `a` relates to everything in `as` via a transitive relation `R`, and `a`
relates to `x` via `R`, then `a` relates to everything in `insertBy cmp x as` via `R`.
Requires that `¬ cmp x y` implies `R y x` (which follows from totality of the underlying
order). This generalizes `insertCI_bound` (case-insensitive string comparison) to any
comparator and any transitive relation meeting this property. -/

lemma insertBy_all_rel {α : Type} (cmp : α → α → Bool) (R : α → α → Prop)
    (h_cmp_false : ∀ a b, cmp a b = false → R b a)
    (h_trans : ∀ {a b c : α}, R a b → R b c → R a c)
    (a x : α) (as : List α) (hx : R a x) (has : ∀ b ∈ as, R a b) :
    ∀ b ∈ insertBy cmp x as, R a b := by
  induction as generalizing x with
  | nil =>
    rw [insertBy]
    simp [hx]
  | cons h t IH =>
    have has_h : R a h := has h (by simp)
    have has_t : ∀ c ∈ t, R a c := by
      intro c hc; exact has c (List.mem_cons_of_mem h hc)
    by_cases h_cmp : cmp x h
    · rw [insertBy, if_pos h_cmp]
      intro b hb
      rcases List.mem_cons.mp hb with (rfl | hb')
      · exact hx
      · rcases List.mem_cons.mp hb' with (rfl | hb'')
        · exact has_h
        · exact has_t _ hb''
    · rw [insertBy, if_neg h_cmp]
      have hhx : R h x := h_cmp_false x h (by simpa using h_cmp)
      have hax' : R a x := h_trans has_h hhx
      intro b hb
      rcases List.mem_cons.mp hb with (rfl | hb')
      · exact has_h
      · exact IH x hax' has_t _ hb'

/-! ### `insertBy_toFinset_eq` and `sortBy_toFinset` — Finset preservation -/

/-- The `toFinset` of `insertBy cmp x ys` equals the `toFinset` of `x :: ys`.
In other words, inserting an element does not change the set of elements. -/
lemma insertBy_toFinset_eq {α : Type} (cmp : α → α → Bool) [DecidableEq α] (x : α) (ys : List α) :
    (insertBy cmp x ys).toFinset = (x :: ys).toFinset := by
  induction' ys with y ys ih
  · rfl
  · unfold insertBy
    split
    · rfl
    · simp [ih, Finset.insert_comm]

/-- Sorting a list with `sortBy` preserves the `toFinset` — the set of elements is unchanged. -/
lemma sortBy_toFinset {α : Type} (cmp : α → α → Bool) [DecidableEq α] (l : List α) :
    (sortBy cmp l).toFinset = l.toFinset := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [sortBy, insertBy_toFinset_eq cmp x (sortBy cmp xs), ih]

/-! ### `dedup_eq_eraseDup` — equivalence of `dedup` and `eraseDup` -/

/-- For any type with `DecidableEq`, `dedup` and `eraseDup` produce the same result.
`List.dedup` uses `pwFilter (· ≠ ·)` (from `Mathlib`) while `List.eraseDup` uses
`pwFilter (· != ·)` (from `Batteries`); under `DecidableEq` these are equivalent. -/
lemma dedup_eq_eraseDup {α : Type} [DecidableEq α] (l : List α) : l.dedup = l.eraseDup := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.dedup, List.eraseDup, List.pwFilter]
    simp [List.foldr, ih]

/-! ### `sorted_dedup` — `dedup` preserves `Sorted` -/

/-- If a list `l` is `Sorted` by a relation `r`, then its deduplicated version `l.dedup`
is also `Sorted` by `r`. This follows from `List.dedup_sublist` and the fact that `Sorted`
descends to sublists. -/
lemma sorted_dedup {α : Type} [DecidableEq α] {r : α → α → Prop} {l : List α}
    (h : List.Sorted r l) : List.Sorted r (l.dedup) :=
  List.Pairwise.sublist (List.dedup_sublist l) h

/-! ### `sortDedupBy` — deduplicate and then sort -/

/-- Deduplicate a list and sort it by the given comparison relation.
Equivalent to `(l.dedup).insertionSort r`. -/
def sortDedupBy {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) : List α :=
  (l.dedup).insertionSort r

/-- Membership in `sortDedupBy` is equivalent to membership in the original list. -/
lemma mem_sortDedupBy {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) (a : α) :
    a ∈ sortDedupBy r l ↔ a ∈ l := by
  unfold sortDedupBy
  simp [List.mem_insertionSort, List.mem_dedup]

/-- Membership in a sorted, deduplicated, mapped list under relation `r` is equivalent to
membership in the original mapped list. That is, `x` belongs to the result of sorting and
deduplicating `l.map f` iff `x = f a` for some `a ∈ l`. -/
lemma mem_insertionSort_dedup_map_iff {α β : Type} [DecidableEq β]
    (r : β → β → Prop) [DecidableRel r] (f : α → β) (l : List α) (x : β) :
    x ∈ List.insertionSort r (List.dedup (l.map f)) ↔ ∃ a, a ∈ l ∧ f a = x := by
  rw [List.mem_insertionSort, List.mem_dedup, List.mem_map]

/-- `sortDedupBy` produces a nodup list. -/
lemma nodup_sortDedupBy {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) :
    (sortDedupBy r l).Nodup := by
  unfold sortDedupBy
  have h_nodup_dedup : l.dedup.Nodup := List.nodup_dedup _
  have h_perm : List.Perm ((l.dedup).insertionSort r) (l.dedup) :=
    List.perm_insertionSort r (l.dedup)
  exact h_perm.nodup_iff.mpr h_nodup_dedup

/-- `sortDedupBy` produces a list sorted with respect to `r`.
Requires `IsTotal` and `IsTrans` for `insertionSort` sortedness. -/
lemma sorted_sortDedupBy {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l : List α) :
    List.Sorted r (sortDedupBy r l) := by
  unfold sortDedupBy
  exact List.sorted_insertionSort r (l.dedup)

/-- `sortDedupBy` has the same length as `eraseDup`. -/
lemma length_sortDedupBy {α : Type} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] (l : List α) :
    (sortDedupBy r l).length = l.eraseDup.length := by
  unfold sortDedupBy
  rw [List.length_insertionSort, dedup_eq_eraseDup]

/-! ### `dedupSort` — deduplicate via Finset then sort by `≤` -/

/-- Sort a list after removing duplicates via Finset operations.
`dedupSort xs` converts `xs` to a `Finset` (eliminating duplicates), then sorts
the result in non-decreasing order using `Finset.sort (· ≤ ·)`.

Contrast with `sortDedupBy r` which uses `List.dedup` followed by `insertionSort r`
and works for any decidable relation `r`. `dedupSort` is specifically for `LinearOrder`
with the built-in `≤` ordering, but its nodup and sorted proofs are trivial one-liners
via Finset lemmas. -/
def dedupSort {α : Type u} [LinearOrder α] (xs : List α) : List α :=
  (xs.toFinset).sort (· ≤ ·)

/-- `dedupSort xs` has no duplicates. -/
theorem dedupSort_nodup {α : Type u} [LinearOrder α] (xs : List α) :
    Nodup (dedupSort xs) :=
  Finset.sort_nodup (· ≤ ·) (xs.toFinset)

/-- `dedupSort xs` is sorted in non-decreasing order by `≤`. -/
theorem dedupSort_sorted {α : Type u} [LinearOrder α] (xs : List α) :
    Sorted (· ≤ ·) (dedupSort xs) :=
  Finset.sort_sorted (· ≤ ·) (xs.toFinset)

/-! ### `insertionSort` membership and non-emptiness lemmas -/

/-- If a list is nonempty, its `insertionSort` is also nonempty.
This follows from `List.length_insertionSort` preserving length. -/
lemma insertionSort_ne_nil {α : Type _} (r : α → α → Prop) [DecidableRel r] (l : List α)
    (h : l ≠ []) : List.insertionSort r l ≠ [] := by
  intro h_nil
  have h_len := List.length_insertionSort r l
  have h_len_zero : (List.insertionSort r l).length = 0 := by simp [h_nil]
  rw [h_len] at h_len_zero
  exact h (List.length_eq_zero_iff.mp h_len_zero)

/-- `insertionSort` preserves `∀ a ∈ l, P a` properties.
If every element of `l` satisfies `P`, then every element of `insertionSort r l`
also satisfies `P`. -/
lemma insertionSort_preserves_forall {α : Type _} (r : α → α → Prop) [DecidableRel r] (P : α → Prop)
    (l : List α) (h : ∀ a ∈ l, P a) : ∀ a ∈ List.insertionSort r l, P a := by
  intro a ha
  exact h a ((List.mem_insertionSort r).mp ha)

/-- For any insertion-sorted list, the element at a valid index `i` (using `getElem!`) is a
member of the original list. This composes `List.get_mem` with `List.mem_insertionSort`. -/
lemma insertionSort_getElem_mem {α : Type} [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (l : List α) (i : Nat) (hi : i < (List.insertionSort r l).length) :
    (List.insertionSort r l)[i]! ∈ l := by
  have hmem_get : (List.insertionSort r l).get ⟨i, hi⟩ ∈ List.insertionSort r l :=
    List.get_mem _ ⟨i, hi⟩
  have hmem_orig : (List.insertionSort r l).get ⟨i, hi⟩ ∈ l :=
    ((List.mem_insertionSort r).mp hmem_get)
  have h_geteq : (List.insertionSort r l)[i]! = (List.insertionSort r l).get ⟨i, hi⟩ := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simpa [h_geteq] using hmem_orig

/-! ### Ordered insertion (LinearOrder) -/

/-- Insert `x` into `xs` (which is expected to be sorted by `(· ≤ ·)`), maintaining the
sorted order. This works for any `LinearOrder` type. -/
def insertSorted {α : Type u} [LinearOrder α] (x : α) : List α → List α
  | [] => [x]
  | (y :: ys) => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- `insertSorted` preserves the count of any element (as measured by filter length).
`insertSorted` is defined in `general.List`. -/
lemma insertSorted_count {α : Type} [LinearOrder α] [DecidableEq α] (x s : α) (l : List α) :
    ((insertSorted x l).filter (· = s)).length = ((x :: l).filter (· = s)).length := by
  induction l generalizing x with
  | nil => rfl
  | cons h t ih =>
    dsimp [insertSorted]
    split
    · rfl
    · rename_i hnle
      by_cases h_eq : h = s
      · rw [h_eq]
        by_cases x_eq : x = s
        · rw [x_eq]; simpa using ih s
        · simp [x_eq, ih x]
      · by_cases x_eq : x = s
        · rw [x_eq]; simp [h_eq, ih s]
        · simp [h_eq, x_eq, ih x]

/-! ### `mergeSort` with pair first-component comparator — transitivity, totality, sortedness -/

/-- Transitivity of comparison by first component via `decide`:
if `a.1 ≤ b.1` and `b.1 ≤ c.1`, then `a.1 ≤ c.1`.
This is the transitivity lemma needed by `List.sorted_mergeSort` when sorting
`α × β` pairs by their first component using `fun a b => a.1 ≤ b.1`. -/
lemma le_trans_comp {α β : Type} [LinearOrder α] (a b c : α × β) :
    (decide (a.1 ≤ b.1) = true) → (decide (b.1 ≤ c.1) = true) → (decide (a.1 ≤ c.1) = true) := by
  intro h1 h2
  have ha_le_b : a.1 ≤ b.1 := of_decide_eq_true h1
  have hb_le_c : b.1 ≤ c.1 := of_decide_eq_true h2
  have ha_le_c : a.1 ≤ c.1 := le_trans ha_le_b hb_le_c
  exact decide_eq_true ha_le_c

/-- Totality of comparison by first component via `decide`:
for any pairs `a, b`, either `a.1 ≤ b.1` or `b.1 ≤ a.1`.
This is the totality lemma needed by `List.sorted_mergeSort` when sorting
`α × β` pairs by their first component. -/
lemma le_total_comp {α β : Type} [LinearOrder α] (a b : α × β) :
    (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
  have h := le_total (a.1) (b.1)
  rcases h with (hle | hle)
  · have hdec : decide (a.1 ≤ b.1) = true := decide_eq_true hle
    rw [hdec]; simp
  · have hdec : decide (b.1 ≤ a.1) = true := decide_eq_true hle
    rw [hdec]; simp

/-- Sorting a list of `α × β` pairs by their first component via `mergeSort` and then projecting
the first components yields a `List.Pairwise (· ≤ ·)` result.
This is useful when you need to sort pairs by key and then extract the sorted keys. -/
lemma sorted_mergeSort_by_fst {α β : Type} [LinearOrder α] (pairs : List (α × β)) :
    List.Pairwise (· ≤ ·) (((pairs.mergeSort (fun a b => a.1 ≤ b.1))).map Prod.fst) := by
  let le : (α × β) → (α × β) → Bool := fun a b => a.1 ≤ b.1
  have h_sorted_pw : List.Pairwise (fun a b => le a b = true) (pairs.mergeSort le) :=
    List.sorted_mergeSort le_trans_comp le_total_comp pairs
  have h_pw_le : List.Pairwise (fun (a b : α × β) => a.1 ≤ b.1) (pairs.mergeSort le) :=
    List.Pairwise.imp (by
      intro a b h
      simpa [le] using of_decide_eq_true h
    ) h_sorted_pw
  have h_sorted : List.Pairwise (fun (x y : α) => x ≤ y) ((pairs.mergeSort le).map Prod.fst) :=
    List.Pairwise.map Prod.fst (by
      intro a b h
      exact h
    ) h_pw_le
  simpa [le] using h_sorted

/-! ### Extracting information from sorted lists -/

/-- If a sorted list starts with `a :: l` and `b ≤ a` with `b ∈ l`, then `b = a`.
This is a useful consequence of antisymmetry for sorted lists:
sortedness forces `a ≤ b` for every `b ∈ l`, so `b ≤ a` implies equality. -/
lemma sorted_mem_tail_le_head_eq {α : Type} [PartialOrder α] {a b : α} {l : List α}
    (h_sorted : List.Sorted (· ≤ ·) (a :: l)) (h_le : b ≤ a) (h_mem : b ∈ l) : b = a := by
  rw [List.sorted_cons] at h_sorted
  rcases h_sorted with ⟨h_all, _⟩
  have h_a_le_b : a ≤ b := h_all b h_mem
  exact le_antisymm h_le h_a_le_b

/-! ### Prepending to a sorted list -/

/-- If `l` is sorted by `≤` and `a` is `≤` every element of `l`, then `a :: l` is also sorted.
This is a convenient front for `List.sorted_cons`. It is the "prepend" dual of
`sorted_append_singleton`. -/
lemma sorted_cons_of_forall_le {α : Type} [Preorder α] {a : α} {l : List α}
    (h_sorted : List.Sorted (· ≤ ·) l) (h_le : ∀ x ∈ l, a ≤ x) :
    List.Sorted (· ≤ ·) (a :: l) := by
  rw [List.sorted_cons]
  exact ⟨h_le, h_sorted⟩

/-! ### Appending a singleton to a sorted list -/

/-- If `l` is sorted by `≤` and every element of `l` is `≤ m`, then `l ++ [m]` is also sorted.
This is a key lemma for building sorted lists by appending a maximum element. -/
lemma sorted_append_singleton {α : Type} [LE α] (l : List α) (m : α) (hsorted : List.Sorted (· ≤ ·) l)
    (hbound : ∀ x ∈ l, x ≤ m) : List.Sorted (· ≤ ·) (l ++ [m]) := by
  induction' l with a as IH generalizing m
  · simp [List.sorted_nil]
  · have ha_le_m : a ≤ m := hbound a (by simp)
    have hbound_as : ∀ x ∈ as, x ≤ m := by
      intro x hx; exact hbound x (List.mem_cons_of_mem a hx)
    simp [List.sorted_cons] at hsorted
    rcases hsorted with ⟨h_head, h_tail⟩
    have h_sorted_as_m : List.Sorted (· ≤ ·) (as ++ [m]) :=
      IH m h_tail hbound_as
    simp [List.sorted_cons]
    refine ⟨?_, h_sorted_as_m⟩
    intro b hb
    rcases hb with (hb_as | hb_m)
    · exact h_head b hb_as
    · subst hb_m; exact ha_le_m

/-! ### Sorted list to array: preserving ordering -/

/-- If `l` is sorted by `≤`, then its `Array` representation preserves the ordering:
for any `i < j` in bounds, `(l.toArray)[i]! ≤ (l.toArray)[j]!`.
This bridges the `List.Sorted` property to `Array` indexing. -/
lemma toArray_sorted {α : Type} [LE α] [Inhabited α] {l : List α} (h : List.Sorted (· ≤ ·) l) :
    ∀ i j, i < j → i < (List.toArray l).size → j < (List.toArray l).size →
    (List.toArray l)[i]! ≤ (List.toArray l)[j]! := by
  intro i j hij hi hj
  have hi_ls : i < l.length := by simpa using hi
  have hj_ls : j < l.length := by simpa using hj
  have h_get := ((List.pairwise_iff_getElem (R := (· ≤ ·)) (l := l)).mp h) i j hi_ls hj_ls hij
  have hi_arr : (List.toArray l)[i]! = l[i] := by simp [hi_ls]
  have hj_arr : (List.toArray l)[j]! = l[j] := by simp [hj_ls]
  rw [hi_arr, hj_arr]
  exact h_get

/-! ### `byFreqThenVal` — compare elements by frequency then value -/

/-- Compare two elements by their frequency in `lst` (ascending), then by their natural order.
This relation can be used with `insertionSort` (or any sorting algorithm requiring a total,
transitive relation) to sort a list by element frequency and then by value. -/
def byFreqThenVal (lst : List α) [DecidableEq α] [LinearOrder α] (a b : α) : Prop :=
  (lst.count a < lst.count b) ∨ (lst.count a = lst.count b ∧ a ≤ b)

instance instDecidableRelByFreqThenVal (lst : List α) [DecidableEq α] [LinearOrder α] :
    DecidableRel (byFreqThenVal lst) := by
  intro a b
  dsimp [byFreqThenVal]
  infer_instance

/-- The `byFreqThenVal` relation is total. Together with `byFreqThenVal_isTrans`, this
provides the `IsTotal` and `IsTrans` instances required by `insertionSort`. -/
lemma byFreqThenVal_isTotal {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) :
    IsTotal α (byFreqThenVal lst) := by
  refine ⟨?hTotal⟩
  intro a b
  dsimp [byFreqThenVal]
  by_cases hc : lst.count a < lst.count b
  · exact Or.inl (Or.inl hc)
  · have hge : lst.count b ≤ lst.count a := Nat.le_of_not_lt hc
    by_cases hclt : lst.count b < lst.count a
    · exact Or.inr (Or.inl hclt)
    · have heq : lst.count a = lst.count b := Nat.le_antisymm (Nat.le_of_not_lt hclt) hge
      by_cases hle : a ≤ b
      · exact Or.inl (Or.inr (And.intro heq hle))
      · have hle' : b ≤ a := le_of_not_le hle
        exact Or.inr (Or.inr (And.intro heq.symm hle'))

/-- The `byFreqThenVal` relation is transitive. Together with `byFreqThenVal_isTotal`, this
provides the `IsTotal` and `IsTrans` instances required by `insertionSort`. -/
lemma byFreqThenVal_isTrans {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) :
    IsTrans α (byFreqThenVal lst) := by
  refine ⟨?hTrans⟩
  intro a b c hab hbc
  dsimp [byFreqThenVal] at hab hbc ⊢
  rcases hab with (hlt | ⟨heq, hle⟩)
  · rcases hbc with (hlt2 | ⟨heq2, hle2⟩)
    · exact Or.inl (Nat.lt_trans hlt hlt2)
    · rw [heq2] at hlt
      exact Or.inl hlt
  · rcases hbc with (hlt2 | ⟨heq2, hle2⟩)
    · rw [heq]
      exact Or.inl hlt2
    · exact Or.inr (And.intro (heq.trans heq2) (le_trans hle hle2))

/-! ### `byFreqDescThenVal` — compare elements by frequency descending then value -/

/-- Compare two elements by their frequency in `lst` (descending), then by their natural order.
This is the descending dual of `byFreqThenVal`. Can be used with `insertionSort` (or any sorting
algorithm requiring a total, transitive relation) to sort a list by element frequency descending
and then by value. -/
def byFreqDescThenVal (lst : List α) [DecidableEq α] [LinearOrder α] (a b : α) : Prop :=
  (lst.count a > lst.count b) ∨ (lst.count a = lst.count b ∧ a ≤ b)

instance instDecidableRelByFreqDescThenVal (lst : List α) [DecidableEq α] [LinearOrder α] :
    DecidableRel (byFreqDescThenVal lst) := by
  intro a b
  dsimp [byFreqDescThenVal]
  infer_instance

/-- The `byFreqDescThenVal` relation is transitive. -/
lemma byFreqDescThenVal_isTrans {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) :
    IsTrans α (byFreqDescThenVal lst) := by
  refine ⟨?hTrans⟩
  intro a b c hab hbc
  dsimp [byFreqDescThenVal] at hab hbc ⊢
  rcases hab with (hgt | ⟨heq, hle⟩)
  · rcases hbc with (hgt2 | ⟨heq2, hle2⟩)
    · exact Or.inl (Nat.lt_trans hgt2 hgt)
    · rw [heq2] at hgt; exact Or.inl hgt
  · rcases hbc with (hgt2 | ⟨heq2, hle2⟩)
    · rw [← heq] at hgt2; exact Or.inl hgt2
    · exact Or.inr (And.intro (heq.trans heq2) (le_trans hle hle2))

/-- The `byFreqDescThenVal` relation is total. Together with `byFreqDescThenVal_isTrans`, this
provides the `IsTotal` and `IsTrans` instances required by `insertionSort`. -/
lemma byFreqDescThenVal_isTotal {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) :
    IsTotal α (byFreqDescThenVal lst) := by
  refine ⟨?hTotal⟩
  intro a b
  dsimp [byFreqDescThenVal]
  by_cases hc : lst.count a > lst.count b
  · exact Or.inl (Or.inl hc)
  · have hle : lst.count a ≤ lst.count b := Nat.le_of_not_gt hc
    by_cases hclt : lst.count b > lst.count a
    · exact Or.inr (Or.inl hclt)
    · have heq : lst.count a = lst.count b := Nat.le_antisymm hle (Nat.le_of_not_gt hclt)
      by_cases hle' : a ≤ b
      · exact Or.inl (Or.inr (And.intro heq hle'))
      · have hle'' : b ≤ a := le_of_not_le hle'
        exact Or.inr (Or.inr (And.intro heq.symm hle''))

/-! ### `byFreqThenValBool` — Bool comparator by frequency ascending then value

`byFreqThenVal` (above) is a `Prop` relation suitable for `insertionSort`.
`byFreqThenValBool` is its `Bool` counterpart suitable for `mergeSort`.
Both compare elements by their frequency in `lst` (ascending), then by `≤`. -/

/-- Boolean comparator: ascending by frequency in `lst` first, then by `≤`.
Returns `true` iff `a` should come before `b`. Suitable for `List.mergeSort`. -/
def byFreqThenValBool (lst : List α) [DecidableEq α] [LinearOrder α] (a b : α) : Bool :=
  let ca := lst.count a
  let cb := lst.count b
  if ca < cb then true
  else if cb < ca then false
  else decide (a ≤ b)

/-- `byFreqThenValBool lst a b = true` iff `byFreqThenVal lst a b`. -/
lemma byFreqThenValBool_eq_true_iff {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) (a b : α) :
    byFreqThenValBool lst a b = true ↔ byFreqThenVal lst a b := by
  unfold byFreqThenValBool byFreqThenVal
  by_cases hlt : lst.count a < lst.count b
  · simp [hlt]
  · by_cases hgt : lst.count b < lst.count a
    · have hne : lst.count a ≠ lst.count b := by omega
      simp [hlt, hgt, hne]
    · have heq : lst.count a = lst.count b := by omega
      simp [hlt, hgt, heq, decide_eq_true_iff]

/-- `byFreqThenValBool` is transitive. Suitable for `List.sorted_mergeSort`. -/
lemma byFreqThenValBool_trans {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) (a b c : α)
    (h1 : byFreqThenValBool lst a b = true) (h2 : byFreqThenValBool lst b c = true) :
    byFreqThenValBool lst a c = true := by
  have h1' : byFreqThenVal lst a b := (byFreqThenValBool_eq_true_iff lst a b).mp h1
  have h2' : byFreqThenVal lst b c := (byFreqThenValBool_eq_true_iff lst b c).mp h2
  have h_trans : IsTrans α (byFreqThenVal lst) := byFreqThenVal_isTrans lst
  have h_trans' : byFreqThenVal lst a c := h_trans.trans a b c h1' h2'
  exact (byFreqThenValBool_eq_true_iff lst a c).mpr h_trans'

/-- `byFreqThenValBool` is total. Suitable for `List.sorted_mergeSort`. -/
lemma byFreqThenValBool_total {α : Type u} [DecidableEq α] [LinearOrder α] (lst : List α) (a b : α) :
    (byFreqThenValBool lst a b || byFreqThenValBool lst b a) = true := by
  have h_total : IsTotal α (byFreqThenVal lst) := byFreqThenVal_isTotal lst
  have h_total' := h_total.total a b
  rcases h_total' with (h | h)
  · have hb : byFreqThenValBool lst a b = true := (byFreqThenValBool_eq_true_iff lst a b).mpr h
    simp [hb]
  · have hb : byFreqThenValBool lst b a = true := (byFreqThenValBool_eq_true_iff lst b a).mpr h
    simp [hb]

/-! ### Key-based descending insertion sort -/

/-- Sort a list by a key function in decreasing order using `insertionSort`.
The resulting list is sorted by `(fun a b => f a ≥ f b)`.

To obtain proofs about the sortedness, use `List.sorted_insertionSort` together with
`isTotal_ge_on` and `isTrans_ge_on` to provide the required `IsTotal` and `IsTrans` instances. -/
def sortByDecreasingKey {α β : Type _} [LinearOrder β] (f : α → β) (xs : List α) : List α :=
  List.insertionSort (fun a b => f a ≥ f b) xs

/-- For any function `f : α → β` into a `LinearOrder β`, the relation
`(fun a b => f a ≥ f b)` is total on `α`. Use as a `haveI` binder before calling
`List.insertionSort` or `List.sorted_insertionSort` with a key-based descending ordering. -/
lemma isTotal_ge_on {α β : Type _} (f : α → β) [LinearOrder β] : IsTotal α (fun a b => f a ≥ f b) :=
  ⟨fun a b => by
    have h := le_total (f a) (f b)
    rcases h with (hle | hle)
    · exact Or.inr hle
    · exact Or.inl hle⟩

/-- For any function `f : α → β` into a `LinearOrder β`, the relation
`(fun a b => f a ≥ f b)` is transitive on `α`. Use as a `haveI` binder before calling
`List.insertionSort` or `List.sorted_insertionSort` with a key-based descending ordering. -/
lemma isTrans_ge_on {α β : Type _} (f : α → β) [LinearOrder β] : IsTrans α (fun a b => f a ≥ f b) :=
  ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

/-! ### `SortedDesc` — inductive predicate for descending sortedness

`SortedDesc` provides a structural induction principle tailored for descending-sorted lists.
Unlike `Sorted (· ≥ ·)`, the `cons` constructor exposes the first two elements `a` and `b`,
making proofs about adjacent-element relations more direct. -/

/-- Inductive predicate for descending sortedness.
`sortedDesc.nil` covers the empty list, `sortedDesc.single a` covers `[a]`,
and `sortedDesc.cons a b l h hs` asserts that `a ≥ b` and `b :: l` is sorted descending. -/
inductive SortedDesc {α : Type} [LE α] : List α → Prop
  | nil : SortedDesc []
  | single (a : α) : SortedDesc [a]
  | cons (a b : α) (l : List α) (h : a ≥ b) (hs : SortedDesc (b :: l)) :
      SortedDesc (a :: b :: l)

/-- In a descending-sorted list `a :: l`, the head `a` is ≥ every element in `l`. -/
lemma sortedDesc_head_ge_all {α : Type} [LinearOrder α] {a : α} {l : List α}
    (h : SortedDesc (a :: l)) (x : α) (hx : x ∈ l) : a ≥ x := by
  cases h with
  | single a' => simp at hx
  | cons a' b' l' hab hs =>
    have hx_or : x = b' ∨ x ∈ l' := by simpa using hx
    rcases hx_or with (rfl | hx')
    · exact hab
    · have hb_ge_x : b' ≥ x := sortedDesc_head_ge_all hs x hx'
      exact le_trans hb_ge_x hab

/-- If a list satisfies `SortedDesc`, then for any indices `i < j` within bounds,
`l[i]! ≥ l[j]!`. This bridges the inductive `SortedDesc` predicate to the
element-access notation. -/
lemma sortedDesc_getElem_ge {α : Type} [LinearOrder α] [Inhabited α] (l : List α)
    (h : SortedDesc l) : ∀ i j, i < j → j < l.length → l[i]! ≥ l[j]! := by
  induction l with
  | nil => intro i j hij hj_len; exact absurd hj_len (Nat.not_lt_zero _)
  | cons hd tl ih =>
    intro i j hij hj_len
    simp at hj_len
    by_cases hi0 : i = 0
    · subst hi0
      simp
      have hj_pos : 0 < j := by omega
      rcases Nat.exists_eq_succ_of_ne_zero hj_pos.ne.symm with ⟨k, rfl⟩
      have hk_len : k < tl.length := by omega
      simp
      have h_ge : hd ≥ tl.get ⟨k, hk_len⟩ :=
        sortedDesc_head_ge_all h (tl.get ⟨k, hk_len⟩) (List.get_mem tl ⟨k, hk_len⟩)
      simpa [hk_len] using h_ge
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      rcases Nat.exists_eq_succ_of_ne_zero hi_pos.ne.symm with ⟨i', rfl⟩
      have hj_pos : 0 < j := by omega
      rcases Nat.exists_eq_succ_of_ne_zero hj_pos.ne.symm with ⟨j', rfl⟩
      simp
      have hi'_lt_j' : i' < j' := by omega
      have hi'_len : i' < tl.length := by omega
      have hj'_len : j' < tl.length := by omega
      match tl with
      | [] => exact absurd hi'_len (Nat.not_lt_zero _)
      | hd' :: tl' =>
        cases h with
        | cons _ _ _ _ hs =>
          simpa using ih hs i' j' hi'_lt_j' hj'_len

/-! ### `insertByFst` — insert a pair into a list sorted by first component

These provide insertion into a list sorted by the first component of pairs.
`insertByFst` uses `LinearOrder` on the key type directly (via `if x.1 ≤ a.1`), unlike
`insertBy` which uses a `cmp : α → α → Bool` comparator, and unlike `insertSorted` which
operates on a homogeneous type. This is useful for stability-based insertion sort on
key-value pairs. -/

/-- Insert a pair `x` into a list sorted by the first component (non-decreasing),
preserving the sorted order and stability (equal-key elements keep relative order).
Generalized over the key type (anything with a `LinearOrder`) and the value type. -/
def insertByFst {α β : Type} [LinearOrder α] (x : α × β) : List (α × β) → List (α × β)
  | [] => [x]
  | a :: as => if x.1 ≤ a.1 then x :: a :: as else a :: insertByFst x as

/-- `insertByFst x ys` is a permutation of `x :: ys`. -/
lemma insertByFst_perm {α β : Type} [LinearOrder α] (x : α × β) (ys : List (α × β)) :
    List.Perm (insertByFst x ys) (x :: ys) := by
  induction ys with
  | nil => simp [insertByFst]
  | cons head tail ih =>
    simp [insertByFst]
    split
    · rfl
    · have hcons : List.Perm (head :: insertByFst x tail) (head :: x :: tail) :=
        List.Perm.cons head ih
      have hswap : List.Perm (head :: x :: tail) (x :: head :: tail) :=
        List.Perm.swap x head tail
      exact List.Perm.trans hcons hswap

/-- If `xs` is a permutation of `ys`, then `x :: xs` is a permutation of `insertByFst x ys`. -/
lemma insertByFst_perm_cons_perm {α β : Type} [LinearOrder α] (x : α × β) (xs ys : List (α × β))
    (h : List.Perm xs ys) : List.Perm (x :: xs) (insertByFst x ys) :=
  List.Perm.trans (List.Perm.cons x h) (List.Perm.symm (insertByFst_perm x ys))

/-- If `a.1 ≤ x.1` and `a.1 ≤` every element of `as`, then `a.1 ≤` every element of
`insertByFst x as`. This is a key boundary lemma for sortedness proofs. -/
lemma insertByFst_all_ge {α β : Type} [LinearOrder α] {a x : α × β} {as : List (α × β)}
    (hax : a.1 ≤ x.1) (has : ∀ (b : α × β), b ∈ as → a.1 ≤ b.1) :
    ∀ (b : α × β), b ∈ insertByFst x as → a.1 ≤ b.1 := by
  induction as generalizing a x with
  | nil =>
    intro b hb
    simp [insertByFst] at hb
    subst hb
    exact hax
  | cons head tail ih =>
    have has_head : a.1 ≤ head.1 := has head (by simp)
    have has_tail : ∀ (c : α × β), c ∈ tail → a.1 ≤ c.1 := by
      intro c hc
      exact has c (List.mem_cons_of_mem head hc)
    intro b hb
    simp [insertByFst] at hb
    by_cases hcase : x.1 ≤ head.1
    · simp [hcase] at hb ⊢
      rcases hb with (rfl | hb')
      · exact hax
      · rcases hb' with (rfl | hb'')
        · exact has_head
        · exact has_tail b hb''
    · simp [hcase] at hb ⊢
      rcases hb with (rfl | hb')
      · exact has_head
      · have hhead_le_x : head.1 ≤ x.1 := le_of_lt (lt_of_not_ge hcase)
        have hax' : a.1 ≤ x.1 := le_trans has_head hhead_le_x
        exact ih hax' has_tail b hb'

/-- `insertByFst` preserves sortedness: if `ys` is sorted by first component,
then `insertByFst x ys` is also sorted by first component. -/
lemma insertByFst_sorted {α β : Type} [LinearOrder α] (x : α × β) (ys : List (α × β))
    (h : List.Sorted (fun a b : α × β => a.1 ≤ b.1) ys) :
    List.Sorted (fun a b : α × β => a.1 ≤ b.1) (insertByFst x ys) := by
  induction ys generalizing x with
  | nil =>
    unfold insertByFst
    exact List.sorted_singleton x
  | cons head tail ih =>
    rcases (List.sorted_cons.mp h) with ⟨ha_all, has⟩
    dsimp [insertByFst]
    by_cases hcase : x.1 ≤ head.1
    · simp [hcase]
      have hx_all : ∀ (a : α) (s : β), (a, s) ∈ tail → x.1 ≤ a := by
        intro a s ha_mem
        exact le_trans hcase (ha_all (a, s) ha_mem)
      have ha_all' : ∀ (a : α) (s : β), (a, s) ∈ tail → head.1 ≤ a := by
        intro a s ha_mem
        exact ha_all (a, s) ha_mem
      exact ⟨hx_all, ha_all', has⟩
    · simp [hcase]
      have hhead_le_x : head.1 ≤ x.1 := le_of_lt (lt_of_not_ge hcase)
      have hge : ∀ (a : α) (s : β), (a, s) ∈ insertByFst x tail → head.1 ≤ a := by
        intro a s ha_mem
        exact insertByFst_all_ge hhead_le_x ha_all (a, s) ha_mem
      constructor
      · exact hge
      · exact ih x has

/-- Filtering `insertByFst x ys` by a key `k` gives `[x] ++ ys.filter (·.1 = k)` if `x.1 = k`,
or just `ys.filter (·.1 = k)` otherwise. This is the key lemma for stability proofs:
elements with the same key maintain their relative order. -/
lemma insertByFst_filter_eq {α β : Type} [LinearOrder α] (x : α × β) (ys : List (α × β)) (k : α) :
    (insertByFst x ys).filter (fun p => p.1 = k) =
    (if x.1 = k then [x] else []) ++ ys.filter (fun p => p.1 = k) := by
  induction ys generalizing x k with
  | nil =>
    unfold insertByFst
    by_cases h : x.1 = k
    · simp [h]
    · simp [h]
  | cons head tail ih =>
    dsimp [insertByFst]
    by_cases hcase : x.1 ≤ head.1
    · simp [hcase]
      by_cases hx_eq : x.1 = k
      · simp [hx_eq]
      · simp [hx_eq]
    · simp [hcase]
      simp only [List.filter_cons]
      rw [ih x k]
      by_cases hhead_eq : head.1 = k
      · simp [hhead_eq]
        by_cases hx_eq : x.1 = k
        · exfalso
          apply hcase
          rw [hx_eq, hhead_eq]
        · simp [hx_eq]
      · simp [hhead_eq]

/-- If `ys` and `xs` agree when filtered by key `k`, then `insertByFst x ys` and `x :: xs`
also agree when filtered by key `k`. This is used in inductive stability proofs for
insertion sort on pairs. -/
lemma insertByFst_filter_cons {α β : Type} [LinearOrder α] (x : α × β) (xs ys : List (α × β)) (k : α)
    (h_filter : ys.filter (fun p => p.1 = k) = xs.filter (fun p => p.1 = k)) :
    (insertByFst x ys).filter (fun p => p.1 = k) = (x :: xs).filter (fun p => p.1 = k) := by
  rw [insertByFst_filter_eq x ys k]
  rw [h_filter]
  simp only [List.filter_cons]
  by_cases hx_eq : x.1 = k
  · simp [hx_eq]
  · simp [hx_eq]

/-! ### `pairwise_map_fst` and `sorted_map_fst` — project sorted pairs to sorted first components -/

/-- If a list of pairs is pairwise-related by a relation on the first components, then
mapping to first components preserves the pairwise property. -/
theorem pairwise_map_fst {α β : Type} {R : α → α → Prop} {l : List (α × β)}
    (h : List.Pairwise (fun (p q : α × β) => R p.1 q.1) l) : List.Pairwise R (l.map Prod.fst) :=
  h.map (f := Prod.fst) (fun _ _ hpq => hpq)

/-- If a list of pairs is sorted by the first component, then mapping to first components
yields a sorted list. -/
theorem sorted_map_fst {α β : Type} {R : α → α → Prop} {l : List (α × β)}
    (h : List.Sorted (fun (p q : α × β) => R p.1 q.1) l) : List.Sorted R (l.map Prod.fst) :=
  pairwise_map_fst h

/-! ### `sortPairsByFst` — sort pairs by first component using `insertionSort` -/

/-- Sort a list of pairs by the first component using `insertionSort`.
This is a stable sort: pairs with equal first components retain their relative order.
Uses the `fstLE` relation and its `IsTotal`/`IsTrans` instances from `general.Pair`. -/
def sortPairsByFst {α β : Type} [LinearOrder α] (l : List (α × β)) : List (α × β) :=
  List.insertionSort fstLE l

/-- `sortPairsByFst l` is a permutation of `l`. -/
lemma sortPairsByFst_perm {α β : Type} [LinearOrder α] (l : List (α × β)) :
    List.Perm (sortPairsByFst l) l := by
  unfold sortPairsByFst
  exact List.perm_insertionSort fstLE l

/-- `sortPairsByFst` produces a list sorted by `fstLE` (i.e., by the first component). -/
lemma sortPairsByFst_sorted {α β : Type} [LinearOrder α] (l : List (α × β)) :
    List.Sorted fstLE (sortPairsByFst l) :=
  List.sorted_insertionSort fstLE l

/-- If a list of pairs is sorted by `fstLE`, then mapping to first components yields
a list sorted by `(· ≤ ·)`. -/
lemma sortPairsByFst_sorted_map_fst {α β : Type} [LinearOrder α] (l : List (α × β)) :
    List.Sorted (· ≤ ·) ((sortPairsByFst l).map Prod.fst) := by
  have h_sorted : List.Sorted fstLE (sortPairsByFst l) := sortPairsByFst_sorted l
  exact sorted_map_fst h_sorted

/-! ### `sortPairsBySnd` — sort pairs by second component using `insertionSort` -/

/-- Sort a list of pairs by the second component using `insertionSort`.
This is a stable sort: pairs with equal second components retain their relative order.
Uses the `sndLE` relation and its `IsTotal`/`IsTrans` instances from `general.Pair`. -/
def sortPairsBySnd {α β : Type} [LE β] [DecidableRel (· ≤ · : β → β → Prop)] (l : List (α × β)) : List (α × β) :=
  List.insertionSort (sndLE (α := α) (β := β)) l

/-- `sortPairsBySnd l` is a permutation of `l`. -/
lemma sortPairsBySnd_perm {α β : Type} [LE β] [DecidableRel (· ≤ · : β → β → Prop)] (l : List (α × β)) :
    List.Perm (sortPairsBySnd l) l := by
  unfold sortPairsBySnd
  exact List.perm_insertionSort (sndLE (α := α) (β := β)) l

/-- `sortPairsBySnd` produces a list sorted by `sndLE` (i.e., by the second component). -/
lemma sortPairsBySnd_sorted {α β : Type} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    [IsTotal β (· ≤ ·)] [IsTrans β (· ≤ ·)] (l : List (α × β)) :
    List.Sorted (sndLE (α := α) (β := β)) (sortPairsBySnd l) :=
  List.sorted_insertionSort (sndLE (α := α) (β := β)) l

/-- If every element of `l` is `≥ x` and `y < x`, then `y` is not a member of `l`.
This is useful for reasoning about lower bounds in sorted lists. -/
lemma not_mem_of_lt_of_forall_le {α : Type} [PartialOrder α] {x y : α} {l : List α}
    (h_forall : ∀ a ∈ l, x ≤ a) (h_lt : y < x) : y ∉ l := by
  intro h
  have hx_le := h_forall y h
  have : y < y := lt_of_lt_of_le h_lt hx_le
  exact lt_irrefl _ this

/-! ### `insertByKey` and `sortInsertByKey` — key-based insertion sort

These provide insertion sort parameterized by a key function `key : α → β` into any
`LinearOrder β`. Unlike `insertBy`/`sortBy` which use a `Bool` comparator, these use the
natural ordering on the key type, making them more convenient for sorting by a projection
(e.g., `sortInsertByKey (fun p => p.1) pairs` to sort pairs by first component). -/

/-- Insert `x` into a list sorted by a key function, preserving the order. -/
def insertByKey {α β : Type} [LinearOrder β] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if key x ≤ key y then x :: y :: ys
    else y :: insertByKey key x ys

/-- Sort a list in non-decreasing order by a key function using insertion sort.
See also `sortByKey` in `general.List` for a foldl-based version specialized to `Nat` keys. -/
def sortInsertByKey {α β : Type} [LinearOrder β] (key : α → β) : List α → List α
  | [] => []
  | x :: xs => insertByKey key x (sortInsertByKey key xs)

/-! ### Membership lemmas for `insertByKey` and `sortInsertByKey` -/

/-- Membership in `insertByKey key x ys` is equivalent to `z = x ∨ z ∈ ys`. -/
lemma mem_insertByKey {α β : Type} [LinearOrder β] (key : α → β) (x z : α) (ys : List α) :
    z ∈ insertByKey key x ys ↔ z = x ∨ z ∈ ys := by
  induction ys with
  | nil => simp [insertByKey]
  | cons y ys' ih =>
    simp [insertByKey]
    split
    · simp [List.mem_cons, ih]
    · simp [List.mem_cons, ih]; tauto

/-- Membership in `sortInsertByKey key l` is equivalent to membership in `l`. -/
lemma mem_sortInsertByKey {α β : Type} [LinearOrder β] (key : α → β) (l : List α) (w : α) :
    w ∈ sortInsertByKey key l ↔ w ∈ l := by
  induction l with
  | nil => simp [sortInsertByKey]
  | cons x xs IH =>
    simp [sortInsertByKey, mem_insertByKey, IH]

/-! ### Permutation lemmas for `insertByKey` and `sortInsertByKey` -/

/-- Inserting an element via `insertByKey` yields a permutation of `x :: ys`. -/
lemma insertByKey_perm {α β : Type} [LinearOrder β] (key : α → β) (x : α) (ys : List α) :
    (insertByKey key x ys).Perm (x :: ys) := by
  induction ys with
  | nil => simp [insertByKey]
  | cons y ys' ih =>
    simp [insertByKey]
    split
    · rfl
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys')

/-- `sortInsertByKey` returns a permutation of the input list. -/
lemma sortInsertByKey_perm {α β : Type} [LinearOrder β] (key : α → β) (xs : List α) :
    (sortInsertByKey key xs).Perm xs := by
  induction xs with
  | nil => simp [sortInsertByKey]
  | cons x xs' ih =>
    simp [sortInsertByKey]
    have h := insertByKey_perm key x (sortInsertByKey key xs')
    exact h.trans (List.Perm.cons x ih)

/-! ### Length lemmas for `insertByKey` and `sortInsertByKey` -/

/-- Inserting an element via `insertByKey` adds exactly one to the list length. -/
lemma insertByKey_length {α β : Type} [LinearOrder β] (key : α → β) (x : α) (l : List α) :
    (insertByKey key x l).length = l.length + 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons y ys ih =>
    unfold insertByKey
    split <;> simp [ih]

/-- Sorting a list with `sortInsertByKey` preserves the list length. -/
lemma sortInsertByKey_length {α β : Type} [LinearOrder β] (key : α → β) (l : List α) :
    (sortInsertByKey key l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold sortInsertByKey
    rw [insertByKey_length key x (sortInsertByKey key xs)]
    simp [ih]

/-! ### `Pairwise` lemmas for `insertByKey` and `sortInsertByKey` -/

/-- If `ys` is pairwise ordered by `(fun a b => key a ≤ key b)`, then inserting `x`
via `insertByKey key` preserves this pairwise ordering. -/
lemma insertByKey_pairwise {α β : Type} [LinearOrder β] (key : α → β) (x : α) (ys : List α)
    (h : List.Pairwise (fun a b => key a ≤ key b) ys) :
    List.Pairwise (fun a b => key a ≤ key b) (insertByKey key x ys) := by
  induction ys with
  | nil => simp [insertByKey]
  | cons y ys' ih =>
    simp [insertByKey]
    rcases List.pairwise_cons.mp h with ⟨hforall, hpair⟩
    split
    · -- key x ≤ key y
      next hle =>
        refine List.Pairwise.cons ?_ h
        intro z hz
        rcases List.mem_cons.mp hz with (rfl | hz')
        · exact hle
        · have h_yz : key y ≤ key z := hforall z hz'
          exact le_trans hle h_yz
    · -- key y < key x
      next h_notle =>
        have h_lt : key y ≤ key x := le_of_lt (lt_of_not_ge h_notle)
        refine List.Pairwise.cons ?_ (ih hpair)
        intro z hz
        rw [mem_insertByKey key] at hz
        rcases hz with (rfl | hz')
        · exact h_lt
        · exact hforall z hz'

/-- `sortInsertByKey key xs` is pairwise ordered by `(fun a b => key a ≤ key b)`. -/
lemma sortInsertByKey_pairwise {α β : Type} [LinearOrder β] (key : α → β) (xs : List α) :
    List.Pairwise (fun a b => key a ≤ key b) (sortInsertByKey key xs) := by
  induction xs with
  | nil => simp [sortInsertByKey]
  | cons x xs' ih =>
    simp [sortInsertByKey]
    exact insertByKey_pairwise key x (sortInsertByKey key xs') ih

/-! ### Lower-bound preservation for `insertByKey` -/

/-- If `key t ≤ key x` and `key t ≤ key u` for every `u ∈ l`, then the same holds
for every element of `insertByKey key x l`. This is a lower-bound preservation lemma:
if `t` is a lower bound of both `x` and every element already in `l`, it remains
a lower bound after inserting `x`. Often used as a helper in pairwise/sortedness proofs. -/
lemma insertByKey_bound {α β : Type} [LinearOrder β] (key : α → β) (t x : α) (l : List α)
    (htx : key t ≤ key x) (hall : ∀ u ∈ l, key t ≤ key u) :
    ∀ u ∈ insertByKey key x l, key t ≤ key u := by
  induction l generalizing t x with
  | nil =>
    simp [insertByKey, htx]
  | cons a as IH =>
    have hta : key t ≤ key a := hall a (by simp)
    have has : ∀ u ∈ as, key t ≤ key u := by
      intro u hu; exact hall u (List.mem_cons_of_mem a hu)
    simp [insertByKey]
    split
    · intro u hu
      rcases List.mem_cons.mp hu with (rfl | hu')
      · exact htx
      · rcases List.mem_cons.mp hu' with (rfl | hu_as)
        · exact hta
        · exact has u hu_as
    · intro u hu
      rcases List.mem_cons.mp hu with (rfl | hu)
      · exact hta
      · exact IH t x htx has u hu

/-! ### `foldl` with `insertByKey` theorems

These describe the result of folding `insertByKey key` over a list `xs` starting from
an accumulator `acc`. This is a common pattern: `xs.foldl (fun acc' x => insertByKey key x acc') acc`,
used when the sorted order is built incrementally via repeated insertions. -/

/-- Folding `insertByKey` over `xs` starting from `acc` gives a list of length
`xs.length + acc.length`. -/
lemma foldl_insertByKey_length {α β : Type} [LinearOrder β] (key : α → β) (xs acc : List α) :
    ((xs.foldl (fun acc' x => insertByKey key x acc') acc)).length =
    xs.length + acc.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    rw [ih (insertByKey key x acc), insertByKey_length key x acc]
    omega

/-- Folding `insertByKey` over `xs` starting from `acc`: `t` is in the result iff
it is in `xs` or `acc`. -/
lemma foldl_insertByKey_mem {α β : Type} [LinearOrder β] (key : α → β) (xs acc : List α) (t : α) :
    (t ∈ (xs.foldl (fun acc' x => insertByKey key x acc') acc)) ↔
    t ∈ xs ∨ t ∈ acc := by
  induction xs generalizing acc t with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl]
    rw [ih (insertByKey key x acc) t, mem_insertByKey key x t acc]
    tauto

/-- Folding `insertByKey` over `xs` preserves the pairwise sorted-by-`key` invariant
of the accumulator. -/
lemma foldl_insertByKey_pairwise {α β : Type} [LinearOrder β] (key : α → β) (xs acc : List α)
    (h_sorted : List.Pairwise (fun a b => key a ≤ key b) acc) :
    List.Pairwise (fun a b => key a ≤ key b)
      (xs.foldl (fun acc' x => insertByKey key x acc') acc) := by
  induction xs generalizing acc with
  | nil => exact h_sorted
  | cons x xs ih =>
    simp [List.foldl]
    apply ih
    exact insertByKey_pairwise key x acc h_sorted

/-! ### `sorted_perm_minimal` — sorted permutation is lexicographically minimal

If a list is `Pairwise (· ≤ ·)` and is a permutation of another list, then it is
`≤` the other list in the lexicographic list order. In other words, the sorted
permutation is the lexicographically minimal permutation. -/

/-- If `l₁` is sorted by `(· ≤ ·)` and is a permutation of `l₂`, then `l₁ ≤ l₂`
in the lexicographic list order. That is, the sorted permutation is the
lexicographically minimal permutation of a multiset. -/
lemma sorted_perm_minimal [LinearOrder α] {l₁ l₂ : List α}
    (hsorted : List.Pairwise (· ≤ ·) l₁) (hperm : l₁.Perm l₂) : l₁ ≤ l₂ := by
  by_contra! hlt
  -- hlt : l₂ < l₁
  have hlex : List.Lex (· < ·) l₂ l₁ := by
    rw [← List.lt_iff_lex_lt]; exact hlt
  induction l₁ generalizing l₂ with
  | nil =>
    cases hlex
  | cons a l₁' ih =>
    rcases List.pairwise_cons.mp hsorted with ⟨ha_le_l₁', hsorted'⟩
    cases l₂ with
    | nil =>
      have hlen := List.Perm.length_eq hperm
      simp at hlen
    | cons b l₂' =>
      have hperm' : (a :: l₁').Perm (b :: l₂') := hperm
      match hlex with
      | List.Lex.rel hlt_ab =>
        -- b < a contradicts that a ≤ every element of l₁' (and thus a ≤ b via perm)
        have hb_mem : b ∈ a :: l₁' := by
          have mem_b : b ∈ b :: l₂' := by simp
          exact (List.Perm.mem_iff hperm').mpr mem_b
        have hb_cases : b = a ∨ b ∈ l₁' := by simpa using hb_mem
        rcases hb_cases with (hb_eq | hb_l₁')
        · rw [hb_eq] at hlt_ab; exact lt_irrefl a hlt_ab
        · have ha_le_b : a ≤ b := ha_le_l₁' b hb_l₁'
          have : b < b := lt_of_lt_of_le hlt_ab ha_le_b
          exact lt_irrefl b this
      | List.Lex.cons hlex' =>
        -- a = b, and l₂' < l₁'; apply induction hypothesis on tails
        have h_cons_inv : l₁'.Perm l₂' := List.Perm.cons_inv hperm'
        have hlt_l₂'_l₁' : l₂' < l₁' :=
          (List.lt_iff_lex_lt l₂' l₁').mpr hlex'
        exact ih hsorted' h_cons_inv hlt_l₂'_l₁' hlex'

/-! ### `PermSorted` — a permutation that is sorted by `r`

`PermSorted r xs result` combines two properties:
1. `result` is a permutation of `xs`
2. `result` is sorted by the relation `r`

This is the natural specification for a correct sorting algorithm:
the output must contain exactly the elements of the input (permutation)
and be sorted by the desired relation. -/

/-- `result` is a permutation of `xs` that is sorted by relation `r`.
This is the canonical combined spec for sorting correctness. -/
def PermSorted {α : Type u} (r : α → α → Prop) (xs result : List α) : Prop :=
  List.Perm xs result ∧ List.Sorted r result

/-- For a total, transitive, decidable relation `r`,
`mergeSort` with the `decide`-wrapped comparator `fun x y => decide (r x y)`
produces a `PermSorted` result — i.e., the output is both a permutation of the input
and sorted by `r`.

This packages `List.mergeSort_perm` and `List.sorted_mergeSort'` into a single
lemma matching the `PermSorted` specification. -/
theorem mergeSort_perm_sorted {α : Type u} (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] (xs : List α) :
    PermSorted r xs (xs.mergeSort (fun x y => decide (r x y))) := by
  unfold PermSorted
  constructor
  · have h := List.mergeSort_perm xs (fun x y => decide (r x y))
    exact h.symm
  · exact List.sorted_mergeSort' r xs

/-! ### `take_pairwise_le_dominates` — prefix domination in a pairwise-sorted list

If a list is `Pairwise`-sorted by a projection `f : α → β` (non-decreasing), then for any
element `x` in the list and any element `y` in the first `k` elements, either `f y ≤ f x`
or `x` itself is among the first `k` elements.

This is useful for greedy algorithms that pick the first `k` elements from a sorted list
and need to argue that unpicked elements are no better than the picked ones. -/

lemma take_pairwise_le_dominates {α β : Type u} [LinearOrder β] (f : α → β) (l : List α)
    (hp : List.Pairwise (fun a b : α => f a ≤ f b) l) (k : Nat) :
    ∀ x ∈ l, ∀ y ∈ l.take k, f y ≤ f x ∨ x ∈ l.take k := by
  induction l generalizing k with
  | nil => simp
  | cons a as ih =>
    rcases List.pairwise_cons.mp hp with ⟨ha_le_as, hp_as⟩
    intro x hx
    rcases List.mem_cons.mp hx with (hx_eq | hx_as)
    · subst hx_eq
      intro y hy
      cases' k with k
      · simp at hy
      · simp [List.take] at hy
        rcases hy with (hy_eq | hy')
        · subst hy_eq; exact Or.inr (by simp)
        · exact Or.inr (by simp)
    · intro y hy
      cases' k with k
      · simp at hy
      · simp [List.take] at hy
        rcases hy with (hy_eq | hy_take)
        · subst hy_eq; exact Or.inl (ha_le_as x hx_as)
        · have h_ih := ih hp_as k x hx_as y hy_take
          rcases h_ih with (hle | hmem)
          · exact Or.inl hle
          · exact Or.inr (List.mem_cons_of_mem _ hmem)

/-! ### `insertSortedRel` and `sortedRel` — generic insertion sort with a `Prop` relation

These are the `Prop`-relation counterparts of the `Bool`-based `insertBy`/`sortBy`.
`insertSortedRel r` inserts an element while preserving ordering by the decidable `Prop`
relation `r`. `sortedRel r` recursively sorts a list via insertion sort.

Unlike the `LinearOrder`-based `insertSorted` in `general.List` (which uses `≤`),
this version is parameterized by any decidable `Prop` relation `r : α → α → Prop`.
The `Rel` suffix distinguishes it from the `LinearOrder`-based version. -/

section InsertSortRel

universe u
variable {α : Type u}

/-- Insert `x` into `xs` such that if `xs` is already sorted by `r`,
    then `insertSortedRel r x xs` will also be sorted by `r`. -/
def insertSortedRel (r : α → α → Prop) [DecidableRel r] (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    if r x y then
      x :: y :: ys
    else
      y :: insertSortedRel r x ys

/-- Sort `xs` by insertion sort using the relation `r`. -/
def sortedRel (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | x :: xs' => insertSortedRel r x (sortedRel r xs')

/-- Inserting an element preserves the multiset of elements. -/
lemma insertSortedRel_perm (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    List.Perm (insertSortedRel r x xs) (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [insertSortedRel]
  | cons y ys IH =>
    simp [insertSortedRel]
    split
    · rfl
    · have h_cons : List.Perm (y :: insertSortedRel r x ys) (y :: x :: ys) :=
        List.Perm.cons y (IH x)
      have h_swap : List.Perm (y :: x :: ys) (x :: y :: ys) :=
        List.Perm.swap x y ys
      exact List.Perm.trans h_cons h_swap

/-- Sorting a list by insertion preserves the multiset of elements. -/
lemma sortedRel_perm (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    List.Perm (sortedRel r xs) xs := by
  induction xs with
  | nil => simp [sortedRel]
  | cons x ys IH =>
    simp [sortedRel]
    have h_insert : List.Perm (insertSortedRel r x (sortedRel r ys)) (x :: sortedRel r ys) :=
      insertSortedRel_perm r x (sortedRel r ys)
    have h_cons : List.Perm (x :: sortedRel r ys) (x :: ys) :=
      List.Perm.cons x IH
    exact List.Perm.trans h_insert h_cons

/-- If `r a x` and `r a b` for all `b ∈ as`, then `r a b` for all `b ∈ insertSortedRel r x as`.
    No additional properties of `r` (transitivity, etc.) are needed. -/
lemma insertSortedRel_bound (r : α → α → Prop) [DecidableRel r] {a x : α} {as : List α}
    (hx : r a x) (has : ∀ b ∈ as, r a b) :
    ∀ b ∈ insertSortedRel r x as, r a b := by
  induction as with
  | nil =>
    intro b hb
    unfold insertSortedRel at hb
    rcases List.mem_singleton.mp hb with rfl
    exact hx
  | cons h t ih =>
    have hh : r a h := has h (by simp)
    have ht : ∀ b ∈ t, r a b := by
      intro b hb
      exact has b (List.mem_cons_of_mem h hb)
    intro b hb
    unfold insertSortedRel at hb
    split at hb
    · rcases List.mem_cons.mp hb with (rfl | hb')
      · exact hx
      · rcases List.mem_cons.mp hb' with (rfl | hb'')
        · exact hh
        · exact ht b hb''
    · rcases List.mem_cons.mp hb with (rfl | hb')
      · exact hh
      · exact ih ht b hb'

/-- If `xs` is pairwise ordered by `r`, and `r` is transitive and total
    (`IsTrans` and `IsTotal`), then `insertSortedRel r x xs` is also
    pairwise ordered by `r`. -/
lemma insertSortedRel_pairwise (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α)
    (h : List.Pairwise r xs)
    [IsTrans α r] [IsTotal α r] :
    List.Pairwise r (insertSortedRel r x xs) := by
  induction xs generalizing x with
  | nil => simp [insertSortedRel]
  | cons z zs IH =>
    rcases List.pairwise_cons.mp h with ⟨hz_all, h_zs⟩
    unfold insertSortedRel
    split
    · rename_i hle
      have h_all_x : ∀ b ∈ (z :: zs), r x b := by
        intro b hb
        rcases List.mem_cons.mp hb with (rfl | hb_zs)
        · exact hle
        · have hz_b : r z b := hz_all b hb_zs
          exact IsTrans.trans (a := x) (b := z) (c := b) hle hz_b
      refine List.Pairwise.cons h_all_x (List.Pairwise.cons hz_all h_zs)
    · rename_i hnle
      have hz_x : r z x := by
        rcases IsTotal.total (r := r) z x with (h_zx | h_xz)
        · exact h_zx
        · exact (hnle h_xz).elim
      have h_all_z : ∀ b ∈ insertSortedRel r x zs, r z b :=
        insertSortedRel_bound r hz_x hz_all
      refine List.Pairwise.cons h_all_z (IH x h_zs)

/-- If `r` is transitive and total (`IsTrans` and `IsTotal`),
    then `sortedRel r xs` is pairwise ordered by `r`. -/
lemma sortedRel_pairwise (r : α → α → Prop) [DecidableRel r] (xs : List α)
    [IsTrans α r] [IsTotal α r] :
    List.Pairwise r (sortedRel r xs) := by
  induction xs with
  | nil => simp [sortedRel]
  | cons x ys IH =>
    simp [sortedRel]
    exact insertSortedRel_pairwise r x (sortedRel r ys) IH

end InsertSortRel

end List

namespace List

/-! ### General `Pairwise` with Bool relations

For lists that are `Pairwise`-sorted by a Bool-valued comparison `le` (commonly from
`List.mergeSort` with a `Bool` comparator), this lemma bridges the `Pairwise` condition
to statements about elements at specific indices via `get`.

It generalizes the pattern
`(List.pairwise_iff_get.mp h) i j hij`
into a named lemma for readability and reuse. -/

/--
Given `List.Pairwise (fun a b => le a b = true) l`,
the `le` relation holds for elements accessed by `Fin` indices in order.
-/
lemma pairwiseBool_get {α : Type _} {le : α → α → Bool} {l : List α}
    (h : List.Pairwise (fun a b => le a b = true) l)
    (i j : Fin l.length) (hij : i < j) : le (l.get i) (l.get j) = true :=
  (List.pairwise_iff_get.mp h) i j hij

/-! ### `sortedDesc` — descending sortedness via `Pairwise`

`sortedDesc xs` means `xs` is sorted in nonincreasing (descending) order: every
consecutive pair `(a, b)` satisfies `a ≥ b`.

This is the `Pairwise`-based counterpart of the inductive `SortedDesc` (defined in
`general.List.Sort`). Use `sortedDesc` for proofs involving `List.Pairwise` infrastructure;
use `SortedDesc` for structural induction on the shape of the sorted list. -/

/-- A list is sorted in nonincreasing (descending) order if every consecutive pair
`(a, b)` satisfies `a ≥ b`. Defined via `List.Pairwise`. -/
def sortedDesc {α : Type u} [LE α] (xs : List α) : Prop :=
  xs.Pairwise (fun a b => a ≥ b)

/-- Insert `x` into a list expected to be sorted in descending order. -/
def insertSortedDesc {α : Type u} [LinearOrder α] (x : α) : List α → List α
  | [] => [x]
  | a :: as =>
    if x ≥ a then x :: a :: as
    else a :: insertSortedDesc x as

/-- Sort a list in descending order using insertion sort. -/
def sortDesc {α : Type u} [LinearOrder α] : List α → List α
  | [] => []
  | a :: as => insertSortedDesc a (sortDesc as)

/-! ### Membership lemmas for `insertSortedDesc` and `sortDesc` -/

lemma insertSortedDesc_mem {α : Type u} [LinearOrder α] (x y : α) (xs : List α) :
    y ∈ insertSortedDesc x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertSortedDesc]
  | cons a as IH =>
    simp [insertSortedDesc]
    split
    · simp [IH]
    · simp [IH, or_assoc, or_comm, or_left_comm]

lemma sortDesc_mem {α : Type u} [LinearOrder α] (lst : List α) (x : α) :
    x ∈ sortDesc lst ↔ x ∈ lst := by
  induction lst with
  | nil => simp [sortDesc]
  | cons a as IH =>
    simp [sortDesc, insertSortedDesc_mem, IH]

/-! ### Perm lemmas for `insertSortedDesc` and `sortDesc` -/

/-- Inserting an element via `insertSortedDesc` yields a list that is a permutation of `x :: xs`.
In other words, `insertSortedDesc` preserves the multiset of elements
(it just rearranges them into descending sorted position). -/
lemma insertSortedDesc_perm {α : Type u} [LinearOrder α] (x : α) (xs : List α) :
    List.Perm (insertSortedDesc x xs) (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [insertSortedDesc]
  | cons a as IH =>
    simp [insertSortedDesc]
    split
    · rfl
    · have h : List.Perm (a :: insertSortedDesc x as) (a :: x :: as) :=
        List.Perm.cons a (IH x)
      have hswap : List.Perm (a :: x :: as) (x :: a :: as) :=
        List.Perm.swap x a as
      exact List.Perm.trans h hswap

/-- Sorting a list in descending order via `sortDesc` returns a permutation of the input list.
Sorting rearranges elements but does not add or remove any. -/
lemma sortDesc_perm {α : Type u} [LinearOrder α] (l : List α) :
    List.Perm (sortDesc l) l := by
  induction l with
  | nil => simp [sortDesc]
  | cons x xs IH =>
    simp [sortDesc]
    have h_insert : List.Perm (insertSortedDesc x (sortDesc xs)) (x :: sortDesc xs) :=
      insertSortedDesc_perm x (sortDesc xs)
    have h_cons : List.Perm (x :: sortDesc xs) (x :: xs) :=
      List.Perm.cons x IH
    exact List.Perm.trans h_insert h_cons

/-! ### Boundary lemma for `insertSortedDesc` -/

/-- If `a ≥ x` and `a` is ≥ every element of `as`, then after inserting `x` into `as`,
`a` remains ≥ every element of the result. This is the key lemma for proving
`insertSortedDesc_sortedDesc`. -/
lemma insertSortedDesc_bound {α : Type u} [LinearOrder α] {a x : α} {as : List α}
    (hx : a ≥ x) (has : ∀ b ∈ as, a ≥ b) : ∀ b ∈ insertSortedDesc x as, a ≥ b := by
  induction as generalizing x with
  | nil =>
    simp [insertSortedDesc, hx]
  | cons h t IH =>
    have has_h : a ≥ h := has h (by simp)
    have has_t : ∀ c ∈ t, a ≥ c := by
      intro c hc; exact has c (List.mem_cons_of_mem h hc)
    simp [insertSortedDesc]
    split <;> intro b hb
    · rcases List.mem_cons.mp hb with (rfl | hb')
      · exact hx
      · rcases List.mem_cons.mp hb' with (rfl | hb'')
        · exact has_h
        · exact has_t _ hb''
    · rcases List.mem_cons.mp hb with (rfl | hb')
      · exact has_h
      · exact IH hx has_t _ hb'

/-! ### Sortedness properties of `insertSortedDesc` and `sortDesc` -/

/-- Inserting an element into a descending-sorted list yields a descending-sorted list. -/
lemma insertSortedDesc_sortedDesc {α : Type u} [LinearOrder α] {x : α} {xs : List α}
    (h : sortedDesc xs) : sortedDesc (insertSortedDesc x xs) := by
  induction xs generalizing x with
  | nil =>
    rw [insertSortedDesc]
    unfold sortedDesc
    refine List.Pairwise.cons (by
      intro y hy
      simp at hy) List.Pairwise.nil
  | cons hd tl IH =>
    unfold sortedDesc at h
    cases h with
    | cons hall hrest =>
      have h_sorted_tl : sortedDesc tl := by
        unfold sortedDesc; exact hrest
      have IH' := IH (x := x) h_sorted_tl
      unfold sortedDesc at IH'
      by_cases hx_ge_hd : x ≥ hd
      · rw [insertSortedDesc, if_pos hx_ge_hd]; unfold sortedDesc
        have h_all : ∀ a', a' ∈ (hd :: tl) → x ≥ a' := by
          intro a' ha'
          rcases List.mem_cons.mp ha' with (rfl | ha'tl)
          · exact hx_ge_hd
          · have hhd_ge_a' : hd ≥ a' := hall a' ha'tl
            exact le_trans hhd_ge_a' hx_ge_hd
        exact List.Pairwise.cons h_all (List.Pairwise.cons hall hrest)
      · have hhd_ge_x : hd ≥ x := by
          rcases le_total hd x with (hle | hle)
          · exfalso; exact hx_ge_hd hle
          · exact hle
        rw [insertSortedDesc, if_neg hx_ge_hd]; unfold sortedDesc
        have h_all : ∀ a', a' ∈ insertSortedDesc x tl → hd ≥ a' :=
          insertSortedDesc_bound hhd_ge_x hall
        exact List.Pairwise.cons h_all IH'

/-- Sorting a list in descending order yields a descending-sorted list. -/
lemma sortDesc_sortedDesc {α : Type u} [LinearOrder α] (lst : List α) :
    sortedDesc (sortDesc lst) := by
  induction lst with
  | nil => unfold sortDesc sortedDesc; simp
  | cons x xs IH =>
    unfold sortDesc
    exact insertSortedDesc_sortedDesc IH

/-! ### Adjacent elements in a descending-sorted list -/

/-- In a descending-sorted list, any two adjacent elements `xs[i]` and `xs[i+1]` satisfy
`xs[i] ≥ xs[i+1]`. This uses the `get?` accessor and the `Pairwise`-based `sortedDesc`. -/
lemma sortedDesc_adjacent {α : Type u} [LE α] {xs : List α} (h : sortedDesc xs) (i : Nat) (x y : α)
    (_hbound : i + 1 < xs.length) (hget1 : xs[i]? = some x) (hget2 : xs[i+1]? = some y) :
    x ≥ y := by
  unfold sortedDesc at h
  have hpair := (List.pairwise_iff_get.mp h)
  rcases (List.getElem?_eq_some_iff.mp hget1) with ⟨hi, hx_eq⟩
  rcases (List.getElem?_eq_some_iff.mp hget2) with ⟨hi1, hy_eq⟩
  have hi_lt_hi1 : (⟨i, hi⟩ : Fin xs.length) < (⟨i+1, hi1⟩ : Fin xs.length) := by
    apply Fin.mk_lt_mk.mpr
    omega
  have hge := hpair (⟨i, hi⟩ : Fin xs.length) (⟨i+1, hi1⟩ : Fin xs.length) hi_lt_hi1
  rw [← hx_eq, ← hy_eq]
  exact hge

/-! ### Interplay between descending and ascending sortedness via `reverse` -/

/-- If a list is sorted by `(· ≥ ·)`, then its reverse is sorted by `(· ≤ ·)`. -/
lemma sorted_reverse_of_sorted_ge {α : Type u} [LinearOrder α] {l : List α}
    (h_sorted : List.Sorted (· ≥ ·) l) : List.Sorted (· ≤ ·) l.reverse := by
  rw [List.Sorted, List.pairwise_reverse]
  simpa [List.Sorted] using h_sorted

/-! ### Prepending to a descending-sorted list -/

/-- If `l` is sorted by `(· ≥ ·)` and every element of `l` is `≤ a`, then `a :: l` is also
sorted by `(· ≥ ·)`. This is the descending dual of `sorted_cons_of_forall_le`. -/
lemma sorted_ge_cons_of_forall_le {α : Type u} [LinearOrder α] {a : α} {l : List α}
    (h_sorted : List.Sorted (· ≥ ·) l) (h_all_le : ∀ x ∈ l, x ≤ a) :
    List.Sorted (· ≥ ·) (a :: l) := by
  rw [List.Sorted, List.pairwise_cons]
  constructor
  · intro y hy
    exact h_all_le y hy
  · rw [List.Sorted] at h_sorted
    exact h_sorted

/-! ### Index condition for descending-sorted lists -/

/-- If `List.Sorted (· ≥ ·) l`, then for any `i < j < l.length`, we have `l[i]! ≥ l[j]!`. -/
theorem sorted_ge_implies_index_condition {α : Type} [LinearOrder α] [Inhabited α] (l : List α)
    (h : List.Sorted (· ≥ ·) l) (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i]! ≥ l[j]! := by
  have h_pairwise : List.Pairwise (· ≥ ·) l := h
  have h_get := (List.pairwise_iff_get.mp h_pairwise) ⟨i, hi⟩ ⟨j, hj⟩ hij
  have h_get_i : l[i]! = l.get ⟨i, hi⟩ := by
    simp [hi]
  have h_get_j : l[j]! = l.get ⟨j, hj⟩ := by
    simp [hj]
  rw [h_get_i, h_get_j]
  exact h_get

/-! ### Appending a minimum element to a sorted-descending list -/

/-- Appending a minimum element `m` to a sorted (descending) list maintains sortedness.
`hbound` asserts that `m` is a lower bound for all elements of `l`. -/
theorem sorted_append_of_sorted_and_bound_desc {α : Type} [LinearOrder α] (l : List α) (m : α)
    (hsorted : List.Sorted (· ≥ ·) l) (hbound : ∀ x ∈ l, m ≤ x) :
    List.Sorted (· ≥ ·) (l ++ [m]) := by
  induction' l with a as ih generalizing m
  · -- l = [], need Sorted [m]
    refine (List.sorted_cons (a := m) (l := [])).mpr ⟨?_, List.sorted_nil⟩
    intro x hx; exfalso; simp at hx
  · -- l = a :: as
    rw [List.sorted_cons] at hsorted
    rcases hsorted with ⟨h_head, h_tail⟩
    have hbound_as : ∀ x ∈ as, m ≤ x := by
      intro x hx; exact hbound x (by simp [hx])
    have ha_ge_m : a ≥ m := hbound a (by simp)
    have h_sorted_as_m : List.Sorted (· ≥ ·) (as ++ [m]) :=
      ih m h_tail hbound_as
    apply (List.sorted_cons (a := a) (l := as ++ [m])).mpr
    refine ⟨?_, h_sorted_as_m⟩
    intro b hb
    rw [List.mem_append] at hb
    rcases hb with (hb_as | hb_m)
    · exact h_head b hb_as
    · simp at hb_m; subst hb_m; exact ha_ge_m

/-! ### `bubble` — one pass of bubble sort (descending) -/

/-- One pass of bubble sort (descending): swaps adjacent elements that are out of order.
After one pass, the minimum element "bubbles" to the last position. -/
def bubble {α : Type} [LinearOrder α] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: ys =>
    if x ≥ y then x :: bubble (y :: ys)
    else y :: bubble (x :: ys)

/-! ### Pairwise sorted descending on first projection

These defs and theorems are the "by first projection" counterparts of
`insertSortedDesc`, `sortDesc`, and `sortedDesc` for lists of pairs `(α × β)`.
Instead of comparing elements directly, they compare only the first projection
using strict `>`. This is useful for sorting association lists by key.
-/

/-- Extract the first projection of each pair in a list.
`fstKeys [(k₁, v₁), (k₂, v₂), …] = [k₁, k₂, …]`. -/
def fstKeys {α : Type u} {β : Type v} (lst : List (α × β)) : List α :=
  lst.map Prod.fst

/-- A list of pairs is sorted descending on the first projection if every
consecutive pair satisfies `a.1 > b.1`. -/
def sortedDescOnFst {α : Type u} [LT α] {β : Type v} (lst : List (α × β)) : Prop :=
  lst.Pairwise (fun a b => a.1 > b.1)

/-- Insert a pair `p` into a list of pairs that is already sorted descending on the
first projection, maintaining that order. Compares `p.1 > h.1` to decide placement. -/
def insertSortedDescOnFst {α : Type u} [LinearOrder α] {β : Type v} (p : α × β) (lst : List (α × β)) : List (α × β) :=
  match lst with
  | [] => [p]
  | h :: t =>
      if p.1 > h.1 then
        p :: lst
      else
        h :: insertSortedDescOnFst p t

/-- Sort a list of pairs in descending order by the first projection using insertion sort. -/
def sortDescOnFst {α : Type u} [LinearOrder α] {β : Type v} (lst : List (α × β)) : List (α × β) :=
  lst.foldr insertSortedDescOnFst []

/-! ### Membership lemmas for `insertSortedDescOnFst` and `sortDescOnFst` -/

/-- Membership in the result of `insertSortedDescOnFst`:
`x` is in the result iff `x = p` or `x` was already in the list. -/
lemma mem_insertSortedDescOnFst {α : Type u} [LinearOrder α] {β : Type v} (p : α × β) (lst : List (α × β)) (x : α × β) :
    x ∈ insertSortedDescOnFst p lst ↔ x = p ∨ x ∈ lst := by
  induction lst generalizing p x with
  | nil => simp [insertSortedDescOnFst]
  | cons hd tl ih =>
    have h_ins : insertSortedDescOnFst p (hd :: tl) =
        (if p.1 > hd.1 then p :: hd :: tl else hd :: insertSortedDescOnFst p tl) := rfl
    rw [h_ins]
    split <;> simp [ih] <;> tauto

/-- Keys membership in the result of `insertSortedDescOnFst`:
`k` is a key in the result iff it was already a key or `k = p.1`. -/
lemma mem_keys_insertSortedDescOnFst {α : Type u} [LinearOrder α] {β : Type v} (p : α × β) (lst : List (α × β)) (k : α) :
    k ∈ fstKeys (insertSortedDescOnFst p lst) ↔ k ∈ fstKeys lst ∨ k = p.1 := by
  induction lst generalizing p k with
  | nil => simp [insertSortedDescOnFst, fstKeys]
  | cons hd tl ih =>
    have h_ins : insertSortedDescOnFst p (hd :: tl) =
        (if p.1 > hd.1 then p :: hd :: tl else hd :: insertSortedDescOnFst p tl) := rfl
    rw [h_ins]
    split
    · simp [fstKeys]
      tauto
    · have ih_inst := ih p k
      calc
        k ∈ fstKeys (hd :: insertSortedDescOnFst p tl) ↔ (k = hd.1 ∨ k ∈ fstKeys (insertSortedDescOnFst p tl)) := by
          simp [fstKeys]
        _ ↔ (k = hd.1 ∨ (k ∈ fstKeys tl ∨ k = p.1)) := by
          rw [ih_inst]
        _ ↔ ((k = hd.1 ∨ k ∈ fstKeys tl) ∨ k = p.1) := by
          tauto
        _ ↔ k ∈ fstKeys (hd :: tl) ∨ k = p.1 := by
          simp [fstKeys]

/-- The keys of `sortDescOnFst lst` are exactly the keys of `lst`.
Sorting by key does not add or remove keys. -/
lemma mem_keys_sortDescOnFst {α : Type u} [LinearOrder α] {β : Type v} (lst : List (α × β)) (k : α) :
    k ∈ fstKeys (sortDescOnFst lst) ↔ k ∈ fstKeys lst := by
  induction lst with
  | nil => simp [sortDescOnFst, fstKeys]
  | cons hd tl ih =>
    have h_sort : sortDescOnFst (hd :: tl) = insertSortedDescOnFst hd (sortDescOnFst tl) := rfl
    rw [h_sort, mem_keys_insertSortedDescOnFst]
    rw [ih]
    simp [fstKeys, or_comm]

/-! ### Nodup keys lemmas -/

/-- Inserting a pair whose key is not already present into a list with nodup keys
preserves the nodup keys property. -/
lemma nodup_keys_insertSortedDescOnFst_of_nodup_disjoint {α : Type u} [LinearOrder α] {β : Type v} (p : α × β) (lst : List (α × β))
    (h_nodup : List.Nodup (fstKeys lst)) (h_disjoint : p.1 ∉ fstKeys lst) :
    List.Nodup (fstKeys (insertSortedDescOnFst p lst)) := by
  induction lst generalizing p with
  | nil => simp [insertSortedDescOnFst, fstKeys]
  | cons hd tl ih =>
    have hn : List.Nodup (fstKeys tl) := h_nodup.of_cons
    have hm : hd.1 ∉ fstKeys tl := h_nodup.not_mem
    have hp_ne_hd : p.1 ≠ hd.1 := by
      intro h_eq; apply h_disjoint; simp [fstKeys, h_eq]
    have hp_notin_tl : p.1 ∉ fstKeys tl := by
      intro h
      apply h_disjoint
      simpa [fstKeys] using List.mem_cons_of_mem hd.1 h
    have h_ins : insertSortedDescOnFst p (hd :: tl) =
        (if p.1 > hd.1 then p :: hd :: tl else hd :: insertSortedDescOnFst p tl) := rfl
    rw [h_ins]
    split
    · -- p.1 > hd.1: result = p :: hd :: tl, fstKeys = p.1 :: hd.1 :: fstKeys tl
      have h_notin : p.1 ∉ hd.1 :: fstKeys tl := by
        simp [hp_ne_hd, hp_notin_tl]
      have h_nodup_hdtl : List.Nodup (hd.1 :: fstKeys tl) := h_nodup
      simpa [fstKeys] using List.Nodup.cons h_notin h_nodup_hdtl
    · -- ¬(p.1 > hd.1): result = hd :: insertSortedDescOnFst p tl, fstKeys = hd.1 :: fstKeys (insertSortedDescOnFst p tl)
      have ih' : List.Nodup (fstKeys (insertSortedDescOnFst p tl)) := ih p hn hp_notin_tl
      have hd_notin : hd.1 ∉ fstKeys (insertSortedDescOnFst p tl) := by
        rw [mem_keys_insertSortedDescOnFst]
        intro h
        rcases h with (hcase | hcase)
        · exact hm hcase
        · exact hp_ne_hd hcase.symm
      simpa [fstKeys] using List.Nodup.cons hd_notin ih'

/-! ### Sortedness lemmas -/

/-- Inserting a pair into a list that is already sorted by descending first projection
preserves sortedness, provided the key is not already present. -/
lemma sortedDescOnFst_insertSortedDescOnFst_of_nodup_disjoint {α : Type u} [LinearOrder α] {β : Type v} (p : α × β) (lst : List (α × β))
    (h_sorted : sortedDescOnFst lst) (h_disjoint : p.1 ∉ fstKeys lst) :
    sortedDescOnFst (insertSortedDescOnFst p lst) := by
  induction lst generalizing p with
  | nil => simp [insertSortedDescOnFst, sortedDescOnFst]
  | cons hd tl ih =>
    have hp_ne_hd : p.1 ≠ hd.1 := by
      intro h_eq; apply h_disjoint; simp [fstKeys, h_eq]
    have hp_notin_tl : p.1 ∉ fstKeys tl := by
      intro h
      apply h_disjoint
      simpa [fstKeys] using List.mem_cons_of_mem hd.1 h
    rcases (List.pairwise_cons (R := (fun a b : α × β => a.1 > b.1))).mp h_sorted with
      ⟨h_all_gt, h_sorted_tl⟩
    have h_ins : insertSortedDescOnFst p (hd :: tl) =
        (if p.1 > hd.1 then p :: hd :: tl else hd :: insertSortedDescOnFst p tl) := rfl
    rw [h_ins]
    by_cases h_gt : p.1 > hd.1
    · rw [if_pos h_gt]
      rw [sortedDescOnFst, List.pairwise_cons]
      constructor
      · intro a' ha'
        simp at ha'
        rcases ha' with (rfl | ha'_tl)
        · exact h_gt
        · have h_hd_gt_a' : hd.1 > a'.1 := h_all_gt a' ha'_tl
          exact lt_trans h_hd_gt_a' h_gt
      · exact h_sorted
    · rw [if_neg h_gt]
      have h_hd_gt_p : hd.1 > p.1 := by
        have hcases := Ne.lt_or_lt hp_ne_hd.symm
        rcases hcases with (hlt | hlt)
        · exact absurd hlt h_gt
        · exact hlt
      have h_gt_all_inserted : ∀ b ∈ insertSortedDescOnFst p tl, hd.1 > b.1 := by
        intro b hb
        rcases (mem_insertSortedDescOnFst p tl b).mp hb with (rfl | hb_tl)
        · exact h_hd_gt_p
        · exact h_all_gt b hb_tl
      have ih' : sortedDescOnFst (insertSortedDescOnFst p tl) := ih p h_sorted_tl hp_notin_tl
      rw [sortedDescOnFst, List.pairwise_cons]
      exact ⟨h_gt_all_inserted, ih'⟩

/-- Sorting a list with nodup keys by descending first projection yields a list
that is descending-sorted on the first projection. -/
lemma sortedDescOnFst_sortDescOnFst_of_nodup {α : Type u} [LinearOrder α] {β : Type v} (lst : List (α × β)) (h : List.Nodup (fstKeys lst)) :
    sortedDescOnFst (sortDescOnFst lst) := by
  induction lst with
  | nil => simp [sortDescOnFst, sortedDescOnFst]
  | cons hd tl ih =>
    have h_nodup_tl : List.Nodup (fstKeys tl) := h.of_cons
    have hd_notin_tl : hd.1 ∉ fstKeys tl := h.not_mem
    have h_sort : sortDescOnFst (hd :: tl) = insertSortedDescOnFst hd (sortDescOnFst tl) := rfl
    rw [h_sort]
    have ih' := ih h_nodup_tl
    have hd_notin_sorted : hd.1 ∉ fstKeys (sortDescOnFst tl) := by
      rw [mem_keys_sortDescOnFst]; exact hd_notin_tl
    exact sortedDescOnFst_insertSortedDescOnFst_of_nodup_disjoint hd (sortDescOnFst tl) ih' hd_notin_sorted

/-! ### `insertDescDedup` — deduplicating descending insertion (strict `>`)

`insertDescDedup x l` inserts `x` into `l` maintaining a strictly descending order (`· > ·`)
while **skipping duplicates**: if `x` already appears in `l`, the result is `l` unchanged.

Contrast with `insertSortedDesc` which:
- uses non-strict comparison `(≥)` (keeps duplicates)
- always inserts — the list length increases by 1

`insertDescDedup` is useful when you want a strictly descending, duplicate-free list.
-/

/-- Insert `x` into `l` maintaining strict descending order (`· > ·`), skipping duplicates.
If `x > y` where `y` is the head, `x` is placed at the front.
If `x = y`, `l` is returned unchanged (duplicate skipped).
Otherwise, recurse into the tail. -/
def insertDescDedup {α : Type u} [LinearOrder α] (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    dite (x > y) (fun _ => x :: y :: ys) (fun _ =>
      dite (x = y) (fun _ => y :: ys) (fun _ =>
        y :: insertDescDedup x ys))

/-- Membership in `insertDescDedup x l`: `y` is in the result iff `y = x` or `y ∈ l`. -/
lemma mem_insertDescDedup {α : Type u} [LinearOrder α] (x y : α) (l : List α) : y ∈ insertDescDedup x l ↔ y = x ∨ y ∈ l := by
  induction l generalizing x y with
  | nil => simp [insertDescDedup]
  | cons z zs IH =>
    dsimp [insertDescDedup]
    split
    · simp
    · split
      · rename_i h; subst h; simp
      · simp [IH]; tauto

/-- If `l` is pairwise `(· > ·)`, then `insertDescDedup x l` is also pairwise `(· > ·)`. -/
lemma pairwise_gt_insertDescDedup {α : Type u} [LinearOrder α] (x : α) (l : List α) (h : List.Pairwise (· > ·) l) :
    List.Pairwise (· > ·) (insertDescDedup x l) := by
  induction l generalizing x with
  | nil => simp [insertDescDedup]
  | cons z zs IH =>
    rcases List.pairwise_cons.mp h with ⟨hz_gt_all, h_pairwise⟩
    dsimp [insertDescDedup]
    split
    case isTrue h_gt =>
      apply List.Pairwise.cons
      · intro a' ha'
        have ha'_or : a' = z ∨ a' ∈ zs := by simpa using ha'
        rcases ha'_or with (rfl | ha'_zs)
        · exact h_gt
        · have hz_gt_a' : z > a' := hz_gt_all a' ha'_zs
          exact lt_trans hz_gt_a' h_gt
      · exact h
    case isFalse h_not_gt =>
      split
      case isTrue h_eq =>
        subst h_eq
        exact h
      case isFalse h_ne =>
        have hz_gt_x : z > x := by
          have hx_le_z : x ≤ z := le_of_not_gt h_not_gt
          rcases eq_or_lt_of_le hx_le_z with (heq | hlt)
          · exfalso; exact h_ne heq
          · exact hlt
        apply List.Pairwise.cons
        · intro a' ha'
          rcases (mem_insertDescDedup x a' zs).mp ha' with (rfl | ha'_zs)
          · exact hz_gt_x
          · exact hz_gt_all a' ha'_zs
        · exact IH x h_pairwise

/-- Membership in a fold of `insertDescDedup`:
`x ∈ (l.foldl (fun acc x' => insertDescDedup x' acc) acc) ↔ x ∈ l ∨ x ∈ acc`. -/
lemma mem_foldl_insertDescDedup {α : Type u} [LinearOrder α] (l acc : List α) (x : α) :
    x ∈ (l.foldl (fun acc x' => insertDescDedup x' acc) acc) ↔ x ∈ l ∨ x ∈ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys IH =>
    simp [List.foldl]
    rw [IH, mem_insertDescDedup]
    tauto

/-- If `acc` is pairwise `(· > ·)`, then folding `insertDescDedup` over `l` preserves this property. -/
lemma pairwise_gt_foldl_insertDescDedup {α : Type u} [LinearOrder α] (l acc : List α) (h : List.Pairwise (· > ·) acc) :
    List.Pairwise (· > ·) (l.foldl (fun acc x => insertDescDedup x acc) acc) := by
  induction l generalizing acc with
  | nil => exact h
  | cons x xs IH =>
    simp [List.foldl]
    apply IH
    exact pairwise_gt_insertDescDedup x acc h

/-! ### Key-based descending insertion

`insertByKeyDesc` generalizes `insertSortedDesc` by allowing elements of type `α`
to be compared via a key function `key : α → β` into any `LinearOrder β`.
This is useful when sorting a list of objects by a derived attribute (e.g., word count,
priority, etc.) in descending order.

The companion theorems mirror those for `insertSortedDesc`: permutation,
lower-bound preservation, and `Pairwise` sortedness for both the insert step
and the full sort (via `List.foldr`). -/

variable {α β : Type} [LinearOrder β]

/-- Insert `x` into `l` maintaining descending order by `key`.
Generalized: works for any type `α` with a `key : α → β` into a `LinearOrder β`. -/
def insertByKeyDesc (key : α → β) (x : α) (l : List α) : List α :=
  match l with
  | [] => [x]
  | h :: t =>
    if key x ≥ key h then x :: h :: t
    else h :: insertByKeyDesc key x t

/-- Inserting an element via `insertByKeyDesc` yields a list that is a permutation of
`x :: l`. In other words, `insertByKeyDesc` preserves the multiset of elements. -/
lemma insertByKeyDesc_perm (key : α → β) (x : α) (l : List α) :
    List.Perm (insertByKeyDesc key x l) (x :: l) := by
  induction l generalizing x with
  | nil => simp [insertByKeyDesc]
  | cons h t IH =>
    simp [insertByKeyDesc]
    split
    · rfl
    · have h_cons : List.Perm (h :: insertByKeyDesc key x t) (h :: x :: t) :=
        List.Perm.cons h (IH x)
      have h_swap : List.Perm (h :: x :: t) (x :: h :: t) := List.Perm.swap x h t
      exact List.Perm.trans h_cons h_swap

/-- Folding `insertByKeyDesc` over a list produces a permutation of the original list.
This is the key-based counterpart of `sortDesc_perm`. -/
lemma foldr_insertByKeyDesc_perm (key : α → β) (l : List α) :
    List.Perm (List.foldr (insertByKeyDesc key) [] l) l := by
  induction l with
  | nil => simp
  | cons x xs IH =>
    simp [List.foldr]
    have h_insert : List.Perm (insertByKeyDesc key x (List.foldr (insertByKeyDesc key) [] xs))
      (x :: List.foldr (insertByKeyDesc key) [] xs) := insertByKeyDesc_perm key x _
    have h_cons : List.Perm (x :: List.foldr (insertByKeyDesc key) [] xs) (x :: xs) :=
      List.Perm.cons x IH
    exact List.Perm.trans h_insert h_cons

/-- If `key a ≥ key x` and `key a ≥ key y` for all `y ∈ as`, then after inserting `x`
into `as` via `insertByKeyDesc`, `key a` remains ≥ the key of every element in the result.
This is the key-based counterpart of `insertSortedDesc_bound`. -/
lemma insertByKeyDesc_bound (key : α → β) {a x : α} {as : List α}
    (hx : key a ≥ key x) (has : ∀ b ∈ as, key a ≥ key b) :
    ∀ b ∈ insertByKeyDesc key x as, key a ≥ key b := by
  induction as generalizing x with
  | nil =>
    simp [insertByKeyDesc, hx]
  | cons h t IH =>
    have has_h : key a ≥ key h := has h (by simp)
    have has_t : ∀ c ∈ t, key a ≥ key c := by
      intro c hc
      exact has c (List.mem_cons_of_mem h hc)
    by_cases hx_ge_h : key x ≥ key h
    · rw [insertByKeyDesc, if_pos hx_ge_h]
      intro b hb
      rcases List.mem_cons.mp hb with (rfl | hb')
      · exact hx
      · rcases List.mem_cons.mp hb' with (rfl | hb'')
        · exact has_h
        · exact has_t _ hb''
    · rw [insertByKeyDesc, if_neg hx_ge_h]
      intro b hb
      rcases List.mem_cons.mp hb with (rfl | hb')
      · exact has_h
      · exact IH hx has_t _ hb'

/-- Inserting an element into a key-descending-sorted list preserves the `Pairwise`
sortedness property. This is the key-based counterpart of `insertSortedDesc_sortedDesc`. -/
lemma insertByKeyDesc_pairwise (key : α → β) (x : α) (xs : List α)
    (h : List.Pairwise (fun a b => key a ≥ key b) xs) :
    List.Pairwise (fun a b => key a ≥ key b) (insertByKeyDesc key x xs) := by
  induction xs generalizing x with
  | nil => simp [insertByKeyDesc]
  | cons a as IH =>
    rcases List.pairwise_cons.mp h with ⟨ha_ge_as, hp_as⟩
    by_cases hx_ge_a : key x ≥ key a
    · rw [insertByKeyDesc, if_pos hx_ge_a]
      have h_all_x : ∀ b ∈ (a :: as), key x ≥ key b := by
        intro b hb
        rcases List.mem_cons.mp hb with (rfl | hb_as)
        · exact hx_ge_a
        · have ha_ge_b : key a ≥ key b := ha_ge_as b hb_as
          exact le_trans ha_ge_b hx_ge_a
      refine List.Pairwise.cons h_all_x (List.Pairwise.cons ha_ge_as hp_as)
    · have ha_ge_x : key a ≥ key x :=
        le_of_lt (lt_of_not_ge hx_ge_a)
      rw [insertByKeyDesc, if_neg hx_ge_a]
      have h_all_a : ∀ b ∈ insertByKeyDesc key x as, key a ≥ key b :=
        insertByKeyDesc_bound key ha_ge_x ha_ge_as
      refine List.Pairwise.cons h_all_a (IH x hp_as)

/-- Folding `insertByKeyDesc` over a list produces a list that is `Pairwise` sorted
by descending key. This is the key-based counterpart of `sortDesc_sortedDesc`. -/
lemma foldr_insertByKeyDesc_pairwise (key : α → β) (l : List α) :
    List.Pairwise (fun a b => key a ≥ key b)
      (List.foldr (insertByKeyDesc key) [] l) := by
  induction l with
  | nil => simp
  | cons x xs IH =>
    simp [List.foldr]
    exact insertByKeyDesc_pairwise key x _ IH

end List

namespace List

/-!
# Sort by a `Nat` measure then by intrinsic order

These provide insertion sort parameterized by a `Nat`-valued measure function `m : α → Nat`.
Elements are compared first by their measure (ascending), and when measures are equal,
by the intrinsic `≤` order of `α`. This corresponds to the `CompareBy.cmpByMeasureThenLex`
relation.

The defs `insertByMeasLex` and `sortByMeasLex` generalize the pattern of sorting strings
by length first and lexicographically second (seen in many verified algorithms).
-/

variable {α : Type u} [LinearOrder α]

/-! ### Core definitions -/

/-- Insert `x` into a list already sorted by measure-then-element order,
preserving the sorted order. Elements are compared first by their `Nat` measure `m x`,
and when measures are equal, by the intrinsic `≤` order. -/
def insertByMeasLex (m : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | h :: t =>
    if m x < m h then x :: h :: t
    else if m h < m x then h :: insertByMeasLex m x t
    else
      if x ≤ h then x :: h :: t else h :: insertByMeasLex m x t

/-- Sort a list by a measure function `m : α → Nat` (ascending), using the intrinsic
`≤` order for tie-breaking, via insertion sort. -/
def sortByMeasLex (m : α → Nat) : List α → List α
  | [] => []
  | h :: t => insertByMeasLex m h (sortByMeasLex m t)

/-! ### Helper lemmas about `cmpByMeasureThenLex` -/

/-- If `m a < m b`, then `cmpByMeasureThenLex m a c` follows from `cmpByMeasureThenLex m b c`. -/
lemma cmpByMeasureThenLex_of_shorter {a b c : α} (m : α → Nat)
    (h_lt : m a < m b) (h_bc : CompareBy.cmpByMeasureThenLex m b c) :
    CompareBy.cmpByMeasureThenLex m a c := by
  have h_ab : CompareBy.cmpByMeasureThenLex m a b := by
    dsimp [CompareBy.cmpByMeasureThenLex]; left; exact h_lt
  exact IsTrans.trans a b c h_ab h_bc

/-- If `m a = m b` and `a ≤ b`, then `cmpByMeasureThenLex m a c` follows from
`cmpByMeasureThenLex m b c`. -/
lemma cmpByMeasureThenLex_of_same_meas_le {a b c : α} (m : α → Nat)
    (h_meas_eq : m a = m b) (h_le : a ≤ b)
    (h_bc : CompareBy.cmpByMeasureThenLex m b c) :
    CompareBy.cmpByMeasureThenLex m a c := by
  have h_ab : CompareBy.cmpByMeasureThenLex m a b := by
    dsimp [CompareBy.cmpByMeasureThenLex]; right; exact ⟨h_meas_eq, h_le⟩
  exact IsTrans.trans a b c h_ab h_bc

/-! ### Length theorems -/

/-- Insert preserves length: result has one more element. -/
lemma insertByMeasLex_length (m : α → Nat) (x : α) (l : List α) :
    (insertByMeasLex m x l).length = l.length + 1 := by
  induction l generalizing x with
  | nil => simp [insertByMeasLex]
  | cons h t ih =>
    simp [insertByMeasLex]
    split
    · simp
    · split
      · simp [ih]
      · split
        · simp
        · simp [ih]

/-- Sorting preserves length. -/
lemma sortByMeasLex_length (m : α → Nat) (l : List α) :
    (sortByMeasLex m l).length = l.length := by
  induction l with
  | nil => simp [sortByMeasLex]
  | cons h t ih =>
    simp [sortByMeasLex, insertByMeasLex_length m, ih]

/-! ### Membership theorems -/

/-- Membership in insert: either the inserted element or from the original list. -/
lemma mem_insertByMeasLex (m : α → Nat) (x y : α) (l : List α) :
    y ∈ insertByMeasLex m x l ↔ y = x ∨ y ∈ l := by
  induction l generalizing x y with
  | nil => simp [insertByMeasLex]
  | cons h t ih =>
    simp only [insertByMeasLex]
    split
    · simp
    · split
      · simp [ih, or_comm, or_assoc, or_left_comm]
      · split
        · simp
        · simp [ih, or_comm, or_assoc, or_left_comm]

/-- Membership in sorted list equals membership in original. -/
lemma mem_sortByMeasLex (m : α → Nat) (l : List α) (x : α) :
    x ∈ sortByMeasLex m l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortByMeasLex]
  | cons h t ih =>
    simp [sortByMeasLex, mem_insertByMeasLex m, ih]

/-! ### Permutation theorems -/

/-- `insertByMeasLex m x l` is a permutation of `x :: l`. -/
lemma insertByMeasLex_perm (m : α → Nat) (x : α) (l : List α) :
    List.Perm (insertByMeasLex m x l) (x :: l) := by
  induction l generalizing x with
  | nil => simp [insertByMeasLex]
  | cons h t ih =>
    dsimp [insertByMeasLex]
    split
    · rfl
    · split
      · have h_perm : List.Perm (insertByMeasLex m x t) (x :: t) := ih x
        have h_cons : List.Perm (h :: insertByMeasLex m x t) (h :: x :: t) :=
          List.Perm.cons h h_perm
        have h_swap : List.Perm (h :: x :: t) (x :: h :: t) := List.Perm.swap x h t
        exact List.Perm.trans h_cons h_swap
      · split
        · rfl
        · have h_perm : List.Perm (insertByMeasLex m x t) (x :: t) := ih x
          have h_cons : List.Perm (h :: insertByMeasLex m x t) (h :: x :: t) :=
            List.Perm.cons h h_perm
          have h_swap : List.Perm (h :: x :: t) (x :: h :: t) := List.Perm.swap x h t
          exact List.Perm.trans h_cons h_swap

/-- `sortByMeasLex m l` is a permutation of `l`. -/
lemma sortByMeasLex_perm (m : α → Nat) (l : List α) :
    List.Perm (sortByMeasLex m l) l := by
  induction l with
  | nil => simp [sortByMeasLex]
  | cons h t ih =>
    simp [sortByMeasLex]
    have h_insert : List.Perm (insertByMeasLex m h (sortByMeasLex m t))
        (h :: sortByMeasLex m t) :=
      insertByMeasLex_perm m h (sortByMeasLex m t)
    have h_cons : List.Perm (h :: sortByMeasLex m t) (h :: t) := List.Perm.cons h ih
    exact List.Perm.trans h_insert h_cons

/-! ### Sortedness theorems -/

/-- Inserting into a sorted list preserves the sorted property
(with respect to `CompareBy.cmpByMeasureThenLex`). -/
lemma insertByMeasLex_sorted (m : α → Nat) (x : α) (l : List α)
    (h_sorted : List.Pairwise (CompareBy.cmpByMeasureThenLex m) l) :
    List.Pairwise (CompareBy.cmpByMeasureThenLex m) (insertByMeasLex m x l) := by
  induction l generalizing x with
  | nil =>
    dsimp [insertByMeasLex]
    apply List.Pairwise.cons (by
      intro y hy; exfalso; exact List.not_mem_nil _ hy)
    exact List.Pairwise.nil
  | cons h t ih =>
    rcases List.pairwise_cons.mp h_sorted with ⟨h_h_all, h_t_sorted⟩
    dsimp [insertByMeasLex]
    by_cases h_lt : m x < m h
    · rw [if_pos h_lt]
      have h_sh : CompareBy.cmpByMeasureThenLex m x h := by
        dsimp [CompareBy.cmpByMeasureThenLex]; left; exact h_lt
      have h_all_x : ∀ y ∈ h :: t, CompareBy.cmpByMeasureThenLex m x y := by
        intro y hy
        rcases List.mem_cons.mp hy with (rfl | hy_t)
        · exact h_sh
        · exact cmpByMeasureThenLex_of_shorter m h_lt (h_h_all y hy_t)
      apply List.Pairwise.cons h_all_x
      apply List.Pairwise.cons h_h_all
      exact h_t_sorted
    · rw [if_neg h_lt]
      by_cases h_gt : m h < m x
      · rw [if_pos h_gt]
        have h_hs : CompareBy.cmpByMeasureThenLex m h x := by
          dsimp [CompareBy.cmpByMeasureThenLex]; left; exact h_gt
        have h_all_h : ∀ y ∈ insertByMeasLex m x t, CompareBy.cmpByMeasureThenLex m h y := by
          intro y hy
          rcases (mem_insertByMeasLex m x y t).mp hy with (rfl | hy_t)
          · exact h_hs
          · exact h_h_all y hy_t
        have h_t_sorted' : List.Pairwise (CompareBy.cmpByMeasureThenLex m) (insertByMeasLex m x t) :=
          ih x h_t_sorted
        apply List.Pairwise.cons h_all_h
        exact h_t_sorted'
      · rw [if_neg h_gt]
        have h_meas_eq : m x = m h := by
          have h_not_lt : ¬ m x < m h := h_lt
          have h_not_gt : ¬ m h < m x := h_gt
          omega
        by_cases h_le : x ≤ h
        · rw [if_pos h_le]
          have h_sh : CompareBy.cmpByMeasureThenLex m x h := by
            dsimp [CompareBy.cmpByMeasureThenLex]; right; exact ⟨h_meas_eq, h_le⟩
          have h_all_x : ∀ y ∈ h :: t, CompareBy.cmpByMeasureThenLex m x y := by
            intro y hy
            rcases List.mem_cons.mp hy with (rfl | hy_t)
            · exact h_sh
            · exact cmpByMeasureThenLex_of_same_meas_le m h_meas_eq h_le (h_h_all y hy_t)
          apply List.Pairwise.cons h_all_x
          apply List.Pairwise.cons h_h_all
          exact h_t_sorted
        · rw [if_neg h_le]
          have h_hl : h ≤ x := le_of_not_ge h_le
          have h_hs : CompareBy.cmpByMeasureThenLex m h x := by
            dsimp [CompareBy.cmpByMeasureThenLex]; right; exact ⟨h_meas_eq.symm, h_hl⟩
          have h_all_h : ∀ y ∈ insertByMeasLex m x t, CompareBy.cmpByMeasureThenLex m h y := by
            intro y hy
            rcases (mem_insertByMeasLex m x y t).mp hy with (rfl | hy_t)
            · exact h_hs
            · exact h_h_all y hy_t
          have h_t_sorted' : List.Pairwise (CompareBy.cmpByMeasureThenLex m) (insertByMeasLex m x t) :=
            ih x h_t_sorted
          apply List.Pairwise.cons h_all_h
          exact h_t_sorted'

/-- The result of `sortByMeasLex` is pairwise sorted by `cmpByMeasureThenLex`. -/
lemma sortByMeasLex_sorted (m : α → Nat) (l : List α) :
    List.Pairwise (CompareBy.cmpByMeasureThenLex m) (sortByMeasLex m l) := by
  induction l with
  | nil => simp [sortByMeasLex]
  | cons h t ih =>
    dsimp [sortByMeasLex]
    exact insertByMeasLex_sorted m h (sortByMeasLex m t) ih

/-! ### Bridge from `Pairwise` to element-wise postcondition -/

/-- Bridge from `List.Pairwise (cmpByMeasureThenLex m)` to the element-wise postcondition:
if a list is pairwise sorted by measure-then-element order, then for any `i < j` in bounds,
either `m (l[i]!) < m (l[j]!)` or `m (l[i]!) = m (l[j]!) ∧ l[i]! ≤ l[j]!`. -/
lemma pairwise_cmpMeasureThenElem_to_postcond [Inhabited α] (m : α → Nat) (l : List α)
    (h : List.Pairwise (CompareBy.cmpByMeasureThenLex m) l) :
    ∀ i j, i < j → i < l.length → j < l.length →
      (m (l[i]!) < m (l[j]!)) ∨
      (m (l[i]!) = m (l[j]!) ∧ l[i]! ≤ l[j]!) := by
  rw [List.pairwise_iff_get] at h
  intro i j hij hi hj
  rw [getElem!_pos l i hi, getElem!_pos l j hj]
  exact h ⟨i, hi⟩ ⟨j, hj⟩ hij

/-! ### Descending by measure then lexicographic (element) order

These provide insertion sort parameterized by a `Nat`-valued measure function `m : α → Nat`,
comparing elements first by their measure in *descending* order (higher measure first),
and when measures are equal, by the intrinsic `≤` order of `α`. This corresponds to the
`CompareBy.descByMeasureThenLex` relation.

The defs `insertByDescMeasLex` and `sortByDescMeasLex` are the descending counterparts of
`insertByMeasLex` and `sortByMeasLex`. -/

/-- Insert `x` into a list already sorted by descending-measure-then-element order,
preserving the sorted order. Elements are compared first by their `Nat` measure `m x`
in descending order (higher measure first), and when measures are equal,
by the intrinsic `≤` order. -/
def insertByDescMeasLex (m : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | h :: t =>
    if m x > m h then x :: h :: t
    else if m h > m x then h :: insertByDescMeasLex m x t
    else
      if x ≤ h then x :: h :: t else h :: insertByDescMeasLex m x t

/-- Sort a list by a measure function `m : α → Nat` in descending order, using the intrinsic
`≤` order for tie-breaking, via insertion sort. -/
def sortByDescMeasLex (m : α → Nat) : List α → List α
  | [] => []
  | h :: t => insertByDescMeasLex m h (sortByDescMeasLex m t)

/-! ### Length theorems -/

/-- Insert preserves length: result has one more element. -/
lemma insertByDescMeasLex_length (m : α → Nat) (x : α) (l : List α) :
    (insertByDescMeasLex m x l).length = l.length + 1 := by
  induction l generalizing x with
  | nil => simp [insertByDescMeasLex]
  | cons h t ih =>
    simp [insertByDescMeasLex]
    split
    · simp
    · split
      · simp [ih]
      · split
        · simp
        · simp [ih]

/-- Sorting preserves length. -/
lemma sortByDescMeasLex_length (m : α → Nat) (l : List α) :
    (sortByDescMeasLex m l).length = l.length := by
  induction l with
  | nil => simp [sortByDescMeasLex]
  | cons h t ih =>
    simp [sortByDescMeasLex, insertByDescMeasLex_length m, ih]

/-! ### Membership theorems -/

/-- Membership in insert: either the inserted element or from the original list. -/
lemma mem_insertByDescMeasLex (m : α → Nat) (x y : α) (l : List α) :
    y ∈ insertByDescMeasLex m x l ↔ y = x ∨ y ∈ l := by
  induction l generalizing x y with
  | nil => simp [insertByDescMeasLex]
  | cons h t ih =>
    simp only [insertByDescMeasLex]
    split
    · simp
    · split
      · simp [ih, or_comm, or_assoc, or_left_comm]
      · split
        · simp
        · simp [ih, or_comm, or_assoc, or_left_comm]

/-- Membership in sorted list equals membership in original. -/
lemma mem_sortByDescMeasLex (m : α → Nat) (l : List α) (x : α) :
    x ∈ sortByDescMeasLex m l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortByDescMeasLex]
  | cons h t ih =>
    simp [sortByDescMeasLex, mem_insertByDescMeasLex m, ih]

/-! ### Permutation theorems -/

/-- `insertByDescMeasLex m x l` is a permutation of `x :: l`. -/
lemma insertByDescMeasLex_perm (m : α → Nat) (x : α) (l : List α) :
    List.Perm (insertByDescMeasLex m x l) (x :: l) := by
  induction l generalizing x with
  | nil => simp [insertByDescMeasLex]
  | cons h t ih =>
    dsimp [insertByDescMeasLex]
    split
    · rfl
    · split
      · have h_perm : List.Perm (insertByDescMeasLex m x t) (x :: t) := ih x
        have h_cons : List.Perm (h :: insertByDescMeasLex m x t) (h :: x :: t) :=
          List.Perm.cons h h_perm
        have h_swap : List.Perm (h :: x :: t) (x :: h :: t) := List.Perm.swap x h t
        exact List.Perm.trans h_cons h_swap
      · split
        · rfl
        · have h_perm : List.Perm (insertByDescMeasLex m x t) (x :: t) := ih x
          have h_cons : List.Perm (h :: insertByDescMeasLex m x t) (h :: x :: t) :=
            List.Perm.cons h h_perm
          have h_swap : List.Perm (h :: x :: t) (x :: h :: t) := List.Perm.swap x h t
          exact List.Perm.trans h_cons h_swap

/-- `sortByDescMeasLex m l` is a permutation of `l`. -/
lemma sortByDescMeasLex_perm (m : α → Nat) (l : List α) :
    List.Perm (sortByDescMeasLex m l) l := by
  induction l with
  | nil => simp [sortByDescMeasLex]
  | cons h t ih =>
    simp [sortByDescMeasLex]
    have h_insert : List.Perm (insertByDescMeasLex m h (sortByDescMeasLex m t))
        (h :: sortByDescMeasLex m t) :=
      insertByDescMeasLex_perm m h (sortByDescMeasLex m t)
    have h_cons : List.Perm (h :: sortByDescMeasLex m t) (h :: t) := List.Perm.cons h ih
    exact List.Perm.trans h_insert h_cons

/-! ### Sortedness theorems -/

/-- Inserting into a list already pairwise-sorted by `descByMeasureThenLex`
preserves the sorted property. -/
lemma insertByDescMeasLex_sorted (m : α → Nat) (x : α) (l : List α)
    (h_sorted : List.Pairwise (CompareBy.descByMeasureThenLex m) l) :
    List.Pairwise (CompareBy.descByMeasureThenLex m) (insertByDescMeasLex m x l) := by
  induction l generalizing x with
  | nil =>
    dsimp [insertByDescMeasLex]
    apply List.Pairwise.cons (by intro y hy; exfalso; exact List.not_mem_nil _ hy)
    exact List.Pairwise.nil
  | cons h t ih =>
    rcases List.pairwise_cons.mp h_sorted with ⟨h_h_all, h_t_sorted⟩
    dsimp [insertByDescMeasLex]
    by_cases h_gt : m x > m h
    · rw [if_pos h_gt]
      have h_sh : CompareBy.descByMeasureThenLex m x h := by
        dsimp [CompareBy.descByMeasureThenLex]; left; exact h_gt
      have h_all_x : ∀ y ∈ h :: t, CompareBy.descByMeasureThenLex m x y := by
        intro y hy
        rcases List.mem_cons.mp hy with (rfl | hy_t)
        · exact h_sh
        · exact (CompareBy.descByMeasureThenLex.trans m).trans x h y h_sh (h_h_all y hy_t)
      apply List.Pairwise.cons h_all_x
      apply List.Pairwise.cons h_h_all
      exact h_t_sorted
    · rw [if_neg h_gt]
      by_cases h_lt : m h > m x
      · rw [if_pos h_lt]
        have h_hs : CompareBy.descByMeasureThenLex m h x := by
          dsimp [CompareBy.descByMeasureThenLex]; left; exact h_lt
        have h_all_h : ∀ y ∈ insertByDescMeasLex m x t, CompareBy.descByMeasureThenLex m h y := by
          intro y hy
          rcases (mem_insertByDescMeasLex m x y t).mp hy with (rfl | hy_t)
          · exact h_hs
          · exact h_h_all y hy_t
        have h_t_sorted' : List.Pairwise (CompareBy.descByMeasureThenLex m) (insertByDescMeasLex m x t) :=
          ih x h_t_sorted
        apply List.Pairwise.cons h_all_h
        exact h_t_sorted'
      · rw [if_neg h_lt]
        have h_meas_eq : m x = m h := by omega
        by_cases h_le : x ≤ h
        · rw [if_pos h_le]
          have h_sh : CompareBy.descByMeasureThenLex m x h := by
            dsimp [CompareBy.descByMeasureThenLex]; right; exact ⟨h_meas_eq, h_le⟩
          have h_all_x : ∀ y ∈ h :: t, CompareBy.descByMeasureThenLex m x y := by
            intro y hy
            rcases List.mem_cons.mp hy with (rfl | hy_t)
            · exact h_sh
            · exact (CompareBy.descByMeasureThenLex.trans m).trans x h y h_sh (h_h_all y hy_t)
          apply List.Pairwise.cons h_all_x
          apply List.Pairwise.cons h_h_all
          exact h_t_sorted
        · rw [if_neg h_le]
          have h_hl : h ≤ x := le_of_not_ge h_le
          have h_hs : CompareBy.descByMeasureThenLex m h x := by
            dsimp [CompareBy.descByMeasureThenLex]; right; exact ⟨h_meas_eq.symm, h_hl⟩
          have h_all_h : ∀ y ∈ insertByDescMeasLex m x t, CompareBy.descByMeasureThenLex m h y := by
            intro y hy
            rcases (mem_insertByDescMeasLex m x y t).mp hy with (rfl | hy_t)
            · exact h_hs
            · exact h_h_all y hy_t
          have h_t_sorted' : List.Pairwise (CompareBy.descByMeasureThenLex m) (insertByDescMeasLex m x t) :=
            ih x h_t_sorted
          apply List.Pairwise.cons h_all_h
          exact h_t_sorted'

/-- The result of `sortByDescMeasLex` is pairwise sorted by `descByMeasureThenLex`. -/
lemma sortByDescMeasLex_sorted (m : α → Nat) (l : List α) :
    List.Pairwise (CompareBy.descByMeasureThenLex m) (sortByDescMeasLex m l) := by
  induction l with
  | nil => simp [sortByDescMeasLex]
  | cons h t ih =>
    dsimp [sortByDescMeasLex]
    exact insertByDescMeasLex_sorted m h (sortByDescMeasLex m t) ih

/-! ### Bridge from `Pairwise` to element-wise postcondition (descending) -/

/-- Bridge from `List.Pairwise (descByMeasureThenLex m)` to the element-wise postcondition:
if a list is pairwise sorted by descending-measure-then-element order, then for any `i < j` in bounds,
either `m (l[i]!) > m (l[j]!)` or `m (l[i]!) = m (l[j]!) ∧ l[i]! ≤ l[j]!`. -/
lemma pairwise_descMeasureThenElem_to_postcond [Inhabited α] (m : α → Nat) (l : List α)
    (h : List.Pairwise (CompareBy.descByMeasureThenLex m) l) :
    ∀ i j, i < j → i < l.length → j < l.length →
      (m (l[i]!) > m (l[j]!)) ∨
      (m (l[i]!) = m (l[j]!) ∧ l[i]! ≤ l[j]!) := by
  rw [List.pairwise_iff_get] at h
  intro i j hij hi hj
  rw [getElem!_pos l i hi, getElem!_pos l j hj]
  exact h ⟨i, hi⟩ ⟨j, hj⟩ hij

end List

namespace List

/-! ### Insertion sort by numeric key -/

/-- Insert `x` into `xs` which is sorted by numeric key `f` (ascending),
    preserving the sorted order. -/
def insertSortedBy {α : Type} (f : α → Nat) (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | h :: t =>
    if f x < f h then
      x :: xs
    else
      h :: insertSortedBy f x t

/-- Sort `xs` by numeric key `f` in ascending order, using insertion sort. -/
def sortByKey {α : Type} (f : α → Nat) (xs : List α) : List α :=
  xs.foldl (fun acc e => insertSortedBy f e acc) []

/-- `insertSortedBy` guarantees the inserted item is in the result list. -/
lemma mem_insertSortedBy {α : Type} {proj : α → Nat} (item : α) (l : List α) :
    item ∈ insertSortedBy proj item l := by
  induction l with
  | nil => simp [insertSortedBy]
  | cons h t ih =>
    simp [insertSortedBy]
    split
    · simp
    · simp [ih]

/-- `insertSortedBy` increases the list length by exactly one. -/
lemma length_insertSortedBy {α : Type} {proj : α → Nat} (item : α) (l : List α) :
    (insertSortedBy proj item l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertSortedBy]
  | cons h t ih =>
    simp [insertSortedBy]
    split <;> simp [ih]

/-! ### `sortedByKey` — predicate for key-sorted lists

`sortedByKey f l` expresses that `l` is sorted by key function `f` in non-decreasing
order. It is defined as `List.Pairwise (fun a b => f a ≤ f b) l`. The indexing lemmas
`sortedByKey_get` and `sortedByKey_iget` bridge this predicate to element access. -/

/-- A list is sorted by key function `f` in non-decreasing order.
This is the `List.Pairwise`-based predicate; use `sortedByKey_get` and
`sortedByKey_iget` to extract element-wise inequalities. -/
def sortedByKey {α : Type} (f : α → Nat) (l : List α) : Prop :=
  List.Pairwise (fun a b => f a ≤ f b) l

/-- If `l` is sorted by key `f`, then for any valid indices `i < j`,
`f (l.get ⟨i, hi⟩) ≤ f (l.get ⟨j, hj⟩)`. -/
lemma sortedByKey_get {α : Type} (f : α → Nat) (l : List α) (h : sortedByKey f l)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    f (l.get ⟨i, hi⟩) ≤ f (l.get ⟨j, hj⟩) := by
  have hrel := (List.pairwise_iff_get.mp h) ⟨i, hi⟩ ⟨j, hj⟩ (Fin.mk_lt_mk.mpr hij)
  exact hrel

/-- From a key-sorted list, the index-based comparison using `get?` and `iget` also holds.
This is a convenience wrapper around `sortedByKey_get` for the `get?`/`iget` API. -/
lemma sortedByKey_iget {α : Type} [Inhabited α] (f : α → Nat) (l : List α) (h : sortedByKey f l)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    f ((l[i]?).iget) ≤ f ((l[j]?).iget) := by
  have h_get_i : (l[i]?).iget = l.get ⟨i, hi⟩ := by
    simp [List.getElem?_eq_getElem hi]
  have h_get_j : (l[j]?).iget = l.get ⟨j, hj⟩ := by
    simp [List.getElem?_eq_getElem hj]
  rw [h_get_i, h_get_j]
  exact sortedByKey_get f l h i j hi hj hij

/-! ### More theorems about `insertSortedBy` -/

/-- Full membership equivalence for `insertSortedBy`: `y` is in `insertSortedBy f x xs`
iff `y = x` or `y ∈ xs`. This complements `mem_insertSortedBy` (one direction). -/
lemma mem_insertSortedBy_iff {α : Type} {f : α → Nat} (x y : α) (xs : List α) :
    y ∈ insertSortedBy f x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insertSortedBy]
  | cons z zs IH =>
    simp [insertSortedBy]
    split
    · simp [IH]
    · simp [IH, or_assoc, or_comm, or_left_comm]

/-- Lower bound preservation for `insertSortedBy`:
if `f a ≤ f x` and `f a ≤ f b` for every `b ∈ xs`,
then `f a ≤ f b` for every `b ∈ insertSortedBy f x xs`. -/
lemma insertSortedBy_lower_bound {α : Type} {f : α → Nat} {a x : α} {xs : List α}
    (h_le : f a ≤ f x) (h_all : ∀ b ∈ xs, f a ≤ f b) :
    ∀ b ∈ insertSortedBy f x xs, f a ≤ f b := by
  induction xs generalizing x a with
  | nil =>
    intro b hb
    simp [insertSortedBy] at hb
    subst hb
    exact h_le
  | cons y ys IH =>
    have hay : f a ≤ f y := h_all y (by simp)
    have h_ys : ∀ b ∈ ys, f a ≤ f b := by
      intro b hb; exact h_all b (mem_cons_of_mem y hb)
    intro b hb
    simp [insertSortedBy] at hb
    split at hb
    · -- hb : b ∈ x :: y :: ys (when f x < f y)
      simp at hb
      rcases hb with (rfl | hb')
      · exact h_le
      · rcases hb' with (rfl | hb_ys)
        · exact hay
        · exact h_ys b hb_ys
    · -- hb : b ∈ y :: insertSortedBy f x ys (when ¬ f x < f y)
      simp at hb
      rcases hb with (rfl | hb')
      · exact hay
      · exact IH h_le h_ys b hb'

/-- If `xs` is sorted by key `f` (i.e., `sortedByKey f xs`), then inserting `x`
via `insertSortedBy f` preserves that property. -/
lemma insertSortedBy_pairwise {α : Type} {f : α → Nat} {x : α} {xs : List α}
    (h : sortedByKey f xs) : sortedByKey f (insertSortedBy f x xs) := by
  induction xs generalizing x with
  | nil =>
    simp [insertSortedBy, sortedByKey]
  | cons y ys IH =>
    have h_pairwise : Pairwise (λ a b => f a ≤ f b) (y :: ys) := h
    cases h_pairwise with
    | cons hy_all h_ys =>
    simp [insertSortedBy]
    by_cases hx_lt_y : f x < f y
    · -- put x first: x :: y :: ys
      simp [hx_lt_y]
      have hx_le_y : f x ≤ f y := Nat.le_of_lt hx_lt_y
      have hx_all : ∀ b ∈ (y :: ys), f x ≤ f b := by
        intro b hb
        rcases List.mem_cons.mp hb with (rfl | hb_ys)
        · exact hx_le_y
        · exact le_trans hx_le_y (hy_all b hb_ys)
      unfold sortedByKey
      exact List.Pairwise.cons hx_all (List.Pairwise.cons hy_all h_ys)
    · -- put y first: y :: insertSortedBy f x ys
      simp [hx_lt_y]
      have hy_le_x : f y ≤ f x := Nat.le_of_not_gt hx_lt_y
      have hy_all_ins : ∀ b ∈ insertSortedBy f x ys, f y ≤ f b :=
        insertSortedBy_lower_bound hy_le_x hy_all
      have h_ins_pw : sortedByKey f (insertSortedBy f x ys) := IH h_ys
      unfold sortedByKey
      exact List.Pairwise.cons hy_all_ins h_ins_pw

/-- The result of `foldr (insertSortedBy f) [] xs` is sorted by key `f`. -/
lemma foldr_insertSortedBy_pairwise {α : Type} (f : α → Nat) (xs : List α) :
    sortedByKey f (foldr (insertSortedBy f) [] xs) := by
  induction xs with
  | nil => simp [sortedByKey]
  | cons x xs IH =>
    simp [foldr]
    exact insertSortedBy_pairwise IH

/-! ### Ordered insertion and insertion sort (LinearOrder) -/

/-- Sort a list in ascending order using insertion sort, via `foldr insertSorted []`.
Works for any `LinearOrder` type. -/
def sortList {α : Type u} [LinearOrder α] (xs : List α) : List α :=
  xs.foldr insertSorted []

/-- Inserting an element via `insertSorted` increases the list length by one. -/

theorem insertSorted_length {α : Type u} [LinearOrder α] (x : α) (xs : List α) :
    (insertSorted x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    unfold insertSorted
    split
    · rfl
    · simp [ih]

/-- Sorting a list via `sortList` preserves its length. -/

theorem sortList_length {α : Type u} [LinearOrder α] (xs : List α) :
    (sortList xs).length = xs.length := by
  induction xs with
  | nil => simp [sortList]
  | cons x xs ih =>
    simp [sortList, List.foldr, insertSorted_length]
    simpa [sortList] using ih

/-- Inserting `x` into `l` via `insertSorted` yields a list that is a permutation of `x :: l`.
In other words, `insertSorted` preserves the multiset of elements
(it just rearranges them into sorted position). -/
theorem insertSorted_perm {α : Type u} [LinearOrder α] (x : α) (l : List α) :
    List.Perm (insertSorted x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons h t ih =>
    unfold insertSorted
    split
    · exact List.Perm.refl _
    · have hcons := ih.cons h
      have hswap := (List.Perm.swap h x t).symm
      exact hcons.trans hswap

/-- `sortList` returns a permutation of the input list.
Sorting rearranges elements but does not add or remove any. -/
theorem sortList_perm {α : Type u} [LinearOrder α] (l : List α) :
    List.Perm (sortList l) l := by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    have h_eq : sortList (h :: t) = insertSorted h (sortList t) := by
      simp [sortList, List.foldr]
    rw [h_eq]
    have hins := insertSorted_perm h (sortList t)
    have hcons := ih.cons h
    exact hins.trans hcons

/-- `sortList` preserves the multiset of elements. -/
theorem sortList_multiset_eq {α : Type u} [LinearOrder α] (l : List α) :
    Multiset.ofList (sortList l) = Multiset.ofList l :=
  Quotient.sound (sortList_perm l)

/-- Membership is preserved by `insertSorted`. -/
lemma mem_insertSorted_iff {α : Type u} [LinearOrder α] (x y : α) (l : List α) :
    x ∈ insertSorted y l ↔ x = y ∨ x ∈ l := by
  have hperm := insertSorted_perm y l
  have hmem := hperm.mem_iff (a := x)
  simpa using hmem

/-- `insertSorted` preserves sortedness. -/
lemma insertSorted_sorted {α : Type u} [LinearOrder α] (x : α) (l : List α)
    (hsorted : List.Sorted (· ≤ ·) l) : List.Sorted (· ≤ ·) (insertSorted x l) := by
  induction' l with y ys ih generalizing x
  · exact List.sorted_singleton _
  · rw [List.sorted_cons] at hsorted
    rcases hsorted with ⟨h_all, h_sorted⟩
    by_cases hxy : x ≤ y
    · have h_insert : insertSorted x (y :: ys) = x :: y :: ys := by
        simp [insertSorted, hxy]
      rw [h_insert]
      rw [List.sorted_cons]
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases (List.mem_cons.mp hz) with (rfl | hz_in_ys)
        · exact hxy
        · exact le_trans hxy (h_all z hz_in_ys)
      · rw [List.sorted_cons]
        exact ⟨h_all, h_sorted⟩
    · have h_insert : insertSorted x (y :: ys) = y :: insertSorted x ys := by
        simp [insertSorted, hxy]
      rw [h_insert]
      rw [List.sorted_cons]
      constructor
      · intro z hz
        have hmem := ((insertSorted_perm x ys).mem_iff (a := z)).mp hz
        rcases (List.mem_cons.mp hmem) with (rfl | hz_in_ys)
        · exact le_of_not_ge hxy
        · exact h_all z hz_in_ys
      · exact ih x h_sorted

/-- `insertSorted` preserves `Nodup` when inserting an element not already present.
If `l` has no duplicates and `a` is not in `l`, then `insertSorted a l` has no duplicates. -/
lemma insertSorted_nodup {α : Type u} [LinearOrder α] (a : α) (l : List α)
    (hn : Nodup l) (ha : a ∉ l) : Nodup (insertSorted a l) := by
  induction l generalizing a with
  | nil =>
    simp [insertSorted]
  | cons h t ih =>
    rcases nodup_cons.mp hn with ⟨hnt, hntd⟩
    unfold insertSorted
    by_cases hah : a ≤ h
    · rw [if_pos hah]
      apply nodup_cons.mpr
      exact ⟨ha, hn⟩
    · rw [if_neg hah]
      apply nodup_cons.mpr
      constructor
      · intro hmem
        have hmem' := (mem_insertSorted_iff h a t).mp hmem
        rcases hmem' with (heq | hmem'')
        · subst heq; apply ha; simp
        · exact hnt hmem''
      · have ha' : a ∉ t := by
          intro ha_t; apply ha; simp [ha_t]
        exact ih a hntd ha'

/-- `sortList` produces a sorted list. -/
lemma sortList_sorted {α : Type u} [LinearOrder α] (l : List α) : List.Sorted (· ≤ ·) (sortList l) := by
  induction' l with x xs ih
  · exact List.sorted_nil
  · simp [sortList, List.foldr]
    apply insertSorted_sorted x (sortList xs) ih

/-- Membership is preserved by `sortList`: `x` is in `sortList l` iff `x` is in `l`. -/
lemma sortList_mem_iff {α : Type u} [LinearOrder α] {x : α} {l : List α} : x ∈ sortList l ↔ x ∈ l :=
  (sortList_perm l).mem_iff

/-! ### `SortedLE` — list sorted in non-decreasing order -/

/-- `SortedLE xs` means `xs` is sorted in non-decreasing order according to the `≤` relation.
This is a concise alias for `List.Sorted (· ≤ ·) xs`, generalized over any type with `LE`. -/
def SortedLE {α : Type u} [LE α] (xs : List α) : Prop :=
  xs.Sorted (· ≤ ·)

/-! ### Boolean versions of `Nodup` and `Sorted` -/

/-- Decidable version of `List.Nodup` as a Boolean. -/
def nodupB {α : Type u} [DecidableEq α] (xs : List α) : Bool :=
  decide (xs.Nodup)

/-- Decidable version of `List.Sorted (· ≤ ·)` as a Boolean. -/
def sortedB {α : Type u} [LinearOrder α] (xs : List α) : Bool :=
  decide (List.Sorted (· ≤ ·) xs)

/-- `nodupB` holds exactly when the underlying list is nodup. -/
lemma nodupB_eq_true_iff {α : Type u} [DecidableEq α] (xs : List α) :
    nodupB xs = true ↔ xs.Nodup := by
  simp [nodupB]

/-- `sortedB` holds exactly when the underlying list is sorted. -/
lemma sortedB_eq_true_iff {α : Type u} [LinearOrder α] (xs : List α) :
    sortedB xs = true ↔ List.Sorted (· ≤ ·) xs := by
  simp [sortedB]

/-! ### `isNonIncreasing` — non-increasing (descending) sequence check -/

/-- Check whether a list is non‑increasing: each element is ≥ the next one.
    Generic over any type with a decidable order.
    Forms the descending counterpart to `sortedB` (which checks non-decreasing ≤).
    For instance, `isNonIncreasing [5, 3, 3, 1] = true` (each element ≥ the next). -/
def isNonIncreasing {α : Type u} [LE α] [DecidableRel (α := α) (· ≤ ·)] (l : List α) : Bool :=
  match l with
  | [] | [_] => true
  | a :: b :: rest => decide (b ≤ a) && isNonIncreasing (b :: rest)

/-- `isNonIncreasing l = true` iff `l` is pairwise non-increasing (`List.Pairwise (· ≥ ·) l`).
This connects the boolean decidable test to the propositional pairwise ordering. -/
lemma isNonIncreasing_eq_true_iff [Preorder α] [DecidableRel (α := α) (· ≤ ·)] (l : List α) :
    isNonIncreasing l = true ↔ List.Pairwise (· ≥ ·) l := by
  constructor
  · intro h
    induction l with
    | nil => exact List.Pairwise.nil
    | cons a l ih =>
      cases l with
      | nil => exact List.pairwise_singleton _ _
      | cons b l =>
        unfold isNonIncreasing at h
        simp at h
        rcases h with ⟨hab, hrest⟩
        have hpair_rest : List.Pairwise (· ≥ ·) (b :: l) := ih hrest
        rcases (List.pairwise_cons.mp hpair_rest) with ⟨h_rest_forall, h_rest_pair⟩
        have h_forall : ∀ a' ∈ (b :: l), a ≥ a' := by
          intro a' ha'
          cases ha' with
          | head l => exact hab
          | tail _ ha'l =>
            have hba' : b ≥ a' := h_rest_forall a' ha'l
            exact le_trans hba' hab
        exact List.Pairwise.cons h_forall hpair_rest
  · intro h
    induction l with
    | nil => rfl
    | cons a l ih =>
      rcases (List.pairwise_cons.mp h) with ⟨h_forall, h_pair⟩
      cases l with
      | nil => rfl
      | cons b l =>
        have hab : b ≤ a := h_forall b (by simp)
        have hrest : isNonIncreasing (b :: l) = true := ih h_pair
        unfold isNonIncreasing
        simp [hab, hrest]

/-! ### `sorted_by` — sorted with respect to a projection -/

/-- `sorted_by proj l` states that `l` is sorted according to the given projection `proj`.
For instance, `sorted_by (·.1) l` means `l` is sorted by the first component. -/
def sorted_by {α β : Type} [LE β] (proj : α → β) (l : List α) : Prop :=
  List.Sorted (fun a b => proj a ≤ proj b) l

/-- The relation `(fun a b => proj a ≤ proj b)` induced by a projection into a `Preorder`
is transitive. Useful for `List.Sorted` induction with `sorted_by`. -/
lemma isTrans_proj {α β : Type} [Preorder β] (proj : α → β) : IsTrans α (fun a b => proj a ≤ proj b) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩

/-! ### Median of a sorted list -/

/-- Compute the median element of a list (lower median for even-length lists,
`default` for empty lists). The list is sorted internally via `sortList`. -/
def median {α : Type} [LinearOrder α] [Inhabited α] (l : List α) : α :=
  let s := sortList l
  let idx := s.length / 2
  match s[idx]? with
  | some v => v
  | none   => default

/-- Compute the median of an already-sorted list of `Nat`s.
For odd-length lists returns the middle element;
for even-length lists returns the floor average of the two middle elements.
Contrast with `median` which picks a single element for any `LinearOrder` type
and sorts the list internally. `medianOfSorted` is specialized to `Nat` because
it performs integer averaging for even-length lists. -/
def medianOfSorted (s : List Nat) : Nat :=
  let n := s.length
  if n % 2 = 1 then
    s.getD (n / 2) 0
  else
    (s.getD (n / 2 - 1) 0 + s.getD (n / 2) 0) / 2

/-! ### Ordered insertion and insertion sort (descending) -/

/-- Inserting an element via `insertSortedDesc` increases the list length by one. -/

theorem insertSortedDesc_length {α : Type u} [LinearOrder α] (x : α) (l : List α) :
    (insertSortedDesc x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    unfold insertSortedDesc
    split
    · rfl
    · simp [ih]

/-- Sorting a list via `sortDesc` preserves its length. -/

theorem sortDesc_length {α : Type u} [LinearOrder α] (l : List α) :
    (sortDesc l).length = l.length := by
  induction l with
  | nil => simp [sortDesc]
  | cons x xs ih =>
    simp [sortDesc, insertSortedDesc_length, ih]

/-! ### Ordered insertion and insertion sort (custom comparator) -/

/-- Insert `x` into `l` (which is expected to be sorted by `cmp`), maintaining the
sorted order under `cmp`. Works for any comparator `cmp : α → α → Bool`, making it
more general than `insertSorted` (which requires `LinearOrder α`) and `insertSortedBy`
(which requires a numeric key). -/
def insertByCmp {α : Type u} (cmp : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | (y :: ys) => if cmp x y then x :: y :: ys else y :: insertByCmp cmp x ys

/-- General-purpose insertion sort using a custom comparator `cmp : α → α → Bool`. -/
def sortByCmp {α : Type u} (cmp : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertByCmp cmp x (sortByCmp cmp xs)

/-- Inserting an element via `insertByCmp` increases the list length by one. -/

theorem insertByCmp_length {α : Type u} (cmp : α → α → Bool) (x : α) (l : List α) :
    (insertByCmp cmp x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    unfold insertByCmp
    split
    · rfl
    · simp [ih]

/-- If `x` appears in the result of `insertByCmp cmp y l`, then `x = y` or `x ∈ l`. -/
lemma mem_insertByCmp {α : Type u} (cmp : α → α → Bool) (x y : α) (l : List α)
    (h : x ∈ insertByCmp cmp y l) : x = y ∨ x ∈ l := by
  induction l generalizing x y with
  | nil =>
      unfold insertByCmp at h; simp at h; exact Or.inl h
  | cons hd tl ih =>
      unfold insertByCmp at h
      by_cases hcmp : cmp y hd
      · simp [hcmp] at h
        rcases h with (hx|hx|hx)
        · exact Or.inl hx
        · exact Or.inr (by simp [hx])
        · exact Or.inr (by simp [hx])
      · simp [hcmp] at h
        rcases h with (hx|hx)
        · exact Or.inr (by simp [hx])
        · rcases ih x y hx with (hx'|hx')
          · exact Or.inl hx'
          · exact Or.inr (by simp [hx'])

/-- Sorting via `sortByCmp` preserves the list length. -/

theorem sortByCmp_length {α : Type u} (cmp : α → α → Bool) (l : List α) :
    (sortByCmp cmp l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold sortByCmp
    rw [insertByCmp_length, ih]
    simp

/-- If `x` appears in the result of `sortByCmp cmp l`, then `x ∈ l`. -/
lemma mem_of_mem_sortByCmp {α : Type u} (cmp : α → α → Bool) (x : α) (l : List α)
    (h : x ∈ sortByCmp cmp l) : x ∈ l := by
  induction l with
  | nil =>
      unfold sortByCmp at h
      simp at h
  | cons hd tl ih =>
      unfold sortByCmp at h
      rcases mem_insertByCmp cmp x hd (sortByCmp cmp tl) h with (rfl | hmem)
      · simp
      · have htl := ih hmem
        simp [htl]

end List


namespace List

/-! ### Merge of two sorted lists -/

/-- Merge two sorted lists into one sorted list.
- `mergeSorted [] l = l`
- `mergeSorted l [] = l`
- For nonempty lists, takes the smaller head and recurses.

This is the standard merge step from merge sort; works for any `LinearOrder α`. -/
def mergeSorted {α : Type} [LinearOrder α] : List α → List α → List α
  | [], l => l
  | l, [] => l
  | (h1 :: t1), (h2 :: t2) =>
      if h1 ≤ h2 then
        h1 :: mergeSorted t1 (h2 :: t2)
      else
        h2 :: mergeSorted (h1 :: t1) t2

/-- Characterization of membership in `mergeSorted`: an element belongs to the merged list
iff it belongs to at least one of the input lists (forward direction). -/
lemma mem_mergeSorted {α : Type} [LinearOrder α] {l1 l2 : List α} {x : α} (h : x ∈ mergeSorted l1 l2) :
    x ∈ l1 ∨ x ∈ l2 := by
  induction l1, l2 using mergeSorted.induct with
  | case1 l2' =>
    simp [mergeSorted] at h
    exact Or.inr h
  | case2 h1 t1 =>
    simp [mergeSorted] at h
    exact Or.inl h
  | case3 h1 t1 h2 t2 hcmp ih =>
    simp [mergeSorted, hcmp] at h
    rcases h with (rfl | hm)
    · exact Or.inl (by simp)
    · rcases ih hm with (hl | hr)
      · exact Or.inl (List.mem_cons_of_mem _ hl)
      · exact Or.inr hr
  | case4 h1 t1 h2 t2 hcmp ih =>
    simp [mergeSorted, hcmp] at h
    rcases h with (rfl | hm)
    · exact Or.inr (by simp)
    · rcases ih hm with (hl | hr)
      · exact Or.inl hl
      · exact Or.inr (List.mem_cons_of_mem _ hr)

/-- `mergeSorted` is a permutation of the concatenation of the input lists:
`List.Perm (l₁ ++ l₂) (mergeSorted l₁ l₂)`. -/
lemma mergeSorted_perm {α : Type} [LinearOrder α] (l₁ l₂ : List α) :
    List.Perm (l₁ ++ l₂) (mergeSorted l₁ l₂) := by
  induction l₁, l₂ using mergeSorted.induct with
  | case1 l₂' =>
    simp [mergeSorted]
  | case2 a as =>
    simp [mergeSorted]
  | case3 a as b bs hle ih =>
    simp [mergeSorted, hle]
    have h := ih.cons a
    simpa using h
  | case4 a as b bs hnle ih =>
    simp [mergeSorted, hnle]
    have h1 : List.Perm ((a :: as) ++ (b :: bs)) ((b :: bs) ++ (a :: as)) :=
      List.perm_append_comm
    have h3 : List.Perm (b :: (bs ++ (a :: as))) (b :: ((a :: as) ++ bs)) :=
      List.Perm.cons b List.perm_append_comm
    have h4 : List.Perm (b :: ((a :: as) ++ bs)) (b :: mergeSorted (a :: as) bs) :=
      ih.cons b
    simpa using h1.trans (h3.trans h4)

/-- Characterization of membership in `mergeSorted` (bidirectional):
an element belongs to the merged list iff it belongs to at least one of the input lists. -/
lemma mergeSorted_mem_iff {α : Type} [LinearOrder α] (l1 l2 : List α) (x : α) :
    x ∈ mergeSorted l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  constructor
  · exact mem_mergeSorted
  · intro h
    have hmem : x ∈ l1 ++ l2 := (List.mem_append).mpr h
    exact (mergeSorted_perm l1 l2).mem_iff.mp hmem

/-- If an element `a` is ≤ every element of both input lists, then `a` is ≤ every element
of the merged list. -/
lemma mergeSorted_all_ge {α : Type} [LinearOrder α] {a : α} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, a ≤ x) (h2 : ∀ x ∈ l2, a ≤ x) : ∀ x ∈ mergeSorted l1 l2, a ≤ x := by
  intro x hx
  rcases mem_mergeSorted hx with (hx' | hx')
  · exact h1 x hx'
  · exact h2 x hx'

/-- `mergeSorted` preserves sortedness: if both input lists are sorted by `≤`,
then the merged list is also sorted by `≤`. -/
lemma mergeSorted_sorted {α : Type} [LinearOrder α] (l1 l2 : List α)
    (h1 : List.Sorted (· ≤ ·) l1) (h2 : List.Sorted (· ≤ ·) l2) :
    List.Sorted (· ≤ ·) (mergeSorted l1 l2) := by
  induction l1, l2 using mergeSorted.induct with
  | case1 l2' =>
    simp [mergeSorted, h2]
  | case2 h1' t1' =>
    simp [mergeSorted, h1]
  | case3 h1' t1' h2' t2' hcmp ih =>
    rcases (List.pairwise_cons.mp h1) with ⟨h1_all, h1_sorted⟩
    have h2_all' : ∀ x ∈ (h2' :: t2'), h1' ≤ x := by
      intro x hx
      simp at hx
      rcases hx with (rfl | hx_t2)
      · exact hcmp
      · rcases (List.pairwise_cons.mp h2) with ⟨h2_all, _⟩
        exact le_trans hcmp (h2_all x hx_t2)
    simp [mergeSorted, hcmp]
    constructor
    · exact mergeSorted_all_ge h1_all h2_all'
    · exact ih h1_sorted h2
  | case4 h1' t1' h2' t2' hcmp ih =>
    rcases (List.pairwise_cons.mp h2) with ⟨h2_all, h2_sorted⟩
    have hcmp' : h2' ≤ h1' := le_of_lt (lt_of_not_ge hcmp)
    have h1_all' : ∀ x ∈ (h1' :: t1'), h2' ≤ x := by
      intro x hx
      simp at hx
      rcases hx with (rfl | hx_t1)
      · exact hcmp'
      · rcases (List.pairwise_cons.mp h1) with ⟨h1_all, _⟩
        exact le_trans hcmp' (h1_all x hx_t1)
    simp [mergeSorted, hcmp]
    constructor
    · exact mergeSorted_all_ge h1_all' h2_all
    · exact ih h1 h2_sorted

/-- The length of `mergeSorted l₁ l₂` equals the sum of the lengths of `l₁` and `l₂`. -/
lemma mergeSorted_length {α : Type} [LinearOrder α] (l₁ l₂ : List α) :
    (mergeSorted l₁ l₂).length = l₁.length + l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp [mergeSorted]
  | cons x xs ih =>
    induction l₂ with
    | nil => simp [mergeSorted]
    | cons y ys ih_inner =>
      simp [mergeSorted]
      split
      · simp [ih, add_comm, add_left_comm, add_assoc]
      · simp [ih_inner, add_comm, add_left_comm, add_assoc]

/-! ### Reverse of merge-sorted list is a permutation -/

/-- The reverse of a merge-sorted list (descending order) is a permutation of the original list.
Useful when working with descending-order sorted lists. -/
lemma reverse_mergeSort_perm {α : Type} [LinearOrder α] (l : List α) :
    List.Perm (List.reverse (l.mergeSort (· ≤ ·))) l := by
  have h_merge := List.mergeSort_perm l (· ≤ ·)
  have h_rev := List.reverse_perm (l.mergeSort (· ≤ ·))
  exact h_rev.trans h_merge

/-- An element is not in the merge-sorted list iff it is not in the original list.
This is the contrapositive of `List.mem_mergeSort`. -/
lemma not_mem_mergeSort {α : Type} [LinearOrder α] {l : List α} {m : α} :
    (m ∉ List.mergeSort l (· ≤ ·)) ↔ (m ∉ l) := by
  simp [List.mem_mergeSort]

/-! ### All interleavings (merges) of two lists -/

/-- Generate all interleavings of two lists.
Each element in the result is a list formed by interleaving the elements of `l₁` and `l₂`
while preserving the relative order within each input list. -/
def allMerges : List α → List α → List (List α)
| [], ys => [ys]
| xs, [] => [xs]
| x :: xs, y :: ys =>
    (allMerges xs (y :: ys)).map (fun m => x :: m) ++
    (allMerges (x :: xs) ys).map (fun m => y :: m)

/-- `allMerges l₁ l₂` is never empty. -/
lemma allMerges_ne_nil (l₁ l₂ : List α) : allMerges l₁ l₂ ≠ [] := by
  induction l₁ generalizing l₂ with
  | nil => simp [allMerges]
  | cons c₁ t₁ ih₁ =>
    induction l₂ with
    | nil => simp [allMerges]
    | cons c₂ t₂ ih₂ =>
      unfold allMerges
      intro h
      have hleft := (List.append_eq_nil_iff.mp h).left
      cases hmap : allMerges t₁ (c₂ :: t₂) with
      | nil => exact ih₁ (c₂ :: t₂) hmap
      | cons x xs => simp [hmap] at hleft

/-- Mapping a non-empty list gives a non-empty list; useful with `allMerges_ne_nil`. -/
lemma allMerges_map_ne_nil (l₁ l₂ : List α) (f : List α → β) : (allMerges l₁ l₂).map f ≠ [] := by
  intro h
  exact allMerges_ne_nil l₁ l₂ (List.map_eq_nil_iff.mp h)

end List
