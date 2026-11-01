import Mathlib
import general.List.Count
import general.List.ExtremumSelection
import general.List.Pairs

namespace List


/-! ### Filter nonemptiness -/

/-- If `a ∈ xs` and `p a = true`, then `xs.filter p` is nonempty. -/
lemma filter_nonempty_of_mem {α : Type u} {xs : List α} {p : α → Bool} {a : α} (h : a ∈ xs) (hp : p a = true) :
    xs.filter p ≠ [] := by
  intro hnil
  have hmem : a ∈ xs.filter p := by
    apply List.mem_filter.mpr
    exact ⟨h, hp⟩
  rw [hnil] at hmem
  simp at hmem




/-! ### `filterNonEmpty` -/

/-- Filter out empty strings from a list of strings. -/
def filterNonEmpty (l : List String) : List String :=
  l.filter (fun t => t ≠ "")

theorem filterNonEmpty_length_le (l : List String) :
    (filterNonEmpty l).length ≤ l.length := by
  simp [filterNonEmpty, List.length_filter_le]

/-! ### Filter length helper lemmas -/

/-- If `p y` holds, the length of `filter p (y :: ys)` is one more than `filter p ys`. -/
lemma length_filter_cons_of_pos {α : Type} (p : α → Bool) (y : α) (ys : List α) (h : p y) :
    ((y :: ys).filter p).length = 1 + (ys.filter p).length := by
  simp [h, add_comm]

/-- If `¬ p y`, the length of `filter p (y :: ys)` equals `filter p ys`. -/
lemma length_filter_cons_of_neg {α : Type} (p : α → Bool) (y : α) (ys : List α) (h : p y = false) :
    ((y :: ys).filter p).length = (ys.filter p).length := by
  simp [h]

/-- If a predicate is `false` on an element, filtering a singleton list by that predicate yields `[]`. -/
lemma filter_singleton_eq_nil {α : Type} (p : α → Bool) (x : α) (h : p x = false) :
    List.filter p [x] = [] := by
  simp [h]

/-- Filter lengths are invariant under permutation. -/
lemma filter_length_perm {α : Type} (p : α → Bool) {l₁ l₂ : List α} (h : List.Perm l₁ l₂) :
    (l₁.filter p).length = (l₂.filter p).length :=
  (h.filter p).length_eq

/-- If `l₁` is a permutation of `l₂`, then any property holding for every element of `l₂`
also holds for every element of `l₁`. -/
lemma forall_mem_of_perm {α : Type} {l₁ l₂ : List α} (hperm : List.Perm l₁ l₂) {P : α → Prop}
    (h : ∀ x ∈ l₂, P x) : ∀ x ∈ l₁, P x := by
  intro x hx
  apply h
  exact (hperm.mem_iff.mp hx)



/-! ### `filter_any_eq` — commuting `filter` and `any` -/

/-- `(l.filter P).any Q = l.any (fun x => P x && Q x)`.
This allows merging two passes (filter then any) into a single pass. -/
lemma filter_any_eq {α : Type} (l : List α) (P Q : α → Bool) :
    (l.filter P).any Q = l.any (fun x => P x && Q x) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : P x
    · simp [h, List.any_cons, ih]
    · simp [h, List.any_cons, ih]


end List

namespace List

/-! ### Filter out equal elements -/

/-- Filter out all elements equal to a given value `a` from list `l`.
`filterNe l a = [x ∈ l | x ≠ a]`. -/
def filterNe {α : Type} [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (fun x => x ≠ a)

/-- `filterNe` removes the first occurrence of the target value
from subsequent occurrences. -/
lemma filterNe_nil {α : Type} [DecidableEq α] (a : α) : filterNe ([] : List α) a = [] := rfl

/-- `filterNe` over a `cons`. -/
lemma filterNe_cons {α : Type} [DecidableEq α] (a x : α) (xs : List α) :
    filterNe (x :: xs) a = (if x = a then filterNe xs a else x :: filterNe xs a) := by
  unfold filterNe
  simp only [List.filter_cons]
  by_cases h : x = a
  · subst h; simp
  · have hne : x ≠ a := h
    simp [hne]

/-- If `x` is not in `l`, then `filterNe l x` returns `l` unchanged. -/
lemma filterNe_of_not_mem {α : Type} [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
    filterNe l x = l := by
  unfold filterNe
  apply List.filter_eq_self.mpr
  intro a ha
  have ha_ne : a ≠ x := by
    intro heq
    apply h
    subst heq
    exact ha
  simp [ha_ne]

/-- If filtering out all elements not equal to `m` from `l` yields the empty list,
then every element of `l` equals `m`. -/
lemma forall_eq_of_filter_ne_empty {α : Type} [DecidableEq α] {l : List α} {m : α}
    (hfilter : (l.filter (fun x => x != m)) = []) : ∀ x ∈ l, x = m := by
  intro x hx
  by_contra hne
  have hx_mem : x ∈ l.filter (fun x => x != m) := by
    rw [List.mem_filter]
    exact ⟨hx, by simpa using hne⟩
  rw [hfilter] at hx_mem
  simp at hx_mem

/-- If every element of `l` equals `a`, then filtering out elements not equal to `a`
yields the empty list. This is the forward direction of the equivalence with
`forall_eq_of_filter_ne_empty`. -/
lemma filter_ne_eq_nil_of_forall_eq {α : Type} [DecidableEq α] (l : List α) (a : α)
    (h : ∀ x ∈ l, x = a) : l.filter (fun x => x ≠ a) = [] := by
  refine (List.filter_eq_nil_iff (p := fun x => x ≠ a)).mpr ?_
  intro x hx
  have hx_eq : x = a := h x hx
  subst hx_eq
  simp

/-- Membership in `filterNe l a` is equivalent to membership in `l` and inequality with `a`. -/
lemma mem_filterNe_iff {α : Type} [DecidableEq α] (l : List α) (a x : α) :
    x ∈ filterNe l a ↔ x ∈ l ∧ x ≠ a := by
  simp [filterNe]

/-- `filterNe` preserves `Nodup`. -/
lemma filterNe_nodup {α : Type} [DecidableEq α] (l : List α) (a : α) (h : l.Nodup) :
    (filterNe l a).Nodup :=
  h.filter _

/-- Removing an element `a` that belongs to a nodup list reduces its length by exactly 1. -/
lemma filterNe_length_nodup {α : Type} [DecidableEq α] (l : List α) (a : α) (hnodup : l.Nodup) (hmem : a ∈ l) :
    (filterNe l a).length + 1 = l.length := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    have hn_cons := List.nodup_cons.mp hnodup
    have hx_not_mem : x ∉ xs := hn_cons.1
    have hn : xs.Nodup := hn_cons.2
    simp at hmem
    rcases hmem with (heq | hmem)
    · subst heq
      unfold filterNe
      have hdrop : ((a :: xs).filter (fun y => y ≠ a)) = xs.filter (fun y => y ≠ a) := by
        simp
      rw [hdrop]
      rw [List.length_cons]
      have h_filter_eq : xs.filter (fun y => y ≠ a) = xs :=
        filterNe_of_not_mem hx_not_mem
      rw [h_filter_eq]
    · have hx_ne_a : x ≠ a := by
        intro heq; subst heq; exact hx_not_mem hmem
      have ih' := ih hn hmem
      unfold filterNe
      have hfilter : ((x :: xs).filter (fun y => y ≠ a)) = x :: (xs.filter (fun y => y ≠ a)) := by
        simp [hx_ne_a]
      rw [hfilter]
      simp
      simpa [filterNe] using ih'

end List


namespace List

/-! ### `filterMapSnd` — filter pairs by second component, then project to first -/

/-- Filter a list of `(α × β)` pairs by a predicate on the second element,
    then project to the first element.
    For example, `filterMapSnd (· > 3) [("a", 5), ("b", 2), ("c", 4)] = ["a", "c"]`. -/
def filterMapSnd {α β : Type} (p : β → Bool) (xs : List (α × β)) : List α :=
  (xs.filter (fun x => p x.snd)).map Prod.fst

/-! ### `filterMapBy` — map elements then filter by predicate on the result -/

/-- Apply `f` to each element of `l`, then keep only those results that satisfy `pred`.
This is a single-pass version of `(l.map f).filter pred`, more efficient for large lists.
For example, `filterMapBy (· ^ 2) (· > 10) [2, 3, 4] = [16]`. -/
def filterMapBy {α β : Type} (f : α → β) (pred : β → Bool) (l : List α) : List β :=
  l.filterMap (fun a =>
    let b := f a
    if pred b then some b else none)

/-- `filterMapBy f pred l` is equivalent to `(l.map f).filter pred`. -/
lemma filterMapBy_eq_map_filter {α β : Type} {f : α → β} {pred : β → Bool} {l : List α} :
    filterMapBy f pred l = (l.map f).filter pred := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    unfold filterMapBy
    simp [List.filterMap_cons]
    rcases hp : pred (f a) with (true | false)
    · simpa [filterMapBy, hp] using congrArg (fun l => f a :: l) ih
    · simpa [filterMapBy, hp] using ih

/-- Membership in `filterMapBy f pred l`: `b ∈ filterMapBy f pred l` iff `∃ a ∈ l, f a = b ∧ pred b`. -/
lemma mem_filterMapBy {α β : Type} {f : α → β} {pred : β → Bool} {l : List α} {b : β} :
    b ∈ filterMapBy f pred l ↔ ∃ a ∈ l, f a = b ∧ pred b := by
  rw [filterMapBy_eq_map_filter]
  simp only [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h⟩; exact ⟨a, ha, rfl, h⟩
  · rintro ⟨a, ha, rfl, h⟩; exact ⟨⟨a, ha, rfl⟩, h⟩

/-! ### `filterThenMap` — filter by predicate, then map (dual of `filterMapBy`) -/

/-- Filter a list by a predicate `p` on the input elements, then project each retained
    element through `f`. This is the dual of `filterMapBy` (which maps first, then filters).
    Equivalent to `(l.filter p).map f`.
    For example, `filterThenMap (· ≥ 5) (· * 2) [3,5,2,7] = [10,14]`. -/
def filterThenMap {α β : Type} (p : α → Bool) (f : α → β) (l : List α) : List β :=
  (l.filter p).map f

/-- Membership in `filterThenMap p f l`: `b` appears in the output iff there exists
    an input element `a ∈ l` that satisfies `p` and maps to `b`. -/
lemma mem_filterThenMap {α β : Type} (p : α → Bool) (f : α → β) {l : List α} {b : β} :
    b ∈ filterThenMap p f l ↔ ∃ a, a ∈ l ∧ p a ∧ f a = b := by
  simp [filterThenMap, List.mem_map, List.mem_filter, and_assoc]

/-! ### `mem_filter` with boolean negation -/

/-- Membership in `List.filter (λ x => !p x) l` is equivalent to `a ∈ l ∧ ¬ (p a = true)`.
This bridges `List.mem_filter` (which operates on `Bool` predicates) with the propositional
view `¬ (p a = true)`, useful when a filter condition is a negated boolean predicate and
the proof goals use `Prop`-level negation. -/
lemma mem_filter_not_eq_true_iff {α : Type} {p : α → Bool} {a : α} {l : List α} :
    a ∈ List.filter (λ x => !p x) l ↔ a ∈ l ∧ ¬ (p a = true) := by
  constructor
  · intro h
    rcases List.mem_filter.mp h with ⟨hmem, hcond⟩
    refine ⟨hmem, ?_⟩
    by_cases hp : p a = true
    · exfalso
      rw [hp] at hcond
      simp at hcond
    · exact hp
  · intro ⟨hmem, hnot⟩
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    have hp_false : p a = false := Bool.eq_false_of_not_eq_true hnot
    simp [hp_false]

/-! ### `filter` / `map` interaction — identity-on-predicate lemmas -/

/-- If `f : α → α` preserves a decidable predicate `P` and acts as identity on elements
satisfying `P`, then filtering `l` by `P` is unchanged by mapping `f` first:
`(l.map f).filter (fun a => decide (P a)) = l.filter (fun a => decide (P a))`.

This is useful when a transformation deletes or replaces non-satisfying elements
while leaving satisfying ones intact (e.g., renaming characters to a fallback), so
the set of satisfying elements is preserved under the mapping. -/
lemma filter_map_eq_filter_of_id_on_pred {α : Type} (f : α → α) (P : α → Prop) [DecidablePred P]
    (h_pres : ∀ a, P (f a) ↔ P a) (h_id : ∀ a, P a → f a = a) (l : List α) :
    (l.map f).filter (fun a => decide (P a)) = l.filter (fun a => decide (P a)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have hdec : decide (P (f a)) = decide (P a) := by simp [h_pres a]
    rw [hdec]
    by_cases hd : decide (P a) = true
    · rw [if_pos hd, if_pos hd]
      have hP : P a := by simpa using hd
      rw [h_id a hP, ih]
    · rw [if_neg hd, if_neg hd, ih]

/-! ### `filterIndices` — filter indices by element predicate -/

/-- Given a list `l`, a predicate `f`, and a bound `n`, return the indices `j < n` where
`f (l[j]?)` holds (treating out-of-bounds retrievals as `false`).
This is useful for finding positions in a list where elements satisfy a condition,
bounded by a maximum index. -/
def filterIndices {α : Type} (l : List α) (f : α → Bool) (n : Nat) : List Nat :=
  (List.range n).filter (fun j =>
    match l[j]? with
    | some x => f x
    | none => false)

/-- `filterIndices` with a `decide (· = a)` predicate is equivalent to filtering
`List.range n` by `decide (l[i]? = some a)`. -/
lemma filterIndices_eq_filter_decide_eq [DecidableEq α] (l : List α) (a : α) (n : Nat) :
    filterIndices l (fun x => decide (x = a)) n =
    (List.range n).filter (fun i => decide (l[i]? = some a)) := by
  unfold filterIndices
  congr
  ext i
  match l[i]? with
  | none => simp
  | some _ => simp

end List

namespace List

/-! ### `sum_filter_add_sum_filter_not` — partition list sum by a Bool predicate -/

/-- Sum of elements satisfying `p` plus sum of elements not satisfying `p` equals total sum.
This is the `List` analogue of `Finset.sum_filter_add_sum_filter_not`, specialized to `Nat`.
For a version with a custom function `f : α → Nat`, combine with `List.map`. -/
lemma sum_filter_add_sum_filter_not (l : List Nat) (p : Nat → Bool) :
    (l.filter p).sum + (l.filter (fun x => !(p x))).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.sum_cons]
    split
    · rename_i h; simp [h, add_assoc, ih]
    · rename_i h; simp [h, ih, add_comm, add_left_comm, add_assoc]

/-- The length of `filter p l` plus the length of `filter (¬ p) l` equals the length of `l`.
This is the partition identity for list lengths — the list is partitioned by the Boolean predicate
`p`. This is the length analogue of `sum_filter_add_sum_filter_not` (which sums the values). -/
lemma length_filter_add_filter_not {α : Type _} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (λ x => !(p x))).length = l.length := by
  induction' l with x xs ih
  · rfl
  · cases hp : p x with
    | true =>
      simp [hp]
      omega
    | false =>
      simp [hp]
      omega

/-- The length of `filter p l` equals `l.length` minus the length of `filter (¬ p) l`.
A subtraction variant of `length_filter_add_filter_not`. -/
lemma length_filter_eq_sub_length_filter_not {α : Type _} (l : List α) (p : α → Bool) :
    (l.filter p).length = l.length - (l.filter (λ x => !(p x))).length := by
  have h := length_filter_add_filter_not l p
  omega

/-- `(l.filter (· < k)).sum + (l.filter (k ≤ ·)).sum = l.sum`.
A convenient specialization of `sum_filter_add_sum_filter_not` for threshold-based
partitions, where `< k` and `k ≤ ·` form a complementary partition of `Nat`. -/
lemma sum_filter_lt_add_sum_filter_ge (l : List Nat) (k : Nat) :
    (l.filter (· < k)).sum + (l.filter (k ≤ ·)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.sum_cons]
    by_cases hx : x < k
    · have hnge : ¬ (k ≤ x) := by omega
      simp [hx, hnge, add_assoc, ih]
    · have hge : k ≤ x := by omega
      simp [hx, hge]
      omega

end List
