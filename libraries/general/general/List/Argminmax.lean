import Mathlib
import general.Common.Option
import general.List.ExtremumSelection
import general.List.Slicing
import general.List.Sort

namespace List

/-! ### `argminByMeasure` — argmin by a measure function -/

section argminByMeasure

variable {α : Type u} [LinearOrder α] (f : α → Nat)

/-- **Case 1 (strictly smaller)**: if `r` is optimal for `xs` and `f x < f r`,
    then `x` is optimal for `x :: xs`. -/
lemma argminByMeasure_optimal_strictly_smaller {x r : α} {xs : List α}
    (hopt : ∀ y, y ∈ xs → f r ≤ f y ∧ (f r = f y → r ≥ y))
    (hlt : f x < f r) :
    x ∈ x :: xs ∧ (∀ y, y ∈ x :: xs → f x ≤ f y ∧ (f x = f y → x ≥ y)) := by
  constructor
  · simp
  · intro y hy
    rcases (by simpa using hy) with (rfl | hy')
    · simp
    · rcases hopt y hy' with ⟨hle, himp⟩
      have hlt_xy : f x < f y := Nat.lt_of_lt_of_le hlt hle
      constructor
      · exact Nat.le_of_lt hlt_xy
      · intro heq
        exfalso
        exact Nat.lt_irrefl _ (calc
          f x < f y := hlt_xy
          _ = f x := heq.symm)

/-- **Case 2 (equal)**: if `r` is optimal for `xs` and `f x = f r`,
    then `max x r` is optimal for `x :: xs`. -/
lemma argminByMeasure_optimal_equal {x r : α} {xs : List α}
    (hmem : r ∈ xs) (hopt : ∀ y, y ∈ xs → f r ≤ f y ∧ (f r = f y → r ≥ y))
    (heq : f x = f r) :
    max x r ∈ x :: xs ∧
    (∀ y, y ∈ x :: xs → f (max x r) ≤ f y ∧ (f (max x r) = f y → max x r ≥ y)) := by
  have hmax_f : f (max x r) = f x := by
    rcases le_total x r with (hle | hge)
    · rw [max_eq_right hle, heq]
    · rw [max_eq_left hge]
  have hmem_max : max x r ∈ x :: xs := max_mem_cons_of_mem hmem
  constructor
  · exact hmem_max
  · intro y hy
    rcases (by simpa using hy) with (rfl | hy')
    · constructor
      · rw [hmax_f]
      · intro _; exact le_max_left _ _
    · rcases hopt y hy' with ⟨hle, himp⟩
      constructor
      · rw [hmax_f, heq]
        exact hle
      · intro h_eq_max_y
        have h_eq_r_y : f r = f y := by
          rw [hmax_f, heq] at h_eq_max_y
          exact h_eq_max_y
        exact le_trans (himp h_eq_r_y) (le_max_right _ _)

/-- Given a measure `f : α → ℕ` and a list, returns the element minimizing `f`,
    breaking ties by the larger element. For the empty list, returns `default`. -/
def argminByMeasure (f : α → Nat) (default : α) : List α → α
  | [] => default
  | [x] => x
  | x :: y :: rest =>
    let r := argminByMeasure f default (y :: rest)
    if f x < f r then x
    else if f x = f r then max x r
    else r

end argminByMeasure

/-! ### `argmaxBy` — argmax by a measure function, tie-breaking by smaller element -/

/-- Find the element in `xs` that maximizes `f : α → Nat`, breaking ties by choosing the smallest element.
Returns `default` for an empty list. This is the dual of `argminByMeasure`: where `argminByMeasure` minimizes
and breaks ties by choosing the *larger* element, `argmaxBy` maximizes and breaks ties by choosing the *smaller*
element. -/
def argmaxBy {α : Type} [Inhabited α] [LinearOrder α] (f : α → Nat) : List α → α
  | [] => default
  | [x] => x
  | x :: y :: zs =>
    let r := argmaxBy f (y :: zs)
    if f x > f r then x
    else if f x < f r then r
    else if x < r then x
    else r


lemma argmaxBy_singleton {α : Type} [Inhabited α] [LinearOrder α] (f : α → Nat) (x : α) :
    argmaxBy f [x] = x := rfl

/-- `argmaxBy f xs` is a member of `xs` when `xs` is nonempty. -/
lemma argmaxBy_mem {α : Type} [Inhabited α] [LinearOrder α]
    (f : α → Nat) (xs : List α) (h : xs ≠ []) : argmaxBy f xs ∈ xs := by
  induction xs with
  | nil => exact absurd rfl h
  | cons x xs' ih =>
    cases xs' with
    | nil => simp [argmaxBy]
    | cons y zs =>
      have hne' : y :: zs ≠ [] := by simp
      have ih_res : argmaxBy f (y :: zs) ∈ y :: zs := ih hne'
      have h_cases : argmaxBy f (y :: zs) = y ∨ argmaxBy f (y :: zs) ∈ zs := by
        simpa [List.mem_cons] using ih_res
      have hmem : argmaxBy f (y :: zs) ∈ x :: y :: zs := by
        rcases h_cases with (h_eq | h_mem)
        · rw [h_eq]; simp
        · simp [h_mem]
      by_cases hgt : f x > f (argmaxBy f (y :: zs))
      · simp [argmaxBy, hgt]
      · by_cases hlt : f x < f (argmaxBy f (y :: zs))
        · simp [argmaxBy, hgt, hlt, hmem]
        · by_cases hlt2 : x < argmaxBy f (y :: zs)
          · simp [argmaxBy, hgt, hlt, hlt2]
          · simp [argmaxBy, hgt, hlt, hlt2, hmem]

/-- For a nonempty `xs` and any `x ∈ xs`, `f x ≤ f (argmaxBy f xs)`.
That is, `argmaxBy` achieves the maximum value of `f` over the list. -/
lemma argmaxBy_max {α : Type} [Inhabited α] [LinearOrder α]
    (f : α → Nat) (xs : List α) (h : xs ≠ []) : ∀ x ∈ xs, f x ≤ f (argmaxBy f xs) := by
  match xs with
  | [] => contradiction
  | [a] => simp [argmaxBy]
  | a :: b :: bs =>
    intro x hx
    have ih := argmaxBy_max f (b :: bs) (by simp)
    have hv : x = a ∨ f x ≤ f (argmaxBy f (b :: bs)) :=
      (List.mem_cons.mp hx).imp_right (fun hm => ih x hm)
    rw [argmaxBy]
    split_ifs <;> rcases hv with rfl | hv <;> omega

/-- Tie-breaking property: if `x ∈ xs` achieves the same `f`-value as `argmaxBy f xs`,
then `argmaxBy f xs ≤ x`. In other words, among all elements maximizing `f`,
`argmaxBy` returns the smallest one. -/
lemma argmaxBy_min_of_max {α : Type} [Inhabited α] [LinearOrder α]
    (f : α → Nat) (xs : List α) (h : xs ≠ []) :
    ∀ x ∈ xs, f x = f (argmaxBy f xs) → argmaxBy f xs ≤ x := by
  match xs with
  | [] => contradiction
  | [a] => simp [argmaxBy]
  | a :: b :: bs =>
    intro x hx he
    have ih := argmaxBy_min_of_max f (b :: bs) (by simp)
    have hm := argmaxBy_max f (b :: bs) (by simp)
    rw [argmaxBy] at he ⊢
    split_ifs at he ⊢ <;> rcases List.mem_cons.mp hx with rfl | hx
    all_goals first | exact le_rfl | omega | exact le_of_not_gt (by assumption) | (have hv := hm x hx; have ht := ih x hx; first | omega | (apply le_trans (le_of_lt (by assumption)); apply ht; omega) | (apply ht; omega) | order)

/-! ### Properties of `List.argmax` with `getD` -/

/-- When `argmax` is not `none`, `getD` retrieves an element that is in the list and achieves
the maximum value of `f` over the list. -/
lemma argmax_getD_mem_and_max {α β : Type} [LinearOrder β] [DecidableEq α] {l : List α} {f : α → β}
    {d : α} (hne : l.argmax f ≠ none) :
    (l.argmax f).getD d ∈ l ∧ ∀ a ∈ l, f a ≤ f ((l.argmax f).getD d) := by
  have h_some : ∃ x, l.argmax f = some x := Option.ne_none_iff_exists'.mp hne
  rcases h_some with ⟨x, hx⟩
  have h_getD : (l.argmax f).getD d = x := by rw [hx, Option.getD_some]
  have h_mem_argmax : x ∈ l.argmax f := by rw [hx]; simp
  have h_mem_iff := List.mem_argmax_iff.mp h_mem_argmax
  rw [h_getD]
  exact ⟨h_mem_iff.1, h_mem_iff.2.1⟩

/-- If the list is nonempty, `List.argmax f l` returns `some m` for some `m`.
This is the contrapositive of `List.argmax_eq_none`. -/
lemma argmax_some_of_nonempty {α : Type} [DecidableEq α] (f : α → Nat) (l : List α) (h : l ≠ []) :
    ∃ m, List.argmax f l = some m := by
  cases hx : List.argmax f l with
  | none =>
    have h_empty : l = [] := (List.argmax_eq_none.mp hx)
    exact absurd h_empty h
  | some m =>
    exact ⟨m, rfl⟩

end List

namespace List

/-! # Argmin over a list

This module provides `argminAux`, a simple tail-recursive scan to find the first
element minimizing a function `f : α → β` where `β` is any `LinearOrder`.
Ties are broken by keeping the earlier element.

Unlike `minimumBy` (which uses a default value for the empty case and processes
from the right), `argminAux` is a forward (left-to-right) fold that takes an
explicit `best` initial value, making it natural for competitive-programming-style
scans.

For non-empty lists, use the convenience wrapper `firstMin`.
-/

variable {α β : Type} [LinearOrder β]

/-- Tail-recursive argmin: find the first element in `best :: rest` minimizing `f`.
Uses strict `<` comparison; ties keep the earlier element.

This is a forward (left-to-right) scan: `argminAux f best [p₁, p₂, …]` folds over
the list, replacing `best` only when `f p < f best`. -/
def argminAux (f : α → β) (best : α) : List α → α
  | [] => best
  | p :: ps =>
    if f p < f best then
      argminAux f p ps
    else
      argminAux f best ps

/-- Find the first element minimizing `f` in a non-empty list.
Convenience wrapper around `argminAux`. -/
def firstMin (f : α → β) (xs : List α) (h_ne : xs ≠ []) : α :=
  match xs with
  | [] => False.elim (h_ne rfl)
  | p :: ps => argminAux f p ps

/-! ### Lemmas for argmin proof composition

These lemmas describe how properties of the form "all (earlier) elements have
f-value >/≥ f r" lift when prepending an element to a list. They are building
blocks for correctness proofs of left-to-right argmin scans. -/

/-- Lifting the "all earlier elements have strictly greater f-value" property
when prepending an element to a list. -/
lemma all_strict_lift_cons (f : α → β) (x' : α)
    (L : List α) (r : α) (i : Nat)
    (h_strict : ∀ j < i, ∃ p, L[j]? = some p ∧ f p > f r)
    (h_x' : f x' > f r) :
    ∀ j < i + 1, ∃ p, (x' :: L)[j]? = some p ∧ f p > f r := by
  intro j hj
  match j with
  | 0 => exact ⟨x', by simp, h_x'⟩
  | j'+1 =>
    have hj' : j' < i := by omega
    rcases h_strict j' hj' with ⟨p, hp, hp_f⟩
    exact ⟨p, by simpa using hp, hp_f⟩

/-- Lifting the "all elements have f-value ≥ f r" property
when prepending an element to a list. -/
lemma all_le_lift_cons (f : α → β) (x' : α)
    (L : List α) (r : α)
    (h_le : ∀ k < L.length, ∃ p, L[k]? = some p ∧ f r ≤ f p)
    (h_x' : f r ≤ f x') :
    ∀ k < (x' :: L).length, ∃ p, (x' :: L)[k]? = some p ∧ f r ≤ f p := by
  intro k hk
  match k with
  | 0 => exact ⟨x', by simp, h_x'⟩
  | k'+1 =>
    have hk' : k' < L.length := by
      simp at hk ⊢; omega
    rcases h_le k' hk' with ⟨p, hp, hp_f⟩
    exact ⟨p, by simpa using hp, hp_f⟩

/-! ### `argminAuxCost` — argmin with separate cost tracking

Unlike `argminAux` which only returns the minimizing element, `argminAuxCost`
returns both the element and its cost `(element, f element)`. The `bestDist`
parameter is tracked separately to avoid recomputing `f best` on each iteration.

This variant is useful when the caller needs the minimum value itself,
not just the element that achieves it.
-/

/-- Tail-recursive argmin that also returns the cost: scans `best :: xs`,
returning `(argmin, f argmin)`. The `bestDist` parameter must equal `f best`.

Ties are broken by keeping the earlier element (strict `<` comparison). -/
def argminAuxCost (f : α → Nat) (best : α) (bestDist : Nat) : List α → α × Nat
  | [] => (best, bestDist)
  | x :: xs =>
    if f x < bestDist then
      argminAuxCost f x (f x) xs
    else
      argminAuxCost f best bestDist xs

/-- Specification for `argminAuxCost`: if `bestDist = f best` and the result
is `(cw, d)`, then:
- `cw ∈ best :: xs`
- `d = f cw`
- `d` is minimal: `∀ x ∈ best :: xs, f x ≥ d` -/
lemma argminAuxCost_spec (f : α → Nat) (best : α) (bestDist : Nat)
    (xs : List α) (h_bestDist : bestDist = f best)
    (cw : α) (d : Nat)
    (h_res : argminAuxCost f best bestDist xs = (cw, d)) :
    cw ∈ best :: xs ∧ d = f cw ∧
    ∀ x ∈ best :: xs, f x ≥ d := by
  induction xs generalizing best bestDist cw d with
  | nil =>
    injection h_res with hcw hd
    subst hcw; subst hd
    simp [h_bestDist]
  | cons x xs ih =>
    dsimp [argminAuxCost] at h_res
    by_cases h_lt : f x < bestDist
    · rw [if_pos h_lt] at h_res
      have h := ih x (f x) rfl cw d h_res
      rcases h with ⟨h_mem, h_cost_eq, h_min⟩
      have h_mem_or : cw = x ∨ cw ∈ xs := by
        simpa using h_mem
      constructor
      · rcases h_mem_or with (h_eq_x | h_mem_xs)
        · simp [h_eq_x]
        · simp [h_mem_xs]
      constructor
      · exact h_cost_eq
      · intro x' h_mem'
        have h_mem'_or : x' = best ∨ x' = x ∨ x' ∈ xs := by
          simpa using h_mem'
        rcases h_mem'_or with (h_x'_best | h_x'_x | h_x'_xs)
        · rw [h_x'_best]
          rw [← h_bestDist]
          apply Nat.le_of_lt
          apply lt_of_le_of_lt (h_min x (by simp)) h_lt
        · rw [h_x'_x]
          exact h_min x (by simp)
        · exact h_min x' (by simp [h_x'_xs])
    · rw [if_neg h_lt] at h_res
      have h_bestDist_le_cost : bestDist ≤ f x :=
        Nat.le_of_not_gt h_lt
      have h := ih best bestDist h_bestDist cw d h_res
      rcases h with ⟨h_mem, h_cost_eq, h_min⟩
      have h_mem_or : cw = best ∨ cw ∈ xs := by
        simpa using h_mem
      constructor
      · rcases h_mem_or with (h_eq_best | h_mem_xs)
        · simp [h_eq_best]
        · simp [h_mem_xs]
      constructor
      · exact h_cost_eq
      · intro x' h_mem'
        have h_mem'_or : x' = best ∨ x' = x ∨ x' ∈ xs := by
          simpa using h_mem'
        rcases h_mem'_or with (h_x'_best | h_x'_x | h_x'_xs)
        · rw [h_x'_best]
          exact h_min best (by simp)
        · rw [h_x'_x]
          have h_cost_ge_d : f best ≥ d := h_min best (by simp)
          rw [← h_bestDist] at h_cost_ge_d
          exact Nat.le_trans h_cost_ge_d h_bestDist_le_cost
        · exact h_min x' (by simp [h_x'_xs])

/-! ### `argminBy` — Nat-specialized argmin with explicit best parameter

`argminBy f xs best` scans `xs` from left to right, starting from `best`,
and returns the element minimizing `f : α → Nat`. This is a convenience
wrapper around `argminAux` with the parameter order `(f, xs, best)` instead
of the curried `(f, best, xs)`.

Unlike `argminAux` which works over any `LinearOrder`, `argminBy` is specialized
to `Nat` to support lemmas that use `Nat.le_of_lt` and similar arithmetic reasoning. -/

/-- Find the element in `best :: xs` minimizing `f : α → Nat`, keeping the
earlier element on ties (strict `<` comparison).

`argminBy f xs best` = `argminAux f best xs` — this is just a syntactic variant
with the list as the second argument. -/
def argminBy {α : Type} (f : α → Nat) (xs : List α) (best : α) : α :=
  argminAux f best xs

/-- `argminBy` preserves any predicate `P` that holds for `best` and all `x ∈ xs`. -/
lemma argminBy_preserves {α : Type} {f : α → Nat} {P : α → Prop}
    (xs : List α) (best : α) (h_best : P best) (h_xs : ∀ x ∈ xs, P x) :
    P (argminBy f xs best) := by
  induction xs generalizing best with
  | nil => simp [argminBy, argminAux, h_best]
  | cons x xs' ih =>
    have h_xs' : ∀ y ∈ xs', P y := by
      intro y hy; exact h_xs y (List.mem_cons_of_mem x hy)
    have hx : P x := h_xs x (List.mem_cons_self x xs')
    simp [argminBy, argminAux]
    split_ifs
    · exact ih x hx h_xs'
    · exact ih best h_best h_xs'

/-- The element returned by `argminBy` minimizes `f` over `best :: xs`:
`f (argminBy f xs best) ≤ f x` for all `x ∈ xs`, and also `≤ f best`. -/
lemma argminBy_le_all {α : Type} (f : α → Nat) (xs : List α) (best : α) :
    (∀ x ∈ xs, f (argminBy f xs best) ≤ f x) ∧
    f (argminBy f xs best) ≤ f best := by
  induction xs generalizing best with
  | nil =>
    constructor
    · intro x hx; simp at hx
    · simp [argminBy, argminAux]
  | cons x xs' ih =>
    have h_ih_x := ih x
    have h_ih_best := ih best
    rcases h_ih_x with ⟨h_all_x, h_le_x⟩
    rcases h_ih_best with ⟨h_all_best, h_le_best⟩
    simp [argminBy, argminAux]
    split_ifs with h
    · constructor
      · constructor
        · exact h_le_x
        · intro y hy; simpa using h_all_x y hy
      · exact le_trans h_le_x (Nat.le_of_lt h)
    · constructor
      · constructor
        · exact le_trans h_le_best (Nat.le_of_not_lt h)
        · intro y hy; simpa using h_all_best y hy
      · exact h_le_best

/-! ### `argminIdxScan` — index of the element minimizing a projection `f : α → β`

Unlike `argminAux` (which returns the element itself), `argminIdxScan` returns the
**index** of the element minimizing `f` in the list. The comparison uses the
`LinearOrder` of the codomain `β`.

This is a tail-recursive linear scan: given the current index `i`, the best index
found so far `bestIdx`, and its value `bestVal`, it scans the suffix `xs` and
returns the index of the first element achieving the minimum.

Contrast with `argminIdxAux` in `general.List` which minimizes the elements directly
(via `LinearOrder α`) without a projection function. `argminIdxScan` is more
general: it minimizes `f a` rather than `a` itself. -/

/-- Tail-recursive scan: find the index of the element in `xs` minimizing `f`,
given the current index `i`, best index `bestIdx`, and best value `bestVal`.
Returns the index of the first element achieving the minimum (strict `<` comparison,
keeping earlier element on ties). -/
def argminIdxScan (f : α → β) (xs : List α) (i bestIdx : Nat) (bestVal : β) : Nat :=
  match xs with
  | [] => bestIdx
  | x :: xs' =>
      let v := f x
      if v < bestVal then
        argminIdxScan f xs' i.succ i v
      else
        argminIdxScan f xs' i.succ bestIdx bestVal

end List

namespace List

/-! # Argmax over a list

This module provides functions and theorems for finding elements in a list
that maximize a scoring/weight function.

- **`maxByWeight`**: Find the element with maximum weight; no tie-breaking or
  order required on the element type.
- **`maxInList`**: Wrapper around `maxByWeight` with a default value for the
  empty list.
- **`findArgMax`**: Like `maxByWeight` but with deterministic tie-breaking
  using a `LinearOrder` on the element type.
-/

/-! ### `maxByWeight` — max by a weight function (no `LinearOrder` required) -/

variable {α : Type}

/--
Find the element in `best :: xs` that maximizes a weight function `weight : α → Nat`.
If multiple elements have the same maximum weight, the first encountered is kept.

Folds over `xs` using `best` as the initial candidate: `maxByWeight weight xs best`.
Polymorphic in the element type, so it can be reused for any max-by-key problem.
-/
def maxByWeight (weight : α → Nat) (xs : List α) (best : α) : α :=
  match xs with
  | [] => best
  | y :: ys =>
    if weight y > weight best then
      maxByWeight weight ys y
    else
      maxByWeight weight ys best

/--
`maxInList` finds the element with maximum weight in `l`, using `default`
when the list is empty. Builds on `maxByWeight`.
-/
def maxInList (weight : α → Nat) (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | h :: t => maxByWeight weight t h

/-! ### Properties of `maxByWeight` -/

/-- The result of `maxByWeight` is always in `best :: xs`. -/
lemma maxByWeight_mem (weight : α → Nat) (xs : List α) (best : α) :
    maxByWeight weight xs best ∈ best :: xs := by
  induction xs generalizing best with
  | nil => simp [maxByWeight]
  | cons y ys ih =>
    simp [maxByWeight]
    split_ifs with h
    · have hmem_or := by simpa using ih y
      rcases hmem_or with (heq | hmem_ys)
      · right; left; exact heq
      · right; right; exact hmem_ys
    · have hmem_or := by simpa using ih best
      rcases hmem_or with (heq | hmem_ys)
      · left; exact heq
      · right; right; exact hmem_ys

/-- Auxiliary lemma: any element in `best :: xs` has weight ≤ `maxByWeight` result. -/
lemma maxByWeight_max_aux (weight : α → Nat) (xs : List α) :
    (∀ (best hm' : α), (hm' = best ∨ hm' ∈ xs) → weight hm' ≤ weight (maxByWeight weight xs best)) := by
  induction xs with
  | nil =>
    intro best hm' hmem_or
    rcases hmem_or with (heq | hnil)
    · rw [heq]; simp [maxByWeight]
    · exact absurd hnil (List.not_mem_nil _)
  | cons y ys ih =>
    intro best hm' hmem_or
    rcases hmem_or with (heq | hmem_ys_or)
    · -- hm' = best
      rw [heq]
      by_cases h : weight y > weight best
      · simp [maxByWeight, h]
        have hy_le_go := ih y y (Or.inl rfl)
        omega
      · simp [maxByWeight, h]
        exact ih best best (Or.inl rfl)
    · -- hm' ∈ y :: ys
      have hmem_cases2 : hm' = y ∨ hm' ∈ ys := by simpa using hmem_ys_or
      rcases hmem_cases2 with (heq2 | hm_mem_ys)
      · -- hm' = y
        rw [heq2]
        by_cases h : weight y > weight best
        · simp [maxByWeight, h]
          exact ih y y (Or.inl rfl)
        · simp [maxByWeight, h]
          have hbest_ge_y : weight y ≤ weight best := by omega
          have best_le_go := ih best best (Or.inl rfl)
          omega
      · -- hm' ∈ ys
        by_cases h : weight y > weight best
        · simp [maxByWeight, h]
          exact ih y hm' (Or.inr hm_mem_ys)
        · simp [maxByWeight, h]
          exact ih best hm' (Or.inr hm_mem_ys)

/--
If `hm'` is in `best :: xs`, then its weight is ≤ the weight of
`maxByWeight weight xs best`.
-/
lemma maxByWeight_max (weight : α → Nat) (xs : List α) (best hm' : α)
    (hmem : hm' ∈ best :: xs) : weight hm' ≤ weight (maxByWeight weight xs best) := by
  have hm_or : hm' = best ∨ hm' ∈ xs := by simpa using hmem
  exact maxByWeight_max_aux weight xs best hm' hm_or

/-! ### `maxByCachedScore` — max by weight with precomputed initial score

This is a variant of `maxByWeight` where the score of the initial `best` candidate
is provided explicitly as `bestScore`. This avoids recomputing `weight best` in
each iteration, which can be more efficient when `weight` is expensive to compute
or when you already know the score from a previous computation.

For example, when counting character frequencies, you compute `score best` once and
pass it as `bestScore`, saving `O(length (candidates))` calls to `score` that
`maxByWeight` would incur.
-/

/-- Find the element in `best :: candidates` maximizing a weight function `weight : α → Nat`,
given the precomputed score `bestScore` of `best` (where `weight best = bestScore`).

Folds over `candidates` comparing the cached `bestScore` against `weight c`,
recomputing the cached score only when a new best is found.

The equivalence lemma `maxByCachedScore_eq_maxByWeight` relates this to `maxByWeight`. -/
def maxByCachedScore (weight : α → Nat) (candidates : List α) (best : α) (bestScore : Nat) : α :=
  match candidates with
  | [] => best
  | c :: rest =>
    let cnt := weight c
    if bestScore < cnt then
      maxByCachedScore weight rest c cnt
    else
      maxByCachedScore weight rest best bestScore

/-- `maxByCachedScore` reduces to `maxByWeight` when given the correct cached score. -/
lemma maxByCachedScore_eq_maxByWeight (weight : α → Nat) (xs : List α) (best : α) :
    maxByCachedScore weight xs best (weight best) = maxByWeight weight xs best := by
  induction xs generalizing best with
  | nil => simp [maxByCachedScore, maxByWeight]
  | cons c cs ih =>
    simp [maxByCachedScore, maxByWeight, ih]

/-- Correctness of `maxByCachedScore`:
the result's score is at least the initial `best`'s score,
and every element in `candidates` has score ≤ the result's score. -/
lemma maxByCachedScore_max (weight : α → Nat)
    (candidates : List α) (best : α) (bestScore : Nat)
    (hbest_score : weight best = bestScore) :
    (weight best ≤ weight (maxByCachedScore weight candidates best bestScore)) ∧
    (∀ c, c ∈ candidates → weight c ≤ weight (maxByCachedScore weight candidates best bestScore)) := by
  induction candidates generalizing best bestScore with
  | nil =>
    simp [maxByCachedScore]
  | cons c cs ih =>
    simp [maxByCachedScore]
    split
    · rename_i h_lt
      have ih_result := ih c (weight c) rfl
      rcases ih_result with ⟨h_c_le_res, h_cs_le_res⟩
      have h_best_le_c : weight best ≤ weight c := by
        rw [hbest_score]; exact Nat.le_of_lt h_lt
      have h_best_le_res : weight best ≤ weight (maxByCachedScore weight cs c (weight c)) :=
        Nat.le_trans h_best_le_c h_c_le_res
      exact ⟨h_best_le_res, h_c_le_res, h_cs_le_res⟩
    · rename_i h_not_lt
      have h_c_le_best : weight c ≤ bestScore := Nat.le_of_not_gt h_not_lt
      have ih_result := ih best bestScore hbest_score
      rcases ih_result with ⟨h_best_le_res, h_cs_le_res⟩
      have h_c_le_best' : weight c ≤ weight best := by
        rw [hbest_score]; exact h_c_le_best
      have h_c_le_res : weight c ≤ weight (maxByCachedScore weight cs best bestScore) :=
        Nat.le_trans h_c_le_best' h_best_le_res
      exact ⟨h_best_le_res, h_c_le_res, h_cs_le_res⟩

/-- The result of `maxByCachedScore` is either `best` or an element of `candidates`. -/
lemma maxByCachedScore_mem (weight : α → Nat) (candidates : List α) (best : α) (bestScore : Nat) :
    maxByCachedScore weight candidates best bestScore = best ∨
    maxByCachedScore weight candidates best bestScore ∈ candidates := by
  induction candidates generalizing best bestScore with
  | nil => simp [maxByCachedScore]
  | cons c cs ih =>
    -- Use `dsimp` to expand the `let` without simplifying membership
    dsimp [maxByCachedScore]
    split
    · rcases ih c (weight c) with (h_eq | h_mem)
      · right; rw [h_eq]; exact .head _
      · right; exact .tail _ h_mem
    · rcases ih best bestScore with (h_eq | h_mem)
      · left; exact h_eq
      · right; exact .tail _ h_mem

/-- Either the result of `maxByCachedScore` has strictly greater weight than the initial
`bestScore`, or the result is exactly `best`. This is a disjunctive version of
`maxByCachedScore_max`: the algorithm either improves upon the initial candidate or
keeps it unchanged. -/
lemma maxByCachedScore_val_gt_or_eq (weight : α → Nat) (candidates : List α) (best : α) (bestScore : Nat)
    (h_score : bestScore = weight best) :
    weight (maxByCachedScore weight candidates best bestScore) > bestScore ∨
    maxByCachedScore weight candidates best bestScore = best := by
  induction candidates generalizing best bestScore with
  | nil => simp [maxByCachedScore, h_score]
  | cons c cs ih =>
    dsimp [maxByCachedScore]
    split
    · rename_i h
      have h_gt : weight c > bestScore := h
      have ih' := ih c (weight c) rfl
      rcases ih' with (h_val_gt | h_eq)
      · left; omega
      · left; rw [h_eq]; omega
    · exact ih best bestScore h_score

/-! ### Properties of `maxInList` -/

/-- If `l` is nonempty, `maxInList weight l default` is in `l`. -/
lemma maxInList_mem_of_ne_nil (weight : α → Nat) (l : List α) (default : α) (hne : l ≠ []) :
    maxInList weight l default ∈ l := by
  cases l with
  | nil => contradiction
  | cons h t =>
    unfold maxInList
    exact maxByWeight_mem weight t h

/-- `maxInList` returns an element with maximal weight: for any `hm' ∈ l`,
`weight hm' ≤ weight (maxInList weight l default)`. -/
lemma maxInList_max (weight : α → Nat) (l : List α) (default : α) (hm' : α) (hmem : hm' ∈ l) :
    weight hm' ≤ weight (maxInList weight l default) := by
  cases l with
  | nil => exact absurd hmem (List.not_mem_nil _)
  | cons h t =>
    unfold maxInList
    exact maxByWeight_max weight t h hm' hmem

/-- If `weight default = 0`, then the weight of the element returned by `maxInList`
equals `maxVal` of the list. This connects the argmax element to the max value. -/
lemma maxInList_weight_eq_maxVal (weight : α → Nat) (l : List α) (default : α)
    (h_default : weight default = 0) : weight (maxInList weight l default) = maxVal weight l := by
  by_cases hne : l = []
  · subst hne
    simp [maxInList, maxVal, h_default]
  · have hmem : maxInList weight l default ∈ l :=
      maxInList_mem_of_ne_nil weight l default hne
    have h_ge : weight (maxInList weight l default) ≤ maxVal weight l :=
      maxVal_ge weight l _ hmem
    have h_le : maxVal weight l ≤ weight (maxInList weight l default) := by
      rcases maxVal_exists weight l hne with ⟨x, hx, hx_eq⟩
      have hx_le : weight x ≤ weight (maxInList weight l default) :=
        maxInList_max weight l default x hx
      rw [hx_eq] at hx_le
      exact hx_le
    exact le_antisymm h_ge h_le

/-! ### `findArgMax` — max with tie-breaking (requires `LinearOrder`) -/

variable [LinearOrder α]

/-- Find the element from `best :: candidates` that maximizes `f`,
with ties broken by picking the smallest element (according to the linear order). -/
def findArgMax (f : α → Nat) (best : α) (candidates : List α) : α :=
  match candidates with
  | [] => best
  | c :: cs =>
    let sb := f best
    let sc := f c
    if sc > sb ∨ (sc = sb ∧ c < best) then
      findArgMax f c cs
    else
      findArgMax f best cs

/-- Equation lemma for `findArgMax` on a non-empty list. -/
lemma findArgMax_cons (f : α → Nat) (best c : α) (cs : List α) :
    findArgMax f best (c :: cs) =
    if f c > f best ∨ (f c = f best ∧ c < best) then
      findArgMax f c cs
    else
      findArgMax f best cs := by
  simp [findArgMax]

/-- The result of `findArgMax` is in `best :: candidates`. -/
lemma findArgMax_mem (f : α → Nat) (best : α) (candidates : List α) :
    findArgMax f best candidates ∈ (best :: candidates) := by
  induction candidates generalizing best with
  | nil => simp [findArgMax]
  | cons c cs ih =>
    rw [findArgMax_cons]
    split_ifs with h
    · have ih' := ih c
      exact List.mem_cons_of_mem best ih'
    · have ih' := ih best
      have ih_cases : findArgMax f best cs = best ∨ findArgMax f best cs ∈ cs := by
        simpa using ih'
      rcases ih_cases with (h_eq | h_mem)
      · rw [h_eq]; exact by simp
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem c h_mem)

set_option maxHeartbeats 400000 in
/-- `findArgMax` returns an element with maximum `f` value. -/
lemma findArgMax_maxScore (f : α → Nat) (best : α) (candidates : List α) (d : α)
    (hd : d ∈ (best :: candidates)) :
    f d ≤ f (findArgMax f best candidates) := by
  induction candidates generalizing best d with
  | nil =>
    have hd' : d = best := by simpa using hd
    rw [hd']
    simp [findArgMax]
  | cons c cs ih =>
    rw [findArgMax_cons]
    split_ifs with h_cond
    · -- recurse with c; result = findArgMax f c cs
      have hd_cases : d = best ∨ d ∈ (c :: cs) := by simpa using hd
      rcases hd_cases with (h_eq_d | hd_rest)
      · rw [h_eq_d]
        rcases h_cond with (h_gt | ⟨h_eq_sc, h_lt⟩)
        · have hc := ih c c (by simp)
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le h_gt hc)
        · have hc := ih c c (by simp)
          rw [← h_eq_sc]
          exact hc
      · exact ih c d hd_rest
    · -- keep best; result = findArgMax f best cs
      have h_not_gt : ¬ (f c > f best) := by
        intro hgt; apply h_cond; exact Or.inl hgt
      have h_f_c_le_best : f c ≤ f best := Nat.le_of_not_gt h_not_gt
      have hd_cases : d = best ∨ d ∈ (c :: cs) := by simpa using hd
      rcases hd_cases with (h_eq_d | hd_rest)
      · rw [h_eq_d]
        exact ih best best (by simp)
      · have hd_cases2 : d = c ∨ d ∈ cs := by simpa using hd_rest
        rcases hd_cases2 with (h_eq_d2 | hd_cs)
        · rw [h_eq_d2]
          have hbest_le := ih best best (by simp)
          exact Nat.le_trans h_f_c_le_best hbest_le
        · have hd_in_best_cs : d ∈ (best :: cs) := List.mem_cons_of_mem best hd_cs
          exact ih best d hd_in_best_cs

/-- When `c` is better than `best` and the recursive call on `(c :: cs)` satisfies
    the optimality spec, then the result is also optimal for `(best :: c :: cs)`.
    This is an induction step lemma that extends the invariant from the tail
    `(c :: cs)` to the full list `(best :: c :: cs)` when `c` beats `best`. -/
lemma findArgMax_better_step (f : α → Nat) (best c : α) (cs : List α)
    (h_better : f c > f best ∨ (f c = f best ∧ c < best))
    (h_mem : findArgMax f c cs ∈ (c :: cs))
    (h_max : ∀ x ∈ (c :: cs), f (findArgMax f c cs) ≥ f x)
    (h_tie : ∀ x ∈ (c :: cs), f (findArgMax f c cs) = f x → findArgMax f c cs ≤ x) :
    (findArgMax f c cs ∈ (best :: c :: cs)) ∧
    (∀ x ∈ (best :: c :: cs), f (findArgMax f c cs) ≥ f x) ∧
    (∀ x ∈ (best :: c :: cs), f (findArgMax f c cs) = f x → findArgMax f c cs ≤ x) := by
  set r := findArgMax f c cs
  have h_mem_all : r ∈ (best :: c :: cs) :=
    List.mem_cons_of_mem best h_mem
  refine ⟨h_mem_all, ?_, ?_⟩
  · intro x hx
    rcases (List.mem_cons.mp hx) with (hx_eq | hx_mem)
    · rw [hx_eq]
      rcases h_better with (h_gt | ⟨h_eq, h_lt⟩)
      · have hge : f r ≥ f c := h_max c (by simp)
        exact Nat.le_trans (Nat.le_of_lt h_gt) hge
      · have hge : f r ≥ f c := h_max c (by simp)
        rw [← h_eq]
        exact hge
    · exact h_max x hx_mem
  · intro x hx hf_eq
    rcases (List.mem_cons.mp hx) with (hx_eq | hx_mem)
    · rw [hx_eq] at hf_eq
      rw [hx_eq]
      rcases h_better with (h_gt | ⟨h_eq_dc, h_lt⟩)
      · have hge : f r ≥ f c := h_max c (by simp)
        have : f r > f best := Nat.lt_of_lt_of_le h_gt hge
        omega
      · have hf_eq_rc : f r = f c := hf_eq.trans h_eq_dc.symm
        have hr_le_c : r ≤ c := h_tie c (by simp) hf_eq_rc
        exact le_trans hr_le_c (le_of_lt h_lt)
    · exact h_tie x hx_mem hf_eq

/-! ### `findArgMin` — min with tie-breaking (requires `LinearOrder`)

This is the dual of `findArgMax`: it minimizes `f` instead of maximizing it.
Ties are broken by picking the smallest element according to the `LinearOrder`.

This generalizes the common "find closest" pattern where elements are compared
by a distance/score function and ties are broken by the element's own ordering.
-/


/-- Find the element from `best :: candidates` that minimizes `f`,
with ties broken by picking the smallest element.
This is the dual of `findArgMax`. -/
def findArgMin (f : α → Nat) (best : α) (candidates : List α) : α :=
  match candidates with
  | [] => best
  | c :: cs =>
    if f c < f best ∨ (f c = f best ∧ c < best) then
      findArgMin f c cs
    else
      findArgMin f best cs

/-- Equation lemma for `findArgMin` on a non-empty list. -/
lemma findArgMin_cons (f : α → Nat) (best c : α) (cs : List α) :
    findArgMin f best (c :: cs) =
    if f c < f best ∨ (f c = f best ∧ c < best) then
      findArgMin f c cs
    else
      findArgMin f best cs := by
  simp [findArgMin]

/-- The result of `findArgMin` is in `best :: candidates`. -/
lemma findArgMin_mem (f : α → Nat) (best : α) (candidates : List α) :
    findArgMin f best candidates ∈ (best :: candidates) := by
  induction candidates generalizing best with
  | nil => simp [findArgMin]
  | cons c cs ih =>
    rw [findArgMin_cons]
    split_ifs with h
    · have ih' := ih c
      exact List.mem_cons_of_mem best ih'
    · have ih' := ih best
      have ih_cases : findArgMin f best cs = best ∨ findArgMin f best cs ∈ cs := by
        simpa using ih'
      rcases ih_cases with (h_eq | h_mem)
      · rw [h_eq]; exact by simp
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem c h_mem)

/-- `findArgMin` returns an element with minimal `f` value (dual of `findArgMax_maxScore`). -/
lemma findArgMin_minScore (f : α → Nat) (best : α) (candidates : List α) (d : α)
    (hd : d ∈ (best :: candidates)) :
    f (findArgMin f best candidates) ≤ f d := by
  induction candidates generalizing best d with
  | nil =>
    have hd' : d = best := by simpa using hd
    rw [hd']
    simp [findArgMin]
  | cons c cs ih =>
    rw [findArgMin_cons]
    split_ifs with h_cond
    · -- recurse with c; result = findArgMin f c cs
      have hd_cases : d = best ∨ d ∈ (c :: cs) := by simpa using hd
      rcases hd_cases with (h_eq_d | hd_rest)
      · rw [h_eq_d]
        rcases h_cond with (h_lt | ⟨h_eq_sc, _⟩)
        · have hc := ih c c (by simp)
          exact Nat.le_trans hc (Nat.le_of_lt h_lt)
        · have hc := ih c c (by simp)
          rw [← h_eq_sc]
          exact hc
      · exact ih c d hd_rest
    · -- keep best; result = findArgMin f best cs
      have hd_cases : d = best ∨ d ∈ (c :: cs) := by simpa using hd
      rcases hd_cases with (h_eq_d | hd_rest)
      · rw [h_eq_d]
        exact ih best best (by simp)
      · have hd_cases2 : d = c ∨ d ∈ cs := by simpa using hd_rest
        rcases hd_cases2 with (h_eq_d2 | hd_cs)
        · rw [h_eq_d2]
          have h_not_lt : ¬ (f c < f best) := by
            intro hlt; apply h_cond; exact Or.inl hlt
          have h_f_best_le_c : f best ≤ f c := Nat.le_of_not_gt h_not_lt
          have hbest_min := ih best best (by simp)
          exact Nat.le_trans hbest_min h_f_best_le_c
        · have hd_in_best_cs : d ∈ (best :: cs) := List.mem_cons_of_mem best hd_cs
          exact ih best d hd_in_best_cs

/-! ### Optimality of `findArgMin` (score minimality + tiebreaker)

The following lemmas are used in the proof of `findArgMin_optimal`, which
proves both the score minimality and the tiebreaker property simultaneously.
-/

/-- If `r` is optimal among `(x :: candidates)`, `f x < f best`, then `r` also
beats `best` in both score and tiebreaker. -/
lemma findArgMin_beats_strictlyBetter (f : α → Nat) (best x r : α) (candidates : List α)
    (h_closer : f x < f best)
    (h_opt : ∀ y ∈ (x :: candidates),
      f r ≤ f y ∧ (f r = f y → r ≤ y)) :
    f r ≤ f best ∧ (f r = f best → r ≤ best) := by
  have hx := h_opt x (by simp)
  rcases hx with ⟨h_rx_dist, _⟩
  have h_dist : f r ≤ f best :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt h_rx_dist h_closer)
  refine ⟨h_dist, ?_⟩
  intro heq
  have h_contra : f x < f x :=
    Nat.lt_of_lt_of_le h_closer (by
      rw [← heq]
      exact h_rx_dist)
  exact (Nat.lt_irrefl _ h_contra).elim

/-- If `r` is optimal among `(x :: candidates)`, `f x = f best`, and `x < best`,
then `r` also beats `best` in both score and tiebreaker.
This generalizes `optimal_beats_farther_of_eq_dist`. -/
lemma findArgMin_beats_eqScore_of_lt (f : α → Nat) (best x r : α) (candidates : List α)
    (h_eq : f x = f best) (h_lt_val : x < best)
    (h_opt : ∀ y ∈ (x :: candidates),
      f r ≤ f y ∧ (f r = f y → r ≤ y)) :
    f r ≤ f best ∧ (f r = f best → r ≤ best) := by
  have hx := h_opt x (by simp)
  rcases hx with ⟨h_rx_dist, h_rx_tie⟩
  have h_dist : f r ≤ f best := by
    rw [← h_eq]
    exact h_rx_dist
  refine ⟨h_dist, ?_⟩
  intro heq
  have hrx_eq : f r = f x := by
    calc
      f r = f best := heq
      _ = f x := h_eq.symm
  have h_r_le_x : r ≤ x := h_rx_tie hrx_eq
  exact le_trans h_r_le_x (le_of_lt h_lt_val)

/-- If `r` is optimal among `(best :: candidates)` and `best` is not worse than `x`
(i.e. `¬ (f x < f best ∨ (f x = f best ∧ x < best))`), then `r` also beats `x`
in both score and tiebreaker. -/
lemma findArgMin_beats_notBetter (f : α → Nat) (best x r : α) (candidates : List α)
    (h_not_better : ¬ (f x < f best ∨ (f x = f best ∧ x < best)))
    (h_opt : ∀ y ∈ (best :: candidates),
      f r ≤ f y ∧ (f r = f y → r ≤ y)) :
    f r ≤ f x ∧ (f r = f x → r ≤ x) := by
  have h_not_lt : ¬ (f x < f best) := by
    intro hlt; apply h_not_better; exact Or.inl hlt
  have h_not_both : ¬ (f x = f best ∧ x < best) := by
    intro hboth; apply h_not_better; exact Or.inr hboth
  have h_le_score : f best ≤ f x := Nat.le_of_not_gt h_not_lt
  have h_tiebreaker : f best = f x → best ≤ x := by
    intro heq
    by_contra! h_lt
    apply h_not_both
    exact ⟨heq.symm, h_lt⟩
  have h_best := h_opt best (by simp)
  rcases h_best with ⟨h_rb_dist, h_rb_tie⟩
  have h_dist : f r ≤ f x := Nat.le_trans h_rb_dist h_le_score
  refine ⟨h_dist, ?_⟩
  intro heq_dist
  have h_eq_fb_fr : f best = f r := by
    apply Nat.le_antisymm
    · calc
        f best ≤ f x := h_le_score
        _ = f r := heq_dist.symm
    · exact h_rb_dist
  have h_r_le_best : r ≤ best := h_rb_tie h_eq_fb_fr.symm
  have h_best_le_x : best ≤ x := h_tiebreaker (h_eq_fb_fr.trans heq_dist)
  exact le_trans h_r_le_best h_best_le_x

/-- `findArgMin` returns an optimal element: minimal `f` value with tie-breaking.
For any `y` in `(best :: candidates)`, the result minimizes `f` and, when `f` values
are equal, the result is ≤ `y`.

This is the main correctness theorem for `findArgMin`, generalizing
`find_closest_aux_optimal`. -/
theorem findArgMin_optimal (f : α → Nat) (best : α) (candidates : List α) :
    (∀ y, y ∈ (best :: candidates) →
      f (findArgMin f best candidates) ≤ f y ∧
      (f (findArgMin f best candidates) = f y → findArgMin f best candidates ≤ y)) := by
  induction candidates generalizing best with
  | nil =>
    intro y hy
    have hy_eq : y = best := by simpa using hy
    simp [findArgMin, hy_eq]
  | cons x xs ih =>
    intro y hy
    rw [findArgMin_cons]
    by_cases h_cond : f x < f best ∨ (f x = f best ∧ x < best)
    · rw [if_pos h_cond]
      have hy_cases : y = best ∨ y ∈ x :: xs := by simpa using hy
      rcases hy_cases with (hy_eq_best | hy_in_x_xs)
      · rw [hy_eq_best]
        rcases h_cond with (h_lt | ⟨h_eq, h_lt_val⟩)
        · exact findArgMin_beats_strictlyBetter f best x (findArgMin f x xs) xs h_lt (ih x)
        · exact findArgMin_beats_eqScore_of_lt f best x (findArgMin f x xs) xs h_eq h_lt_val (ih x)
      · have hy_cases' : y = x ∨ y ∈ xs := by simpa using hy_in_x_xs
        rcases hy_cases' with (hy_eq_x | hy_in_xs)
        · rw [hy_eq_x]; exact (ih x) x (by simp)
        · exact (ih x) y (by simp [hy_in_xs])
    · rw [if_neg h_cond]
      have hy_cases : y = best ∨ y ∈ x :: xs := by simpa using hy
      rcases hy_cases with (hy_eq_best | hy_in_x_xs)
      · rw [hy_eq_best]; exact (ih best) best (by simp)
      · have hy_cases' : y = x ∨ y ∈ xs := by simpa using hy_in_x_xs
        rcases hy_cases' with (hy_eq_x | hy_in_xs)
        · rw [hy_eq_x]
          exact findArgMin_beats_notBetter f best x (findArgMin f best xs) xs h_cond (ih best)
        · exact (ih best) y (by simp [hy_in_xs])

/-! ### `maxByDefault` — recursive max-by-measure with default

This is an alternative formulation to `maxInList` and `maxByWeight`. Unlike those,
`maxByDefault` compares against `default` at every recursion step, not just for the empty
list. This means `default` participates in comparisons throughout.
-/

/-- Find the element of `xs` maximizing `measure : α → Nat`, returning `default`
when the list is empty. Unlike `maxInList`, the `default` value participates in
comparisons at every recursive step. -/
def maxByDefault (measure : α → Nat) (default : α) : List α → α
  | [] => default
  | x :: xs =>
    let r := maxByDefault measure default xs
    if measure r ≤ measure x then x else r

/-! ### Properties of `maxByDefault` -/

/-- If `default`'s measure is ≤ every element's measure, and the list is nonempty,
then `maxByDefault` returns an element in the list. -/
lemma maxByDefault_mem {measure : α → Nat} {default : α} {xs : List α}
    (hmin : ∀ a, measure default ≤ measure a) (hne : xs ≠ []) :
    maxByDefault measure default xs ∈ xs := by
  induction' xs with x xs ih
  · exact (hne rfl).elim
  · dsimp [maxByDefault]
    by_cases hlen : measure (maxByDefault measure default xs) ≤ measure x
    · simp [hlen]
    · simp [hlen]
      have hxs_ne : xs ≠ [] := by
        intro hxs
        subst hxs
        have hle : measure (maxByDefault measure default []) ≤ measure x := by
          simp [maxByDefault, hmin x]
        exact hlen hle
      exact Or.inr (ih hxs_ne)

/-- For any `x ∈ xs`, `measure x ≤ measure (maxByDefault measure default xs)`.
No condition on `default` is needed. -/
lemma maxByDefault_is_maximal {measure : α → Nat} {default : α} {xs : List α}
    {x : α} (hx : x ∈ xs) : measure x ≤ measure (maxByDefault measure default xs) := by
  induction' xs with y ys ih generalizing x
  · exact (List.not_mem_nil _ hx).elim
  · cases hx with
    | head _ =>
        dsimp [maxByDefault]
        by_cases hlen : measure (maxByDefault measure default ys) ≤ measure y
        · simp [hlen]
        · simp [hlen]
          exact Nat.le_of_lt (Nat.not_le.mp hlen)
    | tail _ hx' =>
        dsimp [maxByDefault]
        by_cases hlen : measure (maxByDefault measure default ys) ≤ measure y
        · simp [hlen]
          have h_ih := ih hx'
          exact le_trans h_ih hlen
        · simp [hlen]
          exact ih hx'

/-- `maxByDefault` returns the earliest element achieving the maximum measure.
For any `x ∈ xs` with the same measure, the position of the `maxByDefault` result
is ≤ the position of `x`. -/
lemma maxByDefault_earliest [DecidableEq α] {measure : α → Nat} {default : α}
    {xs : List α} {x : α} (hx : x ∈ xs)
    (h_eq : measure x = measure (maxByDefault measure default xs)) :
    (xs.findIdx? (fun t => t = maxByDefault measure default xs)).getD xs.length ≤
    (xs.findIdx? (fun t => t = x)).getD xs.length := by
  induction' xs with y ys ih generalizing x
  · exact (List.not_mem_nil _ hx).elim
  · cases hx with
    | head _ =>
        dsimp [maxByDefault] at h_eq ⊢
        by_cases hlen : measure (maxByDefault measure default ys) ≤ measure y
        · simp [hlen]
        · simp [hlen] at h_eq ⊢
          have hlt : measure y < measure (maxByDefault measure default ys) := Nat.not_le.mp hlen
          rw [h_eq] at hlt
          exact (Nat.lt_irrefl _ hlt).elim
    | tail _ hx' =>
        dsimp [maxByDefault] at h_eq ⊢
        by_cases hlen : measure (maxByDefault measure default ys) ≤ measure y
        · simp [hlen]
        · simp [hlen]
          have hx_len : measure x = measure (maxByDefault measure default ys) := by
            simpa [hlen] using h_eq
          have hy_lt : measure y < measure (maxByDefault measure default ys) := Nat.not_le.mp hlen
          have hx_ne_y : x ≠ y := by
            intro h_eq_x
            rw [← h_eq_x] at hy_lt
            rw [hx_len] at hy_lt
            exact Nat.lt_irrefl _ hy_lt
          have hr_ne_y : maxByDefault measure default ys ≠ y := by
            intro h_eq_r
            rw [h_eq_r] at hy_lt
            exact Nat.lt_irrefl _ hy_lt
          have h_ih := ih hx' hx_len
          simp [List.findIdx?_cons, hx_ne_y.symm, hr_ne_y.symm, Option.getD_map_succ]
          exact h_ih

/-! ### `argmin` — argmin by weight with inhabited default

Unlike `argminOfCons` (in `general.List`) which requires a non-empty proof via the `a :: l` pattern,
`argmin` uses `[Inhabited α]` to return `default` for empty lists.
For non-empty lists it delegates to `argminOfCons`.
-/

/-- Find the element in `xs` that minimizes `f : α → Nat`.
Returns `default` for the empty list. For non-empty lists, delegates to `argminOfCons`. -/
def argminD [Inhabited α] (f : α → Nat) (xs : List α) : α :=
  match xs with
  | [] => default
  | x :: xs' => argminOfCons f xs' x

/-- Specification for `argminD` on non-empty lists: the result is in the list and minimizes `f`. -/
lemma argminD_spec [Inhabited α] (f : α → Nat) (xs : List α) (hne : xs ≠ []) :
    (argminD f xs ∈ xs) ∧ (∀ y ∈ xs, f (argminD f xs) ≤ f y) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs' =>
    unfold argminD
    exact argminOfCons_mem_and_minimal f xs' x

/-! ### `List.argmax` helper lemmas -/

/-- If a list is non-empty, `List.argmax f l` is not `none`. -/
lemma argmax_ne_none_of_ne_nil {α β : Type u} [DecidableEq β] [LinearOrder β]
    (f : α → β) (l : List α) (hne : l ≠ []) : List.argmax f l ≠ none := by
  intro h
  exact hne ((List.argmax_eq_none (f := f) (l := l)).mp h)

/-- Return the element of `l` that maximizes `f`, or `default` if `l` is empty.
A safe wrapper around `List.argmax` that eliminates the `Option`. -/
def argmaxDefault [LinearOrder β] [DecidableEq α] (f : α → β) (l : List α) (default : α) : α :=
  match List.argmax f l with
  | some a => a
  | none => default

/-- If `List.argmax f l = some m`, then `m` is a member of `l` and `f a ≤ f m` for all `a ∈ l`.
This extracts the membership and maximality components from `List.argmax_eq_some_iff`. -/
lemma argmax_some_mem_and_le {α β : Type u} [LinearOrder β] {f : α → β} {l : List α} {m : α} [DecidableEq α]
    (h : List.argmax f l = some m) : m ∈ l ∧ ∀ a ∈ l, f a ≤ f m := by
  rcases (List.argmax_eq_some_iff (f := f) (l := l) (m := m)).mp h with ⟨hmem, hle, _⟩
  exact ⟨hmem, hle⟩

/-! ### `minimumBy` — argmin by a measure into any `LinearOrder`

This is the dual of `maxByDefault`. While `maxByDefault` returns the element maximizing
a `measure : α → Nat`, `minimumBy` returns the element minimizing `f : α → β` where `β`
is any `LinearOrder`. An explicit `default` is used for the empty list.

Unlike `argminD` (which is restricted to `Nat` and uses `[Inhabited α]`), `minimumBy`
is fully general over the codomain type.
-/

/-- Find the element in `xs` with minimal `f` value, using `default` if `xs` is empty. -/
def minimumBy {α β : Type} [LinearOrder β] (f : α → β) (xs : List α) (default : α) : α :=
  match xs with
  | [] => default
  | x :: xs =>
    let rest := minimumBy f xs default
    if f x ≤ f rest then x else rest


theorem minimumBy_nil {α β : Type} [LinearOrder β] (f : α → β) (default : α) :
    minimumBy f [] default = default := rfl


theorem minimumBy_cons {α β : Type} [LinearOrder β] (f : α → β) (a : α) (as : List α) (default : α) :
    minimumBy f (a :: as) default =
    if f a ≤ f (minimumBy f as default) then a else minimumBy f as default := rfl

/-- If `x` is in `xs`, then `f (minimumBy f xs default) ≤ f x`. -/
lemma minimumBy_le {α β : Type} [LinearOrder β] (f : α → β) (xs : List α) (default : α) {x : α} (hx : x ∈ xs) :
    f (minimumBy f xs default) ≤ f x := by
  induction xs with
  | nil =>
    exfalso; exact List.not_mem_nil x hx
  | cons a as ih =>
    simp only [minimumBy_cons]
    rw [List.mem_cons] at hx
    rcases hx with (hxeq | hx')
    · rw [hxeq]
      by_cases h : f a ≤ f (minimumBy f as default)
      · simp [h]
      · simp [h]
        have hlt : f (minimumBy f as default) < f a := (not_le.mp h)
        exact le_of_lt hlt
    · have hrest : f (minimumBy f as default) ≤ f x := ih hx'
      by_cases h : f a ≤ f (minimumBy f as default)
      · simp [h]
        exact le_trans h hrest
      · simp [h]
        exact hrest

/-! ### `maxByMeasure` — first-occurrence max by measure with partition spec

`maxByMeasure measure default xs` returns the first element in `xs` achieving
the maximum `measure`. Returns `default` if `xs` is empty.

Unlike `maxByDefault` (which returns the last occurrence on ties),
`maxByMeasure` always returns the *first* occurrence, enabling a clean
partition specification: the result partitions `xs` into a prefix where all
elements have strictly smaller measure, and a suffix where all elements have
measure ≤ the returned element.

This property (`maxByMeasure_spec`) is especially useful for proofs about
problems like "longest word" or "largest value" where we care about the
positional structure of the list relative to the argmax element.
-/

variable {α : Type}

/-- Find the first element achieving the maximum measure in a list.
Returns `default` for the empty list. -/
def maxByMeasure (measure : α → Nat) (default : α) : List α → α
  | [] => default
  | [x] => x
  | x :: x' :: xs' =>
    if measure x ≥ measure (maxByMeasure measure default (x' :: xs')) then x
    else maxByMeasure measure default (x' :: xs')

/-- Specification for `maxByMeasure`: in a nonempty list, the element returned by
`maxByMeasure` partitions the list into a prefix where all elements have strictly smaller
measure and a suffix where all elements have measure ≤ the returned element. -/
lemma maxByMeasure_spec (measure : α → Nat) (default : α) (xs : List α) (hne : xs ≠ []) :
    ∃ (l₁ l₂ : List α), xs = l₁ ++ maxByMeasure measure default xs :: l₂ ∧
      (∀ w ∈ l₁, measure w < measure (maxByMeasure measure default xs)) ∧
      (∀ w ∈ l₂, measure w ≤ measure (maxByMeasure measure default xs)) := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    match ys with
    | [] =>
      have hsimp : maxByMeasure measure default (y :: []) = y := by rfl
      rw [hsimp]
      exact ⟨[], [], by simp, by simp, by simp⟩
    | z :: zs =>
      have hfind : maxByMeasure measure default (y :: z :: zs) =
          if measure y ≥ measure (maxByMeasure measure default (z :: zs)) then y
          else maxByMeasure measure default (z :: zs) := by rfl
      rw [hfind]
      have hne_rest : z :: zs ≠ [] := by simp
      rcases ih hne_rest with ⟨l₁', l₂', h_append, h_lt, h_le⟩
      have h_all_le : ∀ w ∈ z :: zs, measure w ≤ measure (maxByMeasure measure default (z :: zs)) := by
        intro w hw
        rw [h_append, List.mem_append] at hw
        rcases hw with (hw_l₁' | hw_rest)
        · have hlt := h_lt w hw_l₁'
          exact Nat.le_of_lt hlt
        · rw [List.mem_cons] at hw_rest
          rcases hw_rest with (rfl | hw_l₂')
          · exact le_refl _
          · exact h_le w hw_l₂'
      by_cases h : measure y ≥ measure (maxByMeasure measure default (z :: zs))
      · rw [if_pos h]
        refine ⟨[], z :: zs, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro w hw
          rw [h_append, List.mem_append] at hw
          rcases hw with (hw_l₁' | hw_rest)
          · have hlt := h_lt w hw_l₁'
            have hle' := Nat.le_of_lt hlt
            exact Nat.le_trans hle' h
          · rw [List.mem_cons] at hw_rest
            rcases hw_rest with (rfl | hw_l₂')
            · exact h
            · have hle' := h_le w hw_l₂'
              exact Nat.le_trans hle' h
      · rw [if_neg h]
        have h_lt_y : measure y < measure (maxByMeasure measure default (z :: zs)) :=
          Nat.lt_of_not_ge h
        refine ⟨y :: l₁', l₂', ?_, ?_, h_le⟩
        · calc
            y :: z :: zs = y :: (z :: zs) := rfl
            _ = y :: (l₁' ++ maxByMeasure measure default (z :: zs) :: l₂') :=
              congrArg (fun t => y :: t) h_append
            _ = (y :: l₁') ++ maxByMeasure measure default (z :: zs) :: l₂' := by simp
        · intro w hw
          cases hw with
          | head => exact h_lt_y
          | tail _ hw_l₁' => exact h_lt w hw_l₁'

/-- If the list is nonempty, `maxByMeasure` returns an element that is in the list. -/
lemma maxByMeasure_mem (measure : α → Nat) (default : α) (l : List α) (hne : l ≠ []) :
    maxByMeasure measure default l ∈ l := by
  induction l with
  | nil => contradiction
  | cons h t ih =>
    match t with
    | [] =>
      simp [maxByMeasure]
    | h' :: t' =>
      dsimp [maxByMeasure]
      by_cases hle : measure h ≥ measure (maxByMeasure measure default (h' :: t'))
      · simp [hle]
      · have hne' : h' :: t' ≠ [] := by simp
        have mem := ih hne'
        simp [hle, mem]

/-- For any `x` in `l`, `measure x ≤ measure (maxByMeasure measure default l)`.
This says `maxByMeasure` returns an element with maximal measure. -/
lemma maxByMeasure_max (measure : α → Nat) (default : α) (l : List α) (x : α) (hx : x ∈ l) :
    measure x ≤ measure (maxByMeasure measure default l) := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil x)
  | cons h t ih =>
    simp at hx
    rcases hx with (h_eq | hx')
    · rw [h_eq]
      match t with
      | [] =>
        simp [maxByMeasure]
      | h' :: t' =>
        dsimp [maxByMeasure]
        by_cases hle : measure h ≥ measure (maxByMeasure measure default (h' :: t'))
        · simp [hle]
        · simp [hle]
          exact Nat.le_of_lt (Nat.not_le.mp hle)
    · have h_ih : measure x ≤ measure (maxByMeasure measure default t) := ih hx'
      match t with
      | [] => exact absurd hx' (List.not_mem_nil x)
      | h' :: t' =>
        dsimp [maxByMeasure]
        by_cases hle : measure h ≥ measure (maxByMeasure measure default (h' :: t'))
        · simp [hle]
          exact Nat.le_trans h_ih hle
        · simp [hle]
          exact h_ih

/-! ### `argmaxIdx` — find the maximum value and its index in a list

Returns a pair `(maxVal, maxIdx)` where `maxVal` is the maximum element
and `maxIdx` is the index of its first occurrence.
Returns `(default, 0)` for the empty list.

Unlike `maxByWeight` / `maxInList` which return the maximizing *element*,
`argmaxIdx` also returns the *position* (index) of that element.
This is useful when the index is needed, e.g., for 2D matrix max-finding. -/

/-- Internal helper for `argmaxIdx`: scans a suffix of `l` starting at position `pos`,
looking for the maximum value. `bestVal` and `bestIdx` represent the best found so far
among elements at positions `< pos`. `l` is a ghost parameter (the original list)
used only for specification purposes. -/
def argmaxIdxScan {α : Type u} [LinearOrder α] [Inhabited α] (l : List α) (pos : Nat)
    (suffix : List α) (bestVal : α) (bestIdx : Nat) : α × Nat :=
  match suffix with
  | [] => (bestVal, bestIdx)
  | y :: ys =>
    if y > bestVal then
      argmaxIdxScan l (pos + 1) ys y pos
    else
      argmaxIdxScan l (pos + 1) ys bestVal bestIdx

/-- Find the maximum value and its first index in a list.
Returns `(default, 0)` for the empty list.
Example: `argmaxIdx [3, 1, 4, 1, 5] = (5, 4)`. -/
def argmaxIdx {α : Type u} [LinearOrder α] [Inhabited α] (l : List α) : α × Nat :=
  match l with
  | [] => (default, 0)
  | x :: xs => argmaxIdxScan l 1 xs x 0

/-- Correctness of `argmaxIdxScan`: under the given invariants, the result is a valid index
(less than the list length), the value at that index matches the returned value,
and every element in the list is ≤ the returned maximum. -/
lemma argmaxIdxScan_spec {α : Type u} [LinearOrder α] [Inhabited α]
    (l : List α) (pos : Nat) (suffix : List α) (bestVal : α) (bestIdx : Nat)
    (h_suffix_eq : suffix = l.drop pos)
    (h_len : pos + suffix.length = l.length)
    (h_bestIdx_pos : bestIdx < pos)
    (h_best_val : l.getD bestIdx default = bestVal)
    (h_bound : ∀ j, j < pos → l.getD j default ≤ bestVal) :
    (argmaxIdxScan l pos suffix bestVal bestIdx).2 < l.length ∧
    l.getD (argmaxIdxScan l pos suffix bestVal bestIdx).2 default =
      (argmaxIdxScan l pos suffix bestVal bestIdx).1 ∧
    ∀ j, j < l.length → l.getD j default ≤
      (argmaxIdxScan l pos suffix bestVal bestIdx).1 := by
  induction suffix generalizing pos bestVal bestIdx with
  | nil =>
    simp [argmaxIdxScan]
    simp at h_len
    have hmaxIdx_lt : bestIdx < l.length := by omega
    refine And.intro hmaxIdx_lt ?_
    refine And.intro h_best_val ?_
    intro j hj
    have hjpos : j < pos := by omega
    exact h_bound j hjpos
  | cons y ys ih =>
    have hy_val : l.getD pos default = y := by
      rw [← getD_drop_zero_eq_getD l pos default, ← h_suffix_eq]
      simp
    have h_suffix_eq' : ys = l.drop (pos + 1) := by
      calc
        ys = (y :: ys).drop 1 := by simp
        _ = (l.drop pos).drop 1 := by rw [h_suffix_eq]
        _ = l.drop (pos + 1) := by simp
    have h_len' : (pos + 1) + ys.length = l.length := by
      have : (y :: ys).length = ys.length + 1 := by simp
      rw [this] at h_len
      omega
    by_cases hy_gt : y > bestVal
    · have h_bound' : ∀ j, j < pos + 1 → l.getD j default ≤ y := by
        intro j hj
        have : j < pos ∨ j = pos := by omega
        rcases this with (hj' | rfl)
        · have hle := h_bound j hj'
          exact le_trans hle (le_of_lt hy_gt)
        · rw [hy_val]
      have h_idx' : pos < pos + 1 := by omega
      have h_val' : l.getD pos default = y := hy_val
      simp [argmaxIdxScan, hy_gt]
      exact ih (pos + 1) y pos h_suffix_eq' h_len' h_idx' h_val' h_bound'
    · have h_bound' : ∀ j, j < pos + 1 → l.getD j default ≤ bestVal := by
        intro j hj
        have : j < pos ∨ j = pos := by omega
        rcases this with (hj' | rfl)
        · exact h_bound j hj'
        · rw [hy_val]
          exact le_of_not_gt hy_gt
      have h_idx' : bestIdx < pos + 1 := by omega
      simp [argmaxIdxScan, hy_gt]
      exact ih (pos + 1) bestVal bestIdx h_suffix_eq' h_len' h_idx' h_best_val h_bound'

/-- Correctness of `argmaxIdx`: for a non-empty list, the returned index is valid,
the value at that index equals the returned maximum, and all elements are ≤ the maximum. -/
lemma argmaxIdx_spec {α : Type u} [LinearOrder α] [Inhabited α] (l : List α) (h_ne : l ≠ []) :
    (argmaxIdx l).2 < l.length ∧
    l.getD (argmaxIdx l).2 default = (argmaxIdx l).1 ∧
    ∀ j, j < l.length → l.getD j default ≤ (argmaxIdx l).1 := by
  cases l with
  | nil => exact absurd rfl h_ne
  | cons x xs =>
    have h_suffix_eq : xs = (x :: xs).drop 1 := by simp
    have h_len : 1 + xs.length = (x :: xs).length := by
      simp [add_comm]
    have h_idx : (0 : Nat) < 1 := by omega
    have h_val : (x :: xs).getD 0 default = x := by simp
    have h_bound : ∀ j, j < 1 → (x :: xs).getD j default ≤ x := by
      intro j hj
      have : j = 0 := by omega
      subst this
      simp
    simp [argmaxIdx]
    exact argmaxIdxScan_spec (x :: xs) 1 xs x 0 h_suffix_eq h_len h_idx h_val h_bound

/-! ### `maxIdx` — index of the maximum element using `List.argmax`

Finds the index of the first occurrence of the maximum element in a list
using `List.argmax id` followed by `idxOf`. Returns `default` for the empty list.

Unlike `argmaxIdx` above (which performs a custom scan and returns a `α × Nat` pair),
`maxIdx` delegates to the standard library's `List.argmax` and is lighter-weight
when only the index is needed and the maximum value itself is not required.
-/

/-- Index of the first occurrence of the maximum element in `l`.
Returns `default` if `l` is empty.
Example: `maxIdx [3, 1, 4, 1, 5] 0 = 4`. -/
def maxIdx [LinearOrder α] [DecidableEq α] (l : List α) (default : Nat) : Nat :=
  match List.argmax id l with
  | none => default
  | some m => l.idxOf m


lemma maxIdx_nil [LinearOrder α] [DecidableEq α] (default : Nat) :
    maxIdx ([] : List α) default = default := by
  simp [maxIdx, List.argmax_nil]

/-- If `l` is non-empty, then `maxIdx l default < l.length`. -/
lemma maxIdx_lt_length [LinearOrder α] [DecidableEq α] {l : List α} {default : Nat}
    (hne : l ≠ []) : maxIdx l default < l.length := by
  unfold maxIdx
  have h_argmax_none : List.argmax id l = none ↔ l = [] :=
    List.argmax_eq_none (f := id) (l := l)
  have h_argmax_ne_none : List.argmax id l ≠ none := by
    intro h; exact hne (h_argmax_none.mp h)
  cases hmax : List.argmax id l
  · contradiction
  · rename_i m
    simp
    have h_argmax_some := (List.argmax_eq_some_iff (f := id) (l := l)).mp hmax
    have h_mem : m ∈ l := h_argmax_some.1
    exact idxOf_lt_length h_mem

/-! ### `argmaxMeasure` — argmax by measure with first-occurrence tie-breaking

`argmaxMeasure` finds the element in `xs` maximizing `measure : α → Nat`.
It returns the **first** occurrence in case of ties, or `default` for the empty list.

Unlike `maxByWeight` / `maxInList` (which use a folding loop and tie-break by
keeping whichever element encountered first with strictly-greater weight),
`argmaxMeasure` is a two-pass algorithm: it first computes `maxVal measure xs`,
then uses `findIdx` to locate the first element achieving that value.

This formulation makes it easier to prove properties about tie-breaking
by position (see `argmaxMeasure_tie`). -/

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Find the first element in `xs` with maximum `measure : α → Nat`.
Returns `default` for the empty list. -/
def argmaxMeasure (measure : α → Nat) (xs : List α) : α :=
  let m := maxVal measure xs
  let idx := xs.findIdx (fun x => decide (measure x = m))
  if h : idx < xs.length then
    xs.get ⟨idx, h⟩
  else
    default

/-- If `xs` is nonempty, `argmaxMeasure measure xs` is in `xs`. -/
lemma argmaxMeasure_mem (measure : α → Nat) (xs : List α) (hne : xs ≠ []) :
    argmaxMeasure measure xs ∈ xs := by
  unfold argmaxMeasure
  rcases maxVal_exists measure xs hne with ⟨x, hx, heq⟩
  have h_lt : xs.findIdx (fun x => decide (measure x = maxVal measure xs)) < xs.length := by
    rw [List.findIdx_lt_length]
    exact ⟨x, hx, by simp [heq]⟩
  rw [dif_pos h_lt]
  exact List.get_mem _ _

/-- For any `x ∈ xs`, `measure x ≤ measure (argmaxMeasure measure xs)`. -/
lemma argmaxMeasure_max (measure : α → Nat) (xs : List α) (x : α) (hx : x ∈ xs) :
    measure x ≤ measure (argmaxMeasure measure xs) := by
  unfold argmaxMeasure
  by_cases hne : xs = []
  · subst hne; simp at hx
  · rcases maxVal_exists measure xs hne with ⟨x', hx', heq'⟩
    have h_lt : xs.findIdx (fun x => decide (measure x = maxVal measure xs)) < xs.length := by
      rw [List.findIdx_lt_length]
      exact ⟨x', hx', by simp [heq']⟩
    rw [dif_pos h_lt]
    let r := xs.get ⟨xs.findIdx (fun x => decide (measure x = maxVal measure xs)), h_lt⟩
    have h_r_val : measure r = maxVal measure xs := by
      have h_sat := ((List.findIdx_eq (h := h_lt)).mp rfl).1
      simpa using h_sat
    have h_x_le_max : measure x ≤ maxVal measure xs := maxVal_ge measure xs x hx
    have : measure x ≤ measure r := by
      rw [h_r_val]
      exact h_x_le_max
    exact this

/-- Tie-breaking by first occurrence: if `x ∈ xs` has the same measure as the result of
`argmaxMeasure`, then the result appears at or before `x` in `xs` (by `idxOf`).
This formalizes that `argmaxMeasure` returns the *first* element achieving the maximum. -/
lemma argmaxMeasure_tie (measure : α → Nat) (xs : List α) (x : α) (hx : x ∈ xs)
    (h_eq_len : measure x = measure (argmaxMeasure measure xs)) :
    idxOf (argmaxMeasure measure xs) xs ≤ idxOf x xs := by
  set idx := xs.findIdx (fun x => decide (measure x = maxVal measure xs)) with hidx
  have hne : xs ≠ [] := by
    intro h; subst h; simp at hx
  rcases maxVal_exists measure xs hne with ⟨x', hx', heq_x'⟩
  have h_lt : idx < xs.length := by
    rw [hidx, List.findIdx_lt_length]
    exact ⟨x', hx', by simp [heq_x']⟩
  have h_res : argmaxMeasure measure xs = xs.get ⟨idx, h_lt⟩ := by
    unfold argmaxMeasure
    dsimp
    rw [← hidx, dif_pos h_lt]
  have h_res_measure : measure (argmaxMeasure measure xs) = maxVal measure xs := by
    rw [h_res]
    have h_sat := ((List.findIdx_eq (h := h_lt)).mp rfl).1
    simpa [hidx] using h_sat
  have h_x_measure_max : measure x = maxVal measure xs := by
    rw [← h_res_measure, h_eq_len]
  have hfirst : idxOf (argmaxMeasure measure xs) xs ≤ idx := by
    apply idxOf_le_of_getElem_eq h_lt
    simpa using h_res.symm
  apply hfirst.trans
  by_contra hn
  have hsmall : idxOf x xs < idx := by omega
  have hfalse := List.not_of_lt_findIdx (p := fun y => decide (measure y = maxVal measure xs)) hsmall
  simp only [List.getElem_idxOf, h_x_measure_max, decide_true] at hfalse
  contradiction

/-! ### `bestByNatPair` — find best element by lexicographic `Nat × Nat` score -/

/-- Find the "best" element from `best :: cs` according to a `Nat × Nat` score,
where a larger first component is always better, and among equal first components,
a smaller second component is better. Ties (both components equal, or second component
being larger despite equal first) are broken in favor of the earlier element.

This is useful for "maximize primary score, minimize secondary score" patterns,
such as finding the most frequent character with earliest first occurrence as tiebreaker.

The result is guaranteed to be in `best :: cs`. -/
def bestByNatPair {α : Type} (score : α → Nat × Nat) : List α → α → α
  | [], best => best
  | c :: cs, best =>
    if (score c).1 > (score best).1 ∨ ((score c).1 = (score best).1 ∧ (score c).2 < (score best).2) then
      bestByNatPair score cs c
    else
      bestByNatPair score cs best

/-- The result of `bestByNatPair` is always in `best :: cs`. -/
lemma bestByNatPair_mem {α : Type} (score : α → Nat × Nat) (cs : List α) (best : α) :
    bestByNatPair score cs best ∈ best :: cs := by
  induction cs generalizing best with
  | nil =>
    simp [bestByNatPair]
  | cons c cs' ih =>
    simp only [bestByNatPair]
    split <;> rename_i hcond
    · -- goal: bestByNatPair score cs' c ∈ best :: c :: cs'
      exact List.mem_cons_of_mem best (ih c)
    · -- goal: bestByNatPair score cs' best ∈ best :: c :: cs'
      have hmem := ih best
      -- hmem: bestByNatPair score cs' best ∈ best :: cs'
      -- Use `List.mem_append` or `List.mem_cons` to break down membership
      have h_or := by
        -- `hmem` converted to an Or via `show_term` or `simp`
        simpa using hmem
      -- h_or : bestByNatPair score cs' best = best ∨ bestByNatPair score cs' best ∈ cs'
      rcases h_or with (heq | hm)
      · -- heq: element = best, so it's the head of best :: c :: cs'
        simp [heq]
      · -- hm: element ∈ cs', so it's after c
        have : bestByNatPair score cs' best ∈ c :: cs' := List.mem_cons_of_mem _ hm
        exact List.mem_cons_of_mem best this

/-- `bestByNatPair` returns an element that is optimal according to the lexicographic
ordering on `Nat × Nat`: maximize the first component, minimize the second.
For any `c` in `best :: cs`, the result `r` satisfies:
`(score r).1 ≥ (score c).1` and if they are equal then `(score r).2 ≤ (score c).2`. -/
lemma bestByNatPair_spec {α : Type} (score : α → Nat × Nat) : ∀ (cs : List α) (init c : α),
    c ∈ init :: cs →
    (score (bestByNatPair score cs init)).1 ≥ (score c).1 ∧
    ((score (bestByNatPair score cs init)).1 = (score c).1 →
     (score (bestByNatPair score cs init)).2 ≤ (score c).2)
  | [], init, c, hc => by
    have hc_eq : c = init := by simpa using hc
    rw [hc_eq]
    simp [bestByNatPair]
  | hd :: tl, init, c, hc => by
    have hc_cases : c = init ∨ c = hd ∨ c ∈ tl := by simpa using hc
    have ih := bestByNatPair_spec score tl
    dsimp [bestByNatPair]
    by_cases h : (score hd).1 > (score init).1 ∨ ((score hd).1 = (score init).1 ∧ (score hd).2 < (score init).2)
    · simp [h]
      rcases hc_cases with (hc_eq | hc_hd | hc_tl)
      · rw [hc_eq]
        have ih_hd := ih hd hd (by simp)
        rcases ih_hd with ⟨hge, htie⟩
        have h_hd_ge_init : (score hd).1 ≥ (score init).1 := by
          rcases h with (hgt | ⟨heq, hlt⟩)
          · omega
          · omega
        constructor
        · omega
        · intro heq_cnt
          have h_result_eq_hd : (score (bestByNatPair score tl hd)).1 = (score hd).1 := by
            omega
          rcases h with (hgt | ⟨heq_cnt_hd, hlt_idx⟩)
          · omega
          · have h_idx_le_hd := htie h_result_eq_hd
            omega
      · rw [hc_hd]
        exact ih hd hd (by simp)
      · exact ih hd c (by simp [hc_tl])
    · simp [h]
      rcases hc_cases with (hc_eq | hc_hd | hc_tl)
      · rw [hc_eq]
        exact ih init init (by simp)
      · rw [hc_hd]
        have ih_init := ih init init (by simp)
        rcases ih_init with ⟨hge_init, htie_init⟩
        have h_not_gt : ¬ (score hd).1 > (score init).1 := by
          intro hgt; apply h; left; exact hgt
        have h_not_better : ¬ ((score hd).1 = (score init).1 ∧ (score hd).2 < (score init).2) := by
          intro hbetter; apply h; right; exact hbetter
        constructor
        · omega
        · intro heq_cnt
          have h_result_eq_init : (score (bestByNatPair score tl init)).1 = (score init).1 := by
            omega
          have h_idx_le_init := htie_init h_result_eq_init
          have h_seq_eq : (score hd).1 = (score init).1 := by
            omega
          have h_idx_not_lt : ¬ (score hd).2 < (score init).2 := by
            intro hlt
            apply h_not_better
            exact ⟨h_seq_eq, hlt⟩
          omega
      · have h_c_in : c ∈ init :: tl := by simp [hc_tl]
        exact ih init c h_c_in

/-! ### `argmaxIdxByVal` — first-maximum index by element value (`LinearOrder`)

This is a simpler, index-only alternative to `argmaxIdxScan` (which returns `α × Nat`).
It uses the element type's `LinearOrder` directly (no weight/mesaure function) and
returns just the index of the first maximum element.  No `Inhabited` constraint needed.

Unlike `maxIdx` (which uses `List.argmax` + `idxOf`), this is a single-pass scan. -/

/-- Scan `remaining` for the first maximum, tracking the best value seen so far in
`bestVal` with its index `bestIdx`. `pos` is the current position in the original list.
When we find `x > bestVal`, update `bestIdx` to `pos` (first occurrence wins
because we only update on strict inequality). -/
def argmaxIdxByValAux {α : Type} [LinearOrder α] (remaining : List α) (bestVal : α) (bestIdx pos : Nat) : Nat :=
  match remaining with
  | [] => bestIdx
  | x :: xs =>
    if x > bestVal then
      argmaxIdxByValAux xs x pos (pos + 1)
    else
      argmaxIdxByValAux xs bestVal bestIdx (pos + 1)

/-- Find the index of the first maximum element in a list using the element type's
`LinearOrder`. Returns `0` for the empty list. -/
def argmaxIdxByVal {α : Type} [LinearOrder α] : List α → Nat
  | [] => 0
  | x :: xs => argmaxIdxByValAux xs x 0 1

/-- `argmaxIdxByValAux` always returns an index less than `bestIdx` or `pos` plus the length
of the remaining suffix (a bound useful for proving correctness). -/
lemma argmaxIdxByValAux_bound {α : Type} [LinearOrder α] (remaining : List α) (bestVal : α) (bestIdx pos : Nat)
    (h_best : bestIdx < pos) : argmaxIdxByValAux remaining bestVal bestIdx pos < pos + remaining.length := by
  induction remaining generalizing bestVal bestIdx pos with
  | nil =>
    simp [argmaxIdxByValAux]
    omega
  | cons x xs ih =>
    simp [argmaxIdxByValAux]
    split
    · have hres := ih x pos (pos + 1) (by omega)
      omega
    · have hres := ih bestVal bestIdx (pos + 1) (by omega)
      omega

/-! ### `argmaxD` — simple recursive max by weight with `[Inhabited α]`

This is the dual of `argminD`. Unlike `maxByWeight` (which requires an explicit `best`
parameter) or `argmaxBy` (which requires `LinearOrder α` for tie-breaking),
`argmaxD` only requires `[Inhabited α]` and uses a simple recursive comparison.
On ties (equal `f` values), the first occurrence wins.
-/

/-- Find the element in `xs` maximizing `f : α → Nat`, using `default` for the empty list.
Only `[Inhabited α]` is needed — no `LinearOrder` or `DecidableEq` constraints.
On ties, the earlier element is kept. -/
def argmaxD {α : Type} [Inhabited α] (f : α → Nat) : List α → α
  | [] => default
  | [a] => a
  | a :: rest =>
    let r := argmaxD f rest
    if f a < f r then r else a

/-- Specification for `argmaxD`: for a nonempty list, the result is in the list,
maximizes `f`, and all elements before the first occurrence of the result have strictly
smaller `f` values. -/
lemma argmaxD_spec {α : Type} [DecidableEq α] [Inhabited α] (f : α → Nat) (xs : List α) (hne : xs ≠ []) :
    argmaxD f xs ∈ xs ∧
    (∀ s ∈ xs, f s ≤ f (argmaxD f xs)) ∧
    (∀ s ∈ xs.takeWhile (fun x => x ≠ argmaxD f xs),
      f s < f (argmaxD f xs)) := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons h t ih =>
    cases t with
    | nil =>
      simp [argmaxD]
    | cons h2 t' =>
      have hne' : h2 :: t' ≠ [] := by simp
      have ih' := ih hne'
      rcases ih' with ⟨hmem, hmax, hstrict⟩
      rw [argmaxD]
      · by_cases hlt : f h < f (argmaxD f (h2 :: t'))
        · rw [if_pos hlt]
          refine ⟨?_, ?_, ?_⟩
          · exact List.mem_cons_of_mem h hmem
          · intro s hs
            have hcases := ((List.mem_cons (a := s) (b := h) (l := h2 :: t')).mp hs)
            rcases hcases with (rfl | hs')
            · exact Nat.le_of_lt hlt
            · exact hmax s hs'
          · have hr_ne_h : argmaxD f (h2 :: t') ≠ h := by
              intro heq
              rw [heq] at hlt
              exact Nat.lt_irrefl _ hlt
            have htake : (h :: h2 :: t').takeWhile (fun x => x ≠ argmaxD f (h2 :: t')) =
                h :: (h2 :: t').takeWhile (fun x => x ≠ argmaxD f (h2 :: t')) := by
              simp [hr_ne_h.symm]
            rw [htake]
            intro s hs
            have hcases := ((List.mem_cons (a := s) (b := h)
              (l := (h2 :: t').takeWhile (fun x => x ≠ argmaxD f (h2 :: t')))).mp hs)
            rcases hcases with (rfl | hs')
            · exact hlt
            · exact hstrict s hs'
        · rw [if_neg hlt]
          refine ⟨?_, ?_, ?_⟩
          · apply List.mem_cons_self
          · intro s hs
            have hcases := ((List.mem_cons (a := s) (b := h) (l := h2 :: t')).mp hs)
            rcases hcases with (rfl | hs')
            · exact Nat.le_refl _
            · have hge : f (argmaxD f (h2 :: t')) ≤ f h := by omega
              have hle := hmax s hs'
              exact Nat.le_trans hle hge
          · simp
      · simp

/-! ### `argmaxByFold` — two-pass argmax via fold + filter

`argmaxByFold measure default xs` computes the maximum value of `measure` over `xs` by folding
`Nat.max`, then filters to find all elements achieving that maximum, and returns the first
(first-occurrence tie-breaking). Returns `default` for the empty list.

The filter-based approach makes membership and maximiality proofs straightforward:
the result is guaranteed to be in the filtered list of maximal-measure elements
(see `argmaxByFold_spec`). -/

/-- From a list, pick an element that maximizes a given measure `measure : α → Nat`.
Returns `default` for the empty list; for nonempty lists, returns the *first*
element (in list order) that achieves the maximum measure.

This is a two-pass algorithm: first compute the maximum value via `foldl Nat.max`,
then filter to find all achieving elements and return the first. -/
def argmaxByFold (measure : α → Nat) (default : α) (ws : List α) : α :=
  let maxLen := ws.foldl (fun acc x => Nat.max acc (measure x)) 0
  let maxWs := ws.filter (fun x => measure x = maxLen)
  match maxWs with
  | [] => default
  | x :: _ => x

/-- For a nonempty list, `argmaxByFold` returns an element from the filtered list of
maximum-measure elements. In particular, the result's measure equals the maximum
measure computed by folding `Nat.max` over the list. -/
lemma argmaxByFold_spec (measure : α → Nat) (default : α) (ws : List α) (hne : ws ≠ []) :
    argmaxByFold measure default ws ∈ (ws.filter (fun x => measure x = ws.foldl (fun acc y => Nat.max acc (measure y)) 0)) := by
  have he : ws.foldl (fun acc y => Nat.max acc (measure y)) 0 = maxVal measure ws := by
    simpa using foldl_max_eq_maxVal measure ws 0
  obtain ⟨x, hx, hv⟩ := maxVal_exists measure ws hne
  have hm : x ∈ ws.filter (fun x => measure x = ws.foldl (fun acc y => Nat.max acc (measure y)) 0) := by
    simp [he, hx, hv]
  unfold argmaxByFold
  dsimp only
  split
  · next hnil => simp [hnil] at hm
  · next l a as heq => rw [heq]; simp

end List

namespace List

/-! # Best score scanning over lists

This module provides functions for scanning a list to find the maximum score
among elements that satisfy a validity predicate.

- **`bestUpdate`**: Update the current best `Option Nat` score with a new candidate element.
- **`bestScan`**: Scan a list from left to right, tracking the maximum score among valid elements.
  Returns `none` if no valid element is found, or `some p` where `p` is the maximum score.
-/

variable {α : Type}

/-- Update the best (maximum) score seen so far with a new candidate element.
If `valid a` holds, the candidate's `score a` may replace the current best if higher.
Otherwise, the current best is unchanged. -/
def bestUpdate (valid : α → Bool) (score : α → Nat) (best : Option Nat) (a : α) : Option Nat :=
  if valid a then
    match best with
    | none => some (score a)
    | some p => if score a > p then some (score a) else best
  else best

/-- Scan a list from left to right, tracking the best (maximum) score among valid elements.
`best` is the best score from already-processed elements.
Returns `none` if no valid element is found. -/
def bestScan (valid : α → Bool) (score : α → Nat) (xs : List α) (best : Option Nat) : Option Nat :=
  match xs with
  | [] => best
  | x :: xs' => bestScan valid score xs' (bestUpdate valid score best x)

/-- Invariant for `bestScan`: relates the current `best` value to the `processed` prefix.
- If `best = none`, no processed element satisfies `valid`.
- If `best = some p`, there exists a processed element with score `p`, and `p` is maximal
  among scores of valid processed elements. -/
def bestInvariant (valid : α → Bool) (score : α → Nat) (processed : List α) (best : Option Nat) : Prop :=
  (best = none → ∀ x ∈ processed, valid x = false) ∧
  (∀ p, best = some p →
    (∃ x ∈ processed, valid x = true ∧ score x = p) ∧
    ∀ y ∈ processed, valid y = true → score y ≤ p)

/-- If the current best is `some p`, updating with any element never yields `none`. -/
lemma bestUpdate_some_ne_none {valid : α → Bool} {score : α → Nat} (p : Nat) (a : α) :
    bestUpdate valid score (some p) a ≠ none := by
  unfold bestUpdate
  split
  · dsimp
    split <;> simp
  · simp

/-- Updating from `none` yields `none` iff the element is not valid. -/
lemma bestUpdate_none_eq_none_iff {valid : α → Bool} {score : α → Nat} (a : α) :
    bestUpdate valid score none a = none ↔ valid a = false := by
  unfold bestUpdate
  constructor
  · intro h
    by_contra h'
    simp [h'] at h
  · intro h
    simp [h]

end List

namespace List

/-! ### Finding the best element by a custom comparator -/

/-- Select the "best" element from a list according to a custom comparator `better : α → α → Bool`.
`better a b = true` means `a` is strictly better than `b`. Returns `default` for the empty list,
and the singleton element for single-element lists.
For example, `bestBy 0 (· < ·) [3, 1, 4, 2] = 1` finds the minimum. -/
def bestBy (default : α) (better : α → α → Bool) : List α → α
  | [] => default
  | [t] => t
  | t :: ts =>
    let b := bestBy default better ts
    if better t b then t else b

/-! ### Picking the better of two elements by a score function -/

/-- Given a `score` function and two elements `a, b`, return the "better" one:
higher score wins, ties are broken by returning the smaller element (via `min a b`).
This is the two-element comparison version of `bestBy`; used as the fold step in
`foldl` to find the best element in a list. -/
def selectBetter {α : Type} [LinearOrder α] (score : α → Nat) (a b : α) : α :=
  if score b > score a then b
  else if score b = score a then min a b
  else a

/-- `selectBetter` always returns an element whose score is at least as large as `b`'s score. -/
lemma selectBetter_score_ge_right {α : Type} [LinearOrder α] (score : α → Nat) (a b : α) :
    score b ≤ score (selectBetter score a b) := by
  unfold selectBetter
  split
  · rfl
  · split
    · by_cases hle : a ≤ b
      · simp [min_eq_left hle, (by assumption : score b = score a)]
      · have hle' : b ≤ a := le_of_not_ge hle
        simp [min_eq_right hle']
    · have h_not_gt : ¬ score b > score a := by assumption
      have h_not_eq : ¬ score b = score a := by assumption
      omega

/-! ### Finding the element in a list closest to a target -/

/-- Select the better of two values `a` and `b` relative to a `target`.
Returns the value whose `Nat.absDiff` from `target` is smaller.
If the distances are equal, returns the smaller value. -/
def selectClosest (target a b : Nat) : Nat :=
  let da := Nat.absDiff a target
  let db := Nat.absDiff b target
  if db < da then b
  else if da < db then a
  else if a ≤ b then a else b

/-- Recursively find the value in `cs` that minimizes `Nat.absDiff` to `target`,
using `best` as the current best candidate. The result is a value drawn from
`best :: cs` that is closest to `target` (ties broken by smaller value). -/
def findClosestAux (target : Nat) : Nat → List Nat → Nat
  | best, [] => best
  | best, c :: cs => findClosestAux target (selectClosest target best c) cs

end List



namespace List

/-! # Maximum by length — pick the longest list from a list of lists

This module provides `maxByLength`, a function that selects the list with maximum
length from a `List (List α)`, along with lemmas about its properties.

This is a specialization of the general "argmax" pattern: it picks the element
from a list of lists that has the greatest `.length`. -/

/-- From a list of lists, return the one with maximum length.
Returns `[]` when the input list is empty. -/
def maxByLength {α : Type u} (candidates : List (List α)) : List α :=
  match candidates with
  | [] => []
  | x :: xs =>
    let r := maxByLength xs
    if r.length ≥ x.length then r else x

/-! ### Properties of `maxByLength` -/

/-- If every element in `xs` is a sublist of `l`, then `maxByLength xs` is also a sublist of `l`. -/
lemma maxByLength_sublist {α : Type u} (xs : List (List α)) (l : List α)
    (h : ∀ s ∈ xs, s <+ l) : maxByLength xs <+ l := by
  induction xs with
  | nil =>
    unfold maxByLength
    exact List.nil_sublist _
  | cons x xs' ih =>
    unfold maxByLength
    simp
    have hx := h x (by simp)
    have hxs' : ∀ s ∈ xs', s <+ l := by
      intro s hs; exact h s (by simp [hs])
    split
    · exact ih hxs'
    · exact hx

/-- For any `s ∈ xs`, the length of `s` is ≤ the length of `maxByLength xs`. -/
lemma maxByLength_max_length {α : Type u} (xs : List (List α)) (s : List α) (h : s ∈ xs) :
    s.length ≤ (maxByLength xs).length := by
  induction xs with
  | nil =>
    exfalso; exact List.not_mem_nil _ h
  | cons x xs' ih =>
    unfold maxByLength
    simp
    rcases List.mem_cons.mp h with (rfl | h)
    · split
      · omega
      · omega
    · have hlen := ih h
      split
      · omega
      · omega

/-! ### Maximum measure value

`maxMeasure f l` computes the maximum value of `f a` for `a ∈ l`.
Returns `0` for the empty list. This is the "value-only" counterpart of `maxByLength`:
`maxByLength` returns the *element* with max length, while `maxMeasure` returns just the max value.
For `List String`, use `maxMeasure String.length ws` to get the maximum word length.
-/

/-- Compute the maximum value of a `Nat`-valued measure `f` over a list.
Returns `0` for the empty list. -/
def maxMeasure {α : Type u} (f : α → Nat) : List α → Nat
| [] => 0
| a :: as => Nat.max (f a) (maxMeasure f as)

/-- For any element `a ∈ l`, `f a ≤ maxMeasure f l`. -/
lemma maxMeasure_ge {α : Type u} (f : α → Nat) (l : List α) (a : α) (ha : a ∈ l) :
    f a ≤ maxMeasure f l := by
  induction' l with hd tl ih
  · simp at ha
  · simp at ha
    rcases ha with (rfl | ha')
    · simp [maxMeasure]
    · have h := ih ha'
      simp [maxMeasure, h]

/-- If `l` is nonempty, there exists some element `a ∈ l` achieving the maximum measure,
i.e., `f a = maxMeasure f l`. -/
lemma exists_maxMeasure {α : Type u} (f : α → Nat) (l : List α) (hne : l ≠ []) :
    ∃ a ∈ l, f a = maxMeasure f l := by
  induction' l with hd tl ih
  · exact absurd rfl hne
  · by_cases htl : tl = []
    · subst htl
      exact ⟨hd, by simp, by simp [maxMeasure]⟩
    · rcases ih htl with ⟨a, ha, ha_len⟩
      by_cases h : maxMeasure f tl ≤ f hd
      · exact ⟨hd, by simp, by
          simp [maxMeasure]
          exact h⟩
      · refine ⟨a, by simp [ha], ?_⟩
        have h' : f hd ≤ maxMeasure f tl := Nat.le_of_not_ge h
        simp [maxMeasure, Nat.max_eq_right h', ha_len]

end List
