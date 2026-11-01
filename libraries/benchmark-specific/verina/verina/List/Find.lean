import Mathlib

namespace Specific

open _root_.List

namespace List

/-!
# `findIdx` theorems

Properties of `List.findIdx` relating the result index to the predicate value.
-/

/--
If `findIdx p xs` is within bounds, then `p` holds at that index
(using `getElem!`, the `Inhabited`-backed indexing notation).
-/
theorem findIdx_getElem!_eq_true {α : Type} [Inhabited α] (p : α → Bool) (xs : List α)
    (h : xs.findIdx p < xs.length) : p xs[xs.findIdx p]! = true := by
  have h_elem := List.findIdx_getElem (w := h)
  have h_pos := getElem!_pos xs (xs.findIdx p) h
  rw [h_pos]
  exact h_elem

/--
If `i < l.findIdx p`, then `p` returns `false` on element `i`.
That is, every element *before* the first match fails the predicate.
-/
theorem findIdx_getElem_eq_false_of_lt {α : Type} {p : α → Bool} :
    ∀ {l : List α} {i : Nat} (_ : i < l.findIdx p) (hi_len : i < l.length),
      p (l[i]'hi_len) = false
  | [], _, _, hlen => by cases hlen
  | a :: as, i, hi, hlen => by
      rw [List.findIdx_cons] at hi
      by_cases hp : p a = true
      · simp [hp] at hi
      · cases i with
        | zero => exact Bool.eq_false_iff.2 hp
        | succ i =>
            have hi' : i < as.findIdx p := by
              simp [hp] at hi
              omega
            have hlen' : i < as.length := by simpa using hlen
            simpa using findIdx_getElem_eq_false_of_lt (p := p) hi' hlen'

/-!
# `firstIdxWhere` – Prop-based first-index search

`firstIdxWhere p xs` returns `some i` where `i` is the first index in `xs` with
`p (xs[i])` holding (as a `Prop`), or `none` if no element satisfies `p`.
Unlike `findIdx` (which works on `α → Bool`), this version accepts `p : α → Prop`
with a `DecidablePred` instance – often more natural in theorem statements.

`firstIdxOf` is the specialization for equality:
`firstIdxOf xs key = firstIdxWhere (· = key) xs`.
-/

/--
Find the first index `i` in `xs` such that `p (xs[i])` holds (as a `Prop`),
returning `some i`, or `none` if no element satisfies `p`.
-/
def firstIdxWhere {α : Type u} (p : α → Prop) [DecidablePred p] : List α → Option Nat
  | [] => none
  | x :: xs => if p x then some 0 else (firstIdxWhere p xs).map Nat.succ

/--
`firstIdxOf xs key` returns the first index of `key` in `xs`, or `none` if not found.
Specialization of `firstIdxWhere` to equality.
-/
def firstIdxOf {α : Type u} [DecidableEq α] (xs : List α) (key : α) : Option Nat :=
  firstIdxWhere (fun x => x = key) xs

/--
If `firstIdxWhere p xs` returns `some idx`, then `idx` is a valid index,
`p` holds at `xs[idx]!`, and no earlier index satisfies `p`.
-/
lemma firstIdxWhere_some_spec {α : Type u} [Inhabited α] {p : α → Prop} [DecidablePred p]
    {xs : List α} {idx : Nat} (h : firstIdxWhere p xs = some idx) :
    idx < xs.length ∧ p xs[idx]! ∧ ∀ j : Nat, j < idx → ¬ p xs[j]! := by
  induction xs generalizing idx with
  | nil =>
      simp [firstIdxWhere] at h
  | cons x xs ih =>
      unfold firstIdxWhere at h
      by_cases hx : p x
      · simp [hx] at h
        subst idx
        simp [hx]
      · simp [hx] at h
        rcases h with ⟨idx', hidx', hs⟩
        subst idx
        have ihspec := ih hidx'
        constructor
        · simp [ihspec.1]
        constructor
        · simpa using ihspec.2.1
        · intro j hj
          cases j with
          | zero =>
              simpa using hx
          | succ j =>
              have hj' : j < idx' := Nat.succ_lt_succ_iff.mp hj
              simpa using ihspec.2.2 j hj'

/--
If `firstIdxWhere p xs` returns `none`, then no element in `xs` satisfies `p`.
-/
lemma firstIdxWhere_none_spec {α : Type u} [Inhabited α] {p : α → Prop} [DecidablePred p]
    {xs : List α} (h : firstIdxWhere p xs = none) :
    ∀ j : Nat, j < xs.length → ¬ p xs[j]! := by
  induction xs with
  | nil =>
      intro j hj
      simp at hj
  | cons x xs ih =>
      unfold firstIdxWhere at h
      by_cases hx : p x
      · simp [hx] at h
      · simp [hx] at h
        intro j hj
        cases j with
        | zero =>
            simpa using hx
        | succ j =>
            have hj' : j < xs.length := Nat.succ_lt_succ_iff.mp hj
            simpa using ih h j hj'

/-!
# `firstIndexWhere` – Bool-based first-index search

`firstIndexWhere p xs` returns `some i` where `i` is the first index in `xs`
with `p (xs[i])` returning `true` (as a `Bool`), or `none` if no element satisfies `p`.
Unlike `firstIdxWhere` (which works on `α → Prop` with `DecidablePred`),
this version is `Bool`-based and simpler.

`firstIndexOf` is the specialization for `BEq`-based equality:
`firstIndexOf key xs = firstIndexWhere (· == key) xs`.
-/

/--
Find the first index `i` in `xs` such that `p x` returns `true`,
returning `some i`, or `none` if no element satisfies `p`.
-/
def firstIndexWhere (p : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs =>
      if p x then
        some 0
      else
        (firstIndexWhere p xs).map Nat.succ

/--
`firstIndexOf key xs` returns the first index of `key` in `xs` (using `BEq`),
or `none` if not found.
-/
def firstIndexOf [BEq α] (key : α) (xs : List α) : Option Nat :=
  firstIndexWhere (fun x => x == key) xs

end List

end Specific
