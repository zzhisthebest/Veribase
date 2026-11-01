import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import fvapps.List.Sort
import fvapps.List.Remove

namespace Specific

open _root_.List

namespace List

/-! ## Maximum/Extremum selection over lists -/

/-- Maximum `Nat` score in a list, with `0` for an empty list. -/
def listMaxBy {α : Type} (score : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => max (score x) (listMaxBy score xs)

/-- Maximum of a list of natural numbers, with `0` for an empty list. -/
def listMax : List Nat → Nat :=
  listMaxBy id

@[simp] theorem listMaxBy_nil {α : Type} (score : α → Nat) : listMaxBy score [] = 0 := rfl

@[simp] theorem listMax_nil : listMax ([] : List Nat) = 0 := rfl

@[simp] theorem listMax_singleton (n : Nat) : listMax [n] = n := by simp [listMax, listMaxBy]

/-- The maximum score is bounded by any upper bound of all scores. -/
theorem listMaxBy_le_of_forall_mem {α : Type} (score : α → Nat) (l : List α)
    {bound : Nat} (h : ∀ x, x ∈ l → score x ≤ bound) :
    listMaxBy score l ≤ bound := by
  induction l with
  | nil => simp [listMaxBy]
  | cons x xs ih =>
      simp [listMaxBy, h x (by simp),
        ih (fun z hz => h z (by simp [hz]))]

/-- The maximum of a list of naturals is bounded by any upper bound. -/
theorem listMax_le_of_forall_mem (l : List Nat) {bound : Nat}
    (h : ∀ x, x ∈ l → x ≤ bound) : listMax l ≤ bound :=
  listMaxBy_le_of_forall_mem id l h

/-- The maximum score is at most the score of the head in a sorted list. -/
theorem listMaxBy_le_head_of_sorted_permutation {α : Type} (score : α → Nat)
    {l : List α} {head : α} {tail : List α}
    (hSort : sortByDescending score l = head :: tail) :
    listMaxBy score l ≤ score head :=
  listMaxBy_le_of_forall_mem score l (fun x hx => by
    have hMemSort : x ∈ sortByDescending score l :=
      mem_sortByDescending_of_mem score hx
    rw [hSort] at hMemSort
    exact score_le_head_score_of_mem_sorted_desc
      (by simpa [hSort] using sortByDescending_sorted score l) hMemSort)

/-! ## Minimum `Nat` score over lists -/

/-- Minimum `Nat` score in a list, with a customizable default for the empty list. -/
def listMinByD (default : Nat) (score : α → Nat) : List α → Nat
  | [] => default
  | x :: xs => xs.foldl (fun best item => Nat.min best (score item)) (score x)

@[simp] theorem listMinByD_nil {α : Type} (default : Nat) (score : α → Nat) :
    listMinByD default score [] = default := rfl

@[simp] theorem listMinByD_singleton {α : Type} (default : Nat) (score : α → Nat) (x : α) :
    listMinByD default score [x] = score x := by
  simp [listMinByD]

/-! ## Minimum with customizable fallback (generic)

This is the generic analog of `listMaxD`. For `Nat`-specific minimum
with a score function, see `listMinByD`. -/

/-- Minimum of a list, with a customizable default for the empty list.
Works for any type with `Min`. Returns the actual element for singleton
lists, so the result is always a member of any nonempty list. -/
def listMinD [Min α] (fallback : α) : List α → α
  | [] => fallback
  | [x] => x
  | x :: y :: xs => min x (listMinD fallback (y :: xs))

/-- Minimum of a list of natural numbers, with `0` for an empty list. -/
def listMin : List Nat → Nat :=
  listMinD 0

@[simp] theorem listMinD_nil [Min α] (fallback : α) : listMinD fallback ([] : List α) = fallback := rfl

@[simp] theorem listMinD_singleton [Min α] (fallback x : α) : listMinD fallback [x] = x := rfl

@[simp] theorem listMin_nil : listMin ([] : List Nat) = 0 := rfl

@[simp] theorem listMin_singleton (x : Nat) : listMin [x] = x := by
  simp [listMin, listMinD]

/-- `listMinD` with duplicate elements returns the element. -/
theorem listMinD_duplicate [LinearOrder α] (fallback x : α) :
    listMinD fallback [x, x] = x := by
  simp [listMinD]

/-! ## Maximum with customizable fallback -/

/-- Maximum of a list, with a customizable default for the empty list.
Works for any type with `Max`. Returns the actual element for singleton
lists, so the result is always a member of any nonempty list. -/
def listMaxD [Max α] (fallback : α) : List α → α
  | [] => fallback
  | [x] => x
  | x :: y :: xs => max x (listMaxD fallback (y :: xs))

@[simp] theorem listMaxD_nil [Max α] (fallback : α) : listMaxD fallback ([] : List α) = fallback := rfl

@[simp] theorem listMaxD_singleton [Max α] (fallback x : α) : listMaxD fallback [x] = x := rfl

/-! ## Minimum with fallback (using `List.min?`) -/

/-- Returns the minimum element of a list, or `fallback` if the list is empty.
    Uses `List.min?` from the standard library. -/
def minWithFallback (fallback : Nat) (candidates : List Nat) : Nat :=
  candidates.min?.getD fallback

@[simp]
theorem minWithFallback_nil (fallback : Nat) : minWithFallback fallback [] = fallback := by
  simp [minWithFallback]

@[simp]
theorem minWithFallback_singleton (fallback x : Nat) : minWithFallback fallback [x] = x := by
  simp [minWithFallback]

/-! ## `max?` and `getElem!` -/

/-- If all elements in `xs` are ≤ the element at index `idx`,
then `max? xs` returns that element. -/
lemma max?_eq_some_of_getElem!_ge {xs : List Nat} {idx : Nat}
    (hidx : idx < xs.length)
    (hmax : ∀ i, i < xs.length → xs[i]! ≤ xs[idx]!) :
    List.max? xs = some xs[idx]! := by
  apply (List.max?_eq_some_iff (fun a : Nat => le_rfl)
    (fun a b : Nat => by
      cases le_total a b with
      | inl h => exact Or.inr (max_eq_right h)
      | inr h => exact Or.inl (max_eq_left h))
    (fun a b c : Nat => Nat.max_le)).2
  constructor
  · rw [getElem!_pos xs idx hidx]
    exact List.getElem_mem hidx
  · intro b hb
    rcases List.mem_iff_get.mp hb with ⟨i, hi⟩
    have hle := hmax i.val i.isLt
    rw [getElem!_pos xs i.val i.isLt] at hle
    rwa [← hi, List.get_eq_getElem]

/-- If `max? xs` is defined and `xs[idx]!` is maximal among the elements,
then they are equal. -/
lemma getElem!_eq_max?_get_of_ge {xs : List Nat} {idx : Nat}
    (hidx : idx < xs.length)
    (hmax : (List.max? xs).isSome)
    (hge : ∀ i, i < xs.length → xs[i]! ≤ xs[idx]!) :
    xs[idx]! = (List.max? xs).get hmax := by
  have hsome : List.max? xs = some xs[idx]! :=
    max?_eq_some_of_getElem!_ge hidx hge
  have hmem : xs[idx]! ∈ List.max? xs := by
    rw [hsome]
    simp
  have hget := Option.get_of_mem hmax hmem
  simpa using hget.symm

/-! ## Membership and ordering theorems for `listMaxD` / `listMinD` -/

/-- For any nonempty list, `listMaxD` returns an element of the list. -/
lemma listMaxD_mem [LinearOrder α] (default : α) {arr : List α} (h : arr.length > 0) :
    listMaxD default arr ∈ arr := by
  match arr with
  | [] => simp at h
  | [x] => simp [listMaxD]
  | x :: y :: xs =>
    by_cases hx : x ≤ listMaxD default (y :: xs)
    · rw [show listMaxD default (x :: y :: xs) = listMaxD default (y :: xs) by
        simp [listMaxD, max_eq_right hx]]
      have hm : listMaxD default (y :: xs) ∈ y :: xs :=
        listMaxD_mem default (arr := y :: xs) (by simp)
      exact List.mem_cons_of_mem x hm
    · have htail : listMaxD default (y :: xs) ≤ x := le_of_not_ge hx
      rw [show listMaxD default (x :: y :: xs) = x by
        simpa [listMaxD] using max_eq_left htail]
      simp

/-- Every element of a list is ≤ `listMaxD` of that list. -/
lemma le_listMaxD_of_mem [LinearOrder α] (default : α) :
    ∀ {arr : List α} {x : α}, x ∈ arr → x ≤ listMaxD default arr
  | [], _, h => by simp at h
  | [y], x, h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst x
      simp [listMaxD]
  | y :: z :: xs, x, h => by
      have h_mem : x = y ∨ x ∈ z :: xs := by simpa using h
      rcases h_mem with (rfl | htail)
      · simp [listMaxD]
      · have hrec : x ≤ listMaxD default (z :: xs) :=
          le_listMaxD_of_mem default htail
        simpa [listMaxD] using le_trans hrec (le_max_right y (listMaxD default (z :: xs)))

/-- For any nonempty list, `listMinD` returns an element of the list. -/
lemma listMinD_mem [LinearOrder α] (default : α) :
    ∀ {arr : List α}, arr.length > 0 → listMinD default arr ∈ arr
  | [], h => by simp at h
  | [x], _ => by simp [listMinD]
  | x :: y :: xs, _ => by
      by_cases hx : listMinD default (y :: xs) ≤ x
      · rw [show listMinD default (x :: y :: xs) = listMinD default (y :: xs) by
          simp [listMinD, min_eq_right hx]]
        have hm : listMinD default (y :: xs) ∈ y :: xs :=
          listMinD_mem default (arr := y :: xs) (by simp)
        exact List.mem_cons_of_mem x hm
      · have hhead : x ≤ listMinD default (y :: xs) := le_of_not_ge hx
        rw [show listMinD default (x :: y :: xs) = x by
          simpa [listMinD] using min_eq_left hhead]
        simp

/-- `listMinD` of a list is ≤ every element of the list. -/
lemma listMinD_le_of_mem [LinearOrder α] (default : α) :
    ∀ {arr : List α} {x : α}, x ∈ arr → listMinD default arr ≤ x
  | [], _, h => by simp at h
  | [y], x, h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst x
      simp [listMinD]
  | y :: z :: xs, x, h => by
      simp only [List.mem_cons] at h
      change min y (listMinD default (z :: xs)) ≤ x
      rcases h with hhead | htail
      · subst x
        exact min_le_left y (listMinD default (z :: xs))
      · have hrec : listMinD default (z :: xs) ≤ x :=
          listMinD_le_of_mem default (arr := z :: xs) (by simpa [List.mem_cons] using htail)
        exact le_trans (min_le_right y (listMinD default (z :: xs))) hrec

/-- For any nonempty list, `listMinD` ≤ `listMaxD`. -/
lemma listMinD_le_listMaxD_of_nonempty [LinearOrder α] (default : α) {arr : List α}
    (h : arr.length > 0) :
    listMinD default arr ≤ listMaxD default arr := by
  match arr with
  | [] => simp at h
  | [x] => simp [listMinD, listMaxD]
  | x :: y :: xs =>
    simp only [listMinD, listMaxD]
    exact le_trans (min_le_left _ _) (le_max_left _ _)

/-- `listMaxD` is invariant under list reversal. -/
lemma listMaxD_reverse [LinearOrder α] (default : α) (arr : List α) (h : arr.length > 0) :
    listMaxD default arr.reverse = listMaxD default arr := by
  have hrev : arr.reverse.length > 0 := by simpa using h
  apply le_antisymm
  · exact le_listMaxD_of_mem default (by
      have hm := listMaxD_mem default (arr := arr.reverse) hrev
      simpa using hm)
  · exact le_listMaxD_of_mem default (arr := arr.reverse) (by
      have hm := listMaxD_mem default (arr := arr) h
      simpa using hm)

/-- `listMinD` is invariant under list reversal. -/
lemma listMinD_reverse [LinearOrder α] (default : α) (arr : List α) (h : arr.length > 0) :
    listMinD default arr.reverse = listMinD default arr := by
  have hrev : arr.reverse.length > 0 := by simpa using h
  apply le_antisymm
  · exact listMinD_le_of_mem default (arr := arr.reverse) (by
      have hm := listMinD_mem default (arr := arr) h
      simpa using hm)
  · exact listMinD_le_of_mem default (by
      have hm := listMinD_mem default (arr := arr.reverse) hrev
      simpa using hm)

/-! ## Maximum with fallback (simpler recursion)

`listMaxWithDefault` uses plain `max x (rest_max)` recursion without a
singleton base case. This makes induction proofs simpler and guarantees
the result is always at least the fallback. Contrast with `listMaxD`,
which returns the actual element for singletons. -/

/-- Maximum of a list with a customizable default value for the empty list.
For each element, takes `max x (recursive_call)`, so the result is always
at least `fallback`. -/
def listMaxWithDefault {α : Type} [Max α] (fallback : α) : List α → α
  | [] => fallback
  | x :: xs => max x (listMaxWithDefault fallback xs)

@[simp]
theorem listMaxWithDefault_nil {α : Type} [Max α] (fallback : α) :
    listMaxWithDefault fallback [] = fallback := rfl

@[simp]
theorem listMaxWithDefault_cons {α : Type} [Max α] (fallback x : α) (xs : List α) :
    listMaxWithDefault fallback (x :: xs) = max x (listMaxWithDefault fallback xs) := rfl

/-- The result of `listMaxWithDefault` is always at least the fallback value. -/
theorem listMaxWithDefault_ge_fallback {α : Type} [LinearOrder α] (fallback : α) (xs : List α) :
    fallback ≤ listMaxWithDefault fallback xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [listMaxWithDefault_cons]
    exact le_trans ih (le_max_right _ _)

/-- If every element of the list is at most the fallback, then `listMaxWithDefault`
returns the fallback. -/
theorem listMaxWithDefault_eq_fallback_of_forall_le {α : Type} [LinearOrder α]
    {fallback : α} {xs : List α} :
    (∀ x ∈ xs, x ≤ fallback) → listMaxWithDefault fallback xs = fallback := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      have hx : x ≤ fallback := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≤ fallback := by
        intro y hy
        exact h y (by simp [hy])
      simp [ih hxs, max_eq_right hx]

/-- If every element of the list is at most `0`, then `listMaxWithDefault 0 xs = 0`. -/
theorem listMaxWithDefault_eq_zero_of_forall_le_zero {xs : List Nat} :
    (∀ x ∈ xs, x ≤ 0) → listMaxWithDefault 0 xs = 0 :=
  listMaxWithDefault_eq_fallback_of_forall_le

/-- If every element of the list is `0`, then `listMaxWithDefault 0 xs = 0`. -/
theorem listMaxWithDefault_eq_zero_of_all_zeros {xs : List Nat} :
    (∀ x ∈ xs, x = 0) → listMaxWithDefault 0 xs = 0 := by
  intro h
  apply listMaxWithDefault_eq_zero_of_forall_le_zero
  intro x hx
  rw [h x hx]

/-- Extracts the maximum element from a list of natural numbers and returns
it together with the list after removing the first occurrence of that maximum.
Returns `(0, [])` for an empty list. -/
def takeMax (l : List Nat) : Nat × List Nat :=
  let m := listMax l
  (m, eraseFirst m l)

/-! ## `argmax` and `reverse` -/

/-- `argmax` returns `none` on the reverse of a list iff the original list is empty. -/
lemma reverse_argmax_eq_none_iff [Preorder β] [DecidableLT β] {score : α → β}
    {xs : List α} :
    xs.reverse.argmax score = none ↔ xs = [] := by
  rw [List.argmax_eq_none]
  constructor
  · intro h; simpa using congrArg List.reverse h
  · intro h; simp [h]

end List

end Specific
