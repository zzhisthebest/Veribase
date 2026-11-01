import Mathlib
import general.List.Fold
import general.List.IndexedAccess
import general.List.Membership
import general.List.Aggregation
import general.List.Sort

namespace List

/-! # Finding elements by array lookup

This module provides utilities for finding the first element in a list
whose corresponding entry in an external `Array` satisfies a predicate.
Common in problems that precompute frequency/count arrays and then
search for the first element meeting a condition.
-/

/-- Find the first index `k ≥ i` in `lst` where `p (lookup[f x]!)` is true.
Returns `none` if no such element exists.

This generalizes `findIdxBy` to the case where the predicate depends on an
external `Array` lookup table. Common use cases:
- Finding the first character with frequency 1 in a string
- Finding the first element whose count satisfies some condition
- Any first-match search with an auxiliary array-based data structure

Example: `findFirstIdxByArray lst counts charToIdx (fun n => n = 1) 0` finds
the index of the first element in `lst` whose corresponding count is exactly 1. -/
def findFirstIdxByArray {α β : Type} [Inhabited β] (lst : List α) (lookup : Array β)
    (f : α → Nat) (p : β → Bool) (i : Nat) : Option Nat :=
  findIdxBy lst (λ x => p (lookup[f x]!)) i

/-! ### First index of an element

`firstIndexOf` returns the 0-based index of the first occurrence of `x` in `xs`,
or `0` if `x` is not found.

This is a `Nat`-returning convenience function (unlike `findIdxFrom` which returns
`Option Nat`). The `0` default for "not found" is useful in contexts where an element
not in the reference list should be treated as having position `0`, such as alien
dictionary rank comparisons.

See also `findIdxFrom` (offset-aware, `Option`-returning) and `findIdx?` (Std). -/
def firstIndexOf [DecidableEq α] (x : α) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | h :: t => if h = x then 0 else Nat.succ (firstIndexOf x t)

/-! ### `findWithDefault` — first element satisfying a `Prop` predicate

`findWithDefault p l default` returns the first element in `l` satisfying `p`,
or `default` if no element satisfies `p`.
This is a `Prop`-predicate variant of `List.find?` that returns a default value
instead of `Option α`. -/

/-- Finds the first element in `l` satisfying predicate `p`.
Returns `default` if no element satisfies `p`.
This is a variant of `List.find?` that returns a default value instead of `Option α`. -/
def findWithDefault {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | a :: as => if p a then a else findWithDefault p as default

/-- Specification for `findWithDefault`: if there exists an element in `l` satisfying `p`,
then the result is a member of `l` that satisfies `p`, and all elements before it
(according to `takeWhile`) do NOT satisfy `p`. -/
lemma findWithDefault_spec {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) (default : α)
    (hex : ∃ a ∈ l, p a) :
    findWithDefault p l default ∈ l ∧
    p (findWithDefault p l default) ∧
    (∀ a ∈ l.takeWhile (fun x => !decide (p x)), ¬ p a) := by
  induction' l with hd tl ih generalizing default
  · exfalso; rcases hex with ⟨a, ha, _⟩; exact List.not_mem_nil _ ha
  · by_cases hdp : p hd
    · have hresult : findWithDefault p (hd :: tl) default = hd := by
        dsimp [findWithDefault]; rw [if_pos hdp]
      rw [hresult]
      have htake : ∀ a ∈ (hd :: tl).takeWhile (fun x => !decide (p x)), ¬ p a := by
        intro a ha
        have hnil : (hd :: tl).takeWhile (fun x => !decide (p x)) = [] := by
          simp [hdp]
        rw [hnil] at ha
        exact absurd ha (List.not_mem_nil _)
      exact ⟨by simp, hdp, htake⟩
    · have hresult : findWithDefault p (hd :: tl) default = findWithDefault p tl default := by
        dsimp [findWithDefault]; rw [if_neg hdp]
      rw [hresult]
      have hex_tl : ∃ a ∈ tl, p a := by
        rcases hex with ⟨a, ha, hpa⟩
        cases ha with
        | head => exact absurd hpa hdp
        | tail _ ha' => exact ⟨a, ha', hpa⟩
      rcases ih default hex_tl with ⟨hmem_res, hp_res, htake_res⟩
      have hmem_total : findWithDefault p tl default ∈ hd :: tl :=
        List.mem_cons_of_mem hd hmem_res
      have htake_total : ∀ a ∈ (hd :: tl).takeWhile (fun x => !decide (p x)), ¬ p a := by
        intro a ha
        rw [List.takeWhile_cons] at ha
        simp [hdp] at ha
        rcases ha with (rfl | ha')
        · exact hdp
        · exact htake_res a ha'
      exact ⟨hmem_total, hp_res, htake_total⟩

/-! ### `findIdx?` lemmas — bridging `Option` to `Fin` -/

/-- If `findIdx?` returns `none`, then no element in the list satisfies the predicate.
This is a reformulation of `List.findIdx?_eq_none_iff` in terms of `Fin` and `get`. -/
lemma findIdx?_eq_none_imp_forall_get {α : Type _} {l : List α} {p : α → Bool}
    (h : l.findIdx? p = none) : ∀ (i : Fin l.length), p (l.get i) = false := by
  rw [List.findIdx?_eq_none_iff] at h
  intro i
  have hm : l.get i ∈ l := List.get_mem _ _
  exact h _ hm

/-- If `findIdx?` returns `some idx`, then the element at `idx` satisfies `p`,
and no earlier element does. Provides a `Fin`-based API convenient for verification proofs. -/
lemma findIdx?_eq_some_imp_exists_fin {α : Type _} {l : List α} {p : α → Bool} {idx : Nat}
    (h : l.findIdx? p = some idx) :
    (∃ (h_lt : idx < l.length),
      p (l.get ⟨idx, h_lt⟩) = true ∧
      ∀ (j : Fin idx), ¬ p (l.get (Fin.castLT j (Nat.lt_trans j.2 h_lt)))) := by
  have h_lemma := (List.findIdx?_eq_some_iff_getElem (p := p)).mp h
  rcases h_lemma with ⟨h_len, h_val, h_forall⟩
  refine ⟨h_len, h_val, λ j => ?_⟩
  have h_j_lt : (j : ℕ) < idx := j.2
  have h_not := h_forall (j : ℕ) h_j_lt
  simpa using h_not

/-- Find the first index where element satisfies `p` in list `l`.
Returns `-1 : ℤ` if no element satisfies `p`.
This is the `Int`-returning variant of `findFirstIdx` (which returns `Nat` with `0` as default). -/
def findFirstIdxAsInt {α : Type _} (p : α → Bool) (l : List α) : Int :=
  match l.findIdx? p with
  | some idx => (idx : Int)
  | none => -1

/-! ### Tail-recursive index-of with offset (returns `Int`) -/

/-- Find the first index of `target` in `l` starting from offset `i`, returning
an `Int`. Returns `-1` if `target` is not found; otherwise returns `Int.ofNat (i + j)`
where `j` is the 0-based position in `l`.

This is a tail-recursive implementation specialized to equality search, commonly
used in problems where `-1` serves as a sentinel "not found" value.

See also `findFirstIdxAsInt` (predicate-based, no offset) and `firstIndexOf`
(Nat-returning). -/
def indexOfFromAsInt {α : Type} [DecidableEq α] (l : List α) (target : α) (i : Nat) : Int :=
  match l with
  | [] => -1
  | x :: xs =>
    if x = target then Int.ofNat i
    else indexOfFromAsInt xs target (i + 1)

/-! ### `indexOfBEq` — index of first occurrence using BEq equality

This is the `BEq`-based counterpart of `firstIndexOf` (which uses `DecidableEq`).
Returns `0` if the element is not found (or is the first element), and
`Nat.succ k` if the element first appears at position `k + 1` from the head.
-/

/-- Returns the 0-based index of the first occurrence of `a` in the list,
using `BEq` equality. Returns `0` if `a` is not found (or is the first element).
For `a` found at position `k > 0`, returns `Nat.succ` applied `k` times to `0`. -/
def indexOfBEq [BEq α] (a : α) : List α → Nat
  | [] => 0
  | x :: xs => if x == a then 0 else Nat.succ (indexOfBEq a xs)

/-- `indexOfBEq a (a :: xs) = 0`: the index of the head element is 0. -/
lemma indexOfBEq_cons_self [DecidableEq α] (a : α) (xs : List α) :
    indexOfBEq a (a :: xs) = 0 := by
  simp [indexOfBEq]

/-- `indexOfBEq a (x :: xs) = Nat.succ (indexOfBEq a xs)` when `x ≠ a`. -/
lemma indexOfBEq_cons_of_ne [DecidableEq α] {a x : α} {xs : List α} (h : x ≠ a) :
    indexOfBEq a (x :: xs) = Nat.succ (indexOfBEq a xs) := by
  simp [indexOfBEq, h]

/-! ### `List.findIdx` cons lemmas -/

/-- Lemma about `List.findIdx.go` offset: `go xs (n+1) = go xs n + 1`. -/
lemma findIdx_go_succ {α : Type} (p : α → Bool) (xs : List α) (n : Nat) :
    List.findIdx.go p xs (n + 1) = List.findIdx.go p xs n + 1 := by
  induction' xs with y ys ih generalizing n
  · simp [List.findIdx.go]
  · simp [List.findIdx.go]
    by_cases h : p y
    · simp [h]
    · simp [h]; rw [ih]

/-- `List.findIdx` on a cons when the predicate is true for the head. -/
lemma findIdx_cons_of_eq {α : Type} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
    (x :: xs).findIdx p = 0 := by
  unfold List.findIdx
  simp [List.findIdx.go, h]

/-- `List.findIdx` on a cons when the predicate is false for the head. -/
lemma findIdx_cons_of_ne {α : Type} (p : α → Bool) (x : α) (xs : List α) (h : p x = false) :
    (x :: xs).findIdx p = xs.findIdx p + 1 := by
  unfold List.findIdx
  simp [List.findIdx.go, h]
  rw [findIdx_go_succ p xs 0]

/-! ### Simple lemmas about `firstIndexOf` -/

/-- `firstIndexOf x (x :: xs) = 0`: looking for the head element returns index 0. -/
lemma firstIndexOf_cons_self {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    firstIndexOf x (x :: xs) = 0 := by
  simp [firstIndexOf]

/-- If `y ≠ x`, then `firstIndexOf x (y :: xs) = Nat.succ (firstIndexOf x xs)`. -/
lemma firstIndexOf_cons_of_ne {α : Type} [DecidableEq α] (x y : α) (xs : List α) (h : y ≠ x) :
    firstIndexOf x (y :: xs) = Nat.succ (firstIndexOf x xs) := by
  simp [firstIndexOf, h]

/-- General unfolding lemma: `firstIndexOf x (a :: bs) = if a = x then 0 else Nat.succ (firstIndexOf x bs)`.
This combines `firstIndexOf_cons_self` and `firstIndexOf_cons_of_ne` into a single equation. -/
lemma firstIndexOf_cons_eq {α : Type} [DecidableEq α] {x a : α} (bs : List α) :
    firstIndexOf x (a :: bs) = if a = x then 0 else Nat.succ (firstIndexOf x bs) := by
  simp [firstIndexOf]

/-- If `x ∉ l₁`, then `firstIndexOf x (l₁ ++ l₂) = firstIndexOf x l₂ + l₁.length`.
This is useful when `x` first appears after a prefix where it is absent. -/
lemma firstIndexOf_append_eq_length_of_not_mem {α : Type} [DecidableEq α] {x : α} {l₁ l₂ : List α}
    (h : x ∉ l₁) : firstIndexOf x (l₁ ++ l₂) = firstIndexOf x l₂ + l₁.length := by
  induction' l₁ with a as ih generalizing l₂
  · simp [firstIndexOf]
  · have ha_ne : a ≠ x := by
      intro heq; subst heq; exact h (List.mem_cons_self _ _)
    have hx_not_mem : x ∉ as := by
      intro hx; exact h (List.mem_cons_of_mem _ hx)
    rw [List.cons_append]
    rw [firstIndexOf_cons_eq (bs := as ++ l₂)]
    have hif : (if a = x then 0 else Nat.succ (firstIndexOf x (as ++ l₂))) =
        Nat.succ (firstIndexOf x (as ++ l₂)) := by simp [ha_ne]
    rw [hif, ih hx_not_mem]
    simp [List.length_cons, add_comm, add_assoc]

/-- `firstIndexOf a xs ≤ firstIndexOf b xs` when `a` is the first element in `xs` satisfying `p`
and `b` is any element in `xs` satisfying `p`. This captures the "first index is minimal" property. -/
lemma firstIndexOf_le_of_find?_eq_some {α : Type} [DecidableEq α] {xs : List α} {p : α → Bool} {a : α}
    (h_find : xs.find? p = some a) {b : α} (h_mem : b ∈ xs) (h_pb : p b) :
    firstIndexOf a xs ≤ firstIndexOf b xs := by
  rcases (List.find?_eq_some_iff_append.mp h_find) with ⟨h_pa, as, bs, h_xs, h_as⟩
  subst h_xs
  have h_a_not_mem_as : a ∉ as := by
    intro hm
    have h_not_pa := h_as a hm
    -- h_not_pa : (!p a) = true, meaning p a = false
    have h_pa_false : p a = false := by
      simpa using h_not_pa
    rw [h_pa_false] at h_pa; simp at h_pa
  have h_b_not_mem_as : b ∉ as := by
    intro hm
    have h_not_pb := h_as b hm
    have h_pb_false : p b = false := by
      simpa using h_not_pb
    rw [h_pb_false] at h_pb; simp at h_pb
  rw [firstIndexOf_append_eq_length_of_not_mem h_a_not_mem_as]
  rw [firstIndexOf_cons_eq (bs := bs)]
  simp
  rw [firstIndexOf_append_eq_length_of_not_mem h_b_not_mem_as]
  rw [firstIndexOf_cons_eq (bs := bs)]
  omega

/-! ### `find?` satisfies-exists → non-none -/

/-- If there exists an element `a ∈ l` such that `p a = true`, then `List.find? p l` is not `none`.
This is the existential-bundled version of `find?_ne_none_of_mem_pred`. -/
lemma find?_ne_none_of_exists {α : Type} (p : α → Bool) (l : List α)
    (h : ∃ a ∈ l, p a = true) : List.find? p l ≠ none := by
  first
  | (solve
    | rfl
    | simp_all []
    | omega
    | aesop
    | simp_all [List.foldl, List.foldr]
    | simp_all [Nat.absDiff]
    | induction l <;> simp_all []
    | cases l <;> simp_all [])

/-- If `x ∈ xs` and `p x` holds, then `xs.find? p ≠ none`.
This is the element-wise version of `find?_ne_none_of_exists`: when you already have
a specific element that satisfies the predicate and is in the list. -/
lemma find?_ne_none_of_mem {α : Type} {xs : List α} {p : α → Bool} {x : α}
    (hx : x ∈ xs) (h_eq : p x) : xs.find? p ≠ none := by
  apply find?_ne_none_of_exists p xs
  exact ⟨x, hx, by simpa using h_eq⟩

/-! ### `findGetD` — first element satisfying a `Bool` predicate, with default -/

/-- Find the first element of `xs` satisfying `Bool` predicate `p`, returning `default` if none exists.
Equivalent to `(xs.find? p).getD default`. This is the `Bool`-predicate counterpart of
`findWithDefault` (which uses `Prop` predicates with `DecidablePred`). -/
def findGetD {α : Type} (xs : List α) (p : α → Bool) (default : α) : α :=
  match xs.find? p with
  | some x => x
  | none => default

/-- If there exists an element `a ∈ ws` such that `p a = true`, then the defaulted
result of `(ws.find? p).getD d` is in `ws`. This bridges `find?`-based search with a
default value to list membership, ensuring that `getD` preserves the "found element is
in the list" invariant.

For example, `getD_find?_mem_of_exists` is used in longest-word problems: if some word
in a sentence has length equal to `maxWordLength ws`, then `(ws.find? p).getD ""` is
guaranteed to be an actual word from the sentence. -/
lemma getD_find?_mem_of_exists {α : Type u} (ws : List α) (p : α → Bool) (d : α)
    (hex : ∃ a ∈ ws, p a = true) : (ws.find? p).getD d ∈ ws := by
  rcases hex with ⟨a, ha, hp⟩
  have h_find_ne_none : ws.find? p ≠ none := by
    intro h_eq_none
    have h_all := (List.find?_eq_none.mp h_eq_none)
    exact h_all a ha hp
  cases hopt : ws.find? p with
  | none => contradiction
  | some res =>
    have hmem : res ∈ ws := List.mem_of_find?_eq_some hopt
    simp [hopt, hmem]

/-! ### `findFirstPred` — first element satisfying a `Bool` predicate, with default

This is the explicit-recursion counterpart of `findGetD` (which uses `List.find?`).
The direct recursion gives a simpler induction structure for some proofs.
`findFirstPred p default xs = findGetD xs p default`.
-/

/-- Find the first element in `xs` satisfying `p`, or `default` if none exists.
This is the explicit-recursion counterpart of `findGetD`. -/
def findFirstPred {α : Type} (p : α → Bool) (default : α) (xs : List α) : α :=
  match xs with
  | [] => default
  | x :: rest => if p x then x else findFirstPred p default rest

/-- If there exists an element satisfying `p`, `findFirstPred` returns one in the list. -/
lemma findFirstPred_mem {α : Type} (p : α → Bool) (default : α) (xs : List α)
    (h : ∃ x ∈ xs, p x) : findFirstPred p default xs ∈ xs := by
  induction xs generalizing default with
  | nil => rcases h with ⟨x, hmem, _⟩; exact absurd hmem (List.not_mem_nil _)
  | cons x xs ih =>
    rcases h with ⟨y, hmem, hp⟩
    unfold findFirstPred
    by_cases hx : p x
    · simp [hx]
    · simp [hx]
      cases hmem with
      | head _ => exfalso; exact hx hp
      | tail _ hmemxs =>
        apply Or.inr; apply ih; exact ⟨y, hmemxs, hp⟩

/-- `findFirstPred` returns an element satisfying the predicate, if one exists. -/
lemma findFirstPred_pred {α : Type} (p : α → Bool) (default : α) (xs : List α)
    (h : ∃ x ∈ xs, p x) : p (findFirstPred p default xs) := by
  induction' xs with x xs ih generalizing default
  · rcases h with ⟨y, hmem, _⟩; exact absurd hmem (List.not_mem_nil _)
  · rcases h with ⟨y, hmem, hp⟩
    unfold findFirstPred
    by_cases hx : p x
    · simp [hx]
    · simp [hx]
      cases hmem with
      | head _ => exfalso; exact hx hp
      | tail _ hmemxs => apply ih; exact ⟨y, hmemxs, hp⟩

/-- Among elements satisfying `p`, `findFirstPred` returns the one with minimal index
(as measured by `indexOfBEq`). -/
lemma findFirstPred_minIndex {α : Type} [DecidableEq α]
    (p : α → Bool) (default : α) (xs : List α) (x : α) (hmem : x ∈ xs) (hpx : p x) :
    indexOfBEq (findFirstPred p default xs) xs ≤ indexOfBEq x xs := by
  induction' xs with y ys ih generalizing x
  · exact absurd hmem (List.not_mem_nil _)
  · cases hmem with
    | head _ =>
      unfold findFirstPred
      -- In the head case, x is unified with y, so hpx : p y
      simp [hpx, indexOfBEq_cons_self]
    | tail _ hmemys =>
      unfold findFirstPred
      by_cases hy : p y
      · simp [hy, indexOfBEq_cons_self]
      · simp [hy]
        have hy_ne_ffb : y ≠ findFirstPred p default ys := by
          intro heq
          apply hy
          have h_exists : ∃ x' ∈ ys, p x' := ⟨x, hmemys, hpx⟩
          have hpred := findFirstPred_pred p default ys h_exists
          rw [heq]; exact hpred
        have hy_ne_x : y ≠ x := by
          intro heq; apply hy; rw [heq]; exact hpx
        rw [indexOfBEq_cons_of_ne hy_ne_ffb, indexOfBEq_cons_of_ne hy_ne_x]
        exact Nat.add_le_add_right (ih x hmemys hpx) 1

/-! ### `findIdxElim` — index-based search with a default and continuation

`findIdxElim l p default f` searches `l` with predicate `p`; if found at index `i`,
returns `f i`; otherwise returns `default`.

This is the index-returning counterpart of `findGetD`: instead of returning the
found *element*, it returns the *index* mapped through a continuation function `f`,
allowing the result type `β` to differ from `α`.

The equality-search variant can be obtained as `findIdxElim l (· == x) d f`
(or `findIdxElim l (fun y => y = x) d f` when `DecidableEq α` is available).
-/

/-- Search a list with predicate `p`; if found at index `i`, return `f i`, otherwise `default`.
Generalizes `List.findIdx?` result handling to any target type `β`. -/
def findIdxElim {α β : Type} (l : List α) (p : α → Bool) (default : β) (f : Nat → β) : β :=
  Option.elim (l.findIdx? p) default f

/-! ### `findIdx?` on concatenated lists -/

/-- When looking for an element by predicate `p` in `as ++ bs`,
if `p` matches nothing in `as` and matches at index `k` in `bs`,
then the overall match is at index `as.length + k`. -/
lemma findIdx?_append_of_not_found_in_first {α : Type} [BEq α] [DecidableEq α]
    (as bs : List α) (p : α → Bool) {k : Nat}
    (h_first : as.findIdx? p = none) (h_second : bs.findIdx? p = some k) :
    (as ++ bs).findIdx? p = some (as.length + k) := by
  rw [List.findIdx?_append, h_first, h_second]
  simp [add_comm]

/-! ### `indexOfD` — `findIdx?`-based index-of with default 0

`indexOfD xs x` returns the 0-based index of the first occurrence of `x` in `xs`,
using `List.findIdx?` with a decidable equality predicate, defaulting to `0`
if `x` is not found.

This is the `findIdx?`-based variant of `firstIndexOf` (manual recursion).
Both return `0` for the head element and for "not found", but `indexOfD`
leverages the standard `findIdx?` infrastructure and its associated lemmas.
-/

/-- Computable (decidable) index-of for any type with decidable equality.
Returns the 0-based index of the first occurrence of `x` in `xs`, defaulting to `0`
if `x` is not found. -/
def indexOfD [DecidableEq α] (xs : List α) (x : α) : Nat :=
  (xs.findIdx? (fun y => decide (y = x))).getD 0

/-- Internal helper: if `findIdx?` returns `none`, no element satisfies the predicate.
Specialized to the equality predicate `fun z => decide (z = y)`. -/
lemma findIdx?_ne_none_of_mem [DecidableEq α] {y : α} {xs : List α} (hy : y ∈ xs) :
    xs.findIdx? (fun z => decide (z = y)) ≠ none := by
  by_contra h
  have heq := (List.findIdx?_eq_none_iff).mp h
  have := heq y hy
  simp at this

/-- Index of head element is 0. -/
lemma indexOfD_cons_self [DecidableEq α] (x : α) (xs : List α) : indexOfD (x :: xs) x = 0 := by
  simp [indexOfD, List.findIdx?_cons]

/-- Index of a different element `y` that is in the tail, counting past the head. -/
lemma indexOfD_cons_of_ne_mem [DecidableEq α] (x y : α) (xs : List α) (hne : x ≠ y) (hy : y ∈ xs) :
    indexOfD (x :: xs) y = indexOfD xs y + 1 := by
  unfold indexOfD
  simp [List.findIdx?_cons, hne]
  have hy_find : xs.findIdx? (fun z => decide (z = y)) ≠ none :=
    findIdx?_ne_none_of_mem hy
  cases h : xs.findIdx? (fun z => decide (z = y)) with
  | none => exact absurd h hy_find
  | some k => simp [h]

/-! ### `findIndicesOf` — all indices where an element occurs

`findIndicesOf l a` returns a list of all indices `i` (0-based) such that `l[i]? = some a`.
This is a "find-all-positions" variant of `firstIndexOf` (single position) and
`List.findIdx?` (predicate-based single position). -/

/-- Returns all indices `i` where `l[i]? = some a`.
Equivalent to `(List.range l.length).filter (λ i => l[i]? = some a)`. -/
def findIndicesOf {α : Type u} [DecidableEq α] (l : List α) (a : α) : List Nat :=
  (List.range l.length).filter (λ i => decide (l[i]? = some a))

/-- Membership in `findIndicesOf` is equivalent to `getElem?` returning `some a`.
This is the fundamental specification lemma for `findIndicesOf`. -/
lemma mem_findIndicesOf_iff {α : Type u} [DecidableEq α] {l : List α} {a : α} {i : Nat} :
    i ∈ l.findIndicesOf a ↔ l[i]? = some a := by
  constructor
  · simp [List.findIndicesOf, List.mem_filter, List.mem_range]
  · intro h
    rcases List.getElem?_eq_some_iff.mp h with ⟨h_lt, _⟩
    simp [List.findIndicesOf, List.mem_filter, List.mem_range, h_lt, h]

end List

namespace List

/-! ### Find all indices of an element -/

/-- Returns the list of indices where `x` occurs in `xs`.
    For example, `indicesOf ['a','b','a'] 'a' = [0,2]`. -/
def indicesOf {α : Type} [DecidableEq α] (xs : List α) (x : α) : List Nat :=
  (xs.zipIdx.filter (fun p => p.1 = x)).map Prod.snd


theorem indicesOf_nil {α : Type} [DecidableEq α] (x : α) : indicesOf ([] : List α) x = [] := rfl

end List

namespace List

/-! ### `findDefault` — first element satisfying a predicate, with a default -/

/-- Return the first element of `xs` satisfying `p`, or `default` if none exists.
This is a version of `List.find?` that returns the element directly rather than `Option α`. -/
def findDefault {α : Type} (p : α → Bool) (xs : List α) (default : α) : α :=
  match xs.filter p with
  | x :: _ => x
  | [] => default

/-- Return the first element of `xs` satisfying predicate `p`, or `Inhabited.default` if none match.
This is the `Inhabited`-based variant of `findDefault` (which takes an explicit default).
`firstWhere` was the original name in problem sources. -/
def firstWhere {α : Type} [Inhabited α] (p : α → Bool) (xs : List α) : α :=
  (xs.filter p).head!

end List

namespace List

/-! ### `findMinByNat` — find the minimum-scoring valid element -/

/-- Given a scoring function `f : α → Nat`, a decidable validity predicate `valid : α → Bool`,
and a list of candidates `xs : List α`, find the candidate with the minimum score
among those satisfying `valid`. Returns `none` if no candidate satisfies `valid`;
otherwise `some (x, v)` where `x` is a candidate with minimum score `v = f x`.

This function is structurally recursive on `xs`. For a version without validity filtering
that works on nonempty lists, see `argminOfCons`. -/
def findMinByNat {α : Type} (f : α → Nat) (valid : α → Bool) (xs : List α) : Option (α × Nat) :=
  match xs with
  | [] => none
  | x :: rest =>
    if valid x then
      let v := f x
      match findMinByNat f valid rest with
      | none => some (x, v)
      | some (y, w) =>
        if v ≤ w then some (x, v) else some (y, w)
    else
      findMinByNat f valid rest

/-- Specification for `findMinByNat`:
1. If it returns `none`, then no candidate in `xs` satisfies `valid`.
2. If it returns `some (x', s)`, then:
   - `x' ∈ xs` and `valid x' = true` and `f x' = s`,
   - for every `y ∈ xs` where `valid y = true`, we have `s ≤ f y`. -/
lemma findMinByNat_spec {α : Type} (f : α → Nat) (valid : α → Bool) (xs : List α) :
    (findMinByNat f valid xs = none → ∀ z ∈ xs, valid z = false) ∧
    (∀ x' s, findMinByNat f valid xs = some (x', s) →
      x' ∈ xs ∧ valid x' = true ∧ f x' = s ∧
      (∀ y ∈ xs, valid y = true → s ≤ f y)) := by
  induction xs with
  | nil =>
    constructor
    · intro h z hz; simp at hz
    · intro x s h; simp [findMinByNat] at h
  | cons hd tl ih =>
    rcases ih with ⟨ih_none, ih_some⟩
    have h_not_none_when_valid : valid hd = true → findMinByNat f valid (hd :: tl) ≠ none := by
      intro hv
      unfold findMinByNat
      simp [hv]
      cases h_rec : findMinByNat f valid tl
      · simp [h_rec]
      · rename_i p; rcases p with ⟨y, t⟩; simp [h_rec]; split <;> simp
    constructor
    · intro h y hy
      have hy_mem := List.mem_cons.mp hy
      rcases hy_mem with (h_eq | hy_rest)
      · rw [h_eq]
        cases h_val : valid hd
        · rfl
        · exfalso; exact h_not_none_when_valid h_val h
      · cases h_val : valid hd
        · unfold findMinByNat at h
          simp [h_val] at h
          exact ih_none h y hy_rest
        · exfalso; exact h_not_none_when_valid h_val h
    · intro x' s h
      unfold findMinByNat at h
      simp at h
      cases h_val : valid hd
      · simp [h_val] at h
        rcases ih_some x' s h with ⟨hx'_in, hvx', hsum, hall⟩
        refine ⟨by simp [hx'_in], hvx', hsum, ?_⟩
        intro y hy hvy
        rcases List.mem_cons.mp hy with (h_eq | hy_rest)
        · subst h_eq; rw [h_val] at hvy; simp at hvy
        · exact hall y hy_rest hvy
      · simp [h_val] at h
        cases h_rec : findMinByNat f valid tl
        · simp [h_rec] at h
          have hpair : (hd, f hd) = (x', s) := by simpa using h
          rcases Prod.mk.inj hpair with ⟨hhd_eq, hs_eq⟩
          subst hhd_eq; subst hs_eq
          refine ⟨by simp, h_val, rfl, ?_⟩
          intro y hy hvy
          rcases List.mem_cons.mp hy with (h_eq | hy_rest)
          · subst h_eq; exact le_refl (f y)
          · have hnone := ih_none h_rec y hy_rest
            rw [hnone] at hvy; simp at hvy
        · rename_i p; rcases p with ⟨y', t⟩
          simp [h_rec] at h
          split at h
          · have hle : f hd ≤ t := by assumption
            have hpair : (hd, f hd) = (x', s) := by simpa using h
            rcases Prod.mk.inj hpair with ⟨hhd_eq, hs_eq⟩
            subst hhd_eq; subst hs_eq
            refine ⟨by simp, h_val, rfl, ?_⟩
            intro y hy hvy
            rcases List.mem_cons.mp hy with (h_eq | hy_rest)
            · subst h_eq; exact le_refl (f y)
            · rcases ih_some y' t h_rec with ⟨_, _, hsum_y', hall⟩
              have ht_le : t ≤ f y := hall y hy_rest hvy
              exact Nat.le_trans hle ht_le
          · have h_not_le : ¬ f hd ≤ t := by assumption
            have hpair : (y', t) = (x', s) := by simpa using h
            rcases Prod.mk.inj hpair with ⟨hy_eq, ht_eq⟩
            subst hy_eq; subst ht_eq
            rcases ih_some y' t h_rec with ⟨hy_in, hvy_val, hsum_y', hall⟩
            refine ⟨by simp [hy_in], hvy_val, hsum_y', ?_⟩
            intro y hy hvy
            rcases List.mem_cons.mp hy with (h_eq | hy_rest)
            · subst h_eq; exact Nat.le_of_lt (Nat.lt_of_not_ge h_not_le)
            · exact hall y hy_rest hvy

end List

namespace List

/-! ### Parent-array tree: children of a node -/

/-- Returns the list of children of node `i` in a parent-array tree.
A node `j` is a child of `i` if `parents[j] = i` (cast from `Nat` to `α` via `Nat.cast`).
For example, if `parents = [-1, 0, 0, 1, 1]`, then `childrenOf parents 0 = [1, 2]`. -/
def childrenOf {α : Type} [NatCast α] [DecidableEq α] (parents : List α) (i : Nat) : List Nat :=
  positionsOf (Nat.cast i : α) parents

/-! ### `map` + `all` interaction -/

/-- **`all` distributes through `map`**: `(l.map f).all p = true` iff `∀ x ∈ l, p (f x) = true`.

This bridges the Boolean `List.all` combinator with the propositional
`∀ x ∈ l, ...` statement across a mapped list. -/
lemma map_all_eq_true_iff {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    ((l.map f).all p = true) ↔ (∀ x, x ∈ l → p (f x) = true) := by
  constructor
  · intro h x hx
    have hmem : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
    have hall := (List.all_eq_true.mp h) (f x) hmem
    simpa using hall
  · intro h
    apply List.all_eq_true.mpr
    intro d hd
    rcases List.mem_map.mp hd with ⟨x, hx, rfl⟩
    simpa using h x hx

/-! ### `all` with conditional `decide` check -/

/-- If `x ≤ y` for all `y ∈ xs` where `P y` holds, then
`xs.all (fun y => if P y then decide (x ≤ y) else true) = true`. -/
lemma all_ite_decide_le_of_forall {α : Type} [LinearOrder α] {x : α} {xs : List α} {P : α → Bool}
    (h : ∀ y ∈ xs, P y = true → x ≤ y) :
    xs.all (fun y => if P y then decide (x ≤ y) else true) = true := by
  rw [List.all_eq_true]
  intro y hy
  by_cases hPy : P y = true
  · simp [hPy, h y hy hPy]
  · simp [hPy]

/-- If a boolean predicate `p` holds for all `i < n`, then `(List.range n).all p = true`.
This combines `List.all_eq_true` with `List.mem_range`. Together with the reverse
direction (via `List.all_eq_true`), this gives the equivalence:
`(List.range n).all p = true ↔ ∀ i < n, p i = true`. -/
lemma range_all_eq_true_of_forall_lt {n : ℕ} {p : ℕ → Bool} (h : ∀ i, i < n → p i = true) :
    (List.range n).all p = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  exact h i hi

/-- Given `l.all f ≠ true`, there exists an element in `l` that does not satisfy `f`.
This bridges the gap between "`l.all f` is not true" (i.e., it's false) and the
existential provided by `List.all_eq_false.mp`. -/
lemma exists_false_of_all_ne_true {α : Type} {l : List α} {f : α → Bool}
    (h : l.all f ≠ true) : ∃ a ∈ l, f a = false := by
  have hfalse : l.all f = false := by
    simpa [Bool.not_eq_true] using h
  rcases List.all_eq_false.mp hfalse with ⟨a, ha, hfalse'⟩
  exact ⟨a, ha, by simpa using hfalse'⟩

/-- Check that a predicate holds for every prefix of `s`. -/
def allPrefixesSatisfy {α : Type} (p : List α → Bool) (s : List α) : Bool :=
  s.inits.all p

/-- Check whether every element of `l` lies in the inclusive range `[lo, hi]`.
Returns `true` for the empty list.
Example: `allBetween 1 9 [1, 5, 9] = true`, `allBetween 1 9 [1, 10, 5] = false`. -/
@[reducible]
def allBetween (lo hi : Nat) (l : List Nat) : Bool :=
  l.all (Nat.between lo hi)

/-! ### `allInRange` — Prop predicate for bounded lists

This is the `Prop` counterpart of `allBetween` (which returns `Bool`).  `allInRange`
is generalised to any `Preorder` type, while `allBetween` is `Nat`‑specific and
uses the decidable `Nat.between`. -/

/-- `allInRange lo hi l` holds when every element of `l` satisfies `lo ≤ x ∧ x ≤ hi`.
Returns `True` for the empty list.
Example: `allInRange (1 : ℕ) 9 [1, 5, 9]` holds, `allInRange (1 : ℕ) 9 [1, 10, 5]` does not. -/
def allInRange {α : Type} [Preorder α] (lo hi : α) (l : List α) : Prop :=
  ∀ x ∈ l, lo ≤ x ∧ x ≤ hi


lemma allInRange_nil {α : Type} [Preorder α] (lo hi : α) : allInRange lo hi ([] : List α) := by
  simp [allInRange]

lemma allInRange_cons {α : Type} [Preorder α] {lo hi x : α} {l : List α} :
    allInRange lo hi (x :: l) ↔ (lo ≤ x ∧ x ≤ hi) ∧ allInRange lo hi l := by
  constructor
  · intro h
    have hx : lo ≤ x ∧ x ≤ hi := h x (by simp)
    have hl : allInRange lo hi l := fun y hy => h y (by simp [hy])
    exact ⟨hx, hl⟩
  · intro ⟨⟨hlo, hhi⟩, hl⟩ y hy
    rcases List.mem_cons.mp hy with (rfl | hy')
    · exact ⟨hlo, hhi⟩
    · exact hl y hy'

/-- `isBoundedList lo hi n xs` holds when `xs` has exactly `n` elements and every
element lies in the inclusive range `[lo, hi]`.  This is a `Prop` predicate that
combines a length constraint with `allInRange`. -/
def isBoundedList (lo hi n : Nat) (xs : List Nat) : Prop :=
  xs.length = n ∧ allInRange lo hi xs

namespace isBoundedList

/-- `List.replicate n x` is a bounded list of length `n` when `x` is in `[lo, hi]`. -/
lemma replicate (lo hi n x : Nat) (hx : lo ≤ x ∧ x ≤ hi) : isBoundedList lo hi n (List.replicate n x) := by
  unfold isBoundedList allInRange
  constructor
  · exact List.length_replicate n x
  · intro y hy
    rcases List.mem_replicate.mp hy with ⟨_, hy_eq⟩
    subst hy_eq
    exact hx

end isBoundedList

/-! ### Minimal element predicate -/

/-- `minimalAmong xs x` means `x` is a member of `xs` and is ≤ every member of `xs`.
In other words, `x` is a minimal element among `xs`. -/
def minimalAmong {α : Type} [LE α] (xs : List α) (x : α) : Prop :=
  x ∈ xs ∧ ∀ y, y ∈ xs → x ≤ y

/-- A singleton list has its only element as minimal. -/
lemma minimalAmong_singleton {α : Type} [Preorder α] (x : α) : minimalAmong [x] x := by
  unfold minimalAmong; simp

/-! ### `any` negation lemma -/

/-- If there is no element in `l` satisfying `p` (i.e., `p x = true` for no `x` in `l`),
then `l.any p` is false. This is the contrapositive direction of `List.any_eq_true`. -/
lemma any_eq_false_of_not_exists {α : Type u} {p : α → Bool} {l : List α}
    (h : ¬ ∃ x, x ∈ l ∧ p x = true) : l.any p = false := by
  by_contra hne
  have htrue : l.any p = true := (Bool.eq_false_or_eq_true _).resolve_right hne
  rcases List.any_eq_true.1 htrue with ⟨x, hx, hp⟩
  exact h ⟨x, hx, hp⟩

/-- For any list and predicate, `any p = true` iff `all (¬p) = false`.
In other words, there exists an element satisfying `p` iff it is not the case
that all elements fail `p`. -/
lemma any_eq_true_iff_all_not_eq_false {α : Type _} (l : List α) (p : α → Bool) :
    l.any p = true ↔ l.all (λx => ¬p x) = false := by
  simp

/-- For any list and predicate, `any p = false` iff `all (¬p) = true`.
In other words, no element satisfies `p` iff all elements fail `p`. -/
lemma any_eq_false_iff_all_not_eq_true {α : Type _} (l : List α) (p : α → Bool) :
    l.any p = false ↔ l.all (λx => ¬p x) = true := by
  simp

/-- De Morgan law for `List.any`/`List.all` using `Bool.not` (`!`):
`!(list.any p)` equals `list.all (λ a => !p a)` at the `Bool` level. -/
lemma bnot_any_eq_all_bnot {α : Type _} (l : List α) (p : α → Bool) : (! l.any p) = l.all (fun a => ! p a) := by
  induction l with
  | nil => simp
  | cons a l' ih =>
    simp [List.any_cons, List.all_cons, ih, Bool.not_or]

/-! ### `List.find?` with uniqueness -/

/-- If `x` is the unique element of `l` satisfying the Boolean predicate `p`
(i.e., `p x = true` and `∀ y, p y → y = x`), and `x` is in `l`,
then `List.find? p l = some x`. -/
lemma find?_of_unique {α : Type} (l : List α) (p : α → Bool) (x : α) (hpx : p x)
    (h_unique : ∀ y, p y → y = x) (h_mem : x ∈ l) : List.find? p l = some x := by
  induction' l with a l ih generalizing x
  · simp at h_mem
  · simp [List.find?] at h_mem ⊢
    rcases h_mem with (h | h)
    · subst h; simp [hpx]
    · by_cases hpa : p a
      · have hax := h_unique a hpa
        subst hax; simp [hpx]
      · simp [hpa, ih x hpx h_unique h]

/-- If `List.find? p l` returns `some a`, then `a` satisfies the predicate `p`
(i.e., `p a = true`). This extracts the first conjunct of
`List.find?_eq_some_iff_append`. -/
lemma pred_of_find?_eq_some {α : Type _} {p : α → Bool} {l : List α} {a : α}
    (h : List.find? p l = some a) : p a = true := by
  rcases (List.find?_eq_some_iff_append.mp h) with ⟨hp, _, _, _, _⟩
  exact hp

/-- `xs.find? f ≠ none ↔ ∃ x, xs.find? f = some x`.
This is a convenience lemma wrapping `Option.isSome_iff_ne_none` and
`Option.isSome_iff_exists` for `List.find?` results. -/
lemma find?_ne_none_iff_exists_some {α : Type} (xs : List α) (f : α → Bool) :
    xs.find? f ≠ none ↔ ∃ x, xs.find? f = some x := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => by rw [hx]; intro h; injection h⟩
  match hres : xs.find? f with
  | none => exact absurd hres h
  | some a => exact ⟨a, rfl⟩

/-- If `List.any` returns `true` for a predicate `p`, then `List.find?` returns `some x` for
some `x`. This bridges the boolean membership check to the optional witness extraction. -/
lemma any_true_implies_find?_some {α : Type} {p : α → Bool} {l : List α}
    (h : l.any p = true) : ∃ x, l.find? p = some x := by
  rw [List.any_eq_true] at h
  rcases h with ⟨x, hx_mem, hx_p⟩
  have h_find_ne_none : l.find? p ≠ none := by
    intro h_eq
    rw [List.find?_eq_none] at h_eq
    exact h_eq x hx_mem hx_p
  rcases Option.ne_none_iff_exists.mp h_find_ne_none with ⟨x', hx'⟩
  exact ⟨x', hx'.symm⟩

/-- If `List.any` returns `false` for a predicate `p`, then `List.find?` returns `none`.
The contrapositive of `any_true_implies_find?_some`. -/
lemma any_false_implies_find?_none {α : Type} {p : α → Bool} {l : List α}
    (h : l.any p = false) : l.find? p = none := by
  rw [List.any_eq_false] at h
  rw [List.find?_eq_none.mpr]
  exact h

/-- If `find?` on a list of pairs returns `some (a, b)` when looking for `p.1 == k`,
then `a = k` (by `LawfulBEq`) and the pair is a member of the list.
Useful for dictionary-style lookups on association lists. -/
lemma find?_pair_fst_eq {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k a : α) (b : β)
    (h : l.find? (fun p => p.1 == k) = some (a, b)) : a = k ∧ (a, b) ∈ l := by
  have h_props := List.find?_eq_some_iff_append.mp h
  have ha_eq_k : a = k := eq_of_beq (by simpa using h_props.1)
  have h_mem : (a, b) ∈ l := by
    rcases h_props.2 with ⟨as, bs, h_eq_list, _⟩
    rw [h_eq_list]
    apply List.mem_append_right
    simp
  exact ⟨ha_eq_k, h_mem⟩

/-- If an element `x` is in `l` and satisfies the predicate `p`,
then `l.find? p` is not `none`. This is a direct consequence of
`List.find?_eq_none`. -/
lemma find?_ne_none_of_mem_pred {α : Type} (p : α → Bool) (l : List α) (x : α)
    (h_mem : x ∈ l) (h_pred : p x = true) : l.find? p ≠ none := by
  intro h_none
  have h_false := List.find?_eq_none.mp h_none x h_mem
  rw [h_pred] at h_false
  exact h_false rfl

/-- If `List.find? p l` is not `none`, then `List.find? p l.reverse` is also not `none`.
This follows from the fact that `l.reverse` contains exactly the same elements as `l`. -/
lemma find?_reverse_ne_none {α : Type} {p : α → Bool} {l : List α}
    (h : List.find? p l ≠ none) : List.find? p l.reverse ≠ none := by
  intro hreverse
  apply h
  rw [List.find?_eq_none]
  have hrev := (List.find?_eq_none (p := p) (l := l.reverse)).mp hreverse
  intro x hx
  apply hrev x
  rw [List.mem_reverse]
  exact hx

/-! ### Pairwise boolean check across two lists -/

/-- Check whether there exists a pair `(a, b)` with `a ∈ l₁`, `b ∈ l₂` such that `f a b` is true. -/
def anyPair {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Bool) : Bool :=
  l₁.any (λ a => l₂.any (λ b => f a b))

/-- Nested `List.any` on two lists is equivalent to the existence of a pair
whose combined boolean predicate is true. This factors the common pattern of checking
all pairs across two lists. -/
lemma anyPair_eq_true_iff {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Bool) :
    anyPair l₁ l₂ f = true ↔ ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ f a b = true := by
  constructor
  · intro h
    unfold anyPair at h
    rw [List.any_eq_true] at h
    rcases h with ⟨a, ha_mem, h_any⟩
    rw [List.any_eq_true] at h_any
    rcases h_any with ⟨b, hb_mem, h_eq⟩
    exact ⟨a, b, ha_mem, hb_mem, h_eq⟩
  · intro h
    rcases h with ⟨a, b, ha_mem, hb_mem, h_eq⟩
    unfold anyPair
    rw [List.any_eq_true]
    refine ⟨a, ha_mem, ?_⟩
    rw [List.any_eq_true]
    refine ⟨b, hb_mem, h_eq⟩

/-! ### `allAny` — forall-exists pattern on two lists -/

/-- Returns true if every `a` in `as` has some `b` in `bs` satisfying `R a b`.
This is the "forall-exists" pattern on lists, as a decidable predicate.
`allAny as bs R` is the ∀-∃ counterpart of `anyPair` (which is ∃-∃).

`allSatisfySome` was the original name in problem sources. -/
def allAny {α β : Type} (as : List α) (bs : List β) (R : α → β → Bool) : Bool :=
  as.all (fun a => bs.any (R a))

/-- `allAny as bs R = true` iff for every `a ∈ as`, there exists `b ∈ bs` such that `R a b = true`. -/
lemma allAny_eq_true_iff {α β : Type} (as : List α) (bs : List β) (R : α → β → Bool) :
    allAny as bs R = true ↔ ∀ a, a ∈ as → ∃ b, b ∈ bs ∧ R a b = true := by
  constructor
  · intro h a ha
    unfold allAny at h
    rw [List.all_eq_true] at h
    rcases h a ha with (h_any : bs.any (R a) = true)
    rw [List.any_eq_true] at h_any
    rcases h_any with ⟨b, hb, hR⟩
    exact ⟨b, hb, hR⟩
  · intro h
    unfold allAny
    rw [List.all_eq_true]
    intro a ha
    rcases h a ha with ⟨b, hb, hR⟩
    rw [List.any_eq_true]
    exact ⟨b, hb, hR⟩

/-! ### Pairwise boolean check over `List.range` with distinct indices -/

/-- Double-nested `List.any` over `List.range` with a distinct-index condition
is equivalent to the existence of distinct indices `i`, `j` (both `< n`)
such that the predicate `P i j` holds.

This abstracts the core combinatorial search pattern:
"does any pair of distinct indices (from 0 to n-1) satisfy a boolean predicate `P`?" -/
theorem any_range_pair_iff {n : Nat} {P : Nat → Nat → Bool} :
    ((List.range n).any (λ i => (List.range n).any (λ j => i != j && P i j)) = true) ↔
    (∃ i < n, ∃ j < n, i ≠ j ∧ P i j = true) := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    rcases h with ⟨i, hi_range, hi_inner⟩
    rw [List.any_eq_true] at hi_inner
    rcases hi_inner with ⟨j, hj_range, hj_pair⟩
    rw [List.mem_range] at hi_range hj_range
    rw [Bool.and_eq_true] at hj_pair
    rcases hj_pair with ⟨hne_val, heq_val⟩
    have hne : i ≠ j := bne_iff_ne.mp hne_val
    exact ⟨i, hi_range, j, hj_range, hne, heq_val⟩
  · intro h
    rcases h with ⟨i, hi, j, hj, hne, heq⟩
    rw [List.any_eq_true]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨bne_iff_ne.mpr hne, heq⟩

end List


namespace List

/-! ### Greedy match: count consecutive pairs satisfying `bs[i] ≤ ms[i]` -/

/-- `greedyMatch bs ms` counts how many consecutive pairs from the start of `bs` and `ms`
satisfy `bs[i] ≤ ms[i]`, stopping at the first violation. This is useful for greedy
matching problems where two sorted lists are paired element-by-element until the
condition fails.

Returns `0` if either list is empty. -/
def greedyMatch (bs ms : List Nat) : Nat :=
  match bs, ms with
  | b :: bs', m :: ms' =>
    if b ≤ m then 1 + greedyMatch bs' ms' else 0
  | _, _ => 0

/-- `greedyMatch` never exceeds the length of either input list. -/
lemma greedyMatch_le_lengths (bs ms : List Nat) :
    greedyMatch bs ms ≤ bs.length ∧ greedyMatch bs ms ≤ ms.length := by
  induction bs generalizing ms with
  | nil => simp [greedyMatch]
  | cons b bs' ih =>
    cases ms with
    | nil => simp [greedyMatch]
    | cons m ms' =>
      simp [greedyMatch]
      split <;> rename_i hle
      · have ⟨h1, h2⟩ := ih ms'
        constructor
        · omega
        · omega
      · constructor <;> omega

/-- `greedyMatch bs ms` is at most the length of `bs`. -/
lemma greedyMatch_le_bs_length (bs ms : List Nat) : greedyMatch bs ms ≤ bs.length :=
  (greedyMatch_le_lengths bs ms).1

/-- `greedyMatch bs ms` is at most the length of `ms`. -/
lemma greedyMatch_le_ms_length (bs ms : List Nat) : greedyMatch bs ms ≤ ms.length :=
  (greedyMatch_le_lengths bs ms).2

/-- Specification of `greedyMatch`: for all `i < greedyMatch bs ms`,
`(bs[i]?).getD 0 ≤ (ms[i]?).getD 0`. In other words, every pair counted by `greedyMatch`
satisfies the element-wise comparison. -/
lemma greedyMatch_spec (bs ms : List Nat) (i : Nat) (hi : i < greedyMatch bs ms) :
    (bs[i]?).getD 0 ≤ (ms[i]?).getD 0 := by
  induction bs generalizing ms i with
  | nil => simp [greedyMatch] at hi
  | cons b bs' ih =>
    cases ms with
    | nil => simp [greedyMatch] at hi
    | cons m ms' =>
      simp [greedyMatch] at hi
      split at hi <;> rename_i hle
      · cases i with
        | zero => simp [hle]
        | succ i' =>
          simp
          apply ih ms' i'
          omega
      · omega

/-- Maximality of `greedyMatch`: if `m` elements satisfy the pairwise condition
in the first `m` positions, then `greedyMatch` finds at least `m` of them.
This is the key theorem establishing that `greedyMatch` is optimal:
no algorithm can find more consecutive matching pairs. -/
lemma greedyMatch_max (bs ms : List Nat) (m : Nat)
    (hmb : m ≤ bs.length) (hmm : m ≤ ms.length)
    (h : ∀ i, i < m → (bs[i]?).getD 0 ≤ (ms[i]?).getD 0) : m ≤ greedyMatch bs ms := by
  induction' m with k ih generalizing bs ms
  · exact Nat.zero_le _
  · cases bs with
    | nil => simp at hmb
    | cons b bs' =>
      cases ms with
      | nil => simp at hmm
      | cons m ms' =>
        have hmb' : k ≤ bs'.length := by
          simp at hmb; omega
        have hmm' : k ≤ ms'.length := by
          simp at hmm; omega
        have h0 : ((b :: bs')[0]?).getD 0 ≤ ((m :: ms')[0]?).getD 0 := h 0 (by omega)
        simp at h0
        have h' : ∀ i, i < k → (bs'[i]?).getD 0 ≤ (ms'[i]?).getD 0 := by
          intro i hi
          have hi' : i + 1 < k + 1 := by omega
          have hfull := h (i + 1) hi'
          simpa using hfull
        have hk := ih bs' ms' hmb' hmm' h'
        simp [greedyMatch]
        rw [if_pos h0]
        omega

/-! ### `greedyMatchLength` — subsequence prefix match length -/

/-- `greedyMatchLength s t` counts how many leading elements of `s` can be matched
in order within `t` (possibly non-contiguously), using a greedy left-to-right scan
that skips mismatched elements in `t`.

This is the length of the longest prefix of `s` that is a subsequence of `t`.
Contrast with `isSubseq` (which is a boolean check) and `greedyMatch` (which
checks element-wise `≤` on consecutive pairs in two `List Nat` simultaneously). -/
def greedyMatchLength {α : Type} [DecidableEq α] : List α → List α → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs =>
    if a = b then
      1 + greedyMatchLength as bs
    else
      greedyMatchLength as (b :: bs)

/-- The greedy match length never exceeds the length of the target list `t`. -/
lemma greedyMatchLength_le_length {α : Type} [DecidableEq α] (s t : List α) :
    greedyMatchLength s t ≤ t.length := by
  induction s generalizing t with
  | nil => simp [greedyMatchLength]
  | cons a as ih =>
    cases t with
    | nil => simp [greedyMatchLength]
    | cons b bs =>
      simp [greedyMatchLength]
      split
      · have h := ih bs
        omega
      · have h := ih (b :: bs)
        exact h

end List
