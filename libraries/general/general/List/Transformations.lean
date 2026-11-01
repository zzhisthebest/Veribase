import Mathlib
import general.Common.Order
import general.List.Range
import general.List.Slicing
import general.Nat.Distances

namespace List

/-! ### Interleave two lists -/

/-- Interleave two lists element by element:
    `interleave [a1,a2,...] [b1,b2,...] = [a1,b1,a2,b2,...]`
    If one list is shorter than the other, the remaining elements of the longer
    list are appended at the end. -/
def interleave : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => x :: y :: interleave xs ys

/-- The length of `interleave xs ys` is `xs.length + ys.length`. -/
lemma length_interleave (xs ys : List α) : (interleave xs ys).length = xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [interleave]
  | cons x xs ih =>
    cases ys with
    | nil => simp [interleave]
    | cons y ys =>
      simp [interleave, ih]
      omega

end List

namespace List

/-! ### `replaceOnPredicate` — conditional element-wise replacement

For each element in `chars`, if it satisfies predicate `p`, replace it with the
corresponding element from `replacements`. Non-matching elements are kept as-is.
`replacements` should have at least as many elements as there are matching
elements in `chars`.

This is used in parallel replacement scenarios where a separate list provides the
replacement values, e.g., replacing vowels with reversed vowels in a string. -/

/-- For each element in `chars`, if it satisfies predicate `p`, replace it with
the corresponding element from `replacements`. Non-matching elements are kept as-is.
`replacements` should have at least as many elements as there are matching
elements in `chars`. -/
def replaceOnPredicate (p : α → Bool) (chars replacements : List α) : List α :=
  match chars with
  | [] => []
  | c :: cs =>
    if p c then
      match replacements with
      | [] => c :: replaceOnPredicate p cs []
      | r :: rs => r :: replaceOnPredicate p cs rs
    else
      c :: replaceOnPredicate p cs replacements

/-- `replaceOnPredicate` preserves the length of the input list. -/

lemma replaceOnPredicate_length (p : α → Bool) (chars replacements : List α) :
    (replaceOnPredicate p chars replacements).length = chars.length := by
  induction chars generalizing replacements with
  | nil => rfl
  | cons c cs ih =>
    unfold replaceOnPredicate
    split
    · rename_i h
      split
      · simp [ih]
      · rename_i r rs
        simp [ih]
    · simp [ih]

/-- If all replacements satisfy `p`, then filtering the result of
`replaceOnPredicate` by `¬ p` gives exactly the elements of `chars` that
do not satisfy `p`. In other words, `replaceOnPredicate` leaves non-matching
elements untouched, and filtering for `¬ p` recovers them.

This is the complement of `filter_replaceOnPredicate_eq`: together they say
that `replaceOnPredicate` partitions its output into replaced elements
(`p`-satisfying, drawn from `replacements`) and preserved elements
(`¬ p`-satisfying, kept from `chars`). -/
lemma filter_not_replaceOnPredicate_eq
    (p : α → Bool)
    (chars replacements : List α)
    (h_all : ∀ r ∈ replacements, p r) :
    List.filter (λ c => ¬ p c) (replaceOnPredicate p chars replacements) =
    List.filter (λ c => ¬ p c) chars := by
  induction chars generalizing replacements with
  | nil => rfl
  | cons c cs ih =>
    unfold replaceOnPredicate
    by_cases hc : p c
    · simp [hc]
      cases replacements with
      | nil =>
        simpa [hc] using ih [] (by intro r hr; exact nomatch hr)
      | cons r rs =>
        have hr_p : p r := h_all r (by simp)
        simp [hr_p]
        simpa [hc] using ih rs (fun x hx => h_all x (List.mem_cons_of_mem r hx))
    · simp [hc]
      simpa [hc] using ih replacements h_all

/-- If all replacements satisfy `p` and there are exactly as many replacements as
elements in `chars` that satisfy `p`, then filtering the result by `p` gives
exactly the list of replacements.

In other words, the replacement elements are precisely the elements in the
output that satisfy the predicate. -/
lemma filter_replaceOnPredicate_eq
    (p : α → Bool)
    (chars replacements : List α)
    (h_all : ∀ r ∈ replacements, p r)
    (h_len : replacements.length = (List.filter p chars).length) :
    List.filter p (replaceOnPredicate p chars replacements) = replacements := by
  revert replacements
  induction chars with
  | nil =>
    intro replacements h_all h_len
    simp [replaceOnPredicate]
    have hv_empty : replacements = [] := by
      simpa using h_len
    simp [hv_empty]
  | cons c cs ih =>
    intro replacements h_all h_len
    unfold replaceOnPredicate
    by_cases hc : p c
    · simp [hc]
      have hv_nonempty : replacements ≠ [] := by
        intro h_empty
        rw [h_empty] at h_len
        simp [hc] at h_len
      cases replacements with
      | nil => exact absurd rfl hv_nonempty
      | cons r rs =>
        simp
        have hr_p : p r := h_all r (by simp)
        simp [hr_p]
        apply ih rs
        · intro x hx
          apply h_all x
          simp [hx]
        · have : (r :: rs).length = (List.filter p (c :: cs)).length := h_len
          simp [hc] at this
          simpa using this
    · simp [hc]
      apply ih replacements h_all
      simpa [hc] using h_len

end List

namespace List

/-! ### `replaceAll` — replace all occurrences of an element in a list -/

/-- Replace all occurrences of `old` with `new` in a list.
Uses `map` with a conditional: `replaceAll [a,b,a,c] a d = [d,b,d,c]`. -/
def replaceAll {α : Type u} [DecidableEq α] (l : List α) (old new : α) : List α :=
  l.map (fun x => if x = old then new else x)

/-- `replaceAll` preserves the length of the list. -/

lemma replaceAll_length {α : Type u} [DecidableEq α] (l : List α) (old new : α) :
    (replaceAll l old new).length = l.length := by
  simp [replaceAll]

end List

/-!
# `removeFirst` — remove the first list element satisfying a predicate

Utilities for removing the first element of a list that satisfies a boolean predicate.
Returns `none` if no element satisfies the predicate, or `some rest` where `rest` is the
list with the first matching element removed.
-/

namespace Option

/-- Cons an element onto the front of an optional list. `optionCons x` is equivalent to
`Option.map (List.cons x)`. -/
def optionCons {α : Type u} (x : α) : Option (List α) → Option (List α)
  | none => none
  | some xs => some (x :: xs)

end Option

namespace List

/-- Remove the first element of a list satisfying a boolean predicate.
Returns `none` if no element satisfies the predicate, or `some rest` where `rest`
is the list with the first matching element removed. -/
def removeFirst {α : Type u} (p : α → Bool) : List α → Option (List α)
  | [] => none
  | x :: xs => if p x then some xs else Option.optionCons x (removeFirst p xs)


theorem removeFirst_nil {α : Type u} (p : α → Bool) : removeFirst p [] = none := rfl

theorem removeFirst_cons_of_pred {α : Type u} (p : α → Bool) (x : α) (xs : List α) (h : p x = true) :
    removeFirst p (x :: xs) = some xs := by
  simp [removeFirst, h]

/-! ### `eraseFirst` — remove the first occurrence of a specific element

Unlike `removeFirst` (which takes a `Bool` predicate and returns `Option (List α)`),
`eraseFirst` uses `DecidableEq` to match a specific value and returns `List α` directly.
If the element is not found, the list is returned unchanged. -/

/-- Remove the first occurrence of `s` from `l` using `=` equality.
Returns the list unchanged if `s` is not in `l`. -/
def eraseFirst {α : Type} [DecidableEq α] (s : α) (l : List α) : List α :=
  match l with
  | [] => []
  | h :: t => if h = s then t else h :: eraseFirst s t


theorem eraseFirst_nil {α : Type} [DecidableEq α] (s : α) : eraseFirst s [] = [] := rfl

theorem eraseFirst_cons_eq {α : Type} [DecidableEq α] (s : α) (t : List α) :
    eraseFirst s (s :: t) = t := by
  simp [eraseFirst]

theorem eraseFirst_cons_ne {α : Type} [DecidableEq α] {s h : α} (hne : h ≠ s) (t : List α) :
    eraseFirst s (h :: t) = h :: eraseFirst s t := by
  simp [eraseFirst, hne]

end List


/-! ### `AppendMonoid` — associative append with identity -/

/-- A typeclass for types with an associative `Append` operation and an identity element
`empty`. This generalizes `String` concatenation and `List α` concatenation.
For `String`: `++` is string concatenation, `empty` is `""`.
For `List α`: `++` is list concatenation, `empty` is `[]`. -/
class AppendMonoid (α : Type) extends Append α where
  empty : α
  append_assoc (a b c : α) : (a ++ b) ++ c = a ++ (b ++ c)
  empty_append (a : α) : empty ++ a = a
  append_empty (a : α) : a ++ empty = a

instance stringAppendMonoid : AppendMonoid String where
  empty := ""
  append_assoc := String.append_assoc
  empty_append := String.empty_append
  append_empty := String.append_empty

instance listAppendMonoid {α : Type} : AppendMonoid (List α) where
  empty := []
  append_assoc := List.append_assoc
  empty_append := List.nil_append
  append_empty := List.append_nil

namespace List

/-! ### `foldl` with append over an `AppendMonoid` -/

/-- `List.foldl (· ++ ·) a xs = a ++ List.foldl (· ++ ·) AppendMonoid.empty xs`
for any `AppendMonoid α`. The initial accumulator factors out as a prefix.
This generalizes `String.foldl_append_acc` (in `general/String.lean`) to all
`AppendMonoid` types. -/
lemma foldl_append_init {α : Type} [AppendMonoid α] (a : α) (xs : List α) :
    List.foldl (· ++ ·) a xs = a ++ List.foldl (· ++ ·) AppendMonoid.empty xs := by
  calc
    List.foldl (· ++ ·) a xs
        = List.foldl (· ++ ·) (a ++ AppendMonoid.empty) xs := by simp [AppendMonoid.append_empty]
    _ = (a ++ ·) (List.foldl (· ++ ·) AppendMonoid.empty xs) := by
      apply List.foldl_hom (a ++ ·) (· ++ ·) (· ++ ·) xs AppendMonoid.empty
      intro x y
      simp [AppendMonoid.append_assoc]
    _ = a ++ List.foldl (· ++ ·) AppendMonoid.empty xs := rfl

/-! ### Membership in `foldl` with append -/

/-- A character belongs to the result of folding `λ acc w => acc ++ f w` over `l`
if and only if it belongs to `f w` for some `w ∈ l`. -/
theorem mem_foldl_append_iff {α β : Type} (f : β → List α) (l : List β) (c : α) :
    c ∈ List.foldl (fun acc w => acc ++ f w) [] l ↔ ∃ w ∈ l, c ∈ f w := by
  induction' l with w ws ih
  · simp
  · simp [List.foldl_cons, ih]

/-- A generalization of `mem_foldl_append_iff` that works with an arbitrary initial
accumulator `init` (instead of only `[]`). If `x` appears in the result of folding
`λ acc a => acc ++ f a` with initial accumulator `init` over list `l`, then either
`x` was already in `init` or `x` belongs to `f a` for some `a ∈ l`. -/
lemma mem_foldl_concat {α β : Type} (l : List α) (f : α → List β) (init : List β) (x : β) :
    x ∈ l.foldl (fun acc a => acc ++ f a) init → x ∈ init ∨ ∃ a, a ∈ l ∧ x ∈ f a := by
  induction' l with a l' IH generalizing init
  · simp
  · intro h
    simp only [List.foldl_cons] at h
    have h_ih := IH (init ++ f a) h
    rcases h_ih with (hx_init | ⟨a', ha'_mem, hx_fa⟩)
    · rw [List.mem_append] at hx_init
      rcases hx_init with (hx_init' | hx_fa')
      · exact Or.inl hx_init'
      · exact Or.inr ⟨a, by simp, hx_fa'⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha'_mem, hx_fa⟩

/-! ### `foldl` preserves membership when the binary function preserves it -/

/-- If a binary function returns an element of `l` whenever both arguments are
    in `l`, then `foldl` of that function preserves membership in `l`. -/
lemma foldl_mem_of_binary_mem {α : Type u} (f : α → α → α) (l : List α)
    (h_mem : ∀ a b, a ∈ l → b ∈ l → f a b ∈ l)
    (init : α) (rest : List α) (hinit : init ∈ l) (hrest : ∀ x ∈ rest, x ∈ l) :
    List.foldl f init rest ∈ l := by
  induction rest generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    have h_foldl : List.foldl f init (x :: xs) = List.foldl f (f init x) xs := rfl
    rw [h_foldl]
    apply ih
    · apply h_mem init x hinit (hrest x (by simp))
    · intro y hy
      apply hrest y
      simp [hy]

/-! ### `foldl` distributes over `flatMap` -/

/-- `foldl` distributes over `flatMap`: folding over the flattened result equals
    folding the inner folds over the outer list. -/
lemma foldl_flatMap {α β γ : Type} (f : α → β → α) (init : α) (l : List γ) (g : γ → List β) :
    ((l.flatMap g).foldl f init) = l.foldl (fun acc x => (g x).foldl f acc) init := by
  rw [List.flatMap, List.foldl_flatten, List.foldl_map]

/-! ### `flatMap` as `foldr`/`++` -/

/-- `List.flatMap` of a function over a list equals the `foldr`/`++` expansion. -/
lemma flatMap_eq_foldr_append {α β : Type u} (xs : List α) (f : α → List β) :
    xs.flatMap f = xs.foldr (fun x acc => f x ++ acc) [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap, List.foldr, ih]

end List

namespace List

/-! ### Append equality from length equality -/

/-- If `a ++ b = c ++ d` and `a.length = c.length`, then `a = c` and `b = d`.
This decomposes a concatenation equality when the prefix lengths match. -/
lemma eq_of_append_eq_of_length_eq {α : Type} {a b c d : List α}
    (h : a ++ b = c ++ d) (h_len : a.length = c.length) : a = c ∧ b = d := by
  have h_take : a = c := by
    have := congrArg (fun xs => xs.take a.length) h
    simp [h_len] at this
    exact this
  have h_drop : b = d := by
    have := congrArg (fun xs => xs.drop a.length) h
    simp [h_len] at this
    exact this
  exact ⟨h_take, h_drop⟩

end List

namespace List

/-! ### `head!` with append -/

/-- If a nonempty list has an element appended (as a singleton), the `head!` of the
extended list equals the `head!` of the original list. -/
lemma head_append_singleton_of_ne_nil {α : Type _} [Inhabited α] {l : List α} {x : α} (h : l ≠ []) :
    (l ++ [x]).head! = l.head! := by
  cases l
  · contradiction
  · simp

end List


/-! ### `mapWith` — map with a fixed second argument

`mapWith f xs a` applies the binary function `f` to each element of `xs`, using `a` as
the fixed second argument. This is equivalent to `xs.map (fun x => f x a)`, extracted
as a reusable combinator for problems where each element is transformed relative to
an aggregate (sum, max, product, etc.) of the entire list.
-/

namespace List

variable {α γ β : Type}

/-- Map each element of a list through a binary function, pairing it with a fixed
parameter `a`. Equivalent to `xs.map (fun x => f x a)`. -/
def mapWith (f : α → γ → β) (xs : List α) (a : γ) : List β :=
  xs.map (fun x => f x a)

/-- `mapWith` preserves the length of the list. -/
lemma mapWith_length (f : α → γ → β) (xs : List α) (a : γ) :
    (mapWith f xs a).length = xs.length := by
  simp [mapWith]

/-- The element at index `i` (using `!` notation) of a `mapWith` is obtained by
applying `f` to the corresponding element of the original list and the fixed
parameter `a`. Requires `i < xs.length` to stay in bounds. -/
lemma mapWith_getElem! [Inhabited α] [Inhabited β] (f : α → γ → β) (xs : List α) (a : γ)
    (i : Nat) (hi : i < xs.length) : (mapWith f xs a)[i]! = f xs[i]! a := by
  unfold mapWith
  have hi_map : i < (xs.map (fun x => f x a)).length := by
    simpa [List.length_map] using hi
  simp [hi, hi_map, List.getElem_map]

end List

namespace List

/-! ### `mapWithRest` — map with the rest of the list (suffix) -/

/-- `mapWithRest f as` maps each element `x` of `as` using `f x xs` where `xs` is the suffix
of `as` after `x`. More precisely, for `as = [a₀, a₁, ..., aₙ₋₁]`, the result is
`[f a₀ [a₁,...,aₙ₋₁], f a₁ [a₂,...,aₙ₋₁], ..., f aₙ₋₁ []]`. -/
def mapWithRest (f : α → List α → β) : List α → List β
  | [] => []
  | x :: xs => f x xs :: mapWithRest f xs

/-- `mapWithRest` preserves the length of the list. -/
lemma mapWithRest_length (f : α → List α → β) (as : List α) :
    (mapWithRest f as).length = as.length := by
  induction as with
  | nil => rfl
  | cons _ _ ih => simp [mapWithRest, ih]

/-- The i-th element of `mapWithRest f as` (where i < as.length) equals `f as[i] (as.drop (i+1))`. -/
lemma mapWithRest_getElem?_eq (f : α → List α → β) (as : List α) (i : Nat) (h : i < as.length) :
    (mapWithRest f as)[i]? = some (f as[i] (as.drop (i + 1))) := by
  revert i
  induction as with
  | nil =>
    intro i h
    exfalso; exact Nat.not_lt_zero _ h
  | cons x xs ih =>
    intro i h
    have hlen : i < (x :: xs).length := h
    simp [List.length_cons] at hlen
    match i with
    | 0 =>
      simp [mapWithRest]
    | i+1 =>
      have hi : i < xs.length := by
        simpa [List.length_cons] using hlen
      simp [mapWithRest]
      simpa using ih i hi

/-- Variant of `mapWithRest_getElem?_eq` using `Option.map`:
`(mapWithRest f as)[i]? = as[i]?.map (fun a => f a (as.drop (i+1)))`. -/
lemma mapWithRest_getElem?_eq_map (f : α → List α → β) (as : List α) (i : Nat) (h : i < as.length) :
    (mapWithRest f as)[i]? = as[i]?.map (fun a => f a (as.drop (i + 1))) := by
  rw [mapWithRest_getElem?_eq f as i h]
  have hget : as[i]? = some as[i] := by
    simp [List.getElem?_eq_getElem h]
  simp [hget]

end List

namespace List

/-- Map with index starting from a given offset `start`.
`mapIdxFrom f start [a₀, a₁, ...] = [f start a₀, f (start+1) a₁, ...]`.
Equivalent to `mapIdx (fun i a => f (start + i) a)`. -/
def mapIdxFrom (f : Nat → α → β) (start : Nat) (as : List α) : List β :=
  match as with
  | [] => []
  | a :: as' => f start a :: mapIdxFrom f (start + 1) as'


lemma mapIdxFrom_length (f : Nat → α → β) (start : Nat) (as : List α) :
    (mapIdxFrom f start as).length = as.length := by
  induction as generalizing start with
  | nil => rfl
  | cons a as' ih =>
    simp [mapIdxFrom, ih]

/-- `mapIdxFrom` preserves element values by shifted index:
`(mapIdxFrom f start as)[i]! = f (start + i) (as[i]!)` when `i` is in bounds. -/
lemma mapIdxFrom_getElem!_of_lt (f : Nat → α → β) (start i : Nat) (as : List α) (hi : i < as.length)
    [Inhabited α] [Inhabited β] :
    (mapIdxFrom f start as)[i]! = f (start + i) (as[i]!) := by
  induction as generalizing start i with
  | nil => simp at hi
  | cons a as ih =>
    rcases i with (rfl | i)
    · simp [mapIdxFrom]
    · have hi' : i < as.length := by
        simpa using hi
      have hL : (f start a :: mapIdxFrom f (start + 1) as)[i+1]! = (mapIdxFrom f (start + 1) as)[i]! := by
        simp
      have hR : (a :: as)[i+1]! = as[i]! := by
        simp
      rw [mapIdxFrom, hL, hR, ih (start + 1) i hi']
      have h_eq : (start + 1) + i = start + (i + 1) := by omega
      rw [h_eq]

/-! ### `getD` on `mapIdx` with conditional replacement -/

/-- When the index is within bounds, `getD` on a `mapIdx` with conditional replacement
distributes the conditional: if `P i` holds, the value is `g i`; otherwise it's the
original list's value at `i` (via `getD`).

This is useful when `mapIdx` is used to selectively replace elements by index
in a list. -/
lemma getD_mapIdx_ite {α : Type} (l : List α) (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → α) (i : ℕ) (d : α) (h : i < l.length) :
    (l.mapIdx (λ i x => if P i then g i else x)).getD i d =
    if P i then g i else l.getD i d := by
  have hlen : i < (l.mapIdx (λ i x => if P i then g i else x)).length := by
    rw [List.length_mapIdx]
    exact h
  rw [List.getD_eq_getElem (l.mapIdx (λ i x => if P i then g i else x)) d hlen]
  rw [List.getElem_mapIdx]
  rw [List.getD_eq_getElem l d h]

end List

namespace List

/-! ### `mapAccum` — map with threaded state -/

/-- `mapAccum f s as` transforms each element `a` of `as` using a stateful
    function `f : σ → α → σ × β`, threading the updated state through.
    Returns the list of `β` values (the final state is discarded).
    This is like `List.map` with an accumulator, generalizing patterns such as
    `scanl`-like computations where each output depends on accumulated state.

    The state is threaded left-to-right: `f` receives the current state and the
    current element, and returns the new state together with the mapped value. -/
def mapAccum {α β σ : Type} (f : σ → α → σ × β) : σ → List α → List β
  | _, [] => []
  | s, a :: as =>
    (f s a).2 :: mapAccum f (f s a).1 as


lemma mapAccum_length {α β σ : Type} (f : σ → α → σ × β) (s : σ) (as : List α) :
    (mapAccum f s as).length = as.length := by
  revert s
  induction' as with a as ih
  · intro s; rfl
  · intro s
    simp [mapAccum]
    apply ih

/-! ### `mapAccumOption` — map with threaded state, collecting only `some` outputs -/

/-- Thread state through a list, collecting only `some` outputs.
`f` takes an element and the current state, returning a new state and an
optional output. Only `some` values are collected into the result list;
`none` outputs are dropped. This is a map-filter performed in a single pass
while threading state, useful for parsing pipelines, stateful filtering, and
command processing where each step may or may not produce output.

Contrast with `mapAccum`, which always produces one output per input element
and preserves list length. -/
def mapAccumOption {α β σ : Type} (f : α → σ → σ × Option β) : List α → σ → List β
  | [], _ => []
  | x :: xs, s =>
    let (s', out?) := f x s
    match out? with
    | none => mapAccumOption f xs s'
    | some y => y :: mapAccumOption f xs s'

/-- Congruence lemma for `mapAccumOption`: if two state-transformer functions are
pointwise equal, then `mapAccumOption` yields the same results for both. -/
lemma mapAccumOption_congr {α β σ : Type} {f g : α → σ → σ × Option β}
    (h : ∀ a s, f a s = g a s) (xs : List α) (s : σ) :
    mapAccumOption f xs s = mapAccumOption g xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs' ih =>
    simp [mapAccumOption, h, ih]

/-! ### Sum of elements at given indices across multiple lists -/

/-- Sum the elements at indices `i`, `j`, `k`, `l` from lists `xs`, `ys`, `zs`, `ws` respectively.
Uses `List.get!` (returns `default` for out-of-bounds). -/
def sumOfFour [Inhabited α] [Add α] (i j k l : Nat) (xs ys zs ws : List α) : α :=
  (xs[i]!) + (ys[j]!) + (zs[k]!) + (ws[l]!)

/-! ### Iterating list-transforming functions -/

/-- If `f` adds 1 to the length of every list, then iterating `f` `m` times via `Nat.iterate`
adds `m` to the length. Useful for DP over rows where each step extends the list by one element. -/
lemma length_nat_iterate (f : List α → List α) (xs : List α) (m : ℕ)
    (h : ∀ ys, (f ys).length = ys.length + 1) : (Nat.iterate f m xs).length = xs.length + m := by
  induction m generalizing xs with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, h]
    omega

end List



namespace List

/-! ### `getWrap` — wrap-around list access via modulo indexing

Access a list element with wrap-around: `getWrap l i` returns the element at index
`i % l.length`, using `get!` (which requires `Inhabited α`). This provides circular
buffer semantics for list access — indices wrap around by modulo the list length.
-/

/-- Safely access a list element with wrap-around via modulo indexing.
`getWrap l i` returns `l[i % l.length]!`. -/
def getWrap {α : Type _} [Inhabited α] (l : List α) (i : Nat) : α :=
  l[i % l.length]!

/-- When the index is within bounds, `getWrap l i` equals `l[i]!`.
That is, wrap-around has no effect for in-range indices. -/
lemma getWrap_eq_of_lt {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    getWrap l i = l[i]! := by
  unfold getWrap
  have hmod : i % l.length = i := Nat.mod_eq_of_lt h
  rw [hmod]

/-! ### `rotations` — all rotations of a list

`rotations l` returns the list of all rotations of `l`, where rotation `k` is
`l.drop k ++ l.take k`. The result has length `l.length`. -/

/-- Returns all rotations of a list. Rotation `k` is `l.drop k ++ l.take k`. -/
def rotations {α : Type u} (l : List α) : List (List α) :=
  List.range (l.length) |>.map (λ k => l.drop k ++ l.take k)

/-! ### `rotateLeft` lemmas

Mathlib provides `List.rotateLeft : List α → Nat → List α`, which rotates a list
left by `i` positions (default `i := 1`). For the empty list or when `xs.length ≤ 1`,
`rotateLeft` returns the list unchanged. Otherwise it drops the first `i % len`
elements and appends them at the end.
-/

/-- Rotating a list left by `n` preserves its length. -/

lemma length_rotateLeft {α : Type _} (l : List α) (n : Nat) : (l.rotateLeft n).length = l.length := by
  -- `rotateLeft` is defined with `let` bindings; we bypass them by case splitting on `l.length ≤ 1`
  delta List.rotateLeft
  by_cases h : l.length ≤ 1
  · simp [h]
  · simp [h, List.length_append, List.length_drop, List.length_take]
    omega

/-! ### `isCyclicShift` — check if a list appears as a cyclic shift prefix

`isCyclicShift s t k` checks whether `t` appears as the first `k` elements of some
cyclic shift of `s` (equivalently, whether there exists `i < k` such that
`((s ++ s).drop i).take k = t`). This generalizes the classic string cyclic-shift
matching problem to lists. -/

/-- Check if `t` appears as a length-`k` prefix of some cyclic shift of `s`.
That is, there exists `i < k` such that `((s ++ s).drop i).take k = t`. -/
def isCyclicShift {α : Type u} [DecidableEq α] (s t : List α) (k : Nat) : Bool :=
  List.any (List.range k) (λ i => ((s ++ s).drop i).take k = t)

/-- `isCyclicShift s t k` is true iff there exists `i < k` such that
`((s ++ s).drop i).take k = t`. -/
theorem isCyclicShift_eq_true_iff {α : Type u} [DecidableEq α] (s t : List α) (k : Nat) :
    isCyclicShift s t k = true ↔ ∃ i, i < k ∧ ((s ++ s).drop i).take k = t := by
  unfold isCyclicShift
  simp [any_range_iff]

end List

namespace List

/-! ### List rotation -/

/-- Direct expansion of `List.rotateRight` into its underlying `drop ++ take` form.
When the list length is 1 or less (empty or singleton), rotation is the identity.
Otherwise, it splits at `length - k % length`. -/
lemma rotateRight_eq {α : Type _} (xs : List α) (k : Nat) :
    xs.rotateRight k =
    if xs.length ≤ 1 then xs
    else xs.drop (xs.length - k % xs.length) ++ xs.take (xs.length - k % xs.length) := rfl

/-- Rotating a list (right by `k`) preserves its length. -/
lemma length_rotateRight {α : Type _} (xs : List α) (k : Nat) : (xs.rotateRight k).length = xs.length := by
  rw [rotateRight_eq]
  split
  · rfl
  · rw [List.length_append, List.length_drop, List.length_take]
    have hsub_le : xs.length - k % xs.length ≤ xs.length := Nat.sub_le _ _
    rw [Nat.min_eq_left hsub_le]
    omega

end List


namespace List

/-! ### `groupSum`, `groupCount`, `groupAvg` — grouped aggregation by key

These definitions compute aggregate statistics over elements of a `List α` grouped by a key
function `key : α → β`, with values extracted by `val : α → Nat`. They are the core primitives
for computing per-group sums, counts, and averages.

- `groupSum xs key val k` — sum of `val x` for all `x ∈ xs` where `key x = k`
- `groupCount xs key k` — number of `x ∈ xs` where `key x = k`
- `groupAvg xs key val k` — average (integer division) of `val x` for all `x ∈ xs` where `key x = k`
-/

/-- Sum of `val` over elements of `xs` whose `key` equals `k`. -/
def groupSum {α β : Type} [DecidableEq β] (xs : List α) (key : α → β) (val : α → Nat) (k : β) : Nat :=
  (xs.filter fun x => key x = k).foldl (fun acc x => acc + val x) 0

/-- Count of elements of `xs` whose `key` equals `k`. -/
def groupCount {α β : Type} [DecidableEq β] (xs : List α) (key : α → β) (k : β) : Nat :=
  (xs.filter fun x => key x = k).length

/-- Average (integer division) of `val` over elements of `xs` whose `key` equals `k`. -/
def groupAvg {α β : Type} [DecidableEq β] (xs : List α) (key : α → β) (val : α → Nat) (k : β) : Nat :=
  groupSum xs key val k / groupCount xs key k

end List

namespace List

/-! ## `getElem!` on `replicate`

Lemmas about using the `getElem!` notation (`l[i]!`) with `List.replicate`.  These cover
1D and 2D replicated lists, both in‑bounds and out‑of‑bounds cases.
-/

/-- If `i < n`, then `(replicate n a)[i]! = a`. -/
lemma getElem!_replicate {α : Type _} [Inhabited α] (a : α) (n i : Nat) (h : i < n) :
    (replicate n a)[i]! = a := by
  have h_len : i < (replicate n a).length := by simpa using h
  rw [getElem!_pos (c := replicate n a) (i := i) (h := h_len), getElem_replicate a h_len]

/-- If `¬ i < n`, then `(replicate n a)[i]! = default`. -/
lemma getElem!_replicate_of_not_lt {α : Type _} [Inhabited α] (a : α) (n i : Nat) (h : ¬ i < n) :
    (replicate n a)[i]! = default := by
  have h_len : ¬ i < (replicate n a).length := by simpa using h
  exact getElem!_neg (c := replicate n a) (i := i) (h := h_len)

/-- `getElem!` on a 2D replicated grid: `((replicate m (replicate n v))[i]!)[j]!`
returns `v` if both indices are in bounds, otherwise `default`. -/
lemma getElem!_replicate_replicate {α : Type _} [Inhabited α] (v : α) (m n i j : Nat) :
    ((replicate m (replicate n v))[i]!)[j]! =
    (if i < m then (if j < n then v else default) else default) := by
  by_cases hi : i < m
  · rw [getElem!_replicate (replicate n v) m i hi]
    by_cases hj : j < n
    · rw [getElem!_replicate v n j hj, if_pos hi, if_pos hj]
    · rw [getElem!_replicate_of_not_lt v n j hj, if_pos hi, if_neg hj]
  · rw [getElem!_replicate_of_not_lt (replicate n v) m i hi, if_neg hi]
    rfl

/-- In a 2D grid of zeros (type `Nat`), every `getElem!` access returns `0`. -/
lemma getElem!_replicate_replicate_zero (m n i j : Nat) :
    ((replicate m (replicate n (0 : Nat)))[i]!)[j]! = 0 := by
  by_cases hi : i < m
  · rw [getElem!_replicate (replicate n (0 : Nat)) m i hi]
    by_cases hj : j < n
    · rw [getElem!_replicate (0 : Nat) n j hj]
    · rw [getElem!_replicate_of_not_lt (0 : Nat) n j hj]
      rfl
  · rw [getElem!_replicate_of_not_lt (replicate n (0 : Nat)) m i hi]
    rfl

/-- If `lo ≤ v ≤ hi`, then every element of `List.replicate n v` satisfies
`lo ≤ r ∧ r ≤ hi`. Generalizes `mem_replicate_range` to any `LE` type. -/
lemma mem_replicate_range {α : Type _} [LE α] {n : Nat} {v lo hi r : α} (hlo : lo ≤ v) (hhi : v ≤ hi)
    (hr : r ∈ List.replicate n v) : lo ≤ r ∧ r ≤ hi := by
  rcases List.mem_replicate.mp hr with ⟨_, h⟩
  subst h
  exact ⟨hlo, hhi⟩

/-! ## Filter on `replicate` -/

/-- When `a ≠ b`, filtering a `replicate` of `b` for equality with `a` yields the empty list. -/
lemma filter_eq_replicate_of_ne {α : Type} [DecidableEq α] {a b : α} (hne : a ≠ b) (n : Nat) :
    List.filter (fun x => x = a) (List.replicate n b) = [] := by
  simp [hne, hne.symm]

/-- When `a ≠ b`, filtering a `replicate` of `b` for inequality with `a` yields the original replicate. -/
lemma filter_ne_replicate_of_ne {α : Type} [DecidableEq α] {a b : α} (hne : a ≠ b) (n : Nat) :
    List.filter (fun x => x ≠ a) (List.replicate n b) = List.replicate n b := by
  simp [hne, hne.symm]

/-! ## Append properties of `replicate` -/

/-- Appending a single `val` to `replicate k val` equals `replicate (k+1) val`. -/
lemma replicate_succ_append_val {α : Type} (k : Nat) (val : α) :
    List.replicate k val ++ [val] = List.replicate (k+1) val := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate, ih, List.append_assoc]

/--
When `a ≤ b`, the length of `List.replicate a x ++ List.replicate (b - a) y` is `b`.
This captures the pattern of distributing `b` total slots, with the first `a` having value `x` and the rest `y`.
-/
lemma length_replicate_append_replicate_sub {α : Type} {a b : Nat} (x y : α) (ha_le_b : a ≤ b) :
    (List.replicate a x ++ List.replicate (b - a) y).length = b := by
  simp [List.length_append, List.length_replicate, Nat.add_sub_cancel' ha_le_b]

/-- The length of a concatenation of two `replicate` lists equals the sum of counts. -/
lemma length_replicate_append {α : Type} (a b : Nat) (x y : α) :
    ((replicate a x) ++ (replicate b y)).length = a + b := by
  simp

/-- If `a ≠ b`, filtering `replicate n a ++ replicate m b` for elements equal to `a`
    yields a list of length `n`. Generalizes the pattern of counting occurrences of
    one value in a two-value list. -/
lemma length_filter_eq_replicate_append_of_ne {α : Type} [DecidableEq α] {a b : α} (hne : a ≠ b) (n m : Nat) :
    (filter (fun x => x = a) ((replicate n a) ++ (replicate m b))).length = n := by
  simp [hne, hne.symm]

/-- If `i < a`, then `getD i` on `(replicate a x ++ replicate b y)` returns `x`. -/
lemma getD_replicate_append_of_lt {α : Type} {a b : Nat} {x y d : α} {i : Nat}
    (h : i < a) : ((replicate a x) ++ (replicate b y)).getD i d = x := by
  rw [List.getD_append _ _ _ _ (by simpa [List.length_replicate] using h)]
  exact List.getD_replicate x (h := h)

/-- If `a ≤ i` and `i - a < b`, then `getD i` on `(replicate a x ++ replicate b y)`
    returns `y`. -/
lemma getD_replicate_append_of_ge {α : Type} {a b : Nat} {x y d : α} {i : Nat}
    (hge : a ≤ i) (hsub : i - a < b) :
    ((replicate a x) ++ (replicate b y)).getD i d = y := by
  have hlen : (replicate a x).length = a := by simp
  rw [List.getD_append_right _ _ _ _ (by simpa [hlen] using hge)]
  have : i - (replicate a x).length = i - a := by simp
  rw [this]
  exact List.getD_replicate y (h := hsub)

/-! ## Predicate over replicated elements -/

/-- If an element satisfies a predicate, every element of a replicated list of that
element also satisfies the predicate. This generalizes the pattern of showing
that a property holds for all members of a uniform list.

For example, if `isHexChar '0' = true`, then every element of `List.replicate 64 '0'`
is a hex character. -/
lemma forall_mem_replicate_of_true {α : Type} (p : α → Bool) (a : α) (hpa : p a = true) :
    ∀ (n : Nat) (x : α), x ∈ List.replicate n a → p x = true := by
  intro n x hx
  rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
  exact hpa

/-! ## `replicateOfLength`

Create a list by replicating a value `a : α` as many times as the length of `xs : List β`.
Useful when output list length must match a reference input length. -/

/-- `replicateOfLength a xs` produces a list of `a` repeated `xs.length` times.
This is a convenience wrapper around `List.replicate xs.length a`. -/
def replicateOfLength {α β : Type} (a : α) (xs : List β) : List α :=
  List.replicate xs.length a

/-- The length of `replicateOfLength a xs` equals the length of `xs`. -/
lemma replicateOfLength_length {α β : Type} (a : α) (xs : List β) :
    (replicateOfLength a xs).length = xs.length := by
  simp [replicateOfLength]

/-- For any in-bounds index `i`, `getD i d` on `replicateOfLength a xs` returns `a`. -/
lemma replicateOfLength_getD {α β : Type} (a : α) (d : α) (xs : List β) (i : Nat)
    (hi : i < xs.length) : (replicateOfLength a xs).getD i d = a := by
  unfold replicateOfLength
  rw [List.getD_replicate a hi]

/-! ## `getD` and `getElem?` on `replicate`

Lemmas about `List.getD` and `List.getElem?` (the `l[i]?` notation) with `List.replicate`.
-/

/-- `getD idx a` on a `replicate` of `a` always returns `a`, regardless of whether
`idx` is in bounds. Generalizes `List.getD_replicate` by using the same value as
the default. -/
lemma getD_replicate_eq_self {α : Type} {len idx : Nat} (a : α) :
    (List.replicate len a).getD idx a = a := by
  by_cases h : idx < len
  · rw [List.getD_replicate (x := a) h]
  · have hle : (List.replicate len a).length ≤ idx := by
      rw [List.length_replicate]
      exact Nat.le_of_not_lt h
    rw [List.getD_eq_default (List.replicate len a) a hle]

/-- When `idx < len`, `(replicate len a)[idx]?` returns `some a`. -/
lemma getElem?_replicate_eq_some {α : Type} {len idx : Nat} (a : α) (h : idx < len) :
    (List.replicate len a)[idx]? = some a := by
  have hi : idx < (List.replicate len a).length := by simpa [List.length_replicate] using h
  have h_eq := List.getElem?_eq_getElem hi
  simpa [List.getElem_replicate] using h_eq

/-! ## `replicateGrid`

Create a rectangular grid by replicating a value `elem` of type `α` in `rows` rows and `cols` columns.
This is simply `List.replicate rows (List.replicate cols elem)`. -/

/-- `replicateGrid rows cols elem` creates a rectangular grid of `rows` copies of
a list of `cols` copies of `elem`. Equivalent to `List.replicate rows (List.replicate cols elem)`. -/
def replicateGrid {α : Type} (rows cols : Nat) (elem : α) : List (List α) :=
  List.replicate rows (List.replicate cols elem)

/-- The outer dimension of `replicateGrid rows cols elem` has length `rows`. -/
lemma replicateGrid_length {α : Type} (rows cols : Nat) (elem : α) :
    (replicateGrid rows cols elem).length = rows := by
  simp [replicateGrid]

/-- Every row in `replicateGrid rows cols elem` has length `cols`. -/
lemma replicateGrid_row_length {α : Type} (rows cols : Nat) (elem : α) :
    ∀ row ∈ replicateGrid rows cols elem, row.length = cols := by
  simp [replicateGrid]

end List

namespace List

/-! ### Replicate + singleton append -/

/-- The length of `replicate k a ++ [b]` is `k + 1`. -/
lemma replicate_append_singleton_length (k a b : Nat) :
    (List.replicate k a ++ [b]).length = k + 1 := by
  simp

/-- Every element of `replicate k a ++ [b]` is bounded by `bound` if `a ≤ bound` and `b ≤ bound`. -/
lemma replicate_append_singleton_all_le (k a b bound : Nat) (ha : a ≤ bound) (hb : b ≤ bound) :
    ∀ w ∈ (List.replicate k a ++ [b]), w ≤ bound := by
  intro w hw
  rcases List.mem_append.mp hw with (hmem | hmem)
  · have heq := (List.mem_replicate.mp hmem).right
    subst heq
    exact ha
  · have heq := List.mem_singleton.mp hmem
    subst heq
    exact hb

/-- For `i < k`, the i-th element of `replicate k a ++ [b]` is `a`. -/
lemma replicate_append_singleton_getElem!_lt (k a b i : Nat) (hi : i < k) :
    (List.replicate k a ++ [b])[i]! = a := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i (by omega)

/-- The element at index `k` of `replicate k a ++ [b]` is `b` (the last element). -/
lemma replicate_append_singleton_getElem!_at_last (k a b : Nat) :
    (List.replicate k a ++ [b])[k]! = b := by
  first
  | (solve
    | rfl
    | simp_all []
    | omega
    | aesop
    | simp_all [List.foldl, List.foldr]
    | simp_all [Nat.absDiff]
    | induction k <;> simp_all []
    | cases k <;> simp_all [])

end List


namespace List

/-! ### `reverse` preserves non-emptiness -/

/-- If a list is non-empty, its reverse is also non-empty. -/
lemma reverse_ne_nil {α : Type} {l : List α} (h : l ≠ []) : l.reverse ≠ [] := by
  intro hrev
  apply h
  have : l.reverse = [].reverse := by simpa using hrev
  exact List.reverse_injective this

/-- `(l₁ ++ l₂).reverse` with `l₂.length` elements dropped from the front gives `l₁.reverse`.
This is useful when reasoning about reversed concatenations, e.g., to extract a prefix
after reversing the whole concatenation. -/
lemma reverse_append_drop_eq {α : Type u} (l₁ l₂ : List α) :
    (l₁ ++ l₂).reverse.drop l₂.length = l₁.reverse := by
  simp [List.reverse_append]

/-- If a list is non-empty, its dedup is also non-empty. -/
lemma dedup_ne_nil {α : Type} [DecidableEq α] {l : List α} (h : l ≠ []) : l.dedup ≠ [] := by
  by_contra hnil
  cases l with
  | nil => exact h rfl
  | cons x xs =>
    have hmem : x ∈ (x :: xs).dedup := by
      rw [List.mem_dedup]; exact List.mem_cons_self x xs
    rw [hnil] at hmem; simp at hmem

end List

namespace List

/-! ### Properties of `zipWith` element access -/

/-- If `j` is within bounds of both `l1` and `l2`, then accessing the `j`-th element
of `zipWith f l1 l2` via `get?` and `getD 0` yields `f` applied to the corresponding
`j`-th elements of `l1` and `l2` (also accessed via `getD 0`). -/
lemma getElem_zipWith_lt (f : Nat → Nat → Nat) (l1 l2 : List Nat) (j : Nat)
    (h1 : j < l1.length) (h2 : j < l2.length) :
    ((List.zipWith f l1 l2)[j]?).getD 0 = f (((l1[j]?).getD 0)) (((l2[j]?).getD 0)) := by
  induction l1 generalizing l2 j with
  | nil => simp at h1
  | cons a l1' ih =>
    induction l2 generalizing j with
    | nil => simp at h2
    | cons b l2' _ =>
      cases j with
      | zero => simp
      | succ j' =>
        have h1' : j' < l1'.length := by
          simp at h1; omega
        have h2' : j' < l2'.length := by
          simp at h2; omega
        simp [ih l2' j' h1' h2']

/-! ### `getElem!` on `zipWith` -/

/-- When `i` is within bounds of both `l₁` and `l₂`, `getElem!` distributes over
`zipWith`: `(zipWith f l₁ l₂)[i]! = f (l₁[i]!) (l₂[i]!)`.  This variant takes two
separate bound proofs instead of a global length equality, making it convenient when
the bounds are known independently. -/
lemma getElem!_zipWith_of_lt {α β γ : Type _} [Inhabited α] [Inhabited β] [Inhabited γ]
    (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : Nat)
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) :
    (List.zipWith f l₁ l₂)[i]! = f (l₁[i]!) (l₂[i]!) := by
  have hi_zip : i < (List.zipWith f l₁ l₂).length := by
    rw [List.length_zipWith]
    exact Nat.lt_min.mpr ⟨hi₁, hi₂⟩
  have hz  : (List.zipWith f l₁ l₂)[i]! = (List.zipWith f l₁ l₂)[i] :=
    getElem!_pos _ i hi_zip
  have hz₁ : l₁[i]! = l₁[i] := getElem!_pos l₁ i hi₁
  have hz₂ : l₂[i]! = l₂[i] := getElem!_pos l₂ i hi₂
  rw [hz, hz₁, hz₂]
  exact List.getElem_zipWith (h := hi_zip)

/-- When `l₁.length = l₂.length` and `i` is in bounds, `getElem!` distributes over
`zipWith`: `(zipWith f l₁ l₂)[i]! = f (l₁[i]!) (l₂[i]!)`.  This is the `getElem!`
counterpart of `List.getElem_zipWith`.  The length equality condition ensures that
both lists have valid elements at `i`. -/
lemma getElem!_zipWith {α β γ : Type _} [Inhabited α] [Inhabited β] [Inhabited γ]
    (f : α → β → γ) (l₁ : List α) (l₂ : List β) (hlen : l₁.length = l₂.length) (i : Nat)
    (hi : i < l₁.length) : (List.zipWith f l₁ l₂)[i]! = f (l₁[i]!) (l₂[i]!) := by
  have h₂ : i < l₂.length := by
    rw [← hlen]
    exact hi
  exact getElem!_zipWith_of_lt f l₁ l₂ i hi h₂

/-! ### `getElem!` on `zip` -/

/-- When `i` is within bounds of both `l₁` and `l₂`, `getElem!` on `zip l₁ l₂` returns
the pair of the `i`-th elements: `(zip l₁ l₂)[i]! = (l₁[i], l₂[i])`.
This is the `zip` counterpart of `getElem!_zipWith_of_lt`. -/
lemma getElem!_zip_of_lt {α β : Type _} [Inhabited α] [Inhabited β]
    (l₁ : List α) (l₂ : List β) (i : Nat)
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) :
    (zip l₁ l₂)[i]! = (l₁[i], l₂[i]) := by
  have hi_zip : i < (zip l₁ l₂).length := by
    rw [length_zip]
    exact Nat.lt_min.mpr ⟨hi₁, hi₂⟩
  rw [getElem!_pos (zip l₁ l₂) i hi_zip]
  exact getElem_zip (h := hi_zip)

/-! ### Properties of `zipIdx` membership -/

/-- If `(a, i) ∈ l.zipIdx`, then `i` is a valid index and `l[i]? = some a`.
This combines `List.mem_zipIdx_iff_getElem?` with `List.getElem?_eq_some_iff`
to provide both the bound and the lookup result in one step. -/
lemma mem_zipIdx_imp_lt_and_getElem? {α : Type} (l : List α) (a : α) (i : Nat)
    (h : (a, i) ∈ l.zipIdx) : i < l.length ∧ l[i]? = some a := by
  have hget : l[i]? = some a := (List.mem_zipIdx_iff_getElem?.mp h)
  rcases (List.getElem?_eq_some_iff.mp hget) with ⟨hlt, heq⟩
  exact ⟨hlt, hget⟩

/-- If `(a, i) ∈ l.zipIdx`, then `i` is a valid index and `l[i]! = a`.
This is the `getElem!` counterpart of `mem_zipIdx_imp_lt_and_getElem?`,
convenient when you need the default value rather than `Option`. -/
lemma mem_zipIdx_getElem! {α : Type} [Inhabited α] (l : List α) (p : α × ℕ) (h : p ∈ l.zipIdx) :
    p.2 < l.length ∧ l[p.2]! = p.1 := by
  have h_mem : l[p.2]? = some p.1 := (List.mem_zipIdx_iff_getElem?.mp h)
  rcases (List.getElem?_eq_some_iff.mp h_mem) with ⟨hlen, h_eq⟩
  have hval : l[p.2]! = p.1 := by
    simpa [hlen] using h_eq
  exact ⟨hlen, hval⟩

/-- If `i < l.length`, then `(l[i], i) ∈ l.zipIdx`.
This is the converse of `mem_zipIdx_imp_lt_and_getElem?` and `mem_zipIdx_getElem!`.
Uses `List.getElem_zipIdx` to construct the membership proof. -/
lemma mem_zipIdx_of_lt {α : Type} (l : List α) (i : Nat) (hi : i < l.length) : (l[i], i) ∈ l.zipIdx := by
  have h_length : i < (l.zipIdx).length := by
    simpa using hi
  have h_get : (l.zipIdx)[i] = (l[i], i) := by
    simpa using (List.getElem_zipIdx l 0 i h_length)
  have h_mem : (l.zipIdx)[i] ∈ l.zipIdx := List.getElem_mem h_length
  rw [h_get] at h_mem
  exact h_mem

/-! ### `maxZippedWith` — maximum of a pairwise-zipped function over two lists -/

/-- Maximum of `f aᵢ bᵢ` for pairwise zipped elements of two lists.
Returns 0 if either list is empty. -/
def maxZippedWith {α β : Type} (f : α → β → Nat) : List α → List β → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => max (f x y) (maxZippedWith f xs ys)

/-- `maxPairSum l1 l2` is the maximum of `x + y` for pairwise zipped elements of
two `Nat` lists. This is a specialization of `maxZippedWith` with addition. -/
def maxPairSum (l1 l2 : List Nat) : Nat := maxZippedWith (· + ·) l1 l2

/-- For any index `i` within bounds of both lists,
`f (l1[i]) (l2[i]) ≤ maxZippedWith f l1 l2`. -/
lemma maxZippedWith_ge_getD {α β : Type} [Inhabited α] [Inhabited β] (f : α → β → Nat)
    (l1 : List α) (l2 : List β) (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length) :
    f (l1.getD i default) (l2.getD i default) ≤ maxZippedWith f l1 l2 := by
  induction' l1 with x xs ih1 generalizing l2 i
  · exact absurd h1 (by simp)
  · cases' l2 with y ys
    · exact absurd h2 (by simp)
    · unfold maxZippedWith
      cases' i with i
      · simp
      · simp
        have hi1 : i < xs.length := by simpa using h1
        have hi2 : i < ys.length := by simpa using h2
        have h_ih : f (xs.getD i default) (ys.getD i default) ≤ maxZippedWith f xs ys :=
          ih1 ys i hi1 hi2
        exact Or.inr h_ih

/-! ### `zip` membership lemmas -/

/-- If a pair is in the zip of `xs` and `ys`, its second component is in `ys`. -/
lemma snd_mem_of_mem_zip {α β : Type u} {xs : List α} {ys : List β} {e : α × β}
    (h : e ∈ xs.zip ys) : e.2 ∈ ys := by
  rcases List.of_mem_zip h with ⟨_, hs⟩
  exact hs

/-- If `v ∈ ys` and the lists have equal length, there exists an element in `xs.zip ys`
whose second component is `v`. -/
lemma exists_mem_zip_snd_eq_of_mem {α β : Type u} {v : β} {xs : List α} {ys : List β}
    (h_len : xs.length = ys.length) (h_mem : v ∈ ys) :
    ∃ e ∈ xs.zip ys, e.2 = v := by
  rcases List.mem_iff_getElem.mp h_mem with ⟨i, hi, hi_eq⟩
  have hi_zip : i < (xs.zip ys).length := by
    rw [List.length_zip, h_len, min_self]
    exact hi
  have hzip := List.getElem_zip (h := hi_zip)
  have h_snd : ((xs.zip ys)[i]).2 = v := by
    rw [hzip, hi_eq]
  refine ⟨(xs.zip ys)[i], List.getElem_mem hi_zip, h_snd⟩

/-- If a pair `p` is in `zip l (map f l)`, then the second component
of `p` equals `f` applied to the first component. -/
lemma eq_of_mem_zip_map {α β : Type} (l : List α) (f : α → β) (p : α × β)
    (h : p ∈ List.zip l (List.map f l)) : p.2 = f p.1 := by
  induction' l with a as ih generalizing p
  · simp at h
  · rw [List.map_cons f a as, List.zip_cons_cons] at h
    simp at h
    rcases h with (rfl | h')
    · rfl
    · exact ih p h'

/-! ### Length of `zipWith` with tail -/

/-- For any list `xs` and function `f`, the length of `zipWith f xs xs.tail` equals
`xs.length - 1`. This holds even for empty lists, where both sides are zero. -/
lemma length_zipWith_tail (xs : List α) (f : α → α → β) :
    (List.zipWith f xs xs.tail).length = xs.length - 1 := by
  rw [List.length_zipWith, List.length_tail, Nat.min_eq_right (Nat.sub_le _ _)]

/-! ### Length of `zipWith` with reverse -/

/-- For any list `l` and function `f`, the length of `zipWith f l l.reverse` equals `l.length`.
The proof follows from `length_zipWith` and `length_reverse`. -/
lemma length_zipWith_reverse {α β : Type _} (f : α → α → β) (l : List α) :
    (List.zipWith f l l.reverse).length = l.length := by
  simp

/-! ### Dot product of two `Nat` lists -/

/-- Dot product of two `Nat` lists: `∑ᵢ (l₁[i] * l₂[i])` for as many elements as the shorter list.
Computes `(l₁.zipWith (· * ·) l₂).foldl (· + ·) 0`.

For example:
* `dotProduct [1, 2, 3] [4, 5, 6] = 1*4 + 2*5 + 3*6 = 32`
* `dotProduct [1] [2, 3] = 1*2 = 2` (uses the shorter list length) -/
def dotProduct (l₁ l₂ : List Nat) : Nat :=
  (List.zipWith (· * ·) l₁ l₂).foldl (· + ·) 0

/-! ### Simplifications when input lists have equal length -/

/-- When `l₁` and `l₂` have equal length, `zipWith f l₁ l₂` has that same length.
This is a corollary of `List.length_zipWith` specialized to equal-length inputs. -/
lemma length_zipWith_of_length_eq {α β γ : Type _} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (hlen : l₁.length = l₂.length) : (zipWith f l₁ l₂).length = l₁.length := by
  rw [List.length_zipWith, hlen, Nat.min_self]

/-! ### Bounds from `zipWith` length -/

/-- If `i < (zipWith f l₁ l₂).length`, then `i` is within bounds of both `l₁` and `l₂`.
This decomposes a bound on the zipped list's length into individual bounds,
using `List.length_zipWith` and `Nat.min` properties. -/
lemma lt_of_lt_length_zipWith {α β γ : Type _} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ)
    (h : i < (zipWith f l₁ l₂).length) : i < l₁.length ∧ i < l₂.length := by
  have hmin : i < min (l₁.length) (l₂.length) := by simpa [List.length_zipWith] using h
  exact ⟨lt_of_lt_of_le hmin (Nat.min_le_left _ _), lt_of_lt_of_le hmin (Nat.min_le_right _ _)⟩

/-- `getD` distributes over `zipWith` when the index is in bounds:
`(zipWith f l₁ l₂).getD i d = f (l₁.getD i da) (l₂.getD i db)`.
This is the `getD` counterpart of `List.getElem_zipWith`. -/
lemma getD_zipWith {α β γ : Type _} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (d : γ) (da : α) (db : β) (i : ℕ)
    (h : i < (zipWith f l₁ l₂).length) : (zipWith f l₁ l₂).getD i d = f (l₁.getD i da) (l₂.getD i db) := by
  have ⟨hi₁, hi₂⟩ := lt_of_lt_length_zipWith f l₁ l₂ i h
  rw [List.getD_eq_getElem _ d h, List.getD_eq_getElem _ da hi₁, List.getD_eq_getElem _ db hi₂]
  exact List.getElem_zipWith (h := h)

/-- When `l₁` and `l₂` have equal length and `i` is in bounds, the `get?` of
`zipWith f l₁ l₂` at `i` is `some (f (l₁[i]) (l₂[i]))`.  This is the `get?` counterpart
of `List.getElem_zipWith`, convenient when both lists are known to have the same length. -/
lemma getElem?_zipWith_of_length_eq {α β γ : Type _} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (i : Nat) (hlen : l₁.length = l₂.length) (hi : i < l₁.length) :
    (zipWith f l₁ l₂)[i]? = some (f (l₁[i]'(hi)) (l₂[i]'(hlen.symm ▸ hi))) := by
  have hi₂ : i < l₂.length := hlen.symm ▸ hi
  have hi_zip : i < (zipWith f l₁ l₂).length := by
    rw [List.length_zipWith]
    exact Nat.lt_min.mpr ⟨hi, hi₂⟩
  have hval : (zipWith f l₁ l₂)[i]'(hi_zip) = f (l₁[i]'(hi)) (l₂[i]'(hi₂)) := by
    rw [List.getElem_zipWith (h := hi_zip)]
  exact (List.getElem?_eq_some_iff (a := f (l₁[i]'(hi)) (l₂[i]'(hi₂)))).mpr ⟨hi_zip, hval⟩

/-- When `i` is within bounds of both `l₁` and `l₂`, the `get?` of `zipWith f l₁ l₂`
at `i` is `some (f (l₁[i]) (l₂[i]))`.  This variant takes two separate bound proofs
instead of a length equality, making it convenient when the bounds are known
independently.  This is the `get?` counterpart of `getElem!_zipWith_of_lt`. -/
lemma getElem?_zipWith_of_lt {α β γ : Type _} (f : α → β → γ) {l₁ : List α} {l₂ : List β} {i : Nat}
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    (List.zipWith f l₁ l₂)[i]? = some (f (l₁[i]) (l₂[i])) := by
  rw [List.getElem?_zipWith]
  have h₁' : l₁[i]? = some (l₁[i]) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨h₁, rfl⟩
  have h₂' : l₂[i]? = some (l₂[i]) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨h₂, rfl⟩
  rw [h₁', h₂']

/-! ### `mapThree` — zipWith over three lists -/

/-- `mapThree f xs ys zs` applies `f` elementwise to three lists, analogous to
`zipWith` but with three inputs.  When any list is exhausted the result terminates.

```lean
example : List.mapThree (fun x y z => (x, y, z)) [1,2] [3,4] [5,6] = [(1,3,5), (2,4,6)] := rfl
``` -/
def mapThree (f : α → β → γ → δ) (xs : List α) (ys : List β) (zs : List γ) : List δ :=
  match xs, ys, zs with
  | x::xs', y::ys', z::zs' => f x y z :: mapThree f xs' ys' zs'
  | _, _, _ => []

/-- When all three input lists have the same length, `mapThree` produces a list
of that length.  This is the three-list analogue of `length_zipWith_of_length_eq`. -/
lemma mapThree_length_eq_left (f : α → β → γ → δ) (xs : List α) (ys : List β) (zs : List γ)
    (hxy : length xs = length ys) (hyz : length ys = length zs) :
    length (mapThree f xs ys zs) = length xs := by
  induction xs generalizing ys zs with
  | nil =>
    have hy_nil : ys = [] :=
      (List.length_eq_zero_iff.mp (by simpa using hxy.symm))
    have hz_nil : zs = [] :=
      (List.length_eq_zero_iff.mp (by simpa [hy_nil] using hyz.symm))
    simp [mapThree, hy_nil, hz_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hxy
    | cons y ys =>
      cases zs with
      | nil => simp at hyz
      | cons z zs =>
        simp [mapThree]
        have hxy' : length xs = length ys := by
          simp at hxy; omega
        have hyz' : length ys = length zs := by
          simp at hyz; omega
        exact ih ys zs hxy' hyz'

/-! ### Membership in `zipWith` -/

/-- If `z` is in `zipWith f l₁ l₂`, then there exist `a ∈ l₁` and `b ∈ l₂` such that
`z = f a b`. This decomposes membership in a zipped list back to membership in the
original lists. -/
lemma mem_zipWith_mp {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) :
    z ∈ zipWith f l₁ l₂ → ∃ a ∈ l₁, ∃ b ∈ l₂, z = f a b := by
  induction l₁ generalizing l₂ with
  | nil => intro h; simp at h
  | cons a as ih =>
    cases l₂ with
    | nil => intro h; simp at h
    | cons b bs =>
      intro h
      simp only [zipWith, mem_cons] at h
      rcases h with (rfl | h)
      · exact ⟨a, by simp, ⟨b, by simp, rfl⟩⟩
      · rcases ih bs h with ⟨a', ha', b', hb', rfl⟩
        have ha_mem : a' ∈ a :: as := mem_cons_of_mem _ ha'
        have hb_mem : b' ∈ b :: bs := mem_cons_of_mem _ hb'
        exact ⟨a', ha_mem, ⟨b', hb_mem, rfl⟩⟩

/-! ### `countZipPairs` — count matching pairs in zipped lists -/

/-- Count the number of index-aligned pairs `(a, b)` across `xs` and `ys` where `a = x` and
`b = y`. This is `countPairOccurrences` (`general.List.Count`) applied to `zip xs ys`, but more
convenient when the two lists are separate rather than pre-zipped.

For example, `countZipPairs "A" 1 ["A", "B", "A"] [1, 1, 2] = 1` (only the first pair `("A", 1)` matches).

Equivalent to `List.countP (fun (p : α × β) => p.1 = x ∧ p.2 = y) (List.zip xs ys)`. -/
def countZipPairs {α β : Type} [DecidableEq α] [DecidableEq β] (x : α) (y : β) (xs : List α) (ys : List β) : Nat :=
  List.countP (fun (p : α × β) => p.1 = x ∧ p.2 = y) (List.zip xs ys)

/-! ### `maskedSum` — sum of elements selected by a boolean mask -/

/-- Sum of elements from `xs` where the corresponding boolean mask entry in `sel` is `true`.
This zips `xs` with `sel`, then folds: for each `(x, b)`, if `b` then add `x` to the accumulator.
If `sel` is shorter than `xs`, extra elements in `xs` are ignored (since `zip` truncates).
If `sel` is longer than `xs`, extra booleans in `sel` are ignored.

Examples:
* `maskedSum [1, 2, 3] [true, false, true] = 1 + 3 = 4`
* `maskedSum [5, 6] [true] = 5`
* `maskedSum [1, 2] [false, true] = 2` -/
def maskedSum (xs : List Nat) (sel : List Bool) : Nat :=
  (List.zip xs sel).foldl (fun acc p => if p.2 then acc + p.1 else acc) 0


lemma maskedSum_nil (xs : List Nat) : maskedSum xs [] = 0 := by
  simp [maskedSum]

end List
