import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Specific

open _root_.List

namespace List

/-! ## `allEqFrom` and `allEq`: uniformity predicates

`allEqFrom x xs` returns `true` if every element of `xs` equals `x`.
`allEq xs` returns `true` if all elements of `xs` are equal to each other. -/

/-- `allEqFrom x xs` is `true` iff every element of `xs` equals `x`. -/
def allEqFrom {α : Type} [BEq α] (x : α) : List α → Bool
  | [] => true
  | y :: ys => (y == x) && allEqFrom x ys

/-- `allEq xs` is `true` iff all elements of `xs` are equal to each other.
An empty list is trivially uniform. -/
def allEq {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => allEqFrom x xs

/-- `allEqFrom x (replicate n x) = true`. -/
theorem allEqFrom_replicate {α : Type} [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    allEqFrom x (List.replicate n x) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp [allEqFrom, ih]

/-- `allEq (replicate n x) = true`. -/
theorem allEq_replicate {α : Type} [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    allEq (List.replicate n x) = true := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [List.replicate_succ]
      simp [allEq, allEqFrom_replicate]

/-- If `y ≠ x`, then `allEqFrom x (y :: ys) = false`. -/
theorem allEqFrom_cons_ne_false {α : Type} [BEq α] [LawfulBEq α]
    (x y : α) (ys : List α) (h : y ≠ x) :
    allEqFrom x (y :: ys) = false := by
  simp [allEqFrom, h]

/-! ## `getElem!` lemmas -/

/-- Pushing `map` through `getElem!` when the index is in bounds.
`(l.map f)[i]! = f (l[i]!)` for `i < l.length`. -/
lemma getElem!_map [Inhabited α] [Inhabited β] (f : α → β) (l : List α) {i : Nat}
    (h : i < l.length) : (l.map f)[i]! = f (l[i]!) := by
  have hmap : i < (l.map f).length := by
    simpa using h
  rw [getElem!_pos (l.map f) i hmap, getElem!_pos l i h]
  simp

/-- If `i < n`, then `(List.replicate n a)[i]! = a`. -/
lemma getElem!_replicate_eq_of_lt {α : Type*} [Inhabited α]
    (a : α) {n i : Nat} (hi : i < n) :
    (List.replicate n a)[i]! = a := by
  rw [getElem!_pos (List.replicate n a) i (by simpa using hi)]
  simp

/-! ## `find?` lemmas -/

/-- If `List.find? p xs` returns `some x`, then `p x` holds (i.e., `p x = true`).
This is the soundness direction of `List.find?_eq_some_iff_append`. -/
theorem find?_some_imp {α : Type u} {p : α → Bool} {xs : List α} {x : α}
    (h : List.find? p xs = some x) : p x := by
  have htrue := (List.find?_eq_some_iff_append.mp h).left
  simpa using htrue

/-! ## `zip` length lemmas -/

/-- The length of `(xs.zip ys)` is at most the length of `xs`. -/
theorem length_zip_le_left {α β : Type} (xs : List α) (ys : List β) :
    (xs.zip ys).length ≤ xs.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys =>
          simp only [List.zip, List.length_cons]
          exact Nat.succ_le_succ (ih ys)

/-- After filtering a zipped list, the length is at most the length of
the left input list. -/
theorem length_filter_zip_le_left {α β : Type}
    (xs : List α) (ys : List β) (keep : α × β → Bool) :
    ((xs.zip ys).filter keep).length ≤ xs.length := by
  exact Nat.le_trans (List.length_filter_le keep (xs.zip ys))
    (length_zip_le_left xs ys)

/-! ## Swapping first two elements

The operation `swapFirstTwo?` tries to swap the first two elements of a
two-element list when they are distinct. It returns `none` for lists of
other lengths or when the two elements are equal. -/

/-- If `xs = [a, b]` with `a ≠ b`, return `some [b, a]`; otherwise `none`. -/
def swapFirstTwo? [DecidableEq α] (xs : List α) : Option (List α) :=
  match xs with
  | [a, b] => if a = b then none else some [b, a]
  | _ => none

/-- `swapFirstTwo? xs` succeeds iff `xs` is a two-element list with distinct
elements, and returns the swapped version. -/
theorem swapFirstTwo?_eq_some_iff {α : Type} [DecidableEq α] {xs ys : List α} :
    swapFirstTwo? xs = some ys ↔ ∃ a b, a ≠ b ∧ xs = [a, b] ∧ ys = [b, a] := by
  constructor
  · intro h
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
      simp [swapFirstTwo?] at h
    exact ⟨a, b, h.1, rfl, h.2.symm⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    simp [swapFirstTwo?, hab]

/-- If `swapFirstTwo?` succeeds, the result has the same length as the input. -/
theorem swapFirstTwo?_length {α : Type} [DecidableEq α] {xs ys : List α}
    (h : swapFirstTwo? xs = some ys) : ys.length = xs.length := by
  rcases (swapFirstTwo?_eq_some_iff.mp h) with ⟨a, b, -, rfl, rfl⟩
  rfl

/-- If `swapFirstTwo?` succeeds, each element in the result is different from the
corresponding element in the input. -/
theorem swapFirstTwo?_get_ne_self {α : Type} [DecidableEq α] {xs ys : List α}
    (h : swapFirstTwo? xs = some ys) :
    ∀ (i : Fin xs.length), ys.get ⟨i, by rw [swapFirstTwo?_length h]; exact i.2⟩ ≠ xs.get i := by
  rcases (swapFirstTwo?_eq_some_iff.mp h) with ⟨a, b, hab, rfl, rfl⟩
  intro i
  fin_cases i
  · exact hab.symm
  · exact hab

/-! ## Branch on list emptiness

`chooseByEmptiness emptyValue nonemptyValue xs` returns `emptyValue` when `xs` is empty
and `nonemptyValue` otherwise. This provides a simple way to pick between two values
based on whether a list is empty, without examining any elements. -/

/-- Return `emptyValue` if `xs` is empty, `nonemptyValue` otherwise. -/
def chooseByEmptiness {α β : Type} (emptyValue nonemptyValue : β) (xs : List α) : β :=
  match xs with
  | [] => emptyValue
  | _ :: _ => nonemptyValue

@[simp]
theorem chooseByEmptiness_nil {α β : Type} (emptyValue nonemptyValue : β) :
    chooseByEmptiness (α := α) emptyValue nonemptyValue [] = emptyValue := by
  simp [chooseByEmptiness]

/-! ## `singletonWhenNonempty`

`singletonWhenNonempty value items` returns `[value]` when `items` is nonempty,
and `[]` when `items` is empty. Unlike `chooseByEmptiness`, the result is always
a `List α` (of the same type as `value`), making it convenient for constructing
singleton lists conditionally. -/

/-- Return `[value]` if `items` is nonempty, `[]` otherwise. -/
def singletonWhenNonempty {α β : Type} (value : α) (items : List β) : List α :=
  match items with
  | [] => []
  | _ :: _ => [value]

@[simp]
theorem singletonWhenNonempty_nil {α β : Type} (value : α) :
    singletonWhenNonempty value ([] : List β) = [] := rfl

@[simp]
theorem singletonWhenNonempty_cons {α β : Type} (value : α) (x : β) (xs : List β) :
    singletonWhenNonempty value (x :: xs) = [value] := rfl

/-- The length of `singletonWhenNonempty value items` is at most the length of `items`. -/
theorem length_singletonWhenNonempty_le_length {α β : Type} (value : α) (items : List β) :
    (singletonWhenNonempty value items).length ≤ items.length := by
  cases items with
  | nil => simp
  | cons _ _ => simp

/-! ## `intercalateWith`

`intercalateWith` folds a list using a custom "append-with-separator" function.
It generalizes `String.intercalate`: given an `empty` value and a binary `appendSep`,
`intercalateWith empty appendSep [a, b, c]` computes `appendSep a (appendSep b c)`.

This is a right-associated fold, useful for building strings (or other appendable types)
from lists with separators between elements. -/

/-- Intercalate elements of a list using a custom append-separator function.
`intercalateWith empty appendSep [a, b, c] = appendSep a (appendSep b c)`,
and the empty-list case returns `empty`, the singleton case returns the element unchanged. -/
def intercalateWith {α : Type} (empty : α) (appendSep : α → α → α) : List α → α
  | [] => empty
  | [s] => s
  | s :: t :: rest => appendSep s (intercalateWith empty appendSep (t :: rest))

@[simp]
theorem intercalateWith_nil {α : Type} (empty : α) (appendSep : α → α → α) :
    intercalateWith empty appendSep [] = empty := rfl

@[simp]
theorem intercalateWith_singleton {α : Type} (empty : α) (appendSep : α → α → α) (s : α) :
    intercalateWith empty appendSep [s] = s := rfl

theorem intercalateWith_two {α : Type} (empty : α) (appendSep : α → α → α) (a b : α) :
    intercalateWith empty appendSep [a, b] = appendSep a b := rfl

/-! ## `eraseDups` length lemmas -/

/-- For a list of length at most 1, removing duplicates does not change its length. -/
theorem eraseDups_length_eq_of_length_le_one {α : Type} [BEq α] {xs : List α}
    (hxs : xs.length ≤ 1) : xs.length = xs.eraseDups.length := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => simp [List.eraseDups, List.eraseDups.loop]
      | cons y ys => simp at hxs

/-! ## `eraseDups` under degenerate `BEq`

These theorems characterize the behavior of `eraseDups` when `BEq` is degenerate,
i.e., when `(x == y) = true` for all `x, y`. This arises in settings where equality
is intentionally trivialized (e.g., treating all elements as indistinguishable). -/

/-- When `BEq` is identically true, `List.eraseDups.loop xs [a]` always yields `[a]`.
That is, the accumulator never grows beyond the singleton. -/
theorem eraseDups_loop_single_of_all_beq_true {α : Type} [BEq α]
    (hbeq : ∀ x y : α, (x == y) = true) (xs : List α) (a : α) :
    List.eraseDups.loop xs [a] = [a] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
      rw [List.eraseDups.loop]
      simp [hbeq, ih]

/-- When `BEq` is identically true, `(a :: xs).eraseDups = [a]` for any list `xs`.
Effectively, every nonempty list collapses to a singleton. -/
theorem eraseDups_cons_eq_singleton_of_all_beq_true {α : Type} [BEq α]
    (hbeq : ∀ x y : α, (x == y) = true) (xs : List α) (a : α) :
    (a :: xs).eraseDups = [a] := by
  unfold List.eraseDups
  rw [List.eraseDups.loop]
  simp [eraseDups_loop_single_of_all_beq_true hbeq]

/-! ## `hasDuplicate`: Boolean test for duplicates -/

/-- `hasDuplicate xs` is `true` iff `xs` is not `Nodup`, i.e., `xs` contains
at least one duplicate element. -/
def hasDuplicate [DecidableEq α] (xs : List α) : Bool :=
  decide (¬ xs.Nodup)

/-- A list is not `Nodup` iff there exist two indices `i < j < l.length`
such that `l[i]! = l[j]!`. -/
theorem not_nodup_iff_exists_getElem!_eq [Inhabited α] {l : List α} :
    ¬ l.Nodup ↔ ∃ i j, i < j ∧ j < l.length ∧ l[i]! = l[j]! := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  push_neg
  constructor
  · intro h
    rcases h with ⟨i, j, hij, hj, heq⟩
    have hi : i < l.length := Nat.lt_trans hij hj
    have hget : l[i] = l[j] := by
      have hsome : some l[i] = some l[j] := by
        simpa [List.getElem?_eq_getElem, hi, hj] using heq
      simpa using Option.some.inj hsome
    exact ⟨i, j, hij, hj, by
      simpa [getElem!_pos l i hi, getElem!_pos l j hj] using hget⟩
  · intro h
    rcases h with ⟨i, j, hij, hj, heq⟩
    have hi : i < l.length := Nat.lt_trans hij hj
    exact ⟨i, j, hij, hj, by
      simpa [List.getElem?_eq_getElem, hi, hj,
        getElem!_pos l i hi, getElem!_pos l j hj] using heq⟩

/-- `hasDuplicate xs = true` iff there exist `i < j < xs.length` such that
`xs[i]! = xs[j]!`. -/
theorem hasDuplicate_eq_true_iff_exists_getElem!_eq [DecidableEq α] [Inhabited α]
    {xs : List α} :
    hasDuplicate xs = true ↔
      ∃ i j, i < j ∧ j < xs.length ∧ xs[i]! = xs[j]! := by
  unfold hasDuplicate
  rw [decide_eq_true_iff, not_nodup_iff_exists_getElem!_eq]

/-! ## `getD` membership lemma

`getD` returns either the `i`-th element or a fallback. If the fallback is already
in the list, the result is guaranteed to be in the list regardless of the index. -/

/-- If the fallback is in the list, then `getD i fallback` is also in the list.
This holds because `getD` either returns an in-bounds element or the fallback,
both of which are in `xs`. -/
theorem getD_mem_of_mem {α : Type} {xs : List α} {i : Nat} {fallback : α}
    (hfallback : fallback ∈ xs) : xs.getD i fallback ∈ xs := by
  unfold List.getD
  cases h : xs[i]? with
  | none => simpa [h] using hfallback
  | some value => simpa [h] using List.mem_of_getElem? h

/-! ## Misc lemmas about length and membership -/

/-- If two lists have equal lengths, one is empty if and only if the other is empty. -/
theorem nil_iff_nil_of_length_eq {α β : Type} {left : List α} {right : List β}
    (hlength : right.length = left.length) :
    left = [] ↔ right = [] := by
  constructor
  · intro hleft
    have : right.length = 0 := by
      simpa [hleft] using hlength
    exact List.length_eq_zero_iff.mp this
  · intro hright
    have : left.length = 0 := by
      simpa [hright] using hlength.symm
    exact List.length_eq_zero_iff.mp this

/-- If a list is nonempty, then its length minus one is strictly less than its length. -/
theorem length_sub_one_lt_of_ne_nil {α : Type} {xs : List α} (h : xs ≠ []) :
    xs.length - 1 < xs.length := by
  exact Nat.sub_lt (List.length_pos_iff.2 h) Nat.zero_lt_one

/-! ## `Nodup` lemmas -/

/-- In a nodup list, elements at distinct valid indices are distinct.
This is a corollary of `List.Nodup.getElem_inj_iff`. -/
theorem nodup_getElem_ne_of_ne {α : Type*} {l : List α} (hl : l.Nodup)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) :
    l[i] ≠ l[j] := by
  intro hget
  exact hne ((hl.getElem_inj_iff).mp hget)

/-- In a nodup list, if two elements at `Fin` positions are equal, then the
positions themselves are equal. This is the forward direction of
`List.Nodup.get_inj_iff`. -/
theorem nodup_get_inj {α : Type*} {xs : List α} (hxs : xs.Nodup)
    {i j : Fin xs.length} (hget : xs.get i = xs.get j) : i = j :=
  (hxs.get_inj_iff).mp hget

/-- If `xs` equals `[]`, then `∀ x ∈ xs, p x` holds vacuously. -/
theorem forall_mem_of_eq_nil {α : Type} {xs : List α} {p : α → Prop}
    (h : xs = []) :
    ∀ x ∈ xs, p x := by
  simp [h]

/-- If a list has length at least 1, it is nonempty. -/
theorem ne_nil_of_one_le_length {α : Type u} {xs : List α} (h : 1 ≤ xs.length) :
    xs ≠ [] := by
  cases xs with
  | nil => simp at h
  | cons _ _ => simp

/-! ## `allRowsSatisfy`: Boolean predicate over 2D lists

`allRowsSatisfy p data` returns `true` if every element in every row of
`data` satisfies the boolean predicate `p`. -/

/-- Returns `true` if all elements in a list of lists satisfy the boolean predicate `p`.
Equivalent to `(data.join).all p`. -/
def allRowsSatisfy {α : Type} (p : α → Bool) (data : List (List α)) : Bool :=
  (data.flatten).all p

/-! ## `mapOnPairs`: Map a binary function over a list of pairs

`mapOnPairs f l` applies `f : α → β → γ` to each pair `(a, b)` in `l : List (α × β)`,
producing a list of `γ`. This is a common pattern in problems involving range queries,
coordinate pairs, and association lists. -/

/-- Maps a binary function `f : α → β → γ` over every pair in a list of pairs.
Equivalent to `l.map (Function.uncurry f)`. -/
def mapOnPairs {α β γ : Type u} (f : α → β → γ) : List (α × β) → List γ :=
  List.map (Function.uncurry f)

/-- The length of `mapOnPairs f l` is equal to the length of `l`. -/
@[simp]
theorem mapOnPairs_length {α β γ : Type u} (f : α → β → γ) (l : List (α × β)) :
    (mapOnPairs f l).length = l.length := by
  simp [mapOnPairs]

/-! ## `splitOnP` lemmas -/

/-- If no element of `xs` satisfies `p`, then `splitOnP.go p xs acc` returns
a singleton list containing `acc.reverse ++ xs`. -/
theorem splitOnP_go_eq_singleton_of_forall_not {α : Type} {p : α → Prop} [DecidablePred p]
    (xs acc : List α) (h : ∀ x ∈ xs, ¬ p x) :
    List.splitOnP.go p xs acc = [acc.reverse ++ xs] := by
  induction xs generalizing acc with
  | nil => simp [List.splitOnP.go]
  | cons x xs ih =>
      have hx : ¬ p x := h x (by simp)
      have hxs : ∀ c ∈ xs, ¬ p c := by
        intro c hc; exact h c (by simp [hc])
      simp only [List.splitOnP.go]
      simp [hx]
      simpa [List.append_assoc] using ih (x :: acc) hxs

/-! ## `segment`: extract a contiguous slice -/

/-- `segment xs start len` extracts a contiguous slice of `xs`: it first drops `start`
elements, then takes `len` elements. So `segment xs s l = (xs.drop s).take l`. -/
def segment {α : Type} (xs : List α) (start len : Nat) : List α :=
  (xs.drop start).take len

/-! ## Reverse of short lists -/

/-- If a list has length at most 1, reversing it yields the same list. -/
lemma reverse_eq_of_length_le_one {α : Type} (xs : List α) (h : xs.length ≤ 1) :
    xs.reverse = xs := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => simp at h

/-! ## `getLast!` lemmas -/

/-- `getLast!` of a list formed by cons + append + singleton:
`(item :: items ++ [last]).getLast! = last`. -/
@[simp]
theorem getLast!_cons_append_singleton {α : Type} [Inhabited α]
    (item : α) (items : List α) (last : α) :
    (item :: items ++ [last]).getLast! = last := by
  induction items generalizing item with
  | nil => rfl
  | cons x _ ih => simpa using ih x

/-! ## Trimming: `rtrim` and `trimList`

`rtrim p xs` removes trailing elements of `xs` that satisfy predicate `p`.
`trimList p xs` removes both leading and trailing elements that satisfy `p`.
-/

/-- `rtrim p xs` drops trailing elements that satisfy `p`. -/
def rtrim {α : Type} (p : α → Bool) (xs : List α) : List α :=
  (xs.reverse.dropWhile p).reverse

/-- `trimList p xs` drops both leading and trailing elements that satisfy `p`. -/
def trimList {α : Type} (p : α → Bool) (xs : List α) : List α :=
  rtrim p (xs.dropWhile p)

lemma length_dropWhile_le {α : Type} (p : α → Bool) (xs : List α) :
    (xs.dropWhile p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      unfold List.dropWhile
      cases p x <;> simp [ih, Nat.le_succ_of_le]

/-- The length of `xs.takeWhile p` is at most the length of `xs`.
Natural counterpart of `length_dropWhile_le`. -/
lemma length_takeWhile_le {α : Type} (p : α → Bool) (xs : List α) :
    (xs.takeWhile p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.takeWhile_cons]
      split <;> simp [ih]

lemma rtrim_length_le {α : Type} (p : α → Bool) (xs : List α) :
    (rtrim p xs).length ≤ xs.length := by
  unfold rtrim
  rw [List.length_reverse]
  simpa [List.length_reverse] using length_dropWhile_le p xs.reverse

lemma trimList_length_le {α : Type} (p : α → Bool) (xs : List α) :
    (trimList p xs).length ≤ xs.length := by
  unfold trimList
  exact le_trans (rtrim_length_le p _) (length_dropWhile_le p xs)

/-! ## `map` and membership with predicates

These lemmas propagate `∀ x ∈ xs, p (f x)` through `List.map` and `List.join`. -/

/-- If `p (f x)` holds for all `x ∈ xs`, then `p y` holds for all `y ∈ xs.map f`.
This is useful for chaining `∀` quantifiers through `List.map` and is often easier
to use than `List.mem_map` directly. -/
lemma forall_mem_map_of_forall_mem {α : Type u} {β : Type v} {xs : List α} {f : α → β}
    {p : β → Prop} (hxs : ∀ x ∈ xs, p (f x)) :
    ∀ y ∈ xs.map f, p y := by
  intro y hy
  rw [List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hxs x hx

/-! ## `any` lemmas

These are convenience forward-only versions of the bidirectional
`List.any_eq_true` and `List.any_eq_false` from mathlib. -/

/-- If `a ∈ xs` and `p a = true`, then `xs.any p = true`.
This is the forward direction of `List.any_eq_true`. -/
theorem any_true_of_mem {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (hmem : a ∈ xs) (hp : p a) :
    xs.any p = true := by
  rw [List.any_eq_true]
  exact ⟨a, hmem, hp⟩

/-- If no element of `xs` satisfies `p` (i.e., `!p a` holds for all `a ∈ xs`),
then `xs.any p = false`. This is the forward direction of `List.any_eq_false`
adapted to boolean negation. -/
theorem any_false_of_all_not {α : Type} {xs : List α} {p : α → Bool}
    (h : ∀ a, a ∈ xs → !p a) :
    xs.any p = false := by
  rw [List.any_eq_false]
  intro a ha hp
  have hnot : !p a := h a ha
  simp [hp] at hnot

end List

end Specific
