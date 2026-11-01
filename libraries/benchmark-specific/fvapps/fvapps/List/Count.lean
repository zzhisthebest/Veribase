import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import fvapps.List.Filter

namespace Specific

open _root_.List

namespace List

/-! ## Counting occurrences in a list -/

/-- In a two-element list with distinct elements, `countP` with an equality
predicate yields at most 1. -/
theorem countP_eq_pair_le_one_of_ne {α : Type} [DecidableEq α] {a b n : α}
    (hab : a ≠ b) :
    countP (· = n) [a, b] ≤ 1 := by
  simp only [countP_cons, countP_nil]
  by_cases ha : a = n <;> by_cases hb : b = n <;> simp [ha, hb]
  exact (hab (ha.trans hb.symm)).elim

/-- Count the number of occurrences of `needle` in the list `xs`.

This is a recursive definition for convenient induction proofs.
See also `sumBy (Function.indicator needle) xs` for a fold-based
alternative. -/
def countOf [DecidableEq α] (needle : α) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => (if x = needle then 1 else 0) + countOf needle rest

@[simp]
theorem countOf_nil [DecidableEq α] (needle : α) : countOf needle [] = 0 := rfl

@[simp]
theorem countOf_cons_eq [DecidableEq α] (x : α) (xs : List α) :
    countOf x (x :: xs) = 1 + countOf x xs := by
  simp [countOf]

@[simp]
theorem countOf_cons_ne [DecidableEq α] {x y : α} (h : x ≠ y) (xs : List α) :
    countOf x (y :: xs) = countOf x xs := by
  simp [countOf, h.symm]

/-! ## Indexed counting

Count elements whose satisfaction of a predicate depends on their position
in the list. -/

/-- Count elements satisfying an indexed predicate `p : Nat → α → Prop`,
starting from a given starting index `j`. For each element `x` at position `j + k`,
the function checks whether `p (j + k) x` holds. -/
def countIndexedFrom {α : Type u} (p : Nat → α → Prop) [DecidableRel p] :
    Nat → List α → Nat
  | _, [] => 0
  | j, x :: xs => (if p j x then 1 else 0) + countIndexedFrom p (j + 1) xs

/-- Count elements satisfying an indexed predicate, starting from index 0. -/
def countIndexed {α : Type u} (p : Nat → α → Prop) [DecidableRel p]
    (xs : List α) : Nat :=
  countIndexedFrom p 0 xs

@[simp]
theorem countIndexedFrom_nil {α : Type u} (p : Nat → α → Prop) [DecidableRel p]
    (j : Nat) : countIndexedFrom p j [] = 0 := rfl

@[simp]
theorem countIndexedFrom_cons {α : Type u} (p : Nat → α → Prop) [DecidableRel p]
    (j : Nat) (x : α) (xs : List α) :
    countIndexedFrom p j (x :: xs) =
      (if p j x then 1 else 0) + countIndexedFrom p (j + 1) xs := rfl

/-- If `p j x` implies `q x` for all `j, x`, then the indexed count
starting from `j` is at most the un-indexed count. -/
theorem countIndexedFrom_le_countWhere {α : Type u}
    (p : Nat → α → Prop) [DecidableRel p]
    (q : α → Prop) [DecidablePred q]
    (h : ∀ j x, p j x → q x) (xs : List α) (j : Nat) :
    countIndexedFrom p j xs ≤ countWhere q xs := by
  induction xs generalizing j with
  | nil =>
      simp [countIndexedFrom, countWhere]
  | cons x xs ih =>
      rw [countIndexedFrom, countWhere_cons]
      by_cases hp : p j x
      · have hq : q x := h j x hp
        simp [hp, hq]
        exact ih (j + 1)
      · simp [hp]
        by_cases hq : q x
        · simp [hq]
          have hih := ih (j + 1)
          omega
        · simp [hq]
          exact ih (j + 1)

/-- If `p j x` implies `q x` for all `j, x`, then the indexed count
is at most the un-indexed count. -/
theorem countIndexed_le_countWhere {α : Type u}
    (p : Nat → α → Prop) [DecidableRel p]
    (q : α → Prop) [DecidablePred q]
    (h : ∀ j x, p j x → q x) (xs : List α) :
    countIndexed p xs ≤ countWhere q xs := by
  simpa [countIndexed] using countIndexedFrom_le_countWhere p q h xs 0

/-! ## Counting elements related to a pivot

Count how many list elements satisfy a relation `rel p` for a given
pivot `p`. This is a recursive definition convenient for induction proofs;
it is equivalent to `countP (rel p)`. -/

/-- Count how many elements `q` in `qs` satisfy `rel p q`. -/
def countRelated (rel : α → α → Bool) (p : α) : List α → Nat
  | [] => 0
  | q :: qs => (if rel p q then 1 else 0) + countRelated rel p qs

@[simp]
theorem countRelated_nil (rel : α → α → Bool) (p : α) :
    countRelated rel p [] = 0 := rfl

@[simp]
theorem countRelated_cons (rel : α → α → Bool) (p q : α) (qs : List α) :
    countRelated rel p (q :: qs) =
      (if rel p q then 1 else 0) + countRelated rel p qs := rfl

theorem countRelated_eq_filter_length (rel : α → α → Bool) (p : α) (qs : List α) :
    countRelated rel p qs = (qs.filter (rel p)).length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp [countRelated, ih]
    by_cases h : rel p q
    · simp [h]; omega
    · simp [h]

/-! ## `countMatches`: filter-based element counting

A non-recursive definition of "count how many times `needle` appears in `xs`",
defined via `countWhere` (which is `(filter p).length`). Equivalent to the
recursive `countOf` above; `countMatches_eq_countOf` establishes the link. -/

/-- Count the number of occurrences of `needle` in `xs` via `filter`.
Equivalent to `countOf` defined above. -/
def countMatches [DecidableEq α] (needle : α) (xs : List α) : Nat :=
  countWhere (· = needle) xs

@[simp]
theorem countMatches_nil [DecidableEq α] (needle : α) : countMatches needle [] = 0 := by
  simp [countMatches]

@[simp]
theorem countMatches_cons_eq [DecidableEq α] (x : α) (xs : List α) :
    countMatches x (x :: xs) = 1 + countMatches x xs := by
  simp [countMatches, countWhere_cons]

@[simp]
theorem countMatches_cons_ne [DecidableEq α] {x y : α} (h : x ≠ y) (xs : List α) :
    countMatches x (y :: xs) = countMatches x xs := by
  simp [countMatches, countWhere_cons, h.symm]

/-- `countMatches` is always nonnegative. -/
theorem countMatches_nonneg [DecidableEq α] (needle : α) (xs : List α) :
    countMatches needle xs ≥ 0 :=
  Nat.zero_le _

/-- `countMatches` (filter-based) equals `countOf` (recursive). -/
theorem countMatches_eq_countOf [DecidableEq α] (needle : α) (xs : List α) :
    countMatches needle xs = countOf needle xs := by
  induction xs with
  | nil => simp [countMatches, countOf]
  | cons x xs ih =>
      rw [countMatches, countWhere_cons, countOf]
      split <;> simp <;> simpa [countMatches] using ih

/-! ## Connecting filter length to `List.count` -/

/-- The length of the filtered list (keeping elements equal to `a`) equals `List.count a xs`.
This bridges filter-based counting with mathlib's `List.count`. -/
theorem length_filter_eq_count [DecidableEq α] (xs : List α) (a : α) :
    (xs.filter (fun x => x = a)).length = xs.count a := by
  rw [← List.countP_eq_length_filter, List.count_eq_countP]
  apply List.countP_congr
  intro x _hx
  simp

/-- general `countMatches` equals mathlib `List.count`. -/
theorem countMatches_eq_count [DecidableEq α] (needle : α) (xs : List α) :
    countMatches needle xs = xs.count needle := by
  simp [countMatches, countWhere, length_filter_eq_count]

/-- `countMatches` distributes over list concatenation. -/
@[simp]
theorem countMatches_append [DecidableEq α] (needle : α) (xs ys : List α) :
    countMatches needle (xs ++ ys) = countMatches needle xs + countMatches needle ys := by
  simp [countMatches, countWhere_append]

/-- Counting occurrences of `x` in `replicate n x` yields `n`. -/
@[simp]
theorem countMatches_replicate_self [DecidableEq α] (x : α) (n : Nat) :
    countMatches x (List.replicate n x) = n := by
  simp [countMatches, countWhere_replicate_of_true]

/-! ## Counting pairs satisfying a binary relation

Count how many ordered pairs `(x, y)` in a list (with `x` appearing before `y`)
satisfy a decidable binary relation `R`. -/

/-- Count the number of pairs `(x, y)` in `xs` (with `x` appearing before `y`)
such that `R x y` holds. For each element `x`, this counts how many later elements `y`
satisfy `R x y` and recursively counts pairs in the tail. -/
def countPairsWhere {α : Type u} (R : α → α → Prop) [DecidableRel R] : List α → Nat
  | [] => 0
  | x :: xs => countWhere (R x) xs + countPairsWhere R xs

@[simp]
theorem countPairsWhere_nil {α : Type u} (R : α → α → Prop) [DecidableRel R] :
    countPairsWhere R [] = 0 := rfl

/-- Count the number of pairs `(x, y)` in the first `n` elements of `xs`
(with `x` appearing before `y`) such that `R x y` holds.
Equivalent to `countPairsWhere R (xs.take n)`. -/
def countPairsInPrefix {α : Type u} (R : α → α → Prop) [DecidableRel R]
    (n : Nat) (xs : List α) : Nat :=
  countPairsWhere R (xs.take n)

/-! ## Positivity and membership for `countMatches` -/

/-- If `countMatches x xs > 0`, then `x ∈ xs`. -/
theorem mem_of_countMatches_pos [DecidableEq α] {xs : List α} {x : α} :
    countMatches x xs > 0 → x ∈ xs := by
  intro hpos
  by_cases hx : x ∈ xs
  · exact hx
  · have hfilter : xs.filter (fun y => y = x) = [] :=
      filter_eq_nil_of_not_mem (xs := xs) (x := x) hx
    simp [countMatches, countWhere, hfilter] at hpos

/-- If `xs` is non-empty, then there exists some element whose count is positive. -/
theorem exists_countMatches_pos_of_ne_nil [DecidableEq α] {xs : List α} :
    xs ≠ [] → ∃ x, countMatches x xs > 0 := by
  intro hxs
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs =>
      refine ⟨x, ?_⟩
      simp [countMatches, countWhere]

/-! ## `countBy`: Bool-based counting

`countBy p xs` counts how many elements of `xs` satisfy the Bool predicate `p`.
It is defined as `(xs.filter p).length` and is equivalent to mathlib's `List.countP`.
-/

/-- Count how many elements of `xs` satisfy the Bool predicate `p`. -/
def countBy {α : Type u} (p : α → Bool) (xs : List α) : Nat :=
  (xs.filter p).length

@[simp]
theorem countBy_nil {α : Type u} (p : α → Bool) : countBy p [] = 0 := rfl

/-- The count of elements satisfying a Bool predicate is at most the list length. -/
theorem countBy_bounded {α : Type u} (p : α → Bool) (xs : List α) :
    countBy p xs ≤ xs.length := by
  unfold countBy
  exact List.length_filter_le p xs

/-- If every element satisfies the predicate, `countBy` equals the list length. -/
theorem countBy_eq_length_of_all {α : Type u} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = true) :
    countBy p xs = xs.length := by
  unfold countBy
  rw [List.filter_eq_self.mpr h]

/-- If no element satisfies the predicate, `countBy` is zero. -/
theorem countBy_eq_zero_of_none {α : Type u} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) :
    countBy p xs = 0 := by
  have hfilter : xs.filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [h x hx]
  simp [countBy, hfilter]

/-- `countBy` is always nonnegative. -/
theorem countBy_non_negative {α : Type u} (p : α → Bool) (xs : List α) :
    countBy p xs ≥ 0 :=
  Nat.zero_le _

/-- Recursive unfolding of `countBy` on `x :: xs`. -/
@[simp]
theorem countBy_cons {α : Type u} (p : α → Bool) (x : α) (xs : List α) :
    countBy p (x :: xs) = (if p x then 1 else 0) + countBy p xs := by
  simp only [countBy, List.filter_cons]; split <;> simp [Nat.add_comm]

/-- If `p x` is true, `countBy` on `x :: xs` adds 1. -/
theorem countBy_cons_of_true {α : Type u} {p : α → Bool} {x : α} {xs : List α}
    (h : p x = true) : countBy p (x :: xs) = 1 + countBy p xs := by
  simp [h]

/-- If `p x` is false, `countBy` on `x :: xs` ignores `x`. -/
theorem countBy_cons_of_false {α : Type u} {p : α → Bool} {x : α} {xs : List α}
    (h : p x = false) : countBy p (x :: xs) = countBy p xs := by
  simp [h]

/-! ## `hasCountBy`: check whether exactly `n` elements satisfy a predicate

`hasCountBy p n xs` returns `true` iff the number of elements in `xs` that satisfy
the Bool predicate `p` equals `n`. -/

/-- `hasCountBy p n xs` is true when `countBy p xs = n`. -/
def hasCountBy {α : Type u} (p : α → Bool) (n : Nat) (xs : List α) : Bool :=
  countBy p xs == n

/-- Forward direction: if the count equals `n`, then `hasCountBy` yields true. -/
theorem hasCountBy_of_countBy_eq {α : Type u} {p : α → Bool} {n : Nat}
    {xs : List α} (h : countBy p xs = n) : hasCountBy p n xs = true := by
  simp [hasCountBy, h]

/-- If the count is not `n`, then `hasCountBy` yields false. -/
theorem hasCountBy_of_countBy_ne {α : Type u} {p : α → Bool} {n : Nat}
    {xs : List α} (h : countBy p xs ≠ n) : hasCountBy p n xs = false := by
  simp [hasCountBy, h]

/-! ## `exactlyOneBy`: check that exactly one element satisfies a predicate

`exactlyOneBy p xs` is true iff exactly one element of `xs` satisfies the
Bool predicate `p`. It is a specialization of `hasCountBy` with `n = 1`. -/

/-- `exactlyOneBy p xs` is true when exactly one element satisfies `p`. -/
def exactlyOneBy {α : Type u} (p : α → Bool) (xs : List α) : Bool :=
  hasCountBy p 1 xs

@[simp]
theorem exactlyOneBy_nil {α : Type u} (p : α → Bool) : exactlyOneBy p [] = false :=
  rfl

/-- If `countBy p xs = 1`, then `exactlyOneBy p xs` is true. -/
theorem exactlyOneBy_of_countBy_eq_one {α : Type u} {p : α → Bool} {xs : List α}
    (h : countBy p xs = 1) : exactlyOneBy p xs = true := by
  exact hasCountBy_of_countBy_eq h

/-- If `countBy p xs ≠ 1`, then `exactlyOneBy p xs` is false. -/
theorem exactlyOneBy_of_countBy_ne_one {α : Type u} {p : α → Bool} {xs : List α}
    (h : countBy p xs ≠ 1) : exactlyOneBy p xs = false := by
  exact hasCountBy_of_countBy_ne h

/-! ## `countPairsBy`: count matching pairs in zipped lists

`countPairsBy rel xs ys` zips `xs` and `ys`, then counts how many position-matched
pairs `(x, y)` satisfy the decidable relation `rel`. This is useful for comparing
two lists position-by-position (e.g., counting how many positions have equal elements). -/

/-- Count how many position-matched pairs `(x, y)` from `xs` and `ys` satisfy `rel`.
The result is `((xs.zip ys).filter (fun p => rel p.1 p.2)).length`. -/
def countPairsBy {α β : Type} (rel : α → β → Prop) [DecidableRel rel]
    (xs : List α) (ys : List β) : Nat :=
  ((xs.zip ys).filter (fun p => rel p.1 p.2)).length

@[simp]
theorem countPairsBy_nil_left {α β : Type} (rel : α → β → Prop) [DecidableRel rel]
    (ys : List β) :
    countPairsBy rel [] ys = 0 := by
  simp [countPairsBy]

@[simp]
theorem countPairsBy_nil_right {α β : Type} (rel : α → β → Prop) [DecidableRel rel]
    (xs : List α) :
    countPairsBy rel xs [] = 0 := by
  simp [countPairsBy]

/-- `countPairsBy rel xs ys` is bounded above by the length of the zipped list. -/
theorem countPairsBy_le_zip_length {α β : Type} (rel : α → β → Prop) [DecidableRel rel]
    (xs : List α) (ys : List β) :
    countPairsBy rel xs ys ≤ (xs.zip ys).length := by
  exact List.length_filter_le (fun p => rel p.1 p.2) (xs.zip ys)

/-- Counting equality-matched pairs in `(xs, xs)` yields `xs.length`:
every position trivially matches itself. -/
theorem countPairsBy_eq_self_length {α : Type} [DecidableEq α] (xs : List α) :
    countPairsBy Eq xs xs = xs.length := by
  induction xs with
  | nil => simp [countPairsBy]
  | cons x xs ih => simpa [countPairsBy] using ih

end List

end Specific
