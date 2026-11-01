import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Adjacent pair predicates

Operations for checking whether adjacent elements in a list satisfy a relation.
-/

/-- `hasAdjacentPair p xs` returns `true` if there exists a pair of adjacent
elements `xs[i]` and `xs[i+1]` (for some index `i`) such that `p xs[i] xs[i+1]`
holds. Returns `false` for lists of length < 2. -/
def hasAdjacentPair {α : Type u} [Inhabited α] (p : α → α → Prop)
    [DecidableRel p] (xs : List α) : Bool :=
  decide (∃ i < xs.length - 1, p xs[i]! xs[i+1]!)

/-- `adjacentAll p xs` returns `true` if the proposition `p` holds for **every**
pair of adjacent elements in `xs`. Returns `true` for empty and singleton lists.
This is the universal counterpart of `hasAdjacentPair`. -/
def adjacentAll {α : Type u} (p : α → α → Prop) [DecidableRel p] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => decide (p x y) && adjacentAll p (y :: xs)

/-- `isStrictlyIncreasing xs` returns `true` if the list is strictly increasing:
each element is strictly less than the next. -/
def isStrictlyIncreasing {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (l : List α) : Bool :=
  adjacentAll (· < ·) l

/-- `isStrictlyDecreasing xs` returns `true` if the list is strictly decreasing:
each element is strictly greater than the next. -/
def isStrictlyDecreasing {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (l : List α) : Bool :=
  adjacentAll (fun a b => b < a) l

/-! ## Bool-valued adjacent pair satisfaction

A `Bool`-valued version of `adjacentAll` that takes a `Bool`-returning relation
directly, avoiding the need for `DecidableRel`. -/

/-- `adjacentPairsSatisfy rel xs` returns `true` if `rel x y` is `true` for every
pair of adjacent elements `x`, `y` in `xs`. Returns `true` for empty and singleton
lists. -/
def adjacentPairsSatisfy (rel : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => rel x y && adjacentPairsSatisfy rel (y :: rest)

/-! ## Adjacent relation at a specific index

Check whether a binary relation holds between two adjacent elements at a given
index. This is a pointwise check, in contrast to the global checks above. -/

/-- `adjacentRelAt r xs i` returns `true` if `i > 0`, `i < xs.length`, and the
relation `r` holds between `xs[i - 1]` and `xs[i]`. -/
def adjacentRelAt {α : Type u} [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (i : Nat) : Bool :=
  i > 0 && i < xs.length && decide (r xs[i - 1]! xs[i]!)

/-- `isStrictlyIncreasingAt xs i` returns `true` if `xs[i - 1] < xs[i]` at a
specific index `i`. This is a pointwise check, different from `isStrictlyIncreasing`
which checks the entire list. -/
def isStrictlyIncreasingAt {α : Type u} [Inhabited α] [LT α] [DecidableRel ((· < ·) : α → α → Prop)]
    (xs : List α) (i : Nat) : Bool :=
  adjacentRelAt (· < ·) xs i

/-- `isNonDecreasingAt xs i` returns `true` if `xs[i - 1] ≤ xs[i]` at a specific
index `i`. -/
def isNonDecreasingAt {α : Type u} [Inhabited α] [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (xs : List α) (i : Nat) : Bool :=
  adjacentRelAt (· ≤ ·) xs i

/-! ## Prop-valued adjacent relation from a starting index

In contrast to the `Bool`-valued checks above which cover the entire list or a
single index, these `Prop`-valued predicates check all adjacent pairs starting
from a specific index. -/

/-- `isNonDecreasingFrom l start` holds if for every pair of adjacent elements at
and after index `start`, the left element is `≤` the right element. Vacuously true
when `start ≥ l.length`. -/
def isNonDecreasingFrom {α : Type u} [LE α] (l : List α) (start : Nat) : Prop :=
  ∀ (i : Nat) (v1 v2 : α),
    start ≤ i →
    l[i]? = some v1 →
    l[i+1]? = some v2 →
    v1 ≤ v2

/-! ## Existential adjacent pair checks (Bool-valued recursion)

These defs check whether **some** adjacent pair satisfies a relation, in contrast
to `adjacentPairsSatisfy` which checks **all** pairs and `hasAdjacentPair` which
uses indexed access and requires `Inhabited`. -/

/-- `hasAdjacentRel r xs` returns `true` if there exists a pair of adjacent
elements `xs[i]`, `xs[i+1]` such that `r xs[i] xs[i+1]` is `true`.
Returns `false` for lists of length < 2. -/
def hasAdjacentRel (r : α → α → Bool) : List α → Bool
  | a :: b :: rest => r a b || hasAdjacentRel r (b :: rest)
  | _ => false

/-- `hasAdjacentIncrease xs` returns `true` if there exists a pair of adjacent
elements `xs[i]`, `xs[i+1]` such that `xs[i] < xs[i+1]`. Returns `false` for
lists of length < 2. This is the existential counterpart of `isStrictlyIncreasing`. -/
def hasAdjacentIncrease {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (xs : List α) : Bool :=
  hasAdjacentRel (fun a b => decide (a < b)) xs

/-- `hasAdjacentDecrease xs` returns `true` if there exists a pair of adjacent
elements `xs[i]`, `xs[i+1]` such that `xs[i] > xs[i+1]`. Returns `false` for
lists of length < 2. This is the existential counterpart of `isStrictlyDecreasing`. -/
def hasAdjacentDecrease {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (xs : List α) : Bool :=
  hasAdjacentRel (fun a b => decide (b < a)) xs

end List

end Specific
