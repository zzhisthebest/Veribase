import Mathlib.Data.List.Basic
import verina.List.Sort

namespace Specific

open _root_.List

namespace List

/-! ## Sum over lists with `Nat` scores -/

/-- Sum a `Nat`-valued score function over a list. -/
def sumBy {β : Type} (f : β → Nat) : List β → Nat
  | [] => 0
  | x :: xs => f x + sumBy f xs

@[simp] theorem sumBy_nil {β : Type} (f : β → Nat) : sumBy f [] = 0 := rfl

@[simp] theorem sumBy_cons {β : Type} (f : β → Nat) (x : β) (xs : List β) :
    sumBy f (x :: xs) = f x + sumBy f xs := rfl

@[simp] theorem sumBy_singleton {β : Type} (f : β → Nat) (x : β) : sumBy f [x] = f x := by simp

/-- Sum a list of natural numbers. -/
def listSum : List Nat → Nat := sumBy id

@[simp] theorem listSum_nil : listSum [] = 0 := rfl

@[simp] theorem listSum_cons (x : Nat) (xs : List Nat) :
    listSum (x :: xs) = x + listSum xs := rfl

/-- Sum over an empty list truncated to n is zero. -/
theorem sumBy_take_nil {β : Type} (f : β → Nat) (n : Nat) :
    sumBy f (List.take n []) = 0 := by
  cases n <;> rfl

/-- Sum is invariant under permutation of the list. -/
theorem sumBy_perm {β : Type} (f : β → Nat) {l₁ l₂ : List β}
    (h : Perm l₁ l₂) :
    sumBy f l₁ = sumBy f l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sumBy, ih]
  | swap x y l => simp [sumBy, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Sorting by descending score does not change the sum. -/
theorem sumBy_sortByDescending {β : Type} (f : β → Nat) (l : List β) :
    sumBy f (sortByDescending f l) = sumBy f l := by
  exact sumBy_perm f
    (perm_insertionSort (fun a b : β => f b ≤ f a) l)

/-- `sumBy` distributes over list append. -/
@[simp]
theorem sumBy_append {β : Type} (f : β → Nat) (l₁ l₂ : List β) :
    sumBy f (l₁ ++ l₂) = sumBy f l₁ + sumBy f l₂ := by
  induction l₁ with
  | nil => simp [sumBy]
  | cons x xs ih => simp [sumBy, ih, Nat.add_assoc]

/-- Sum of a list of naturals is preserved by descending sort. -/
theorem listSum_sortDesc (l : List Nat) : listSum (sortDesc l) = listSum l := by
  exact sumBy_sortByDescending id l

/-- The sum of `Nat`-valued scores is non-negative. -/
theorem zero_le_sumBy {β : Type} (f : β → Nat) (xs : List β) : 0 ≤ sumBy f xs :=
  Nat.zero_le _

/-- The sum of a list of naturals is non-negative. -/
theorem zero_le_listSum (xs : List Nat) : 0 ≤ listSum xs :=
  zero_le_sumBy id xs

/-! ## Sum over a range of natural numbers -/

/-- Sum `f i` for `i` from `0` to `n-1`. Equivalent to `sumBy f (range n)`. -/
def rangeSum (n : Nat) (f : Nat → Nat) : Nat :=
  sumBy f (range n)

@[simp] theorem rangeSum_zero (f : Nat → Nat) : rangeSum 0 f = 0 := by
  simp [rangeSum]

theorem rangeSum_succ (n : Nat) (f : Nat → Nat) :
    rangeSum (n + 1) f = f n + rangeSum n f := by
  simp [rangeSum, sumBy_append, range_succ, sumBy_singleton, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end List

end Specific
