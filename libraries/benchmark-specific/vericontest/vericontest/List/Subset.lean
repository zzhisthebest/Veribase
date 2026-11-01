import Mathlib

open List

namespace List

/-! ### Sum over all subsets

`subsetOpSum op xs init` computes: for each subset of `xs`, combine elements
using `op` (starting from `init`), then sum all results using `+`.

Formally, if the subsets of `[x₁, x₂, …, xₙ]` are `{S₁, S₂, …, S₂ⁿ}`, then
`subsetOpSum op xs init = ∑ₖ foldl op init Sₖ`.

This generalizes patterns from LeetCode problems that compute the sum of XOR
totals over all subsets (LC 1863 "Sum of All Subset XOR Totals") and similar
subset-aggregation problems.
-/

/-- Sum over all subsets: for each subset of `xs`, combine elements using `op`
(starting from `init`), then sum all results using `+`. -/
def subsetOpSum {α : Type} [AddMonoid α] (op : α → α → α) (xs : List α) (init : α) : α :=
  match xs with
  | [] => init
  | x :: xs' => subsetOpSum op xs' (op init x) + subsetOpSum op xs' init

@[simp]
theorem subsetOpSum_nil {α : Type} [AddMonoid α] (op : α → α → α) (init : α) :
    subsetOpSum op [] init = init :=
  rfl

theorem subsetOpSum_cons {α : Type} [AddMonoid α] (op : α → α → α) (x : α) (xs : List α) (init : α) :
    subsetOpSum op (x :: xs) init = subsetOpSum op xs (op init x) + subsetOpSum op xs init :=
  rfl

/-! ### Specialization to XOR

`subsetXorSum` is the specialization of `subsetOpSum` to `Int.xor` with initial
value `0`. This computes the XOR sum over all subsets of a list of `Int`s,
corresponding to LeetCode 1863 "Sum of All Subset XOR Totals". -/

/-- XOR sum over all subsets: for each subset of `nums`, XOR all elements (starting from `0`),
then sum all those results. Specialization of `subsetOpSum` to `Int.xor`. -/
def subsetXorSum (nums : List Int) : Int :=
  subsetOpSum (Int.xor · ·) nums 0

@[simp]
theorem subsetXorSum_nil : subsetXorSum ([] : List Int) = 0 :=
  rfl

end List
