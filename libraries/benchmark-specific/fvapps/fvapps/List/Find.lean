import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## `firstSatisfyingWithDefault`: find the first element satisfying a predicate

`firstSatisfyingWithDefault default p xs` scans `xs` left-to-right and returns the first
element `x` for which `p x` holds. If no element satisfies `p`, it returns `default`.

Unlike `List.find?`, which works with `Bool` predicates and returns `Option α`,
`firstSatisfyingWithDefault` works with `Prop` predicates (via `DecidablePred`) and
uses a user-supplied default value, avoiding the `Option` layer. -/

/-- Return the first element of `xs` satisfying `p`, or `default` if none do. -/
def firstSatisfyingWithDefault {α : Type u} (default : α)
    (p : α → Prop) [DecidablePred p] : List α → α
  | [] => default
  | x :: xs => if p x then x else firstSatisfyingWithDefault default p xs

@[simp]
theorem firstSatisfyingWithDefault_nil {α : Type u} (default : α)
    (p : α → Prop) [DecidablePred p] :
    firstSatisfyingWithDefault default p [] = default := rfl

/-- If the head of the list satisfies `p`, it is returned immediately. -/
theorem firstSatisfyingWithDefault_of_head {α : Type u} (default : α)
    (p : α → Prop) [DecidablePred p] {x : α} (xs : List α) (hx : p x) :
    firstSatisfyingWithDefault default p (x :: xs) = x := by
  simp [firstSatisfyingWithDefault, hx]

/-- If the head of the list does not satisfy `p`, the search continues in the tail. -/
theorem firstSatisfyingWithDefault_of_not_head {α : Type u} (default : α)
    (p : α → Prop) [DecidablePred p] {x : α} (xs : List α) (hx : ¬ p x) :
    firstSatisfyingWithDefault default p (x :: xs) =
      firstSatisfyingWithDefault default p xs := by
  simp [firstSatisfyingWithDefault, hx]

end List

end Specific
