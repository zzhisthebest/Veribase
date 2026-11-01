import Mathlib

/-- A singly linked list node, as used across LeetCode problems.

Each node carries a value of type `α` and an optional reference to the next node.
This matches the pointer-based linked list representation common in imperative
languages. The type parameter `α` generalizes the hardcoded `Nat` that appears
in individual problem statements. -/
inductive ListNode (α : Type u) where
  | mk (val : α) (next : Option (ListNode α))
deriving Repr, Inhabited

/-- Typeclass for types that behave like a linked list node, providing value access
and next-pointer access. `α` is an `outParam` because it is determined by the node type. -/
class ListNodeLike (node : Type v) (α : outParam (Type u)) where
  val : node → α
  next : node → Option node

namespace ListNode

instance : ListNodeLike (ListNode α) α where
  val n := match n with | .mk v _ => v
  next n := match n with | .mk _ nxt => nxt

/-- `sizeOf` lemma: the `next` field of a `ListNode` is strictly smaller in `sizeOf`.
This is the main termination lemma for functions that recurse on `Option (ListNode α)`. -/
lemma sizeOf_next_lt_some (v : α) (nxt : Option (ListNode α)) :
    sizeOf nxt < sizeOf (some (.mk v nxt : ListNode α)) := by
  simp [Option.some.sizeOf_spec, ListNode.mk.sizeOf_spec]
  omega

/-- Extracts the list of values from an optional linked list head, from head to tail.
Unlike `values`, this handles the `none` case (empty list). -/
def toList (head : Option (ListNode α)) : List α :=
  match head with
  | none => []
  | some (.mk v nxt) => v :: toList nxt
termination_by sizeOf head
decreasing_by
  simp_wf
  omega

lemma toList_none : toList (none : Option (ListNode α)) = [] := by
  simp [toList]

lemma toList_some (v : α) (nxt : Option (ListNode α)) :
    toList (some (.mk v nxt)) = v :: toList nxt := by
  simp [toList]

/-- Length of an optional linked list, counting nodes from the given head.
Useful as a termination measure for functions that recurse on `Option (ListNode α)`,
and as an induction measure alternative to `sizeOf`. -/
def lengthOpt (head : Option (ListNode α)) : Nat :=
  match head with
  | none => 0
  | some (.mk _ nxt) => lengthOpt nxt + 1
termination_by sizeOf head
decreasing_by
  simp_wf
  omega

lemma lengthOpt_none : lengthOpt (none : Option (ListNode α)) = 0 := by
  simp [lengthOpt]

lemma lengthOpt_some (v : α) (nxt : Option (ListNode α)) :
    lengthOpt (some (.mk v nxt)) = lengthOpt nxt + 1 := by
  simp [lengthOpt]

lemma lengthOpt_next_lt_lengthOpt_some (v : α) (nxt : Option (ListNode α)) :
    lengthOpt nxt < lengthOpt (some (.mk v nxt)) := by
  rw [lengthOpt_some]; omega

/-- Converts a `List α` to an optional `ListNode α` (the inverse of `toList`). -/
def ofList : List α → Option (ListNode α)
  | [] => none
  | x :: xs => some (.mk x (ofList xs))

/-- Roundtrip: `toList (ofList l) = l`. -/
theorem toList_ofList (l : List α) : toList (ofList l) = l := by
  induction l with
  | nil => simp [toList, ofList]
  | cons h t ih => simp [toList, ofList, ih]

/-- Extracts the list of values from a linked list, from head to tail. -/
def values : ListNode α → List α
  | mk v none => [v]
  | mk v (some nxt) => v :: values nxt

/-- Number of nodes in the linked list. -/
def length : ListNode α → Nat
  | mk _ none => 1
  | mk _ (some nxt) => 1 + length nxt

/-- `allVals p node` asserts that predicate `p` holds for every value in the linked list.

Generalizes problem-specific properties like `allValsNeZero` (all values ≠ 0)
or `allValsLe n` (all values ≤ n). The predicate is `α → Prop` so it supports
both computational (`Decidable`) and non-computational reasoning. -/
def allVals (p : α → Prop) : ListNode α → Prop
  | mk v none => p v
  | mk v (some nxt) => p v ∧ allVals p nxt

/-- Left fold over the values of a `ListNode`.

`foldl f node acc` processes the list from head to tail, applying `f` at each step.
It is the fundamental iterator for linked lists and generalizes many problem-specific
computations (e.g., binary-to-decimal conversion, sum, product). -/
def foldl (f : β → α → β) (node : ListNode α) (acc : β) : β :=
  match node with
  | mk v none => f acc v
  | mk v (some nxt) => foldl f nxt (f acc v)

/-- The length of a linked list equals the length of its value list. -/
theorem length_eq_values_length (node : ListNode α) :
    length node = (values node).length := by
  match node with
  | mk v none => simp [length, values]
  | mk v (some nxt) =>
    have ih := length_eq_values_length nxt
    simp [length, values, ih]
    omega

/-- `foldl` over a `ListNode` equals `List.foldl` over its `values`. -/
theorem foldl_eq (f : β → α → β) (node : ListNode α) (acc : β) :
    foldl f node acc = (values node).foldl f acc := by
  match node with
  | mk v none =>
    simp [foldl, values, List.foldl]
  | mk v (some nxt) =>
    have ih := foldl_eq f nxt (f acc v)
    simp [foldl, values, List.foldl, ih]

/-- Extends `allVals` to optional linked list heads: `none` is trivially satisfied,
a `some node` requires `allVals p node`.

Generalizes the common LeetCode pattern of "all node values satisfy a predicate,
even when the list may be empty". -/
def allValsOpt (p : α → Prop) (head : Option (ListNode α)) : Prop :=
  match head with
  | none => True
  | some node => allVals p node

/-- The length of an optional linked list (via `lengthOpt`) equals the length of
its `toList` conversion. Corresponds to `listLengthFuel_eq_toListFuel_length`
from fuel-based linked list formalizations. -/
theorem lengthOpt_eq_toList_length (head : Option (ListNode α)) :
    lengthOpt head = (toList head).length := by
  match head with
  | none => simp [lengthOpt, toList]
  | some (.mk v nxt) =>
    simp only [lengthOpt_some, toList_some, List.length_cons]
    rw [lengthOpt_eq_toList_length nxt]
termination_by sizeOf head
decreasing_by exact sizeOf_next_lt_some _ _

end ListNode
