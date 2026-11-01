namespace Specific

open _root_.List

universe u v

/--
A simple singly-linked list type, equivalent to `List` but defined inductively
with explicit `nil`/`cons` constructors.  Useful in problem domains where a
custom linked-list representation is needed.
-/
inductive LinkedList (α : Type u) : Type u
  | nil : LinkedList α
  | cons : α → LinkedList α → LinkedList α

namespace LinkedList

/--
Right fold over a `LinkedList`.
-/
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) : LinkedList α → β
  | nil => init
  | cons head tail => f head (foldr f init tail)

@[simp]
theorem foldr_nil {α : Type u} {β : Type v} (f : α → β → β) (init : β) :
    foldr f init (nil : LinkedList α) = init :=
  rfl

@[simp]
theorem foldr_cons {α : Type u} {β : Type v} (f : α → β → β) (init : β)
    (head : α) (tail : LinkedList α) :
    foldr f init (cons head tail) = f head (foldr f init tail) :=
  rfl

/--
Convert a `LinkedList` to the standard `List`.  This uses `foldr` with `List.cons`,
so the list elements appear in the same order as the linked-list traversal.
-/
def toList {α : Type u} : LinkedList α → List α :=
  foldr List.cons []

@[simp]
theorem toList_nil {α : Type u} :
    toList (nil : LinkedList α) = [] :=
  rfl

@[simp]
theorem toList_cons {α : Type u} (head : α) (tail : LinkedList α) :
    toList (cons head tail) = head :: toList tail :=
  rfl

end LinkedList

end Specific
