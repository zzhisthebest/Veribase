namespace Specific

open _root_.List

/-!
# Binary Tree

A binary tree where each node holds a value and has optional left/right subtrees.
-/

universe u

/-- A binary tree node with a value of type `α` and optional left and right subtrees. -/
inductive TreeNode (α : Type u) where
  | mk : α → Option (TreeNode α) → Option (TreeNode α) → TreeNode α
  deriving Inhabited

namespace TreeNode

variable {α β : Type u}

/-- Preorder traversal: apply `f` to each node value, producing a list.

The traversal visits the root first, then recursively traverses the left subtree,
then the right subtree. -/
def preorderMap (f : α → β) : TreeNode α → List β
  | mk v none none => [f v]
  | mk v (some left) none => f v :: preorderMap f left
  | mk v none (some right) => f v :: preorderMap f right
  | mk v (some left) (some right) =>
      f v :: preorderMap f left ++ preorderMap f right

/-- Preorder traversal of a tree, collecting node values as a list. -/
def toList : TreeNode α → List α :=
  preorderMap id

@[simp]
theorem toList_mk_none_none (v : α) : toList (mk v none none) = [v] := by
  simp [toList, preorderMap]

@[simp]
theorem toList_mk_none_right (v : α) (right : TreeNode α) :
    toList (mk v none (some right)) = v :: toList right := by
  simp [toList, preorderMap]

@[simp]
theorem toList_mk_left_none (v : α) (left : TreeNode α) :
    toList (mk v (some left) none) = v :: toList left := by
  simp [toList, preorderMap]

end TreeNode

/-!
# Nested / Rose Tree

A tree where each internal node holds a list of child subtrees.
This generalizes binary trees to arbitrary arity.
-/

/-- A rose tree (or "nested" structure): a leaf holds a value of type `α`,
and a node holds a list of child subtrees. -/
inductive Nested (α : Type u) where
  | leaf : α → Nested α
  | node : List (Nested α) → Nested α

namespace Nested

end Nested

end Specific
