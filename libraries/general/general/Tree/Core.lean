import Mathlib

namespace Tree

universe u
variable {α : Type u}

/-- `isMirror t₁ t₂` holds when the two trees `t₁` and `t₂` are mirrors of each other:
their root values are equal, and the left subtree of `t₁` mirrors the right subtree of `t₂`,
and vice versa. -/
def isMirror : Tree α → Tree α → Prop
  | .nil, .nil => True
  | .node v₁ l₁ r₁, .node v₂ l₂ r₂ => v₁ = v₂ ∧ isMirror l₁ r₂ ∧ isMirror r₁ l₂
  | _, _ => False

/-! ### Mirror / Invert -/

/-- Mirror (invert) a binary tree: recursively swap left and right subtrees at every node.
This is the computational counterpart to `isMirror`. -/
def mirror : Tree α → Tree α
  | .nil => .nil
  | .node v l r => .node v (mirror r) (mirror l)


theorem mirror_nil : mirror (.nil : Tree α) = .nil := rfl


theorem mirror_node (v : α) (l r : Tree α) :
    mirror (.node v l r) = .node v (mirror r) (mirror l) := rfl

/-- Number of nodes in the tree. Equivalent to `numNodes`. -/
def size : Tree α → Nat
  | .nil => 0
  | .node _ l r => 1 + size l + size r


theorem size_nil : size (.nil : Tree α) = 0 := rfl


theorem size_node (v : α) (l r : Tree α) : size (.node v l r) = 1 + size l + size r := rfl

/-- Mirroring preserves the number of nodes. -/
theorem size_mirror (t : Tree α) : size (mirror t) = size t := by
  induction t with
  | nil => rfl
  | node _ l r ih_l ih_r =>
    simp [mirror, size, ih_l, ih_r]
    omega

/-! ### Node value accessor -/

/-- Get the value at the root of a tree, returning a caller-specified default for `nil`. -/
def valDefault (default : α) : Tree α → α
  | .nil => default
  | .node v _ _ => v


theorem valDefault_nil (default : α) : valDefault default (.nil : Tree α) = default := rfl


theorem valDefault_node (default : α) (v : α) (l r : Tree α) :
    valDefault default (.node v l r) = v := rfl

/-- Get the value at the root of a tree as an `Option`. Returns `none` for `nil`,
`some v` for `node v _ _`. Complementary to `valDefault` which uses a caller-provided
default instead of `Option`. -/
def rootVal : Tree α → Option α
  | .nil => none
  | .node v _ _ => some v


theorem rootVal_nil : rootVal (.nil : Tree α) = none := rfl


theorem rootVal_node (v : α) (l r : Tree α) : rootVal (.node v l r) = some v := rfl

/-! ### Sum of node values -/

section sum
variable [AddMonoid α]

/-- Sum of all node values in a tree. Works for any `AddMonoid α`,
including `Nat`, `Int`, `ℚ`, `ℝ`, etc. -/
def sumTree : Tree α → α
  | .nil => 0
  | .node v l r => v + sumTree l + sumTree r


theorem sumTree_nil : sumTree (.nil : Tree α) = 0 := rfl


theorem sumTree_node (v : α) (l r : Tree α) : sumTree (.node v l r) = v + sumTree l + sumTree r := rfl

end sum

/-! ### Bottom-up transformation -/

/-- Bottom-up transformation of a tree: recursively transform children,
then apply `f` to the value and transformed children.

This generalises `Tree.map` (which rebuilds `.node` unconditionally) by letting
the caller decide what to do with the value and transformed subtrees. Typical
use cases include pruning (`f v l' r' = .nil` when a condition holds) and
conditional reconstruction. -/
def mapPost (f : α → Tree α → Tree α → Tree α) : Tree α → Tree α
  | .nil => .nil
  | .node v l r =>
      let l' := mapPost f l
      let r' := mapPost f r
      f v l' r'


theorem mapPost_nil (f : α → Tree α → Tree α → Tree α) : mapPost f (.nil : Tree α) = .nil := rfl


theorem mapPost_node (f : α → Tree α → Tree α → Tree α) (v : α) (l r : Tree α) :
    mapPost f (.node v l r) = f v (mapPost f l) (mapPost f r) := rfl

/-! ### Collect values from subtrees -/

/-- Apply `f` to every subtree (including the root) and collect results in a list. -/
def collectSubtreeVals (f : Tree α → β) : Tree α → List β
  | .nil => []
  | .node v l r => f (.node v l r) :: (collectSubtreeVals f l ++ collectSubtreeVals f r)


theorem collectSubtreeVals_nil (f : Tree α → β) : collectSubtreeVals f .nil = [] := rfl

theorem collectSubtreeVals_node (f : Tree α → β) (v : α) (l r : Tree α) :
    collectSubtreeVals f (.node v l r) = f (.node v l r) :: (collectSubtreeVals f l ++ collectSubtreeVals f r) :=
  rfl

/-- `collectSubtreeVals` returns an empty list exactly when the tree is `nil`.
Since every non-nil node contributes at least one value, this is a clean
iff characterization. -/
theorem collectSubtreeVals_eq_nil_iff (f : Tree α → β) (t : Tree α) :
    collectSubtreeVals f t = [] ↔ t = .nil := by
  constructor
  · intro h
    induction t with
    | nil => rfl
    | node v l r =>
      simp [collectSubtreeVals] at h
  · intro h; subst h; rfl

/-! ### Counting nodes satisfying a predicate -/

/-- Count the number of subtrees (nodes) in a tree that satisfy a predicate `p`.
The predicate receives the whole subtree, not just the node value, enabling structural checks. -/
def countWhere (p : Tree α → Bool) : Tree α → Nat
  | .nil => 0
  | n@(.node _ l r) =>
      let inc := if p n then 1 else 0
      inc + countWhere p l + countWhere p r


theorem countWhere_nil (p : Tree α → Bool) : countWhere p (.nil : Tree α) = 0 := rfl


theorem countWhere_node (p : Tree α → Bool) (v : α) (l r : Tree α) :
    countWhere p (.node v l r) =
      (if p (.node v l r) then 1 else 0) + countWhere p l + countWhere p r :=
  rfl

/-- The depth (height) of a tree, with `Nat.succ ∘ Nat.max` formulation.
Equivalent to `height` from `Mathlib.Data.Tree.Basic`, but uses `Nat.succ (Nat.max ...)`
rather than `max ... + 1`. -/
def depth : Tree α → Nat
  | .nil => 0
  | .node _ l r => Nat.succ (Nat.max (depth l) (depth r))


theorem depth_nil : depth (.nil : Tree α) = 0 := rfl


theorem depth_node (v : α) (l r : Tree α) :
    depth (.node v l r) = Nat.succ (Nat.max (depth l) (depth r)) := rfl

/-! ### Depth of a specific value -/

/-- Helper for computing the depth of a value in the tree.
`depthOfValueAux t target cur` returns the depth at which `target` first
appears in a pre-order traversal of `t`, offset by `cur`. Returns `none` if
`target` is not present. -/
def depthOfValueAux [DecidableEq α] (t : Tree α) (target : α) (cur : Nat) : Option Nat :=
  match t with
  | .nil => none
  | .node v l r =>
      if v = target then some cur
      else
        match depthOfValueAux l target (cur + 1) with
        | some d => some d
        | none   => depthOfValueAux r target (cur + 1)

/-- Depth of a value in the tree, if it appears. Root has depth 0.
Returns `none` if the value is not present. -/
def depthOfValue [DecidableEq α] (t : Tree α) (target : α) : Option Nat :=
  depthOfValueAux t target 0

/-! ### Diameter -/

/-- Compute the (height, diameter) pair for a tree in a single bottom-up pass.
The height is the length of the longest path from root to leaf (in edges),
and the diameter is the length of the longest path between any two nodes (in edges). -/
def diameterAux : Tree α → Nat × Nat
  | .nil => (0, 0)
  | .node _ l r =>
      let (hl, dl) := diameterAux l
      let (hr, dr) := diameterAux r
      (Nat.succ (Nat.max hl hr), Nat.max (Nat.max dl dr) (hl + hr))

/-- The diameter of a tree: the length (in edges) of the longest path between any two nodes. -/
def diameter (t : Tree α) : Nat := (diameterAux t).2

/-- The first component of `diameterAux` equals the tree depth. -/
theorem diameterAux_fst_eq_depth (t : Tree α) : (diameterAux t).1 = depth t := by
  induction t with
  | nil => rfl
  | node _ l r ihl ihr =>
    simp [diameterAux, depth, ihl, ihr]

/-- `Tree.all p t` holds when every value in `t` satisfies predicate `p`. -/
def all (p : α → Prop) : Tree α → Prop
  | .nil => True
  | .node v l r => p v ∧ all p l ∧ all p r


theorem all_nil (p : α → Prop) : all p (.nil : Tree α) := trivial


theorem all_node (p : α → Prop) (v : α) (l r : Tree α) :
    all p (.node v l r) ↔ p v ∧ all p l ∧ all p r := by
  simp [all]

/-! ### All values equal to a given value -/

/-- `allEq t val` holds when every value in tree `t` equals `val`.
This is a convenience specialisation of `Tree.all` for the equality predicate. -/
def allEq : Tree α → α → Prop
  | .nil, _ => True
  | .node v l r, val => v = val ∧ allEq l val ∧ allEq r val


theorem allEq_nil (val : α) : allEq (.nil : Tree α) val := by
  simp [allEq]


theorem allEq_node (v val : α) (l r : Tree α) :
    allEq (.node v l r) val ↔ v = val ∧ allEq l val ∧ allEq r val := by
  simp [allEq]

/-- `allEq t val` is equivalent to `all (· = val) t`. -/
lemma allEq_iff_all (t : Tree α) (val : α) : allEq t val ↔ all (· = val) t := by
  induction t with
  | nil => simp [allEq, all]
  | node v l r ih_l ih_r => simp [allEq, all, ih_l, ih_r]

/-- Boolean version of `allEq`: checks whether all values in `t` equal `val`. -/
def allEqBool [BEq α] : Tree α → α → Bool
  | .nil, _ => true
  | .node v l r, val => (v == val) && allEqBool l val && allEqBool r val


theorem allEqBool_nil [BEq α] (val : α) : allEqBool (.nil : Tree α) val = true := rfl

/-- The boolean `allEqBool` correctly reflects propositional `allEq`. -/
lemma allEqBool_eq_true_iff [DecidableEq α] (t : Tree α) (val : α) :
    allEqBool t val = true ↔ allEq t val := by
  induction t with
  | nil => simp [allEqBool, allEq]
  | node v l r ih_l ih_r =>
    simp [allEqBool, allEq, ih_l, ih_r, decide_eq_true_iff, and_assoc]

/-- If all values in a non-nil tree equal `val`, then the root value equals `val`. -/
lemma allEq_root_eq {v val : α} {l r : Tree α} (h : allEq (.node v l r) val) : v = val :=
  h.1

/-! ### All values in a range -/

/-- `allInRange t lo hi` holds when every value in tree `t` lies in the
closed interval `[lo, hi]`. This is a convenience specialisation of `Tree.all`
for the common pattern of range-checking all node values. -/
def allInRange [LE α] (t : Tree α) (lo hi : α) : Prop :=
  match t with
  | .nil => True
  | .node v l r => lo ≤ v ∧ v ≤ hi ∧ allInRange l lo hi ∧ allInRange r lo hi


theorem allInRange_nil [LE α] (lo hi : α) :
    allInRange (.nil : Tree α) lo hi := by
  unfold allInRange; trivial


theorem allInRange_node [LE α] (v : α) (l r : Tree α) (lo hi : α) :
    allInRange (.node v l r) lo hi =
    (lo ≤ v ∧ v ≤ hi ∧ allInRange l lo hi ∧ allInRange r lo hi) := rfl

/-- Propositional structural equality of two trees. -/
def same : Tree α → Tree α → Prop
  | .nil, .nil => True
  | .node v1 l1 r1, .node v2 l2 r2 => v1 = v2 ∧ same l1 l2 ∧ same r1 r2
  | _, _ => False

/-- Check structural equality of two trees using `BEq` on elements. -/
def beq [BEq α] : Tree α → Tree α → Bool
  | .nil, .nil => true
  | .node v1 l1 r1, .node v2 l2 r2 =>
      (v1 == v2) && (beq l1 l2) && (beq r1 r2)
  | _, _ => false

/-! ### Equivalence between boolean and propositional equality -/

/-- Structural equality `same t₁ t₂` is equivalent to propositional equality `t₁ = t₂`. -/
theorem same_iff_eq (t₁ t₂ : Tree α) : same t₁ t₂ ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | nil =>
    cases t₂ <;> simp [same]
  | node v₁ l₁ r₁ ih_l ih_r =>
    cases t₂
    · simp [same]
    · rename_i v₂ l₂ r₂
      simp only [same]
      constructor
      · rintro ⟨hv, hl, hr⟩
        subst hv
        have hl_eq : l₁ = l₂ := ((ih_l l₂).mp hl)
        have hr_eq : r₁ = r₂ := ((ih_r r₂).mp hr)
        subst hl_eq; subst hr_eq; rfl
      · intro h
        injection h with hv hl_eq hr_eq
        subst hv hl_eq hr_eq
        simp [*]

/-- The boolean equality test `beq` correctly decides propositional equality. -/
theorem beq_eq_true_iff_eq [DecidableEq α] (t₁ t₂ : Tree α) : beq t₁ t₂ = true ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | nil =>
    cases t₂ <;> simp [beq]
  | node v₁ l₁ r₁ ih_l ih_r =>
    cases t₂ with
    | nil => simp [beq]
    | node v₂ l₂ r₂ =>
      constructor
      · intro h
        simp [beq] at h
        rcases h with ⟨⟨hv, hl_beq⟩, hr_beq⟩
        have hl : l₁ = l₂ := ((ih_l l₂).mp hl_beq)
        have hr : r₁ = r₂ := ((ih_r r₂).mp hr_beq)
        subst hv hl hr; rfl
      · intro h
        cases h
        simp [beq, ih_l l₁, ih_r r₁]

/-- The boolean equality test `beq` correctly decides structural equality `same`. -/
theorem beq_eq_same_iff [DecidableEq α] (t₁ t₂ : Tree α) : beq t₁ t₂ = true ↔ same t₁ t₂ := by
  rw [beq_eq_true_iff_eq, same_iff_eq]

/-- Get all values at a given depth `d` (0-indexed from root) in the tree. -/
def getLevel (d : Nat) : Tree α → List α
  | .nil => []
  | .node v l r =>
      match d with
      | 0 => [v]
      | Nat.succ d' => (getLevel d' l) ++ (getLevel d' r)


theorem getLevel_succ (d : Nat) (v : α) (l r : Tree α) :
    getLevel (Nat.succ d) (.node v l r) = getLevel d l ++ getLevel d r := rfl

/-! ### Sum at depth -/

/-- Sum of the values of all nodes that lie on depth `d` (root at depth 0). -/
def sumAtDepth [AddMonoid α] (d : Nat) : Tree α → α
  | .nil => 0
  | .node v l r =>
      match d with
      | 0 => v
      | Nat.succ d' => sumAtDepth d' l + sumAtDepth d' r


theorem sumAtDepth_succ [AddMonoid α] (v : α) (l r : Tree α) (d : Nat) :
    sumAtDepth (Nat.succ d) (.node v l r) = sumAtDepth d l + sumAtDepth d r := rfl

/-! ### DFS Path Sum -/

/-- DFS traversal that collects all root-to-leaf paths whose cumulative sum equals `target`.
The accumulator `path` holds the current path from root to current node, and `sumSoFar`
is the sum of `path`. Returns the list of all paths (each path is from root to leaf)
whose sum equals `target`. -/
def dfsPathSum [AddMonoid α] [DecidableEq α]
    (node : Tree α) (path : List α) (sumSoFar : α) (target : α) : List (List α) :=
  match node with
  | Tree.nil => []
  | Tree.node v l r =>
      let newSum := sumSoFar + v
      let newPath := path ++ [v]
      if l = Tree.nil ∧ r = Tree.nil then
        if newSum = target then [newPath] else []
      else
        dfsPathSum l newPath newSum target ++ dfsPathSum r newPath newSum target

/-- Find all root-to-leaf paths in `root` whose node values sum to `targetSum`.
This is a convenience wrapper around `dfsPathSum` starting with an empty path and
initial sum zero. -/
def pathSum [AddMonoid α] [DecidableEq α] (root : Tree α) (targetSum : α) : List (List α) :=
  dfsPathSum root [] 0 targetSum

/-- In-order traversal collecting values from a binary tree into a list. -/
def inorder : Tree α → List α
  | .nil => []
  | .node v l r => inorder l ++ [v] ++ inorder r

/-- If a value is not in the inorder traversal of a `node v l r`, then it is not in
the inorder of `l`, not equal to `v`, and not in the inorder of `r`. -/
lemma not_mem_inorder_node {val v : α} {l r : Tree α} (h : val ∉ inorder (.node v l r)) :
    val ∉ inorder l ∧ val ≠ v ∧ val ∉ inorder r := by
  have h' : val ∉ inorder l ++ [v] ++ inorder r := by simpa [inorder] using h
  have h_notin_l : val ∉ inorder l := by
    intro h_contra; apply h'; simp [h_contra]
  have h_ne_v : val ≠ v := by
    intro h_eq; apply h'; simp [h_eq]
  have h_notin_r : val ∉ inorder r := by
    intro h_contra; apply h'; simp [h_contra]
  exact ⟨h_notin_l, h_ne_v, h_notin_r⟩

/-- Pre-order traversal collecting values from a binary tree into a list.
Visits root, then left subtree, then right subtree. -/
def preorder : Tree α → List α
  | .nil => []
  | .node v l r => v :: (preorder l ++ preorder r)


theorem preorder_nil : preorder (.nil : Tree α) = [] := rfl


theorem preorder_node (v : α) (l r : Tree α) :
    preorder (.node v l r) = v :: (preorder l ++ preorder r) := rfl

/-- Non-nil trees have non-empty preorder traversal. -/
theorem preorder_ne_nil_of_ne_nil {t : Tree α} (h : t ≠ .nil) : preorder t ≠ [] := by
  cases t
  · contradiction
  · simp [preorder]

/-! ### Value membership (Prop) -/

/-- `subtreeContains t x` holds when the value `x` appears at some node in tree `t`. -/
def subtreeContains : Tree α → α → Prop
  | .nil, _ => False
  | .node v l r, x => x = v ∨ subtreeContains l x ∨ subtreeContains r x

/-! ### Value membership (Bool) -/

/-- `elem t x` is the decidable boolean version of `subtreeContains t x`. -/
def elem [DecidableEq α] : Tree α → α → Bool
  | .nil, _ => false
  | .node v l r, x => (v == x) || elem l x || elem r x

/-- The boolean `elem` correctly reflects the propositional `subtreeContains`. -/
theorem elem_iff_subtreeContains [DecidableEq α] (t : Tree α) (x : α) :
    elem t x = true ↔ subtreeContains t x := by
  induction t with
  | nil => simp [elem, subtreeContains]
  | node v l r ih_l ih_r =>
    simp [elem, subtreeContains]
    rw [ih_l, ih_r]
    simp [or_assoc, eq_comm]

/-- Conjunction of boolean membership implies conjunction of propositional membership. -/
theorem elem_and_true_iff [DecidableEq α] (t : Tree α) (p q : α) :
    (elem t p && elem t q) = true ↔ subtreeContains t p ∧ subtreeContains t q := by
  rw [Bool.and_eq_true, elem_iff_subtreeContains, elem_iff_subtreeContains]

/-- If boolean membership of both `p` and `q` is false, then they cannot both be
propositionally contained. -/
theorem not_and_subtreeContains_of_elem_and_false [DecidableEq α] (t : Tree α) (p q : α)
    (h : (elem t p && elem t q) = false) :
    ¬ (subtreeContains t p ∧ subtreeContains t q) := by
  rw [Bool.and_eq_false_iff] at h
  rcases h with (h_false | h_false)
  · intro ⟨hp, _⟩
    have : elem t p = true := (elem_iff_subtreeContains _ _).mpr hp
    rw [h_false] at this
    exact Bool.false_ne_true this
  · intro ⟨_, hq⟩
    have : elem t q = true := (elem_iff_subtreeContains _ _).mpr hq
    rw [h_false] at this
    exact Bool.false_ne_true this

/-! ### No duplicate values -/

/-- The tree has no duplicate values: for every node, its value does not appear
in either of its subtrees, and both subtrees are themselves duplicate-free. -/
def nodup [DecidableEq α] : Tree α → Prop
  | .nil => True
  | .node v l r => elem l v = false ∧ elem r v = false ∧ nodup l ∧ nodup r

/-! ### Subnode membership -/

/-- `isSubnode s t` holds when `t` is structurally equal to some node (subtree) of `s`. -/
def isSubnode : Tree α → Tree α → Prop
  | .nil, _ => False
  | .node v l r, t => (t = .node v l r) ∨ isSubnode l t ∨ isSubnode r t


lemma isSubnode_self (v : α) (l r : Tree α) : isSubnode (.node v l r) (.node v l r) := by
  simp [isSubnode]

lemma isSubnode_left (v : α) (l r t : Tree α) (h : isSubnode l t) :
    isSubnode (.node v l r) t := by
  simp [isSubnode, h]

lemma isSubnode_right (v : α) (l r t : Tree α) (h : isSubnode r t) :
    isSubnode (.node v l r) t := by
  simp [isSubnode, h]

/-! ### Boolean version of subnode checking -/

/-- Boolean version of `isSubnode`: returns `true` iff `sub` is structurally equal to some
subtree of `t`. Uses `beq` for the structural comparison. -/
def isSubnodeBool [DecidableEq α] (t sub : Tree α) : Bool :=
  match t with
  | .nil => false
  | .node v l r => beq (.node v l r) sub || isSubnodeBool l sub || isSubnodeBool r sub

/-- `isSubnodeBool t sub = true` is equivalent to propositional `isSubnode t sub`. -/
theorem isSubnodeBool_eq_iff [DecidableEq α] (t sub : Tree α) :
    isSubnodeBool t sub = true ↔ isSubnode t sub := by
  induction t generalizing sub with
  | nil => simp [isSubnodeBool, isSubnode]
  | node v l r ih_l ih_r =>
    simp only [isSubnodeBool, isSubnode]
    rw [Bool.or_eq_true, Bool.or_eq_true, beq_eq_true_iff_eq, eq_comm, ih_l sub, ih_r sub]
    simp only [or_assoc]

/-! ### Leaves -/

/-- Collects the values of all leaf nodes (nodes with two `.nil` children). -/
def leaves : Tree α → List α
  | .nil => []
  | .node v .nil .nil => [v]
  | .node _ l r => leaves l ++ leaves r


theorem leaves_nil : leaves (.nil : Tree α) = [] := rfl


theorem leaves_leaf (v : α) : leaves (.node v .nil .nil) = [v] := rfl

theorem leaves_node (v : α) (l r : Tree α) (h : l ≠ .nil ∨ r ≠ .nil) :
    leaves (.node v l r) = leaves l ++ leaves r := by
  cases l with
  | nil =>
    cases r with
    | nil =>
      rcases h with (hl | hr)
      · exact (hl rfl).elim
      · exact (hr rfl).elim
    | node _ _ _ => simp [leaves]
  | node _ _ _ => simp [leaves]

/-- Any non-nil tree has at least one leaf, so its `leaves` list is non-empty. -/
lemma leaves_ne_nil_of_size_pos {t : Tree α} (h : size t ≥ 1) : leaves t ≠ [] := by
  induction t with
  | nil => simp [size] at h
  | node v l r ihl ihr =>
    by_cases hl : l = .nil
    · subst hl
      by_cases hr : r = .nil
      · subst hr; simp [leaves]
      · cases r with
        | nil => exact absurd rfl hr
        | node rv rl rr =>
          have hsr : size (node rv rl rr) ≥ 1 := by
            simp [size]; omega
          have hlr : leaves (node rv rl rr) ≠ [] := ihr hsr
          simpa [leaves] using hlr
    · cases l with
      | nil => exact absurd rfl hl
      | node lv ll lr =>
        have hsl : size (node lv ll lr) ≥ 1 := by
          simp [size]; omega
        intro h_eq
        simp [leaves] at h_eq
        exact ihl hsl h_eq.left

/-- Removes all leaf nodes from a tree, replacing each leaf with `.nil`. -/
def removeLeaves : Tree α → Tree α
  | .nil => .nil
  | .node _ .nil .nil => .nil
  | .node v l r => .node v (removeLeaves l) (removeLeaves r)


theorem removeLeaves_nil : removeLeaves (.nil : Tree α) = .nil := rfl


theorem removeLeaves_leaf (v : α) : removeLeaves (.node v .nil .nil) = .nil := rfl

theorem removeLeaves_node (v : α) (l r : Tree α) (h : l ≠ .nil ∨ r ≠ .nil) :
    removeLeaves (.node v l r) = .node v (removeLeaves l) (removeLeaves r) := by
  cases l with
  | nil =>
    cases r with
    | nil =>
      rcases h with (hl | hr)
      · exact (hl rfl).elim
      · exact (hr rfl).elim
    | node _ _ _ => simp [removeLeaves]
  | node _ _ _ => simp [removeLeaves]

/-- Removing leaves strictly decreases the tree size, provided the tree is non-nil. -/
lemma size_removeLeaves_lt {t : Tree α} (ht : t ≠ .nil) : size (removeLeaves t) < size t := by
  induction t with
  | nil => contradiction
  | node v l r ih_l ih_r =>
    by_cases hl : l = .nil
    · subst hl
      by_cases hr : r = .nil
      · subst hr; simp [removeLeaves, size]
      · have hlt_r : size (removeLeaves r) < size r := ih_r hr
        have h_rem : removeLeaves (.node v .nil r) = .node v .nil (removeLeaves r) := by
          simp [removeLeaves, hr]
        rw [h_rem]; simp [size]
        exact hlt_r
    · have hlt_l : size (removeLeaves l) < size l := ih_l hl
      by_cases hr : r = .nil
      · subst hr
        have h_rem : removeLeaves (.node v l .nil) = .node v (removeLeaves l) .nil := by
          simp [removeLeaves, hl]
        rw [h_rem]; simp [size]
        exact hlt_l
      · have hlt_r : size (removeLeaves r) < size r := ih_r hr
        have h_rem : removeLeaves (.node v l r) = .node v (removeLeaves l) (removeLeaves r) := by
          simp [removeLeaves, hl, hr]
        rw [h_rem]; simp [size, Nat.succ_add]
        have hsum : size (removeLeaves l) + size (removeLeaves r) < size l + size r :=
          Nat.add_lt_add hlt_l hlt_r
        exact hsum

/-! ### Boundary -/

/-- Check whether a tree node is a leaf (both children are `nil`). -/
def isLeaf : Tree α → Bool
  | .node _ .nil .nil => true
  | _ => false


theorem isLeaf_nil : isLeaf (.nil : Tree α) = false := rfl


theorem isLeaf_leaf (v : α) : isLeaf (.node v .nil .nil) = true := rfl


theorem isLeaf_node (v : α) (l r : Tree α) (h : l ≠ .nil ∨ r ≠ .nil) :
    isLeaf (.node v l r) = false := by
  cases l with
  | nil =>
    cases r with
    | nil => rcases h with (h' | h'); exact (h' rfl).elim; exact (h' rfl).elim
    | node _ _ _ => rfl
  | node _ _ _ => rfl

/-- Collect the left boundary of a tree (excluding leaves).
Traverses the left side, going right only when there is no left child.
Leaf nodes are excluded from the result. -/
def leftBoundary : Tree α → List α
  | .nil => []
  | .node v l r =>
    if isLeaf (.node v l r) then []
    else v :: (match l with
      | .nil => leftBoundary r
      | _ => leftBoundary l)


theorem leftBoundary_nil : leftBoundary (.nil : Tree α) = [] := rfl


theorem leftBoundary_leaf (v : α) : leftBoundary (.node v .nil .nil) = [] := by
  rfl

/-- Collect the right boundary of a tree (excluding leaves).
Traverses the right side, going left only when there is no right child.
Values are collected in bottom-up order (appended after the recursive result).
Leaf nodes are excluded from the result. -/
def rightBoundary : Tree α → List α
  | .nil => []
  | .node v l r =>
    if isLeaf (.node v l r) then []
    else (match r with
      | .nil => rightBoundary l
      | _ => rightBoundary r) ++ [v]


theorem rightBoundary_nil : rightBoundary (.nil : Tree α) = [] := rfl


theorem rightBoundary_leaf (v : α) : rightBoundary (.node v .nil .nil) = [] := by
  rfl

/-! ### Flip-equivalence

Flip‑equivalent binary trees are trees where we can flip (swap) left and right
children at any node and still reach the same structure. This captures the idea
behind LeetCode 951 "Flip Equivalent Binary Trees". -/

/-- Boolean flip‑equivalence predicate for binary trees over any type with `BEq`.
Two trees are flip‑equivalent when they are either both `nil`, or their root
values are equal and their subtrees are flip‑equivalent either in the same
order or with one pair of children swapped. -/
def flipEquivBool {α : Type} [BEq α] : Tree α → Tree α → Bool
  | .nil, .nil => true
  | .node v1 l1 r1, .node v2 l2 r2 =>
    (v1 == v2) && ((flipEquivBool l1 l2 && flipEquivBool r1 r2) ||
                   (flipEquivBool l1 r2 && flipEquivBool r1 l2))
  | _, _ => false

/-- Propositional flip‑equivalence predicate for binary trees over any type.
Mirrors `flipEquivBool` as a `Prop`. -/
def flipEquivProp {α : Type} : Tree α → Tree α → Prop
  | .nil, .nil => True
  | .node v1 l1 r1, .node v2 l2 r2 =>
      v1 = v2 ∧ ((flipEquivProp l1 l2 ∧ flipEquivProp r1 r2) ∨
                 (flipEquivProp l1 r2 ∧ flipEquivProp r1 l2))
  | _, _ => False

/-- The boolean and propositional flip‑equivalence predicates agree.
Proved by induction on the first tree, generalizing over the second. -/
lemma flipEquivBool_iff_flipEquivProp {α : Type} [BEq α] [LawfulBEq α]
    (t1 t2 : Tree α) : flipEquivBool t1 t2 = true ↔ flipEquivProp t1 t2 := by
  induction t1 generalizing t2 with
  | nil =>
    cases t2 with
    | nil => simp [flipEquivBool, flipEquivProp]
    | node => simp [flipEquivBool, flipEquivProp]
  | node v1 l1 r1 ihl ihr =>
    cases t2 with
    | nil => simp [flipEquivBool, flipEquivProp]
    | node v2 l2 r2 =>
      have h_l1l2 := ihl l2
      have h_l1r2 := ihl r2
      have h_r1l2 := ihr l2
      have h_r1r2 := ihr r2
      unfold flipEquivBool flipEquivProp
      by_cases hval : v1 = v2
      · simp [hval, h_l1l2, h_l1r2, h_r1l2, h_r1r2]
      · simp [hval, h_l1l2, h_l1r2, h_r1l2, h_r1r2]

end Tree

/-- A binary tree where every node (both internal and leaf) carries a value.
Leaves have no children. Unlike `Tree` from `Mathlib.Data.Tree.Basic` (which has `nil`
for empty subtrees), this representation is common in programming competition
problems (e.g., LeetCode) where empty trees aren't represented explicitly. -/
inductive NodeTree (α : Type u) : Type u where
  | leaf : α → NodeTree α
  | node : α → NodeTree α → NodeTree α → NodeTree α
deriving DecidableEq, Repr, Inhabited

namespace NodeTree

/-- Pre-order traversal collecting values from a `NodeTree` into a list.
Visits root, then left subtree, then right subtree.
Every node (including leaves) contributes its value. -/
def preorder : NodeTree α → List α
  | .leaf v => [v]
  | .node v l r => v :: (preorder l ++ preorder r)


theorem preorder_leaf (v : α) : preorder (.leaf v) = [v] := rfl


theorem preorder_node (v : α) (l r : NodeTree α) :
    preorder (.node v l r) = v :: (preorder l ++ preorder r) := rfl

/-- Number of nodes in a `NodeTree`. Every leaf counts as one node. -/
def size : NodeTree α → Nat
  | .leaf _ => 1
  | .node _ l r => 1 + size l + size r


theorem size_leaf (v : α) : size (.leaf v) = 1 := rfl


theorem size_node (v : α) (l r : NodeTree α) : size (.node v l r) = 1 + size l + size r := rfl

/-- The number of nodes in a `NodeTree` is always odd.
This follows by structural induction: leaves contribute 1, nodes contribute
1 + (odd + odd) = odd. -/
theorem size_odd (t : NodeTree α) : size t % 2 = 1 := by
  induction t with
  | leaf v => simp [size]
  | node v l r ih_l ih_r =>
    simp [size, ih_l, ih_r]
    omega

/-- The preorder traversal of a `NodeTree` always has odd length. -/
theorem preorder_length_odd (t : NodeTree α) : (preorder t).length % 2 = 1 := by
  induction t with
  | leaf v => simp [preorder]
  | node v l r ih_l ih_r =>
    simp [preorder, ih_l, ih_r]
    omega

/-- Construct a right-spine `NodeTree` from a list.
For the empty list, returns a leaf with the `Inhabited` default value of `α`. -/
def ofPreorderList [Inhabited α] : List α → NodeTree α
  | [] => .leaf default
  | [x] => .leaf x
  | x :: y :: rest => .node x (.leaf y) (ofPreorderList rest)

/-- If a list has odd length, `ofPreorderList` constructs a tree whose
preorder traversal equals the original list. This uses strong induction on
the length so we can recurse on the tail that is two elements shorter. -/
lemma preorder_ofPreorderList [Inhabited α] (xs : List α) (h : xs.length % 2 = 1) :
    preorder (ofPreorderList xs) = xs := by
  refine @Nat.strong_induction_on (λ n => ∀ (ys : List α),
    ys.length = n → ys.length % 2 = 1 → preorder (ofPreorderList ys) = ys) xs.length ?_ xs rfl h
  intro n IH ys h_len h_odd
  match ys with
  | [] => simp at h_odd
  | [x] => simp [ofPreorderList, preorder]
  | x :: y :: rest =>
    have h_rest_odd : rest.length % 2 = 1 := by
      have hlen : (x :: y :: rest).length = rest.length + 2 := by simp
      rw [hlen] at h_odd
      omega
    have h_rest_len_lt_n : rest.length < n := by
      rw [← h_len]
      have hlen : (x :: y :: rest).length = rest.length + 2 := by simp
      rw [hlen]
      omega
    have ih_rest := IH rest.length h_rest_len_lt_n rest rfl h_rest_odd
    simp [ofPreorderList, preorder, ih_rest]

end NodeTree


/-- A binary tree where each node carries a value and has optional left/right children.

This is the standard representation used across LeetCode tree problems. Unlike `Tree`
from `Mathlib.Data.Tree.Basic` which uses `nil` for empty subtrees, `TreeNode` uses
`Option` for children, matching the pointer-based representation common in imperative
languages. The `α` parameter generalizes the hardcoded `Nat` that appears in individual
problem statements. -/
structure TreeNode (α : Type u) where
  val : α
  left : Option (TreeNode α)
  right : Option (TreeNode α)
deriving Repr

/-- Typeclass for types that behave like a binary tree node, providing value access
and child-pointer access. `α` is an `outParam` because it is determined by the node type. -/
class TreeNodeLike (node : Type v) (α : outParam (Type u)) where
  val : node → α
  left : node → Option node
  right : node → Option node

namespace TreeNode

instance : TreeNodeLike (TreeNode α) α where
  val n := n.val
  left n := n.left
  right n := n.right

/-! ### Size of a tree -/

/-- Number of nodes in the tree. Every node counts as 1, plus all nodes in subtrees. -/
def size : TreeNode α → Nat
  | ⟨_, l, r⟩ =>
      1 +
        (match l with
          | some tl => size tl
          | none => 0) +
        (match r with
          | some tr => size tr
          | none => 0)
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega

/-- Every tree node has size at least 1. -/
lemma size_pos (t : TreeNode α) : size t ≥ 1 := by
  cases t; unfold size; omega

/-- If a tree has size at least 2, then it has at least one non-null child. -/
lemma child_exists_of_size_ge_two (t : TreeNode α) (h : size t ≥ 2) :
    t.left ≠ none ∨ t.right ≠ none := by
  cases t with | mk v l r =>
  unfold size at h
  have h_child_sizes_ge_one : (match l with | some tl => size tl | none => 0) +
      (match r with | some tr => size tr | none => 0) ≥ 1 := by omega
  cases l with
  | some _ => left; simp
  | none =>
    cases r with
    | some _ => right; simp
    | none => simp at h_child_sizes_ge_one

/-! ### Predicate on all node values -/

/-- `all p t` holds when every node value in `t` satisfies predicate `p`. -/
def all (p : α → Prop) : TreeNode α → Prop
  | ⟨v, l, r⟩ =>
      p v ∧
        (match l with
          | some tl => all p tl
          | none => True) ∧
        (match r with
          | some tr => all p tr
          | none => True)
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega

/-! ### Well-formed trees with leaf/internal node predicates -/

/-- `wellFormed leafP internalP t` holds when the tree `t` is well-formed with respect to
two predicates on node values:
- Leaf nodes (no children) must satisfy `leafP` on their value
- Internal nodes (both children present) must satisfy `internalP` on their value,
  and both subtrees must also be well-formed
- Nodes with exactly one child are never well-formed (they are malformed)

This generalizes pattern-checking predicates common in tree problems (e.g., boolean expression
trees where leaves are `0`/`1` and internal nodes are `2`/`3`). -/
def wellFormed (leafP internalP : α → Prop) : TreeNode α → Prop
  | ⟨v, none, none⟩ => leafP v
  | ⟨v, some l, some r⟩ => internalP v ∧ wellFormed leafP internalP l ∧ wellFormed leafP internalP r
  | _ => False

/-- Well-formedness is preserved when weakening the leaf predicate:
if `leafP` implies `leafQ`, then `wellFormed leafP internalP t` implies `wellFormed leafQ internalP t`. -/
lemma wellFormed.imp_leaf {leafP leafQ internalP : α → Prop} (h : ∀ a, leafP a → leafQ a) :
    ∀ t, wellFormed leafP internalP t → wellFormed leafQ internalP t
  | ⟨_, none, none⟩, hw => h _ hw
  | ⟨_, some l, some r⟩, ⟨hv, hl, hr⟩ => ⟨hv, wellFormed.imp_leaf h l hl, wellFormed.imp_leaf h r hr⟩

/-- Well-formedness is preserved when weakening the internal predicate:
if `internalP` implies `internalQ`, then `wellFormed leafP internalP t` implies `wellFormed leafP internalQ t`. -/
lemma wellFormed.imp_internal {leafP internalP internalQ : α → Prop} (h : ∀ a, internalP a → internalQ a) :
    ∀ t, wellFormed leafP internalP t → wellFormed leafP internalQ t
  | ⟨_, none, none⟩, hw => hw
  | ⟨_, some l, some r⟩, ⟨hv, hl, hr⟩ => ⟨h _ hv, wellFormed.imp_internal h l hl, wellFormed.imp_internal h r hr⟩

/-- A well-formed node is either a leaf (no children) or an internal node
with exactly two children. Nodes with a single child are excluded. -/
lemma wellFormed_cases {t : TreeNode α} (h : wellFormed leafP internalP t) :
    (t.left = none ∧ t.right = none) ∨
    (∃ l r, t.left = some l ∧ t.right = some r) := by
  cases t with | mk v left right =>
    cases left with
    | none =>
      cases right with
      | none => left; simp
      | some r => simp [wellFormed] at h
    | some l =>
      cases right with
      | none => simp [wellFormed] at h
      | some r => right; exact ⟨l, r, rfl, rfl⟩

/-- A well-formed leaf node satisfies `leafP` on its value. -/
lemma wellFormed_leaf {v : α} (h : wellFormed leafP internalP ⟨v, none, none⟩) : leafP v := by
  simpa [wellFormed] using h

/-- A well-formed internal node satisfies `internalP` on its value
and both subtrees are themselves well-formed. -/
lemma wellFormed_internal {v : α} {l r : TreeNode α}
    (h : wellFormed leafP internalP ⟨v, some l, some r⟩) :
    internalP v ∧ wellFormed leafP internalP l ∧ wellFormed leafP internalP r := by
  simpa [wellFormed] using h

/-! ### Ancestor relation -/

/-- `Ancestor a b` holds when `a` is a (proper or improper) ancestor of `b` in the tree.
That is, `b` is either a direct child of `a` or a descendant through one of `a`'s children. -/
def Ancestor (a b : TreeNode α) : Prop :=
  match a with
  | ⟨_, l, r⟩ =>
      (match l with
        | some tl => tl = b ∨ Ancestor tl b
        | none => False) ∨
      (match r with
        | some tr => tr = b ∨ Ancestor tr b
        | none => False)

/-! ### Operations on optional trees -/

/-- `sizeOpt t` returns 0 if `t` is `none`, otherwise the size of the tree. -/
def sizeOpt : Option (TreeNode α) → Nat
  | none => 0
  | some t => size t

theorem sizeOpt_none : sizeOpt (none : Option (TreeNode α)) = 0 := by
  simp [sizeOpt]

/-- `allOpt p t` holds when every value in the optional tree `t` satisfies `p`. -/
def allOpt (p : α → Prop) : Option (TreeNode α) → Prop
  | none => True
  | some t => all p t

theorem allOpt_none (p : α → Prop) : allOpt p (none : Option (TreeNode α)) = True := by
  simp [allOpt]

/-! ### Sum operations -/

/-- `sumWhere p t` returns the sum of all values in the optional tree `t`
that satisfy the boolean predicate `p`. Returns `0` if `t` is `none`. -/
def sumWhere [AddMonoid α] (p : α → Bool) : Option (TreeNode α) → α
  | none => 0
  | some ⟨v, l, r⟩ =>
      let rest := sumWhere p l + sumWhere p r
      if p v then v + rest else rest
termination_by t => sizeOf t

/-- `sum t` returns the sum of all values in the optional tree `t`. -/
def sum [AddMonoid α] : Option (TreeNode α) → α :=
  sumWhere (fun _ => true)

theorem sumWhere_none [AddMonoid α] (p : α → Bool) :
    sumWhere p (none : Option (TreeNode α)) = 0 := by
  simp [sumWhere]

theorem sum_none [AddMonoid α] : sum (none : Option (TreeNode α)) = 0 := by
  simp [sum, sumWhere_none]

/-! ### Depth-indexed sum -/

/-- `sumAtDepth t d` returns the sum of node values at depth `d` (1-indexed: root is depth 1,
and depth 0 always returns 0). Returns `0` if `t` is `none`. -/
def sumAtDepth [AddMonoid α] : Option (TreeNode α) → Nat → α
  | none, _ => 0
  | some _, 0 => 0
  | some ⟨v, _, _⟩, 1 => v
  | some ⟨_, l, r⟩, d + 1 => sumAtDepth l d + sumAtDepth r d

theorem sumAtDepth_none [AddMonoid α] (d : Nat) :
    sumAtDepth (none : Option (TreeNode α)) d = 0 := by
  simp [sumAtDepth]

theorem sumAtDepth_some_zero [AddMonoid α] (t : TreeNode α) :
    sumAtDepth (some t) 0 = 0 := by
  simp [sumAtDepth]

/-! ### Nodes at a given depth -/

/-- `nodesAtLevel t d` returns the list of nodes at depth `d` (root at depth 0)
from left to right. Returns `[]` if `t` is `none`. -/
def nodesAtLevel : Option (TreeNode α) → Nat → List (TreeNode α)
  | none, _ => []
  | some n, 0 => [n]
  | some n, Nat.succ d => (nodesAtLevel n.left d) ++ (nodesAtLevel n.right d)

/-! ### Inorder traversal -/

/-- In-order traversal of a `TreeNode`, collecting node values into a list.
Visits the left subtree, then the root, then the right subtree. -/
def inorder : TreeNode α → List α
  | ⟨v, l, r⟩ =>
      let leftList := match l with
        | none => []
        | some tl => inorder tl
      let rightList := match r with
        | none => []
        | some tr => inorder tr
      leftList ++ [v] ++ rightList
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega

/-- In-order traversal of an optional tree. Returns `[]` for `none`. -/
def inorderOpt : Option (TreeNode α) → List α
  | none => []
  | some t => inorder t

theorem inorderOpt_none : inorderOpt (none : Option (TreeNode α)) = [] := by
  simp [inorderOpt]

theorem inorderOpt_some (t : TreeNode α) : inorderOpt (some t) = inorder t := by
  simp [inorderOpt]

/-! ### Stateful traversals -/

/-- Traverse the tree in reverse in-order (right child, then root, then left child),
applying `f` to each node's value with accumulated state. `f acc v` returns a pair
`(newValue, newAcc)` where `newValue` replaces the node's value and `newAcc` is
the updated state passed to subsequent traversals.

This is useful for problems that require building a new tree while threading
accumulated state through a reverse in-order traversal (e.g., BST to Greater Sum Tree). -/
def mapAccumRInorder {σ β : Type} : Option (TreeNode α) → σ → (σ → α → β × σ) → Option (TreeNode β) × σ
  | none, acc, _ => (none, acc)
  | some ⟨v, l, r⟩, acc, f =>
      let (rightConv, accRight) := mapAccumRInorder r acc f
      let (newVal, accNode) := f accRight v
      let (leftConv, accFinal) := mapAccumRInorder l accNode f
      (some { val := newVal, left := leftConv, right := rightConv }, accFinal)
termination_by t _ _ => sizeOf t

theorem mapAccumRInorder_none {σ β : Type} (acc : σ) (f : σ → α → β × σ) :
    mapAccumRInorder (none : Option (TreeNode α)) acc f = (none, acc) := by
  simp [mapAccumRInorder]

/-! ### Termination helpers -/

/-- If the left child of `t` is `some ln`, then `sizeOf ln < sizeOf t`.
Useful for proving termination of recursive functions that traverse the tree. -/
lemma sizeOf_lt_of_left_eq_some {α : Type u} (t ln : TreeNode α) (h : t.left = some ln) :
    sizeOf ln < sizeOf t := by
  cases t
  rename_i val left right
  dsimp at h
  subst h
  simp
  omega

/-- If the right child of `t` is `some rn`, then `sizeOf rn < sizeOf t`.
Useful for proving termination of recursive functions that traverse the tree. -/
lemma sizeOf_lt_of_right_eq_some {α : Type u} (t rn : TreeNode α) (h : t.right = some rn) :
    sizeOf rn < sizeOf t := by
  cases t
  rename_i val left right
  dsimp at h
  subst h
  simp
  omega

/-! ### Bottom-up transformation (post-order map) -/

/-- Apply a bottom-up (post-order) transformation to an optional tree.
Given `f : α → Option (TreeNode α) → Option (TreeNode α) → Option (TreeNode α)`,
`mapBottomUp f t` recursively transforms the left and right children first,
then applies `f` to the node value and the already-transformed children.

This enables operations like conditional node deletion, where the decision
whether to keep a node depends on the state of its (already processed) children. -/
def mapBottomUp (f : α → Option (TreeNode α) → Option (TreeNode α) → Option (TreeNode α)) :
    Option (TreeNode α) → Option (TreeNode α)
  | none => none
  | some ⟨v, l, r⟩ => f v (mapBottomUp f l) (mapBottomUp f r)
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega


theorem mapBottomUp_none (f : α → Option (TreeNode α) → Option (TreeNode α) → Option (TreeNode α)) :
    mapBottomUp f none = none := by
  simp [mapBottomUp]


theorem mapBottomUp_some (f : α → Option (TreeNode α) → Option (TreeNode α) → Option (TreeNode α))
    (v : α) (l r : Option (TreeNode α)) :
    mapBottomUp f (some ⟨v, l, r⟩) = f v (mapBottomUp f l) (mapBottomUp f r) := by
  simp [mapBottomUp]

/-! ### Root-to-leaf path validity -/

/-- `validPath node lst` holds iff there exists a root‑to‑leaf path starting at `node`
    whose node values, read from the current node down to a leaf, exactly equal `lst`. -/
def validPath {α : Type u} : TreeNode α → List α → Prop
  | node, [] => False
  | node, (x :: xs) =>
      node.val = x ∧
      match xs with
      | [] =>
          -- `xs` empty ⇒ we must be at a leaf
          node.left = none ∧ node.right = none
      | _ =>
          (match node.left with
           | some l => validPath l xs
           | none   => False) ∨
          (match node.right with
           | some r => validPath r xs
           | none   => False)

/-! ### Node value equals sum of children -/

/-- `childrenSumEqVal t` returns `true` when `t` has both left and right children
and its value equals the sum of the children's values.

This is a common predicate in tree problems (e.g., LeetCode 2236 "Root Equals Sum of Children"). -/
def childrenSumEqVal [Add α] [BEq α] (t : TreeNode α) : Bool :=
  match t.left, t.right with
  | some l, some r => t.val == l.val + r.val
  | _, _ => false

/-- When the left and right children of `t` are known, `childrenSumEqVal` simplifies
to a direct comparison of values. -/

theorem childrenSumEqVal_eq [Add α] [BEq α] (t : TreeNode α) (l r : TreeNode α)
    (hl : t.left = some l) (hr : t.right = some r) :
    childrenSumEqVal t = (t.val == l.val + r.val) := by
  unfold childrenSumEqVal
  simp [hl, hr]

/-! ### Height of a tree -/

/-- Height of a binary tree. Leaves (nodes with no children) have height 0;
internal nodes (both children present) have height `Nat.succ (max h_l h_r)`.
Nodes with exactly one child default to height 0 (unreachable for well-formed trees). -/
def height : TreeNode α → Nat
  | ⟨_, none, none⟩ => 0
  | ⟨_, some l, some r⟩ => Nat.succ (max (height l) (height r))
  | _ => 0

/-! ### Perfect tree predicate -/

/-- `isPerfect t` holds iff `t` is a perfect binary tree: all internal nodes have
two children and all leaves are at the same depth. -/
def isPerfect : TreeNode α → Prop
  | ⟨_, none, none⟩ => True
  | ⟨_, some l, some r⟩ => isPerfect l ∧ isPerfect r ∧ (height l = height r)
  | _ => False

/-- An unbalanced tree with only a left child is not perfect. -/

lemma not_isPerfect_leftOnly {α : Type u} {v : α} {l : TreeNode α} :
    ¬ isPerfect (⟨v, some l, none⟩) := by
  simp [isPerfect]

/-- An unbalanced tree with only a right child is not perfect. -/

lemma not_isPerfect_rightOnly {α : Type u} {v : α} {r : TreeNode α} :
    ¬ isPerfect (⟨v, none, some r⟩) := by
  simp [isPerfect]

/-! ### Values at a given depth -/

/-- List of node values at depth `d` (root at depth 0), from left to right.
Returns `[]` for depths beyond the tree's height or for malformed nodes.
Contrast with `nodesAtLevel` which returns the full nodes, not just their values. -/
def valsAtLevel : TreeNode α → Nat → List α
  | ⟨v, none, none⟩, 0 => [v]
  | ⟨_, none, none⟩, Nat.succ _ => []
  | ⟨v, some _, some _⟩, 0 => [v]
  | ⟨_, some l, some r⟩, Nat.succ d => (valsAtLevel l d) ++ (valsAtLevel r d)
  | _, _ => []

/-! ### Sum of left leaves -/

/-- Auxiliary function for summing values of left leaf nodes.
`isLeft` indicates whether the current node is a left child of its parent.
A left leaf is a leaf node (both children are `none`) that is a left child. -/
def sumLeftLeavesAux [AddMonoid α] : Option (TreeNode α) → Bool → α
  | none, _ => 0
  | some ⟨v, l, r⟩, isLeft =>
    let leftSum := sumLeftLeavesAux l true
    let rightSum := sumLeftLeavesAux r false
    if isLeft && l.isNone && r.isNone then v else leftSum + rightSum
termination_by o _ => sizeOf o
decreasing_by
  all_goals
    simp_wf
    omega

/-- Sum of values of all left leaf nodes in the tree.
A left leaf is a leaf node that is the left child of its parent. -/
def sumLeftLeaves [AddMonoid α] (root : Option (TreeNode α)) : α :=
  sumLeftLeavesAux root false


theorem sumLeftLeavesAux_none [AddMonoid α] (b : Bool) :
    sumLeftLeavesAux (none : Option (TreeNode α)) b = 0 := by
  simp [sumLeftLeavesAux]

theorem sumLeftLeavesAux_some [AddMonoid α] (v : α) (l r : Option (TreeNode α)) (isLeft : Bool) :
    sumLeftLeavesAux (some ⟨v, l, r⟩) isLeft =
    (if isLeft && l.isNone && r.isNone then v
     else sumLeftLeavesAux l true + sumLeftLeavesAux r false) := by
  simp [sumLeftLeavesAux]


theorem sumLeftLeaves_eq [AddMonoid α] (root : Option (TreeNode α)) :
    sumLeftLeaves root = sumLeftLeavesAux root false := by
  simp [sumLeftLeaves]

/-! ### SizeOf helper -/

/-- `sizeOf` for a `TreeNode α` expands to `1 + sizeOf val + sizeOf left + sizeOf right`.
Useful for termination proofs when recursion descends into child nodes. -/
lemma sizeOf_eq (t : TreeNode α) : sizeOf t = 1 + sizeOf t.val + sizeOf t.left + sizeOf t.right := by
  cases t; simp

/-! ### Preorder value collection (optional tree) -/

/-- Preorder traversal collecting all node values from an optional tree into a list.
Returns `[]` for `none`. This is a convenience wrapper that works directly on
`Option (TreeNode α)`, matching the common LeetCode pattern where trees are
represented as optional nodes. -/
def vals : Option (TreeNode α) → List α
  | none => []
  | some ⟨v, l, r⟩ => v :: (vals l ++ vals r)
termination_by t => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega

/-! ### Membership in tree values -/

/-- Membership in `vals` for a `some` node decomposes into the node's value or
membership in the left or right subtree. -/
lemma mem_vals_some_iff {v : α} {n : TreeNode α} :
    v ∈ vals (some n) ↔ v = n.val ∨ v ∈ vals n.left ∨ v ∈ vals n.right := by
  cases n; simp [vals]

/-- If a value is in the left subtree, it's in the parent's `vals`. -/
lemma mem_vals_of_mem_left {v : α} {n : TreeNode α} (h : v ∈ vals n.left) : v ∈ vals (some n) := by
  cases n; simp [vals, h]

/-- If a value is in the right subtree, it's in the parent's `vals`. -/
lemma mem_vals_of_mem_right {v : α} {n : TreeNode α} (h : v ∈ vals n.right) : v ∈ vals (some n) := by
  cases n; simp [vals, h]

/-! ### Range-based BST property -/

/-- `isBST t lo hi` holds when every node value in the optional tree `t` lies
within the closed interval `[lo, hi]` and the tree satisfies the binary search tree
property: for each node, all values in its left subtree are at most the node's value,
and all values in its right subtree are at least the node's value.

This is the range-based BST predicate common in LeetCode trim/validate problems.
Contrast with `BST.IsBST` (which uses in-order traversal bounds)
and `BST.IsBSTStruct` (which checks order structurally without range bounds). -/
def isBST [LE α] : Option (TreeNode α) → α → α → Prop
  | none, _, _ => True
  | some ⟨v, l, r⟩, lo, hi =>
      lo ≤ v ∧ v ≤ hi ∧
      isBST l lo v ∧
      isBST r v hi
termination_by t _ _ => sizeOf t
decreasing_by
  all_goals
    simp_wf
    omega

/-! ### Construction lemmas for isBST -/

/-- Construct `isBST` for a node from known properties of its subtrees.
Given that the node value lies within `[lo, hi]` and both subtrees are BSTs
within their respective sub-ranges, the combined tree is a BST on `[lo, hi]`. -/
lemma isBST_some_intro [LE α] (n : TreeNode α) (l r : Option (TreeNode α)) (lo hi : α)
    (h_lo : lo ≤ n.val) (h_hi : n.val ≤ hi)
    (h_l : isBST l lo n.val) (h_r : isBST r n.val hi) :
    isBST (some { val := n.val, left := l, right := r }) lo hi := by
  simp [isBST, h_lo, h_hi, h_l, h_r]

/-! ### Range composition for tree values -/

/-- Range composition: if all values in the left subtree lie in `[lo, val]` and
all values in the right subtree lie in `[val, hi]`, then all values in the combined
tree lie in `[lo, hi]`. Requires `Preorder α` for transitivity of `≤`. -/
lemma vals_some_range [Preorder α] (n : TreeNode α) (l r : Option (TreeNode α)) (lo hi : α)
    (h_lo : lo ≤ n.val) (h_hi : n.val ≤ hi)
    (hrange_l : ∀ v, v ∈ vals l → lo ≤ v ∧ v ≤ n.val)
    (hrange_r : ∀ v, v ∈ vals r → n.val ≤ v ∧ v ≤ hi) :
    ∀ v, v ∈ vals (some { val := n.val, left := l, right := r }) → lo ≤ v ∧ v ≤ hi := by
  intro v hv
  rw [mem_vals_some_iff] at hv
  rcases hv with (rfl | hv | hv)
  · exact ⟨h_lo, h_hi⟩
  · rcases hrange_l v hv with ⟨hlo, hhi⟩
    exact ⟨hlo, le_trans hhi h_hi⟩
  · rcases hrange_r v hv with ⟨hlo, hhi⟩
    exact ⟨le_trans h_lo hlo, hhi⟩

end TreeNode


/-!
# Binary Search Tree (BST)

A simple binary search tree data structure with ordering-based insertion.
The tree itself does not enforce the BST invariant at the type level, but
`insert` and `fromList` are designed to maintain it.

This is structurally identical to `Tree` from `Mathlib.Data.Tree.Basic` but
semantically used for ordered binary search tree operations.
-/

/-- Binary search tree data structure, parameterized over element type -/
inductive BST (α : Type) where
  | empty
  | node (val : α) (left : BST α) (right : BST α)
  deriving Repr, Inhabited

namespace BST

/-- Insert a value into the BST, maintaining the BST ordering invariant. -/
def insert [LinearOrder α] : BST α → α → BST α
  | .empty, x => .node x .empty .empty
  | .node v l r, x =>
    if x < v then
      .node v (l.insert x) r
    else if x > v then
      .node v l (r.insert x)
    else
      .node v l r

/-- Compute the depth (height) of a BST. -/
def depth : BST α → Nat
  | .empty => 0
  | .node _ l r => 1 + max (l.depth) (r.depth)

/-- Number of nodes in a BST. -/
def size : BST α → Nat
  | .empty => 0
  | .node _ l r => 1 + size l + size r

/-- Build a BST from a list by folding `insert` over the elements. -/
def fromList [LinearOrder α] (xs : List α) : BST α :=
  xs.foldl (fun t x => t.insert x) .empty

/-- In-order traversal collecting values from a BST into a list. -/
def inorder : BST α → List α
  | .empty => []
  | .node v l r => inorder l ++ [v] ++ inorder r

/-- Pre-order traversal collecting values from a BST into a list.
Visits the root, then the left subtree, then the right subtree. -/
def preorder : BST α → List α
  | .empty => []
  | .node v l r => v :: (preorder l ++ preorder r)

/-- Predicate stating that a tree satisfies the BST ordering property:
all values in the left subtree are `<` the root value,
all values in the right subtree are `>` the root value,
and both subtrees recursively satisfy the BST property. -/
def IsBST [LT α] : BST α → Prop
  | .empty => True
  | .node v l r =>
      (∀ x ∈ inorder l, x < v) ∧
      (∀ x ∈ inorder r, v < x) ∧
      IsBST l ∧ IsBST r

/-! ### Theorems -/


theorem depth_empty : depth (.empty : BST α) = 0 := rfl


theorem depth_node (v : α) (l r : BST α) : depth (.node v l r) = 1 + max (l.depth) (r.depth) := rfl


theorem size_empty : size (.empty : BST α) = 0 := rfl


theorem size_node (v : α) (l r : BST α) : size (.node v l r) = 1 + size l + size r := rfl


theorem inorder_empty : inorder (.empty : BST α) = [] := rfl


theorem inorder_node (v : α) (l r : BST α) : inorder (.node v l r) = inorder l ++ [v] ++ inorder r := rfl


theorem preorder_empty : preorder (.empty : BST α) = [] := rfl


theorem preorder_node (v : α) (l r : BST α) : preorder (.node v l r) = v :: (preorder l ++ preorder r) := rfl

/-- The size of a BST equals the length of its in-order traversal. -/
theorem size_eq_length_inorder (t : BST α) : size t = (inorder t).length := by
  induction t with
  | empty => rfl
  | node v l r ihl ihr =>
    simp [size, inorder, List.length_append, ihl, ihr]
    omega


theorem insert_empty [LinearOrder α] (x : α) : (.empty : BST α).insert x = .node x .empty .empty := rfl


theorem fromList_nil [LinearOrder α] : fromList ([] : List α) = .empty := rfl

/-! ### allLT / allGT: structural ordering predicates -/

/-- `allLT t v` holds when every value in tree `t` is less than `v`.
This is a structural predicate defined by recursion on `t`, useful for BST
correctness proofs that reason directly about subtrees without computing
in-order traversals. -/
def allLT [LT α] (t : BST α) (v : α) : Prop :=
  match t with
  | .empty => True
  | .node x l r => x < v ∧ allLT l v ∧ allLT r v

/-- `allGT t v` holds when every value in tree `t` is greater than `v`. -/
def allGT [LT α] (t : BST α) (v : α) : Prop :=
  match t with
  | .empty => True
  | .node x l r => x > v ∧ allGT l v ∧ allGT r v

theorem allLT_empty [LT α] (v : α) : allLT (.empty : BST α) v := by
  simp [allLT]

theorem allLT_node [LT α] (x v : α) (l r : BST α) :
    allLT (.node x l r) v ↔ x < v ∧ allLT l v ∧ allLT r v := by
  simp [allLT]

theorem allGT_empty [LT α] (v : α) : allGT (.empty : BST α) v := by
  simp [allGT]

theorem allGT_node [LT α] (x v : α) (l r : BST α) :
    allGT (.node x l r) v ↔ x > v ∧ allGT l v ∧ allGT r v := by
  simp [allGT]

/-! ### Boolean versions of allLT / allGT -/

/-- Boolean version of `allLT`: returns `true` when every value in `t` is less than `v`.
Uses `decide` for the comparison so that it works with any `LinearOrder`. -/
def allLTBool [LinearOrder α] (t : BST α) (v : α) : Bool :=
  match t with
  | .empty => true
  | .node x l r => decide (x < v) && allLTBool l v && allLTBool r v

/-- Boolean version of `allGT`: returns `true` when every value in `t` is greater than `v`. -/
def allGTBool [LinearOrder α] (t : BST α) (v : α) : Bool :=
  match t with
  | .empty => true
  | .node x l r => decide (x > v) && allGTBool l v && allGTBool r v

theorem allLTBool_empty [LinearOrder α] (v : α) : allLTBool (.empty : BST α) v = true := rfl

theorem allGTBool_empty [LinearOrder α] (v : α) : allGTBool (.empty : BST α) v = true := rfl

lemma allLTBool_eq_true_iff [LinearOrder α] (t : BST α) (v : α) :
    allLTBool t v = true ↔ allLT t v := by
  induction t with
  | empty => simp [allLTBool, allLT]
  | node x l r ihl ihr =>
    simp [allLTBool, allLT, ihl, ihr, and_assoc, decide_eq_true_iff]

lemma allGTBool_eq_true_iff [LinearOrder α] (t : BST α) (v : α) :
    allGTBool t v = true ↔ allGT t v := by
  induction t with
  | empty => simp [allGTBool, allGT]
  | node x l r ihl ihr =>
    simp [allGTBool, allGT, ihl, ihr, and_assoc, decide_eq_true_iff]

/-! ### Structural BST check (using allLT / allGT) -/

/-- Structural BST property: a tree is a valid BST when every node's value is greater
than all values in its left subtree and less than all values in its right subtree,
and both subtrees are themselves BSTs. This is the canonical structural definition
that does not require computing in-order traversals.

Contrast with `BST.IsBST` which uses `inorder` to express the ordering constraints. -/
def IsBSTStruct [LT α] : BST α → Prop
  | .empty => True
  | .node v l r => IsBSTStruct l ∧ IsBSTStruct r ∧ allLT l v ∧ allGT r v

/-- Boolean version of `IsBSTStruct`: a decidable BST check via structural recursion. -/
def IsBSTBool [LinearOrder α] : BST α → Bool
  | .empty => true
  | .node v l r => IsBSTBool l && IsBSTBool r && allLTBool l v && allGTBool r v

theorem IsBSTStruct_empty [LT α] : IsBSTStruct (.empty : BST α) := by
  simp [IsBSTStruct]

theorem IsBSTBool_empty [LinearOrder α] : IsBSTBool (.empty : BST α) = true := rfl

lemma IsBSTBool_eq_true_iff [LinearOrder α] (t : BST α) :
    IsBSTBool t = true ↔ IsBSTStruct t := by
  induction t with
  | empty => simp [IsBSTBool, IsBSTStruct]
  | node v l r ihl ihr =>
    simp [IsBSTBool, IsBSTStruct, ihl, ihr, allLTBool_eq_true_iff, allGTBool_eq_true_iff,
      and_assoc]

lemma not_IsBSTStruct_of_not_IsBSTBool [LinearOrder α] (t : BST α)
    (h : ¬ IsBSTBool t = true) : ¬ IsBSTStruct t := by
  intro hbst
  have htrue : IsBSTBool t = true := (IsBSTBool_eq_true_iff _).mpr hbst
  exact h htrue

/-! ### Subtree relation -/

/-- `isSubtree s t` holds when `s` is structurally equal to some subtree of `t`
(including `t` itself). Defined recursively on `t`. -/
def isSubtree (s t : BST α) : Prop :=
  s = t ∨
    match t with
    | .empty => False
    | .node _ l r => isSubtree s l ∨ isSubtree s r

lemma isSubtree_refl (t : BST α) : isSubtree t t := by
  unfold isSubtree; left; rfl


lemma isSubtree_node_iff (s : BST α) (v : α) (l r : BST α) :
    isSubtree s (.node v l r) ↔ s = .node v l r ∨ isSubtree s l ∨ isSubtree s r := by
  simp [isSubtree]

lemma isSubtree_node_left (s : BST α) (v : α) (l r : BST α)
    (h : isSubtree s l) : isSubtree s (.node v l r) := by
  rw [isSubtree_node_iff]; right; left; exact h

lemma isSubtree_node_right (s : BST α) (v : α) (l r : BST α)
    (h : isSubtree s r) : isSubtree s (.node v l r) := by
  rw [isSubtree_node_iff]; right; right; exact h

/-! ### Pointwise structural relation

`relValues R t₁ t₂` holds when `t₁` and `t₂` have the same shape
and corresponding node values satisfy the relation `R`. This generalises
structural equality (`same`) from a fixed equality relation to an
arbitrary binary relation, enabling reasoning about tree transformations
(e.g., `map` correctness proofs). -/

/-- `relValues R t₁ t₂` holds when `t₁` and `t₂` have the same shape
and corresponding node values are related by `R : α → β → Prop`. -/
def relValues (R : α → β → Prop) : BST α → BST β → Prop
  | .empty, .empty => True
  | .node v₁ l₁ r₁, .node v₂ l₂ r₂ =>
      R v₁ v₂ ∧ relValues R l₁ l₂ ∧ relValues R r₁ r₂
  | _, _ => False


theorem relValues_empty_empty (R : α → β → Prop) :
    relValues R (.empty : BST α) (.empty : BST β) := by
  simp [relValues]


theorem relValues_empty_node (R : α → β → Prop) (v : β) (l r : BST β) :
    ¬ relValues R (.empty : BST α) (.node v l r) := by
  simp [relValues]


theorem relValues_node_empty (R : α → β → Prop) (v : α) (l r : BST α) :
    ¬ relValues R (.node v l r) (.empty : BST β) := by
  simp [relValues]

theorem relValues_node_iff (R : α → β → Prop) (v₁ : α) (l₁ r₁ : BST α) (v₂ : β) (l₂ r₂ : BST β) :
    relValues R (.node v₁ l₁ r₁) (.node v₂ l₂ r₂) ↔
    R v₁ v₂ ∧ relValues R l₁ l₂ ∧ relValues R r₁ r₂ := by
  simp [relValues]

/-- If the relation `R` is reflexive, then `relValues R t t` holds for all `t`. -/
theorem relValues_refl (R : α → α → Prop) (hR : ∀ a, R a a) (t : BST α) : relValues R t t := by
  induction t with
  | empty => simp [relValues]
  | node v l r ihl ihr => simp [relValues, hR v, ihl, ihr]

/-- `relValues` is symmetric when `R` is symmetric. -/
theorem relValues_symm (R : α → α → Prop) (hR : ∀ a b, R a b → R b a) {t₁ t₂ : BST α}
    (h : relValues R t₁ t₂) : relValues R t₂ t₁ := by
  cases t₁ with
  | empty =>
    cases t₂ with
    | empty => simp [relValues]
    | node v₂ l₂ r₂ => simp [relValues] at h
  | node v₁ l₁ r₁ =>
    cases t₂ with
    | empty => simp [relValues] at h
    | node v₂ l₂ r₂ =>
      simp [relValues] at h ⊢
      rcases h with ⟨hR_val, hl, hr⟩
      have ihl : relValues R l₂ l₁ := relValues_symm R hR hl
      have ihr : relValues R r₂ r₁ := relValues_symm R hR hr
      exact ⟨hR _ _ hR_val, ihl, ihr⟩
termination_by t₁

/-- `relValues` is transitive when `R` is transitive. -/
theorem relValues_trans (R : α → α → Prop) (hR : ∀ a b c, R a b → R b c → R a c)
    {t₁ t₂ t₃ : BST α} (h₁₂ : relValues R t₁ t₂) (h₂₃ : relValues R t₂ t₃) : relValues R t₁ t₃ := by
  cases t₁ with
  | empty =>
    cases t₂ with
    | empty =>
      cases t₃ with
      | empty => simp [relValues]
      | node v₃ l₃ r₃ => simp [relValues] at h₂₃
    | node v₂ l₂ r₂ => simp [relValues] at h₁₂
  | node v₁ l₁ r₁ =>
    cases t₂ with
    | empty => simp [relValues] at h₁₂
    | node v₂ l₂ r₂ =>
      cases t₃ with
      | empty => simp [relValues] at h₂₃
      | node v₃ l₃ r₃ =>
        simp [relValues] at h₁₂ h₂₃ ⊢
        rcases h₁₂ with ⟨hR₁₂, hl₁₂, hr₁₂⟩
        rcases h₂₃ with ⟨hR₂₃, hl₂₃, hr₂₃⟩
        have ihl : relValues R l₁ l₃ := relValues_trans R hR hl₁₂ hl₂₃
        have ihr : relValues R r₁ r₃ := relValues_trans R hR hr₁₂ hr₂₃
        exact ⟨hR _ _ _ hR₁₂ hR₂₃, ihl, ihr⟩
termination_by t₁

/-- Structural equality is the special case of `relValues` with `(=)`. -/
def same (t₁ t₂ : BST α) : Prop := relValues (· = ·) t₁ t₂


theorem same_empty_empty : same (.empty : BST α) (.empty : BST α) :=
  relValues_empty_empty _

theorem same_node_iff (v₁ : α) (l₁ r₁ : BST α) (v₂ : α) (l₂ r₂ : BST α) :
    same (.node v₁ l₁ r₁) (.node v₂ l₂ r₂) ↔ v₁ = v₂ ∧ same l₁ l₂ ∧ same r₁ r₂ := by
  simp [same, relValues_node_iff]

theorem same_refl (t : BST α) : same t t :=
  relValues_refl (· = ·) (λ _ => rfl) t

theorem same_symm {t₁ t₂ : BST α} (h : same t₁ t₂) : same t₂ t₁ :=
  relValues_symm (· = ·) (λ _ _ h => h.symm) h

theorem same_trans {t₁ t₂ t₃ : BST α} (h₁₂ : same t₁ t₂) (h₂₃ : same t₂ t₃) : same t₁ t₃ :=
  relValues_trans (· = ·) (λ _ _ _ h₁ h₂ => h₁.trans h₂) h₁₂ h₂₃

end BST

