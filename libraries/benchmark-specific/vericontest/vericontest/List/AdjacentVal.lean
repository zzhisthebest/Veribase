import Mathlib

open List

/-!
# Value-Position Adjacency

`allAdjacent_specificDuplicate nums` asserts that every element of `nums` is within distance 1 of its index:
`|nums[i] - i| ≤ 1` for all `i`. Equivalently, `nums[i] ≤ i + 1` and `i ≤ nums[i] + 1`.

This property characterizes **ideal permutations** (LeetCode 775 "Global and Local Inversions"):
a permutation where all inversions are local. In an ideal permutation, each element can only
appear at its "correct" position, one position before, or one position after.

The concept is reusable in any problem involving permutation inversions or element-position
distance constraints.
-/

namespace List

/-- `allAdjacent_specificDuplicate nums` holds when every element of `nums` is within 1 of its index:
`nums[i] ≤ i + 1` and `i ≤ nums[i] + 1` for all valid indices `i`.
Equivalently, `|nums[i] - i| ≤ 1` for all `i`. -/
def allAdjacent_specificDuplicate (nums : List Nat) : Prop :=
  ∀ (i : Fin nums.length), nums.get i ≤ i.val + 1 ∧ i.val ≤ nums.get i + 1

end List
