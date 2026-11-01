import Mathlib
import vericontest.List

open List

/-!
# Consecutive prefix

`consecutivePrefixLen` computes the length of the longest prefix where each adjacent pair
differs by a given `step`. `consecutivePrefixSum` sums the elements in that prefix.

These generalize patterns from LeetCode 2996 ("Smallest Missing Integer Greater Than
Sequential Prefix Sum"), where the problem asks for the sum of the longest prefix with
consecutive integers (step = 1), and then finds the smallest missing integer ≥ that sum.

The concepts are reusable for any problem involving "find the longest prefix where
elements form an arithmetic progression with a given step."
-/

namespace List

/-- Length of the longest prefix where each adjacent pair differs by `step`.
For `a :: b :: tail`, if `b = a + step` then the prefix extends through `b` and we
recurse on `b :: tail`; otherwise the prefix stops at `a` and returns `1`.

Examples:
- `consecutivePrefixLen [1,2,3,5,6] 1 = 3`  (1,2,3 are consecutive with step 1)
- `consecutivePrefixLen [2,4,6,7,9] 2 = 3`  (2,4,6 differ by step 2)
- `consecutivePrefixLen [1,3,5] 1 = 1`      (first pair 1→3 is not step 1) -/
def consecutivePrefixLen {α : Type} [Add α] [DecidableEq α] (nums : List α) (step : α) : ℕ :=
  match nums with
  | [] | [_] => nums.length
  | a :: b :: tail =>
    if b = a + step then
      1 + consecutivePrefixLen (b :: tail) step
    else
      1

/-- Sum of elements in the consecutive prefix (with given step).
Equivalent to `prefixSum_specificDuplicate nums (consecutivePrefixLen nums step)`. -/
def consecutivePrefixSum {α : Type} [AddMonoid α] [DecidableEq α] (nums : List α) (step : α) : α :=
  prefixSum_specificDuplicate nums (consecutivePrefixLen nums step)

/-- The consecutive prefix sum (step = 1) is at least 1 when the list is nonempty
and all elements are ≥ 1. This is a key lower-bound property used in problems where
a missing integer is sought above the consecutive prefix sum. -/
lemma consecutivePrefixSum_ge_one (nums : List ℤ) (h_ne : nums ≠ [])
    (h_all_ge_one : ∀ v ∈ nums, 1 ≤ v) : 1 ≤ consecutivePrefixSum nums 1 := by
  have hlen : ∀ (a : ℤ) (xs : List ℤ), 1 ≤ consecutivePrefixLen (a :: xs) 1 := by
    intro a xs
    cases xs with
    | nil => simp [consecutivePrefixLen]
    | cons b xs => simp only [consecutivePrefixLen]; split <;> omega
  cases nums with
  | nil => contradiction
  | cons a xs =>
    have ha : 1 ≤ a := h_all_ge_one a (by simp)
    have hn := hlen a xs
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : consecutivePrefixLen (a :: xs) 1 ≠ 0)
    unfold consecutivePrefixSum prefixSum_specificDuplicate
    rw [hk, List.take_succ_cons, List.sum_cons]
    have hs : 0 ≤ (xs.take k).sum := List.sum_nonneg (fun x hx => by
      have := h_all_ge_one x (by simp only [List.mem_cons]; exact Or.inr (List.mem_of_mem_take hx))
      omega)
    omega

end List
