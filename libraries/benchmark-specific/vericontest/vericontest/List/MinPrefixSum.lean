import Mathlib
import vericontest.List

open List

/-!
# Minimum prefix sum

`minPrefixSum_specificDuplicate nums` computes the minimum value among all prefix sums of `nums`
(including the empty prefix sum `0` at position 0). This is useful for problems
where the minimum prefix sum determines a threshold, e.g., LeetCode 1413
("Minimum Value to Get Positive Step by Step Sum").

The computation is done via a recursive helper `minPrefixSum_go` that scans the
list left-to-right, updating a running sum and tracking the minimum seen so far.

See also `List.prefixSum_specificDuplicate` for individual prefix sums.
-/

namespace List

/-! ### Core definitions -/

/-- Recursive helper: given `running` (sum of elements processed so far) and
`minSoFar` (minimum prefix sum seen so far), find the minimum of these and all
prefix sums formed by continuing through `nums`.
Works for any type with addition and a minimum operation. -/
def minPrefixSum_go {α : Type} [Add α] [Min α] (nums : List α) (running : α) (minSoFar : α) : α :=
  match nums with
  | [] => min minSoFar running
  | x :: xs => minPrefixSum_go xs (running + x) (min minSoFar running)

/-- The minimum prefix sum among positions 0..|nums|. Position 0 gives sum 0.
Works for any additive monoid with a minimum operation. -/
def minPrefixSum_specificDuplicate {α : Type} [AddMonoid α] [Min α] (nums : List α) : α :=
  minPrefixSum_go nums 0 0

/-! ### Helper lemma: the result never exceeds the initial minimum -/

/-- `minPrefixSum_go` never exceeds `minSoFar`: the running minimum can only
stay the same or decrease. This is the invariant maintained by the recursion. -/
lemma minPrefixSum_go_le_minSoFar {α : Type} [LinearOrder α] [Add α]
    (nums : List α) (running minSoFar : α) :
    minPrefixSum_go nums running minSoFar ≤ minSoFar := by
  induction' nums with x xs ih generalizing running minSoFar
  · simp [minPrefixSum_go]
  · simp [minPrefixSum_go]
    have h := ih (running + x) (min minSoFar running)
    exact le_trans h (min_le_left _ _)

/-! ### Relation to `prefixSum_specificDuplicate` -/

/-- The result of `minPrefixSum_go` is bounded by `running + prefixSum_specificDuplicate nums k`
for any prefix index `k` within bounds. This is the core inductive invariant. -/
lemma minPrefixSum_go_le_prefixSum {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (running minSoFar : α) (k : Nat) (hk : k ≤ nums.length) :
    minPrefixSum_go nums running minSoFar ≤ running + prefixSum_specificDuplicate nums k := by
  induction' nums with x xs ih generalizing running minSoFar k
  · -- nil case: k must be 0
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simp [minPrefixSum_go, prefixSum_specificDuplicate]
  · -- cons case: nums = x :: xs
    simp [minPrefixSum_go]
    by_cases hk0 : k = 0
    · subst hk0
      simp [prefixSum_specificDuplicate]
      have h := minPrefixSum_go_le_minSoFar xs (running + x) (min minSoFar running)
      exact le_trans h (min_le_right _ _)
    · rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨k', hk_eq⟩
      subst hk_eq
      have hk'_le : k' ≤ xs.length := by
        have hlen : (x :: xs).length = xs.length + 1 := by simp
        rw [hlen] at hk
        omega
      have h_prefix : prefixSum_specificDuplicate (x :: xs) (k' + 1) = x + prefixSum_specificDuplicate xs k' := by
        simp [prefixSum_specificDuplicate]
      rw [h_prefix]
      have h_ih := ih (running + x) (min minSoFar running) k' hk'_le
      simpa [add_comm, add_left_comm, add_assoc] using h_ih

/-! ### Main theorems about `minPrefixSum_specificDuplicate` -/

/-- `minPrefixSum_specificDuplicate nums` is never positive: it is always ≤ 0.
This holds because the empty prefix (position 0) has sum 0. -/
lemma minPrefixSum_nonpos {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) : minPrefixSum_specificDuplicate nums ≤ 0 := by
  have h := minPrefixSum_go_le_prefixSum nums 0 0 0 (Nat.zero_le _)
  simp [minPrefixSum_specificDuplicate, prefixSum_specificDuplicate] at h
  exact h

/-- `minPrefixSum_specificDuplicate nums` is a lower bound for every prefix sum:
for any `k ≤ nums.length`, `minPrefixSum_specificDuplicate nums ≤ prefixSum_specificDuplicate nums k`. -/
lemma minPrefixSum_le_prefixSum {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (k : Nat) (hk : k ≤ nums.length) :
    minPrefixSum_specificDuplicate nums ≤ prefixSum_specificDuplicate nums k := by
  have h := minPrefixSum_go_le_prefixSum nums 0 0 k hk
  simp [minPrefixSum_specificDuplicate] at h
  simpa [zero_add] using h

/-! ### Achievement theorems — the min prefix sum is attained at some prefix -/

/-- `minPrefixSum_go` is either `min minSoFar running` (the base value) or is
achieved as `running + prefixSum_specificDuplicate nums k` for some prefix index `k`. -/
lemma minPrefixSum_go_achieved {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (running minSoFar : α) :
    minPrefixSum_go nums running minSoFar = min minSoFar running ∨
    ∃ k : Nat, k ≤ nums.length ∧ running + prefixSum_specificDuplicate nums k = minPrefixSum_go nums running minSoFar := by
  induction' nums with x xs ih generalizing running minSoFar
  · left; rfl
  · rw [minPrefixSum_go]
    rcases ih (running + x) (min minSoFar running) with h_eq | ⟨k, hk, h_eq'⟩
    · -- h_eq : go xs (running + x) (min minSoFar running) = min (min minSoFar running) (running + x)
      by_cases hx : min minSoFar running ≤ running + x
      · -- the old min is still the overall min
        left
        rw [h_eq, min_eq_left hx]
      · -- the new prefix sum is smaller, so it achieves the min at position 1
        have hx' : running + x ≤ min minSoFar running := by
          have h_total := le_total (min minSoFar running) (running + x)
          rcases h_total with h | h
          · exact absurd h hx
          · exact h
        right
        refine ⟨1, by simp, ?_⟩
        simp [prefixSum_specificDuplicate, h_eq, min_eq_right hx']
    · -- h_eq' : (running + x) + prefixSum_specificDuplicate xs k = go xs (running + x) (min minSoFar running)
      right
      refine ⟨k + 1, ?_, ?_⟩
      · simpa [length_cons] using Nat.succ_le_succ hk
      · simpa [prefixSum_specificDuplicate, sum_cons, add_assoc] using h_eq'

/-- The minimum prefix sum is either `0` (the empty prefix) or is achieved
as `prefixSum_specificDuplicate nums k` for some prefix index `k`. -/
lemma minPrefixSum_achieved_specificDuplicate {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) : minPrefixSum_specificDuplicate nums = 0 ∨
    ∃ k : Nat, k ≤ nums.length ∧ prefixSum_specificDuplicate nums k = minPrefixSum_specificDuplicate nums := by
  unfold minPrefixSum_specificDuplicate
  rcases minPrefixSum_go_achieved nums 0 0 with h | ⟨k, hk, h_eq⟩
  · left; simpa using h
  · right; refine ⟨k, hk, ?_⟩
    simpa [zero_add] using h_eq

end List
