import Mathlib
import vericontest.List

open List

/-!
# Maximum prefix sum

`maxPrefixSum_specificDuplicate nums` computes the maximum value among all prefix sums of `nums`
(including the empty prefix sum `0` at position 0). This is the natural dual of
`minPrefixSum_specificDuplicate` and is useful for problems like LeetCode 1749 ("Maximum Absolute
Sum of Any Subarray") and Kadane-like maximum-subarray algorithms.

The computation is done via a recursive helper `maxPrefixSum_go` that scans the
list left-to-right, updating a running sum and tracking the maximum seen so far.

See also `List.prefixSum_specificDuplicate` for individual prefix sums and `List.minPrefixSum_specificDuplicate`
for the minimum prefix sum.
-/

namespace List

/-! ### Core definitions -/

/-- Recursive helper: given `running` (sum of elements processed so far) and
`maxSoFar` (maximum prefix sum seen so far), find the maximum of these and all
prefix sums formed by continuing through `nums`.
At each step, the new prefix sum `running + x` is compared against `maxSoFar`. -/
def maxPrefixSum_go {α : Type} [Add α] [Max α] (nums : List α) (running : α) (maxSoFar : α) : α :=
  match nums with
  | [] => maxSoFar
  | x :: xs => maxPrefixSum_go xs (running + x) (max maxSoFar (running + x))

/-- The maximum prefix sum among positions 0..|nums|. Position 0 gives sum 0.
Works for any additive monoid with a maximum operation. -/
def maxPrefixSum_specificDuplicate {α : Type} [AddMonoid α] [Max α] (nums : List α) : α :=
  maxPrefixSum_go nums 0 0

/-! ### Helper lemma: the result never goes below the initial maximum -/

/-- `maxPrefixSum_go` never goes below `maxSoFar`: the running maximum can only
stay the same or increase. This is the invariant maintained by the recursion. -/
lemma maxPrefixSum_go_ge_maxSoFar {α : Type} [LinearOrder α] [Add α]
    (nums : List α) (running maxSoFar : α) :
    maxSoFar ≤ maxPrefixSum_go nums running maxSoFar := by
  induction nums generalizing running maxSoFar with
  | nil => simp [maxPrefixSum_go]
  | cons x xs ih =>
    rw [maxPrefixSum_go]
    have h1 : maxSoFar ≤ max maxSoFar (running + x) := le_max_left _ _
    have h2 : max maxSoFar (running + x) ≤ maxPrefixSum_go xs (running + x) (max maxSoFar (running + x)) :=
      ih (running + x) (max maxSoFar (running + x))
    exact le_trans h1 h2

/-! ### Relation to `prefixSum_specificDuplicate` -/

/-- The result of `maxPrefixSum_go` is bounded below by `running + prefixSum_specificDuplicate nums k`
for any prefix index `k` within bounds, assuming `running ≤ maxSoFar`.
This is the core inductive invariant. -/
lemma maxPrefixSum_go_ge_prefixSum {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (running maxSoFar : α) (k : Nat) (hk : k ≤ nums.length)
    (hinit : running ≤ maxSoFar) :
    running + prefixSum_specificDuplicate nums k ≤ maxPrefixSum_go nums running maxSoFar := by
  induction nums generalizing running maxSoFar k with
  | nil =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simp [maxPrefixSum_go, prefixSum_specificDuplicate]
    exact hinit
  | cons x xs ih =>
    rw [maxPrefixSum_go]
    cases' k with k
    · simp [prefixSum_specificDuplicate]
      have h1 : running ≤ maxSoFar := hinit
      have h2 : maxSoFar ≤ max maxSoFar (running + x) := le_max_left _ _
      have h3 : max maxSoFar (running + x) ≤ maxPrefixSum_go xs (running + x) (max maxSoFar (running + x)) :=
        maxPrefixSum_go_ge_maxSoFar xs (running + x) (max maxSoFar (running + x))
      exact le_trans h1 (le_trans h2 h3)
    · have hk_le : k ≤ xs.length := by
        have hlen : (x :: xs).length = xs.length + 1 := by simp
        rw [hlen] at hk
        omega
      have h_curSum_x : running + x ≤ max maxSoFar (running + x) := le_max_right _ _
      have h_prefix : prefixSum_specificDuplicate (x :: xs) (k + 1) = x + prefixSum_specificDuplicate xs k := by
        simp [prefixSum_specificDuplicate, sum_cons]
      rw [h_prefix]
      have ih' := ih (running + x) (max maxSoFar (running + x)) k hk_le h_curSum_x
      simpa [add_comm, add_left_comm, add_assoc] using ih'

/-! ### Main theorems about `maxPrefixSum_specificDuplicate` -/

/-- `maxPrefixSum_specificDuplicate nums` is never negative: it is always ≥ 0.
This holds because the empty prefix (position 0) has sum 0. -/
lemma maxPrefixSum_nonneg {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) : 0 ≤ maxPrefixSum_specificDuplicate nums := by
  have h := maxPrefixSum_go_ge_prefixSum nums 0 0 0 (Nat.zero_le _) (by rfl)
  simp [maxPrefixSum_specificDuplicate, prefixSum_specificDuplicate] at h
  exact h

/-- `maxPrefixSum_specificDuplicate nums` is an upper bound for every prefix sum:
for any `k ≤ nums.length`, `prefixSum_specificDuplicate nums k ≤ maxPrefixSum_specificDuplicate nums`. -/
lemma maxPrefixSum_ge_prefixSum {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (k : Nat) (hk : k ≤ nums.length) :
    prefixSum_specificDuplicate nums k ≤ maxPrefixSum_specificDuplicate nums := by
  have h := maxPrefixSum_go_ge_prefixSum nums 0 0 k hk (by rfl)
  simp [maxPrefixSum_specificDuplicate] at h
  simpa [zero_add] using h

/-! ### Achievement theorems — the max prefix sum is attained at some prefix -/

/-- `maxPrefixSum_go` is either `maxSoFar` (the initial value) or is
achieved as `running + prefixSum_specificDuplicate nums k` for some prefix index `k`. -/
lemma maxPrefixSum_go_achieved {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) (running maxSoFar : α) (hinit : running ≤ maxSoFar) :
    maxPrefixSum_go nums running maxSoFar = maxSoFar ∨
    ∃ k : Nat, k ≤ nums.length ∧ running + prefixSum_specificDuplicate nums k = maxPrefixSum_go nums running maxSoFar := by
  induction nums generalizing running maxSoFar with
  | nil => left; rfl
  | cons x xs ih =>
    rw [maxPrefixSum_go]
    by_cases hx : maxSoFar ≥ running + x
    · have hmax : max maxSoFar (running + x) = maxSoFar := max_eq_left hx
      rw [hmax]
      have hx' : running + x ≤ maxSoFar := hx
      rcases ih (running + x) maxSoFar hx' with h_eq | ⟨k, hk, h_eq'⟩
      · left; exact h_eq
      · right
        have h_prefix : prefixSum_specificDuplicate (x :: xs) (k + 1) = x + prefixSum_specificDuplicate xs k := by
          simp [prefixSum_specificDuplicate, sum_cons]
        refine ⟨k + 1, ?_, ?_⟩
        · have hlen : (x :: xs).length = xs.length + 1 := by simp
          rw [hlen]
          exact Nat.succ_le_succ hk
        · simpa [h_prefix, add_assoc] using h_eq'
    · have h_lt : maxSoFar < running + x := by
        by_contra! h
        exact hx h
      have hmax : max maxSoFar (running + x) = running + x := max_eq_right (le_of_lt h_lt)
      rw [hmax]
      rcases ih (running + x) (running + x) (le_refl _) with h_eq | ⟨k, hk, h_eq'⟩
      · right
        refine ⟨1, ?_, ?_⟩
        · simp
        · simp [prefixSum_specificDuplicate, h_eq]
      · right
        have h_prefix : prefixSum_specificDuplicate (x :: xs) (k + 1) = x + prefixSum_specificDuplicate xs k := by
          simp [prefixSum_specificDuplicate, sum_cons]
        refine ⟨k + 1, ?_, ?_⟩
        · have hlen : (x :: xs).length = xs.length + 1 := by simp
          rw [hlen]
          exact Nat.succ_le_succ hk
        · simpa [h_prefix, add_assoc] using h_eq'

/-- The maximum prefix sum is either `0` (the empty prefix) or is achieved
as `prefixSum_specificDuplicate nums k` for some prefix index `k`. -/
lemma maxPrefixSum_achieved_specificDuplicate {α : Type} [AddCommMonoid α] [LinearOrder α]
    (nums : List α) : maxPrefixSum_specificDuplicate nums = 0 ∨
    ∃ k : Nat, k ≤ nums.length ∧ prefixSum_specificDuplicate nums k = maxPrefixSum_specificDuplicate nums := by
  unfold maxPrefixSum_specificDuplicate
  rcases maxPrefixSum_go_achieved nums 0 0 (by rfl) with h | ⟨k, hk, h_eq⟩
  · left; exact h
  · right; refine ⟨k, hk, ?_⟩
    simpa [zero_add] using h_eq

end List
