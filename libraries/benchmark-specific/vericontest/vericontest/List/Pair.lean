import Mathlib
import vericontest.Nat

open List

namespace List

/-! ### Pair prefix count (predicate-based, two-list prefix counting)

`pairPrefixCount` counts how many of the first `k` pairs `(xs[i], ys[i])` satisfy
a boolean predicate `pred`. Out-of-bounds access counts as `0`. The return type `γ`
is polymorphic (any `AddMonoid γ` with `One γ`), typically `Nat` or `Int`.

This generalizes `countPairsEq` (which is equality-based) to arbitrary boolean
predicates, and is polymorphic in the counting type.

This pattern appears in problems like CF 467A ("George and Accommodation") where
we count rooms satisfying `q - p ≥ 2` from two parallel lists of room capacities. -/

/-- Count how many of the first `k` pairs `(xs[i], ys[i])` satisfy `pred`.
Formally: `∑_{i=0}^{k-1} (if pred xs[i] ys[i] then 1 else 0)`, where
out-of-bounds access contributes `0`.
The return type `γ` can be any `AddMonoid` with `One`, typically `Nat` or `Int`. -/
def pairPrefixCount {α β γ : Type} [AddMonoid γ] [One γ]
    (xs : List α) (ys : List β) (pred : α → β → Bool) : Nat → γ
  | 0 => 0
  | k + 1 =>
    pairPrefixCount xs ys pred k +
      (match xs[k]?, ys[k]? with
       | some x, some y => if pred x y then 1 else 0
       | _, _ => 0)

/-- Uniqueness / equational principle for `pairPrefixCount`:
if a function `f` satisfies the same recurrence as `pairPrefixCount`, they are equal.
This is useful for proving that an alternative function computes the same value. -/
theorem pairPrefixCount_eq_of_rec {α β γ : Type} [AddMonoid γ] [One γ]
    (xs : List α) (ys : List β) (pred : α → β → Bool) (f : Nat → γ) (k : Nat)
    (h_zero : f 0 = 0)
    (h_succ : ∀ n, f (n + 1) =
      f n + (match xs[n]?, ys[n]? with
        | some x, some y => if pred x y then 1 else 0
        | _, _ => 0)) :
    pairPrefixCount xs ys pred k = f k := by
  induction k with
  | zero => exact h_zero.symm
  | succ k ih =>
    rw [pairPrefixCount, ih, h_succ]

/-- Casting a `Nat`-valued `pairPrefixCount` to `Int` agrees with computing it in `Int`
directly. This is useful when the result needs to participate in integer arithmetic. -/
@[simp]
theorem pairPrefixCount_nat_cast {α β : Type} (xs : List α) (ys : List β)
    (pred : α → β → Bool) (k : Nat) :
    ((pairPrefixCount (γ := Nat) xs ys pred k : Nat) : Int) =
      pairPrefixCount (γ := Int) xs ys pred k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [pairPrefixCount, ih]
    split <;> simp

/-! ### Pair predicate at specific indices

`pairNeRefAndEq a ref i j` checks that the elements at positions `i` and `j` in `a`
are both different from `ref` and equal to each other. Uses `getElem!` (total access),
so out-of-bounds indices produce a default value that may affect the result.

This pattern appears in combinatorial search over lists where we need to find two
elements that are equal to each other but not equal to a distinguished reference
value (e.g., finding a non-leg pair in stick-counting problems like "MUH and Sticks"). -/

/-- Check that `a[i]!` and `a[j]!` are both different from `ref` and equal to each other. -/
def pairNeRefAndEq {α : Type} [DecidableEq α] [Inhabited α] (a : List α) (ref : α) (i j : Nat) : Bool :=
  decide (a[i]! ≠ ref) && decide (a[j]! ≠ ref) && decide (a[i]! = a[j]!)

/-! ### Pairwise prefix sum

`pairPrefixSum score xs ys k` computes `∑_{i=0}^{k-1} score xs[i] ys[i]`, where
out-of-bounds access (when one list is shorter than `k`) contributes `0`.
This is the sum-extended counterpart of `pairPrefixCount`: instead of counting
`Bool` predicates, it sums arbitrary `ℤ`-valued scores.

This pattern appears in problems that require summing pairwise contributions
from two lists element-by-element, e.g., lock digit distance problems (CF 540A),
where the total cost is the sum of pairwise digit distances. -/

/-- Sum of `score(xs[i], ys[i])` for `i = 0..k-1`. Out-of-bounds contributes `0`. -/
def pairPrefixSum {α β : Type} (score : α → β → Int) : List α → List β → Nat → Int
  | _, _, 0 => 0
  | x :: xs, y :: ys, k + 1 => pairPrefixSum score xs ys k + score x y
  | _, _, _ => 0

/-- If `score x y` is nonnegative whenever `x` and `y` satisfy their respective
preconditions (`leftOk` / `rightOk`), and all elements in `xs` and `ys` satisfy
those preconditions, then `pairPrefixSum score xs ys k` is nonnegative for any `k`. -/
lemma pairPrefixSum_nonneg {α β : Type} (score : α → β → Int)
    (xs : List α) (ys : List β) (k : Nat)
    (leftOk : α → Prop) (rightOk : β → Prop)
    (hxs : ∀ x ∈ xs, leftOk x) (hys : ∀ y ∈ ys, rightOk y)
    (hscore : ∀ x y, leftOk x → rightOk y → 0 ≤ score x y) :
    0 ≤ pairPrefixSum score xs ys k := by
  induction k generalizing xs ys hxs hys with
  | zero =>
      simp [pairPrefixSum]
  | succ k ih =>
      cases xs with
      | nil =>
          simp [pairPrefixSum]
      | cons x xs =>
          cases ys with
          | nil =>
              simp [pairPrefixSum]
          | cons y ys =>
              simp [pairPrefixSum]
              apply add_nonneg
              · apply ih
                · intro x' hx'
                  exact hxs x' (by simp [hx'])
                · intro y' hy'
                  exact hys y' (by simp [hy'])
              · exact hscore x y (hxs x (by simp)) (hys y (by simp))

/-! ### Divisible pair counting

`countDivisibleMatchesBefore s d j k` counts how many indices `k' < k` satisfy
`pairSumDivisible s[j] s[k'] d` (using `0` for out-of-bounds access). This is the
inner loop: given a fixed index `j`, count matches among earlier elements.

`countDivisiblePairsInPrefix s d n` counts all ordered pairs `(i, k)` with
`k < i < n` such that `pairSumDivisible s[i] s[k] d`. This is the outer loop:
for each `i`, count matching earlier elements.

Together these generalize the pair-counting pattern from problems like
"Pairs of Songs With Total Durations Divisible by 60" (LC 1010) to any
divisor `d`. -/

/-! ### Generic ordered-pair counting (predicate-based, single-list)

`countMatchesBeforeIdx pred as idx k` counts how many indices `j < k` satisfy
`pred as[j]! as[idx]!`. This is the inner loop: given a fixed index `idx`, count
matches among previous elements.

`countOrderedPairsInPrefix pred as n` counts all ordered pairs `(j, i)` with
`j < i < n` such that `pred as[j]! as[i]!`. This is the outer loop: for each `i`,
count matching earlier elements.

Together these generalize `countDivisibleMatchesBefore` / `countDivisiblePairsInPrefix`
(which are specialized to `Nat.pairSumDivisible`) to arbitrary boolean predicates
and arbitrary types. They also generalize `pair_count_impl` / `match_count_impl`
from LeetCode 1128 ("Number of Equivalent Domino Pairs"). -/

/-- Count how many indices `j < k` satisfy `pred as[j]! as[idx]!`.
Uses `getElem!` for total access (returns default if out-of-bounds).
Returns `ℤ` for convenience in integer arithmetic. -/
def countMatchesBeforeIdx {α : Type u} [Inhabited α] (pred : α → α → Bool) (as : List α) (idx : ℕ) : ℕ → ℤ
  | 0 => 0
  | bound + 1 => countMatchesBeforeIdx pred as idx bound + (if pred (as[bound]!) (as[idx]!) then 1 else 0)

/-- Count all ordered pairs `(j, i)` with `j < i < n` such that `pred as[j]! as[i]!`.
Equivalently, `∑_{i=0}^{n-1} countMatchesBeforeIdx pred as i i`. -/
def countOrderedPairsInPrefix {α : Type u} [Inhabited α] (pred : α → α → Bool) (as : List α) : ℕ → ℤ
  | 0 => 0
  | n + 1 => countOrderedPairsInPrefix pred as n + countMatchesBeforeIdx pred as n n

/-- Congruence lemma: if two predicates are pointwise equal, their match counts are equal. -/
theorem countMatchesBeforeIdx_congr {α : Type u} [Inhabited α] {p q : α → α → Bool}
    (h : ∀ a b, p a b = q a b) (as : List α) (idx n : ℕ) :
    countMatchesBeforeIdx p as idx n = countMatchesBeforeIdx q as idx n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countMatchesBeforeIdx, ih, h]

/-- Congruence lemma: if two predicates are pointwise equal, their ordered pair counts are equal. -/
theorem countOrderedPairsInPrefix_congr {α : Type u} [Inhabited α] {p q : α → α → Bool}
    (h : ∀ a b, p a b = q a b) (as : List α) (n : ℕ) :
    countOrderedPairsInPrefix p as n = countOrderedPairsInPrefix q as n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countOrderedPairsInPrefix, ih, countMatchesBeforeIdx_congr h]

/-- Count how many `k' < k` satisfy `Nat.pairSumDivisible s[j]? s[k']? d`.
Uses `getD 0` for out-of-bounds access (indices beyond the list length). -/
def countDivisibleMatchesBefore (s : List Nat) (d j k : Nat) : Nat :=
  if k = 0 then
    0
  else
    let vj := (s[j]?).getD 0
    let ve := (s[k - 1]?).getD 0
    (if Nat.pairSumDivisible vj ve d then 1 else 0) + countDivisibleMatchesBefore s d j (k - 1)
termination_by k

/-- Count all ordered pairs `(i, k)` with `k < i < n` such that
`Nat.pairSumDivisible s[i]? s[k]? d`. -/
def countDivisiblePairsInPrefix (s : List Nat) (d n : Nat) : Nat :=
  if n = 0 then
    0
  else
    countDivisiblePairsInPrefix s d (n - 1) + countDivisibleMatchesBefore s d (n - 1) (n - 1)
termination_by n

@[simp]
lemma countDivisibleMatchesBefore_zero (s : List Nat) (d j : Nat) :
    countDivisibleMatchesBefore s d j 0 = 0 := by
  rw [countDivisibleMatchesBefore]; rfl

lemma countDivisibleMatchesBefore_succ (s : List Nat) (d j k : Nat) :
    countDivisibleMatchesBefore s d j (k + 1) =
    (if Nat.pairSumDivisible ((s[j]?).getD 0) ((s[k]?).getD 0) d then 1 else 0) +
    countDivisibleMatchesBefore s d j k := by
  conv => lhs; rw [countDivisibleMatchesBefore]
  simp

@[simp]
lemma countDivisiblePairsInPrefix_zero (s : List Nat) (d : Nat) :
    countDivisiblePairsInPrefix s d 0 = 0 := by
  rw [countDivisiblePairsInPrefix]; rfl

lemma countDivisiblePairsInPrefix_succ (s : List Nat) (d n : Nat) :
    countDivisiblePairsInPrefix s d (n + 1) =
    countDivisiblePairsInPrefix s d n + countDivisibleMatchesBefore s d n n := by
  conv => lhs; rw [countDivisiblePairsInPrefix]
  simp

/-! ### Any distinct pair satisfying a binary predicate

`anyDistinctPair_specificDuplicate arr p` returns `true` iff there exist distinct indices `i ≠ j`
such that `p arr[i] arr[j] = true`. The check is symmetric: for each head `x`
and tail `y`, both `p x y` and `p y x` are tested via `||`.

This combinator appears in problems that check whether any pair of distinct
list elements satisfies a given relation (e.g., "does any element equal twice
another?" — LeetCode 1346). -/

/-- Return `true` iff there exist distinct indices `i ≠ j` such that
`p arr[i] arr[j] = true`.

```
anyDistinctPair_specificDuplicate [] p = false
anyDistinctPair_specificDuplicate (x :: xs) p = (xs.any (λ y => p x y || p y x)) || anyDistinctPair_specificDuplicate xs p
```
-/
def anyDistinctPair_specificDuplicate {α : Type} (arr : List α) (p : α → α → Bool) : Bool :=
  match arr with
  | [] => false
  | x :: xs => (xs.any (λ y => p x y || p y x)) || anyDistinctPair_specificDuplicate xs p

/-- `anyDistinctPair_specificDuplicate arr p = true` iff there exist distinct indices `i ≠ j`
in `Fin arr.length` such that `p arr[i] arr[j] = true`. -/
lemma anyDistinctPair_eq_iff {α : Type} (arr : List α) (p : α → α → Bool) :
    (anyDistinctPair_specificDuplicate arr p = true) ↔ (∃ (i j : Fin arr.length), i ≠ j ∧ p (arr[i]) (arr[j]) = true) := by
  induction arr with
  | nil => simp [anyDistinctPair_specificDuplicate]
  | cons x xs ih =>
    simp only [anyDistinctPair_specificDuplicate, Bool.or_eq_true, List.any_eq_true, ih,
      List.length_cons]
    constructor
    · intro h
      rcases h with h | ⟨i, j, hij, hp⟩
      · obtain ⟨y, hy, hp⟩ := h
        obtain ⟨i, hi⟩ := List.get_of_mem hy
        rcases hp with hp | hp
        · exact ⟨0, i.succ, by intro h; have := congrArg Fin.val h; simp at this,
            by simpa [← hi] using hp⟩
        · exact ⟨i.succ, 0, by intro h; have := congrArg Fin.val h; simp at this,
            by simpa [← hi] using hp⟩
      · exact ⟨i.succ, j.succ, by simpa using hij, by simpa using hp⟩
    · rintro ⟨i, j, hij, hp⟩
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (hij rfl)
        | succ j =>
          left
          exact ⟨xs[j], List.getElem_mem j.isLt, Or.inl (by simpa using hp)⟩
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          left
          exact ⟨xs[i], List.getElem_mem i.isLt, Or.inr (by simpa using hp)⟩
        | succ j =>
          right
          exact ⟨i, j, by simpa using hij, by simpa using hp⟩

/-! ### Predicate-based ordered pair counting (list-index predicate)

`countPairsFromIdx nums p i j` counts how many indices `k` with `i < k < j`
satisfy `p nums i k`. This is the inner loop: for a fixed first index `i`,
count matching second indices `k` below `j`.

`countOrderedPairsFromIdx nums p i` counts all ordered pairs `(i', j')` with
`i ≤ i' < j' < nums.length` such that `p nums i' j'` holds. This is the outer
loop: accumulate across all first indices `i'` starting from `i`.

Together these generalize `count_inner` / `count_all` from LeetCode 1512
("Number of Good Pairs") to arbitrary boolean predicates over list-index pairs.
-/

/-- Count how many indices `k` with `i < k < j` satisfy `p nums i k`.
This is the inner loop of ordered-pair counting with a fixed first index. -/
def countPairsFromIdx {α : Type} (nums : List α) (p : List α → Nat → Nat → Bool) (i j : Nat) : Nat :=
  if j ≤ i + 1 then
    0
  else
    countPairsFromIdx nums p i (j - 1) + (if p nums i (j - 1) then 1 else 0)
termination_by j
decreasing_by
  omega

/-- If two predicates agree pointwise, `countPairsFromIdx` produces equal results. -/
lemma countPairsFromIdx_congr {α : Type} (nums : List α) (p q : List α → Nat → Nat → Bool)
    (h : ∀ i' j', p nums i' j' = q nums i' j') (i j : Nat) :
    countPairsFromIdx nums p i j = countPairsFromIdx nums q i j := by
  induction' j with j IH
  · unfold countPairsFromIdx; rfl
  · unfold countPairsFromIdx
    by_cases hle : j.succ ≤ i + 1
    · simp [hle]
    · have hsub : j.succ - 1 = j := by omega
      simp [hle, hsub, IH, h i j]

/-- Count all ordered pairs `(i', j')` with `i ≤ i' < j' < nums.length`
such that `p nums i' j'` holds. Recursively accumulates from `i` upward,
using `countPairsFromIdx` for the inner loop at each first index. -/
def countOrderedPairsFromIdx {α : Type} (nums : List α) (p : List α → Nat → Nat → Bool) (i : Nat) : Nat :=
  if nums.length ≤ i then
    0
  else
    countOrderedPairsFromIdx nums p (i + 1) + countPairsFromIdx nums p i nums.length
termination_by nums.length - i
decreasing_by
  omega

/-- If two predicates agree pointwise, `countOrderedPairsFromIdx` produces equal results. -/
lemma countOrderedPairsFromIdx_congr {α : Type} (nums : List α) (p q : List α → Nat → Nat → Bool)
    (h : ∀ i' j', p nums i' j' = q nums i' j') (i : Nat) :
    countOrderedPairsFromIdx nums p i = countOrderedPairsFromIdx nums q i := by
  have h_total : ∀ d, ∀ i, nums.length - i = d →
      countOrderedPairsFromIdx nums p i = countOrderedPairsFromIdx nums q i := by
    intro d
    induction' d with d IH
    · intro i h_eq
      have hi : nums.length ≤ i := by omega
      unfold countOrderedPairsFromIdx
      simp [hi]
    · intro i h_eq
      have hi : i < nums.length := by omega
      unfold countOrderedPairsFromIdx
      have hle : ¬ nums.length ≤ i := by omega
      simp [hle]
      have h_next : nums.length - (i + 1) = d := by omega
      rw [IH (i + 1) h_next, countPairsFromIdx_congr nums p q h i nums.length]
  exact h_total (nums.length - i) i rfl

/-! ### Unordered pair counting (predicate-based, single-list)

`pairwiseCount pred as` counts the number of unordered pairs `(i, j)` with `i < j`
such that `pred as[i] as[j]` holds. For each element `x` at the head, it counts how
many tail elements `y` satisfy `pred x y`, then recurses on the tail.

This is simpler than `countOrderedPairsInPrefix` / `countMatchesBeforeIdx` because
it operates on elements directly rather than via `getElem!` indexing. It does not
require `Inhabited` and works with any predicate `α → α → Bool`.

This pattern appears in problems that require counting pair relationships
(e.g., LeetCode 3027 "Count Pairs of Points" and many combinatorics problems). -/

/-- Count the number of unordered pairs `(i, j)` with `i < j` in `as` such that
`pred as[i] as[j]` holds. For each head element, counts matching tail elements
via `filter`, then recurses. -/
def pairwiseCount {α : Type} (pred : α → α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (xs.filter (pred x)).length + pairwiseCount pred xs

@[simp]
lemma pairwiseCount_nil {α : Type} (pred : α → α → Bool) :
    pairwiseCount pred [] = 0 := rfl

@[simp]
lemma pairwiseCount_cons {α : Type} (pred : α → α → Bool) (x : α) (xs : List α) :
    pairwiseCount pred (x :: xs) = (xs.filter (pred x)).length + pairwiseCount pred xs := rfl

/-- If the predicate is always `true`, `pairwiseCount` counts all unordered pairs,
which equals `n * (n - 1) / 2` where `n = as.length`. -/
lemma pairwiseCount_eq_choose_two {α : Type} (as : List α) :
    pairwiseCount (λ _ _ => true) as = as.length * (as.length - 1) / 2 := by
  rw [← Nat.choose_two_right]
  induction as with
  | nil => simp [pairwiseCount]
  | cons a as ih =>
    simpa [pairwiseCount, Nat.choose_succ_succ, Nat.choose_one_right] using
      congrArg (fun n => as.length + n) ih

/-- If two predicates are pointwise equal, their `pairwiseCount` results are equal. -/
lemma pairwiseCount_congr {α : Type} {p q : α → α → Bool} (h : ∀ a b, p a b = q a b) (as : List α) :
    pairwiseCount p as = pairwiseCount q as := by
  induction as with
  | nil => rfl
  | cons x xs ih =>
    simp only [pairwiseCount, ih]
    have hpred : (fun y => p x y) = (fun y => q x y) := by
      ext y; exact h x y
    simp [hpred]

end List
