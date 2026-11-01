import Mathlib
import general.Nat.ArithmeticCore

namespace Nat

/-! ### Folding over a range -/

/-- Left-fold a binary operation over `[g 0, g 1, ..., g hi]` (inclusive).
The function `g` maps each index to the value to combine via `f`. -/
def foldlRange {α : Type} (f : α → α → α) (g : Nat → α) (init : α) (hi : Nat) : α :=
  (List.range (hi + 1)).foldl (λ acc i => f acc (g i)) init

/-- XOR all numbers from `0` to `n` inclusive. -/
def xor1To (n : Nat) : Nat :=
  foldlRange Nat.xor id 0 n

/-- `rangeAll p hi` returns `true` iff `p i` holds for every natural number `i`
from `0` to `hi` (inclusive). Equivalent to `(List.range (hi+1)).all p = true`.
For the propositional equivalence, see `rangeAll_eq_true_iff`. -/
def rangeAll (p : Nat → Bool) (hi : Nat) : Bool :=
  (List.range (hi+1)).all p

/-- `Nat.rangeAll p hi = true` iff `p i = true` for all `i ≤ hi`. -/
lemma rangeAll_eq_true_iff (p : Nat → Bool) (hi : Nat) :
    rangeAll p hi = true ↔ ∀ i, i ≤ hi → p i = true := by
  unfold rangeAll
  rw [List.all_eq_true]
  constructor
  · intro h i hi_le
    apply h
    rw [List.mem_range]
    omega
  · intro h i hi_mem
    rw [List.mem_range] at hi_mem
    apply h i
    omega

/-! ### Interval size on `Nat × Nat` -/

/-- The size (length) of an interval `[l, r]`, defined as `r - l + 1`.
Returns the number of integers in the inclusive range `[l, r]` when `l ≤ r`;
for `l > r`, the result is `0` (since natural subtraction clips at `0`). -/
def intervalSize (p : Nat × Nat) : Nat := p.2 - p.1 + 1

/-! ### Boolean range predicate -/

/-- Boolean check: `lo ≤ x` and `x ≤ hi`. Returns `true` iff `x` lies in the inclusive
range `[lo, hi]`. Designed for use with `List.all` and similar boolean list operations.
For example, `Nat.between 1 9 5 = true` and `Nat.between 1 9 10 = false`. -/
@[reducible]
def between (lo hi x : Nat) : Bool :=
  decide (lo ≤ x ∧ x ≤ hi)

/-- Boolean check: `start ≤ x` and `x < start + len`. Returns `true` iff `x` lies
in the half-open interval `[start, start+len)`. Unlike `Nat.between` which uses
inclusive bounds, this uses start + length semantics common in array indexing
and subarray iteration. -/
def interval_covers (start len x : Nat) : Bool :=
  decide (start ≤ x) && decide (x < start + len)

/-- `Nat.interval_covers start len x = true` iff `start ≤ x ∧ x < start + len`. -/

lemma interval_covers_iff (start len x : Nat) : interval_covers start len x = true ↔ (start ≤ x ∧ x < start + len) := by
  simp [interval_covers]

/-! ### Division-by-two termination lemmas -/

/-- For any `n : Nat`, `(n+1) / 2 < n+1`. A convenient termination lemma for
divide-by-2 recursion on `Nat.succ`. Unlike `div_two_lt_self` which requires `1 < n`,
this version works for all `n` including `n = 0`. -/
lemma succ_div_two_lt (n : Nat) : (Nat.succ n) / 2 < Nat.succ n :=
  Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- The sum of the halves is strictly less than the sum:
`(a+1)/2 + (b+1)/2 < (a+1) + (b+1)`.
Used in termination proofs for divide-by-2 recursions on pairs. -/
lemma succ_div_two_add_lt (a b : Nat) :
    (Nat.succ a) / 2 + (Nat.succ b) / 2 < Nat.succ a + Nat.succ b := by
  have ha : (Nat.succ a) / 2 < Nat.succ a := succ_div_two_lt a
  have hb : (Nat.succ b) / 2 < Nat.succ b := succ_div_two_lt b
  exact Nat.add_lt_add ha hb

end Nat

namespace Nat

/-!
# Folding `max` over numeric index ranges

This module provides `maxOverJ`, a general-purpose function that iterates
over a numeric range `[j, len)` with a two-argument function `f : Nat → Nat → Nat`,
computing the maximum of an initial `best` value and all `f i k` for `k ∈ [j, len)`.

This is useful for problems that need to maximize a function over a 2D grid
of indices (e.g., "maximum area rectangle in histogram", "maximum subarray
product", etc.).
-/

/-- Given `f : Nat → Nat → Nat`, iterate `k` from `j` to `len-1`, computing the maximum
of `best` and all `f i k`. Returns `best` when `j ≥ len`. -/
def maxOverJ (f : Nat → Nat → Nat) (i j len : Nat) (best : Nat) : Nat :=
  if h : j < len then
    let val := f i j
    maxOverJ f i (j + 1) len (max best val)
  else
    best
termination_by len - j
decreasing_by
  omega

/-- Lemma: `maxOverJ` result is ≥ the initial best value. -/
lemma maxOverJ_ge_best (f : Nat → Nat → Nat) (i j len best : Nat) :
    maxOverJ f i j len best ≥ best := by
  let P (k : Nat) : Prop :=
    ∀ (i j len best : Nat), len - j = k → maxOverJ f i j len best ≥ best
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i j len best hm
      unfold maxOverJ
      by_cases hj : j < len
      · simp [hj]
        have h_lt : len - (j + 1) < k := by
          rw [← hm]
          have hpos : 0 < len - j := Nat.sub_pos_of_lt hj
          omega
        have h_rec := ih (len - (j + 1)) h_lt i (j + 1) len (max best (f i j)) rfl
        exact le_trans (le_max_left _ _) h_rec
      · simp [hj]
  exact hP (len - j) i j len best rfl

/-- Lemma: For any `k` with `j ≤ k < len`, `maxOverJ` result is ≥ `f i k`. -/
lemma maxOverJ_ge_val (f : Nat → Nat → Nat) (i j len best k : Nat)
    (hjk : j ≤ k) (hk : k < len) :
    maxOverJ f i j len best ≥ f i k := by
  let P (d : Nat) : Prop :=
    ∀ (i j len best k : Nat), len - j = d → j ≤ k → k < len →
      maxOverJ f i j len best ≥ f i k
  have hP : ∀ d, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h m ih =>
      intro i j len best k hm hjk hk
      unfold maxOverJ
      by_cases hj : j < len
      · simp [hj]
        by_cases h_eq : j = k
        · rw [h_eq]
          have h_rec := maxOverJ_ge_best f i (k + 1) len (max best (f i k))
          exact le_trans (le_max_right _ _) h_rec
        · have h_lt : len - (j + 1) < m := by
            rw [← hm]
            have hpos : 0 < len - j := Nat.sub_pos_of_lt hj
            omega
          have hjk_succ : j + 1 ≤ k := by omega
          have h_rec := ih (len - (j + 1)) h_lt i (j + 1) len (max best (f i j)) k rfl hjk_succ hk
          simpa
      · simp [hj]
        omega
  exact hP (len - j) i j len best k rfl hjk hk

/-- Lemma: `maxOverJ` result is either the initial `best` or equals some `f i k`
with `j ≤ k < len`. -/
lemma maxOverJ_attained (f : Nat → Nat → Nat) (i j len best : Nat) :
    maxOverJ f i j len best = best ∨
    (∃ k, j ≤ k ∧ k < len ∧ maxOverJ f i j len best = f i k) := by
  let P (d : Nat) : Prop :=
    ∀ (i j len best : Nat), len - j = d →
      maxOverJ f i j len best = best ∨
      (∃ k, j ≤ k ∧ k < len ∧ maxOverJ f i j len best = f i k)
  have hP : ∀ d, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h m ih =>
      intro i j len best hm
      unfold maxOverJ
      by_cases hj : j < len
      · simp [hj]
        have h_lt : len - (j + 1) < m := by
          rw [← hm]
          have hpos : 0 < len - j := Nat.sub_pos_of_lt hj
          omega
        have h_rec := ih (len - (j + 1)) h_lt i (j + 1) len (max best (f i j)) rfl
        rcases h_rec with (h_eq | ⟨k', hk_j1, hk_len, hk_eq⟩)
        · -- result = max best (f i j)
          rw [h_eq]
          by_cases hbest : f i j ≤ best
          · left; omega
          · right
            refine ⟨j, le_refl j, hj, ?_⟩
            omega
        · -- result = f i k for some k ≥ j+1
          right
          refine ⟨k', by omega, hk_len, hk_eq⟩
      · simp [hj]
  exact hP (len - j) i j len best rfl

end Nat

namespace Nat


/-! ### Folding over subarray index pairs -/

/-- Fold a function over all suffix indices `j` starting at `start`, i.e., for all `j` such
that `start ≤ j < n`, apply `f start j acc`. The second argument to `f` is the end index `j`,
the third is the accumulator.

This is the inner loop for iterating over all subarray interval pairs `(i, j)`. -/
def foldSubarraysFrom (f : Nat → Nat → β → β) (start n : Nat) (init : β) : β :=
  (List.range (n - start)).foldl (fun acc d => f start (start + d) acc) init

/-- Fold a function over all subarray interval pairs `(i, j)` with `0 ≤ i ≤ j < n`.
Equivalent to nesting `foldSubarraysFrom f i n` for each `i` from `0` to `n-1`.

This is a general combinator useful for any problem that needs to iterate over all
subarray index ranges of an array of size `n`. See also `countPairs` for the specialized
version that counts pairs satisfying a Boolean predicate. -/
def foldSubarrays (f : Nat → Nat → β → β) (n : Nat) (init : β) : β :=
  (List.range n).foldl (fun acc i => foldSubarraysFrom f i n acc) init

/-! ### Counting index pairs satisfying a predicate -/

/-- Count the number of index pairs `(i, j)` with `0 ≤ i ≤ j < n` such that `pred i j` holds.

This is a general combinator useful for any problem that counts subarrays or substrings
satisfying a binary index predicate. -/
def countPairs (n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  foldSubarrays (fun i j acc => if pred i j then acc + 1 else acc) n 0

/-! ### Counting all ordered index pairs (i, j) — full n² grid -/

/-- Count the number of ordered index pairs `(i, j)` with `0 ≤ i < n` and `0 ≤ j < n`
such that `pred i j` holds. This counts **all** n² ordered pairs, including reflexive
pairs `(i, i)` and both `(i, j)` and `(j, i)` for `i ≠ j`.

Contrast with `countPairs` which only counts pairs with `i ≤ j` (subarray index pairs). -/
def countAllOrderedPairs (n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  (List.range n).foldl
    (fun acc i =>
      (List.range n).foldl
        (fun acc' j =>
          if pred i j then acc' + 1 else acc')
        acc)
    0

/-- Count the number of ordered index pairs `(i, j)` with `0 ≤ i < n` and `0 ≤ j < m`
such that `pred i j` holds. This is the rectangular (n × m) generalization of
`countAllOrderedPairs`. -/
def countOrderedPairsRect (n m : Nat) (pred : Nat → Nat → Bool) : Nat :=
  (List.range n).foldl
    (fun acc i =>
      acc + ((List.range m).filter (fun j => pred i j)).length)
    0

/-- Count the number of strictly ordered index pairs `(i, j)` with `0 ≤ i < j < n`
such that `pred i j` holds.

This is `|{(i, j) | i < j < n ∧ pred i j}|`.

Contrast with `countPairs` which counts pairs with `i ≤ j`, and
`countAllOrderedPairs` which counts all n² pairs including `i = j` and `j < i`. -/
def countStrictOrderedPairs (n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  ((List.range n).product (List.range n)).filter (fun (i, j) => i < j ∧ pred i j) |>.length

/-! ### Maximum subarray length by index predicate -/

/-- Find the maximum length (`j - i + 1`) of a subarray index pair `(i, j)` with
`0 ≤ i ≤ j < n` such that the binary index predicate `p i j` holds. Returns `0` if no
valid pair satisfies `p`.

This is a brute-force O(n²) search over all index pairs and is useful when the
predicate is computed from the original data externally (e.g., via a precomputed
comparison array or memoized pairwise test). For subarray predicates that directly
operate on lists, see `List.maxSubarrayLen` in `general/List/Subarray`. -/
def maxSubarrayLenWhere (n : Nat) (p : Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun best i =>
    (List.range n).foldl (fun best j =>
      if h : i ≤ j ∧ j < n then
        let len := j - i + 1
        if p i j then Nat.max best len else best
      else
        best
    ) best
  ) 0


lemma maxSubarrayLenWhere_zero (p : Nat → Nat → Bool) : maxSubarrayLenWhere 0 p = 0 := rfl

/-- If `maxSubarrayLenWhere n p = 0`, then no pair `(i, j)` with `i ≤ j < n` satisfies `p`. -/
lemma maxSubarrayLenWhere_eq_zero_iff (n : Nat) (p : Nat → Nat → Bool) :
    maxSubarrayLenWhere n p = 0 ↔ ∀ i j, i ≤ j → j < n → p i j = false := by
  let step := fun (i best j : Nat) =>
    if i ≤ j ∧ j < n then if p i j then max best (j-i+1) else best else best
  have inner (l : List Nat) (i a : Nat) :
      l.foldl (step i) a = 0 ↔ a = 0 ∧ ∀ j ∈ l, i ≤ j → j < n → p i j = false := by
    induction l generalizing a with
    | nil => simp
    | cons j js ih =>
      rw [List.foldl_cons, ih]
      by_cases hv : i ≤ j ∧ j < n
      · cases hp : p i j
        · simp [step, hv, hp, List.mem_cons]
        · have hlen : j-i+1 ≠ 0 := by omega
          simp [step, hv, hp, Nat.max_eq_zero_iff, hlen, List.mem_cons]
      · simp [step, hv, List.mem_cons]
        tauto
  have outer (l : List Nat) (a : Nat) :
      l.foldl (fun best i => (List.range n).foldl (step i) best) a = 0 ↔
        a = 0 ∧ ∀ i ∈ l, ∀ j < n, i ≤ j → p i j = false := by
    induction l generalizing a with
    | nil => simp
    | cons i is ih =>
      rw [List.foldl_cons, ih, inner]
      simp [List.mem_range, List.mem_cons, and_assoc]
      aesop
  change (List.range n).foldl (fun best i => (List.range n).foldl (step i) best) 0 = 0 ↔ _
  rw [outer]
  simp only [true_and, List.mem_range]
  constructor
  · intro h i j hij hj; exact h i (by omega) j hj hij
  · intro h i _ j hj hij; exact h i j hij hj

end Nat

namespace Nat


/-! ### Sum of a function over a range -/

/-- Sum of `f i` for `i` from `0` to `n-1`, computed via `List.foldl`.
Equivalent to `(Finset.range n).sum f`; the `foldl` formulation is convenient
for proofs that already use `List.foldl` machinery. -/
def sum_range (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f i) 0

/-! ### Maximum of a function over a range -/

/-- `maxOverRange f n` returns the maximum value of `f` over the integer range `[0, n]`.

This is a general combinator: given any `f : Nat → Nat` and a bound `n`, compute
`max {f 0, f 1, ..., f n}`. Companion to `sum_range` which sums over `[0, n-1]`. -/
def maxOverRange (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => Nat.max acc (f i)) 0

/-- Induction step: max over [0, n+1] = max(max over [0, n], f(n+1)). -/
theorem maxOverRange_succ (f : Nat → Nat) (n : Nat) :
    maxOverRange f (n + 1) = Nat.max (maxOverRange f n) (f (n + 1)) := by
  simp [maxOverRange, List.range_succ, List.foldl_append]

/-- Every value `f i` for `i ≤ n` is bounded by `maxOverRange f n`. -/
theorem le_maxOverRange (f : Nat → Nat) (n i : Nat) (h : i ≤ n) : f i ≤ maxOverRange f n := by
  induction' n with m ih
  · have : i = 0 := Nat.eq_zero_of_le_zero h
    subst this
    simp [maxOverRange, List.range_succ, Nat.zero_max]
  · rw [maxOverRange_succ f m]
    rcases Nat.eq_or_lt_of_le h with (rfl | hlt)
    · exact le_max_right _ _
    · have hle : i ≤ m := Nat.le_of_lt_succ hlt
      have ih' := ih hle
      exact le_trans ih' (le_max_left _ _)

/-- The maximum is actually attained: there exists an `s ≤ n` such that `f s = maxOverRange f n`. -/
lemma maxOverRange_exists_eq (f : Nat → Nat) (n : Nat) :
    ∃ s, s ≤ n ∧ f s = maxOverRange f n := by
  induction' n with k ih
  · refine ⟨0, by omega, ?_⟩
    simp [maxOverRange, List.range_succ, Nat.zero_max]
  · rw [maxOverRange_succ f k]
    rcases ih with ⟨s, hs, heq⟩
    by_cases h : f (k+1) ≤ maxOverRange f k
    · have hmax_eq : Nat.max (maxOverRange f k) (f (k+1)) = maxOverRange f k := by
        apply Nat.le_antisymm
        · exact (Nat.max_le).mpr ⟨le_refl _, h⟩
        · apply Nat.le_max_left
      rw [hmax_eq]
      exact ⟨s, by omega, heq⟩
    · have hmax_eq : Nat.max (maxOverRange f k) (f (k+1)) = f (k+1) := by
        apply Nat.le_antisymm
        · exact (Nat.max_le).mpr ⟨by omega, le_refl _⟩
        · apply Nat.le_max_right
      rw [hmax_eq]
      exact ⟨k+1, by omega, rfl⟩

/-! ### Maximum over a suffix range -/

/-- `maxOverRangeFrom f sz idx` returns the maximum of `f i` for `i` from `idx` to `sz - 1`.
Returns `0` if `idx ≥ sz` (empty range).

This generalizes `maxOverRange` (which always starts at index `0`) by allowing an
arbitrary start index. Useful for iterating over suffix ranges of an array. -/
def maxOverRangeFrom (f : Nat → Nat) (sz idx : Nat) : Nat :=
  if h : idx < sz then
    max (f idx) (maxOverRangeFrom f sz (idx + 1))
  else
    0
termination_by sz - idx
decreasing_by
  simp_wf
  omega

/-- `maxOverRangeFrom f sz idx` is an upper bound for all `f i` with `idx ≤ i < sz`. -/
lemma maxOverRangeFrom_ge (f : Nat → Nat) (sz idx i : Nat) (hidx : idx ≤ i) (hi : i < sz) :
    f i ≤ maxOverRangeFrom f sz idx := by
  refine maxOverRangeFrom.induct sz
    (λ idx' => ∀ i, idx' ≤ i → i < sz → f i ≤ maxOverRangeFrom f sz idx')
    ?_ ?_ idx i hidx hi
  · intro x hx_lt IH j hj_le hj_lt
    rw [maxOverRangeFrom, dif_pos hx_lt]
    rcases Nat.eq_or_lt_of_le hj_le with (rfl | hlt)
    · apply le_max_left
    · have hx1_le_j : x + 1 ≤ j := by omega
      have h_ih := IH j hx1_le_j hj_lt
      exact le_trans h_ih (le_max_right _ _)
  · intro x hx_nlt j hj_le hj_lt
    omega

/-- If `idx < sz`, then `maxOverRangeFrom f sz idx` equals `f i` for some `i` with `idx ≤ i < sz`. -/
lemma maxOverRangeFrom_exists (f : Nat → Nat) (sz idx : Nat) (h_idx : idx < sz) :
    ∃ i, idx ≤ i ∧ i < sz ∧ maxOverRangeFrom f sz idx = f i := by
  refine maxOverRangeFrom.induct sz
    (λ idx' => (idx' < sz → ∃ i, idx' ≤ i ∧ i < sz ∧ maxOverRangeFrom f sz idx' = f i))
    ?_ ?_ idx h_idx
  · intro x hx_lt IH _
    rw [maxOverRangeFrom, dif_pos hx_lt]
    by_cases hle : maxOverRangeFrom f sz (x + 1) ≤ f x
    · refine ⟨x, le_refl _, hx_lt, ?_⟩
      rw [Nat.max_eq_left hle]
    · have hlt' : f x < maxOverRangeFrom f sz (x + 1) := Nat.lt_of_not_ge hle
      rw [Nat.max_eq_right (Nat.le_of_lt hlt')]
      by_cases h_next : x + 1 < sz
      · have h_ih := IH h_next
        rcases h_ih with ⟨i, hi_le, hi_lt, hi_eq⟩
        refine ⟨i, by omega, hi_lt, hi_eq⟩
      · have hzero : maxOverRangeFrom f sz (x + 1) = 0 := by
          rw [maxOverRangeFrom, dif_neg h_next]
        rw [hzero] at hlt'
        omega
  · intro x hx_nlt hx_lt
    omega

/-! ### Minimum of a function over a range -/

/-- `minOverRange f n` returns the minimum value of `f` over the integer range `[0, n]`.

This is the companion to `maxOverRange`. Unlike `maxOverRange` which starts from `0`
(the identity for `Nat.max`), `minOverRange` starts from `f 0` since `0` is not
the identity for `Nat.min` — `Nat.min 0 x = 0` always. -/
def minOverRange (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => Nat.min acc (f i)) (f 0)

/-- Induction step: min over [0, n+1] = min(min over [0, n], f(n+1)). -/
theorem minOverRange_succ (f : Nat → Nat) (n : Nat) :
    minOverRange f (Nat.succ n) = min (minOverRange f n) (f (Nat.succ n)) := by
  dsimp [minOverRange]
  have h_range : List.range (Nat.succ n + 1) = List.range (n + 1) ++ [Nat.succ n] := by
    calc
      List.range (Nat.succ n + 1) = List.range (n + 1 + 1) := by
        simp [Nat.succ_eq_add_one, add_comm, add_assoc]
      _ = List.range (n + 1) ++ [n + 1] := by rw [List.range_succ]
      _ = List.range (n + 1) ++ [Nat.succ n] := by simp
  rw [h_range, List.foldl_append, List.foldl]
  simp

/-- Every value `f i` for `i ≤ n` is bounded below by `minOverRange f n`. -/
theorem minOverRange_le (f : Nat → Nat) (n i : Nat) (h : i ≤ n) : minOverRange f n ≤ f i := by
  induction' n with m ih
  · have : i = 0 := Nat.eq_zero_of_le_zero h
    subst this
    simp [minOverRange, List.range_succ, Nat.min_self]
  · rw [minOverRange_succ f m]
    rcases Nat.eq_or_lt_of_le h with (rfl | hlt)
    · exact min_le_right _ _
    · have hle : i ≤ m := Nat.le_of_lt_succ hlt
      have ih' := ih hle
      exact le_trans (min_le_left _ _) ih'

/-! ### Maximum over a filtered index range -/

/-- `maxFilterRange p f start count best` searches the range `[start, start + count)`
    for the maximum value of `f i` among indices `i` where `p i = true`.
    `best` is the initial best value (carried forward from indices `< start`).
    Returns the maximum among all `i` in `[0, start + count)` satisfying `p`.

    This generalizes `maxOverRange` by adding a predicate filter `p`, a start offset,
    and an explicit initial `best` value. Use `maxOverRange` for the simpler case
    of finding the max of `f i` over `i ∈ [0, n]` without filtering. -/
def maxFilterRange (p : Nat → Bool) (f : Nat → Nat) (start count best : Nat) : Nat :=
  match count with
  | 0 => best
  | k + 1 =>
    if p start then
      if best < f start then
        maxFilterRange p f (start + 1) k (f start)
      else
        maxFilterRange p f (start + 1) k best
    else
      maxFilterRange p f (start + 1) k best

/-- The result of `maxFilterRange` is at least the initial `best` value. -/
lemma maxFilterRange_ge_best (p : Nat → Bool) (f : Nat → Nat) (start count best : Nat) :
    best ≤ maxFilterRange p f start count best := by
  induction' count with k ih generalizing start best
  · rw [maxFilterRange]
  · rw [maxFilterRange]
    split_ifs with hp hlt
    · have hle : f start ≤ maxFilterRange p f (start + 1) k (f start) := ih (start + 1) (f start)
      omega
    · exact ih (start + 1) best
    · exact ih (start + 1) best

/-- Either the result equals the initial `best`, or there exists a valid index
    in `[start, start + count)` whose value equals the result. -/
lemma maxFilterRange_exists (p : Nat → Bool) (f : Nat → Nat) (start count best : Nat) :
    maxFilterRange p f start count best = best ∨
    (∃ m, start ≤ m ∧ m < start + count ∧
      p m = true ∧
      f m = maxFilterRange p f start count best) := by
  match count with
  | 0 => left; rw [maxFilterRange]
  | k+1 =>
    rw [maxFilterRange]
    split_ifs with hp hlt
    · rcases maxFilterRange_exists p f (start + 1) k (f start) with (heq | hnew)
      · right
        refine ⟨start, le_refl _, ?_, hp, ?_⟩
        · omega
        · simpa [heq]
      · rcases hnew with ⟨m, hm_low, hm_high, hm_sat, hm_cnt⟩
        right
        refine ⟨m, by omega, ?_, hm_sat, ?_⟩
        · omega
        · simpa
    · rcases maxFilterRange_exists p f (start + 1) k best with (heq | hnew)
      · left; simpa
      · rcases hnew with ⟨m, hm_low, hm_high, hm_sat, hm_cnt⟩
        right
        refine ⟨m, by omega, ?_, hm_sat, ?_⟩
        · omega
        · simpa
    · rcases maxFilterRange_exists p f (start + 1) k best with (heq | hnew)
      · left; simpa
      · rcases hnew with ⟨m, hm_low, hm_high, hm_sat, hm_cnt⟩
        right
        refine ⟨m, by omega, ?_, hm_sat, ?_⟩
        · omega
        · simpa


end Nat
