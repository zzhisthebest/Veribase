import general.Nat.NumberTheory
import general.Nat.Search

namespace Nat


/-! ### Counting numbers satisfying a predicate -/

/--
Count how many `k` from `1` to `n` satisfy predicate `p`.
Uses classical decidability; `countWhere p 0 = 0`.
-/
noncomputable def countWhere (p : Nat → Prop) : Nat → Nat
  | 0 => 0
  | k + 1 => by
      classical
      exact (if p (k + 1) then 1 else 0) + countWhere p k

/-- Count how many `k` with `1 ≤ k ≤ n` satisfy the decidable predicate `p`.
This is the computable counterpart of `countWhere`, using `[DecidablePred p]`
instead of `classical`. Defined recursively for convenient induction proofs. -/
def countPred (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | m + 1 => countPred p m + (if p (m + 1) then 1 else 0)


lemma countPred_zero (p : Nat → Prop) [DecidablePred p] : countPred p 0 = 0 := rfl


lemma countPred_succ (p : Nat → Prop) [DecidablePred p] (m : Nat) :
    countPred p (m + 1) = countPred p m + (if p (m + 1) then 1 else 0) := rfl

/-- Count how many numbers `k` with `1 ≤ k ≤ n` satisfy a Boolean predicate `p`.
This is the computable counterpart of `countWhere`. -/
def countByPred (p : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih =>
    let k := i + 1
    if p k then ih + 1 else ih) n


theorem countByPred_zero (p : Nat → Bool) : countByPred p 0 = 0 := rfl


theorem countByPred_succ (p : Nat → Bool) (n : Nat) :
    countByPred p (n + 1) = countByPred p n + (if p (n + 1) then 1 else 0) := by
  simp [countByPred]
  split <;> omega

/-- Count how many numbers from `1` to `n` (inclusive) satisfy a Boolean predicate `p`.
This is the pattern-matching recursive definition, semantically equivalent to `countByPred`
but more convenient for induction proofs that case-split on the bound.

Both `countUpTo p n` and `countByPred p n` count numbers `1 ≤ k ≤ n` where `p k = true`. -/
def countUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if p (n + 1) then
      countUpTo p n + 1
    else
      countUpTo p n


theorem countUpTo_zero (p : Nat → Bool) : countUpTo p 0 = 0 := rfl

theorem countUpTo_succ_of_true (p : Nat → Bool) {n : Nat} (hp : p (n + 1) = true) :
    countUpTo p (n + 1) = countUpTo p n + 1 := by
  simp [countUpTo, hp]

theorem countUpTo_eq_countByPred (p : Nat → Bool) (n : Nat) : countUpTo p n = countByPred p n := by
  first
  | (solve
    | rfl
    | simp_all [countByPred, countUpTo]
    | omega
    | aesop
    | simp_all [countByPred, countUpTo, List.foldl, List.foldr]
    | simp_all [countByPred, countUpTo, Nat.absDiff]
    | induction n <;> simp_all [countByPred, countUpTo]
    | cases n <;> simp_all [countByPred, countUpTo])

/-- Count how many numbers `k` with `0 ≤ k ≤ n` satisfy a Boolean predicate `p`.
Unlike `countByPred` which counts from `1` to `n`, this counts from `0` to `n` (inclusive).
Defined via `List.range` and `List.filter` for convenient algebraic manipulation. -/
def countBy (p : Nat → Bool) (n : Nat) : Nat :=
  (List.range (n + 1)).filter p |>.length

theorem countBy_zero (p : Nat → Bool) : countBy p 0 = (if p 0 then 1 else 0) := by
  unfold countBy
  have : List.range 1 = [0] := by decide
  rw [this]
  by_cases h : p 0
  · simp [h]
  · simp [h]

theorem countBy_succ (p : Nat → Bool) (n : Nat) :
    countBy p (n + 1) = countBy p n + (if p (n + 1) then 1 else 0) := by
  unfold countBy
  rw [show List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] from List.range_succ (n + 1)]
  rw [List.filter_append, List.length_append]
  by_cases h : p (n + 1)
  · simp [h]
  · simp [h]

/-- Count how many indices `i` with `i < n` satisfy the Boolean predicate `p`.
Equivalent to `(List.range n).filter p |>.length`.
Unlike `countBy` which counts from `0` to `n` (inclusive), this counts the
half-open range `[0, n)`. Useful when iterating over array indices. -/
def countPositions (p : Nat → Bool) (n : Nat) : Nat :=
  (List.range n).filter p |>.length


lemma countPositions_zero (p : Nat → Bool) : countPositions p 0 = 0 := by
  simp [countPositions]

lemma countPositions_succ (p : Nat → Bool) (n : Nat) :
    countPositions p (n + 1) = countPositions p n + (if p n then 1 else 0) := by
  unfold countPositions
  rw [List.range_succ]
  by_cases h : p n
  · simp [h]
  · simp [h]

/-! ### `rangeFilterCount` — count numbers in [0, upto] satisfying a Prop predicate (List-based)

`rangeFilterCount p upto = |{i ∈ [0, upto] | p i}|`.
This is the List-based `Prop` counterpart of `Nat.countBy` (which uses `Bool`) and
`Nat.countSatisfying` (which uses `Finset`). Use this when you want a `List`-based representation
with direct `[DecidablePred p]` for predicates like `Nat.Prime`. -/

/-- Count how many numbers in `{0..upto}` satisfy the decidable predicate `p`.
Equivalent to `Nat.countBy (fun n => decide (p n)) upto` and `Nat.countSatisfying p upto`. -/
def rangeFilterCount (p : Nat → Prop) [DecidablePred p] (upto : Nat) : Nat :=
  (List.filter p (List.range (upto + 1))).length

lemma rangeFilterCount_zero (p : Nat → Prop) [DecidablePred p] :
    rangeFilterCount p 0 = (if decide (p 0) then 1 else 0) := by
  unfold rangeFilterCount
  simp [List.range_succ]
  by_cases h : decide (p 0)
  · have hp : p 0 := of_decide_eq_true h
    simp [h, hp]
  · have hnp : ¬ p 0 := by
      simpa using h
    simp [h, hnp]

lemma rangeFilterCount_succ (p : Nat → Prop) [DecidablePred p] (upto : Nat) :
    rangeFilterCount p (upto + 1) =
    rangeFilterCount p upto + (if decide (p (upto + 1)) then 1 else 0) := by
  unfold rangeFilterCount
  have hrange : List.range ((upto + 1) + 1) = List.range (upto + 1) ++ [upto + 1] := by
    simp [List.range_succ, add_assoc]
  rw [hrange]
  rw [List.filter_append]
  simp [List.length_append]
  by_cases h : decide (p (upto + 1))
  · have hp : p (upto + 1) := of_decide_eq_true h
    have hfilter : List.filter p [upto + 1] = [upto + 1] := by
      simp [hp]
    rw [hfilter]
    simp [List.length_append, h, hp]
  · have hnp : ¬ p (upto + 1) := by
      simpa using h
    have hfilter : List.filter p [upto + 1] = [] := by
      simp [hnp]
    rw [hfilter]
    simp [List.length_append, h, hnp]

/-! ### `Nat.count` — bridge to list-based filter representation

`Nat.count p m` (from mathlib) counts how many `k < m` satisfy `p k`.
The following lemma relates it to the list-based `((List.range m).filter p).length`,
which is used throughout general for `List`-based counting. -/

/-- `Nat.count p m` equals the length of `(List.range m).filter p`.
This bridges mathlib's `Nat.count` to the list-based filter representation. -/
lemma count_eq_filter_length (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Nat.count p m = ((List.range m).filter p).length := by
  rw [Nat.count, List.countP_eq_length_filter]

/-- Count how many `i` in `[0, n]` satisfy the `Prop` predicate `p`.
This is the `Prop`-based counterpart of `Nat.countBy` (which uses `Bool`).
Defined via `Finset.filter` on `Finset.range (n + 1)` for convenient use with Finset lemmas. -/
def countSatisfying (p : Nat → Prop) [DecidablePred p] (n : Nat) : Nat :=
  (Finset.filter p (Finset.range (n + 1))).card


theorem countSatisfying_zero (p : Nat → Prop) [DecidablePred p] : countSatisfying p 0 = (if p 0 then 1 else 0) := by
  unfold countSatisfying
  have : Finset.range 1 = {0} := by decide
  rw [this]
  have h_singleton : ({0} : Finset Nat) = insert 0 ∅ := by simp
  rw [h_singleton, Finset.filter_insert, Finset.filter_empty]
  by_cases h : p 0
  · simp [h]
  · simp [h]

theorem countSatisfying_succ (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    countSatisfying p (n + 1) = countSatisfying p n + (if p (n + 1) then 1 else 0) := by
  unfold countSatisfying
  have h_range : Finset.range ((n + 1) + 1) = insert (n + 1) (Finset.range (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using Finset.range_succ (n := n + 1)
  rw [h_range, Finset.filter_insert]
  split
  · rename_i h
    have h_not_mem_filter : (n + 1) ∉ Finset.filter p (Finset.range (n + 1)) := by
      intro hmem
      have h_mem_range : (n + 1) ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hmem).1
      have := Finset.mem_range.mp h_mem_range
      omega
    simp [Finset.card_insert_of_not_mem h_not_mem_filter]
  · rename_i h
    simp

/-- Relate `countSatisfying` (Prop-based) to `countBy` (Bool-based) via `decide`. -/
theorem countSatisfying_eq_countBy (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    countSatisfying p n = countBy (fun i => decide (p i)) n := by
  induction' n with k ih
  · rw [countSatisfying_zero, countBy_zero]
    simp
  · rw [countSatisfying_succ, countBy_succ]
    simp [ih]

/-! ### Summing numbers satisfying a predicate -/

/-- Sum numbers from `1` to `n` (inclusive) that satisfy predicate `p`.
This is the sum analog of `countByPred`. For example,
`foldSumPred Nat.Prime 10 = 2 + 3 + 5 + 7 = 17`. -/
def foldSumPred (p : Nat → Prop) [DecidablePred p] : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih =>
    let x := k.succ
    if p x then ih + x else ih)


theorem foldSumPred_zero (p : Nat → Prop) [DecidablePred p] : foldSumPred p 0 = 0 := rfl

theorem foldSumPred_succ (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    foldSumPred p (n + 1) = foldSumPred p n + (if p (n + 1) then n + 1 else 0) := by
  induction' n with m ih
  · simp [foldSumPred]
  · simp [foldSumPred, ih]
    split <;> omega

theorem foldSumPred_eq_foldSumPred_of_iff (p q : Nat → Prop) [DecidablePred p] [DecidablePred q] (n : Nat)
    (h : ∀ k, 1 ≤ k → k ≤ n → (p k ↔ q k)) : foldSumPred p n = foldSumPred q n := by
  induction n with
  | zero => simp [foldSumPred]
  | succ n ih =>
    have hn := ih (fun k hk hkn => h k hk (by omega))
    change (if p (n+1) then foldSumPred p n + (n+1) else foldSumPred p n) =
      (if q (n+1) then foldSumPred q n + (n+1) else foldSumPred q n)
    simp only [hn, h (n+1) (by omega) (by omega)]

/-! ### Sum of filtered range `[0, n)` via `List.range` -/

/-- Sum of all numbers in `[0, n)` that satisfy a decidable predicate `p`.
This is the list-based counterpart to `foldSumPred` (which sums from `1` to `n`),
including `0` in the range and using `List.range`/`List.filter` for convenient
algebraic manipulation. -/
def sumFilteredBelow (p : Nat → Prop) [DecidablePred p] (n : Nat) : Nat :=
  ((List.range n).filter p).sum

/-- Recurrence: the sum over `[0, n+1)` decomposes as the sum over `[0, n)` plus
the contribution of `n` (which is `n` if `p n` holds, otherwise `0`). -/
theorem sumFilteredBelow_succ (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    sumFilteredBelow p (n+1) = sumFilteredBelow p n + (if p n then n else 0) := by
  unfold sumFilteredBelow
  rw [List.range_succ]
  by_cases h : p n
  · simp [h]
  · simp [h]

/-! ### Combined sum and count over a filtered range `[0, limit]`

These functions compute both the sum and the count of elements in `[0, limit]`
that satisfy a decidable predicate, in a single pass. Generalizations of the
`prime_sums` pattern (which computed sum and count of primes up to `limit`). -/

/-- Fold over the range `n, …, 0`: for each `i` where `p i` holds, add `i` to the
accumulated sum `s` and increment the count `c`. Returns `(final sum, final count)`.
This is a single-pass computation that avoids materializing intermediate lists or Finsets. -/
def filterRangeFold (p : Nat → Prop) [DecidablePred p] (n : Nat) (s c : Nat) : Nat × Nat :=
  match n with
  | 0 => if h : p 0 then (s, c + 1) else (s, c)
  | m + 1 =>
    if h : p (m + 1) then
      filterRangeFold p m (s + (m + 1)) (c + 1)
    else
      filterRangeFold p m s c

/-- Sum and count of elements in `[0, limit]` satisfying predicate `p`.
Returns `(sum, count)` where `sum` is the sum of all `k ∈ {0,…,limit}` with `p k`
and `count` is the number of such `k`. This is a convenience wrapper around
`filterRangeFold` with initial accumulators `(0, 0)`. -/
def rangeSumCount (p : Nat → Prop) [DecidablePred p] (limit : Nat) : Nat × Nat :=
  filterRangeFold p limit 0 0


theorem rangeSumCount_zero (p : Nat → Prop) [DecidablePred p] :
    rangeSumCount p 0 = (if p 0 then (0, 1) else (0, 0)) := by
  unfold rangeSumCount filterRangeFold
  split <;> simp

end Nat

namespace Nat

/-! ### Power of two predicate -/

/-- `IsPowerOfTwo m` holds when `m` is a power of two, i.e. there exists `k` such that `m = 2 ^ k`.
This includes `m = 1` (since `1 = 2 ^ 0`). Note that `IsPowerOfTwo 0` is true because `0 = 2 ^ 0` does
not hold; `0` is not a power of two in this definition. -/
def IsPowerOfTwo (m : Nat) : Prop :=
  ∃ k : Nat, m = 2 ^ k

/-! ### Linear recurrence list generation -/

/-- Generate the first `n` terms of a 2-term linear recurrence with step function `f`
and initial values `(a, b)`. Returns a list of length `n` where the sequence is:
`[a, b, f a b, f b (f a b), f (f a b) (f b (f a b)), ...]`.

This is a generalized version of `Nat.fibList` (which specializes `f := (· + ·)`).
Works over any type `α` with the iteration count given as a `Nat`. -/
def linrecTwoList {α : Type} (f : α → α → α) (n : Nat) (a b : α) : List α :=
  match n with
  | 0 => []
  | k+1 => a :: linrecTwoList f k b (f a b)

/-- The length of `linrecTwoList f n a b` is exactly `n`. -/
lemma linrecTwoList_length {α : Type} (f : α → α → α) (n : Nat) (a b : α) :
    (linrecTwoList f n a b).length = n := by
  induction' n with n ih generalizing a b
  · rfl
  · unfold linrecTwoList
    simp [ih]

/-! ### Tribonacci numbers -/

/-- The i-th Tribonacci number: T(0)=0, T(1)=1, T(2)=1, T(n+3)=T(n)+T(n+1)+T(n+2). -/
def trib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n+3 => trib (n+2) + trib (n+1) + trib n


lemma trib_recurrence (i : Nat) : trib (i+3) = trib (i+2) + trib (i+1) + trib i := by
  simp [trib]

end Nat
