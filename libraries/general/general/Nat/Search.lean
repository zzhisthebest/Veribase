import general.Nat.ArithmeticCore
import general.Nat.Representation

namespace Nat

/-! ### Nat.find utilities -/

/-- If `P` is a nonempty predicate on `Nat`, then `Nat.find h_nonempty` satisfies `P`
and is minimal among all `n` that satisfy `P`. -/
lemma find_satisfies_and_min {P : Nat → Prop} [DecidablePred P] (h_nonempty : ∃ n, P n) :
    P (Nat.find h_nonempty) ∧ ∀ n, P n → Nat.find h_nonempty ≤ n :=
  ⟨Nat.find_spec h_nonempty, λ n hn => Nat.find_min' h_nonempty hn⟩

/-- If a predicate `P : ℕ → Prop` is nonempty, there exists a minimal `m` satisfying `P`.
Bundles `Nat.find_spec` and `Nat.find_min'` into a single existential. Uses `classical`
to avoid requiring `[DecidablePred P]` from callers. -/
lemma exists_min {P : Nat → Prop} (h_nonempty : ∃ n, P n) :
    ∃ m, P m ∧ (∀ k, P k → m ≤ k) := by
  classical
    let m := Nat.find h_nonempty
    exact ⟨m, Nat.find_spec h_nonempty, λ k hk => Nat.find_min' h_nonempty hk⟩

/-- If `P` is a nonempty predicate, then `Nat.find h` satisfies `P` and all strictly
smaller indices do not. This is the contrapositive-style counterpart to `find_satisfies_and_min`,
convenient when the proof goal asks for `∀ k, k < Nat.find h → ¬ P k`. -/
lemma find_satisfies_and_not_lt {P : Nat → Prop} [DecidablePred P] (h : ∃ n, P n) :
    P (Nat.find h) ∧ ∀ k, k < Nat.find h → ¬ P k :=
  ⟨Nat.find_spec h, fun _ hk => Nat.find_min h hk⟩

/-- If a predicate `P` holds for all `n : ℕ`, then `0` is the minimum index satisfying `P`.
This is a specialization of `exists_min` when the predicate is universally true.
The result packages the zero witness with the proof that `0` is smaller than any other
witness, matching the common `∃ min, min = 0 ∧ P min ∧ (∀ c', P c' → min ≤ c')` pattern. -/
lemma exists_min_zero_of_forall {P : Nat → Prop} (h : ∀ n, P n) :
    ∃ (c : Nat), c = 0 ∧ P c ∧ (∀ (c' : Nat), P c' → c ≤ c') := by
  refine ⟨0, rfl, h 0, ?_⟩
  intro c' _
  exact Nat.zero_le c'

/-- `Nat.find_min` wrapped for Bool-valued predicates: if `m` is below the minimum `k`
with `p k = true`, then `decide (p m) = false`. -/
lemma find_min_decide {p : Nat → Bool} (h_exists : ∃ k, p k = true) {m : Nat}
    (hm : m < Nat.find h_exists) : decide (p m) = false := by
  have h_not : ¬ p m = true := Nat.find_min h_exists hm
  have h_false : p m = false := by
    cases h : p m
    · rfl
    · exfalso; exact h_not h
  simp [h_false]

/-- The computational pattern "if there exists `t` with `P t`, return the minimal
such `t` (as `Int`), else return `-1`" satisfies the expected disjunctive
postcondition for any predicate `P : Nat → Prop`.
Specifically, either `result = -1` and no `t` satisfies `P`,
or `result = (t : Int)` where `t` is minimal satisfying `P`.
This bundles `Nat.find_spec` and `Nat.find_min` for the common competitive
programming convention of returning `-1` as a sentinel for "not found".
Uses classical decidability via `open Classical` — the lemma is noncomputable. -/
lemma minimal_find_int_spec {P : Nat → Prop} [∀ n, Decidable (P n)] [Decidable (∃ t : Nat, P t)] :
    ((if h : ∃ t : Nat, P t then (Nat.find h : Int) else (-1 : Int)) = (-1 : Int) ∧ ¬ ∃ t : Nat, P t) ∨
    (∃ t : Nat, (if h : ∃ t : Nat, P t then (Nat.find h : Int) else (-1 : Int)) = (t : Int) ∧ P t ∧ ∀ s : Nat, s < t → ¬ P s) := by
  by_cases h : ∃ t : Nat, P t
  · right
    have heq : (if h' : ∃ t : Nat, P t then (Nat.find h' : Int) else (-1 : Int)) = (Nat.find h : Int) := by
      simp [h]
    rw [heq]
    refine ⟨Nat.find h, rfl, Nat.find_spec h, ?_⟩
    intro s hs
    exact Nat.find_min h hs
  · left
    have heq : (if h' : ∃ t : Nat, P t then (Nat.find h' : Int) else (-1 : Int)) = (-1 : Int) := by
      simp [h]
    rw [heq]
    exact ⟨rfl, h⟩

/-- A bound-aware version of `Nat.find_spec`: if there exists `m ≥ n` satisfying `P`, then
`Nat.find` produces a result `≥ n` satisfying `P`, and it's minimal among all such `m` satisfying
both the bound and `P`. -/
lemma find_spec_of_bound {n : Nat} {P : Nat → Prop} [DecidablePred P]
    (h_ex : ∃ m, n ≤ m ∧ P m) :
    n ≤ Nat.find h_ex ∧ P (Nat.find h_ex) ∧ (∀ m, n ≤ m → P m → Nat.find h_ex ≤ m) := by
  have h_spec := Nat.find_spec h_ex
  rcases h_spec with ⟨hle, hP⟩
  refine ⟨hle, hP, ?_⟩
  intro m hmle hmP
  exact Nat.find_min' h_ex ⟨hmle, hmP⟩

/-- If `h` witnesses `∃ n, P n ∧ Q n` and `m < Nat.find h` with `P m`, then `¬ Q m`.
This decomposes `Nat.find_min` for conjunction predicates: when `P m` is known to hold
but `m` is below the minimum satisfying both `P` and `Q`, it must be that `Q m` fails.
Useful for using `Nat.find` to find the minimum satisfying a conjunction. -/
lemma find_min_conj {P Q : Nat → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∃ n, P n ∧ Q n) {m : Nat} (hPm : P m) (hm : m < Nat.find h) : ¬ Q m := by
  have hmin := Nat.find_min h hm
  intro hQm
  exact hmin ⟨hPm, hQm⟩

end Nat

namespace Nat

/-! ### Bounded collection by predicate -/

/-- Collect the first `n` naturals at or above `start` satisfying `P`, examining at most `fuel` values. -/
def collectFirstN (P : Nat → Prop) [DecidablePred P] (n : Nat) (fuel : Nat)
    (start : Nat := 0) (acc : List Nat := []) : List Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    if hlen : acc.length < n then
      if hP : P start then
        collectFirstN P n fuel' (start + 1) (acc ++ [start])
      else
        collectFirstN P n fuel' (start + 1) acc
    else
      acc

/-- Elements produced by `collectFirstN` are below the end of its search interval. -/
lemma collectFirstN_elements_bound (P : Nat → Prop) [DecidablePred P]
    (n start fuel : Nat) (acc : List Nat)
    (h_acc_lt : ∀ x ∈ acc, x < start) :
    ∀ x ∈ collectFirstN P n fuel start acc, x < start + fuel := by
  induction fuel generalizing start acc with
  | zero => simpa [collectFirstN] using h_acc_lt
  | succ fuel ih =>
    intro x hx
    simp only [collectFirstN] at hx
    split at hx
    · split at hx
      · have hnew : ∀ y ∈ acc ++ [start], y < start + 1 := by
          intro y hy
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · have := h_acc_lt y hy; omega
          · omega
        have := ih (start + 1) (acc ++ [start]) hnew x hx
        omega
      · have := ih (start + 1) acc (fun y hy => by have := h_acc_lt y hy; omega) x hx
        omega
    · have := h_acc_lt x hx; omega

end Nat

namespace Nat

/-! ### Predicate search: find the maximum index satisfying a predicate -/

/-- `findMax P n` returns the largest `k ≤ n` such that `P k = true`, or `0` if no such `k` exists. -/
def findMax (P : Nat → Bool) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 =>
    if P (m + 1) then m + 1
    else findMax P m
termination_by n

/-- `findMax_spec`: either `P` holds at the result, or the result is `0` (no element found). -/
lemma findMax_spec (P : Nat → Bool) (n : Nat) :
    P (findMax P n) = true ∨ findMax P n = 0 := by
  induction' n with m ih
  · right; simp [findMax]
  · simp [findMax]
    split
    · left; assumption
    · exact ih

/-- If `P 0 = true`, then `P (findMax P n) = true` for all `n`.
This is a strengthening of `findMax_spec` under the base-case assumption. -/
lemma findMax_spec_of_base (P : Nat → Bool) (n : Nat) (h0 : P 0 = true) :
    P (findMax P n) = true := by
  induction' n with m ih
  · simp [findMax, h0]
  · rw [findMax]
    by_cases h : P (m+1) = true
    · simp [h]
    · simp [h]; exact ih

/-- If `findMax P n < len ≤ n`, then `P len` is false — i.e., `findMax` is truly maximal. -/
lemma findMax_is_max (P : Nat → Bool) (n len : Nat)
    (h_lt : findMax P n < len) (h_le : len ≤ n) :
    P len = false := by
  revert len
  induction' n with m ih
  · intro len h_lt h_le
    simp [findMax] at h_lt
    omega
  · intro len h_lt h_le
    by_cases h_possible : P (m + 1)
    · have h_true : P (m + 1) = true := by simp [h_possible]
      simp [findMax, h_true] at h_lt
      omega
    · have h_false : P (m + 1) = false := by simp [h_possible]
      simp [findMax, h_false] at h_lt
      by_cases h_eq : len = m + 1
      · subst h_eq; exact h_false
      · have h_len_le_m : len ≤ m := by omega
        exact ih len h_lt h_len_le_m

/-- If `m ≤ n` and `P m = true`, then `m ≤ findMax P n`.
That is, `findMax` returns a value at least as large as any `m` satisfying `P` within the bound.
This is the "lower bound" companion to `findMax_is_max`. -/
lemma findMax_ge (P : Nat → Bool) (n m : Nat) (hmle : m ≤ n) (hP : P m = true) : m ≤ findMax P n := by
  induction' n with k ih generalizing m
  · have hm0 : m = 0 := by omega
    subst hm0; exact Nat.zero_le _
  · unfold findMax
    by_cases h : P (k + 1)
    · simp [h]; omega
    · simp [h]
      by_cases hm_kplus1 : m = k + 1
      · subst hm_kplus1; exfalso; exact h hP
      · have hmle_k : m ≤ k := by omega
        exact ih m hmle_k hP

/-- The result of `findMax P n` never exceeds the bound `n`. -/
lemma findMax_le (P : Nat → Bool) (n : Nat) : findMax P n ≤ n := by
  induction' n with m ih
  · simp [findMax]
  · simp [findMax]
    split <;> omega

/-! ### Predicate search with a custom default -/

/-- `findMaxWithDefault P default k` returns the largest `i` such that `P i` is true and `i ≤ k`,
    returning `default` if no such `i` exists. This generalizes `findMax` (which uses `0` as default). -/
def findMaxWithDefault (P : Nat → Bool) (default : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => default
  | n+1 =>
    if P (n + 1) then
      n + 1
    else
      findMaxWithDefault P default n
termination_by k

/-- If `findMaxWithDefault P default k` exceeds `default`, then `P` holds at that index. -/
lemma findMaxWithDefault_gt_default (P : Nat → Bool) (default : Nat) (k : Nat)
    (hpos : default < findMaxWithDefault P default k) : P (findMaxWithDefault P default k) = true := by
  induction' k with m ih
  · simp [findMaxWithDefault] at hpos
  · by_cases hP : P (m + 1) = true
    · have h_val : findMaxWithDefault P default (m + 1) = m + 1 := by
        simp [findMaxWithDefault, hP]
      rw [h_val]
      exact hP
    · have h_val : findMaxWithDefault P default (m + 1) = findMaxWithDefault P default m := by
        simp [findMaxWithDefault, hP]
      rw [h_val] at hpos ⊢
      exact ih hpos

/-- For every `j` strictly between `findMaxWithDefault P default k` and `k` (inclusive), `P j` is false. -/
lemma findMaxWithDefault_false_above (P : Nat → Bool) (default : Nat) (k : Nat) :
    ∀ j, findMaxWithDefault P default k < j → j ≤ k → P j = false := by
  induction' k with m ih
  · intro j hj hk; omega
  · simp [findMaxWithDefault]
    split_ifs with hP
    · intro j hj hk; omega
    · intro j hj hk
      by_cases hjm : j ≤ m
      · exact ih j hj hjm
      · have heq : j = m + 1 := by omega
        rw [heq]
        simpa [Bool.not_eq_true] using hP

/-! ### Predicate search: find the first index in range satisfying a predicate -/

/-- `findFirstInRange P n` returns the smallest `i ≤ n` such that `P i = true`, or `n` if no such `i` exists. -/
def findFirstInRange (P : Nat → Bool) (n : Nat) : Nat :=
  match (List.range (n + 1)).find? P with
  | some i => i
  | none => n

lemma findFirstInRange_le_bound (P : Nat → Bool) (n : Nat) : findFirstInRange P n ≤ n := by
  unfold findFirstInRange
  split
  · rename_i i hi
    have hi_mem := List.mem_of_find?_eq_some hi
    have hi_lt : i < n + 1 := List.mem_range.mp hi_mem
    omega
  · omega

lemma findFirstInRange_spec (P : Nat → Bool) (n : Nat) (h : ∃ i, i < n + 1 ∧ P i = true) :
    P (findFirstInRange P n) = true := by
  rcases h with ⟨x, hx_range, hx⟩
  unfold findFirstInRange
  by_cases h_none : (List.range (n + 1)).find? P = none
  · exfalso
    have h_all := ((List.find?_eq_none (p := P) (l := List.range (n + 1))).mp h_none)
    exact h_all x (List.mem_range.mpr hx_range) hx
  · have h_some : ∃ i, (List.range (n + 1)).find? P = some i := by
      exact Option.isSome_iff_exists.mp (Option.ne_none_iff_isSome.mp h_none)
    rcases h_some with ⟨i, hi⟩
    rw [hi]
    rw [List.find?_eq_some_iff_append] at hi
    rcases hi with ⟨hP, _⟩
    exact hP

end Nat


namespace Nat


/-! ### Option-returning predicate search over bounded ranges -/

/-- Find the minimal `i ∈ [start, bound]` such that predicate `p` holds.
    Returns `none` if no such `i` exists. Uses `Finset` to search the bounded range. -/
def findFirstInRange? (p : Nat → Prop) [DecidablePred p] (start bound : Nat) : Option Nat :=
  let valid := Finset.filter (fun i => start ≤ i ∧ p i) (Finset.range (bound + 1))
  if h : valid.Nonempty then
    some (valid.min' h)
  else
    none

/-! ### Binary search for the first index satisfying a Boolean predicate -/

/-- Binary search for the smallest `i ∈ [lo, hi)` such that `f i` holds.
    Assumes `f` is monotone: once `f i` holds, `f j` holds for all `j ≥ i` in the range.
    If `f i` never holds in the range, returns `lo`. -/
def binarySearch (f : Nat → Bool) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if f mid then
      binarySearch f lo mid
    else
      binarySearch f (mid.succ) hi
  else
    lo
termination_by hi - lo

/-- Binary search for the smallest `i ∈ [lo, hi]` such that `P i` holds, using a `DecidablePred`.
This is the `Prop`-based counterpart to `binarySearch` (which uses `Bool`).
Returns `lo` if no `i` in the range satisfies `P`. -/
def binarySearchMin (lo hi : Nat) (P : Nat → Prop) [DecidablePred P] : Nat :=
  if h : lo < hi then
    let mid : Nat := (lo + hi) / 2
    if hP : P mid then
      binarySearchMin lo mid P
    else
      binarySearchMin (mid + 1) hi P
  else
    lo
termination_by hi - lo

/-- Binary search: find the first `k` in `[lo, hi)` such that `p k` holds.
Precondition: `¬ p lo` and `p hi` (so the answer is guaranteed to exist in `[lo, hi]`).
Returns the minimal index where `p` becomes true.

Contrast with `binarySearchMin` which returns `lo` on empty range without a precondition.
`firstTrue` requires the stronger precondition but provides the stronger lemma
`firstTrue_invariant`. -/
def firstTrue (p : Nat → Prop) [DecidablePred p] (lo hi : Nat) : Nat :=
  if h : lo + 1 < hi then
    if h_mid : p ((lo + hi) / 2) then
      firstTrue p lo ((lo + hi) / 2)
    else
      firstTrue p ((lo + hi) / 2) hi
  else
    hi
termination_by hi - lo
decreasing_by
  · -- first branch: firstTrue p lo ((lo+hi)/2), need (lo+hi)/2 - lo < hi - lo
    have hlo_le_mid : lo ≤ (lo + hi) / 2 := by
      omega
    have hmid_lt_hi : (lo + hi) / 2 < hi := by
      have hpos : 0 < 2 := by decide
      apply (Nat.div_lt_iff_lt_mul hpos).mpr
      omega
    apply Nat.sub_lt_sub_right hlo_le_mid hmid_lt_hi
  · -- second branch: firstTrue p ((lo+hi)/2) hi, need hi - (lo+hi)/2 < hi - lo
    have hlo_lt_mid : lo < (lo + hi) / 2 := by
      have h_ineq : 2 * lo + 2 ≤ lo + hi := by omega
      have h_div : (2 * lo + 2) / 2 ≤ (lo + hi) / 2 := Nat.div_le_div_right h_ineq
      have h_simp : (2 * lo + 2) / 2 = lo + 1 := by
        have : 2 * lo + 2 = (lo + 1) * 2 := by omega
        rw [this, Nat.mul_div_cancel _ (by decide : 0 < 2)]
      have : lo + 1 ≤ (lo + hi) / 2 := by
        rw [← h_simp]
        exact h_div
      omega
    have hlo_lt_hi : lo < hi := by omega
    exact Nat.sub_lt_sub_left hlo_lt_hi hlo_lt_mid

/-- Main invariant lemma for `firstTrue`: given a monotone predicate `p` and valid preconditions,
the result satisfies `p` and is minimal among candidates ≥ lo. -/
lemma firstTrue_invariant (p : Nat → Prop) [DecidablePred p] (h_mono : ∀ a b, a ≤ b → p a → p b)
    (lo hi : Nat) (hlo_false : ¬ p lo) (hhi_true : p hi) (hle : lo ≤ hi) :
    p (firstTrue p lo hi) ∧
    (∀ k', lo ≤ k' → k' < firstTrue p lo hi → ¬ p k') := by
  refine firstTrue.induct p
    (motive := λ lo hi =>
      (¬ p lo) →
      (p hi) →
      (lo ≤ hi) →
      p (firstTrue p lo hi) ∧
      (∀ k', lo ≤ k' → k' < firstTrue p lo hi → ¬ p k'))
    ?case1 ?case2 ?case3 lo hi hlo_false hhi_true hle
  · -- case1: lo + 1 < hi, p ((lo+hi)/2) holds, recursive call lo ((lo+hi)/2)
    intro lo hi h_lt h_mid_true ih hlo_false' hhi_true' hle'
    have hlo_le_mid : lo ≤ (lo + hi) / 2 := by
      omega
    rcases ih hlo_false' h_mid_true hlo_le_mid with ⟨h_ge, h_min⟩
    have h_ft_eq : firstTrue p lo hi = firstTrue p lo ((lo + hi) / 2) := by
      conv =>
        lhs
        unfold firstTrue
      simp [h_lt, h_mid_true]
    constructor
    · simpa [h_ft_eq] using h_ge
    · intro k' hk'_ge_lo hk'_lt_ft
      rw [h_ft_eq] at hk'_lt_ft
      exact h_min k' hk'_ge_lo hk'_lt_ft
  · -- case2: lo + 1 < hi, ¬ p ((lo+hi)/2), recursive call ((lo+hi)/2) hi
    intro lo hi h_lt h_mid_false ih hlo_false' hhi_true' hle'
    set mid := (lo + hi) / 2 with hmid_def
    have h_mid_false' : ¬ p mid := by
      rw [hmid_def]
      exact h_mid_false
    have hmid_le_hi : mid ≤ hi := by
      rw [hmid_def]
      omega
    rcases ih h_mid_false' hhi_true' hmid_le_hi with ⟨h_ge, h_min⟩
    have h_ft_eq : firstTrue p lo hi = firstTrue p mid hi := by
      rw [hmid_def]
      have h_mid_false_at_pos : ¬ p ((lo + hi) / 2) := by rwa [← hmid_def]
      conv =>
        lhs
        unfold firstTrue
      simp [h_lt, h_mid_false_at_pos]
    constructor
    · simpa [h_ft_eq] using h_ge
    · intro k' hk'_ge_lo hk'_lt_ft
      rw [h_ft_eq] at hk'_lt_ft
      by_cases hk'_lt_mid : k' < mid
      · -- k' < mid: use monotonicity contrapositive
        have hk'_le_mid : k' ≤ mid := Nat.le_of_lt hk'_lt_mid
        exact mt (h_mono k' mid hk'_le_mid) h_mid_false'
      · -- mid ≤ k' < firstTrue mid hi: use IH
        have hk'_ge_mid : mid ≤ k' := Nat.le_of_not_lt hk'_lt_mid
        exact h_min k' hk'_ge_mid hk'_lt_ft
  · -- case3: ¬ lo + 1 < hi, i.e., hi ≤ lo+1
    intro lo hi h_nlt hlo_false' hhi_true' hle'
    have h_hi_cases : hi = lo ∨ hi = lo + 1 := by omega
    rcases h_hi_cases with (h_hi_eq_lo | h_hi_eq_succ)
    · -- hi = lo: contradiction with hlo_false' and hhi_true'
      rw [h_hi_eq_lo] at hhi_true'
      exact absurd hhi_true' hlo_false'
    · -- hi = lo+1
      subst h_hi_eq_succ
      have h_ft_eq : firstTrue p lo (lo + 1) = lo + 1 := by
        unfold firstTrue
        simp [show ¬ (lo + 1 < lo + 1) by omega]
      rw [h_ft_eq]
      constructor
      · exact hhi_true'
      · intro k' hk'_ge_lo hk'_lt_succ
        have : k' = lo := by omega
        subst this
        exact hlo_false'

/-! ### Binary search for the largest index satisfying a Boolean predicate -/

/-- Binary search for the largest `i ∈ [lo, hi]` such that `f i` holds.
    Assumes `f` is monotone decreasing: if `f (i+1)` holds then `f i` holds,
    i.e., `f` is downward-closed. Preconditions: `f lo = true` and `hi` is an
    upper bound beyond which `f` fails.

    Contrast with `binarySearch` which finds the **smallest** satisfying index
    using floor division `(lo + hi) / 2`; `binarySearchMax` uses ceiling division
    `(lo + hi + 1) / 2` to bias toward the right half. -/
def binarySearchMax (f : Nat → Bool) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi + 1) / 2
    if f mid then
      binarySearchMax f mid hi
    else
      binarySearchMax f lo (mid - 1)
  else
    lo
termination_by hi - lo
decreasing_by
  · -- hi - mid < hi - lo (since lo < mid when lo < hi)
    omega
  · -- (mid - 1) - lo < hi - lo (since mid ≤ hi, so mid - 1 < hi)
    omega

/-- `findFirstInRange? p start bound` returns the minimal `i ∈ [start, bound]` satisfying `p`,
    or `none` if no such `i` exists. -/
lemma findFirstInRange?_spec (p : Nat → Prop) [DecidablePred p] (start bound : Nat) :
    (∃ M, findFirstInRange? p start bound = some M ∧ p M ∧
      start ≤ M ∧ M ≤ bound ∧ (∀ m, start ≤ m → m < M → ¬ p m)) ∨
    (findFirstInRange? p start bound = none ∧ ∀ m, start ≤ m → m ≤ bound → ¬ p m) := by
  let s := Finset.filter (fun i => start ≤ i ∧ p i) (Finset.range (bound + 1))
  have h_def : findFirstInRange? p start bound = (if h : s.Nonempty then some (s.min' h) else none) := rfl
  rw [h_def]
  by_cases hne : s.Nonempty
  · have h_if_eq : (if h : s.Nonempty then some (s.min' h) else none) = some (s.min' hne) := by
      simp [hne]
    rw [h_if_eq]
    set M := s.min' hne with hM
    have hM_mem : M ∈ s := s.min'_mem hne
    rcases Finset.mem_filter.mp hM_mem with ⟨hM_range, ⟨hM_ge, hM_p⟩⟩
    have hM_le_bound : M ≤ bound := by
      have hM_lt : M < bound + 1 := Finset.mem_range.mp hM_range
      omega
    left
    refine ⟨M, rfl, hM_p, hM_ge, hM_le_bound, ?_⟩
    intro m hm_start hm_lt hm_p
    have hm_mem : m ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm_start, hm_p⟩
    have hM_le_m : M ≤ m := Finset.min'_le s m hm_mem
    omega
  · have h_if_eq : (if h : s.Nonempty then some (s.min' h) else none) = none := by
      simp [hne]
    rw [h_if_eq]
    right
    refine ⟨rfl, ?_⟩
    intro m hm_start hm_le hm_p
    have hm_mem : m ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm_start, hm_p⟩
    exact hne ⟨m, hm_mem⟩

/-! ### Recursive first-satisfying search over a bounded range -/

/-- Find the first natural `y` in `[lo, hi]` such that `p y` holds, returning `some y`,
or `none` if no such `y` exists. This is a recursive implementation that works with
`DecidablePred p` and provides a termination proof. -/
def findFirstSatisfying (hi : Nat) (p : Nat → Prop) [DecidablePred p] (lo : Nat) : Option Nat :=
  if h : lo ≤ hi then
    if p lo then
      some lo
    else
      findFirstSatisfying hi p (lo + 1)
  else
    none
termination_by hi + 1 - lo
decreasing_by
  simp_wf
  omega

/-- Specification for `findFirstSatisfying`: scanning upward through `[lo, hi]` for a property `p`,
either we find some `y` with `p y` (and return `some y`), or we find none in the
range (and return `none`). The found `y` is the *first* such element. -/
lemma findFirstSatisfying_spec (hi : Nat) (p : Nat → Prop) [DecidablePred p] (lo : Nat) :
    (∃ (y : Nat), lo ≤ y ∧ y ≤ hi ∧ p y ∧
      findFirstSatisfying hi p lo = some y ∧
      (∀ (z : Nat), lo ≤ z → z < y → ¬ p z))
    ∨ (findFirstSatisfying hi p lo = none ∧
      (∀ (y : Nat), lo ≤ y → y ≤ hi → ¬ p y)) := by
  let P (k : Nat) : Prop :=
    ∀ (hi' lo' : Nat), hi' + 1 - lo' = k →
      (∃ (y : Nat), lo' ≤ y ∧ y ≤ hi' ∧ p y ∧
        findFirstSatisfying hi' p lo' = some y ∧
        (∀ (z : Nat), lo' ≤ z → z < y → ¬ p z))
      ∨ (findFirstSatisfying hi' p lo' = none ∧
        (∀ (y : Nat), lo' ≤ y → y ≤ hi' → ¬ p y))
  have h_all : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k' IH hi' lo' hk
    unfold findFirstSatisfying
    split
    · rename_i hle
      split
      · rename_i hp_true
        left
        refine ⟨lo', ?_, hle, hp_true, rfl, ?_⟩
        · rfl
        · intro z hz1 hz2; omega
      · rename_i hp_false
        have h_lt : hi' + 1 - (lo' + 1) < k' := by
          rw [← hk]
          omega
        have hk_next : hi' + 1 - (lo' + 1) = hi' + 1 - (lo' + 1) := rfl
        rcases IH (hi' + 1 - (lo' + 1)) h_lt hi' (lo' + 1) hk_next with
          (⟨y, hlo'y, hyn, hpy, hret, hfirst⟩ | ⟨hret, hall⟩)
        · left
          refine ⟨y, by omega, hyn, hpy, ?_, ?_⟩
          · simpa [hle, hp_false] using hret
          · intro z hz1 hz2
            by_cases hz_eq_lo' : z = lo'
            · subst hz_eq_lo'; exact hp_false
            · have hz_ge_lo'1 : lo' + 1 ≤ z := by omega
              exact hfirst z hz_ge_lo'1 hz2
        · right
          constructor
          · simpa [hle, hp_false] using hret
          · intro y hlo'y hyn
            by_cases hy_lo' : y = lo'
            · subst hy_lo'; exact hp_false
            · have hlo'1y : lo' + 1 ≤ y := by omega
              exact hall y (by omega) hyn
    · rename_i hgt
      right
      constructor
      · rfl
      · intro y hlo'y hyn
        omega
  exact h_all (hi + 1 - lo) hi lo rfl

/-! ### Find minimal element in [0, maxVal] satisfying a `Prop` predicate, returning `-1` on failure -/

/-- Find the smallest `n` in `[0, maxVal]` satisfying `p n`, or `-1` if none exists.
Returns `Int` with `-1` as the "not found" sentinel, per competitive programming convention.
Contrast with `findFirstInRange?` which returns `Option Nat` and allows a custom start bound. -/
def findMinWhere (maxVal : Nat) (p : Nat → Prop) [DecidablePred p] : Int :=
  let candidates := ((Finset.range (maxVal + 1)).filter p)
  if h : candidates.Nonempty then
    Int.ofNat (candidates.min' h)
  else
    (-1 : Int)

/-- Specification of `findMinWhere`:
either it returns `-1` and no `d ≤ maxVal` satisfies `p`,
or it returns `Int.ofNat d` where `d` is the minimal element ≤ maxVal satisfying `p`. -/
lemma findMinWhere_spec (maxVal : Nat) (p : Nat → Prop) [DecidablePred p] :
    (findMinWhere maxVal p = (-1 : Int) ∧ ∀ d, d ≤ maxVal → ¬ p d) ∨
    (∃ d, findMinWhere maxVal p = Int.ofNat d ∧ d ≤ maxVal ∧
      p d ∧ ∀ d', d' < d → ¬ p d') := by
  unfold findMinWhere
  let candidates := ((Finset.range (maxVal + 1)).filter p)
  by_cases h : candidates.Nonempty
  · right
    rw [dif_pos h]
    let d := candidates.min' h
    have hmem : d ∈ candidates := Finset.min'_mem _ h
    rcases Finset.mem_filter.mp hmem with ⟨hrange, hp⟩
    have hrange_d : d ≤ maxVal := by
      rw [Finset.mem_range] at hrange
      omega
    refine ⟨d, rfl, hrange_d, hp, ?_⟩
    intro d' hd'_lt_d
    have hd'_lt_maxp1 : d' < maxVal + 1 := by omega
    have hd'_mem_range : d' ∈ Finset.range (maxVal + 1) := by
      rw [Finset.mem_range]; exact hd'_lt_maxp1
    by_cases hp' : p d'
    · have hd'_mem_cand : d' ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨hd'_mem_range, hp'⟩
      have hle := Finset.min'_le _ _ hd'_mem_cand
      omega
    · exact hp'
  · left
    rw [dif_neg h]
    refine ⟨rfl, ?_⟩
    intro d hd_le_max
    by_cases hp' : p d
    · have hd_mem_range : d ∈ Finset.range (maxVal + 1) := by
        rw [Finset.mem_range]; omega
      have hd_mem_cand : d ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨hd_mem_range, hp'⟩
      have h_empty : candidates = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [h_empty] at hd_mem_cand
      exfalso; exact Finset.not_mem_empty _ hd_mem_cand
    · exact hp'

end Nat
