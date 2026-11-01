import Mathlib

namespace Search

/-- Bounded search over a state space. Starting from `current`, repeatedly applies `next`
until `ready current` returns true or `fuel` steps are exhausted (returning the last state).

`firstHitFrom` is the most general form of linear search combinators: it walks through
an arbitrary state space defined by a transition function `next : α → α`, stopping when
a terminal predicate `ready : α → Bool` is satisfied. Specializing `next` to `(· + 1)`
and `α` to `Nat` or `Int` yields numeric bounded-search functions like `findFrom` or
`searchFrom`.

Example: `firstHitFrom (· + 1) (· ≥ 5) 10 0 = 5` (find first number ≥ 5 within 10 steps). -/
def firstHitFrom {α : Type u} (next : α → α) (ready : α → Bool) : Nat → α → α
  | 0, current => current
  | fuel + 1, current =>
    if ready current then current else firstHitFrom next ready fuel (next current)

/-! ### `firstHitFrom` on `ℤ` with `next = (· + 1)`

This specializes `firstHitFrom` to the common integer case where the next state
is obtained by adding 1. The key theorem `firstHitFrom_int_spec` states that if
`ok j` is equivalent to `measure j ≤ bound` and the right endpoint `k + n` satisfies
the bound, then the search result also satisfies the bound and is the *first* such
position (all earlier positions exceed the bound).

This pattern is used in binary-search or bounded-linear-search problems where you
scan upward from `k` looking for the first position satisfying a monotone predicate
(e.g., finding minimum eating speed in LeetCode 875). -/

/-- Specification for `firstHitFrom` on `ℤ` with successor step function.
Given `ok : ℤ → Bool` equivalent to `measure ≤ bound`, if `measure (k + n) ≤ bound`,
then the result `r = firstHitFrom (· + 1) ok n k` satisfies:
1. `measure r ≤ bound`
2. For every `j` with `k ≤ j < r`, `measure j > bound`
(i.e., `r` is the first position from `k` upward where the measure is ≤ bound). -/
lemma firstHitFrom_int_spec (ok : Int → Bool) (measure : Int → Int) (bound : Int) :
    ∀ (n : Nat) (k : Int),
      (∀ j : Int, ok j = true ↔ measure j ≤ bound) →
      measure (k + n) ≤ bound →
      measure (firstHitFrom (fun x => x + 1) ok n k) ≤ bound ∧
      (∀ j : Int, k ≤ j → j < firstHitFrom (fun x => x + 1) ok n k →
        measure j > bound)
  | 0, k, hok, hk => by
      simp only [firstHitFrom]
      constructor
      · simpa using hk
      · intro j hkj hj
        omega
  | n + 1, k, hok, hk => by
      by_cases hc : ok k = true
      · have hcs := (hok k).mp hc
        simp only [firstHitFrom, hc, ↓reduceIte]
        constructor
        · exact hcs
        · intro j hkj hj
          omega
      · have hcs : measure k > bound := by
          by_contra hn
          exact hc ((hok k).mpr (le_of_not_gt hn))
        simp only [firstHitFrom, hc, ↓reduceIte]
        have hk' : measure (k + 1 + n) ≤ bound := by
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hk
        obtain ⟨hs, hmin⟩ := firstHitFrom_int_spec ok measure bound n (k + 1) hok hk'
        constructor
        · exact hs
        · intro j hkj hj
          by_cases hje : j = k
          · subst j
            exact hcs
          · apply hmin j
            · omega
            · exact hj

/-! ## Binary search on `Int`

`binarySearch p lo hi` finds the largest integer `x` in `[lo, hi]` such that `p x = true`,
assuming `p` is antitone on the interval (if `p b = true` and `a ≤ b` are both in `[lo, hi]`,
then `p a = true`) and `p lo = true`.

This is the "upper bound" / "last true" variant. For the dual "lower bound" / "first true"
search (with a monotone predicate), compose with `¬ p`. -/

/-- Binary search on `Int` for the largest `x ∈ [lo, hi]` such that `p x = true`.
Assumes `p` is antitone on `[lo, hi]` and `p lo = true`.

Example: `binarySearch (λ x => x ≤ 5) 0 10 = 5` finds the largest `x ≤ 10` such that `x ≤ 5`. -/
def binarySearch (p : Int → Bool) (lo hi : Int) : Int :=
  if lo ≥ hi then
    lo
  else
    let mid := (lo + hi + 1) / 2
    if p mid then
      binarySearch p mid hi
    else
      binarySearch p lo (mid - 1)
termination_by Int.toNat (hi - lo)
decreasing_by
  · -- recursive call `binarySearch p mid hi`
    have hdelta_pos : 0 < hi - lo := by omega
    have hdiff_lt : hi - mid < hi - lo := by omega
    refine (Int.toNat_lt_toNat hdelta_pos).mpr hdiff_lt
  · -- recursive call `binarySearch p lo (mid - 1)`
    have hdelta_pos : 0 < hi - lo := by omega
    have hdiff_lt : (mid - 1) - lo < hi - lo := by omega
    refine (Int.toNat_lt_toNat hdelta_pos).mpr hdiff_lt

/-- Correctness specification for `binarySearch`.
Given `p : Int → Bool`, bounds `lo ≤ hi`, `p lo = true`, and `p` antitone on `[lo, hi]`
(i.e., if `p b = true` and `lo ≤ a ≤ b ≤ hi`, then `p a = true`),
`binarySearch p lo hi` returns `x` such that:
1. `p x = true`
2. `lo ≤ x ≤ hi`
3. For any `y` with `x < y ≤ hi`, `p y = false` (i.e., `x` is the largest true). -/
theorem binarySearch_spec (p : Int → Bool) (lo hi : Int) (hle : lo ≤ hi) (hlo : p lo = true)
    (h_antitone : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → p b = true → p a = true) :
    p (binarySearch p lo hi) = true ∧
    lo ≤ binarySearch p lo hi ∧ binarySearch p lo hi ≤ hi ∧
    (∀ x, binarySearch p lo hi < x → x ≤ hi → p x = false) := by
  by_cases hge : lo ≥ hi
  · have heq : lo = hi := by omega
    subst heq
    rw [binarySearch]
    simp [hlo]
    exact λ x hx_lt hx_le => by omega
  · have h_lt : lo < hi := by omega
    rw [binarySearch]
    simp [hge]
    set mid := (lo + hi + 1) / 2 with hmid_def
    have hmid_le_hi : mid ≤ hi := by
      have : lo + hi + 1 ≤ 2 * hi := by nlinarith
      omega
    have hlo_le_mid_sub_one : lo ≤ mid - 1 := by
      have : lo + hi + 1 ≥ 2 * lo + 2 := by nlinarith
      omega
    by_cases hmid : p mid = true
    · simp [hmid]
      have h_anti_mid : ∀ a b, mid ≤ a → a ≤ b → b ≤ hi → p b = true → p a = true := by
        intro a b ha_mid ha_b hb_hi hpb
        apply h_antitone a b
        · omega
        · exact ha_b
        · exact hb_hi
        · exact hpb
      have ih := binarySearch_spec p mid hi hmid_le_hi hmid h_anti_mid
      rcases ih with ⟨hp, hle_lo, hle_hi, hforall⟩
      refine ⟨hp, ?_, hle_hi, hforall⟩
      omega
    · simp [hmid]
      have h_anti_lo : ∀ a b, lo ≤ a → a ≤ b → b ≤ mid - 1 → p b = true → p a = true := by
        intro a b ha_lo ha_b hb_mid hpb
        apply h_antitone a b
        · exact ha_lo
        · exact ha_b
        · omega
        · exact hpb
      have ih := binarySearch_spec p lo (mid - 1) hlo_le_mid_sub_one hlo h_anti_lo
      rcases ih with ⟨hp, hle_lo, hle_hi, hforall⟩
      refine ⟨hp, hle_lo, ?_, ?_⟩
      · omega
      · intro x hx_gt hx_le
        by_cases hx_mid : x ≤ mid - 1
        · exact hforall x hx_gt hx_mid
        · have hx_ge_mid : mid ≤ x := by omega
          by_contra! hx_false
          have hx_true_val : p x = true := Bool.eq_true_of_not_eq_false hx_false
          have hmid_true : p mid = true := h_antitone mid x (by omega) hx_ge_mid hx_le hx_true_val
          exact hmid hmid_true
termination_by Int.toNat (hi - lo)
decreasing_by
  · -- recursive call `binarySearch_spec p mid hi`
    have hdelta_pos : 0 < hi - lo := by omega
    have hdiff_lt : hi - mid < hi - lo := by omega
    refine (Int.toNat_lt_toNat hdelta_pos).mpr hdiff_lt
  · -- recursive call `binarySearch_spec p lo (mid - 1)`
    have hdelta_pos : 0 < hi - lo := by omega
    have hdiff_lt : (mid - 1) - lo < hi - lo := by omega
    refine (Int.toNat_lt_toNat hdelta_pos).mpr hdiff_lt

/-! ### Downward linear search on `ℤ`

`findLastTrue p k` scans downward from `k` to `0` and returns the largest integer `h`
(0 ≤ h ≤ k) such that `p h = true`. Returns `0` if no positive `h` satisfies `p`,
assuming `p 0 = true` (the base case). This is the "last-true" counterpart of a forward
linear search — useful for problems like h-index where you need the largest index
satisfying a self-referential property. -/

/-- Scan downward from `k` to `0`, returning the largest `h` (0 ≤ h ≤ k)
such that `p h = true`. Assumes `p 0 = true` to guarantee a result.
Example: `findLastTrue (λ h => h ≤ 5) 10 = 5`. -/
def findLastTrue (p : ℤ → Bool) (k : ℕ) : ℤ :=
  match k with
  | 0 => 0
  | k'+1 =>
    let cur := (k'+1 : ℤ)
    if p cur then cur else findLastTrue p k'

/-- Correctness specification for `findLastTrue`:
1. The result is between `0` and `k` (inclusive).
2. The predicate holds at the result.
3. For any larger value within bounds, the predicate fails.
Requires `p 0 = true` for the base case. -/
theorem findLastTrue_spec (p : ℤ → Bool) (k : ℕ) (h_p0 : p 0 = true) :
    0 ≤ findLastTrue p k ∧ findLastTrue p k ≤ (k : ℤ) ∧
    p (findLastTrue p k) = true ∧
    (∀ h : ℤ, findLastTrue p k < h → h ≤ (k : ℤ) → p h = false) := by
  induction k with
  | zero =>
    have h0 : findLastTrue p 0 = (0 : ℤ) := rfl
    rw [h0]
    have h_zero_le : (0 : ℤ) ≤ 0 := by omega
    refine ⟨h_zero_le, h_zero_le, h_p0, ?_⟩
    intro h hpos hle
    omega
  | succ k' ih =>
    have h_succ : findLastTrue p (Nat.succ k') =
        (if p (k'+1 : ℤ) then (k'+1 : ℤ) else findLastTrue p k') := by
      rfl
    rw [h_succ]
    by_cases hcond : p (k'+1 : ℤ)
    · rw [if_pos hcond]
      have h_nonneg : 0 ≤ (k'+1 : ℤ) := by omega
      refine ⟨h_nonneg, by omega, hcond, ?_⟩
      intro h h_gt h_le
      omega
    · rw [if_neg hcond]
      rcases ih with ⟨h_nonneg, h_le_k, h_p_res, h_max⟩
      have h_le_succ : (findLastTrue p k' : ℤ) ≤ (k'+1 : ℤ) := by omega
      refine ⟨h_nonneg, h_le_succ, h_p_res, ?_⟩
      intro h h_gt h_le
      by_cases h_eq_succ : h = (k'+1 : ℤ)
      · subst h_eq_succ
        simp [hcond]
      · have h_le_k' : (h : ℤ) ≤ (k' : ℤ) := by omega
        exact h_max h h_gt h_le_k'

/-! ### Forward linear search on `ℕ` → `ℤ`

`findFirstSatisfying n p start` scans forward from `start` to `n-1` and returns the first
index (as `ℤ`) where `p` holds. Returns `-1` if no index in range satisfies `p`.

This is the "first-true" variant of forward linear search, complementary to `findLastTrue`
(which scans downward). Together they cover both search directions common in competitive
programming. -/

/-- Scan forward from `start` to `n-1`, returning the first index `i` (as `ℤ`) where
`p i = true`. Returns `-1` if no such index exists.
Example: `findFirstSatisfying 10 (λ i => i ≥ 5) 0 = 5`. -/
def findFirstSatisfying (n : ℕ) (p : ℕ → Bool) (start : ℕ) : ℤ :=
  if h : start < n then
    if p start then (start : ℤ) else findFirstSatisfying n p (start + 1)
  else
    -1
termination_by n - start
decreasing_by
  omega

/-- `findFirstSatisfying` always returns either `-1` or a valid index (as `ℤ`). -/
theorem findFirstSatisfying_bound (n : ℕ) (p : ℕ → Bool) (start : ℕ) :
    findFirstSatisfying n p start = (-1 : ℤ) ∨
    ∃ m, start ≤ m ∧ m < n ∧ findFirstSatisfying n p start = (m : ℤ) := by
  induction start using findFirstSatisfying.induct n p with
  | case1 x h_lt hc =>
    right
    refine ⟨x, by omega, h_lt, ?_⟩
    unfold findFirstSatisfying
    simp [h_lt, hc]
  | case2 x h_lt hc ih =>
    rcases ih with (h_neg | ⟨m, hm_ge, hm_lt, h_eq⟩)
    · left
      unfold findFirstSatisfying
      simp [h_lt, hc, h_neg]
    · right
      refine ⟨m, by omega, hm_lt, ?_⟩
      unfold findFirstSatisfying
      simp [h_lt, hc, h_eq]
  | case3 x h_ge =>
    left
    unfold findFirstSatisfying
    simp [h_ge]

/-- If `findFirstSatisfying` returns `-1`, then `p` is false for all indices from `start`
to `n-1`. -/
theorem findFirstSatisfying_none (n : ℕ) (p : ℕ → Bool) (start : ℕ)
    (h : findFirstSatisfying n p start = (-1 : ℤ)) :
    ∀ i, start ≤ i → i < n → p i = false := by
  induction start using findFirstSatisfying.induct n p with
  | case1 x h_lt hc =>
    unfold findFirstSatisfying at h
    simp [h_lt, hc] at h
  | case2 x h_lt hc ih =>
    unfold findFirstSatisfying at h
    simp [h_lt, hc] at h
    intro i hi_lo hi_hi
    rcases Nat.eq_or_lt_of_le hi_lo with (rfl | h_lt')
    · exact (Bool.not_eq_true (p x)).mp hc
    · exact ih h i (by omega) hi_hi
  | case3 x h_ge =>
    unfold findFirstSatisfying at h
    simp [h_ge] at h
    intro i hi_lo hi_hi
    omega

/-! ### Forward linear search on `ℕ` → `ℕ` with default

`findFirstIdx_specificDuplicate p start len default` scans forward from `start` to `len-1` and returns the
first index `i` where `p i = true`. Returns `default` if no index in `[start, len)` satisfies `p`.

Unlike `findFirstSatisfying` (which returns `ℤ` with `-1` as sentinel), this version stays
in `ℕ` and takes an explicit `default` value, which is useful when the default should be
context-dependent (e.g., the length of a list). -/

/-- Find the first index `i` in `[start, len)` such that `p i` is true.
Returns `default` if no such index exists.
Example: `findFirstIdx_specificDuplicate (λ i => i ≥ 5) 0 10 0 = 5`. -/
def findFirstIdx_specificDuplicate (p : Nat → Bool) (start len : Nat) (default : Nat) : Nat :=
  if h : start < len then
    if p start then start else findFirstIdx_specificDuplicate p (start + 1) len default
  else
    default
termination_by len - start

/-- If `p start` is false, the search advances to `start + 1`. -/
lemma findFirstIdx_step (p : Nat → Bool) (start len default : Nat) (hpos : start < len)
    (hp : p start = false) : findFirstIdx_specificDuplicate p start len default = findFirstIdx_specificDuplicate p (start + 1) len default := by
  rw [findFirstIdx_specificDuplicate]; simp [hpos, hp]

/-! ### Inclusive-range existence check on `ℕ`

`anyInRange start stop p` checks whether any `i` in the inclusive range `[start, stop]`
satisfies `p`. Returns `true` if there exists `i` with `start ≤ i ≤ stop` and `p i = true`,
and `false` otherwise.

Unlike `findFirstSatisfying` or `findFirstIdx_specificDuplicate` (which return the index of the first match),
`anyInRange` only answers the boolean existence question. This is useful when you only need
to know *whether* a property holds somewhere in a range, not *where* it holds. -/

/-- Check whether any `i` in the inclusive range `[start, stop]` satisfies the predicate `p`.
Example: `anyInRange 0 10 (λ i => i ≥ 5) = true` (since `5` is in `[0, 10]`). -/
def anyInRange (start stop : ℕ) (p : ℕ → Bool) : Bool :=
  if h : start ≤ stop then
    if p start then true
    else anyInRange (start + 1) stop p
  else false
termination_by stop + 1 - start
decreasing_by omega

/-! ### Forward linear search on `ℤ` predicate with inclusive bound

`findFirstValid p start m` scans forward from `start` to `m` (inclusive) and returns the first
integer `k` (as `ℤ`) in the range `[start, m]` where `p k = true`. Returns `-1` if no such `k` exists.

This is similar to `findFirstSatisfying` but:
* Works on `ℤ → Bool` predicates (not just `ℕ → Bool`)
* Uses an inclusive upper bound `m` (the range is `[start, m]` rather than `[start, n)`)
-/

/-- Find the first integer `k` in `[start, m]` (inclusive) such that `p k = true`.
Returns `-1` if no such `k` exists.
Example: `findFirstValid (λ i => i ≥ 5) 0 10 = 5`. -/
def findFirstValid (p : ℤ → Bool) (start m : ℕ) : ℤ :=
  if h : start ≤ m then
    if p (start : ℤ) then
      (start : ℤ)
    else
      findFirstValid p (start + 1) m
  else
    -1
termination_by m + 1 - start

/-- Complete specification of `findFirstValid`:
either it returns `-1` and no element in `[start, m]` satisfies `p`,
or it returns a value `r ≠ -1` which is the first element in `[start, m]` satisfying `p`. -/
theorem findFirstValid_spec (p : ℤ → Bool) (start m : ℕ) :
    (findFirstValid p start m = -1 ∧ (∀ (k : ℤ), (start : ℤ) ≤ k → k ≤ (m : ℤ) → p k = false)) ∨
    (∃ (r : ℤ), findFirstValid p start m = r ∧ r ≠ -1 ∧ (start : ℤ) ≤ r ∧ r ≤ (m : ℤ) ∧ p r = true ∧
      (∀ (k : ℤ), (start : ℤ) ≤ k → k < r → p k = false)) := by
  set d0 := m + 1 - start with hd0
  have h_main : ∀ (d : ℕ), d ≤ d0 → (∀ (s : ℕ), m + 1 - s = d →
      (findFirstValid p s m = -1 ∧ (∀ (k : ℤ), (s : ℤ) ≤ k → k ≤ (m : ℤ) → p k = false)) ∨
      (∃ (r : ℤ), findFirstValid p s m = r ∧ r ≠ -1 ∧ (s : ℤ) ≤ r ∧ r ≤ (m : ℤ) ∧ p r = true ∧
        (∀ (k : ℤ), (s : ℤ) ≤ k → k < r → p k = false))) := by
    intro d hle
    induction' d with d IH
    · -- d = 0: s > m, search range is empty
      intro s h_meas
      have hs_gt_m : ¬ (s ≤ m) := by omega
      left
      unfold findFirstValid
      simp [hs_gt_m]
      intro k hsk hkm
      omega
    · -- d = d+1: s ≤ m, check p s
      intro s h_meas
      have hs_le_m : s ≤ m := by omega
      unfold findFirstValid
      rw [dif_pos hs_le_m]
      by_cases hp : p (s : ℤ) = true
      · -- found at s
        refine Or.inr (Exists.intro (s : ℤ) ?_)
        have h_eq : (if p (s : ℤ) then (s : ℤ) else findFirstValid p (s + 1) m) = (s : ℤ) := by simp [hp]
        refine ⟨h_eq, ?_, le_refl _, Nat.cast_le.mpr hs_le_m, hp, λ k hsk hkr => ?_⟩
        · intro h; omega
        · omega
      · -- not found at s, recurse at s+1
        have hp_false : p (s : ℤ) = false := (Bool.not_eq_true _).mp hp
        have h_meas_next : m + 1 - (s + 1) = d := by omega
        rcases IH (by omega) (s+1) h_meas_next with (⟨h_neg, h_all⟩ | ⟨r', h_eq, h_ne, h_low, h_high, h_pr, h_lt⟩)
        · -- recursion returned -1: no element from s+1 onward satisfies p
          refine Or.inl ?_
          have h_ff : (if p (s : ℤ) then (s : ℤ) else findFirstValid p (s + 1) m) = -1 := by
            simp [hp_false, h_neg]
          refine ⟨h_ff, λ k hsk hkm => ?_⟩
          by_cases hk_eq_s : k = (s : ℤ)
          · subst hk_eq_s; exact hp_false
          · have hsk' : (s + 1 : ℤ) ≤ k := by omega
            exact h_all k hsk' hkm
        · -- recursion found at r'
          refine Or.inr (Exists.intro r' ?_)
          have h_ff : (if p (s : ℤ) then (s : ℤ) else findFirstValid p (s + 1) m) = r' := by
            simp [hp_false, h_eq]
          refine ⟨h_ff, h_ne, ?_, h_high, h_pr, λ k hsk hkr => ?_⟩
          · push_cast at h_low; omega
          · by_cases hk_eq_s : k = (s : ℤ)
            · subst hk_eq_s; exact hp_false
            · have hsk' : (s + 1 : ℤ) ≤ k := by omega
              exact h_lt k hsk' hkr
  rcases h_main d0 (le_refl _) start hd0 with (h | h)
  · exact Or.inl h
  · exact Or.inr h

/-- If `findFirstValid` returns `-1`, then `p` is false for all `k` in `[start, m]`. -/
theorem findFirstValid_eq_neg_one (p : ℤ → Bool) (start m : ℕ) (h : findFirstValid p start m = -1) :
    ∀ (k : ℤ), (start : ℤ) ≤ k → k ≤ (m : ℤ) → p k = false := by
  rcases findFirstValid_spec p start m with (⟨h_eq, h_all⟩ | ⟨r, h_eq', h_ne, h_low, h_high, h_pr, h_lt⟩)
  · exact h_all
  · exfalso
    rw [h_eq'] at h
    exact h_ne h

/-- If `findFirstValid` returns a value `r ≠ -1`, then `r` is the first element in `[start, m]`
satisfying `p`. -/
theorem findFirstValid_ne_neg_one (p : ℤ → Bool) (start m : ℕ) (r : ℤ) (h : findFirstValid p start m = r)
    (hne : r ≠ -1) : (start : ℤ) ≤ r ∧ r ≤ (m : ℤ) ∧ p r = true ∧
      (∀ (k : ℤ), (start : ℤ) ≤ k → k < r → p k = false) := by
  rcases findFirstValid_spec p start m with (⟨h_eq, h_all⟩ | ⟨r', h_eq', h_ne', h_low, h_high, h_pr, h_lt⟩)
  · exfalso
    rw [h_eq] at h
    exact hne h.symm
  · rw [h_eq'] at h
    have hr : r = r' := Eq.symm h
    subst hr
    exact ⟨h_low, h_high, h_pr, h_lt⟩

/-! ### Downward search from `k` to `1` on `Nat → Prop`

`search_down_to_one p k` searches from `k` down to `1` for the first `n` where
`p n` holds, returning `1` if none found. This is the "largest true" variant of
downward linear search on `ℕ`, complementary to `findLastTrue` (which scans `ℤ`)
and `findFirstIdx_specificDuplicate` (which scans forward on `ℕ`).

Unlike `findLastTrue` (which takes `p : ℤ → Bool` and returns `0` as default),
`search_down_to_one` uses `Nat → Prop` with `DecidablePred`, returning `1` as
the default (common in 1-indexed problem domains). -/

/-- Search from `k` down to `1` for the first `n` where `p n` holds. Returns `1` if none found. -/
def search_down_to_one (p : Nat → Prop) [DecidablePred p] (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | m+1 => if _ : p (m+1) then m+1 else search_down_to_one p m

/-! ### Forward linear search with score function on `ℤ`

`firstIntAtLeast score threshold start fuel` finds the first integer `y ≥ start`
(within `fuel` steps) such that `score y ≥ threshold`. Steps by `+1` from `start`.
Returns the last position if no such `y` is found within `fuel` steps.

Unlike `searchFrom` (which takes `p : Int → Prop`), `firstIntAtLeast` takes an
`Int → Int` score function and a threshold, which enables stronger theorems about
score comparisons (e.g., `score (firstIntAtLeast ...) ≥ threshold` rather than just
`p (firstIntAtLeast ...)`).

This is useful for problems where you need to find the first argument that makes a
monotone score function cross a threshold, e.g., "Kth Smallest Number in
Multiplication Table" (LeetCode 668). -/

/-- Forward linear search: find the first `y ∈ [start, start + fuel]` with `score y ≥ threshold`.
Steps by `+1` from `start`, checking at most `fuel + 1` positions.
Returns the last position if no such `y` exists within the fuel budget. -/
def firstIntAtLeast (score : Int → Int) (threshold start : Int) : Nat → Int
  | 0 => start
  | fuel + 1 =>
      if score start ≥ threshold then
        start
      else
        firstIntAtLeast score threshold (start + 1) fuel

/-- Main correctness theorem for `firstIntAtLeast`:
if there exists some `j ∈ [0, fuel]` such that `score (start + j) ≥ threshold`,
then:
1. `score (firstIntAtLeast ...) ≥ threshold`
2. For every `y` with `start ≤ y < firstIntAtLeast ...`, `score y < threshold`
   (i.e., the result is the *first* position satisfying the threshold). -/
theorem firstIntAtLeast_spec (score : Int → Int) (threshold : Int) :
    ∀ (fuel : Nat) (start : Int),
      (∃ j : Nat, j ≤ fuel ∧ score (start + (j : Int)) ≥ threshold) →
      score (firstIntAtLeast score threshold start fuel) ≥ threshold ∧
        ∀ y, start ≤ y → y < firstIntAtLeast score threshold start fuel → score y < threshold := by
  intro fuel
  induction fuel with
  | zero =>
      intro start h
      rcases h with ⟨j, hj, hpj⟩
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simp [firstIntAtLeast] at hpj ⊢
      constructor
      · exact hpj
      · intro y hxy hy
        omega
  | succ fuel ih =>
      intro start h
      by_cases hp : score start ≥ threshold
      · simp [firstIntAtLeast, hp]
        intro y hxy hy
        omega
      · have hnext :
            ∃ j : Nat, j ≤ fuel ∧ score (start + 1 + (j : Int)) ≥ threshold := by
          rcases h with ⟨j, hj, hpj⟩
          cases j with
          | zero =>
              simp at hpj
              exact False.elim (hp hpj)
          | succ j =>
              use j
              constructor
              · exact Nat.succ_le_succ_iff.mp hj
              · simpa [Nat.cast_succ, add_assoc, add_comm, add_left_comm] using hpj
        have ih_res := ih (start + 1) hnext
        simp [firstIntAtLeast, hp]
        constructor
        · exact ih_res.1
        · intro y hxy hy
          by_cases hy_eq : y = start
          · subst y
            exact lt_of_not_ge hp
          · have hxy' : start + 1 ≤ y := by omega
            exact ih_res.2 y hxy' hy

/-- The result of `firstIntAtLeast` is always at least `start`. -/
theorem firstIntAtLeast_ge_start (score : Int → Int) (threshold : Int) :
    ∀ (fuel : Nat) (start : Int), start ≤ firstIntAtLeast score threshold start fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      simp [firstIntAtLeast]
  | succ fuel ih =>
      intro start
      by_cases hp : score start ≥ threshold
      · simp [firstIntAtLeast, hp]
      · have h := ih (start + 1)
        simp [firstIntAtLeast, hp]
        omega

/-- If there exists `j ≤ fuel` with `score (start + j) ≥ threshold`, then
`firstIntAtLeast score threshold start fuel ≤ start + fuel`. -/
theorem firstIntAtLeast_le_of_exists (score : Int → Int) (threshold : Int) {fuel : Nat} {start : Int}
    (h : ∃ j : Nat, j ≤ fuel ∧ score (start + (j : Int)) ≥ threshold) :
    firstIntAtLeast score threshold start fuel ≤ start + (fuel : Int) := by
  rcases h with ⟨j, hj, hpj⟩
  have hs := firstIntAtLeast_spec score threshold fuel start ⟨j, hj, hpj⟩
  have hnot : ¬ start + (j : Int) < firstIntAtLeast score threshold start fuel := by
    intro hlt
    have hj_nonneg : (0 : Int) ≤ (j : Int) := by exact_mod_cast Nat.zero_le j
    have hsmall := hs.2 (start + (j : Int)) (by omega) hlt
    omega
  have hle_j : firstIntAtLeast score threshold start fuel ≤ start + (j : Int) := le_of_not_gt hnot
  have hj_int : (j : Int) ≤ (fuel : Int) := by exact_mod_cast hj
  omega

end Search
