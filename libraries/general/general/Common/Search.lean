import Mathlib
import general.Int.Core

namespace Search


/-! ### Ascending range search on `Nat` returning `Option` -/

/-- Find the first index `k` in `[start, len)` such that `p k` is true.
Returns `none` if no such index exists.
This is a simple ascending linear search returning `Option Nat`;
contrast with `linearSearch` which returns `Int` with `-1` as a sentinel. -/
def findIdx (len start : Nat) (p : Nat → Bool) : Option Nat :=
  if h : start < len then
    if p start then some start
    else findIdx len (start + 1) p
  else none
termination_by len - start

/-- If `p k = true` and `start ≤ k < len`, then `findIdx` returns a non-`none` result. -/
lemma findIdx_some_of_exists (len start k : Nat) (p : Nat → Bool)
    (hle : start ≤ k) (hk_lt : k < len) (hp : p k = true) :
    findIdx len start p ≠ none := by
  have h_base : findIdx len k p ≠ none := by
    unfold findIdx
    simp [hk_lt, hp]
  have h_step : ∀ i < k, start ≤ i → (findIdx len (i + 1) p ≠ none) → (findIdx len i p ≠ none) := by
    intro i hi hsi hnext
    have hi_lt_len : i < len := Nat.lt_trans hi hk_lt
    unfold findIdx
    simp [hi_lt_len]
    by_cases hpi : p i = true
    · simp [hpi]
    · simp [hpi, hnext]
  exact Nat.decreasingInduction' (m := start) (n := k)
    (h := h_step) (mn := hle) (hP := h_base)

/-- Full specification of `findIdx`: either a matching index is found (with `start ≤ i0 < len`,
`p i0 = true`, and all earlier indices `start ≤ i < i0` have `p i = false`), or no match
exists (returns `none` and every `start ≤ i < len` has `p i = false`). -/
lemma findIdx_spec (len start : Nat) (p : Nat → Bool) :
    (∃ i0, findIdx len start p = some i0 ∧ start ≤ i0 ∧ i0 < len ∧ p i0 = true ∧
      (∀ i, start ≤ i → i < i0 → p i = false))
    ∨ (findIdx len start p = none ∧ (∀ i, start ≤ i → i < len → p i = false)) := by
  induction' h_measure : len - start using Nat.strong_induction_on with d IH generalizing start
  unfold findIdx
  split
  · rename_i h_lt
    split
    · rename_i hp
      left
      refine ⟨start, rfl, le_refl start, h_lt, hp, λ i hi_start hi_lt_i => ?_⟩
      omega
    · rename_i hp
      have hpos : start < len := h_lt
      have h_lt_d : len - (start + 1) < d := by
        rw [← h_measure]
        exact Nat.sub_lt_sub_left hpos (Nat.lt_succ_self start)
      have ih := IH (len - (start + 1)) h_lt_d (start + 1) rfl
      rcases ih with (⟨i0, h_res, h_le, h_lt_len, hp0, h_earliest⟩ | ⟨h_res, h_all⟩)
      · left
        refine ⟨i0, h_res, by omega, h_lt_len, hp0, ?_⟩
        intro i hi_start hi_lt_i
        by_cases hi_eq_start : i = start
        · subst hi_eq_start
          simp [hp]
        · have hi_start_succ : start + 1 ≤ i := by omega
          exact h_earliest i hi_start_succ hi_lt_i
      · right
        refine ⟨h_res, ?_⟩
        intro i hi_start hi_lt_len
        by_cases hi_eq_start : i = start
        · subst hi_eq_start
          simp [hp]
        · have hi_start_succ : start + 1 ≤ i := by omega
          exact h_all i hi_start_succ hi_lt_len
  · rename_i h_ge
    right
    refine ⟨rfl, ?_⟩
    intro i hi_start hi_lt_len
    omega


/-! ### Ascending range search with `Prop` predicate -/

/-- Search for the smallest `i` with `k ≤ i < bound` such that `P i` holds.
    Returns `true` if found, `false` otherwise.
    Contrast with `findIdx` which returns `Option Nat` and uses `Nat → Bool` predicates. -/
def findUpTo (bound : Nat) (P : Nat → Prop) [DecidablePred P] (k : Nat) : Bool :=
  if h : k < bound then
    if hP : P k then
      true
    else
      findUpTo bound P (k + 1)
  else
    false
termination_by bound - k
decreasing_by
  all_goals
    exact Nat.sub_lt_sub_left h (Nat.lt_succ_self k)

/-- Soundness (aux): by induction on the remaining distance `n`, if `findUpTo` returns `true`
    and the distance from `k` to `bound` is at most `n`, then there exists `l` with
    `k ≤ l < bound` satisfying `P l`. -/
lemma findUpTo_sound_aux (bound : Nat) (P : Nat → Prop) [DecidablePred P]
    (n : Nat) : (∀ k, bound - k ≤ n → findUpTo bound P k = true → ∃ l, k ≤ l ∧ l < bound ∧ P l) := by
  induction' n with n IH
  · intro k hle h
    unfold findUpTo at h
    have hk : ¬ (k < bound) := by omega
    simp [hk] at h
  · intro k hle h
    unfold findUpTo at h
    by_cases hk : k < bound
    · simp [hk] at h
      by_cases hP : P k
      · simp [hP] at h
        exact ⟨k, le_refl k, hk, hP⟩
      · simp [hP] at h
        have hsub : bound - (k + 1) ≤ n := by omega
        rcases IH (k + 1) hsub h with ⟨l, hle', hlt, hP_l⟩
        refine ⟨l, ?_, hlt, hP_l⟩
        omega
    · simp [hk] at h

/-- Soundness: if `findUpTo` returns `true` when starting from `k`,
    then there exists `l` with `k ≤ l < bound` satisfying `P l`. -/
lemma findUpTo_sound (bound : Nat) (P : Nat → Prop) [DecidablePred P]
    (k : Nat) (h : findUpTo bound P k = true) : ∃ l, k ≤ l ∧ l < bound ∧ P l := by
  apply findUpTo_sound_aux bound P (bound - k) k (le_refl _) h

/-- Completeness: if `P l` holds with `l < bound` and `k ≤ l`,
    then `findUpTo` starting from `k` will return `true`. -/
lemma findUpTo_complete (bound : Nat) (P : Nat → Prop) [DecidablePred P]
    (l : Nat) (hP : P l) (hlt : l < bound) (k : Nat) (hk : k ≤ l) : findUpTo bound P k = true := by
  have h : ∀ d : Nat, (∀ n, l - n = d → n ≤ l → findUpTo bound P n = true) := by
    intro d
    induction' d with d IH
    · intro n hsub hn
      have hn_eq_l : n = l := by omega
      subst hn_eq_l
      unfold findUpTo
      simp [hlt, hP]
    · intro n hsub hn
      have hn_lt_l : n < l := by
        by_contra! hge
        have hsub0 : l - n = 0 := Nat.sub_eq_zero_of_le hge
        rw [hsub0] at hsub
        omega
      have hn_lt_bound : n < bound := Nat.lt_trans hn_lt_l hlt
      unfold findUpTo
      simp [hn_lt_bound]
      by_cases hP_n : P n
      · simp [hP_n]
      · have hsub_next : l - (n + 1) = d := by omega
        have hnext : findUpTo bound P (n + 1) = true :=
          IH (n + 1) hsub_next (by omega)
        simp [hP_n, hnext]
  exact h (l - k) k rfl hk


/-! ### Ascending linear search on `Nat` -/

/-- Recursive helper for linear search: find the smallest `i ≤ m` such that `P i = true`.
Returns `-1` if no such `i` exists. -/
def linearSearchAux (P : Nat → Bool) : Nat → Int
  | 0 => if P 0 then 0 else -1
  | m + 1 =>
    let prev := linearSearchAux P m
    if prev ≠ -1 then prev
    else if P (m + 1) then (m + 1 : Int)
    else -1

/-- Find the smallest `i ≤ bound` such that `P i = true`, or `-1` if none exists.
This is an ascending linear search (contrast with `maxByDecr` which descends). -/
def linearSearch (P : Nat → Bool) (bound : Nat) : Int :=
  linearSearchAux P bound

/-- Specification for `linearSearchAux`: either no `i ≤ m` satisfies `P`, or it returns the
    minimal `i ≤ m` where `P i = true`. -/
lemma linearSearchAux_spec (P : Nat → Bool) (m : Nat) :
    (linearSearchAux P m = -1 ∧ ∀ (i : Nat), i ≤ m → P i = false)
    ∨
    (∃ (i : Nat), linearSearchAux P m = (i : Int) ∧ i ≤ m ∧ P i = true ∧
           ∀ (j : Nat), j < i → P j = false) := by
  induction m with
  | zero =>
    dsimp [linearSearchAux]
    by_cases h : P 0
    · have htrue : P 0 = true := by simpa using h
      rw [htrue]
      right
      refine ⟨0, ?_, by omega, h, ?_⟩
      · simp
      · intro j hlt; omega
    · have hfalse : P 0 = false := by simpa using h
      rw [hfalse]
      left
      constructor
      · rfl
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        exact hfalse
  | succ m ih =>
    rcases ih with (⟨hprev, hprev_all⟩ | ⟨i, hprev_eq, hprev_le, hprev_true, hprev_min⟩)
    · dsimp [linearSearchAux]
      rw [hprev]
      by_cases h : P (m + 1)
      · have htrue : P (m + 1) = true := by simpa using h
        rw [htrue]
        right
        refine ⟨m + 1, ?_, by omega, h, ?_⟩
        · simp
        · intro j hlt
          have : j ≤ m := by omega
          exact hprev_all j this
      · have hfalse : P (m + 1) = false := by simpa using h
        rw [hfalse]
        left
        constructor
        · rfl
        · intro j hj
          have : j ≤ m ∨ j = m + 1 := by omega
          rcases this with (hle' | heq)
          · exact hprev_all j hle'
          · subst heq; exact hfalse
    · have hpos : (i : Int) ≠ -1 := by omega
      dsimp [linearSearchAux]
      rw [hprev_eq]
      have hif : (if (i : Int) ≠ -1 then (i : Int)
                  else if P (m + 1) then (m + 1 : Int) else -1) =
                (i : Int) := by
        simp [hpos]
      rw [hif]
      right
      refine ⟨i, rfl, ?_, hprev_true, hprev_min⟩
      omega

/-- Specification for `linearSearch`: either no `i ≤ bound` satisfies `P`, or it returns the
    minimal such `i`. -/
lemma linearSearch_spec (P : Nat → Bool) (bound : Nat) :
    (linearSearch P bound = -1 ∧ ∀ (i : Nat), i ≤ bound → P i = false)
    ∨
    (∃ (i : Nat), linearSearch P bound = (i : Int) ∧ i ≤ bound ∧ P i = true ∧
           ∀ (j : Nat), j < i → P j = false) := by
  dsimp [linearSearch]
  exact linearSearchAux_spec P bound


end Search

namespace Search


/-! ### Descending search on `Nat` -/

/-- Find the largest `n` in `[k, k-1, …, 0]` such that `p n` is true.
Returns `0` if no such `n` exists. -/
def maxByDecr (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k' + 1 =>
    if p (k' + 1) then k' + 1
    else maxByDecr p k'

/-- Specification of `maxByDecr p k`:
1. It returns a value ≤ k
2. Either `p` holds at the returned value, or the result is 0
3. It is maximal: any `j ≤ k` where `p` holds is ≤ the result -/
lemma maxByDecr_spec (p : Nat → Bool) (k : Nat) :
    (maxByDecr p k ≤ k) ∧
    (p (maxByDecr p k) = true ∨ maxByDecr p k = 0) ∧
    (∀ j, j ≤ k → p j = true → j ≤ maxByDecr p k) := by
  induction k with
  | zero =>
    unfold maxByDecr
    simp
  | succ k' ih =>
    unfold maxByDecr
    rcases ih with ⟨hle, hp_or, hmax⟩
    by_cases hc : p (k' + 1)
    · rw [if_pos hc]
      refine ⟨Nat.le_refl _, Or.inl hc, fun j hj _ => hj⟩
    · rw [if_neg hc]
      refine ⟨Nat.le_succ_of_le hle, hp_or, fun j hj hpj => ?_⟩
      by_cases hj' : j ≤ k'
      · exact hmax j hj' hpj
      · have h_eq : j = k' + 1 := by omega
        subst h_eq
        exfalso; exact hc hpj

/-- Search downward from `len` to `fallback` (inclusive). Returns the first `k` such that
`P k` is true, scanning from `len` down to `fallback`. If no such `k` is found, returns
`fallback`. This is like `maxByDecr` but with a configurable fallback value instead of
always returning `0`.

Contrast with `maxByDecr` which always returns `0` when no satisfying value exists.
`searchDownTo` is useful when you need a minimum bound (e.g., always return at least `1`
even when no witness is found). -/
def searchDownTo (P : Nat → Bool) (len fallback : Nat) : Nat :=
  match len with
  | 0 => fallback
  | l + 1 =>
    if P (l + 1) then
      l + 1
    else
      searchDownTo P l fallback

/-- For any `k` strictly between the search result and `len`, the predicate is false.
This is the maximality property of `searchDownTo`: the result is the largest index
in `[fallback, len]` satisfying `P`. -/
lemma searchDownTo_maximal (P : Nat → Bool) (len k fallback : Nat)
    (hk_gt : searchDownTo P len fallback < k) (hk_le : k ≤ len) : P k = false := by
  revert k
  induction len with
  | zero =>
    intro k
    simp [searchDownTo]; omega
  | succ l ih =>
    intro k hk_gt hk_le
    by_cases h_wit : P (l + 1) = true
    · have h_search : searchDownTo P (l + 1) fallback = l + 1 := by
        unfold searchDownTo; simp [h_wit]
      rw [h_search] at hk_gt
      omega
    · have h_not_wit : P (l + 1) = false := by
        cases hb : P (l + 1)
        · rfl
        · exfalso; exact h_wit hb
      simp [searchDownTo, h_not_wit] at hk_gt
      by_cases hk_eq : k = l + 1
      · subst hk_eq; exact h_not_wit
      · have hk_le_l : k ≤ l := by omega
        exact ih k hk_gt hk_le_l

/-- Find the largest `n` in `[k, k-1, …, 0]` such that `p n` holds.
Returns `-1` if no such `n` exists. Uses `Nat → Prop` with `[DecidablePred p]`.

Contrast with `maxByDecr` which uses `Nat → Bool` and returns `Nat` with `0` as sentinel.
`findMaxWhere` uses `Nat → Prop` and returns `Int` with `-1` as sentinel, making it
suitable for competitive programming contexts where `-1` indicates "not found". -/
def findMaxWhere (p : Nat → Prop) [DecidablePred p] (k : Nat) : Int :=
  if h : k = 0 then
    if p 0 then 0 else -1
  else if p k then
    Int.ofNat k
  else
    findMaxWhere p (k - 1)
termination_by k
decreasing_by
  have hpos : 0 < k := Nat.pos_of_ne_zero h
  exact Nat.sub_lt hpos (by decide : 0 < 1)

/-- Specification of `findMaxWhere p k`:
Either it returns `-1` and no `x ≤ k` satisfies `p`,
or it returns `Int.ofNat x` for some `x ≤ k` where `p x` holds and `x` is maximal
(any `y ≤ k` where `p y` holds satisfies `y ≤ x`). -/
lemma findMaxWhere_spec (p : Nat → Prop) [DecidablePred p] (k : Nat) :
    (findMaxWhere p k = -1 ∧ ¬ ∃ x : Nat, p x ∧ x ≤ k) ∨
    ∃ x : Nat, p x ∧ x ≤ k ∧ (∀ y : Nat, p y ∧ y ≤ k → y ≤ x) ∧
      findMaxWhere p k = Int.ofNat x := by
  induction' k using Nat.strong_induction_on with k IH
  unfold findMaxWhere
  split
  · rename_i hk
    subst hk
    split
    · rename_i hp
      right
      refine ⟨0, hp, ?_, ?_, rfl⟩
      · exact Nat.le_refl 0
      · intro y ⟨hy, hyle⟩
        omega
    · rename_i hp_not
      left
      constructor
      · rfl
      · rintro ⟨x, hx, hxle⟩
        have hx0 : x = 0 := by omega
        subst hx0
        exact hp_not hx
  · rename_i hk_ne
    split
    · rename_i hp
      right
      refine ⟨k, hp, ?_, ?_, rfl⟩
      · exact Nat.le_refl k
      · intro y ⟨hy, hyle⟩
        exact hyle
    · rename_i hp_not
      have hpos : 0 < k := Nat.pos_of_ne_zero hk_ne
      have hsub : k - 1 < k := Nat.sub_lt hpos (by decide : 0 < 1)
      have ih := IH (k - 1) hsub
      rcases ih with (⟨hres, hno⟩ | ⟨x, hx, hxle, hmax, hres⟩)
      · left
        constructor
        · exact hres
        · rintro ⟨y, hy, hyle⟩
          by_cases hy_eq_k : y = k
          · subst hy_eq_k
            exact hp_not hy
          · have hy_le_sub : y ≤ k - 1 := by
              have hy_lt_k : y < k := lt_of_le_of_ne hyle hy_eq_k
              omega
            exact hno ⟨y, hy, hy_le_sub⟩
      · right
        refine ⟨x, hx, ?_, ?_, hres⟩
        · omega
        · intro y ⟨hy, hyle⟩
          by_cases hy_eq_k : y = k
          · subst hy_eq_k
            exact (hp_not hy).elim
          · have hy_le_sub : y ≤ k - 1 := by
              have hy_lt_k : y < k := lt_of_le_of_ne hyle hy_eq_k
              omega
            exact hmax y ⟨hy, hy_le_sub⟩

/-- Find the largest natural number `< k` satisfying `P`. Returns `-1` if no such
number exists. Searches downwards from `k-1`.

Contrast with `findMaxWhere` which searches the inclusive range `≤ k`.
`findMaxBelow P k` is equivalent to `findMaxWhere P (k-1)` when `k > 0`,
and always returns `-1` when `k = 0`. -/
def findMaxBelow (P : Nat → Prop) [DecidablePred P] (k : Nat) : Int :=
  match k with
  | 0 => -1
  | k' + 1 =>
    if P k' then Int.ofNat k' else findMaxBelow P k'

/-- Correctness lemma for `findMaxBelow`:
* The result is `-1` iff no `p < k` satisfies `P`.
* If the result is not `-1`, it is the largest `p < k` satisfying `P`. -/
lemma findMaxBelow_correct (P : Nat → Prop) [DecidablePred P] (k : Nat) :
    (findMaxBelow P k = (-1 : Int) ↔ ∀ p : Nat, p < k → ¬ P p) ∧
    (findMaxBelow P k ≠ (-1 : Int) →
      ∃ p : Nat,
        findMaxBelow P k = Int.ofNat p ∧
        p < k ∧
        P p ∧
        ∀ q : Nat, q < k → P q → q ≤ p) := by
  induction' k with k' ih
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro _ p hp; exact absurd hp (Nat.not_lt_zero p)
      · intro _; rfl
    · intro h; exact absurd rfl h
  · have hsrch : findMaxBelow P (k' + 1) =
        if P k' then Int.ofNat k' else findMaxBelow P k' := by
      simp [findMaxBelow]
    rw [hsrch]
    by_cases hP : P k'
    · simp only [hP, ↓reduceIte]
      have hlt : k' < k' + 1 := Nat.lt_succ_self k'
      have hne : Int.ofNat k' ≠ (-1 : Int) := Int.natCast_ne_neg_one (n := k')
      constructor
      · constructor
        · intro h_eq; exact absurd h_eq hne
        · intro h_all; exfalso; exact h_all k' hlt hP
      · intro _
        refine ⟨k', rfl, hlt, hP, fun q hq _ => ?_⟩
        rw [Nat.lt_succ_iff] at hq; exact hq
    · simp only [hP, ↓reduceIte]
      rcases ih with ⟨⟨h_eq_to, h_to_eq⟩, h_ne⟩
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro h_eq p hp
          rw [Nat.lt_succ_iff] at hp
          rcases Nat.eq_or_lt_of_le hp with (rfl | hp')
          · exact hP
          · exact h_eq_to h_eq p hp'
        · intro h_all
          apply h_to_eq
          intro p hp
          apply h_all p
          exact Nat.lt_of_lt_of_le hp (Nat.le_succ k')
      · intro h_search_ne
        rcases h_ne h_search_ne with ⟨p, hp_eq, hp_lt, hpP, hp_max⟩
        refine ⟨p, hp_eq, Nat.lt_of_lt_of_le hp_lt (Nat.le_succ k'), hpP, ?_⟩
        intro q hq hqP
        rw [Nat.lt_succ_iff] at hq
        rcases Nat.eq_or_lt_of_le hq with (rfl | hq')
        · exact absurd hqP hP
        · exact hp_max q hq' hqP

/-- The search result is `-1` iff no element below `k` satisfies `P`. -/
lemma findMaxBelow_eq_neg_one_iff (P : Nat → Prop) [DecidablePred P] (k : Nat) :
    findMaxBelow P k = (-1 : Int) ↔ ∀ p : Nat, p < k → ¬ P p :=
  (findMaxBelow_correct P k).1

/-- If the search does not return `-1`, it found a maximal element below `k` satisfying `P`. -/
lemma findMaxBelow_ne_neg_one (P : Nat → Prop) [DecidablePred P] (k : Nat)
    (h : findMaxBelow P k ≠ (-1 : Int)) :
    ∃ p : Nat,
      findMaxBelow P k = Int.ofNat p ∧
      p < k ∧
      P p ∧
      ∀ q : Nat, q < k → P q → q ≤ p :=
  (findMaxBelow_correct P k).2 h

/-- Find the smallest `m ≤ cur` such that `p m` is true,
given that `p cur` is true and `p` is monotone
(if `p m₁` and `m₁ ≤ m₂` then `p m₂`).
Descends from `cur` until `p` becomes false, then returns the last true position.

Contrast with `maxByDecr` which finds the *largest* satisfying index below a bound
by scanning the full range, and `firstTrue` which binary-searches for the first true
in a given interval `[lo, hi]`. `minByDecr` is a linear descent from a known true point. -/
def minByDecr (p : Nat → Bool) (cur : Nat) : Nat :=
  if h : cur = 0 then 0
  else
    let prev := cur - 1
    if p prev then minByDecr p prev
    else cur
termination_by cur
decreasing_by
  have hpos : 0 < cur := Nat.pos_of_ne_zero h
  exact Nat.sub_lt hpos (by decide)


/-! ### Descending search from `k` down to `min` with `Option` return -/

/-- Search downward from `k` for the largest index `i` (where `min ≤ i ≤ k`) such that `P i` holds.
Returns `some i` if found, or `none` if no such `i` exists in `[min, k]`.

This is a `Nat → Prop` predicate version returning `Option Nat`, as opposed to
`findMaxWhere` which returns `Int` with `-1` as sentinel. Contrast also with
`searchDownTo` which uses `Nat → Bool` and returns a bare `Nat` with a configurable
fallback value.

The function terminates because `k` strictly decreases on each recursive call
(except at `k = 0`, which is handled as a base case). -/
def findLargestWhere (P : Nat → Prop) [DecidablePred P] (min k : Nat) : Option Nat :=
  if k < min then
    none
  else if hkz : k = 0 then
    if hP : P 0 then some 0 else none
  else if hP : P k then
    some k
  else
    have hpos : 0 < k := Nat.pos_of_ne_zero hkz
    have : k - 1 < k := Nat.sub_lt hpos (by omega)
    findLargestWhere P min (k - 1)
termination_by k

/-- Specification of `findLargestWhere`:
either no `p` in `[min, k]` satisfies `P` (and the result is `none`),
or the result is `some p` where `p` is the largest element in `[min, k]` satisfying `P`. -/
lemma findLargestWhere_spec (P : Nat → Prop) [DecidablePred P] (min k : Nat) :
    (findLargestWhere P min k = none ∧ ∀ p : Nat, min ≤ p → p ≤ k → ¬ P p) ∨
    (∃ p : Nat, findLargestWhere P min k = some p ∧ P p ∧ min ≤ p ∧ p ≤ k ∧
      ∀ q : Nat, min ≤ q → q ≤ k → P q → q ≤ p) := by
  induction' k using Nat.strong_induction_on with k ih
  unfold findLargestWhere
  split
  · -- k < min
    left
    constructor
    · rfl
    · intro p hpmin hplek; omega
  · rename_i hkge
    split
    · -- k = 0 case
      rename_i hkz
      split
      · -- P 0
        rename_i hP0
        right
        refine ⟨0, rfl, hP0, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro q hqmin hqle hqP; omega
      · -- ¬ P 0
        rename_i hnotP0
        left
        constructor
        · rfl
        · intro p hpmin hple
          have hp0 : p = 0 := by
            have : k = 0 := hkz
            omega
          subst hp0; exact hnotP0
    · -- k ≠ 0
      rename_i hknz
      split
      · -- P k
        rename_i hPk
        right
        refine ⟨k, rfl, hPk, ?_, le_refl k, ?_⟩
        · omega
        · intro q hqmin hqle hqP; exact hqle
      · -- ¬ P k, recurse
        rename_i hkPf
        have hpos : 0 < k := Nat.pos_of_ne_zero hknz
        have hsub : k - 1 < k := Nat.sub_lt hpos (by omega)
        rcases ih (k - 1) hsub with (⟨hnone, hPnone⟩ | ⟨p, hsome, hPp, hpmin, hple, hmax⟩)
        · left
          constructor
          · exact hnone
          · intro p hpmin' hplek
            by_cases hpk : p = k
            · subst hpk; exact hkPf
            · have hplekm1 : p ≤ k - 1 := by omega
              exact hPnone p hpmin' hplekm1
        · right
          refine ⟨p, hsome, hPp, hpmin, ?_, ?_⟩
          · omega
          · intro q hqmin hqlek hqP
            by_cases hqk : q = k
            · subst hqk; exact (hkPf hqP).elim
            · have hqlekm1 : q ≤ k - 1 := by omega
              exact hmax q hqmin hqlekm1 hqP


end Search

namespace Search

/-! ### Ascending range search with fuel (returns `Int` with `-1` sentinel) -/

/-- Fuel-based scan from `start` to `len` (exclusive) for the first index `i` where `p i` is true.
Returns `-1` if no such index exists. The `fuel` parameter guarantees termination.

Contrast with `linearSearch` which always starts from `0`, and `findIdx` which returns `Option Nat`.
`findFirstFuel` is the most general variant: it allows starting from any `start`, scanning up to
`len` (exclusive), with an explicit `fuel` bound. -/
def findFirstFuel (len start fuel : Nat) (p : Nat → Bool) : Int :=
  match fuel with
  | 0 => -1
  | fuel'+1 =>
    if _h : start < len then
      if p start then
        (start : Int)
      else
        findFirstFuel len (start + 1) fuel' p
    else
      -1

/-- Scan from `start` to `len` (exclusive) for the first index satisfying `p`.
This is a convenience wrapper around `findFirstFuel` using `len` as the fuel.

Contrast with `linearSearch` (starts from `0`) and `findIdx` (returns `Option Nat`). -/
def findFirst (len start : Nat) (p : Nat → Bool) : Int :=
  findFirstFuel len start len p

/-- If fuel is sufficient (`start + fuel ≥ len`) and the scan returns `-1`, then no position from
`start` to `len - 1` satisfies `p`. -/
lemma findFirstFuel_none (len start fuel : Nat) (p : Nat → Bool)
    (hfuel : start + fuel ≥ len) (hres : findFirstFuel len start fuel p = -1) :
    ∀ j, start ≤ j → j < len → p j = false := by
  induction fuel generalizing start with
  | zero =>
    intro j hj_start hj_len
    have hlen_le_start : len ≤ start := by
      simpa using hfuel
    have hj_lt_start : j < start := lt_of_lt_of_le hj_len hlen_le_start
    exact absurd hj_start (Nat.not_le_of_lt hj_lt_start)
  | succ fuel ih =>
    intro j hj_start hj_len
    unfold findFirstFuel at hres
    by_cases hstart : start < len
    · simp [hstart] at hres
      by_cases hp : p start
      · simp [hp] at hres
      · simp [hp] at hres
        by_cases h_eq_start : j = start
        · subst h_eq_start; simpa using hp
        · have hj_start_succ : start + 1 ≤ j :=
            Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hj_start (Ne.symm h_eq_start))
          have hfuel_succ : (start + 1) + fuel ≥ len := by
            omega
          exact ih (start := start + 1) hfuel_succ hres j hj_start_succ hj_len
    · have hlen_le_start : len ≤ start := Nat.le_of_not_lt hstart
      have hj_lt_start : j < start := lt_of_lt_of_le hj_len hlen_le_start
      exact absurd hj_start (Nat.not_le_of_lt hj_lt_start)

/-- The result of `findFirstFuel` is either `-1` or a natural number cast to `Int`. -/
lemma findFirstFuel_cases (len start fuel : Nat) (p : Nat → Bool) :
    findFirstFuel len start fuel p = (-1 : Int) ∨
    ∃ (k : Nat), findFirstFuel len start fuel p = (k : Int) := by
  induction fuel generalizing start with
  | zero =>
    left; rfl
  | succ fuel ih =>
    dsimp [findFirstFuel]
    by_cases hstart : start < len
    · rw [if_pos hstart]
      by_cases hp : p start
      · rw [if_pos hp]; right; exact ⟨start, rfl⟩
      · rw [if_neg hp]
        have h_ih := ih (start + 1)
        rcases h_ih with (h | ⟨k', h⟩)
        · left; exact h
        · right; exact ⟨k', h⟩
    · rw [if_neg hstart]; left; rfl

/-- If fuel is sufficient (`start + fuel ≥ len`) and the scan returns a non-negative index `idx`,
then `idx` is the first position from `start` onward satisfying `p`. -/
lemma findFirstFuel_some (len start fuel : Nat) (p : Nat → Bool) (idx : Nat)
    (hfuel : start + fuel ≥ len) (hres : findFirstFuel len start fuel p = (idx : Int)) :
    start ≤ idx ∧ idx < len ∧ p idx = true ∧
    (∀ j, start ≤ j → j < idx → p j = false) := by
  induction fuel generalizing start with
  | zero =>
    unfold findFirstFuel at hres
    simp at hres
  | succ fuel ih =>
    unfold findFirstFuel at hres
    by_cases hstart : start < len
    · simp [hstart] at hres
      by_cases hp : p start
      · simp [hp] at hres
        have h_idx_eq_start : idx = start := by
          apply Int.ofNat_inj.mp; simpa using hres.symm
        rw [h_idx_eq_start]
        refine ⟨le_rfl, hstart, hp, ?_⟩
        intro j hj_start hj_lt
        exfalso
        exact Nat.not_lt.mpr hj_start hj_lt
      · have hp_false : p start = false := Bool.eq_false_of_not_eq_true hp
        simp [hp_false] at hres
        have hfuel_succ : (start + 1) + fuel ≥ len := by
          omega
        have ih_res := ih (start := start + 1) hfuel_succ hres
        rcases ih_res with ⟨h_idx_ge_succ, h_idx_lt_len, hp_idx, h_earlier⟩
        have h_idx_ge_start : start ≤ idx :=
          Nat.le_trans (Nat.le_succ start) h_idx_ge_succ
        refine ⟨h_idx_ge_start, h_idx_lt_len, hp_idx, ?_⟩
        intro j hj_start hj_lt_idx
        by_cases h_eq : j = start
        · subst h_eq; exact hp_false
        · have hj_ge_succ : start + 1 ≤ j :=
            Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hj_start (Ne.symm h_eq))
          exact h_earlier j hj_ge_succ hj_lt_idx
    · simp [hstart] at hres

/-- Combined specification for `findFirst`: either it finds the first matching index
within `[start, len)`, or no such index exists and it returns `-1`. -/
lemma findFirst_spec (len start : Nat) (p : Nat → Bool) :
    (∃ j, start ≤ j ∧ j < len ∧ p j = true ∧
     (∀ j', start ≤ j' → j' < j → p j' = false) ∧
     findFirst len start p = (j : Int)) ∨
    (findFirst len start p = -1 ∧
     ∀ j, start ≤ j → j < len → p j = false) := by
  unfold findFirst
  have hfuel : start + len ≥ len := Nat.le_add_left len start
  rcases findFirstFuel_cases len start len p with (hneg | ⟨idx, hidx⟩)
  · right
    exact ⟨hneg, findFirstFuel_none len start len p hfuel hneg⟩
  · rcases findFirstFuel_some len start len p idx hfuel hidx with ⟨hge, hlt, hp, hmin⟩
    left
    exact ⟨idx, hge, hlt, hp, hmin, hidx⟩

end Search
