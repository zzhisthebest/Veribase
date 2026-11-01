import Mathlib

namespace Finset

/-- Given `h : ∀ x ∈ Finset.Icc lo hi, P x` and proofs that `lo ≤ x` and `x ≤ hi`,
deduce `P x`. This is a convenience lemma to avoid manually constructing
`Finset.mem_Icc.mpr ⟨hlo, hhi⟩` at every call site. -/
lemma forall_Icc {lo hi : Nat} {P : Nat → Prop}
    (h : ∀ x ∈ Finset.Icc lo hi, P x) (x : Nat) (hlo : lo ≤ x) (hhi : x ≤ hi) : P x :=
  h x (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)

/-- The subset of `{0, 1, ..., n-1}` satisfying a predicate `p : ℕ → Prop`.
Uses `classical` to obtain decidability, so this is `noncomputable`.

This is a convenience wrapper around `(Finset.range n).filter p` for predicates
that are `ℕ → Prop` rather than `ℕ → Bool` or `DecidablePred`. -/
noncomputable def filterRange_specificDuplicate (n : ℕ) (p : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.range n).filter p

/-- A natural number `k` is in `(Finset.range n).filter P` iff `k < n` and `P k` is true. -/
lemma mem_filter_range_iff_specificDuplicate {n k : Nat} {P : Nat → Bool} :
    k ∈ (Finset.range n).filter (λ i => P i) ↔ k < n ∧ P k := by
  simp

/-- `(Finset.range n).filter P` is nonempty iff there exists `k < n` such that `P k` is true. -/
lemma filter_range_nonempty_iff {n : Nat} {P : Nat → Bool} :
    ((Finset.range n).filter (λ i => P i)).Nonempty ↔ ∃ k, k < n ∧ P k := by
  constructor
  · intro h; rcases h with ⟨k, hk⟩; rw [mem_filter_range_iff_specificDuplicate] at hk; exact ⟨k, hk⟩
  · intro ⟨k, hk_lt, hk_P⟩; refine ⟨k, ?_⟩; rw [mem_filter_range_iff_specificDuplicate]; exact ⟨hk_lt, hk_P⟩

/-- Maximum element of a `Finset`, or `d` if the set is empty.
This wraps `Finset.max'` with a user-specified default value,
avoiding the need for a `Nonempty` proof at the call site. -/
def maxDefault {α : Type} [LinearOrder α] (s : Finset α) (d : α) : α :=
  if h : s.Nonempty then s.max' h else d

/-- When the set is nonempty, `maxDefault` equals `max'`. -/
lemma maxDefault_eq_max'_of_nonempty {α : Type} [LinearOrder α] (s : Finset α) (d : α) (h : s.Nonempty) :
    maxDefault s d = s.max' h := by
  unfold maxDefault; rw [dif_pos h]

/-- If `maxDefault s d ≠ d`, then `maxDefault s d` is an element of `s`. -/
lemma mem_of_maxDefault_ne {α : Type} [LinearOrder α] (s : Finset α) (d : α) (hne : maxDefault s d ≠ d) :
    maxDefault s d ∈ s := by
  by_cases h : s.Nonempty
  · have h_eq : maxDefault s d = s.max' h := maxDefault_eq_max'_of_nonempty s d h
    rw [h_eq]
    exact Finset.max'_mem _ h
  · have h_eq : maxDefault s d = d := by
      unfold maxDefault; simp [h]
    rw [h_eq] at hne
    exact (hne rfl).elim

/-- Every element of `s` is ≤ `maxDefault s d`. -/
lemma le_maxDefault {α : Type} [LinearOrder α] (s : Finset α) (d : α) {x : α} (hx : x ∈ s) :
    x ≤ maxDefault s d := by
  unfold maxDefault
  have hn : s.Nonempty := ⟨x, hx⟩
  rw [dif_pos hn]
  exact Finset.le_max' s x hx

/-- Maximum value of `score` over `domain`, or `default` if `domain` is empty.
This is `maxDefault` lifted through a scoring function:
`maxScore d dom score = maxDefault (dom.image score) d`. -/
def maxScore [DecidableEq β] [LinearOrder β]
    (default : β) (domain : Finset α) (score : α → β) : β :=
  if h : domain.Nonempty then
    (domain.image score).max' (h.image score)
  else
    default

/-- Minimum value of `score` over `domain`, or `default` if `domain` is empty. -/
def minScore [DecidableEq β] [LinearOrder β]
    (default : β) (domain : Finset α) (score : α → β) : β :=
  if h : domain.Nonempty then
    (domain.image score).min' (h.image score)
  else
    default

/-- Elements of `domain` that achieve the maximum score. -/
def maxCandidates [DecidableEq α] [DecidableEq β] [LinearOrder β]
    (default : β) (domain : Finset α) (score : α → β) : Finset α :=
  domain.filter fun x => score x = maxScore default domain score

/-- Elements of `domain` that achieve the minimum score. -/
def minCandidates [DecidableEq α] [DecidableEq β] [LinearOrder β]
    (default : β) (domain : Finset α) (score : α → β) : Finset α :=
  domain.filter fun x => score x = minScore default domain score

/-- The smallest element of a `Finset`, or `default` if the set is empty.
This is `Finset.min'` with a user-specified default value. -/
def earliest [DecidableEq α] [LinearOrder α]
    (default : α) (domain : Finset α) : α :=
  if h : domain.Nonempty then
    domain.min' h
  else
    default

/-- The smallest element of `domain` that achieves the maximum score.
If there are ties for the max score, returns the earliest (smallest) element. -/
def earliestMax [DecidableEq α] [LinearOrder α] [DecidableEq β] [LinearOrder β]
    (defaultArg : α) (defaultScore : β) (domain : Finset α) (score : α → β) : α :=
  earliest defaultArg (maxCandidates defaultScore domain score)

/-- The smallest element of `domain` that achieves the minimum score.
If there are ties for the min score, returns the earliest (smallest) element. -/
def earliestMin [DecidableEq α] [LinearOrder α] [DecidableEq β] [LinearOrder β]
    (defaultArg : α) (defaultScore : β) (domain : Finset α) (score : α → β) : α :=
  earliest defaultArg (minCandidates defaultScore domain score)

/-! ### Properties of `maxScore` and `minScore` -/

lemma maxScore_eq_of_nonempty [DecidableEq β] [LinearOrder β]
    {default : β} {domain : Finset α} {score : α → β}
    (h : domain.Nonempty) :
    maxScore default domain score = (domain.image score).max' (h.image score) := by
  simp [maxScore, h]

lemma le_maxScore_of_mem [DecidableEq β] [LinearOrder β]
    {default : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) {x : α} (hx : x ∈ domain) :
    score x ≤ maxScore default domain score := by
  rw [maxScore_eq_of_nonempty hne]
  exact Finset.le_max' (domain.image score) (score x)
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- If the domain is nonempty, the maximum score is attained by some element:
there exists `x ∈ domain` such that `score x = maxScore default domain score`.
This is the "maximum is attained" property, complementing `le_maxScore_of_mem`
which states that every score is ≤ the max. -/
lemma exists_score_eq_maxScore [DecidableEq β] [LinearOrder β]
    {default : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) :
    ∃ x, x ∈ domain ∧ score x = maxScore default domain score := by
  rw [maxScore_eq_of_nonempty hne]
  have h_mem : (domain.image score).max' (hne.image score) ∈ domain.image score :=
    Finset.max'_mem _ _
  rcases Finset.mem_image.mp h_mem with ⟨x, hx, hx_eq⟩
  refine ⟨x, hx, hx_eq⟩

/-! ### Properties of `earliest` -/

lemma earliest_eq_of_nonempty [DecidableEq α] [LinearOrder α]
    {default : α} {domain : Finset α} (hne : domain.Nonempty) :
    earliest default domain = domain.min' hne := by
  simp [earliest, hne]

lemma earliest_le [DecidableEq α] [LinearOrder α]
    {default : α} {domain : Finset α} (hne : domain.Nonempty)
    {x : α} (hx : x ∈ domain) :
    earliest default domain ≤ x := by
  rw [earliest_eq_of_nonempty hne]
  exact Finset.min'_le domain x hx

/-! ### Properties of `maxCandidates` and `minCandidates` -/

lemma maxCandidates_nonempty [DecidableEq α] [DecidableEq β] [LinearOrder β]
    {default : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) :
    (maxCandidates default domain score).Nonempty := by
  have hmem : maxScore default domain score ∈ domain.image score := by
    rw [maxScore_eq_of_nonempty hne]
    exact Finset.max'_mem (domain.image score) (hne.image score)
  rcases Finset.mem_image.mp hmem with ⟨s, hs, hsScore⟩
  refine ⟨s, ?_⟩
  simp [maxCandidates, hs, hsScore]

lemma minCandidates_nonempty [DecidableEq α] [DecidableEq β] [LinearOrder β]
    {default : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) :
    (minCandidates default domain score).Nonempty := by
  have hmem : minScore default domain score ∈ domain.image score := by
    dsimp [minScore]
    rw [dif_pos hne]
    exact Finset.min'_mem (domain.image score) (hne.image score)
  rcases Finset.mem_image.mp hmem with ⟨s, hs, hsScore⟩
  refine ⟨s, ?_⟩
  simp [minCandidates, hs, hsScore]

/-! ### Properties of `earliestMax` and `earliestMin` -/

lemma earliestMax_eq_of_nonempty [DecidableEq α] [LinearOrder α]
    [DecidableEq β] [LinearOrder β]
    {defaultArg : α} {defaultScore : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) :
    earliestMax defaultArg defaultScore domain score =
      (maxCandidates defaultScore domain score).min'
        (maxCandidates_nonempty (default := defaultScore) (score := score) hne) := by
  simp [earliestMax, earliest, maxCandidates_nonempty (default := defaultScore) (score := score) hne]

lemma earliestMin_eq_of_nonempty [DecidableEq α] [LinearOrder α]
    [DecidableEq β] [LinearOrder β]
    {defaultArg : α} {defaultScore : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) :
    earliestMin defaultArg defaultScore domain score =
      (minCandidates defaultScore domain score).min'
        (minCandidates_nonempty (default := defaultScore) (score := score) hne) := by
  simp [earliestMin, earliest, minCandidates_nonempty (default := defaultScore) (score := score) hne]

lemma earliestMax_earliest [DecidableEq α] [LinearOrder α]
    [DecidableEq β] [LinearOrder β]
    {defaultArg : α} {defaultScore : β} {domain : Finset α} {score : α → β}
    (hne : domain.Nonempty) {x : α} (hx : x ∈ domain)
    (hscore : score x = score (earliestMax defaultArg defaultScore domain score)) :
    earliestMax defaultArg defaultScore domain score ≤ x := by
  have hscore_eq : score (earliestMax defaultArg defaultScore domain score) =
      maxScore defaultScore domain score := by
    rw [earliestMax_eq_of_nonempty hne]
    have hmem := Finset.min'_mem (maxCandidates defaultScore domain score)
      (maxCandidates_nonempty (default := defaultScore) (score := score) hne)
    simpa [maxCandidates] using (Finset.mem_filter.mp hmem).2
  rw [earliestMax_eq_of_nonempty hne]
  apply Finset.min'_le
  simp [maxCandidates, hx, hscore, hscore_eq]

/-! ### Argmin-max on `Ico` intervals

Operations for finding the smallest element in a `Nat` interval `[lo, hi)` that achieves
the maximum value of a function `f : Nat → Nat`. This is the "earliest maximum" pattern
common in competitive programming (e.g., "find the earliest year with max population").
-/

/-- The maximum value of `f` on the interval `[lo, hi)`. -/
def maxOnIco (lo hi : Nat) (f : Nat → Nat) : Nat :=
  Finset.sup (Finset.Ico lo hi) f

/-- Every `y` in `[lo, hi)` satisfies `f y ≤ maxOnIco lo hi f`. -/
lemma le_maxOnIco (lo hi : Nat) (f : Nat → Nat) {y : Nat} (hy : y ∈ Finset.Ico lo hi) :
    f y ≤ maxOnIco lo hi f := by
  simpa [maxOnIco] using Finset.le_sup hy

/-- The subset of `[lo, hi)` where `f` achieves its maximum value on the interval. -/
def argmaxOnIco (lo hi : Nat) (f : Nat → Nat) : Finset Nat :=
  Finset.filter (λ y => f y = maxOnIco lo hi f) (Finset.Ico lo hi)

/-- When `lo < hi`, the argmax set is nonempty. -/
lemma argmaxOnIco_nonempty (lo hi : Nat) (h_lt : lo < hi) (f : Nat → Nat) :
    (argmaxOnIco lo hi f).Nonempty := by
  have h_Ico_nonempty : (Finset.Ico lo hi).Nonempty := by
    refine ⟨lo, Finset.mem_Ico.mpr ⟨le_rfl, h_lt⟩⟩
  rcases Finset.exists_mem_eq_sup (Finset.Ico lo hi) h_Ico_nonempty f with ⟨y, hy, h_eq⟩
  refine ⟨y, ?_⟩
  simp [argmaxOnIco, maxOnIco, hy, h_eq]

/-- The smallest `y` in `[lo, hi)` achieving the maximum value of `f`.
Requires `h_lt : lo < hi` to guarantee the interval is nonempty. -/
def argminMaxOnIco (lo hi : Nat) (f : Nat → Nat) (h_lt : lo < hi) : Nat :=
  (argmaxOnIco lo hi f).min' (argmaxOnIco_nonempty lo hi h_lt f)

/-- Specification of `argminMaxOnIco`: the result lies in `[lo, hi)`, maximizes `f` on
the interval, and is strictly greater than any earlier (smaller-index) maximizer.
This enforces the tie-breaking rule: among all elements achieving the maximum,
the smallest one is chosen. -/
lemma argminMaxOnIco_spec (lo hi : Nat) (h_lt : lo < hi) (f : Nat → Nat) :
    lo ≤ argminMaxOnIco lo hi f h_lt ∧ argminMaxOnIco lo hi f h_lt < hi ∧
    (∀ y, lo ≤ y → y < hi → f (argminMaxOnIco lo hi f h_lt) ≥ f y) ∧
    (∀ y, lo ≤ y → y < argminMaxOnIco lo hi f h_lt → f (argminMaxOnIco lo hi f h_lt) > f y) := by
  unfold argminMaxOnIco
  let r := (argmaxOnIco lo hi f).min' (argmaxOnIco_nonempty lo hi h_lt f)
  have hr_mem_cand : r ∈ argmaxOnIco lo hi f :=
    Finset.min'_mem (argmaxOnIco lo hi f) (argmaxOnIco_nonempty lo hi h_lt f)
  have hr_mem_Ico : r ∈ Finset.Ico lo hi := by
    rcases Finset.mem_filter.mp hr_mem_cand with ⟨h, _⟩
    exact h
  have hr_val_eq : f r = maxOnIco lo hi f := by
    rcases Finset.mem_filter.mp hr_mem_cand with ⟨_, h⟩
    exact h
  have hr_bounds : lo ≤ r ∧ r < hi :=
    Finset.mem_Ico.mp hr_mem_Ico
  have hr_lower : lo ≤ r := hr_bounds.1
  have hr_upper : r < hi := hr_bounds.2
  have h_ge : ∀ y, lo ≤ y → y < hi → f r ≥ f y := by
    intro y hy_low hy_high
    have hy_mem_Ico : y ∈ Finset.Ico lo hi :=
      Finset.mem_Ico.mpr ⟨hy_low, hy_high⟩
    rw [hr_val_eq]
    exact le_maxOnIco lo hi f hy_mem_Ico
  have h_gt : ∀ y, lo ≤ y → y < r → f r > f y := by
    intro y hy_low hy_lt
    have hy_lt_hi : y < hi := by
      omega
    have hy_mem_Ico : y ∈ Finset.Ico lo hi :=
      Finset.mem_Ico.mpr ⟨hy_low, hy_lt_hi⟩
    have hy_f_le : f y ≤ maxOnIco lo hi f :=
      le_maxOnIco lo hi f hy_mem_Ico
    by_cases h_eq : f r = f y
    · have h_f_eq_max : f y = maxOnIco lo hi f := by
        rw [← hr_val_eq, h_eq]
      have hy_mem_cand : y ∈ argmaxOnIco lo hi f := by
        simp [argmaxOnIco, Finset.mem_filter, hy_mem_Ico, h_f_eq_max]
      have h_r_le_y : r ≤ y :=
        Finset.min'_le (argmaxOnIco lo hi f) y hy_mem_cand
      omega
    · have h_le : f y ≤ f r := by
        rw [hr_val_eq]
        exact hy_f_le
      exact Nat.lt_of_le_of_ne h_le (Ne.symm h_eq)
  exact ⟨hr_lower, hr_upper, h_ge, h_gt⟩

/-- The set of all ordered pairs `(i, j)` with `i < n` and `j < n`.
Equivalent to `(Finset.range n).product (Finset.range n)`.
This is the Cartesian product of `{0, …, n-1}` with itself, commonly used
as the index space for pair-wise operations on an `n`-element list or array. -/
def indexPairs_specificDuplicate (n : Nat) : Finset (Nat × Nat) :=
  (Finset.range n).product (Finset.range n)

/-! ### Proof-irrelevance of `max'` and `min'`

`Finset.max' s h` and `Finset.min' s h` depend on a proof `h : s.Nonempty`.
These lemmas state that the value does not depend on which proof is supplied,
since `s.Nonempty` is a `Subsingleton`. -/

/-- `s.max' h₁ = s.max' h₂` for any two proofs `h₁, h₂ : s.Nonempty`. -/
lemma max'_irrel_specificDuplicate {α : Type*} [LinearOrder α] {s : Finset α} {h₁ h₂ : s.Nonempty} :
    s.max' h₁ = s.max' h₂ := by
  have h_eq : h₁ = h₂ := Subsingleton.elim _ _
  subst h_eq
  rfl

/-- `s.min' h₁ = s.min' h₂` for any two proofs `h₁, h₂ : s.Nonempty`. -/
lemma min'_irrel_specificDuplicate {α : Type*} [LinearOrder α] {s : Finset α} {h₁ h₂ : s.Nonempty} :
    s.min' h₁ = s.min' h₂ := by
  have h_eq : h₁ = h₂ := Subsingleton.elim _ _
  subst h_eq
  rfl

end Finset
