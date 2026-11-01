import Mathlib

namespace List

/-- Check that a boolean predicate holds for every pair of elements at distinct positions. -/
def forAllPairs {α : Type u} (p : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => List.all xs (p x) && forAllPairs p xs

/-- Characterization of `forAllPairs` for symmetric predicates. -/
theorem forAllPairs_spec {α : Type u} (p : α → α → Bool)
    (hp_symm : ∀ a b, p a b = p b a) (l : List α) :
    forAllPairs p l = true ↔
      (∀ a b : Fin l.length, a ≠ b → p (l.get a) (l.get b) = true) := by
  have aux (xs : List α) : forAllPairs p xs = true ↔ List.Pairwise (fun a b => p a b = true) xs := by
    induction xs with
    | nil => simp [forAllPairs]
    | cons x xs ih => simp [forAllPairs, List.all_eq_true, List.pairwise_cons, ih]
  rw [aux, List.pairwise_iff_get]
  constructor
  · intro h a b hab
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact h a b hlt
    · rw [hp_symm]; exact h b a hlt
  · intro h a b hab
    exact h a b (ne_of_lt hab)

end List

/-!
# Order-related utilities

Operations on linearly ordered types.
-/

/-- Clamp a value `x` to the interval `[lo, hi]`. -/
def clamp {α : Type _} [LinearOrder α] (lo hi : α) (x : α) : α :=
  max lo (min x hi)

/-- In a linear order, if two elements are distinct and the first is not greater than the second,
    then the first is less than the second. -/
lemma lt_of_ne_of_not_gt {α : Type u} [LinearOrder α] {a b : α} (hne : a ≠ b) (hngt : ¬ a > b) : a < b := by
  have h_cases := lt_or_gt_of_ne hne
  rcases h_cases with (hlt | hgt)
  · exact hlt
  · exfalso; exact hngt hgt

/-- In a linear order, if `a` is not less than `b` and `a ≠ b`, then `b < a`.
This is the dual of `lt_of_ne_of_not_gt`. -/
lemma lt_of_not_lt_of_ne {α : Type u} [LinearOrder α] {a b : α} (hnotlt : ¬ a < b) (hne : a ≠ b) : b < a :=
  lt_of_le_of_ne (le_of_not_gt hnotlt) hne.symm

/-- In a linear order, from `¬ a > b` and `¬ b > a` we can deduce `a = b`. -/
lemma eq_of_not_gt_and_not_gt {α : Type u} [LinearOrder α] {a b : α} (h1 : ¬ a > b) (h2 : ¬ b > a) : a = b :=
  le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)

/-! ### Min/max transitivities -/

/-- In a linearly ordered type, if `a ≤ b` then `min a c ≤ max b c`.
This is a transitivity lemma combining `min_le_left` and `le_max_left`.
Useful for bounding a value that lies between the min of lower bounds
and the max of upper bounds. -/
lemma min_le_max_of_le {β : Type} [LinearOrder β] {a b c : β} (h : a ≤ b) : min a c ≤ max b c :=
  calc
    min a c ≤ a := min_le_left _ _
    _ ≤ b := h
    _ ≤ max b c := le_max_left _ _

/-- In a linearly ordered type, `max a b` is either `a` or `b`. -/
lemma max_eq_or {α : Type} [LinearOrder α] (a b : α) : max a b = a ∨ max a b = b := by
  by_cases h : a ≤ b
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left (le_of_not_ge h))

/-- In a linearly ordered type, `min a b` is either `a` or `b`. -/
lemma min_eq_or {α : Type} [LinearOrder α] (a b : α) : min a b = a ∨ min a b = b := by
  by_cases h : a ≤ b
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right (le_of_not_ge h))

/-- In a linearly ordered type, `max a (max b c)` is either `a`, `b`, or `c`.
This generalizes `max_eq_or` from two elements to three. -/
lemma max3_eq_cases {α : Type _} [LinearOrder α] (a b c : α) :
    max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
  by_cases ha : a ≥ max b c
  · left; simpa [max_comm a (max b c)] using max_eq_right ha
  · have hlt : a < max b c := lt_of_not_ge ha
    have h_eq : max a (max b c) = max b c := by
      simpa [max_comm a (max b c)] using max_eq_left (le_of_lt hlt)
    rw [h_eq]
    by_cases hb : b ≥ c
    · right; left; simpa [max_comm b c] using max_eq_right hb
    · right; right; simpa [max_comm b c] using max_eq_left (le_of_lt (lt_of_not_ge hb))

/-- In a linearly ordered type, `min a (min b c)` is either `a`, `b`, or `c`.
This generalizes `min_eq_or` from two elements to three. -/
lemma min3_eq_cases {α : Type _} [LinearOrder α] (a b c : α) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  by_cases ha : a ≤ min b c
  · left; simpa [min_comm a (min b c)] using min_eq_left ha
  · have hlt : min b c < a := lt_of_not_ge ha
    have h_eq : min a (min b c) = min b c := by
      simpa [min_comm a (min b c)] using min_eq_right (le_of_lt hlt)
    rw [h_eq]
    by_cases hb : b ≤ c
    · right; left; simpa [min_comm b c] using min_eq_left hb
    · right; right; simpa [min_comm b c] using min_eq_right (le_of_lt (lt_of_not_ge hb))

/-- In a linearly ordered type, the minimum of two elements is at most their maximum.
This is a basic comparison lemma: `min x y ≤ max x y`. -/
lemma le_min_max {α : Type} [LinearOrder α] (x y : α) : min x y ≤ max x y := by
  by_cases h : x ≤ y
  · rw [min_eq_left h, max_eq_right h]; exact h
  · have h' : y ≤ x := le_of_not_le h
    rw [min_eq_right h', max_eq_left h']; exact h'

/-- If the minimum and maximum of two elements are equal, then the elements are equal.
This is a key property relating `min` and `max` in a linear order. -/
lemma min_eq_max_imp_eq {α : Type} [LinearOrder α] {x y : α} (h : min x y = max x y) : x = y := by
  by_cases hle : x ≤ y
  · rw [min_eq_left hle, max_eq_right hle] at h; exact h
  · have hle' : y ≤ x := le_of_not_le hle
    rw [min_eq_right hle', max_eq_left hle'] at h; exact h.symm

/-- If two elements are distinct, their minimum and maximum are also distinct.
Contrapositive of `min_eq_max_imp_eq`. -/
lemma min_ne_max_of_ne {α : Type} [LinearOrder α] {x y : α} (hne : x ≠ y) : min x y ≠ max x y := by
  intro h; apply hne; exact min_eq_max_imp_eq h

/-- If `y ∈ xs`, then `min x y ∈ x :: xs`. Useful for membership proofs involving ordered pairs
constructed from list elements. -/
lemma mem_min_cons {α : Type} [LinearOrder α] {x y : α} {xs : List α} (hy : y ∈ xs) : min x y ∈ x :: xs := by
  by_cases h : x ≤ y
  · rw [min_eq_left h]; exact by simp
  · rw [min_eq_right (le_of_not_le h)]; exact List.mem_cons_of_mem _ hy

/-- If `y ∈ xs`, then `max x y ∈ x :: xs`. Companion to `mem_min_cons`. -/
lemma mem_max_cons {α : Type} [LinearOrder α] {x y : α} {xs : List α} (hy : y ∈ xs) : max x y ∈ x :: xs := by
  by_cases h : x ≤ y
  · rw [max_eq_right h]; exact List.mem_cons_of_mem _ hy
  · rw [max_eq_left (le_of_not_le h)]; exact by simp

/-! ### Transitivity lemma for partitioned indices

Useful for argmax/argmin proofs where a list is split into a prefix and suffix
with different comparison properties. -/

/-- Combine transitivity of `<` and `≤`: if all `i < bestIdx` satisfy `getter i < bestVal`,
all `bestIdx ≤ i < pos` satisfy `getter i ≤ bestVal`, and `bestVal < y`,
then all `i < pos` satisfy `getter i < y`.

This lemma partitions `[0, pos)` into `[0, bestIdx)` and `[bestIdx, pos)` and uses
transitivity to lift the bound from `bestVal` to `y`. -/
lemma all_lt_of_lt_best_and_le_between {α : Type} [LinearOrder α]
    (getter : Nat → α) (bestIdx pos : Nat) (bestVal y : α)
    (h_lt : ∀ i < bestIdx, getter i < bestVal)
    (h_le : ∀ i, bestIdx ≤ i → i < pos → getter i ≤ bestVal)
    (hy : bestVal < y) : ∀ i < pos, getter i < y := by
  intro i hi_pos
  by_cases hi_bestIdx : i < bestIdx
  · have hlt := h_lt i hi_bestIdx
    exact lt_trans hlt hy
  · have hle := h_le i (by omega) hi_pos
    exact lt_of_le_of_lt hle hy

/-! ### Interval overlap -/

/-- Check whether two intervals `[s1, e1]` and `[s2, e2]` overlap.
Returns `true` iff `max s1 s2 ≤ min e1 e2`. Generalized for any `LinearOrder` type. -/
def intervalsOverlap {α : Type} [LinearOrder α] (s1 e1 s2 e2 : α) : Bool :=
  decide (max s1 s2 ≤ min e1 e2)

/-- `intervalsOverlap s1 e1 s2 e2 = true` iff `max s1 s2 ≤ min e1 e2`. -/
lemma intervalsOverlap_spec {α : Type} [LinearOrder α] (s1 e1 s2 e2 : α) :
    intervalsOverlap s1 e1 s2 e2 = true ↔ max s1 s2 ≤ min e1 e2 := by
  unfold intervalsOverlap
  simp

/-! ### `decide` combined with `≤` for `LinearOrder` -/

/-- For types with a `LinearOrder`, `decide (a ≤ b)` is transitive.
This is a convenience lemma packaging `le_trans` with `decide` for use with
`List.sorted_mergeSort` and other APIs expecting boolean transitivity arguments. -/
lemma decide_le_trans {α : Type u} [LinearOrder α] (a b c : α) :
    decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
  intro h1 h2
  have h1' : a ≤ b := by simpa using h1
  have h2' : b ≤ c := by simpa using h2
  have h3' : a ≤ c := le_trans h1' h2'
  simpa using h3'

/-- For types with a `LinearOrder`, `(decide (a ≤ b) || decide (b ≤ a))` always holds (totality).
This is a convenience lemma packaging `le_total` with `decide` for use with
`List.sorted_mergeSort` and other APIs expecting boolean totality arguments. -/
lemma decide_le_total {α : Type u} [LinearOrder α] (a b : α) :
    (decide (a ≤ b) || decide (b ≤ a)) = true := by
  cases le_total a b with
  | inl h => simp [h]
  | inr h => simp [h]

/-- For types with a `LinearOrder`, `decide (a ≥ b)` is transitive.
This is the `≥` dual of `decide_le_trans`, useful for descending sorts using
`List.sorted_mergeSort` with `(fun a b => decide (a ≥ b))`. -/
lemma decide_ge_trans {α : Type u} [LinearOrder α] (a b c : α) :
    decide (a ≥ b) = true → decide (b ≥ c) = true → decide (a ≥ c) = true := by
  intro h1 h2
  have h1' : a ≥ b := by simpa using h1
  have h2' : b ≥ c := by simpa using h2
  have h3' : a ≥ c := le_trans h2' h1'
  simpa using h3'

/-- For types with a `LinearOrder`, `(decide (a ≥ b) || decide (b ≥ a))` always holds (totality).
This is the `≥` dual of `decide_le_total`, useful for descending sorts using
`List.sorted_mergeSort` with `(fun a b => decide (a ≥ b))`. -/
lemma decide_ge_total {α : Type u} [LinearOrder α] (a b : α) :
    (decide (a ≥ b) || decide (b ≥ a)) = true := by
  cases le_total a b with
  | inl h => simp [h]
  | inr h => simp [h]

/-! ### `decide` transitivity/totality lifted through a function

These generalize `decide_le_trans` and `decide_le_total` by allowing comparison via
a pre-transform `f : α → β`. Useful for sorting by a derived key, e.g., case-insensitive
string sorting via `String.toLower`. -/

/-- For types with a `LinearOrder` on the codomain, `decide` of `f a ≤ f b` is transitive
through a function `f`. This generalizes `decide_le_trans` by comparing via a pre-transform.
For example, `decide_le_trans_on (fun s : String => s.toLower) a b c h₁ h₂` gives
transitivity of case-insensitive string comparison. -/
lemma decide_le_trans_on {α β : Type} [LinearOrder β] (f : α → β) (a b c : α) :
    decide (f a ≤ f b) = true → decide (f b ≤ f c) = true → decide (f a ≤ f c) = true := by
  intro h₁ h₂
  have h₁' : f a ≤ f b := by simpa using h₁
  have h₂' : f b ≤ f c := by simpa using h₂
  have h₃' : f a ≤ f c := le_trans h₁' h₂'
  simpa using h₃'

/-- For types with a `LinearOrder` on the codomain, `(decide (f a ≤ f b) || decide (f b ≤ f a))`
always holds (totality through a function `f`). This generalizes `decide_le_total`. -/
lemma decide_le_total_on {α β : Type} [LinearOrder β] (f : α → β) (a b : α) :
    (decide (f a ≤ f b) || decide (f b ≤ f a)) = true := by
  have h := le_total (f a) (f b)
  cases h with
  | inl hle => simp [hle]
  | inr hle => simp [hle]


/-- If `f a = f b` then `f (max a b) = f a`. This holds because `max a b` is either `a` or `b`. -/
lemma max_f_eq_f_of_f_eq {α β : Type u} [LinearOrder α] (f : α → β) {a b : α} (h : f a = f b) : f (max a b) = f a := by
  rcases le_total a b with (hle | hge)
  · rw [max_eq_right hle, h]
  · rw [max_eq_left hge]

/-! ### Integer order -/

namespace Int

/-- If `a ≤ b` and `a ≠ b`, then `a + 1 ≤ b` (for `Int`).
Convenient combination of `lt_of_le_of_ne` and `Int.add_one_le_of_lt`. -/
lemma succ_le_of_lt_or_eq {a b : Int} (hle : a ≤ b) (hne : a ≠ b) : a + 1 ≤ b :=
  Int.add_one_le_of_lt ((lt_or_eq_of_le hle).resolve_right hne)

end Int

/-! ### Interval non-overlap (pair form) -/

/-- Check whether two intervals `(a.1, a.2)` and `(b.1, b.2)` are non-overlapping.
One interval ends before or at the start of the other. Generalized for any `LinearOrder` type.
Returns `true` iff `a.2 ≤ b.1 ∨ b.2 ≤ a.1`.

Contrast with `intervalsOverlap` which takes four explicit endpoints and checks for overlap. -/
def checkNonOverlap {α : Type u} [LinearOrder α] (a b : α × α) : Bool :=
  decide (a.2 ≤ b.1) || decide (b.2 ≤ a.1)

/-- `checkNonOverlap a b = true` iff `a.2 ≤ b.1 ∨ b.2 ≤ a.1`. -/
lemma checkNonOverlap_iff {α : Type u} [LinearOrder α] (a b : α × α) :
    checkNonOverlap a b = true ↔ a.2 ≤ b.1 ∨ b.2 ≤ a.1 := by
  simp [checkNonOverlap]

/-- `checkNonOverlap` is symmetric. -/
lemma checkNonOverlap_symm {α : Type u} [LinearOrder α] (a b : α × α) :
    checkNonOverlap a b = checkNonOverlap b a := by
  simp [checkNonOverlap, Bool.or_comm]

/-- Check that no pair of intervals in the list overlap (non-strict non-overlap: one interval
ends before or at the start of the other). Uses `List.forAllPairs` on all ordered pairs.
Generalized for any `LinearOrder` type.

Contrast with `List.intervalsNonOverlapping` which uses strict `<` and checks all pairs
including self-comparisons. -/
def intervalsNoOverlap {α : Type u} [LinearOrder α] (intervals : List (α × α)) : Bool :=
  List.forAllPairs checkNonOverlap intervals

/-- `intervalsNoOverlap l = true` iff for all distinct indices `a ≠ b`,
the intervals at those positions are non-overlapping. -/
lemma intervalsNoOverlap_spec {α : Type u} [LinearOrder α] (l : List (α × α)) :
    intervalsNoOverlap l = true ↔
    (∀ a b : Fin l.length, a ≠ b →
      let i := l.get a; let j := l.get b; i.2 ≤ j.1 ∨ j.2 ≤ i.1) := by
  simp [intervalsNoOverlap]
  rw [List.forAllPairs_spec checkNonOverlap checkNonOverlap_symm l]
  constructor
  · intro h a b hne
    have hp := h a b hne
    rw [checkNonOverlap_iff] at hp
    exact hp
  · intro h a b hne
    have hp := h a b hne
    rw [checkNonOverlap_iff]
    exact hp

/-! ### Relation pullbacks along a function

If `R` is a total/transitive relation on `β`, then its pullback `(fun a b => R (f a) (f b))`
inherits these properties on `α`. These are useful for sorting by a projection `f : α → β`
where the order on `β` is total and transitive. -/

/-- If `R` is a total relation on `β`, then its pullback along `f : α → β` is total on `α`. -/
lemma IsTotal.pullback {α β : Type} {R : β → β → Prop} [IsTotal β R] (f : α → β) :
    IsTotal α (fun a b => R (f a) (f b)) :=
  ⟨fun a b => IsTotal.total (f a) (f b)⟩

/-- If `R` is a transitive relation on `β`, then its pullback along `f : α → β` is transitive on `α`. -/
lemma IsTrans.pullback {α β : Type} {R : β → β → Prop} [IsTrans β R] (f : α → β) :
    IsTrans α (fun a b => R (f a) (f b)) :=
  ⟨fun a b c hab hbc => IsTrans.trans (f a) (f b) (f c) hab hbc⟩

/-! ### Normalized comparison relation

`normalizedLE f` compares elements by applying a normalization function `f` and then
comparing with `≤`. This is useful for case-insensitive comparison
(`normalizedLE String.toLower`), sorting by a derived key, etc.

`insertionSort_normalizedLE_spec` bundles the permutation and sortedness guarantees
when `List.insertionSort` is used with `normalizedLE f`. -/

/-- A relation that compares elements after applying a normalization function `f`.
`normalizedLE f a b` holds iff `f a ≤ f b`. -/
def normalizedLE {α : Type u} [LE α] (f : α → α) (a b : α) : Prop := f a ≤ f b

instance {α : Type u} [LE α] {f : α → α} [DecidableRel (fun a b => f a ≤ f b)] :
    DecidableRel (normalizedLE f) := by
  intro a b; unfold normalizedLE; infer_instance

instance {α : Type u} [LinearOrder α] {f : α → α} : IsTotal α (normalizedLE f) := by
  refine ⟨fun a b => ?_⟩
  unfold normalizedLE
  simpa using le_total (f a) (f b)

instance {α : Type u} [LE α] {f : α → α} [IsTrans α (· ≤ ·)] : IsTrans α (normalizedLE f) := by
  refine ⟨fun a b c h₁ h₂ => ?_⟩
  unfold normalizedLE at *
  exact IsTrans.trans (r := (· ≤ · : α → α → Prop)) (f a) (f b) (f c) h₁ h₂

/-- `List.insertionSort` with a `normalizedLE` relation produces a permutation that is
sorted by the underlying comparison `fun a b => f a ≤ f b`. -/
lemma insertionSort_normalizedLE_spec {α : Type u} [LE α] {f : α → α} [DecidableRel (normalizedLE f)]
    [IsTotal α (normalizedLE f)] [IsTrans α (normalizedLE f)] (l : List α) :
    List.Perm l (List.insertionSort (normalizedLE f) l) ∧
    List.Sorted (fun a b => f a ≤ f b) (List.insertionSort (normalizedLE f) l) := by
  have h_perm := (List.perm_insertionSort (normalizedLE f) l).symm
  have h_sorted := List.sorted_insertionSort (normalizedLE f) l
  exact And.intro h_perm h_sorted

/-! ### Three-way comparison with labels

`compareLabel a b gtLabel ltLabel eqLabel` returns one of three labels based on
the linear-order comparison of `a` and `b`:
- `gtLabel` when `a > b`
- `ltLabel` when `b > a` (i.e. `a < b`)
- `eqLabel` when `a = b`

This generalizes the sentiment-classification pattern `classifyByCount` where two
numeric counts are compared to choose "positive", "negative", or "neutral".
-/

/-- Compare two elements `a` and `b` in a `LinearOrder` and return one of three labels.
* `gtLabel` if `a > b`
* `ltLabel` if `b > a` (i.e. `a < b`)
* `eqLabel` if `a = b` -/
def compareLabel {α : Type u} [LinearOrder α] {β : Type v} (a b : α) (gtLabel ltLabel eqLabel : β) : β :=
  if a > b then gtLabel else if b > a then ltLabel else eqLabel

lemma compareLabel_of_gt {α : Type u} [LinearOrder α] {β : Type v} {a b : α}
    {gtLabel ltLabel eqLabel : β} (h : a > b) :
    compareLabel a b gtLabel ltLabel eqLabel = gtLabel := by
  unfold compareLabel; simp [h]

lemma compareLabel_of_lt {α : Type u} [LinearOrder α] {β : Type v} {a b : α}
    {gtLabel ltLabel eqLabel : β} (h₁ : ¬ a > b) (h₂ : b > a) :
    compareLabel a b gtLabel ltLabel eqLabel = ltLabel := by
  unfold compareLabel; simp [h₁, h₂]

lemma compareLabel_of_eq {α : Type u} [LinearOrder α] {β : Type v} {a b : α}
    {gtLabel ltLabel eqLabel : β} (h₁ : ¬ a > b) (h₂ : ¬ b > a) :
    compareLabel a b gtLabel ltLabel eqLabel = eqLabel := by
  unfold compareLabel; simp [h₁, h₂]

/-! ### `decide_ge_trans_on` / `decide_ge_total_on` — function-lifted `≥` transitivity/totality

These are the `≥` duals of `decide_le_trans_on` and `decide_le_total_on`. They provide
transitivity and totality of `decide (f a ≥ f b)` for any function `f : α → β` where `β`
has a `LinearOrder`. -/

/-- For types with a `LinearOrder` on the codomain, `decide` of `f a ≥ f b` is transitive
through a function `f`. This generalizes `decide_ge_trans` by comparing via a pre-transform. -/
lemma decide_ge_trans_on {α β : Type} [LinearOrder β] (f : α → β) (a b c : α) :
    decide (f a ≥ f b) = true → decide (f b ≥ f c) = true → decide (f a ≥ f c) = true := by
  intro h₁ h₂
  have h₁' : f a ≥ f b := by simpa using h₁
  have h₂' : f b ≥ f c := by simpa using h₂
  have h₃' : f a ≥ f c := le_trans h₂' h₁'
  simpa using h₃'

/-- For types with a `LinearOrder` on the codomain, `(decide (f a ≥ f b) || decide (f b ≥ f a))`
always holds (totality through a function `f`). This generalizes `decide_ge_total`. -/
lemma decide_ge_total_on {α β : Type} [LinearOrder β] (f : α → β) (a b : α) :
    (decide (f a ≥ f b) || decide (f b ≥ f a)) = true := by
  have h := le_total (f a) (f b)
  cases h with
  | inl hle => simp [hle]
  | inr hle => simp [hle]

/-! ### `head_max_of_pairwise_sorted` — head is maximum in a descending-sorted non-empty list -/

/-- In a non-empty list that is `Pairwise` sorted in descending value order by `f : α → β`,
the head has the maximum `f`-value. -/
lemma head_max_of_pairwise_sorted {α β : Type} [Preorder β] (f : α → β) (l : List α)
    (h_pairwise : List.Pairwise (fun a b => f a ≥ f b) l) (hne : l ≠ []) :
    ∀ x ∈ l, f (l.head hne) ≥ f x := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as =>
    rcases List.pairwise_cons.mp h_pairwise with ⟨h_all, _⟩
    intro x hx
    rcases List.mem_cons.mp hx with (rfl | hx')
    · exact le_refl _
    · exact h_all x hx'

/-! ### `byLengthThenLex` — lexicographic ordering by a length function then a secondary relation

`byLengthThenLex length le a b` compares `a` and `b` first by `length : α → Nat`
(ascending), then ties are broken by `le : α → α → Prop`. This is useful for sorting
tasks where elements are primarily ordered by some numeric "length" or "weight" function
and fall back to a secondary comparison when lengths are equal.

Together with the `IsTrans` and `IsTotal` instances, this relation is directly usable
with `List.insertionSort` and other sorting algorithms that require a total, transitive,
decidable relation. -/

/-- Order by a length function first (ascending), then by a secondary order for tie-breaking.
`byLengthThenLex length le a b` means `a` should come before `b` in the sorted output. -/
def byLengthThenLex (length : α → Nat) (le : α → α → Prop) (a b : α) : Prop :=
  length a < length b ∨ (length a = length b ∧ le a b)

/-- `byLengthThenLex` is decidable when its components are. -/
instance byLengthThenLex_decidable (length : α → Nat) (le : α → α → Prop)
    [DecidableRel le] (a b : α) : Decidable (byLengthThenLex length le a b) := by
  dsimp [byLengthThenLex]
  infer_instance

/-- `byLengthThenLex` is transitive when `le` is transitive. -/
theorem byLengthThenLex_trans (length : α → Nat) (le : α → α → Prop) [IsTrans α le]
    {a b c : α} (h_ab : byLengthThenLex length le a b) (h_bc : byLengthThenLex length le b c) :
    byLengthThenLex length le a c := by
  rcases h_ab with (h_lt | ⟨h_eq, h_le⟩)
  · rcases h_bc with (h_lt' | ⟨h_eq', h_le'⟩)
    · exact Or.inl (lt_trans h_lt h_lt')
    · rw [h_eq'] at h_lt
      exact Or.inl h_lt
  · rcases h_bc with (h_lt' | ⟨h_eq', h_le'⟩)
    · rw [← h_eq] at h_lt'
      exact Or.inl h_lt'
    · exact Or.inr ⟨h_eq.trans h_eq', IsTrans.trans (a := a) (b := b) (c := c) h_le h_le'⟩

/-- `byLengthThenLex` is total when `le` is total. -/
theorem byLengthThenLex_total (length : α → Nat) (le : α → α → Prop) [IsTotal α le]
    (a b : α) : byLengthThenLex length le a b ∨ byLengthThenLex length le b a := by
  dsimp [byLengthThenLex]
  by_cases h_len : length a < length b
  · exact Or.inl (Or.inl h_len)
  · have h_le_len : length b ≤ length a := by omega
    by_cases h_len' : length b < length a
    · exact Or.inr (Or.inl h_len')
    · have h_eq_len : length a = length b := by omega
      have h_cmp := IsTotal.total (r := le) a b
      rcases h_cmp with (h_le | h_le)
      · exact Or.inl (Or.inr ⟨h_eq_len, h_le⟩)
      · exact Or.inr (Or.inr ⟨h_eq_len.symm, h_le⟩)

/-- `byLengthThenLex` provides an `IsTrans` instance when `le` is transitive. -/
instance byLengthThenLex_isTrans (length : α → Nat) (le : α → α → Prop) [IsTrans α le] :
    IsTrans α (byLengthThenLex length le) :=
  ⟨fun _ _ _ => byLengthThenLex_trans length le⟩

/-- `byLengthThenLex` provides an `IsTotal` instance when `le` is total. -/
instance byLengthThenLex_isTotal (length : α → Nat) (le : α → α → Prop) [IsTotal α le] :
    IsTotal α (byLengthThenLex length le) :=
  ⟨fun a b => byLengthThenLex_total length le a b⟩


namespace CompareBy

/-! ### Compare elements by a function into `Nat` -/

/-- Compare two elements by a function into `Nat`; returns `true` iff `f a ≤ f b`.
    This is a `Bool`-valued comparator suitable for `List.mergeSort` and similar
    sorting/ordering operations. -/
def compareBy {α : Type} (f : α → Nat) (a b : α) : Bool :=
  decide (f a ≤ f b)

/-- `compareBy` is transitive: if `f a ≤ f b` and `f b ≤ f c`, then `f a ≤ f c`. -/
lemma trans {α : Type} (f : α → Nat) (a b c : α)
    (h1 : compareBy f a b = true) (h2 : compareBy f b c = true) : compareBy f a c = true := by
  dsimp [compareBy] at h1 h2 ⊢
  have h1' : f a ≤ f b := decide_eq_true_iff.mp h1
  have h2' : f b ≤ f c := decide_eq_true_iff.mp h2
  have h3 : f a ≤ f c := Nat.le_trans h1' h2'
  exact decide_eq_true_iff.mpr h3

/-- `compareBy` is total: for any `a, b`, either `compareBy f a b` or `compareBy f b a` holds. -/
lemma total {α : Type} (f : α → Nat) (a b : α) :
    (compareBy f a b || compareBy f b a) = true := by
  dsimp [compareBy]
  rcases Nat.le_total (f a) (f b) with (h | h)
  · simp [decide_eq_true_iff.mpr h]
  · simp [decide_eq_true_iff.mpr h]

/-- `mergeSort` with `compareBy f` produces a list that is `Pairwise` ordered by `compareBy`. -/
lemma mergeSort_sorted {α : Type} (f : α → Nat) (l : List α) :
    List.Pairwise (fun a b => compareBy f a b = true) (List.mergeSort l (compareBy f)) :=
  List.sorted_mergeSort (trans f) (total f) l

/-- `mergeSort` with `compareBy f` produces a list that is `Pairwise` ordered by
    the propositional `f a ≤ f b`. This is the `Prop`-valued version of
    `mergeSort_sorted`, useful when reasoning directly about the natural-number
    ordering of the projected values. -/
lemma mergeSort_pairwise_le {α : Type} (f : α → Nat) (l : List α) :
    List.Pairwise (fun a b => f a ≤ f b) (List.mergeSort l (compareBy f)) := by
  have h := mergeSort_sorted f l
  apply h.imp
  intro a b hb
  have hle : f a ≤ f b := of_decide_eq_true (by simpa [compareBy] using hb)
  exact hle

/-- If a list is `Pairwise` ordered by `compareBy f`, then `f` of the `i`-th element is
    ≤ `f` of the `j`-th element whenever `i < j`. -/
lemma pairwise_get {α : Type} (f : α → Nat) (L : List α)
    (h_pairwise : List.Pairwise (fun a b => compareBy f a b = true) L)
    (i j : Nat) (hij : i < j) (hi : i < L.length) (hj : j < L.length) :
    f (L.get ⟨i, hi⟩) ≤ f (L.get ⟨j, hj⟩) := by
  have h_pairwise_get := (List.pairwise_iff_get (R := fun a b => compareBy f a b = true)).mp h_pairwise
  have hfin : (⟨i, hi⟩ : Fin L.length) < (⟨j, hj⟩ : Fin L.length) := hij
  have hR := h_pairwise_get _ _ hfin
  dsimp [compareBy] at hR
  exact decide_eq_true_iff.mp hR

/-- Lexicographic `Bool` comparator: first compare by a natural-number score projection,
    then by a tiebreak relation when scores are equal. -/
def lexOrd {α : Type} (score : α → Nat) (tiebreak : α → α → Bool) (a b : α) : Bool :=
  (score a < score b) || ((score a = score b) && (tiebreak a b))

/-! ### `lexOrdDesc` — descending by a `Nat` measure, then by a custom tiebreak

This is the descending counterpart of `lexOrd`. Where `lexOrd` uses `score a < score b`
(ascending by score), `lexOrdDesc` uses `cnt a > cnt b` (descending by count/measure).
Both accept a custom `Bool`-valued tiebreak for when the measures are equal.

For example, `lexOrdDesc List.count (· ≤ ·)` sorts strings by descending frequency
with ascending lexicographic tie-breaking for equal frequencies. -/

/-- Compare by a `Nat` measure in descending order first, then by a custom `Bool`-valued
tiebreak relation. `lexOrdDesc cnt tiebreak a b` returns `true` iff `cnt a > cnt b`,
or `cnt a = cnt b` and `tiebreak a b = true`.

This is the descending counterpart of `lexOrd`. For the common case where the tiebreak
is the intrinsic `≤` on a `LinearOrder`, use `compareByDescMeasure`. -/
def lexOrdDesc {α : Type u} (cnt : α → Nat) (tiebreak : α → α → Bool) (a b : α) : Bool :=
  cnt a > cnt b || (cnt a = cnt b && tiebreak a b)

/-- `lexOrdDesc` is transitive when the underlying tiebreak relation is transitive.
If `cnt a >= cnt b >= cnt c` according to `lexOrdDesc`, then `cnt a >= cnt c`. -/
lemma lexOrdDesc_trans {α : Type u} (cnt : α → Nat) (tiebreak : α → α → Bool)
    (h_trans : ∀ a b c, tiebreak a b = true → tiebreak b c = true → tiebreak a c = true)
    (a b c : α) (h1 : lexOrdDesc cnt tiebreak a b = true) (h2 : lexOrdDesc cnt tiebreak b c = true) :
    lexOrdDesc cnt tiebreak a c = true := by
  unfold lexOrdDesc at h1 h2 ⊢
  simp at h1 h2
  rcases h1 with (h1 | ⟨h1eq, h1le⟩)
  · rcases h2 with (h2 | ⟨h2eq, h2le⟩)
    · simp; left; exact Nat.lt_trans h2 h1
    · simp; left
      calc
        cnt c = cnt b := h2eq.symm
        _ < cnt a := h1
  · rcases h2 with (h2 | ⟨h2eq, h2le⟩)
    · simp; left
      calc
        cnt c < cnt b := h2
        _ = cnt a := h1eq.symm
    · simp; right
      have heq : cnt a = cnt c := h1eq.trans h2eq
      have hle : tiebreak a c = true := h_trans a b c h1le h2le
      exact ⟨heq, hle⟩

/-- `lexOrdDesc` is total when the underlying tiebreak relation is total.
For any `a, b`, either `lexOrdDesc cnt tiebreak a b` or `lexOrdDesc cnt tiebreak b a` holds. -/
lemma lexOrdDesc_total {α : Type u} (cnt : α → Nat) (tiebreak : α → α → Bool)
    (h_total : ∀ a b, (tiebreak a b || tiebreak b a) = true)
    (a b : α) : (lexOrdDesc cnt tiebreak a b || lexOrdDesc cnt tiebreak b a) = true := by
  unfold lexOrdDesc
  by_cases h : cnt a > cnt b
  · simp [h]
  · have hle_cnt : cnt a ≤ cnt b := Nat.le_of_not_gt h
    rcases Nat.lt_or_eq_of_le hle_cnt with (hlt | heq)
    · simp [hlt]
    · have htotal' : tiebreak a b = true ∨ tiebreak b a = true :=
        (Bool.or_eq_true _ _).mp (h_total a b)
      rcases htotal' with (htieab | htieba)
      · simp [heq, htieab]
      · simp [heq, htieba]

/-! ### `BetterBy` — `Prop` relation comparing by score with linear-order tiebreak

This is the `Prop` counterpart of `lexOrd`, useful for specification and correctness proofs.
Instead of a custom `Bool` tiebreak function, it uses the inherent `≤` from `LinearOrder α`. -/

section BetterBy

variable {α : Type u} [LinearOrder α]

/-- `BetterBy score x y` means `x` is at least as good as `y` according to the score `score`.
    Either `score x` is strictly better (smaller), or scores are equal and `x ≤ y` (tiebreak). -/
def BetterBy (score : α → ℕ) (x y : α) : Prop :=
  (score x < score y) ∨ (score x = score y ∧ x ≤ y)

namespace BetterBy

lemma trans (score : α → ℕ) (x y z : α)
    (hxy : BetterBy score x y) (hyz : BetterBy score y z) :
    BetterBy score x z := by
  unfold BetterBy at hxy hyz ⊢
  rcases hxy with (hxy_lt | ⟨hxy_eq, hxy_le⟩)
  · rcases hyz with (hyz_lt | ⟨hyz_eq, hyz_le⟩)
    · left; exact lt_trans hxy_lt hyz_lt
    · left; exact lt_of_lt_of_eq hxy_lt hyz_eq
  · rcases hyz with (hyz_lt | ⟨hyz_eq, hyz_le⟩)
    · left; exact lt_of_eq_of_lt hxy_eq hyz_lt
    · right; exact ⟨hxy_eq.trans hyz_eq, le_trans hxy_le hyz_le⟩

end BetterBy

end BetterBy

/-! ### `cmpByMeasureThenLex` — `Prop` relation first comparing by a `Nat` measure, then by intrinsic `≤`

This generalizes `BetterBy` by only requiring `LE α` with separate `IsTrans`/`IsTotal`
instances rather than a full `LinearOrder α`. It provides `DecidableRel`, `IsTrans`, and
`IsTotal` typeclass instances, making it suitable for `List.insertionSort`, `List.Sorted`,
and similar APIs. -/

/-- Compare by a `Nat` measure first, then by the intrinsic `≤`.
`cmpByMeasureThenLex m a b` holds iff `m a < m b`, or `m a = m b` and `a ≤ b`. -/
def cmpByMeasureThenLex {α : Type u} (m : α → Nat) [LE α] (a b : α) : Prop :=
  m a < m b ∨ (m a = m b ∧ a ≤ b)

/-- Decidable instance for `cmpByMeasureThenLex`. -/
instance instDecidableRelCmpByMeasureThenLex {α : Type u} [LE α] [DecidableEq α]
    [DecidableRel (· ≤ · : α → α → Prop)] (m : α → Nat) :
    DecidableRel (cmpByMeasureThenLex m) := by
  intro a b
  unfold cmpByMeasureThenLex
  infer_instance

/-- `IsTrans` instance: `cmpByMeasureThenLex` is transitive when the underlying `≤` is transitive. -/
instance instIsTransCmpByMeasureThenLex {α : Type u} (m : α → Nat) [LE α] [IsTrans α (· ≤ ·)] :
    IsTrans α (cmpByMeasureThenLex m) := by
  refine ⟨fun {a b c} h1 h2 => ?_⟩
  unfold cmpByMeasureThenLex at h1 h2 ⊢
  rcases h1 with (h1 | ⟨hlen1, hle1⟩)
  · rcases h2 with (h2 | ⟨hlen2, hle2⟩)
    · exact Or.inl (Nat.lt_trans h1 h2)
    · have hlt : m a < m c := by
        rw [← hlen2]
        exact h1
      exact Or.inl hlt
  · rcases h2 with (h2 | ⟨hlen2, hle2⟩)
    · have hlt : m a < m c := by
        rw [hlen1]
        exact h2
      exact Or.inl hlt
    · exact Or.inr ⟨by rw [hlen1, hlen2], IsTrans.trans a b c hle1 hle2⟩

/-- `IsTotal` instance: `cmpByMeasureThenLex` is total when the underlying `≤` is total. -/
instance instIsTotalCmpByMeasureThenLex {α : Type u} (m : α → Nat) [LE α] [IsTotal α (· ≤ ·)] :
    IsTotal α (cmpByMeasureThenLex m) := by
  refine ⟨fun a b => ?_⟩
  unfold cmpByMeasureThenLex
  by_cases hlt : m a < m b
  · exact Or.inl (Or.inl hlt)
  · have hlen_le : m b ≤ m a := Nat.le_of_not_gt hlt
    by_cases hgt : m b < m a
    · exact Or.inr (Or.inl hgt)
    · have hlen_eq : m a = m b := Nat.le_antisymm (Nat.le_of_not_gt hgt) hlen_le
      rcases IsTotal.total (r := (· ≤ ·)) a b with (hle | hle)
      · exact Or.inl (Or.inr ⟨hlen_eq, hle⟩)
      · exact Or.inr (Or.inr ⟨hlen_eq.symm, hle⟩)

/-! ### `descByMeasureThenLex` — descending by a `Nat` measure, then ascending lexicographically

This is the descending analog of `cmpByMeasureThenLex`: order by a `Nat` measure
in *descending* order, with ascending lexicographic tie-breaking via `≤`.
`descByMeasureThenLex f a b` holds iff `f a > f b` or (`f a = f b` and `a ≤ b`).

Commonly used for sorting by frequency: higher frequency comes first, with
lexicographic ordering as tiebreaker for equal frequencies. -/

/-- Compare by a `Nat` measure in descending order first, then by the intrinsic `≤`.
`descByMeasureThenLex f a b` holds iff `f a > f b`, or `f a = f b` and `a ≤ b`.

When `f` is a frequency function, this says "a precedes b if a occurs more often,
or if they occur equally often but a is lexicographically first". -/
def descByMeasureThenLex {α : Type u} [LinearOrder α] (f : α → Nat) (a b : α) : Prop :=
  (f a > f b) ∨ ((f a = f b) ∧ a ≤ b)

/-- `Decidable` instance for `descByMeasureThenLex`. -/
def descByMeasureThenLex.dec {α : Type u} [LinearOrder α] (f : α → Nat) (a b : α) :
    Decidable (descByMeasureThenLex f a b) := by
  unfold descByMeasureThenLex; infer_instance

/-- `Std.Total` instance: `descByMeasureThenLex f` is total. -/
def descByMeasureThenLex.total {α : Type u} [LinearOrder α] (f : α → Nat) :
    Std.Total (descByMeasureThenLex f) where
  total a b := by
    unfold descByMeasureThenLex
    by_cases hgt : f a > f b
    · exact Or.inl (Or.inl hgt)
    · by_cases hlt : f b > f a
      · exact Or.inr (Or.inl hlt)
      · have heq : f a = f b := by omega
        have hle_or : a ≤ b ∨ b ≤ a := le_total a b
        rcases hle_or with (hle | hle)
        · exact Or.inl (Or.inr ⟨heq, hle⟩)
        · exact Or.inr (Or.inr ⟨heq.symm, hle⟩)

/-- `IsTrans` instance: `descByMeasureThenLex f` is transitive. -/
def descByMeasureThenLex.trans {α : Type u} [LinearOrder α] (f : α → Nat) :
    IsTrans α (descByMeasureThenLex f) where
  trans a b c h1 h2 := by
    unfold descByMeasureThenLex at h1 h2 ⊢
    rcases h1 with (h1 | ⟨heq1, hle1⟩)
    · rcases h2 with (h2 | ⟨heq2, hle2⟩)
      · have h : f a > f c := by
          calc
            f c < f b := h2
            _ < f a := h1
        exact Or.inl h
      · have h : f a > f c := by
          calc
            f c = f b := heq2.symm
            _ < f a := h1
        exact Or.inl h
    · rcases h2 with (h2 | ⟨heq2, hle2⟩)
      · have h : f a > f c := by
          calc
            f c < f b := h2
            _ = f a := heq1.symm
        exact Or.inl h
      · exact Or.inr ⟨heq1.trans heq2, le_trans hle1 hle2⟩

/-- `Std.Antisymm` instance: `descByMeasureThenLex f` is antisymmetric. -/
def descByMeasureThenLex.antisymm {α : Type u} [LinearOrder α] (f : α → Nat) :
    Std.Antisymm (descByMeasureThenLex f) where
  antisymm a b h1 h2 := by
    unfold descByMeasureThenLex at h1 h2
    rcases h1 with (h1 | ⟨heq1, hle1⟩)
    · rcases h2 with (h2 | ⟨heq2, hle2⟩)
      · exact absurd (lt_trans h1 h2) (lt_irrefl _)
      · rw [heq2] at h1; exact absurd h1 (lt_irrefl _)
    · rcases h2 with (h2 | ⟨heq2, hle2⟩)
      · rw [heq1] at h2; exact absurd h2 (lt_irrefl _)
      · exact le_antisymm hle1 hle2

/-- `IsTotal` instance for `descByMeasureThenLex f`. -/
def descByMeasureThenLex.isTotal {α : Type u} [LinearOrder α] (f : α → Nat) :
    IsTotal α (descByMeasureThenLex f) where
  total a b := (descByMeasureThenLex.total f).total a b

/-- `IsAntisymm` instance for `descByMeasureThenLex f`. -/
def descByMeasureThenLex.isAntisymm {α : Type u} [LinearOrder α] (f : α → Nat) :
    IsAntisymm α (descByMeasureThenLex f) where
  antisymm a b h1 h2 := (descByMeasureThenLex.antisymm f).antisymm a b h1 h2

/-- Given a `Nodup` list `l` that is `Pairwise` ordered by `descByMeasureThenLex f`,
for any two indices `i < j` (as `Nat` with bounds), the ordering relation
simplifies to either `f` strictly decreasing, or equal-`f` with strict
lexicographic tie-breaking. -/
lemma descByMeasureThenLex.pairwise_nodup_get_ordering {α : Type u} [LinearOrder α] (f : α → Nat)
    (l : List α) (hnodup : l.Nodup) (hpair : List.Pairwise (descByMeasureThenLex f) l)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (f (l.get ⟨i, hi⟩) > f (l.get ⟨j, hj⟩)) ∨
      ((f (l.get ⟨i, hi⟩) = f (l.get ⟨j, hj⟩)) ∧ l.get ⟨i, hi⟩ < l.get ⟨j, hj⟩) := by
  let fi : Fin l.length := ⟨i, hi⟩
  let fj : Fin l.length := ⟨j, hj⟩
  have hfin_lt : fi < fj := hij
  have h := (List.pairwise_iff_get (R := descByMeasureThenLex f) (l := l)).mp hpair fi fj hfin_lt
  unfold descByMeasureThenLex at h
  rcases h with (hrel | ⟨heq, hle⟩)
  · exact Or.inl hrel
  · have hne : l.get fi ≠ l.get fj := by
      intro hget_eq
      have hfin_eq : fi = fj := (hnodup.get_inj_iff).mp hget_eq
      have hval_eq : i = j := congrArg Fin.val hfin_eq
      exact Nat.ne_of_lt hij hval_eq
    have hlt : l.get fi < l.get fj := Ne.lt_of_le hne hle
    exact Or.inr ⟨heq, hlt⟩

/-- If a list is `Pairwise` ordered by `descByMeasureThenLex f`, then for any indices
`i < j` in bounds, either `f` strictly decreases or the `f`-values are equal and the
elements are `≤`-ordered. This is the simpler version of `pairwise_nodup_get_ordering`
that does not require `Nodup` and uses `≤` (instead of `<`) for equal-measure tie-breaking. -/
lemma descByMeasureThenLex.pairwise_getElem_ordering {α : Type u} [LinearOrder α] (f : α → Nat)
    (l : List α) (hpair : List.Pairwise (descByMeasureThenLex f) l)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (f (l.get ⟨i, hi⟩) > f (l.get ⟨j, hj⟩)) ∨
      ((f (l.get ⟨i, hi⟩) = f (l.get ⟨j, hj⟩)) ∧ l.get ⟨i, hi⟩ ≤ l.get ⟨j, hj⟩) := by
  have h_rel := (List.pairwise_iff_get.mp hpair) ⟨i, hi⟩ ⟨j, hj⟩ hij
  unfold descByMeasureThenLex at h_rel
  rcases h_rel with (h_gt | ⟨h_eq, h_le⟩)
  · left; exact h_gt
  · right; exact ⟨h_eq, h_le⟩

/-! ### `compareByDescMeasure` — `Bool` comparator: descending by a `Nat` measure, then ascending by element `≤`

This is the `Bool`-valued counterpart of `descByMeasureThenLex`. It is suitable for
`List.mergeSort` and other boolean-comparator APIs.

`compareByDescMeasure f a b = true` iff `f a > f b`, or `f a = f b` and `a ≤ b`. -/

/-- Compare two elements by a `Nat` measure in descending order first, then by the intrinsic `≤`.
Returns `true` iff `measure a > measure b`, or `measure a = measure b` and `a ≤ b`.

This is a `Bool`-valued comparator suitable for `List.mergeSort` and other
sorting APIs. -/
def compareByDescMeasure {α : Type u} (measure : α → Nat) [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) : Bool :=
  if measure a > measure b then true
  else if measure b > measure a then false
  else decide (a ≤ b)

/-- `compareByDescMeasure measure a b = true` iff `measure a > measure b`, or
`measure a = measure b` and `a ≤ b`. -/
lemma compareByDescMeasure_eq_true_iff {α : Type u} (measure : α → Nat) [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :
    compareByDescMeasure measure a b = true ↔ (measure a > measure b) ∨ (measure a = measure b ∧ a ≤ b) := by
  unfold compareByDescMeasure
  by_cases h : measure a > measure b
  · simp [h]
  · by_cases h' : measure b > measure a
    · have hne : measure a ≠ measure b := by
        intro heq; apply h; omega
      simp [h, h', hne]
    · have h_eq : measure a = measure b := by omega
      simp [h, h', h_eq, decide_eq_true_iff]

/-- `compareByDescMeasure` is transitive: if `measure a` beats `measure b` and `measure b` beats
`measure c` according to `compareByDescMeasure`, then `measure a` beats `measure c`. -/
lemma compareByDescMeasure_trans {α : Type u} (measure : α → Nat) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b c : α) :
    compareByDescMeasure measure a b = true → compareByDescMeasure measure b c = true → compareByDescMeasure measure a c = true := by
  intro h1 h2
  have h1' := (compareByDescMeasure_eq_true_iff measure a b).mp h1
  have h2' := (compareByDescMeasure_eq_true_iff measure b c).mp h2
  rcases h1' with (h1_len | ⟨h1_eq, h1_le⟩)
  · rcases h2' with (h2_len | ⟨h2_eq, h2_le⟩)
    · have h_ac : measure a > measure c := Nat.lt_trans h2_len h1_len
      exact (compareByDescMeasure_eq_true_iff measure a c).mpr (Or.inl h_ac)
    · have h_ac : measure a > measure c := by
        rw [h2_eq] at h1_len
        exact h1_len
      exact (compareByDescMeasure_eq_true_iff measure a c).mpr (Or.inl h_ac)
  · rcases h2' with (h2_len | ⟨h2_eq, h2_le⟩)
    · have h_ac : measure a > measure c := by
        rw [← h1_eq] at h2_len
        exact h2_len
      exact (compareByDescMeasure_eq_true_iff measure a c).mpr (Or.inl h_ac)
    · have h_ac_eq : measure a = measure c := Eq.trans h1_eq h2_eq
      have h_ac_le : a ≤ c := le_trans h1_le h2_le
      exact (compareByDescMeasure_eq_true_iff measure a c).mpr (Or.inr ⟨h_ac_eq, h_ac_le⟩)

/-- `compareByDescMeasure` is total: for any `a, b`, either `compareByDescMeasure measure a b` or
`compareByDescMeasure measure b a` holds. -/
lemma compareByDescMeasure_total {α : Type u} [LinearOrder α] (measure : α → Nat) (a b : α) :
    (compareByDescMeasure measure a b || compareByDescMeasure measure b a) = true := by
  by_cases hlen : measure a > measure b
  · have htrue : compareByDescMeasure measure a b = true := (compareByDescMeasure_eq_true_iff measure a b).mpr (Or.inl hlen)
    simp [htrue]
  · by_cases hlen' : measure b > measure a
    · have htrue : compareByDescMeasure measure b a = true := (compareByDescMeasure_eq_true_iff measure b a).mpr (Or.inl hlen')
      simp [htrue]
    · have h_eq : measure a = measure b := by omega
      by_cases hle : a ≤ b
      · have htrue : compareByDescMeasure measure a b = true := (compareByDescMeasure_eq_true_iff measure a b).mpr (Or.inr ⟨h_eq, hle⟩)
        simp [htrue]
      · have hle' : b ≤ a := by
          have hlt : a > b := lt_of_not_ge hle
          exact le_of_lt hlt
        have htrue : compareByDescMeasure measure b a = true := (compareByDescMeasure_eq_true_iff measure b a).mpr (Or.inr ⟨h_eq.symm, hle'⟩)
        simp [htrue]

/-! ### `sortByWeight` — sort by a `Nat` weight in descending order

`sortByWeight w xs` sorts `xs` by the projection `w` in descending order (higher weight first),
with ties broken by the natural order `≤`. This is a convenience wrapper around
`xs.mergeSort (compareByDescMeasure w)`. -/

/-- Sort a list by a `Nat` weight function in descending order (higher weight first),
with ties broken by the natural order `≤`. -/
def sortByWeight {α : Type _} [LinearOrder α] (w : α → Nat) (xs : List α) : List α :=
  xs.mergeSort (compareByDescMeasure w)

/-! ### `compareByDesc` — compare elements by a `Nat` projection in descending order

This is the dual of `compareBy`: instead of checking `f a ≤ f b`, it checks `f a ≥ f b`.
Used when sorting by descending score, e.g., sorting `α × Nat` pairs by the second component.

`compareByDesc f a b = decide (f a ≥ f b)`. -/

/-- Compare two elements by a `Nat` projection in descending order.
Returns `true` iff `f a ≥ f b`. Suitable for `List.mergeSort` and similar operations
that require a descending comparator. -/
def compareByDesc {α : Type} (f : α → Nat) (a b : α) : Bool :=
  decide (f a ≥ f b)

/-- `compareByDesc` is transitive: if `f a ≥ f b` and `f b ≥ f c`, then `f a ≥ f c`. -/
lemma desc_trans {α : Type} (f : α → Nat) (a b c : α)
    (h1 : compareByDesc f a b = true) (h2 : compareByDesc f b c = true) : compareByDesc f a c = true := by
  dsimp [compareByDesc] at h1 h2 ⊢
  have h1' : f b ≤ f a := of_decide_eq_true h1
  have h2' : f c ≤ f b := of_decide_eq_true h2
  have h3' : f c ≤ f a := Nat.le_trans h2' h1'
  exact decide_eq_true h3'

/-- `compareByDesc` is total: for any `a, b`, either `compareByDesc f a b` or `compareByDesc f b a` holds. -/
lemma desc_total {α : Type} (f : α → Nat) (a b : α) :
    (compareByDesc f a b || compareByDesc f b a) = true := by
  dsimp [compareByDesc]
  rcases Nat.le_total (f b) (f a) with (h | h)
  · simp [decide_eq_true_iff.mpr h]
  · simp [decide_eq_true_iff.mpr h]

/-- `mergeSort` with `compareByDesc f` produces a list that is `Pairwise` ordered by `compareByDesc f`. -/
lemma desc_mergeSort_sorted {α : Type} (f : α → Nat) (l : List α) :
    List.Pairwise (fun a b => compareByDesc f a b = true) (List.mergeSort l (compareByDesc f)) :=
  List.sorted_mergeSort (desc_trans f) (desc_total f) l

/-- If a list is `Pairwise` ordered by `compareByDesc f`, then `f` of the `i`-th element is
    ≥ `f` of the `j`-th element whenever `i < j`. -/
lemma desc_pairwise_get {α : Type} (f : α → Nat) (L : List α)
    (h_pairwise : List.Pairwise (fun a b => compareByDesc f a b = true) L)
    (i j : Nat) (hij : i < j) (hi : i < L.length) (hj : j < L.length) :
    f (L.get ⟨i, hi⟩) ≥ f (L.get ⟨j, hj⟩) := by
  have h_pairwise_get := (List.pairwise_iff_get (R := fun a b => compareByDesc f a b = true)).mp h_pairwise
  have hfin : (⟨i, hi⟩ : Fin L.length) < (⟨j, hj⟩ : Fin L.length) := hij
  have hR := h_pairwise_get _ _ hfin
  dsimp [compareByDesc] at hR
  exact of_decide_eq_true hR

/-! ### `desc` — `Prop`-valued descending comparator by a `Nat` projection

This is the `Prop` counterpart of `compareByDesc`. While `compareByDesc` is a `Bool` comparator
for `List.mergeSort`, `desc` is a `Prop` relation with `DecidableRel`, `IsTrans`, and `IsTotal`
instances, making it suitable for `List.insertionSort` and `List.Sorted`.

For example, `desc Prod.snd` compares `α × Nat` pairs by their second component in descending
order, analogous to `compareByDesc Prod.snd`. -/

/-- `desc f a b` holds iff `f a ≥ f b`. A `Prop`-valued descending comparator,
suitable for `List.insertionSort` and `List.Sorted`. -/
def desc {α : Type u} (f : α → Nat) (a b : α) : Prop := f a ≥ f b

instance instDecidableRelDesc {α : Type u} (f : α → Nat) : DecidableRel (desc f) :=
  λ a b => by
    dsimp [desc]
    infer_instance

instance instIsTransDesc {α : Type u} (f : α → Nat) : IsTrans α (desc f) where
  trans a b c h₁ h₂ := by
    dsimp [desc] at h₁ h₂ ⊢
    exact Nat.le_trans h₂ h₁

instance instIsTotalDesc {α : Type u} (f : α → Nat) : IsTotal α (desc f) where
  total a b := by
    dsimp [desc]
    rcases Nat.le_total (f a) (f b) with (h | h)
    · right; exact h
    · left; exact h

/-- If a list `l` is `List.Sorted` by `desc f`, then for any indices `i < j` (as `Fin l.length`),
the projected values satisfy `f (l.get i) ≥ f (l.get j)`. -/
lemma sorted_desc_get_ge {α : Type u} (f : α → Nat) (l : List α)
    (h_sorted : List.Sorted (desc f) l) {i j : Fin l.length} (hij : i < j) :
    f (l.get i) ≥ f (l.get j) := by
  have h_get_rel : desc f (l.get i) (l.get j) :=
    h_sorted.rel_get_of_lt (a := i) (b := j) hij
  simpa [desc] using h_get_rel

/-! ### `relDescThenAsc` — descending by a projection, then ascending by element

This generalizes `descByMeasureThenLex`: instead of fixing the target to `Nat`,
it is parameterized by both `α` (element type) and `β` (projection type).
`relDescThenAsc f a b` holds iff `f a > f b`, or `f a = f b` and `a ≤ b`.

Use this for sorting where elements are compared by some projection in
descending order, with the elements themselves providing ascending tie-breaking.

When `β := Nat`, this specializes to `descByMeasureThenLex`. -/

/-- Compare by a projection `f : α → β` in descending order first, then by the intrinsic `≤` on `α`.
`relDescThenAsc f a b` holds iff `f a > f b`, or `f a = f b` and `a ≤ b`. -/
def relDescThenAsc {α β : Type} [LT β] [DecidableEq β] [LE α] (f : α → β) (a b : α) : Prop :=
  f a > f b ∨ (f a = f b ∧ a ≤ b)

/-- `DecidableRel` instance for `relDescThenAsc f` when both `α` and `β` have `LinearOrder`. -/
instance instDecidableRelRelDescThenAsc {α β : Type} [LinearOrder β] [LinearOrder α] (f : α → β) :
    DecidableRel (relDescThenAsc f) := by
  intro a b
  unfold relDescThenAsc
  infer_instance

/-- `IsTrans` instance: `relDescThenAsc f` is transitive when `α` and `β` have `LinearOrder`. -/
instance instIsTransRelDescThenAsc {α β : Type} [LinearOrder β] [LinearOrder α] (f : α → β) :
    IsTrans α (relDescThenAsc f) := by
  refine ⟨fun a b c h1 h2 => ?_⟩
  unfold relDescThenAsc at h1 h2 ⊢
  rcases h1 with (h1 | ⟨heq1, hle1⟩)
  · rcases h2 with (h2 | ⟨heq2, hle2⟩)
    · have : f a > f c := lt_trans h2 h1
      exact Or.inl this
    · rw [heq2] at h1
      exact Or.inl h1
  · rcases h2 with (h2 | ⟨heq2, hle2⟩)
    · rw [heq1]
      exact Or.inl h2
    · have heq : f a = f c := by
        rw [heq1, heq2]
      have hle : a ≤ c := le_trans hle1 hle2
      exact Or.inr ⟨heq, hle⟩

/-- `IsTotal` instance: `relDescThenAsc f` is total when `α` and `β` have `LinearOrder`. -/
instance instIsTotalRelDescThenAsc {α β : Type} [LinearOrder β] [LinearOrder α] (f : α → β) :
    IsTotal α (relDescThenAsc f) := by
  refine ⟨fun a b => ?_⟩
  unfold relDescThenAsc
  by_cases h : f a > f b
  · exact Or.inl (Or.inl h)
  · have hle : f b ≥ f a := le_of_not_gt h
    by_cases heq : f a = f b
    · have hle_or : a ≤ b ∨ b ≤ a := le_total a b
      rcases hle_or with (hle' | hle')
      · exact Or.inl (Or.inr ⟨heq, hle'⟩)
      · exact Or.inr (Or.inr ⟨heq.symm, hle'⟩)
    · have hlt : f b > f a := lt_of_le_of_ne hle heq
      exact Or.inr (Or.inl hlt)

/-- If a list is `Sorted` by `relDescThenAsc f`, then for any indices `i < j` within bounds,
the elements at those positions satisfy the descending-`f`-then-ascending-element property
(via `getD`). -/
theorem sorted_relDescThenAsc_implies_get_property {α β : Type} [LinearOrder β] [LinearOrder α]
    (f : α → β) (l : List α) (a0 : α)
    (h_sorted : List.Sorted (relDescThenAsc f) l) :
    ∀ i j : Nat,
      i < j →
      i < l.length →
      j < l.length →
        (f (l.getD i a0) > f (l.getD j a0)) ∨
        (f (l.getD i a0) = f (l.getD j a0) ∧ l.getD i a0 ≤ l.getD j a0) := by
  intro i j hlt hi hj
  have h_pairwise := (List.pairwise_iff_get.mp h_sorted)
  let fi : Fin l.length := ⟨i, hi⟩
  let fj : Fin l.length := ⟨j, hj⟩
  have h_rel : relDescThenAsc f (l.get fi) (l.get fj) := h_pairwise fi fj hlt
  unfold relDescThenAsc at h_rel
  rcases h_rel with (h | ⟨heq, hle⟩)
  · left
    have h_get_i : l.getD i a0 = l.get fi := by
      simpa [fi] using List.getD_eq_getElem l a0 hi
    have h_get_j : l.getD j a0 = l.get fj := by
      simpa [fj] using List.getD_eq_getElem l a0 hj
    rw [h_get_i, h_get_j]
    exact h
  · right
    have h_get_i : l.getD i a0 = l.get fi := by
      simpa [fi] using List.getD_eq_getElem l a0 hi
    have h_get_j : l.getD j a0 = l.get fj := by
      simpa [fj] using List.getD_eq_getElem l a0 hj
    rw [h_get_i, h_get_j]
    exact ⟨heq, hle⟩

/-! ### `lexMeasureRel` — ascending by a measure, then ascending by element

This is the ascending analog of `relDescThenAsc`: instead of descending by the
projection, it orders by the projection in *ascending* order, with ascending
lexicographic tie-breaking via `≤`.

`lexMeasureRel m a b` holds iff `m a < m b`, or `m a = m b` and `a ≤ b`.

Use this for sorting where elements are compared by some projection in
ascending order, with the elements themselves providing ascending tie-breaking.

When `β := Nat`, this specializes to `cmpByMeasureThenLex`. -/

/-- Compare by a projection `m : α → β` in ascending order first, then by the intrinsic `≤` on `α`.
`lexMeasureRel m a b` holds iff `m a < m b`, or `m a = m b` and `a ≤ b`. -/
def lexMeasureRel {α β : Type} [LinearOrder β] [LinearOrder α] (m : α → β) (a b : α) : Prop :=
  m a < m b ∨ (m a = m b ∧ a ≤ b)

/-- `DecidableRel` instance for `lexMeasureRel m`. -/
instance instDecidableRelLexMeasureRel {α β : Type} [LinearOrder β] [LinearOrder α] (m : α → β) :
    DecidableRel (lexMeasureRel m) := by
  intro a b
  unfold lexMeasureRel
  infer_instance

/-- `IsTrans` instance: `lexMeasureRel m` is transitive. -/
instance instIsTransLexMeasureRel {α β : Type} [LinearOrder β] [LinearOrder α] (m : α → β) :
    IsTrans α (lexMeasureRel m) := by
  refine ⟨fun a b c h1 h2 => ?_⟩
  unfold lexMeasureRel at h1 h2 ⊢
  rcases h1 with (h1 | ⟨heq1, hle1⟩)
  · rcases h2 with (h2 | ⟨heq2, hle2⟩)
    · exact Or.inl (lt_trans h1 h2)
    · rw [heq2] at h1
      exact Or.inl h1
  · rcases h2 with (h2 | ⟨heq2, hle2⟩)
    · rw [← heq1] at h2
      exact Or.inl h2
    · exact Or.inr ⟨heq1.trans heq2, le_trans hle1 hle2⟩

/-- `IsTotal` instance: `lexMeasureRel m` is total. -/
instance instIsTotalLexMeasureRel {α β : Type} [LinearOrder β] [LinearOrder α] (m : α → β) :
    IsTotal α (lexMeasureRel m) := by
  refine ⟨fun a b => ?_⟩
  unfold lexMeasureRel
  by_cases h : m a < m b
  · exact Or.inl (Or.inl h)
  · have h' : m b ≤ m a := le_of_not_gt h
    rcases lt_or_eq_of_le h' with (hlt | heq)
    · exact Or.inr (Or.inl hlt)
    · rcases le_total a b with (hle | hle)
      · exact Or.inl (Or.inr ⟨heq.symm, hle⟩)
      · exact Or.inr (Or.inr ⟨heq, hle⟩)

/-! ### Three-way comparison labeling -/

/-- Compare two natural numbers and return one of three labels:
- `pos` if `a > b`
- `neg` if `a < b`
- `neu` if `a = b`

This is a three-way comparison combinator useful for classifying numeric comparisons
(sentiment analysis, score-based classification, etc.). -/
def labelByComparison {α : Type u} (pos neg neu : α) (a b : Nat) : α :=
  if a > b then pos
  else if a < b then neg
  else neu

/-- Specification of `labelByComparison`: the result is exactly one of the three labels
paired with the corresponding comparison condition. -/
lemma labelByComparison_spec {α : Type u} (pos neg neu : α) (a b : Nat) :
    (labelByComparison pos neg neu a b = pos ∧ a > b) ∨
    (labelByComparison pos neg neu a b = neg ∧ a < b) ∨
    (labelByComparison pos neg neu a b = neu ∧ a = b) := by
  unfold labelByComparison
  by_cases h : a > b
  · simp [h]
  · by_cases h2 : a < b
    · simp [h, h2]
    · have heq : a = b := by omega
      simp [h, h2, heq]

/-! ### `lexMeasureOrder` — lexicographic order by `Nat` measure then arbitrary relation

This is the most general form of measure-then-relation ordering: first compare by a
`Nat` measure `m`, then by an arbitrary relation `r` when the measures are equal.

All other measure-then-rel comparators in this module are special cases with `r`
fixed to the intrinsic `≤` (e.g., `cmpByMeasureThenLex`, `BetterBy`, `lexMeasureRel`).
By taking `r` as an explicit parameter, `lexMeasureOrder` supports custom tiebreak
relations such as reverse-string order, case-insensitive comparison, or any decidable
total-transitive relation.

It provides decidability, transitivity, and totality lemmas parameterized by the
corresponding properties of `r`. -/

/-- Compare first by a `Nat` measure `m`, then by an arbitrary relation `r`.
`lexMeasureOrder m r a b` holds iff `m a < m b`, or `m a = m b` and `r a b`. -/
def lexMeasureOrder {α : Type u} (m : α → Nat) (r : α → α → Prop) (a b : α) : Prop :=
  m a < m b ∨ (m a = m b ∧ r a b)

/-- `DecidableRel` instance constructor for `lexMeasureOrder` when `r` is decidable. -/

def lexMeasureOrder_decidable {α : Type u} (m : α → Nat) (r : α → α → Prop) [DecidableRel r] :
    DecidableRel (lexMeasureOrder m r) := by
  intro a b; unfold lexMeasureOrder; infer_instance

/-- If `r` is transitive, then `lexMeasureOrder m r` is transitive. -/
theorem lexMeasureOrder_isTrans {α : Type u} (m : α → Nat) (r : α → α → Prop) [IsTrans α r] :
    IsTrans α (lexMeasureOrder m r) := by
  refine ⟨λ a b c h₁ h₂ => ?_⟩
  unfold lexMeasureOrder at h₁ h₂ ⊢
  rcases h₁ with (h₁ | ⟨heq₁, hle₁⟩)
  · rcases h₂ with (h₂ | ⟨heq₂, hle₂⟩)
    · exact Or.inl (lt_trans h₁ h₂)
    · rw [heq₂] at h₁; exact Or.inl h₁
  · rcases h₂ with (h₂ | ⟨heq₂, hle₂⟩)
    · rw [← heq₁] at h₂; exact Or.inl h₂
    · exact Or.inr ⟨heq₁.trans heq₂, IsTrans.trans (a := a) (b := b) (c := c) hle₁ hle₂⟩

/-- If `r` is total, then `lexMeasureOrder m r` is total. -/
theorem lexMeasureOrder_isTotal {α : Type u} (m : α → Nat) (r : α → α → Prop) [IsTotal α r] :
    IsTotal α (lexMeasureOrder m r) := by
  refine ⟨λ a b => ?_⟩
  have h := lt_trichotomy (m a) (m b)
  rcases h with (hlt | heq | hgt)
  · exact Or.inl (Or.inl hlt)
  · have htotal := (inferInstance : IsTotal α r).total a b
    rcases htotal with (hle | hge)
    · exact Or.inl (Or.inr ⟨heq, hle⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hge⟩)
  · exact Or.inr (Or.inl hgt)

/-! ### `descMeasureOrder` — descending by a `Nat` measure, then by an arbitrary relation

This is the descending counterpart of `lexMeasureOrder`: first compare by a `Nat` measure `m`
in *descending* order, then by an arbitrary relation `r` when the measures are equal.

It provides decidability and totality lemmas parameterized by the corresponding properties
of `r`. -/

/-- Compare first by a `Nat` measure `m` in descending order, then by an arbitrary relation `r`.
`descMeasureOrder m r a b` holds iff `m a > m b`, or `m a = m b` and `r a b`. -/
def descMeasureOrder {α : Type u} (m : α → Nat) (r : α → α → Prop) (a b : α) : Prop :=
  m a > m b ∨ (m a = m b ∧ r a b)

/-- `DecidableRel` instance constructor for `descMeasureOrder` when `r` is decidable. -/

def descMeasureOrder_decidable {α : Type u} (m : α → Nat) (r : α → α → Prop) [DecidableRel r] :
    DecidableRel (descMeasureOrder m r) := by
  intro a b; unfold descMeasureOrder; infer_instance

/-- If `r` is total, then `descMeasureOrder m r` is total. -/
theorem descMeasureOrder_isTotal {α : Type u} (m : α → Nat) (r : α → α → Prop) [IsTotal α r] :
    IsTotal α (descMeasureOrder m r) := by
  refine ⟨λ a b => ?_⟩
  unfold descMeasureOrder
  by_cases h : m a > m b
  · exact Or.inl (Or.inl h)
  · by_cases h' : m b > m a
    · exact Or.inr (Or.inl h')
    · have heq : m a = m b := by omega
      have htotal := (inferInstance : IsTotal α r).total a b
      rcases htotal with (hle | hge)
      · exact Or.inl (Or.inr ⟨heq, hle⟩)
      · exact Or.inr (Or.inr ⟨heq.symm, hge⟩)

/-! ### `lexOrdProj` — Bool lexicographic order by two projections

`lexOrdProj f g a b` compares `a` and `b` first by projection `f` (strict `<`),
then by projection `g` (non-strict `≤`) when `f a = f b`.

This generalizes `lexOrd` (which fixes the first projection to `Nat` and uses a custom
`Bool` tiebreak function) by allowing the first projection to map to any type `β`
and using a second projection for tiebreaking.

Common usage: `lexOrdProj (fun s : String => s.length) id s1 s2` sorts by length then
lexicographically; `lexOrdProj freq id a b` sorts by frequency then by value. -/

/-- Compare by projection `f` first (strict `<`), then by projection `g` (non-strict `≤`).
`lexOrdProj f g a b` returns `true` iff `f a < f b`, or `f a = f b` and `g a ≤ g b`. -/
def lexOrdProj {α β γ : Type} [LT β] [DecidableRel (β := β) (· < ·)] [DecidableEq β]
    [LE γ] [DecidableRel (β := γ) (· ≤ ·)] (f : α → β) (g : α → γ) (a b : α) : Bool :=
  decide (f a < f b) || (decide (f a = f b) && decide (g a ≤ g b))

/-- `lexOrdProj f g a b = true` iff `f a < f b` or `(f a = f b ∧ g a ≤ g b)`. -/
lemma lexOrdProj_iff {α β γ : Type} [LT β] [DecidableRel (β := β) (· < ·)] [DecidableEq β]
    [LE γ] [DecidableRel (β := γ) (· ≤ ·)] (f : α → β) (g : α → γ) (a b : α) :
    lexOrdProj f g a b = true ↔ (f a < f b) ∨ (f a = f b ∧ g a ≤ g b) := by
  unfold lexOrdProj
  simp [decide_eq_true_iff, Bool.or_eq_true_iff, Bool.and_eq_true_iff]

/-- Transitivity of `lexOrdProj`. Requires that `<` on `β` and `≤` on `γ` are transitive,
given as explicit arguments (e.g., `Nat.lt_trans` and `le_trans`). -/
lemma lexOrdProj_trans {α β γ : Type} [LT β] [DecidableRel (β := β) (· < ·)] [DecidableEq β]
    [LE γ] [DecidableRel (β := γ) (· ≤ ·)] (f : α → β) (g : α → γ) (a b c : α)
    (hlt_trans : ∀ {x y z : β}, x < y → y < z → x < z)
    (hle_trans : ∀ {x y z : γ}, x ≤ y → y ≤ z → x ≤ z) :
    lexOrdProj f g a b = true → lexOrdProj f g b c = true → lexOrdProj f g a c = true := by
  rw [lexOrdProj_iff f g a b, lexOrdProj_iff f g b c, lexOrdProj_iff f g a c]
  intro h₁ h₂
  rcases h₁ with (h₁ | ⟨h₁eq, h₁le⟩)
  · rcases h₂ with (h₂ | ⟨h₂eq, h₂le⟩)
    · exact Or.inl (hlt_trans h₁ h₂)
    · rw [← h₂eq]; exact Or.inl h₁
  · rcases h₂ with (h₂ | ⟨h₂eq, h₂le⟩)
    · rw [h₁eq]; exact Or.inl h₂
    · rw [h₁eq, h₂eq]; exact Or.inr ⟨rfl, hle_trans h₁le h₂le⟩

/-- Totality of `lexOrdProj` when `β` and `γ` are linearly ordered.
For any `a, b`, either `lexOrdProj f g a b` or `lexOrdProj f g b a` holds.
Useful for `List.sorted_mergeSort`. -/
lemma lexOrdProj_total {α β γ : Type} [LinearOrder β] [LinearOrder γ]
    (f : α → β) (g : α → γ) (a b : α) : (lexOrdProj f g a b || lexOrdProj f g b a) = true := by
  by_cases hlt : f a < f b
  · have h := (lexOrdProj_iff f g a b).2 (Or.inl hlt)
    simp [h]
  · have hge : f b ≤ f a := le_of_not_gt hlt
    by_cases hlt' : f b < f a
    · have h := (lexOrdProj_iff f g b a).2 (Or.inl hlt')
      simp [h]
    · have heq : f a = f b := le_antisymm (le_of_not_gt hlt') hge
      by_cases hle : g a ≤ g b
      · have h := (lexOrdProj_iff f g a b).2 (Or.inr ⟨heq, hle⟩)
        simp [h]
      · have hle' : g b ≤ g a := le_of_not_le hle
        have h := (lexOrdProj_iff f g b a).2 (Or.inr ⟨heq.symm, hle'⟩)
        simp [h]

/-! ### `cmpByValue` — `Bool` comparator by a function into any `LinearOrder`

`cmpByValue f a b` returns `true` iff `f a ≥ f b`. This generalizes `compareByDesc`
(which is specialized to `f : α → Nat`) to any function into a `LinearOrder` codomain.
It is suitable for `List.mergeSort` and similar `Bool`-comparator APIs. -/

/-- `Bool` comparator: `cmpByValue f a b` is `true` iff `f a ≥ f b`.
Generalized over `β` with `[LinearOrder β]`. -/
def cmpByValue {α β : Type} [LinearOrder β] (f : α → β) (a b : α) : Bool :=
  decide (f a ≥ f b)

/-- `cmpByValue` is transitive: if `f a ≥ f b` and `f b ≥ f c`, then `f a ≥ f c`. -/
lemma cmpByValue_trans {α β : Type} [LinearOrder β] (f : α → β) (a b c : α)
    (hab : cmpByValue f a b = true) (hbc : cmpByValue f b c = true) :
    cmpByValue f a c = true := by
  unfold cmpByValue at hab hbc ⊢
  have h1 : f a ≥ f b := of_decide_eq_true hab
  have h2 : f b ≥ f c := of_decide_eq_true hbc
  have h3 : f a ≥ f c := le_trans h2 h1
  simpa using h3

/-- `cmpByValue` is total: for any `a, b`, either `cmpByValue f a b` or `cmpByValue f b a`. -/
lemma cmpByValue_total {α β : Type} [LinearOrder β] (f : α → β) (a b : α) :
    (cmpByValue f a b || cmpByValue f b a) = true := by
  unfold cmpByValue
  have h := le_total (f a) (f b)
  rcases h with (hle | hle)
  · simp [hle]
  · simp [hle]

/-- If a list is `Pairwise` sorted by `cmpByValue f = true`, then it is also `Pairwise`
sorted by the underlying `≥` relation on values. -/
lemma pairwise_cmpByValue_imp {α β : Type} [LinearOrder β] (f : α → β) (l : List α)
    (h : List.Pairwise (fun a b => cmpByValue f a b = true) l) :
    List.Pairwise (fun a b => f a ≥ f b) l := by
  apply List.Pairwise.imp _ h
  intro a b h_eq
  unfold cmpByValue at h_eq
  exact of_decide_eq_true h_eq

/-! ### `notWorseBy` — relation by two `Nat` metrics: primary ≥, secondary ≤ on tie

`notWorseBy f g a b` means `a` is not worse than `b` with respect to two metrics:
`f` (primary, higher is better — `f a ≥ f b`) and `g` (secondary, lower is better —
if `f a = f b` then `g a ≤ g b`). This is equivalent to `descMeasureOrder f`
with tiebreak `λ a b => g a ≤ g b`.

For example, when ranking words by frequency first and first-position second,
`notWorseBy count frequency position a b` holds iff `a` occurs at least as
often as `b`, and if they occur equally often, `a` appears no later than `b`. -/

/-- `notWorseBy f g a b` means `a` is not worse than `b` with respect to two
`Nat`-valued metrics `f` (primary, higher is better) and `g` (secondary, lower
is better). Specifically, `f a ≥ f b`, and if `f a = f b` then `g a ≤ g b`. -/
def notWorseBy {α : Type u} (f g : α → Nat) (a b : α) : Prop :=
  f a ≥ f b ∧ (f a = f b → g a ≤ g b)

/-- `notWorseBy` is reflexive. -/
lemma notWorseBy_refl {α : Type u} (f g : α → Nat) (a : α) : notWorseBy f g a a := by
  refine ⟨Nat.le_refl _, λ _ => Nat.le_refl _⟩

/-- `notWorseBy` is transitive. -/
lemma notWorseBy_trans {α : Type u} (f g : α → Nat) (a b c : α)
    (h_ab : notWorseBy f g a b) (h_bc : notWorseBy f g b c) : notWorseBy f g a c := by
  rcases h_ab with ⟨hge_ab, hfp_ab⟩
  rcases h_bc with ⟨hge_bc, hfp_bc⟩
  refine ⟨?_, ?_⟩
  · omega
  · intro heq_ac
    have heq_ab : f a = f b := by omega
    have heq_bc : f b = f c := by omega
    have h_fp_ab : g a ≤ g b := hfp_ab heq_ab
    have h_fp_bc : g b ≤ g c := hfp_bc heq_bc
    exact le_trans h_fp_ab h_fp_bc

end CompareBy
