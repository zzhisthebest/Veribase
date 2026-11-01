import Mathlib

namespace Fin

/-! ### Cardinalities of `Fin` subtypes -/

/-- Connect `Nat.card` of a `Fin n` subtype to `Fintype.card` and then to `Finset.card`.
In other words, the number of `Fin n` elements satisfying `p` (as a `Nat.card`) equals
the cardinality of the `Finset.filter p Finset.univ`. -/
lemma nat_card_subtype_eq_finset_card {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Nat.card {j : Fin n // p j} = (Finset.filter p Finset.univ).card := by
  let s : Finset (Fin n) := Finset.filter p Finset.univ
  have h_equiv : ∀ (x : Fin n), x ∈ s ↔ p x := by
    intro x; simp [s]
  calc
    Nat.card {j : Fin n // p j} = Fintype.card {j : Fin n // p j} := by
      simp
    _ = s.card := Fintype.card_of_subtype s h_equiv
    _ = (Finset.filter p Finset.univ).card := rfl

/-! ### Strictly increasing triples of `Fin n` indices -/

/-- The Finset of all strictly increasing triples of `Fin n` indices.
That is, all triples `(i, j, k)` with `0 ≤ i < j < k < n`.
Useful for combinatorics problems that iterate over ordered triples of distinct indices. -/
def increasingTriples (n : Nat) : Finset (Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    fun ⟨i, ⟨j, k⟩⟩ => i.val < j.val ∧ j.val < k.val

/-- Membership in `increasingTriples n` iff the components are strictly increasing. -/
lemma mem_increasingTriples_iff {n : Nat} {p : Fin n × Fin n × Fin n} :
    p ∈ increasingTriples n ↔ p.1.val < p.2.1.val ∧ p.2.1.val < p.2.2.val := by
  simp [increasingTriples]

/-! ### Triples of distinct indices (any order) -/

/-- The Finset of all triples `(i, j, k)` of `Fin n` indices where the indices are
pairwise distinct (i.e., `i.1 ≠ j.1`, `i.1 ≠ k.1`, and `j.1 ≠ k.1`).

Contrast with `increasingTriples` which only includes strictly increasing triples
(`i.val < j.val ∧ j.val < k.val`). `distinctTriples` includes all 6 permutations of
any 3 distinct indices (P(n,3) = n·(n-1)·(n-2) elements). -/
def distinctTriples (n : Nat) : Finset (Fin n × Fin n × Fin n) :=
  Finset.filter (λ ⟨i, j, k⟩ => i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1)
    (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ))

/-- Membership in `distinctTriples n` iff all three indices are pairwise distinct. -/
lemma mem_distinctTriples_iff (n : Nat) (i j k : Fin n) :
    (i, j, k) ∈ distinctTriples n ↔ i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 := by
  unfold distinctTriples
  simp

/-- For `n ≥ 3`, `distinctTriples n` is nonempty. -/
lemma distinctTriples_nonempty (n : Nat) (h : n ≥ 3) : (distinctTriples n).Nonempty := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  let i : Fin n := ⟨0, h0⟩
  let j : Fin n := ⟨1, h1⟩
  let k : Fin n := ⟨2, h2⟩
  refine ⟨(i, j, k), ?_⟩
  rw [mem_distinctTriples_iff]
  simp [i, j, k]

/-! ### `Fin n` elements in `Finset.range n ×ˢ Finset.range n` -/

/-- Given two `Fin n` values `a` and `b`, their underlying `Nat` values are in the Cartesian
product `(Finset.range n) ×ˢ (Finset.range n)`. This is useful for theorems that iterate
over all ordered pairs of indices in `[0, n)`. -/
lemma mem_product_range {n : Nat} (a b : Fin n) :
    (a.1, b.1) ∈ Finset.range n ×ˢ Finset.range n :=
  Finset.mem_product.mpr ⟨Finset.mem_range.mpr a.2, Finset.mem_range.mpr b.2⟩

/-! ### All ordered pairs of `Fin n` indices -/

/-- Generate all ordered pairs `(i, j)` of `Fin n` indices as a `List`.
This is the Cartesian product `finRange n × finRange n`, useful for iterating
over all `(i, j)` with `i, j < n` as `Fin n` values. -/
def allPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).product (List.finRange n)

end Fin


namespace Finset

/-! ### All ordered index pairs `(i, j)` with `i, j < n` -/

/-- The Finset of all ordered index pairs `(i, j)` such that `0 ≤ i, j < n`.
This is the full `n × n` Cartesian product `Finset.range n ×ˢ Finset.range n`,
generalized from the LeetCode problem pattern of iterating over all index pairs.
This is the Finset counterpart of `List.indexPairs`. Contrast with:
- `allPairs n` which filters to `i < j` (strict, excludes diagonal and reversed)
- `subarrayIndexPairs n` which filters to `i ≤ j < n` (subarray boundaries) -/
def indexPairs (n : Nat) : Finset (Nat × Nat) :=
  Finset.range n ×ˢ Finset.range n

/-- Membership in `indexPairs n` iff both components are `< n`. -/
lemma mem_indexPairs_iff {i j n : Nat} : (i, j) ∈ indexPairs n ↔ i < n ∧ j < n := by
  dsimp [indexPairs]
  constructor
  · intro h
    rcases Finset.mem_product.mp h with ⟨hi, hj⟩
    exact ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩
  · intro ⟨hi, hj⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩

/-- The cardinality of `indexPairs n` is `n * n`. -/
lemma card_indexPairs (n : Nat) : (indexPairs n).card = n * n := by
  dsimp [indexPairs]
  simp

/-! ### All ordered pairs `(i, j)` with `i < j < n` -/

/-- The Finset of all ordered pairs `(i, j)` such that `0 ≤ i < j < n`.
This is the Finset analogue of `List.allPairs`. Useful for optimization problems
that iterate over all unordered pairs of indices in a range. -/
def allPairs (n : Nat) : Finset (Nat × Nat) :=
  Finset.filter (λ (p : Nat × Nat) => p.1 < p.2) (Finset.range n ×ˢ Finset.range n)

/-- If `i < j < n`, then `(i, j)` is in `allPairs n`. -/
lemma mem_allPairs_of_lt {i j n : Nat} (h_lt : i < j) (h_j : j < n) : (i, j) ∈ allPairs n := by
  unfold allPairs
  refine Finset.mem_filter.mpr ⟨?_, h_lt⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr h_j⟩

/-- Membership in `allPairs n` iff `i < j < n`. -/
lemma mem_allPairs_iff {i j n : Nat} : (i, j) ∈ allPairs n ↔ i < j ∧ j < n := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨h_prod, h_lt⟩
    rcases Finset.mem_product.mp h_prod with ⟨h_i, h_j⟩
    exact ⟨h_lt, Finset.mem_range.mp h_j⟩
  · intro ⟨h_lt, h_j⟩
    exact mem_allPairs_of_lt h_lt h_j

/-- If `1 < n`, then `allPairs n` is nonempty (e.g., `(0, 1)` is in it). -/
lemma allPairs_nonempty_of_one_lt {n : Nat} (h : 1 < n) : (allPairs n).Nonempty := by
  have h_mem : (0, 1) ∈ allPairs n := mem_allPairs_of_lt (by omega) (by omega)
  exact ⟨(0, 1), h_mem⟩

/-! ### All Fin-indexed pairs filtered by a predicate -/

/-- The Finset of all ordered pairs `(i, j)` with `i, j : Fin n` that satisfy
the decidable predicate `pred`. This is `Finset.univ` (the full `Fin n × Fin n`)
filtered by `pred`.

Contrast with:
- `Finset.indexPairs n` which uses `Nat × Nat` indices and returns the full `range n ×ˢ range n`
- `Finset.allPairs n` which uses `Nat × Nat` indices and filters to `i < j`
- `Finset.subarrayIndexPairs n` which uses `Nat × Nat` indices and filters to `i ≤ j`

This is the most general version: the caller supplies any binary predicate `pred : Fin n → Fin n → Prop`
and gets back the Finset of all pairs satisfying it. -/
def filteredPairs (n : Nat) (pred : Fin n → Fin n → Prop) [DecidableRel pred] :
    Finset (Fin n × Fin n) :=
  Finset.filter (λ ⟨i, j⟩ => pred i j) Finset.univ

/-- Convenience wrapper: `filteredListPairs xs pred` is `filteredPairs xs.length pred`,
filtering index pairs from a list by a predicate on `Fin` indices. -/
def filteredListPairs {α : Type _} (xs : List α)
    (pred : Fin xs.length → Fin xs.length → Prop) [DecidableRel pred] :
    Finset (Fin xs.length × Fin xs.length) :=
  filteredPairs xs.length pred

/-- Forward direction: if `pred i j` holds, then `(i, j) ∈ filteredPairs n pred`. -/
lemma mem_filteredPairs {n : Nat} (pred : Fin n → Fin n → Prop) [DecidableRel pred]
    (i j : Fin n) (hp : pred i j) : (i, j) ∈ filteredPairs n pred := by
  unfold filteredPairs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

/-- Reverse direction: if `(i, j) ∈ filteredPairs n pred`, then `pred i j` holds. -/
lemma filteredPairs_mem_imp {n : Nat} (pred : Fin n → Fin n → Prop) [DecidableRel pred]
    {i j : Fin n} (hm : (i, j) ∈ filteredPairs n pred) : pred i j := by
  unfold filteredPairs at hm
  exact (Finset.mem_filter.mp hm).2

/-! ### All ordered triples `(i, j, k)` with `i < j < k < n` -/

/-- The Finset of all ordered triples `(i, j, k)` such that `0 ≤ i < j < k < n`.
This is the 3-index analogue of `allPairs`. Useful for problems that iterate over
all strictly increasing triples of indices in a range. -/
def allTriples (n : Nat) : Finset (Nat × Nat × Nat) :=
  Finset.filter (λ (i, j, k) => i < j ∧ j < k)
    (Finset.product (Finset.range n) (Finset.product (Finset.range n) (Finset.range n)))

/-- Membership in `allTriples n` iff `i < j < k < n`. -/
lemma mem_allTriples_iff {i j k n : Nat} : (i, j, k) ∈ allTriples n ↔ i < j ∧ j < k ∧ i < n ∧ j < n ∧ k < n := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨h_prod, hij, hjk⟩
    rcases Finset.mem_product.mp h_prod with ⟨hi_mem, hjk_mem⟩
    rcases Finset.mem_product.mp hjk_mem with ⟨hj_mem, hk_mem⟩
    exact ⟨hij, hjk, Finset.mem_range.mp hi_mem, Finset.mem_range.mp hj_mem, Finset.mem_range.mp hk_mem⟩
  · intro ⟨hij, hjk, hi, hj, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hij, hjk⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr hi, ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩

/-! ### Counting strictly increasing index triples based on a value function -/

/-- Count the number of index triples `(a,b,c)` with `a < b < c < n`
    such that `vals` is strictly increasing at those indices.
    General over the value type `α`, requiring only a decidable `<`.

    This is the counting counterpart of `allTriples`: given a sequence `vals`,
    count how many strictly increasing index triples also have strictly increasing values.
    For example, if `vals = [1, 5, 3, 7]` and `n = 4`, the triple `(0,1,3)` contributes
    because `1 < 5 < 7`. -/
def countStrictlyIncreasingTriplesOf {α : Type u} [LT α] [DecidableRel (λ x y : α => x < y)]
    (vals : ℕ → α) (n : ℕ) : Nat :=
  ((allTriples n).filter (fun (a, b, c) => vals a < vals b ∧ vals b < vals c)).card

/-! ### All ordered quadruples `(i₀, i₁, i₂, i₃)` with `i₀ < i₁ < i₂ < i₃ < n` -/

/-- The Finset of all ordered quadruples `(i₀, i₁, i₂, i₃)` such that `0 ≤ i₀ < i₁ < i₂ < i₃ < n`.
This is the 4-index analogue of `allPairs` and `allTriples`. Useful for problems that iterate over
all strictly increasing quadruples of indices in a range. -/
def allQuadruples (n : Nat) : Finset (Nat × Nat × Nat × Nat) :=
  Finset.filter (λ ((i0,i1,i2,i3) : Nat × Nat × Nat × Nat) => i0 < i1 ∧ i1 < i2 ∧ i2 < i3)
    (Finset.product (Finset.range n)
      (Finset.product (Finset.range n)
        (Finset.product (Finset.range n) (Finset.range n))))

/-! ### All subarray index pairs `(i, j)` with `i ≤ j < n` -/

/-- The Finset of all index pairs `(i, j)` such that `0 ≤ i ≤ j < n`, representing all
possible subarray boundaries for a list of length `n` (including single-element subarrays
where `i = j`). Contrast with `allPairs n` which requires `i < j` (strict, excludes the diagonal). -/
def subarrayIndexPairs (n : Nat) : Finset (Nat × Nat) :=
  Finset.filter (λ (p : Nat × Nat) => p.1 ≤ p.2 ∧ p.2 < n) (Finset.range n ×ˢ Finset.range n)

/-- Membership in `subarrayIndexPairs n` iff `p.1 ≤ p.2` and `p.2 < n`. -/
lemma mem_subarrayIndexPairs_iff {n : Nat} {p : Nat × Nat} :
    p ∈ subarrayIndexPairs n ↔ p.1 ≤ p.2 ∧ p.2 < n := by
  dsimp [subarrayIndexPairs]
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro ⟨hle, hlt⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · rw [Finset.mem_range]; exact Nat.lt_of_le_of_lt hle hlt
      · rw [Finset.mem_range]; exact hlt
    · exact ⟨hle, hlt⟩

/-- If `0 < n`, then `subarrayIndexPairs n` is nonempty. -/
lemma subarrayIndexPairs_nonempty {n : Nat} (hn : 0 < n) : (subarrayIndexPairs n).Nonempty := by
  have hmem : (0, 0) ∈ subarrayIndexPairs n := by
    rw [mem_subarrayIndexPairs_iff]
    exact ⟨Nat.le_refl 0, hn⟩
  exact ⟨(0, 0), hmem⟩

/-! ### All subarray start-length pairs `(i, len)` with `len > 0` and `i + len ≤ n`

These pairs encode subarray positions using `(start, length)` instead of `(start, end)`.
Contrast with `subarrayIndexPairs` which uses `(start, end)` with `i ≤ j < n`. -/

/-- The Finset of all valid `(i, len)` pairs for subarrays of an array of size `n`,
where `i` is the start index and `len` is the length. Valid means `len > 0` and
`i + len ≤ n` (the subarray fits within bounds). -/
def subarrayStartLenPairs (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range n) ×ˢ (Finset.range (n + 1))).filter (fun (i, len) => i + len ≤ n ∧ len > 0)

/-- Membership in `subarrayStartLenPairs n` iff `i < n`, `len > 0`, and `i + len ≤ n`. -/
lemma mem_subarrayStartLenPairs_iff (i len n : Nat) :
    (i, len) ∈ subarrayStartLenPairs n ↔ i < n ∧ len > 0 ∧ i + len ≤ n := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hprod, ⟨hsum, hpos⟩⟩
    rcases Finset.mem_product.mp hprod with ⟨hi, hlen⟩
    have hi_lt : i < n := Finset.mem_range.mp hi
    exact ⟨hi_lt, hpos, hsum⟩
  · intro ⟨hi_lt, hpos, hsum⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr hi_lt
      · have hlen_lt : len < n + 1 := by omega
        exact Finset.mem_range.mpr hlen_lt
    · exact ⟨hsum, hpos⟩

/-! ### `range n ×ˢ range n` membership -/

/-- If `(a, b) ∈ (range n) ×ˢ (range n)`, then `a < n ∧ b < n`.
This is the reverse direction of combining `Finset.mem_product` and `Finset.mem_range`. -/
lemma mem_product_range_imp_lt {n a b : Nat} (h : (a, b) ∈ Finset.range n ×ˢ Finset.range n) :
    a < n ∧ b < n := by
  rcases Finset.mem_product.mp h with ⟨ha, hb⟩
  exact ⟨Finset.mem_range.mp ha, Finset.mem_range.mp hb⟩

/-- If `a < n` and `b < m`, then `(a, b) ∈ Finset.range n ×ˢ Finset.range m`.
This is the forward direction: combining `Finset.mem_range` and `Finset.mem_product`. -/
lemma mem_product_range_of_lt {n m a b : Nat} (ha : a < n) (hb : b < m) :
    (a, b) ∈ Finset.range n ×ˢ Finset.range m := by
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩

/-! ### Filter by predicate → consequences of emptiness -/

/-- If filtering a Finset by `f x ≠ g x` yields empty, then `f` and `g` agree on all `x ∈ s`. -/
lemma forall_mem_of_filter_eq_empty {α β : Type} [DecidableEq β] {s : Finset α} {f g : α → β}
    (h : (s.filter (fun x => f x ≠ g x)) = ∅) (x : α) (hx : x ∈ s) : f x = g x := by
  by_contra! h_ne
  have h_filter : x ∈ s.filter (fun x => f x ≠ g x) :=
    Finset.mem_filter.mpr ⟨hx, h_ne⟩
  rw [h] at h_filter
  exact Finset.not_mem_empty x h_filter

/-- If `Finset.filter P s = ∅` and `x ∈ s`, then `¬ P x`.
This is the general version: when the filter for *any* decidable predicate is empty,
no element in the set can satisfy the predicate. -/
lemma not_pred_of_mem_of_filter_eq_empty {α : Type} {P : α → Prop} [DecidablePred P] {s : Finset α}
    (h_empty : s.filter P = ∅) (x : α) (h_mem : x ∈ s) : ¬ P x := by
  intro hP
  have h_mem_filter : x ∈ s.filter P := Finset.mem_filter.mpr ⟨h_mem, hP⟩
  rw [h_empty] at h_mem_filter
  exact Finset.not_mem_empty _ h_mem_filter

/-! ### Minimum in image under a function -/

/-- If `(s.image f)` is nonempty, then its minimum is attained at some `a ∈ s`,
and `f a` is minimal among all `f b` for `b ∈ s`. -/
lemma min'_mem_image {α β : Type _} [LinearOrder β]
    (f : α → β) (s : Finset α) (h : (s.image f).Nonempty) :
    ∃ a ∈ s, (s.image f).min' h = f a ∧ ∀ b ∈ s, f a ≤ f b := by
  have hmem := Finset.min'_mem (s.image f) h
  rcases Finset.mem_image.mp hmem with ⟨a, ha, ha_eq⟩
  refine ⟨a, ha, ha_eq.symm, fun b hb => ?_⟩
  have hb_image : f b ∈ s.image f := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hle := Finset.min'_le (s.image f) (f b) hb_image
  simpa [ha_eq] using hle

/-! ### Maximum in image under a function -/

/-- If `(s.image f)` is nonempty, then its maximum is attained at some `a ∈ s`,
and `f a` is maximal among all `f b` for `b ∈ s`.
This is the max' analogue of `min'_mem_image`. -/
lemma max'_mem_image {α β : Type _} [LinearOrder β]
    (f : α → β) (s : Finset α) (h : (s.image f).Nonempty) :
    ∃ a ∈ s, (s.image f).max' h = f a ∧ ∀ b ∈ s, f b ≤ f a := by
  have hmem := Finset.max'_mem (s.image f) h
  rcases Finset.mem_image.mp hmem with ⟨a, ha, ha_eq⟩
  refine ⟨a, ha, ha_eq.symm, fun b hb => ?_⟩
  have hb_image : f b ∈ s.image f := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hle := Finset.le_max' (s.image f) (f b) hb_image
  simpa [ha_eq] using hle

/-- If `a ∈ s`, then `f a ≤ (s.image f).max'` under the nonemptiness proof derived from `a`.
This is a convenience lemma for the common case where the nonemptiness of `s.image f`
is witnessed by `a` itself. -/
lemma le_max'_of_mem_image {α β : Type} [LinearOrder β] {s : Finset α} {f : α → β}
    {a : α} (ha : a ∈ s) : f a ≤ (s.image f).max' (Finset.image_nonempty.mpr ⟨a, ha⟩) := by
  have h_mem : f a ∈ s.image f := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact Finset.le_max' (s.image f) (f a) h_mem

/-! ### Irrelevance of `max'`/`min'` proof arguments -/

/-- The value of `Finset.max'` does not depend on the proof of nonemptiness:
if `h₁` and `h₂` are both proofs that `s` is nonempty, then `s.max' h₁ = s.max' h₂`.
Useful when bridging different nonemptiness proofs, e.g. from two different
witnesses of `s.Nonempty`. -/
lemma max'_irrel {α : Type} [LinearOrder α] {s : Finset α} (h₁ h₂ : s.Nonempty) :
    s.max' h₁ = s.max' h₂ := by
  congr

/-- The value of `Finset.min'` does not depend on the proof of nonemptiness.
The min' analogue of `max'_irrel`. -/
lemma min'_irrel {α : Type} [LinearOrder α] {s : Finset α} (h₁ h₂ : s.Nonempty) :
    s.min' h₁ = s.min' h₂ := by
  congr

/-! ### Uniqueness of `max'` / `min'` -/

/-- An element that belongs to the set and dominates all elements is the unique `max'`.
If `x ∈ s` and `∀ y ∈ s, y ≤ x`, then `x = s.max' h` (where `h` is any nonemptiness proof).
This is useful when you've identified a candidate maximum by other reasoning
and want to equate it to the Finset's `max'`. -/
lemma max'_unique {α : Type} [LinearOrder α] {s : Finset α} {h : s.Nonempty} {x : α}
    (hx_mem : x ∈ s) (hx_ge : ∀ y ∈ s, y ≤ x) : x = s.max' h := by
  apply le_antisymm
  · exact Finset.le_max' s x hx_mem
  · exact Finset.max'_le s h x hx_ge

/-! ### Cardinality bridge: Finset.card ↔ Nat.card of a subtype -/

/-- If a Finset `s` has the same elements as the subtype `{x // P x}`, then their cardinalities match.
This bridges `Finset.card` and `Nat.card` of a subtype. -/
lemma card_eq_natCard_of_finset_subtype {α : Type} (s : Finset α) (P : α → Prop)
    (h : ∀ x, x ∈ s ↔ P x) : s.card = Nat.card {x : α // P x} := by
  have h_card : Nat.card {x : α // x ∈ s} = s.card := by rw [Nat.card_eq_finsetCard]
  have h_equiv : {x : α // x ∈ s} ≃ {x : α // P x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (λ x => h x)
  calc
    s.card = Nat.card {x : α // x ∈ s} := by rw [h_card]
    _ = Nat.card {x : α // P x} := by rw [Nat.card_congr h_equiv]

/-- The cardinality of `Finset.univ.filter p` equals `Fintype.card` of the corresponding subtype.
This bridges the Finset world (where elements are and-decidable) with the Fintype world
(subtype cardinality). Useful for problems that count elements satisfying a property `p`
using `Finset.univ.filter` and then need to relate to `Fintype.card` of the subtype. -/
lemma card_filter_univ_eq_fintype_card_subtype {α : Type} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset α).filter p).card = Fintype.card {x : α // p x} := by
  rw [Fintype.card_subtype]

/-! ### Nonemptiness of `range` for positive bounds -/

/-- If `0 < m`, then `Finset.range m` is nonempty. -/
lemma range_nonempty_of_pos {m : Nat} (hm : 0 < m) : (Finset.range m).Nonempty :=
  ⟨0, Finset.mem_range.mpr hm⟩

/-! ### `range (n+1)` membership via `≤` -/

/-- If `x ≤ n`, then `x` is in `Finset.range (n + 1)`.
This is the forward direction of `Finset.mem_range_succ_iff`. -/
lemma mem_range_succ_of_le {x n : Nat} (h : x ≤ n) : x ∈ Finset.range (n + 1) :=
  Finset.mem_range_succ_iff.mpr h

/-- Membership in `Finset.range (b+1)` is equivalent to `a ≤ b`.
This is the iff version of `mem_range_succ_of_le`, combining
`Finset.mem_range` with `Nat.lt_succ_iff`. -/
lemma mem_range_succ_iff_le {a b : Nat} : a ∈ Finset.range (b + 1) ↔ a ≤ b := by
  rw [Finset.mem_range]
  exact ⟨Nat.le_of_lt_succ, Nat.lt_succ_of_le⟩

/-! ### Filter a predicate with lower bound on a range -/

/-- Filter a decidable predicate `P` on the inclusive interval `[L, R]` of natural numbers.
Returns the Finset `{x | P x ∧ L ≤ x ∧ x ≤ R}`, implemented by filtering
`Finset.range (R+1)` with the lower-bound condition. -/
def filterRange (P : Nat → Prop) [DecidablePred P] (L R : Nat) : Finset Nat :=
  Finset.filter (fun p => P p ∧ L ≤ p) (Finset.range (R + 1))

/-- Membership in `filterRange P L R` is equivalent to `P p ∧ L ≤ p ∧ p ≤ R`. -/
lemma mem_filterRange_iff {p L R : Nat} {P : Nat → Prop} [DecidablePred P] :
    p ∈ filterRange P L R ↔ P p ∧ L ≤ p ∧ p ≤ R := by
  unfold filterRange
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hp_range, hp_P, hp_L⟩
    rw [mem_range_succ_iff_le] at hp_range
    exact ⟨hp_P, hp_L, hp_range⟩
  · rintro ⟨hp_P, hp_L, hp_R⟩
    exact ⟨by rw [mem_range_succ_iff_le]; exact hp_R, hp_P, hp_L⟩

/-! ### Sum of filtered range `[0, n]` -/

/-- Sum of all natural numbers in `[0, n]` (inclusive) that satisfy the decidable
predicate `p`. This is the Finset-based counterpart to `Nat.sumFilteredBelow` (which
sums over `[0, n)` using `List.range`). Uses `Finset.range (n+1)`, `Finset.filter`,
and `Finset.sum` for convenient algebraic manipulation with Finset lemmas.

Example: `sumWhere 10 Nat.Prime = 2 + 3 + 5 + 7 = 17`. -/
def sumWhere (n : Nat) (p : Nat → Prop) [DecidablePred p] : Nat :=
  ((Finset.range (n + 1)).filter p).sum id


lemma sumWhere_eq (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    sumWhere n p = ((Finset.range (n + 1)).filter p).sum id :=
  rfl


theorem sumWhere_zero (p : Nat → Prop) [DecidablePred p] :
    sumWhere 0 p = (if p 0 then 0 else 0) := by
  simp [sumWhere]

theorem sumWhere_succ (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    sumWhere (n + 1) p = sumWhere n p + (if p (n + 1) then n + 1 else 0) := by
  simp [sumWhere, Finset.range_succ, Finset.sum_insert, Finset.sum_filter]
  split <;> omega

/-- Sum of `f k` for all `k` in `[0, n]` (inclusive) such that the decidable predicate `p k`
holds. This generalizes `sumWhere` by allowing an arbitrary function `f : Nat → Nat` instead
of just `id`.

Example: `sumFilteredRange 10 (fun k => k % 2 = 0) (fun k => k^2)` sums the squares of
all even numbers from 0 to 10. -/
def sumFilteredRange (n : Nat) (p : Nat → Prop) [DecidablePred p] (f : Nat → Nat) : Nat :=
  ((Finset.range (n + 1)).filter p).sum f


theorem sumFilteredRange_eq (n : Nat) (p : Nat → Prop) [DecidablePred p] (f : Nat → Nat) :
    sumFilteredRange n p f = ((Finset.range (n + 1)).filter p).sum f :=
  rfl

/-! ### Counting elements satisfying a predicate -/

/-- Count the number of elements in a `Finset` that satisfy a decidable predicate.
This is the Finset counterpart of `List.count_filter` / `List.countP`. -/
def countFilter {α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) : Nat :=
  (filter p s).card

/-! ### Counting ordered pairs satisfying a predicate -/

/-- Count the number of ordered pairs `(a, b)` drawn from a Finset `s` (including the
diagonal `a = b`) that satisfy the binary predicate `pred`.

This is a general combinator for counting pairs satisfying a relation within any Finset.
For counting pairs of natural number indices in a range `0..n`, see `Nat.countAllOrderedPairs`. -/
def countOrderedPairs {α : Type} [DecidableEq α] (s : Finset α) (pred : α → α → Prop)
    [h : ∀ a b, Decidable (pred a b)] : Nat :=
  have hpred : DecidablePred (fun (p : α × α) => pred p.1 p.2) := by
    intro ⟨a, b⟩; exact h a b
  ((s ×ˢ s).filter (fun p : α × α => pred p.1 p.2)).card

lemma countOrderedPairs_eq {α : Type} [DecidableEq α] (s : Finset α) (pred : α → α → Prop)
    [∀ a b, Decidable (pred a b)] :
    countOrderedPairs s pred = ((s ×ˢ s).filter (fun p : α × α => pred p.1 p.2)).card := by
  simp [countOrderedPairs]

/-! ### Counting pairs between two (possibly heterogeneous) Finsets -/

/-- Count the number of ordered pairs `(a, b)` with `a ∈ s` and `b ∈ t` such that the
binary predicate `r a b` holds. This is the heterogeneous version of `countOrderedPairs`:
`s` and `t` may have different types (`α` and `β`). For example, counting all pairs of
indices `(i, j)` in `range n` satisfying `i < j ∧ f i > 2 * f j`.

Uses `Finset.product` (equivalently `×ˢ`) then filters and takes the cardinality. -/
abbrev countPairsWhere {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [inst : DecidablePred (fun (p : α × β) => r p.1 p.2)] : Nat :=
  Finset.card (Finset.filter (fun (p : α × β) => r p.1 p.2) (s.product t))

/-! ### Counting subarray pairs whose value falls in a range -/

/-- Count the number of index pairs `(i, j)` with `i ≤ j < n` such that the value `f i j`
lies within `[lower, upper]`. This counts subarrays whose aggregate value (computed by
the 2D index function `f`) falls in a given range.

This generalizes LeetCode 327 "Count of Range Sum": given a numeric array, count how many
contiguous subarrays have their sum within `[lower, upper]`. Simply instantiate `f i j`
as the sum from index `i` to `j`. -/
def countSubarrayValuesInRange {α : Type} [LE α] [∀ a b : α, Decidable (a ≤ b)]
    (n : Nat) (f : Nat → Nat → α) (lower upper : α) : Nat :=
  ((subarrayIndexPairs n).filter (fun (i, j) => lower ≤ f i j ∧ f i j ≤ upper)).card

/-! ### All ordered triples from a Finset -/

/-- The Finset of all ordered triples `(a, b, c)` with each component drawn from `s`.
This is the Cartesian product `s × s × s` flattened to `(a, b, c)` triples.
For the special case of `s := Finset.range n`, this is the set of all ordered triples
of natural numbers with each coordinate in `[0, n)`. -/
def orderedTriples {α : Type} [DecidableEq α] (s : Finset α) : Finset (α × α × α) :=
  (((s ×ˢ s) ×ˢ s).image (fun p : (α × α) × α => (p.1.1, p.1.2, p.2)))

/-- Membership in `orderedTriples s` is equivalent to each component being in `s`. -/
lemma mem_orderedTriples_iff {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} :
    (a, b, c) ∈ orderedTriples s ↔ a ∈ s ∧ b ∈ s ∧ c ∈ s := by
  constructor
  · intro h
    rw [orderedTriples, Finset.mem_image] at h
    rcases h with ⟨p, hp, hp_eq⟩
    have ha : p.1.1 = a := by
      have := congrArg (fun (x : α × α × α) => x.1) hp_eq
      simpa using this
    have hb : p.1.2 = b := by
      have := congrArg (fun (x : α × α × α) => x.2.1) hp_eq
      simpa using this
    have hc : p.2 = c := by
      have := congrArg (fun (x : α × α × α) => x.2.2) hp_eq
      simpa using this
    subst ha; subst hb; subst hc
    have hmem_prod : p.1 ∈ s ×ˢ s ∧ p.2 ∈ s := Finset.mem_product.mp hp
    rcases hmem_prod with ⟨hmem_ab, hmem_c⟩
    have hmem_ab' : p.1.1 ∈ s ∧ p.1.2 ∈ s := Finset.mem_product.mp hmem_ab
    rcases hmem_ab' with ⟨hmem_a, hmem_b⟩
    exact ⟨hmem_a, hmem_b, hmem_c⟩
  · intro ⟨ha, hb, hc⟩
    rw [orderedTriples, Finset.mem_image]
    refine ⟨((a, b), c), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩

/-! ### Counting ordered triples satisfying a predicate -/

/-- Count the number of triples `(a, b, c)` with `a ∈ sa`, `b ∈ sb`, `c ∈ sc` such that
`pred a b c` holds. This is the ternary analogue of `countOrderedPairs`, generalized to
three potentially different Finsets over three different types. -/
def countTriplesSatisfying {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sa : Finset α) (sb : Finset β) (sc : Finset γ)
    (pred : α → β → γ → Bool) : Nat :=
  ((sa ×ˢ sb ×ˢ sc).filter (fun x : α × β × γ => pred x.1 x.2.1 x.2.2)).card

/-! ### Filter nonemptiness -/

/-- If `x ∈ s` and `p x`, then `s.filter p` is nonempty.
This is the forward direction of `filter_nonempty_iff`. -/
lemma filter_nonempty_of_mem {s : Finset α} {p : α → Prop} [DecidablePred p] {x : α}
    (hx : x ∈ s) (hp : p x) : (s.filter p).Nonempty :=
  ⟨x, mem_filter.mpr ⟨hx, hp⟩⟩

/-! ### `decide` on filter membership for Bool-valued predicates -/

/-- If `a ∈ s`, then `decide (a ∈ s.filter (λ x => f x = true))` equals `f a`.
This is useful when working with Finset filters that use a `Bool` predicate
wrapped as `f x = true`. -/
lemma decide_mem_filter_of_fn_eq {α : Type} [DecidableEq α] (f : α → Bool) (a : α) (s : Finset α)
    (ha : a ∈ s) : decide (a ∈ Finset.filter (λ x => f x = true) s) = f a := by
  simp [Finset.mem_filter, ha]

/-! ### `max'` of a filtered set -/

/-- If `s.filter p` is nonempty, then the predicate `p` holds for its `max'` element.
This is a convenience lemma combining `Finset.max'_mem` with the filter membership
condition: the maximum element of a nonempty filtered set satisfies the filter predicate. -/
lemma max'_mem_filter {α : Type} [LinearOrder α] {p : α → Prop} [DecidablePred p] {s : Finset α}
    (h_nonempty : (s.filter p).Nonempty) : p ((s.filter p).max' h_nonempty) := by
  have hmem : (s.filter p).max' h_nonempty ∈ s.filter p := Finset.max'_mem _ h_nonempty
  exact (Finset.mem_filter.mp hmem).2

/-! ### Minimum element characterization -/

/-- In a linearly ordered Finset, if `k ∈ s` and everything strictly less than `k`
is not in `s`, then `k` is the minimum element of `s`. -/
lemma min'_eq_of_mem_of_forall_not_lt [LinearOrder α] {s : Finset α} {hne : s.Nonempty} {k : α}
    (hk_mem : k ∈ s) (h_lt_not_mem : ∀ x, x < k → x ∉ s) : s.min' hne = k := by
  have h_le : s.min' hne ≤ k := Finset.min'_le _ _ hk_mem
  by_cases h_lt : s.min' hne < k
  · have h_not_mem : s.min' hne ∉ s := h_lt_not_mem (s.min' hne) h_lt
    have h_mem : s.min' hne ∈ s := Finset.min'_mem _ hne
    exact absurd h_mem h_not_mem
  · have h_ge : k ≤ s.min' hne := le_of_not_gt h_lt
    exact le_antisymm h_le h_ge

/-- If an element is strictly less than the minimum of a nonempty Finset,
it is not in the set. -/
lemma not_mem_of_lt_min' [LinearOrder α] {s : Finset α} (hne : s.Nonempty) (m : α)
    (hm : m < s.min' hne) : m ∉ s := by
  intro hm_s
  have hle := Finset.min'_le s m hm_s
  exact not_lt.mpr hle hm

/-! ### Index-of-minimum via predicate -/

/-- Given a length `n` and a sequence `f(0), f(1), ..., f(n-1)` of values,
find the minimal index `k < n` such that `f(k)` satisfies the decidable predicate `P`.
Returns `-1` if no such index exists. -/
def minIndexWhere (n : Nat) (f : Nat → α) (P : α → Bool) : Int :=
  let candidates := Finset.filter (λ k => P (f k)) (Finset.range n)
  if h : candidates.Nonempty then
    (candidates.min' h : Int)
  else
    -1

/-! ### Find the first index ≤ n satisfying a predicate -/

/-- Find the minimum index i ≤ n such that `P i` holds, or return `-1` if no such index exists.
This is the `Prop`-predicate counterpart of `minIndexWhere`: instead of applying a function
`f : Nat → α` and checking a `Bool` predicate on its value, `firstIndexWhere` directly checks
`P : Nat → Prop` with a `[DecidablePred P]` instance. The search is inclusive (`range (n+1)`),
whereas `minIndexWhere` searches the half-open range `range n`.

Implementation: builds `Finset.filter P (Finset.range (n+1))` and returns its `min'`. -/
def firstIndexWhere (n : Nat) (P : Nat → Prop) [DecidablePred P] : Int :=
  let s := Finset.filter P (Finset.range (n + 1))
  if h : s.Nonempty then (s.min' h : Int) else -1

/-- `firstIndexWhere` returns the minimum satisfying index when the candidate set is nonempty. -/
lemma firstIndexWhere_eq_of_nonempty {n : Nat} {P : Nat → Prop} [DecidablePred P]
    (hne : (Finset.filter P (Finset.range (n + 1))).Nonempty) :
    firstIndexWhere n P = ((Finset.filter P (Finset.range (n + 1))).min' hne : Int) := by
  unfold firstIndexWhere
  simp [hne]

/-- `firstIndexWhere` returns -1 when the candidate set is empty. -/
lemma firstIndexWhere_eq_neg_one_of_empty {n : Nat} {P : Nat → Prop} [DecidablePred P]
    (hempty : Finset.filter P (Finset.range (n + 1)) = ∅) :
    firstIndexWhere n P = (-1 : Int) := by
  unfold firstIndexWhere
  simp [hempty]

/-! ### Existence and minimal element above a bound not in a Finset -/

/-- Given `s : Nat` and a finite set `A : Finset Nat`, there exists some `n ≥ s`
that is not in `A`. This holds because a finite set cannot cover an infinite tail
of `Nat`. -/
lemma exists_ge_not_mem (s : Nat) (A : Finset Nat) : ∃ n, s ≤ n ∧ n ∉ A := by
  by_cases h : s ∈ A
  · have h_nonempty : A.Nonempty := ⟨s, h⟩
    let m := Finset.max' A h_nonempty
    have hs_le_m : s ≤ m := Finset.le_max' A s h
    refine ⟨m + 1, by omega, ?_⟩
    intro hm1
    have hm1_le_m : m + 1 ≤ m := Finset.le_max' A (m + 1) hm1
    omega
  · exact ⟨s, le_rfl, h⟩

/-- Properties of the smallest `n ≥ s` not in `A`, computed via `Nat.find`.
If `r := Nat.find (exists_ge_not_mem s A)`, then:
- `s ≤ r` (the result is at least the lower bound),
- `r ∉ A` (the result is indeed not in `A`),
- For all `y`, if `s ≤ y < r`, then `y ∈ A` (minimality: every smaller candidate is in `A`). -/
lemma find_ge_not_mem_spec (s : Nat) (A : Finset Nat) :
    let r := Nat.find (exists_ge_not_mem s A)
    s ≤ r ∧ r ∉ A ∧ ∀ y, s ≤ y → y < r → y ∈ A := by
  intro r
  have h_spec := Nat.find_spec (exists_ge_not_mem s A)
  rcases h_spec with ⟨hge, hmem⟩
  have hmin : ∀ y, s ≤ y → y < r → y ∈ A := by
    intro y hy1 hy2
    by_contra h_not
    have hP : s ≤ y ∧ y ∉ A := ⟨hy1, h_not⟩
    have hmin' := Nat.find_min' (exists_ge_not_mem s A) hP
    omega
  exact ⟨hge, hmem, hmin⟩

/-! ### Intersecting Finsets over a list -/

/-- Given a list `ss` and a function `f : α → Finset β`, intersect all Finsets `f a`
for `a ∈ ss`. Returns `∅` for the empty list.

This generalizes the common pattern of "find elements common to all Finsets
derived from a list" — for example, finding common words across multiple strings. -/
def interAll {α β : Type} [DecidableEq β] (f : α → Finset β) (ss : List α) : Finset β :=
  match ss with
  | [] => ∅
  | s :: ss => ss.foldl (fun acc a => acc ∩ f a) (f s)

/-- A value `w` is in the intersection of all Finsets `f a` for `a ∈ ss` iff
`ss` is non-empty and `w ∈ f a` for all `a ∈ ss`. -/
lemma mem_interAll_iff {α β : Type} [DecidableEq β] (w : β) (f : α → Finset β) (ss : List α) :
    w ∈ interAll f ss ↔ ss ≠ [] ∧ ∀ a ∈ ss, w ∈ f a := by
  cases ss
  · simp [interAll]
  · rename_i s ss
    have hfold (start : Finset β) : w ∈ ss.foldl (fun acc a => acc ∩ f a) start ↔ w ∈ start ∧ ∀ a ∈ ss, w ∈ f a := by
      induction' ss with a as ih generalizing start
      · simp
      · rw [List.foldl, List.forall_mem_cons]
        rw [ih (start ∩ f a)]
        simp [Finset.mem_inter, and_assoc]
    simp [interAll, hfold (f s)]

/-! ### Second maximum element -/

/-- A Finset with at least 2 elements is nonempty. -/
lemma card_ge_two_imp_nonempty {α : Type} (s : Finset α) (hcard : 2 ≤ s.card) : s.Nonempty :=
  Finset.card_pos.mp (by omega : 0 < s.card)

/-- After removing the maximum element from a Finset with at least 2 elements,
    the remainder is nonempty. -/
lemma card_ge_two_imp_erase_max_nonempty {α : Type} [LinearOrder α] (s : Finset α) (hcard : 2 ≤ s.card)
    (hne : s.Nonempty) : (s.erase (s.max' hne)).Nonempty := by
  have hpos : 1 < s.card := by omega
  rcases Finset.one_lt_card.mp hpos with ⟨a, ha, b, hb, hne_ab⟩
  let max_val := s.max' hne
  by_cases ha_max : a = max_val
  · have hb_erase : b ∈ s.erase max_val :=
      Finset.mem_erase_of_ne_of_mem (by
        intro h_eq; apply hne_ab; rw [ha_max, h_eq]) hb
    exact ⟨b, hb_erase⟩
  · have ha_erase : a ∈ s.erase max_val :=
      Finset.mem_erase_of_ne_of_mem ha_max ha
    exact ⟨a, ha_erase⟩

/-- Given a Finset with at least 2 elements, returns the second largest element
    (the maximum of the set with its maximum removed). -/
def second_max {α : Type} [LinearOrder α] (s : Finset α) (hcard : 2 ≤ s.card) : α :=
  let hne_s := card_ge_two_imp_nonempty s hcard
  let max_val := s.max' hne_s
  (s.erase max_val).max' (card_ge_two_imp_erase_max_nonempty s hcard hne_s)

/-- `second_max` is not equal to the maximum element. -/
lemma second_max_ne_max {α : Type} [LinearOrder α] (s : Finset α) (hcard : 2 ≤ s.card) :
    second_max s hcard ≠ s.max' (card_ge_two_imp_nonempty s hcard) := by
  let hne_s := card_ge_two_imp_nonempty s hcard
  unfold second_max
  simp [hne_s]
  have hne_erase := card_ge_two_imp_erase_max_nonempty s hcard hne_s
  have hmem_erase : (s.erase (s.max' hne_s)).max' hne_erase ∈ s.erase (s.max' hne_s) :=
    Finset.max'_mem _ hne_erase
  exact Finset.ne_of_mem_erase hmem_erase

/-- Any element of `s` that is not the maximum is ≤ `second_max`. -/
lemma le_second_max_of_ne_max {α : Type} [LinearOrder α] (s : Finset α) (hcard : 2 ≤ s.card)
    (z : α) (hz : z ∈ s) (hz_ne_max : z ≠ s.max' (card_ge_two_imp_nonempty s hcard)) :
    z ≤ second_max s hcard := by
  let hne_s := card_ge_two_imp_nonempty s hcard
  let max_val := s.max' hne_s
  have hz_erase : z ∈ s.erase max_val :=
    Finset.mem_erase_of_ne_of_mem (by simpa [max_val] using hz_ne_max) hz
  have hne_erase := card_ge_two_imp_erase_max_nonempty s hcard hne_s
  have hsecond_eq : second_max s hcard = (s.erase max_val).max' hne_erase := by
    unfold second_max
    simp [hne_s, max_val, hne_erase]
  rw [hsecond_eq]
  have his_greatest : IsGreatest ((s.erase max_val : Finset α) : Set α) ((s.erase max_val).max' hne_erase) :=
    Finset.isGreatest_max' (s.erase max_val) hne_erase
  exact his_greatest.right hz_erase

/-- If a finset has at least 2 elements and we remove one that is in the set,
    the remaining set still has at least 1 element. -/
lemma card_erase_ge_one_of_card_ge_two {α : Type} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∈ s) (hcard : 2 ≤ s.card) : 1 ≤ (s.erase a).card := by
  have heq := Finset.card_erase_add_one ha
  omega

/-- If a finset has at least 2 elements and we remove one that is in the set,
    the remaining set is nonempty. This is the `Nonempty` version of
    `card_erase_ge_one_of_card_ge_two`. -/
lemma erase_nonempty_of_card_ge_two {α : Type} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∈ s) (hcard : 2 ≤ s.card) : (s.erase a).Nonempty :=
  Finset.one_le_card.mp (card_erase_ge_one_of_card_ge_two ha hcard)

/-- In any finset with at least 2 distinct elements, there exist two distinct elements
    `max1` and `max2` such that `max1` is the maximum, and `max2` is the maximum
    among the remaining elements (i.e., the second largest). -/
theorem exists_secondMax {α : Type} [LinearOrder α] (s : Finset α) (hcard : 2 ≤ s.card) :
    ∃ (max1 max2 : α),
      max1 ∈ s ∧ max2 ∈ s ∧ max1 ≠ max2 ∧
      (∀ z ∈ s, z ≤ max1) ∧
      (∀ z ∈ s, z ≠ max1 → z ≤ max2) := by
  have hcard1 : 1 ≤ s.card := by omega
  have hne : s.Nonempty := Finset.one_le_card.mp hcard1
  let max1 := s.max' hne
  have hmax1_isGreatest : IsGreatest (s : Set α) max1 := Finset.isGreatest_max' _ hne
  have hmax1_mem : max1 ∈ s := hmax1_isGreatest.1
  have hcard_erase : 1 ≤ (s.erase max1).card :=
    card_erase_ge_one_of_card_ge_two hmax1_mem hcard
  have hne_erase : (s.erase max1).Nonempty := Finset.one_le_card.mp hcard_erase
  let max2 := (s.erase max1).max' hne_erase
  have hmax2_isGreatest : IsGreatest ((s.erase max1) : Set α) max2 :=
    Finset.isGreatest_max' _ hne_erase
  have hmax2_mem_erase : max2 ∈ s.erase max1 := hmax2_isGreatest.1
  have hmax2_ne_max1 : max2 ≠ max1 := Finset.ne_of_mem_erase hmax2_mem_erase
  have hmax2_mem_s : max2 ∈ s := Finset.mem_of_mem_erase hmax2_mem_erase
  refine ⟨max1, max2, hmax1_mem, hmax2_mem_s, hmax2_ne_max1.symm, ?_, ?_⟩
  · intro z hz; exact hmax1_isGreatest.2 hz
  · intro z hz hzne
    have hz_erase : z ∈ s.erase max1 := by
      rw [Finset.mem_erase]
      exact ⟨hzne, hz⟩
    exact hmax2_isGreatest.2 hz_erase

/-- Find the second largest element in a finset.
    Returns `none` if the finset has fewer than 2 elements.
    This is the `Option`-based version; for the proof-carrying version, see `second_max`. -/
def secondMax {α : Type} [LinearOrder α] (s : Finset α) : Option α :=
  if h : s.card < 2 then
    none
  else
    let hcard : 1 ≤ s.card := by omega
    let hne : s.Nonempty := Finset.one_le_card.mp hcard
    let max1 : α := s.max' hne
    let hmax1_mem : max1 ∈ s := Finset.max'_mem _ hne
    let hcard_erase : 1 ≤ (s.erase max1).card :=
      card_erase_ge_one_of_card_ge_two hmax1_mem (by omega)
    let hne_erase : (s.erase max1).Nonempty := Finset.one_le_card.mp hcard_erase
    some ((s.erase max1).max' hne_erase)

/-- Specification for `Finset.secondMax`:
    either the set has fewer than 2 elements and we return `none`,
    or we return `some m` where `m` is the second largest element. -/
def secondMax_spec {α : Type} [LinearOrder α] (s : Finset α) (result : Option α) : Prop :=
  (s.card < 2 ∧ result = none) ∨
  ∃ (max1 max2 : α),
    max1 ∈ s ∧ max2 ∈ s ∧ max1 ≠ max2 ∧
    (∀ z ∈ s, z ≤ max1) ∧
    (∀ z ∈ s, z ≠ max1 → z ≤ max2) ∧
    result = some max2

/-- `Finset.secondMax` satisfies its specification. -/
theorem secondMax_satisfies_spec {α : Type} [LinearOrder α] {s : Finset α} :
    secondMax_spec s (secondMax s) := by
  unfold secondMax_spec
  by_cases hcard : s.card < 2
  · have hsecondMax : secondMax s = none := by
      unfold secondMax
      simp [hcard]
    rw [hsecondMax]
    left
    exact ⟨hcard, rfl⟩
  · have hcard2 : 2 ≤ s.card := by omega
    have hcard1 : 1 ≤ s.card := by omega
    have hne : s.Nonempty := Finset.one_le_card.mp hcard1
    let max1 := s.max' hne
    have hmax1_isGreatest : IsGreatest (s : Set α) max1 := Finset.isGreatest_max' _ hne
    have hmax1_mem : max1 ∈ s := hmax1_isGreatest.1
    have hcard_erase : 1 ≤ (s.erase max1).card :=
      card_erase_ge_one_of_card_ge_two hmax1_mem hcard2
    have hne_erase : (s.erase max1).Nonempty := Finset.one_le_card.mp hcard_erase
    let max2 := (s.erase max1).max' hne_erase
    have hmax2_isGreatest : IsGreatest ((s.erase max1) : Set α) max2 :=
      Finset.isGreatest_max' _ hne_erase
    have hmax2_mem_erase : max2 ∈ s.erase max1 := hmax2_isGreatest.1
    have hmax2_ne_max1 : max2 ≠ max1 := Finset.ne_of_mem_erase hmax2_mem_erase
    have hmax2_mem_s : max2 ∈ s := Finset.mem_of_mem_erase hmax2_mem_erase
    have hsecondMax : secondMax s = some max2 := by
      unfold secondMax
      simp [hcard]
      dsimp
    rw [hsecondMax]
    right
    refine ⟨max1, max2, hmax1_mem, hmax2_mem_s, hmax2_ne_max1.symm, ?_, ?_, rfl⟩
    · intro z hz; exact hmax1_isGreatest.2 hz
    · intro z hz hzne
      have hz_erase : z ∈ s.erase max1 := by
        rw [Finset.mem_erase]
        exact ⟨hzne, hz⟩
      exact hmax2_isGreatest.2 hz_erase

/-! ### Lemmas about `max'` after erasing the maximum -/

/-- No element of the Finset is strictly greater than its maximum. -/
lemma not_gt_max' {α : Type} [LinearOrder α] {s : Finset α} {hne : s.Nonempty} {a : α}
    (ha : a ∈ s) : ¬ s.max' hne < a :=
  not_lt_of_le (Finset.le_max' s a ha)

/-- The maximum of a Finset after erasing its maximum (the "second maximum") is strictly
    less than the maximum of the original Finset. -/
lemma max'_erase_lt_max' {α : Type} [LinearOrder α] [DecidableEq α] {s : Finset α}
    {hne : s.Nonempty} (hne_rest : (s.erase (s.max' hne)).Nonempty) :
    (s.erase (s.max' hne)).max' hne_rest < s.max' hne := by
  set r := (s.erase (s.max' hne)).max' hne_rest with hr
  have hmem : r ∈ s.erase (s.max' hne) := Finset.max'_mem _ hne_rest
  have hmem_s : r ∈ s := (Finset.mem_erase.mp hmem).2
  have hne_max : r ≠ s.max' hne := (Finset.mem_erase.mp hmem).1
  have hle : r ≤ s.max' hne := Finset.le_max' s r hmem_s
  exact lt_of_le_of_ne hle hne_max

/-- If an element is greater than the second maximum, it must be the maximum element. -/
lemma eq_max'_of_gt_secondMax {α : Type} [LinearOrder α] [DecidableEq α] {s : Finset α}
    {hne : s.Nonempty} (hne_rest : (s.erase (s.max' hne)).Nonempty) {a : α}
    (ha : a ∈ s) (hgt : (s.erase (s.max' hne)).max' hne_rest < a) : a = s.max' hne := by
  by_cases h_eq : a = s.max' hne
  · exact h_eq
  · have ha_mem_rest : a ∈ s.erase (s.max' hne) := by
      rw [Finset.mem_erase]
      exact ⟨h_eq, ha⟩
    have hle : a ≤ (s.erase (s.max' hne)).max' hne_rest :=
      Finset.le_max' _ a ha_mem_rest
    exact absurd (lt_of_lt_of_le hgt hle) (lt_irrefl _)

end Finset

namespace Nat

/-- For a fintype `α` and a decidable predicate `p`, the `Nat.card` of the subtype `{ x // p x }`
equals the count of elements in `Finset.univ` that satisfy `p`. -/
lemma card_subtype_eq_finset_filter_card {α : Type _} [Fintype α] {p : α → Prop}
    [DecidablePred p] : Nat.card { x : α // p x } = (Finset.filter p Finset.univ).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Nat

