import Mathlib

namespace List

/-! ### `indices` — valid index positions of a list -/

/-- Return the list of valid indices `[0, …, l.length - 1]` for any list `l`.
Reusable across any problem that iterates over list positions. -/
def indices (l : List α) : List Nat :=
  List.range l.length

lemma indices_nil : indices ([] : List α) = [] := by
  simp [indices]

lemma indices_singleton (a : α) : indices [a] = [0] := by
  unfold indices; simp [List.range_succ]

lemma indices_eq_range_length (l : List α) : indices l = List.range l.length := rfl

lemma mem_indices_iff (l : List α) (i : Nat) : i ∈ indices l ↔ i < l.length := by
  simp [indices]

/-! ### `rangeList` — list of naturals between two bounds (inclusive)

`rangeList left right` produces the list `[left, left+1, …, right]`.
This is the list analogue of `Finset.Icc`. -/

/-- Generate the list of all natural numbers from `left` to `right` inclusive. -/
def rangeList (left right : Nat) : List Nat :=
  List.filter (λ x => left ≤ x) (List.range (right + 1))

/-- Membership in `rangeList`: `a ∈ rangeList left right` iff `left ≤ a ≤ right`. -/

lemma mem_rangeList_iff (a left right : Nat) : a ∈ rangeList left right ↔ (left ≤ a ∧ a ≤ right) := by
  unfold rangeList
  rw [List.mem_filter]
  constructor
  · rintro ⟨h₁, h₂⟩
    have ha_lt : a < right + 1 := (List.mem_range.1 h₁)
    constructor
    · simpa using h₂
    · omega
  · rintro ⟨hl, hr⟩
    constructor
    · apply List.mem_range.2; omega
    · have : decide (left ≤ a) = true := by simp [hl]
      simpa using this

/-- For any predicate `f` on `ℕ`, `f` holds on all elements of `rangeList left right`
    exactly when `f x` holds for all `x` between `left` and `right` inclusive. -/
lemma all_rangeList_eq_true (left right : Nat) (f : Nat → Bool) :
    ((rangeList left right).all f = true) ↔ (∀ x, left ≤ x → x ≤ right → f x = true) := by
  rw [List.all_eq_true]
  constructor
  · intro h x hxl hxr
    apply h
    rw [mem_rangeList_iff]
    exact ⟨hxl, hxr⟩
  · intro h x hx_mem
    rw [mem_rangeList_iff] at hx_mem
    rcases hx_mem with ⟨hxl, hxr⟩
    exact h x hxl hxr

/-- `rangeList l l` is exactly the singleton list `[l]`. -/

lemma rangeList_self (l : Nat) : rangeList l l = [l] := by
  unfold rangeList
  rw [List.range_succ, List.filter_append]
  simp

/-- If `r < l`, then `rangeList l r` is empty. -/

lemma rangeList_nil_of_lt {l r : Nat} (h : r < l) : rangeList l r = [] := by
  unfold rangeList
  rw [List.eq_nil_iff_forall_not_mem]
  intro a ha
  rcases List.mem_filter.mp ha with ⟨ha_mem, ha_le⟩
  have ha_range : a < r + 1 := List.mem_range.mp ha_mem
  have ha_ge : l ≤ a := by simpa using ha_le
  omega

/-! ### `posRange` — list `[1, 2, …, n]` -/

/-- The list of integers 1, 2, ..., n.
This is a convenience alias for `List.range' 1 n`. -/
def posRange (n : Nat) : List Nat :=
  List.range' 1 n

/-- Membership in `posRange n` is equivalent to being between 1 and n inclusive. -/

lemma mem_posRange_iff {i n : Nat} : i ∈ posRange n ↔ 1 ≤ i ∧ i ≤ n := by
  unfold posRange
  simp [List.mem_range']
  constructor
  · rintro ⟨j, hj, h⟩
    rw [h]
    have : j + 1 ≤ n := by omega
    omega
  · intro ⟨h1, h2⟩
    have : i - 1 < n := by
      omega
    refine ⟨i - 1, this, ?_⟩
    omega

/-! ### `map_range` — map a function over a range

`map_range f n` is the list `[f 0, f 1, …, f (n-1)]`. It is syntactic sugar for
`(List.range n).map f`. -/

/-- Map a function `f` over `List.range n`, producing a list of the first `n` values of `f`. -/
def map_range (f : Nat → α) (n : Nat) : List α := (List.range n).map f

/-- If `f : Nat → α` is injective, then `(List.range n).map f` is nodup. -/
lemma nodup_map_range {α : Type} (f : Nat → α) (hf : Function.Injective f) (n : Nat) :
    ((List.range n).map f).Nodup :=
  List.Nodup.map hf (List.nodup_range n)

/-- The list `[1, 2, …, n]` (as `(List.range n).map (· + 1)`) is nodup. -/
lemma nodup_range_map_succ (n : Nat) : ((List.range n).map (fun i => i + 1)).Nodup :=
  nodup_map_range (fun i => i + 1) (fun _x _y h => Nat.add_right_cancel h) n

/-- `posRange n` (i.e., `[1, 2, …, n]`) has no duplicates. -/
lemma nodup_posRange (n : Nat) : (posRange n).Nodup := by
  unfold posRange
  rw [List.range'_eq_map_range]
  apply nodup_map_range (1 + ·) (fun _x _y h => Nat.add_left_cancel h) n

/-! ### `(List.range n).map (· + 1)` — the list `[1, 2, …, n]` -/

/-- Membership in `(List.range n).map (· + 1)` (i.e., `[1, 2, …, n]`)
is equivalent to being between `1` and `n` inclusive. -/
lemma mem_map_range_succ_iff (i n : Nat) : i ∈ ((List.range n).map (· + 1)) ↔ 1 ≤ i ∧ i ≤ n := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j, hj, rfl⟩
    have hj_lt : j < n := List.mem_range.mp hj
    constructor <;> omega
  · intro ⟨hi1, hi2⟩
    refine List.mem_map.mpr ⟨i - 1, List.mem_range.mpr ?_, ?_⟩
    · omega
    · omega

/-- `List.any` over `(range n).map (· + 1)` is equivalent to
an existential over `1 .. n`. This abstracts the common pattern of checking
whether any choice/move in `[1, n]` satisfies a condition `P`. -/
lemma any_map_range_succ_eq_true_iff (n : Nat) (P : Nat → Bool) :
    ((List.range n).map (· + 1)).any P = true ↔ ∃ i, 1 ≤ i ∧ i ≤ n ∧ P i = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hP⟩
    rw [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [List.mem_range] at hy
    have hy' : 1 ≤ y + 1 := by omega
    have hy'' : y + 1 ≤ n := by omega
    exact ⟨y + 1, hy', hy'', hP⟩
  · rintro ⟨i, hi1, hi2, hiP⟩
    have hi_sub : i - 1 < n := by omega
    refine ⟨i, List.mem_map.mpr ⟨i - 1, List.mem_range.mpr hi_sub, by omega⟩, hiP⟩

/-! ### `rangeFilter` — filter a bounded range of ℕ by a predicate -/

/-- Filter numbers in `[l, r]` that satisfy a predicate `pred`.
This is a one-pass composition of `range` and `filter`:
`rangeFilter pred l r = (List.range (r + 1)).filter (fun n => l ≤ n ∧ pred n = true)`.

Compare with `rangeList`, which is `rangeFilter (fun _ => true)`. -/
def rangeFilter (pred : Nat → Bool) (l r : Nat) : List Nat :=
  (List.range (r + 1)).filter (fun n => l ≤ n && pred n)

/-- Membership in `rangeFilter`: `a ∈ rangeFilter pred l r` iff `l ≤ a ≤ r` and `pred a = true`. -/

lemma mem_rangeFilter_iff (pred : Nat → Bool) (l r a : Nat) :
    a ∈ rangeFilter pred l r ↔ l ≤ a ∧ a ≤ r ∧ pred a := by
  unfold rangeFilter
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨ha_range, hcond⟩
    have ha_range' : a ≤ r := by omega
    have hcond' : decide (l ≤ a) = true ∧ pred a = true := by
      simpa [Bool.and_eq_true] using hcond
    rcases hcond' with ⟨hl, hp⟩
    refine ⟨by simpa using hl, ha_range', hp⟩
  · rintro ⟨hl, hr, hp⟩
    refine ⟨by omega, ?_⟩
    simp [hl, hp]

/-- Membership in `rangeFilter` with a `DecidablePred` predicate (bridged via `decide`):
`n ∈ rangeFilter (λ x => decide (P x)) l r ↔ P n ∧ l ≤ n ∧ n ≤ r`.
This is the `DecidablePred` version of `mem_rangeFilter_iff`. -/
lemma mem_rangeFilter_decide_iff {P : Nat → Prop} [DecidablePred P] {l r n : Nat} :
    n ∈ rangeFilter (λ x => decide (P x)) l r ↔ P n ∧ l ≤ n ∧ n ≤ r := by
  simp [mem_rangeFilter_iff, decide_eq_true_iff, and_comm, and_assoc, and_left_comm]

/-- `rangeFilter pred l r = []` when `r < l`. -/
lemma rangeFilter_nil_of_lt (pred : Nat → Bool) {l r : Nat} (h : r < l) :
    rangeFilter pred l r = [] := by
  unfold rangeFilter
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  rcases List.mem_filter.mp ha with ⟨ha_range, ha_cond⟩
  have ha_lt : a < r + 1 := List.mem_range.mp ha_range
  simp at ha_cond
  omega

/-! ### Interval covering predicates -/

/-- A point `x` is covered by some interval in `ranges` (as a `Bool` test via `List.any`)
    iff there exists an interval in `ranges` whose endpoints bound `x`. -/
lemma any_intervals_cover_iff (ranges : List (Nat × Nat)) (x : Nat) :
    (ranges.any (λ p => p.1 ≤ x && x ≤ p.2) = true) ↔ (∃ p, p ∈ ranges ∧ p.1 ≤ x ∧ x ≤ p.2) := by
  rw [List.any_eq_true]
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨p, hp_mem, hp₁, hp₂⟩
    exact ⟨p, hp_mem, by simpa using hp₁, by simpa using hp₂⟩
  · rintro ⟨p, hp_mem, hp₁, hp₂⟩
    exact ⟨p, hp_mem, by simp [hp₁], by simp [hp₂]⟩

/-- All elements in a range `[left, right]` are covered by at least one interval from `ranges`
    iff for every `x` in that range, there exists an interval in `ranges` covering `x`.
    Combines `all_rangeList_eq_true` and `any_intervals_cover_iff`. -/
lemma all_any_spec (ranges : List (Nat × Nat)) (left right : Nat) :
    ((rangeList left right).all (λ x => ranges.any (λ p => p.1 ≤ x && x ≤ p.2)) = true) ↔
    (∀ x, left ≤ x → x ≤ right → ∃ p, p ∈ ranges ∧ p.1 ≤ x ∧ x ≤ p.2) := by
  rw [all_rangeList_eq_true]
  simp [any_intervals_cover_iff]

/-! ### Basic properties of `List.range` -/

/-- For `n ≠ 0`, the head of `List.range n` is `some 0`.
This is a `@[simp]`-friendly version of `List.head?_range` that avoids the `if` in the result. -/

lemma range_head?_zero (n : Nat) (hn0 : n ≠ 0) : (List.range n).head? = some 0 := by
  simpa [hn0] using List.head?_range n

/-- If a boolean predicate `p` holds on all `i < n`, then `List.all (List.range n) p = true`.
This is the bridge between a quantified `∀` statement and the `List.all` operation on `List.range`. -/
lemma all_range_eq_true_of_forall_lt {n : Nat} {p : Nat → Bool} (h : ∀ i, i < n → p i = true) :
    List.all (List.range n) p = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  exact h i hi

/-- `(List.range limit).all p = true` iff `p i = true` for all `i < limit`.
This is the full equivalence version of `all_range_eq_true_of_forall_lt`. -/
lemma all_range_eq_true_iff {p : Nat → Bool} {limit : Nat} :
    (List.range limit).all p = true ↔ ∀ i < limit, p i = true := by
  simp [List.all_eq_true, List.mem_range]

/-- Bridges an existential over membership in `List.range n` to an existential
over `k < n` with the same `Prop` predicate `p`.
This is the existential analogue of `all_range_eq_true_iff`. -/
lemma exists_mem_range_iff {n : Nat} {p : Nat → Prop} :
    (∃ x, x ∈ List.range n ∧ p x) ↔ (∃ k, k < n ∧ p k) := by
  constructor
  · rintro ⟨x, hx, hp⟩; exact ⟨x, List.mem_range.mp hx, hp⟩
  · rintro ⟨k, hk, hp⟩; exact ⟨k, List.mem_range.mpr hk, hp⟩

/-- If `i < j` and `j < N`, then `i ∈ List.range N`.
This packages `List.mem_range.mpr` with `Nat.lt_trans` for convenience. -/
lemma mem_range_of_lt_of_lt {i j N : Nat} (hij : i < j) (hjN : j < N) : i ∈ List.range N :=
  List.mem_range.mpr (Nat.lt_trans hij hjN)

/-! ### `mem_range_succ` — membership in `range (n+1)` is equivalent to `≤ n` -/

/-- `n ∈ List.range (k + 1)` iff `n ≤ k`.
This bridges the strict inequality from `List.mem_range` (`n < k`) to the non-strict version
via `Nat.lt_succ_iff`. -/

lemma mem_range_succ_iff {n k : Nat} : n ∈ List.range (k + 1) ↔ n ≤ k := by
  rw [List.mem_range, Nat.lt_succ_iff]

/-- If `n ∈ List.range (k + 1)`, then `n ≤ k`.
Forward direction of `mem_range_succ_iff`. -/
lemma mem_range_succ_imp_le {n k : Nat} (h : n ∈ List.range (k + 1)) : n ≤ k :=
  mem_range_succ_iff.mp h

/-- If `n ≤ k`, then `n` is a member of `List.range (k + 1)`.
Reverse direction of `mem_range_succ_iff`. -/
lemma mem_range_succ_of_le {n k : Nat} (h : n ≤ k) : n ∈ List.range (k + 1) :=
  mem_range_succ_iff.mpr h

/-! ### `filterRange` — filter `List.range` by a decidable `Prop` predicate -/

/-- Filter `List.range limit` by a decidable predicate `P : Nat → Prop`.
This is a convenience wrapper that applies `decide` to lift `P` to a `Bool` predicate.
Compare with `rangeFilter` which additionally filters by a lower bound. -/
def filterRange (P : Nat → Prop) [DecidablePred P] (limit : Nat) : List Nat :=
  List.filter (λ n => decide (P n)) (List.range limit)

/-- Membership in `filterRange P n`: `x ∈ filterRange P n` iff `x < n` and `P x` holds. -/

lemma mem_filterRange_iff {P : Nat → Prop} [DecidablePred P] {n x : Nat} :
    x ∈ filterRange P n ↔ (x < n ∧ P x) := by
  dsimp [filterRange]
  simp [decide_eq_true_iff]

/-! ### `range` + `filter` combinations -/

/-- Membership in a filtered range: `i ∈ (List.range n).filter p` iff `i < n` and `p i` holds. -/

theorem mem_range_filter_iff {n : Nat} {p : Nat → Bool} {i : Nat} :
    i ∈ (List.range n).filter p ↔ i < n ∧ p i := by
  simp

/-- Membership in a filtered range using `decide` on a decidable predicate `p`.
This bridges the gap between `Bool`-valued `decide` and `Prop`-valued `p`.
This is the `DecidablePred` version of `mem_range_filter_iff`. -/
lemma mem_range_filter_decide_iff {L i : Nat} {p : Nat → Prop} [DecidablePred p] :
    i ∈ (List.range L).filter (λ j => decide (p j)) ↔ i < L ∧ p i := by
  simp [decide_eq_true_iff]

/-- If `n < N` is already known, membership in `(range N).filter (λ x => decide (p x))`
simplifies to just `p n`. This is a convenient corollary of `mem_range_filter_decide_iff`
for when the bound condition is already available as a hypothesis. -/
lemma mem_filter_range_decide_iff_of_lt {p : Nat → Prop} [DecidablePred p] {N n : Nat} (h_lt : n < N) :
    n ∈ (List.range N).filter (λ x => decide (p x)) ↔ p n := by
  constructor
  · intro h
    rw [List.mem_filter] at h
    simpa using h.2
  · intro h
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr h_lt, by simpa⟩

/-- Find all indices `i < n` that satisfy a boolean predicate.
Equivalent to `(List.range n).filter pred` but with an explicit name
for readability. This is the `List` counterpart of `Array.indicesWhere`. -/
def indicesWhere (n : Nat) (pred : Nat → Bool) : List Nat :=
  (List.range n).filter pred

/-- Membership in `(range (n+1)).filter (λ x => decide (P x))` is equivalent to
`P i` and `i ≤ n`. This is the `≤ n` (inclusive) version of `mem_range_filter_iff`
for `Prop`-based predicates via `decide`. -/
lemma mem_range_succ_filter_iff {P : Nat → Prop} [DecidablePred P] {n i : Nat} :
    i ∈ (List.range (n + 1)).filter (λ x => decide (P x)) ↔ P i ∧ i ≤ n := by
  rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, Nat.le_of_lt_succ hlt⟩
  · rintro ⟨hp, hle⟩
    exact ⟨Nat.lt_succ_of_le hle, hp⟩

/-- Membership in `(range (n+1)).filter p` for a `Bool` predicate `p`:
`i ∈ (range (n+1)).filter p` iff `i ≤ n` and `p i` holds.
This is the `≤ n` (inclusive) Bool version of `mem_range_filter_iff`,
and the Bool counterpart of `mem_range_succ_filter_iff` (which uses `Prop` + `decide`). -/

lemma mem_range_succ_filter_bool_iff {n : Nat} {p : Nat → Bool} {i : Nat} :
    i ∈ (List.range (n + 1)).filter p ↔ i ≤ n ∧ p i := by
  simp [Nat.lt_succ_iff]

/-- An element belongs to `(range n).filter (λ j => f j = a)` iff it is less than `n`
and `f` maps it to `a`. -/
lemma mem_range_filter_eq_iff {α : Type} [DecidableEq α] (n i : Nat) (f : Nat → α) (a : α) :
    i ∈ ((List.range n).filter (fun j => f j = a)) ↔ i < n ∧ f i = a := by
  simp

/-- The sublist of `List.range n` obtained by filtering with any predicate `p` is sorted. -/
theorem sorted_range_filter (n : Nat) (p : Nat → Bool) :
    List.Sorted (· ≤ ·) ((List.range n).filter p) :=
  (List.pairwise_le_range n).filter p

/-- A filtered range is nodup. Applies to any predicate `p : Nat → Bool`. -/
lemma nodup_range_filter {n : Nat} (p : Nat → Bool) :
    List.Nodup ((List.range n).filter p) :=
  (List.nodup_range n).filter _

/-- A filtered range is both nodup and sorted. -/
theorem nodup_sorted_range_filter {n : Nat} (p : Nat → Bool) :
    List.Nodup ((List.range n).filter p) ∧ List.Sorted (· ≤ ·) ((List.range n).filter p) := by
  exact ⟨nodup_range_filter p, sorted_range_filter n p⟩

/-- A filtered range is nodup (specialized to equality predicates). -/
lemma nodup_filter_range {α : Type} [DecidableEq α] (n : Nat) (f : Nat → α) (a : α) :
    List.Nodup ((List.range n).filter (fun j => f j = a)) :=
  nodup_range_filter (fun j => decide (f j = a))

/-- Forward direction of `mem_range_filter_iff` for `Prop` predicates:
if `i < n` and `p i` holds, then `i` belongs to `(range n).filter p`.
This bridges `DecidablePred` to `Bool` via `decide`. -/
theorem mem_range_filter_of_lt_and_pred {p : Nat → Prop} [DecidablePred p] {n i : Nat}
    (hi : i < n) (hp : p i) : i ∈ (List.range n).filter p :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true hp⟩

/-! ### `mem_cons_range_lt` — membership in `a :: range len` implies bound -/

/-- If `x ∈ a :: List.range len` and `a < len`, then `x < len`.
Useful when the head `a` is known to be in bounds and the tail is a range. -/
lemma mem_cons_range_lt {x a len : Nat} (ha : a < len) (h : x ∈ a :: List.range len) : x < len := by
  cases h
  · exact ha
  · exact List.mem_range.mp ‹_›

/-! ### `product (range m) (range n)` membership and filtering -/

/-- Every element of `List.product (List.range m) (List.range n)` has both components
    strictly less than their respective bounds. -/
lemma mem_product_range_lt {m n : Nat} {p : Nat × Nat}
    (h : p ∈ List.product (List.range m) (List.range n)) : p.1 < m ∧ p.2 < n := by
  rcases List.mem_product.mp h with ⟨h₁, h₂⟩
  rw [List.mem_range] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- When filtering a product of ranges, the bounds conditions `(i < m ∧ j < n)` are redundant:
    they are satisfied by all elements in the list, so filtering with `Q` alone is equivalent. -/
lemma filter_product_range_remove_bounds {m n : Nat} (Q : Nat × Nat → Bool) :
    List.filter (fun (p : Nat × Nat) => decide (p.1 < m) && decide (p.2 < n) && Q p)
      (List.product (List.range m) (List.range n)) =
    List.filter Q (List.product (List.range m) (List.range n)) := by
  apply List.filter_congr
  intro p hp
  rcases mem_product_range_lt hp with ⟨h₁, h₂⟩
  simp [h₁, h₂]

/-! ### Filtered range `(range (n+1)).filter (λ x => decide (p x))` — nonempty / empty characterizations -/

/-- If `p k` holds for some `k ≤ n`, then filtering `range (n+1)` by `decide p` is nonempty. -/
lemma filter_range_succ_ne_nil_of_exists {n k : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hk : k ≤ n) (hp : p k) : (List.range (n + 1)).filter (λ a => decide (p a)) ≠ [] := by
  intro heq
  have hmem : k ∈ (List.range (n + 1)).filter (λ a => decide (p a)) :=
    (mem_range_succ_filter_iff.mpr ⟨hp, hk⟩)
  rw [heq] at hmem
  simp at hmem

/-- If no `k ≤ n` satisfies `p`, then filtering `range (n+1)` by `decide p` yields `[]`. -/
lemma filter_range_succ_eq_nil_of_forall_not {n : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (h : ∀ k, k ≤ n → ¬ p k) : (List.range (n + 1)).filter (λ a => decide (p a)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  rw [List.mem_filter] at hx
  rcases hx with ⟨hxr, hxd⟩
  rw [List.mem_range] at hxr
  exact h x (by omega) (of_decide_eq_true hxd)

/-! ### All pairs of indices in range — `subarrayIndices` -/

/-- Generate all pairs `(i, j)` with `i, j < n`. Useful for enumerating subarray endpoints
or any index-based traversal over a square grid. -/
def subarrayIndices (n : Nat) : List (Nat × Nat) :=
  List.product (List.range n) (List.range n)

lemma subarrayIndices_zero : subarrayIndices 0 = [] := by
  unfold subarrayIndices; rfl

/-! ### `find?` on `range` — finding the first satisfying element -/

/-- `List.find? p (List.range n) = some k` iff `k` is the smallest index `< n` with `p k = true`.

That is: `p k = true`, `k < n`, and for all `j < k`, `p j = false`. -/
lemma find?_range_eq_some_iff (p : Nat → Bool) {n k : Nat} :
    List.find? p (List.range n) = some k ↔ p k = true ∧ k < n ∧ ∀ j, j < k → p j = false := by
  constructor
  · -- forward: find? returns some k → k is the minimal satisfying index
    intro h
    induction' n with m ih generalizing k
    · simp at h
    · rw [List.range_succ, List.find?_append] at h
      cases h' : List.find? p (List.range m) with
      | some j =>
        simp [h'] at h
        have hk_eq_j : k = j := h.symm
        rw [hk_eq_j]
        rcases ih h' with ⟨hp, hj_lt_m, hj_forall⟩
        exact ⟨hp, Nat.lt_trans hj_lt_m (Nat.lt_succ_self m), hj_forall⟩
      | none =>
        simp [h'] at h
        rcases h with ⟨hpm, hm_eq_k⟩
        have hk_eq_m : k = m := hm_eq_k.symm
        rw [hk_eq_m]
        have h_forall : ∀ j, j < m → p j = false := by
          have hnone' := (List.find?_eq_none.mp h')
          intro j hj
          have hj_mem : j ∈ List.range m := List.mem_range.mpr hj
          have : ¬ p j = true := hnone' j hj_mem
          exact Bool.of_not_eq_true this
        exact ⟨hpm, Nat.lt_succ_self m, h_forall⟩
  · -- reverse: if k is the minimal satisfying index, find? returns some k
    rintro ⟨hp, hk_lt, h_forall⟩
    induction' n with m ih generalizing k
    · exact absurd hk_lt (Nat.not_lt_zero _)
    · rw [List.range_succ, List.find?_append]
      by_cases hkm : k < m
      · have h_find_m : List.find? p (List.range m) = some k := ih hp hkm h_forall
        simp [h_find_m]
      · have hk_eq_m : k = m := by omega
        rw [hk_eq_m] at hp h_forall ⊢
        have h_find_m_none : List.find? p (List.range m) = none := by
          apply (List.find?_eq_none.mpr)
          intro j hj_mem
          have hj_lt_m : j < m := List.mem_range.mp hj_mem
          intro htrue
          have hfalse : p j = false := h_forall j hj_lt_m
          rw [hfalse] at htrue
          exact Bool.false_ne_true htrue
        simp [h_find_m_none, hp]

/-- `List.find? p (List.range n) = none` iff `p j = false` for all `j < n`. -/
lemma find?_range_eq_none_iff (p : Nat → Bool) {n : Nat} :
    List.find? p (List.range n) = none ↔ ∀ j, j < n → p j = false := by
  constructor
  · intro h
    induction' n with m ih
    · intro j hj; exact absurd hj (Nat.not_lt_zero j)
    · rw [List.range_succ, List.find?_append] at h
      cases h' : List.find? p (List.range m) with
      | some val => simp [h'] at h
      | none =>
        simp [h'] at h
        intro j hj
        have h_le : j ≤ m := Nat.lt_succ_iff.mp hj
        rcases Nat.lt_or_eq_of_le h_le with (hj_lt_m | hj_eq_m)
        · exact ih h' j hj_lt_m
        · rw [hj_eq_m]; exact h
  · intro h
    apply (List.find?_eq_none.mpr)
    intro j hj_mem
    have hj_lt : j < n := List.mem_range.mp hj_mem
    have hfalse : p j = false := h j hj_lt
    intro htrue
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue

/-- If `List.find?` on `List.range len` returns `some t`, then for every `t' < t`,
the predicate is false. This is a convenient corollary of `find?_range_eq_some_iff`. -/
lemma find?_range_minimal (PB : Nat → Bool) (len t t' : Nat)
    (h : (List.range len).find? PB = some t) (hlt : t' < t) : PB t' = false :=
  ((find?_range_eq_some_iff PB).mp h).right.right t' hlt

/-- If `List.find? p (List.range n) = some k`, then `k < n`.
This is a convenient corollary of `find?_range_eq_some_iff` that uses
`List.mem_of_find?_eq_some` and `List.mem_range` for a direct proof. -/
lemma lt_of_find?_range_eq_some {p : Nat → Bool} {n k : Nat} (h : List.find? p (List.range n) = some k) : k < n := by
  have h_mem := List.mem_of_find?_eq_some h
  exact (List.mem_range.1 h_mem)

/-- If `List.find? p (List.range n) = none`, then `(List.range n).any p = false`.
This bridges `find?` and `any` semantics on ranges. -/
lemma find?_range_none_implies_any_false (p : Nat → Bool) {n : Nat} (h : List.find? p (List.range n) = none) :
    (List.range n).any p = false := by
  rw [List.any_eq_false]
  intro x hx_mem
  have hx_lt : x < n := List.mem_range.mp hx_mem
  have hx_false : p x = false := (find?_range_eq_none_iff p).mp h x hx_lt
  simpa [hx_false]

/-! ### Sum of filtered range -/

/-- Sum of all natural numbers in the closed interval `[0, n]` that satisfy
the `Bool`-valued predicate `p`. Expressed via `foldl` for direct match with
fold-based proof patterns.

This is a convenience specialization of `sumFilterMap` for `List.range (n + 1)`:
`sumFilterRange n p = sumFilterMap id p (List.range (n + 1))`. -/
def sumFilterRange (n : Nat) (p : Nat → Bool) : Nat :=
  ((List.range (n + 1)).filter p).foldl (fun acc i => acc + i) 0

/-! ### Membership in the product map of two ranges -/

/-- If `x < m` and `y < n`, then `f x y` belongs to the list generated by mapping `f`
over the Cartesian product `range m × range n`, flattened via `flatMap`.
This is the key lemma for proving that a candidate pair `(x, y)` appears in the
enumeration of all grid positions.

```lean
f x y ∈ ((List.range m).flatMap (λ x' => (List.range n).map (λ y' => f x' y'))) :=
  mem_range_product_map m n f x y hx hy
``` -/
lemma mem_range_product_map {α : Type} (m n : Nat) (f : Nat → Nat → α) (x y : Nat)
    (hx : x < m) (hy : y < n) :
    f x y ∈ ((List.range m).flatMap (λ x' =>
      (List.range n).map (λ y' => f x' y'))) := by
  rw [List.mem_flatMap]
  refine ⟨x, List.mem_range.mpr hx, ?_⟩
  rw [List.mem_map]
  refine ⟨y, List.mem_range.mpr hy, rfl⟩

/-! ### `getElem?`, `getElem`, and `getD` on `map f (range n)` -/

/-- For `i < n`, the `i`-th element of `List.map f (List.range n)` is `f i`.
This captures a common pattern: mapping a function over a range and then indexing. -/
lemma getElem?_map_range_eq_some {α : Type} (f : Nat → α) (n i : Nat) (hi : i < n) :
    (List.map f (List.range n))[i]? = some (f i) := by
  calc
    (List.map f (List.range n))[i]? = Option.map f ((List.range n)[i]?) :=
      List.getElem?_map f (List.range n) i
    _ = Option.map f (some i) := by rw [List.getElem?_range hi]
    _ = some (f i) := rfl

/-- The `i`-th element of `List.map f (List.range n)` is `f i`, given `i < n`.
This is the `getElem` (non-optional) version of `getElem?_map_range_eq_some`. -/
lemma getElem_map_range {α : Type} (f : Nat → α) (n i : Nat) (h : i < ((List.range n).map f).length) :
    ((List.range n).map f)[i] = f i := by
  have h_range_len : i < (List.range n).length := by
    simpa [List.length_map, List.length_range] using h
  calc
    ((List.range n).map f)[i] = f ((List.range n)[i]) :=
      List.getElem_map f (l := List.range n) (i := i) (h := h)
    _ = f i := by rw [List.getElem_range i h_range_len]

/-- For `i < n`, the `i`-th element (using `!` indexing) of `List.map f (List.range n)`
is `f i`. This is the `getElem!` variant of `getElem_map_range`, where the hypothesis
is `i < n` rather than a proof about the length of the mapped list. -/
lemma getElem_map_range! {α : Type u} [Inhabited α] (f : Nat → α) (n i : Nat) (h : i < n) :
    (List.map f (List.range n))[i]! = f i := by
  have hm : i < (List.map f (List.range n)).length := by
    simpa [List.length_map, List.length_range] using h
  have hr : i < (List.range n).length := by
    simpa [List.length_range] using h
  have h_eq : (List.map f (List.range n))[i]! = (List.map f (List.range n))[i] := by
    simp [(List.map f (List.range n)).getElem?_eq_getElem hm]
  rw [h_eq, List.getElem_map (f := f) (l := List.range n) (h := hm), List.getElem_range (h := hr)]

/-- For `i < n`, accessing the `i`-th element via `getD` of a list built by mapping `f`
over `List.range n` gives `f i`, regardless of the default value `d`.
This is the `getD` variant of `getElem_map_range`. -/
lemma getD_map_range_of_lt {α : Type u} (n i : Nat) (f : Nat → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [h]

/-- For `i < n`, `getD` on `List.range n` returns `i` itself.
This is a specialization of `getD_map_range_of_lt` with `f = id`. -/
lemma getD_range_of_lt (n i d : Nat) (h : i < n) : (List.range n).getD i d = i := by
  simpa using getD_map_range_of_lt n i id d h

/-- Looking up index `i` in a mapped `List.range'` gives `f (start + step * i)`.
This generalizes `getElem?_map_range_eq_some` to arbitrary `start` and `step`. -/
lemma getElem?_map_range'_eq_some {α : Type} (f : Nat → α) (start step len i : Nat) (h : i < len) :
    ((List.range' start len step).map f)[i]? = some (f (start + step * i)) := by
  simp [List.getElem?_map, List.getElem?_range' start step h]

/-! ### Nested `List.all` over `List.range` -/

/-- Bridging lemma for nested `List.all` on `List.range n` with `List.range n`:
    the double-`all` is equivalent to a double-`∀` over `i < n, j < n`. -/
lemma all_range_nested_iff {p : Nat → Nat → Bool} (n : Nat) :
    (List.all (List.range n) (λ i =>
      List.all (List.range n) (λ j => p i j))) = true ↔
    (∀ i, i < n → ∀ j, j < n → p i j = true) := by
  simp [List.all_eq_true, List.mem_range]

/-! ### Membership in mapped ranges -/

/-- Membership in the image of `List.range n` under `f` is equivalent to the existence
of an index `i < n` such that `f i = x`. This combines `List.mem_range` and `List.mem_map`,
providing the full `↔` generalizing `mem_map_range` which only gives the forward direction. -/
lemma mem_map_range_iff {α : Type u} (n : Nat) (f : Nat → α) (x : α) :
    x ∈ (List.range n).map f ↔ ∃ i, i < n ∧ f i = x := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    exact ⟨i, hi, rfl⟩
  · intro ⟨i, hi, h⟩
    apply List.mem_map.mpr
    have hi' : i ∈ List.range n := by rw [List.mem_range]; exact hi
    exact ⟨i, hi', h⟩

/-- Characterize membership in the image of a filtered range.
`b ∈ map f (filter p (range n))` iff there exists an index `i < n` such that
`p i = true` and `f i = b`. This combines `mem_map_range_iff` and `mem_range_filter_iff`
into a single `↔` for the common `map ∘ filter ∘ range` pipeline. -/
lemma mem_map_filter_range_iff {α : Type u} (f : Nat → α) (p : Nat → Bool) (n : Nat) (b : α) :
    b ∈ List.map f (List.filter p (List.range n)) ↔ ∃ i, i < n ∧ p i = true ∧ f i = b := by
  constructor
  · intro h
    rw [List.mem_map] at h
    rcases h with ⟨i, hi, h_eq⟩
    rw [List.mem_filter] at hi
    rcases hi with ⟨hi_range, hi_p⟩
    rw [List.mem_range] at hi_range
    subst h_eq
    exact ⟨i, hi_range, hi_p, rfl⟩
  · intro h
    rcases h with ⟨i, hi_range, hi_p, h_eq⟩
    rw [← h_eq]
    apply List.mem_map_of_mem
    rw [List.mem_filter]
    exact ⟨by rw [List.mem_range]; exact hi_range, hi_p⟩

/-! ### Non-emptiness of mapped ranges -/

/-- When `0 < n`, `(List.range n).map f` is nonempty. -/
lemma range_map_ne_nil {α : Type} (f : Nat → α) (n : Nat) (hn : 0 < n) :
    (List.range n).map f ≠ [] := by
  intro h
  have h' := List.map_eq_nil_iff.mp h
  rw [List.range_eq_nil] at h'
  omega

/-- The length of `(List.range n).map f` is `n`.
This is the exact-length version of `map_range_length_pos`. -/

lemma map_range_length {α : Type u} (f : Nat → α) (n : Nat) : ((List.range n).map f).length = n := by
  simp

/-- If `0 < n`, then `(List.range n).map f` has positive length.
This is the `0 < length` variant of `range_map_ne_nil`, convenient for use with
`List.maximum_of_length_pos` and similar length-positive hypotheses. -/
lemma map_range_length_pos {α : Type u} (n : Nat) (f : Nat → α) (hn : 0 < n) :
    0 < ((List.range n).map f).length := by
  simp [map_range_length, hn]

/-! ### `range_map_succ_shift` — shift decomposition of mapped range

Decompose `(range (k+1)).map (λ i => f (m + i))` into the head `f m`
followed by `(range k).map (λ i => f (m + 1 + i))`. This is the "shift-by-one"
counterpart of `map_range_succ_append`, useful for induction on the offset `m`. -/

/-- Decompose `(List.range (k+1)).map (λ i => f (m + i))` into `[f m]` followed by
the shifted tail `(List.range k).map (λ i => f (m + 1 + i))`. -/
lemma range_map_succ_shift {α : Type u} (f : Nat → α) (k m : Nat) :
    (List.range (k+1)).map (λ i => f (m + i)) =
    [f m] ++ (List.range k).map (λ i => f (m + 1 + i)) := by
  induction' k with k ih generalizing m
  · simp [List.range_succ]
  · calc
      (List.range (k+2)).map (λ i => f (m + i))
          = ((List.range (k+1)) ++ [k+1]).map (λ i => f (m + i)) := by simp [List.range_succ]
      _ = (List.range (k+1)).map (λ i => f (m + i)) ++ [f (m + (k+1))] := by simp
      _ = ([f m] ++ (List.range k).map (λ i => f (m + 1 + i))) ++ [f (m + (k+1))] := by rw [ih m]
      _ = [f m] ++ ((List.range k).map (λ i => f (m + 1 + i)) ++ [f (m + 1 + k)]) := by
        simp [add_comm, add_left_comm, add_assoc]
      _ = [f m] ++ (List.range (k+1)).map (λ i => f (m + 1 + i)) := by simp [List.range_succ]

/-! ### `range.any` ↔ `Fin` existential bridge -/

/-- If `(List.range n).any f` is true, there exists a `Fin n` index where `f` holds.
This is the `Fin`-based variant of `range_any_iff`; it is convenient when working with
`Fin n` index types (e.g., in array problems). -/
lemma exists_fin_of_any_range_true {n : Nat} {f : Nat → Bool} (h : (List.range n).any f = true) :
    ∃ (i : Fin n), f i.val = true := by
  rcases List.any_eq_true.mp h with ⟨i, hi_mem, hi_f⟩
  exact ⟨⟨i, List.mem_range.mp hi_mem⟩, hi_f⟩

/-- If there is a `Fin n` index where `f` holds, then `(List.range n).any f` is true.
Converse of `exists_fin_of_any_range_true`. -/
lemma any_range_true_of_exists_fin {n : Nat} {f : Nat → Bool} (h : ∃ (i : Fin n), f i.val = true) :
    (List.range n).any f = true := by
  rcases h with ⟨i, hi_f⟩
  apply List.any_eq_true.mpr
  exact ⟨i.val, List.mem_range.mpr i.is_lt, hi_f⟩

/-- `(List.range n).any f = true` iff there exists a `Fin n` index where `f` holds. -/
lemma any_range_true_iff_exists_fin {n : Nat} {f : Nat → Bool} :
    (List.range n).any f = true ↔ ∃ (i : Fin n), f i.val = true :=
  ⟨exists_fin_of_any_range_true, any_range_true_of_exists_fin⟩

/-- `(List.range n).any p = true` iff there exists `k < n` such that `p k = true`.
This is a direct bridge between `List.any` on a range and a plain existential over `Nat`.
It follows from `List.any_eq_true` and `List.mem_range`. -/
lemma any_range_iff {p : Nat → Bool} {n : Nat} :
    (List.range n).any p = true ↔ ∃ k < n, p k = true := by
  simp only [List.any_eq_true, List.mem_range]

/-! ### `rangeFromTo` — efficient inclusive range generator

`rangeFromTo start fin` produces `[start, start+1, …, fin]` using `List.range` and `map`,
which is more efficient than `rangeList` (which uses `filter` on the full range).
The two are extensionally equal; use whichever is most convenient for proofs. -/

/-- Generate the inclusive range `[start, start+1, …, fin]` via `range` + `map`.
This is an alternative to `rangeList` with a different computational representation. -/
def rangeFromTo (start fin : Nat) : List Nat :=
  (List.range (fin + 1 - start)).map (fun i => start + i)

/-- Membership in `rangeFromTo`: `n ∈ rangeFromTo start fin` iff `start ≤ n ∧ n ≤ fin`. -/
lemma mem_rangeFromTo_iff (n start fin : Nat) : n ∈ rangeFromTo start fin ↔ start ≤ n ∧ n ≤ fin := by
  unfold rangeFromTo
  simp only [List.mem_map, List.mem_range]
  constructor
  · intro ⟨i, hi, h_eq⟩
    have hi_bound : i ≤ fin - start := by omega
    rw [← h_eq]
    constructor
    · exact Nat.le_add_right start i
    · omega
  · intro ⟨h_start_n, h_n_fin⟩
    have h_sub : n - start < fin + 1 - start := by omega
    refine ⟨n - start, h_sub, ?_⟩
    omega

/-! ### `rangeInclusive` — inclusive range via `List.range'`

`rangeInclusive start fin` produces `[start, start+1, …, fin]` using `List.range'`.
When `start > fin`, returns the empty list `[]`.
This is a simpler implementation than `rangeFromTo` (which uses `range` + `map`),
and the two are extensionally equal. Use whichever is most convenient. -/

/-- Produce the inclusive range `[start, fin]` as a list.
Returns `[]` when `start > fin`. -/
def rangeInclusive (start fin : Nat) : List Nat :=
  List.range' start (fin + 1 - start)

/-- Membership in `rangeInclusive`: `n ∈ rangeInclusive start fin` iff `start ≤ n ∧ n ≤ fin`. -/

lemma mem_rangeInclusive_iff {start fin n : Nat} :
    n ∈ rangeInclusive start fin ↔ start ≤ n ∧ n ≤ fin := by
  simp [rangeInclusive, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    constructor
    · omega
    · omega
  · intro ⟨hle, hle'⟩
    refine ⟨n - start, ?_, ?_⟩
    · omega
    · omega

/-- `rangeInclusive start fin` contains no duplicate elements. -/
lemma nodup_rangeInclusive (start fin : Nat) : (rangeInclusive start fin).Nodup := by
  unfold rangeInclusive
  exact List.nodup_range' start (fin + 1 - start)

/-! ### `filteredInRange` — filter predicate on inclusive range

`filteredInRange pred start finish` returns elements in `[start, finish]` satisfying `pred`.
This is a convenience combining `rangeInclusive` with `List.filter`. -/

/-- Filter elements in the inclusive range `[start, finish]` that satisfy a boolean predicate. -/
def filteredInRange (pred : Nat → Bool) (start finish : Nat) : List Nat :=
  List.filter pred (rangeInclusive start finish)

/-- Membership in `filteredInRange` is equivalent to the predicate holding
and the element being within the inclusive bounds. -/
lemma mem_filteredInRange_iff (pred : Nat → Bool) (start finish n : Nat) :
    n ∈ filteredInRange pred start finish ↔ pred n ∧ start ≤ n ∧ n ≤ finish := by
  unfold filteredInRange
  simp only [List.mem_filter, mem_rangeInclusive_iff, and_assoc, and_comm, and_left_comm]

/-- A `filteredInRange` list never contains duplicates because `rangeInclusive` produces
distinct elements and `List.filter` preserves distinctness. -/
lemma nodup_filteredInRange (pred : Nat → Bool) (start finish : Nat) :
    (filteredInRange pred start finish).Nodup := by
  unfold filteredInRange
  apply List.Nodup.filter
  exact nodup_rangeInclusive start finish

/-! ### Membership bounds for `range'` with step=1

These lemmas provide direct `s ≤ a` / `a < s + n` bounds for membership in `List.range' s n`
when using the default step of 1. They complement the built-in `List.mem_range'` which
uses an existential form. -/

/-- If `a ∈ List.range' s n` (with default step=1), then `s ≤ a` and `a < s + n`. -/
lemma mem_range'_bounds {a s n : Nat} (h : a ∈ List.range' s n) : s ≤ a ∧ a < s + n := by
  rw [List.mem_range'] at h
  rcases h with ⟨i, hi, ha⟩
  have ha_eq : a = s + i := by omega
  rw [ha_eq]
  constructor
  · omega
  · omega

/-- If `s ≤ a` and `a < s + n`, then `a ∈ List.range' s n` (with default step=1). -/
lemma mem_range'_of_bounds {a s n : Nat} (hs : s ≤ a) (hl : a < s + n) : a ∈ List.range' s n := by
  rw [List.mem_range']
  have h_exists : a - s < n := by omega
  refine ⟨a - s, h_exists, ?_⟩
  omega

/-- If a list is sorted by `≤`, mapping `(start + ·)` over it preserves sortedness. -/
lemma sorted_map_add (start : Nat) (l : List Nat) (h : List.Sorted (· ≤ ·) l) :
    List.Sorted (· ≤ ·) (l.map (fun i => start + i)) := by
  induction' h with a l h₁ h₂ IH
  · simp
  · rw [List.map_cons]
    refine List.Pairwise.cons ?_ ?_
    · intro b hb
      rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
      have h_ax : a ≤ x := h₁ x hx
      omega
    · exact IH

/-- `rangeFromTo start fin` is sorted in non-decreasing order. -/
lemma sorted_rangeFromTo (start fin : Nat) : List.Sorted (· ≤ ·) (rangeFromTo start fin) := by
  unfold rangeFromTo
  apply sorted_map_add start (List.range (fin + 1 - start))
  exact List.sorted_le_range (fin + 1 - start)

/-- `rangeFromTo start fin` contains no duplicate elements. -/
lemma nodup_rangeFromTo (start fin : Nat) : List.Nodup (rangeFromTo start fin) := by
  unfold rangeFromTo
  refine List.Nodup.map (fun x y h => ?_) (List.nodup_range (fin + 1 - start))
  omega

/-- Filtering `rangeFromTo` with a Bool predicate: membership is equivalent to
the predicate holding and the number being in range. -/
lemma mem_filter_rangeFromTo_iff (p start fin : Nat) (P : Nat → Bool) :
    p ∈ ((rangeFromTo start fin).filter P) ↔ P p ∧ start ≤ p ∧ p ≤ fin := by
  rw [List.mem_filter, mem_rangeFromTo_iff]
  constructor
  · rintro ⟨⟨hs, he⟩, hp⟩; exact ⟨hp, hs, he⟩
  · rintro ⟨hp, hs, he⟩; exact ⟨⟨hs, he⟩, hp⟩

/-! ### `range'` sortedness -/

/-- `List.range' s n` is sorted in non-decreasing order (with default step=1). -/
lemma range'_sorted (s n : Nat) : List.Sorted (· ≤ ·) (List.range' s n) := by
  induction n generalizing s with
  | zero =>
    exact List.sorted_nil
  | succ n ih =>
    have h_eq : List.range' s (Nat.succ n) = s :: List.range' (s + 1) n := by
      simp [List.range']
    rw [h_eq, List.sorted_cons]
    constructor
    · intro b hb
      have hge := (mem_range'_bounds hb).left
      omega
    · exact ih (s + 1)

/-! ### `oneHot` — one-hot vector

A one-hot vector of length `n` with a `1` at position `i` and `0` elsewhere.
This is the list analogue of a one-hot encoding, commonly used in machine learning
and classification problems. -/

/-- Create a one-hot vector of length `n` with a `1` at position `i`.
For `j = i`, the entry is `1`; otherwise `0`.

Example: `oneHot 5 2 = [0, 0, 1, 0, 0]` -/
def oneHot (n i : Nat) : List Nat :=
  (List.range n).map (fun j => if j = i then 1 else 0)

/-- The length of `oneHot n i` is `n`. -/

lemma length_oneHot (n i : Nat) : (oneHot n i).length = n := by
  unfold oneHot; simp

/-- The element at index `i` of `oneHot n i` is `1` when `i < n`. -/
lemma getElem_oneHot_eq_one (n i : Nat) (h : i < n) : (oneHot n i)[i]! = 1 := by
  unfold oneHot; simp [h]

/-- The element at index `j ≠ i` of `oneHot n i` is `0` when `j < n`. -/
lemma getElem_oneHot_eq_zero (n i j : Nat) (hji : j ≠ i) (hjn : j < n) : (oneHot n i)[j]! = 0 := by
  unfold oneHot; simp [hji, hjn]

end List

namespace List

/-!
# Intervals: Insertion, Sorting, and Merging

Operations on lists of `Nat × Nat` intervals where each interval `(s, e)` satisfies `s ≤ e`.
An interval list is *sorted* when its elements are in non-decreasing order of their first
component (`a.1 ≤ b.1`).
-/

/-! ## Insertion and Sorting -/

/-- Insert an interval into a list sorted by the first component, keeping it sorted. -/
def insertInterval (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys =>
    if x.1 ≤ y.1 then
      x :: y :: ys
    else
      y :: insertInterval x ys

/-- Sort a list of intervals by their first component using insertion sort. -/
def sortIntervals (l : List (Nat × Nat)) : List (Nat × Nat) :=
  List.foldr insertInterval [] l

lemma insertInterval_mem (x : Nat × Nat) (l : List (Nat × Nat)) (p : Nat × Nat) :
    p ∈ insertInterval x l ↔ p = x ∨ p ∈ l := by
  induction' l with y ys ih generalizing x
  · simp [insertInterval]
  · simp [insertInterval]
    by_cases hcmp : x.1 ≤ y.1
    · simp [hcmp]
    · simp [hcmp, ih]
      tauto

lemma insertInterval_wellformed (x : Nat × Nat) (hx : x.1 ≤ x.2) (l : List (Nat × Nat))
    (hl : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) l) :
    List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) (insertInterval x l) := by
  induction' l with y ys ih generalizing x
  · simp [insertInterval, hx]
  · rw [List.forall_cons] at hl
    rcases hl with ⟨hy, hys⟩
    simp [insertInterval]
    by_cases hcmp : x.1 ≤ y.1
    · simp [hcmp, hx, hy, hys, List.forall_cons]
    · simp [hcmp, hy, List.forall_cons, ih _ hx hys]

lemma insertInterval_sorted (x : Nat × Nat) (l : List (Nat × Nat))
    (hsorted : List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) l) :
    List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) (insertInterval x l) := by
  induction' l with y ys ih generalizing x
  · simp [insertInterval]
  · rw [List.pairwise_cons] at hsorted
    rcases hsorted with ⟨hall, hpair⟩
    rcases y with ⟨ys', ye'⟩
    by_cases hcmp : x.1 ≤ ys'
    · have h_insert : insertInterval x ((ys', ye') :: ys) = x :: (ys', ye') :: ys := by
        simp [insertInterval, hcmp]
      rw [h_insert, List.pairwise_cons]
      constructor
      · intro a' ha'
        simp at ha'
        rcases ha' with (rfl | ha')
        · exact hcmp
        · exact le_trans hcmp (hall _ ha')
      · exact List.pairwise_cons.mpr ⟨hall, hpair⟩
    · have h_insert : insertInterval x ((ys', ye') :: ys) = (ys', ye') :: insertInterval x ys := by
        simp [insertInterval, hcmp]
      rw [h_insert, List.pairwise_cons]
      have hyx : ys' ≤ x.1 := Nat.le_of_not_ge hcmp
      constructor
      · intro a' ha'
        rw [insertInterval_mem x ys a'] at ha'
        rcases ha' with (rfl | ha')
        · exact hyx
        · exact hall _ ha'
      · exact ih x hpair

lemma sortIntervals_mem (l : List (Nat × Nat)) (p : Nat × Nat) :
    p ∈ sortIntervals l ↔ p ∈ l := by
  unfold sortIntervals
  induction' l with x xs ih
  · simp
  · simp [List.foldr, insertInterval_mem, ih]

lemma sortIntervals_wellformed (l : List (Nat × Nat))
    (hl : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) l) :
    List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) (sortIntervals l) := by
  unfold sortIntervals
  induction' l with x xs ih
  · simp
  · rw [List.forall_cons] at hl
    rcases hl with ⟨hx, hxs⟩
    have ih_res := ih hxs
    exact insertInterval_wellformed x hx (List.foldr insertInterval [] xs) ih_res

lemma sortIntervals_sorted (l : List (Nat × Nat)) :
    List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) (sortIntervals l) := by
  unfold sortIntervals
  induction' l with x xs ih
  · exact List.Pairwise.nil
  · have h : List.foldr insertInterval [] (x :: xs) = insertInterval x (List.foldr insertInterval [] xs) := by
      simp
    rw [h]
    exact insertInterval_sorted x (List.foldr insertInterval [] xs) ih

/-! ## Merging Overlapping Intervals

Given a list of intervals sorted by first component, merge overlapping adjacent intervals
into a list of pairwise-disjoint intervals that cover exactly the same set of points.
Uses a single linear pass; O(n) time complexity.
-/

/-- Auxiliary function for `mergeIntervalList`: given a current interval `(curS, curE)` and a
sorted `rest`, recursively merges overlapping subsequent intervals into the current one. -/
def mergeIntervalListAux (curS curE : Nat) (rest : List (Nat × Nat)) : List (Nat × Nat) :=
  match rest with
  | [] => [(curS, curE)]
  | (s', e') :: rs =>
    if s' ≤ curE then
      mergeIntervalListAux curS (Nat.max curE e') rs
    else
      (curS, curE) :: mergeIntervalListAux s' e' rs

/-- Merge a sorted list of intervals into a list of pairwise-disjoint intervals
that cover exactly the same points. Empty list maps to empty list. -/
def mergeIntervalList (l : List (Nat × Nat)) : List (Nat × Nat) :=
  match l with
  | [] => []
  | (s, e) :: t => mergeIntervalListAux s e t

lemma mergeIntervalList_wellformed (l : List (Nat × Nat))
    (h : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) l) :
    List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) (mergeIntervalList l) := by
  cases l with
  | nil => simp [mergeIntervalList]
  | cons hd tl =>
    rcases hd with ⟨s, e⟩
    simp [mergeIntervalList]
    rw [List.forall_cons] at h
    rcases h with ⟨hse, htl_wf⟩
    induction' tl with hd' tl' ih generalizing s e
    · simp [mergeIntervalListAux, hse]
    · rcases hd' with ⟨s', e'⟩
      rw [List.forall_cons] at htl_wf
      rcases htl_wf with ⟨hs'e'_wf, htl_wf'⟩
      by_cases hmerge : s' ≤ e
      · have h_eq : mergeIntervalListAux s e ((s', e') :: tl') =
            mergeIntervalListAux s (Nat.max e e') tl' := by
          simp [mergeIntervalListAux, hmerge]
        rw [h_eq]
        apply ih s (Nat.max e e') (le_trans hse (Nat.le_max_left _ _)) htl_wf'
      · have h_eq : mergeIntervalListAux s e ((s', e') :: tl') =
            (s, e) :: mergeIntervalListAux s' e' tl' := by
          simp [mergeIntervalListAux, hmerge]
        rw [h_eq]
        simp [hse, ih s' e' hs'e'_wf htl_wf']

lemma mergeIntervalListAux_pairwise (curS curE : Nat) (hle : curS ≤ curE) (rest : List (Nat × Nat))
    (hsorted : List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) rest)
    (hwf : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) rest) :
    List.Pairwise (fun a b : Nat × Nat => a.2 < b.1) (mergeIntervalListAux curS curE rest) := by
  have lower (rs : List (Nat × Nat)) (s e bound : Nat) (hs : bound ≤ s)
      (hr : ∀ p ∈ rs, bound ≤ p.1) : ∀ q ∈ mergeIntervalListAux s e rs, bound ≤ q.1 := by
    induction rs generalizing s e with
    | nil => simp [mergeIntervalListAux, hs]
    | cons p ps ih =>
      rcases p with ⟨a,b⟩
      have ht : ∀ p ∈ ps, bound ≤ p.1 := fun p hp => hr p (by simp [hp])
      rw [mergeIntervalListAux]
      split
      · exact ih s (max e b) hs ht
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hs
        · exact ih a b (hr (a,b) (by simp)) ht q hq
  induction rest generalizing curS curE with
  | nil => simp [mergeIntervalListAux]
  | cons p ps ih =>
    rcases p with ⟨s,e⟩
    rw [List.pairwise_cons] at hsorted
    rw [List.forall_cons] at hwf
    rw [mergeIntervalListAux]
    split
    · exact ih curS (max curE e) (hle.trans (le_max_left _ _)) hsorted.2 hwf.2
    · next hgap =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih s e hwf.1 hsorted.2 hwf.2⟩
      intro q hq
      exact (Nat.lt_of_not_ge hgap).trans_le (lower ps s e s le_rfl hsorted.1 q hq)

lemma mergeIntervalList_pairwise (l : List (Nat × Nat))
    (hsorted : List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) l)
    (hwf : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) l) :
    List.Pairwise (fun a b : Nat × Nat => a.2 < b.1) (mergeIntervalList l) := by
  cases l with
  | nil => simp [mergeIntervalList]
  | cons hd tl =>
    rcases hd with ⟨s, e⟩
    simp [mergeIntervalList]
    rw [List.forall_cons] at hwf
    rcases hwf with ⟨hse_wf, htl_wf⟩
    rw [List.pairwise_cons] at hsorted
    rcases hsorted with ⟨hsorted_head, hsorted_tail⟩
    exact mergeIntervalListAux_pairwise s e hse_wf tl hsorted_tail htl_wf

lemma mergeIntervalList_covers (l : List (Nat × Nat))
    (hsorted : List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) l)
    (hwf : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) l) (x : Nat) :
    (∃ p ∈ l, p.1 ≤ x ∧ x ≤ p.2) ↔ (∃ q ∈ mergeIntervalList l, q.1 ≤ x ∧ x ≤ q.2) := by
  have aux (rs : List (Nat × Nat)) (s e : Nat) (hse : s ≤ e)
      (hs : ∀ p ∈ rs, s ≤ p.1)
      (hso : List.Pairwise (fun a b : Nat × Nat => a.1 ≤ b.1) rs)
      (hw : List.Forall (fun p : Nat × Nat => p.1 ≤ p.2) rs) :
      (∃ p ∈ (s,e) :: rs, p.1 ≤ x ∧ x ≤ p.2) ↔
        (∃ q ∈ mergeIntervalListAux s e rs, q.1 ≤ x ∧ x ≤ q.2) := by
    induction rs generalizing s e with
    | nil => simp [mergeIntervalListAux]
    | cons p ps ih =>
      rcases p with ⟨a,b⟩
      rw [List.pairwise_cons] at hso
      rw [List.forall_cons] at hw
      have hsa := hs (a,b) (by simp)
      have hst : ∀ p ∈ ps, s ≤ p.1 := fun p hp => hs p (by simp [hp])
      rw [mergeIntervalListAux]
      split
      · next hover =>
        rw [← ih s (max e b) (hse.trans (le_max_left _ _)) hst hso.2 hw.2]
        simp only [List.mem_cons, exists_eq_or_imp, Prod.fst, Prod.snd]
        by_cases hr : ∃ p ∈ ps, p.1 ≤ x ∧ x ≤ p.2
        · simp [hr]
        · simp only [hr, or_false]
          have hab := hw.1
          change a ≤ b at hab
          change s ≤ a at hsa
          omega
      · simp only [List.mem_cons, exists_eq_or_imp, Prod.fst, Prod.snd]
        rw [← ih a b hw.1 hso.1 hso.2 hw.2]
        simp
  cases l with
  | nil => simp [mergeIntervalList]
  | cons p ps =>
    rcases p with ⟨s,e⟩
    rw [List.pairwise_cons] at hsorted
    rw [List.forall_cons] at hwf
    exact aux ps s e hwf.1 hsorted.1 hsorted.2 hwf.2

/-! ## Total Covered Length (Union Measure)

Given a list of intervals, sort by first component, merge overlapping ones,
and return the total length of the union. This is the core subroutine of
sweep-line algorithms for computing union area/measure.
-/

/-- Total covered length after merging overlapping intervals.
    Sorts intervals by their first component using merge sort,
    merges overlapping intervals in a single linear pass,
    and returns the sum of `end - start` for each merged disjoint interval. -/
def intervalsCoveredLength (intervals : List (Nat × Nat)) : Nat :=
  go (intervals.mergeSort (λ a b => decide (a.1 ≤ b.1)))
where
  go : List (Nat × Nat) → Nat
    | [] => 0
    | (y1, y2) :: rest => mergeAux y1 y2 rest
  mergeAux (curStart curEnd : Nat) : List (Nat × Nat) → Nat
    | [] => curEnd - curStart
    | (y1', y2') :: rest' =>
      if y1' ≤ curEnd then
        mergeAux curStart (max curEnd y2') rest'
      else
        (curEnd - curStart) + mergeAux y1' y2' rest'

end List

namespace List

/-! ### `List.Ico` filter lemmas

These lemmas characterize `filter` applied to `List.Ico a b`, the half-open
range of natural numbers `[a, b)`.
-/

/-- Membership in a `List.Ico` filtered by a decidable predicate is equivalent to
the predicate holding and the index being within the half-open interval `[a, b)`. -/
lemma mem_filter_Ico_iff (p : Nat → Prop) [DecidablePred p] (a b x : Nat) :
    x ∈ List.filter (fun n => decide (p n)) (List.Ico a b) ↔ p x ∧ a ≤ x ∧ x < b := by
  rw [List.mem_filter, List.Ico.mem]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hdec⟩
    exact ⟨of_decide_eq_true hdec, hlo, hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hlo, hhi⟩, decide_eq_true hp⟩

/-- Membership in a `List.Ico a (b+1)` filtered by a decidable predicate is equivalent to
the predicate holding and the index being in the inclusive range `[a, b]`. -/
lemma mem_filter_Ico_succ_iff (p : Nat → Prop) [DecidablePred p] (a b x : Nat) :
    x ∈ List.filter (fun n => decide (p n)) (List.Ico a (b + 1)) ↔ p x ∧ a ≤ x ∧ x ≤ b := by
  rw [mem_filter_Ico_iff p a (b + 1) x]
  constructor
  · rintro ⟨hp, hlo, hhi⟩; exact ⟨hp, hlo, by omega⟩
  · rintro ⟨hp, hlo, hhi⟩; exact ⟨hp, hlo, by omega⟩

/-- Filtering a `List.Ico` by a decidable predicate preserves `Nodup`. -/
lemma nodup_filter_Ico (p : Nat → Prop) [DecidablePred p] (a b : Nat) :
    (List.filter (fun n => decide (p n)) (List.Ico a b)).Nodup :=
  List.Nodup.filter (fun n => decide (p n)) (List.Ico.nodup a b)

/-- Filtering a `List.Ico` by a decidable predicate preserves sortedness (non-decreasing). -/
lemma sorted_filter_Ico (p : Nat → Prop) [DecidablePred p] (a b : Nat) :
    List.Sorted (· ≤ ·) (List.filter (fun n => decide (p n)) (List.Ico a b)) := by
  have h_lt : List.Sorted (· < ·) (List.Ico a b) := List.Ico.pairwise_lt a b
  exact (h_lt.le_of_lt).filter (fun n => decide (p n))

end List
