import Mathlib
import general.Common.Order
import general.List.IndexedAccess
import general.List.IndexedUpdate
import general.List.Slicing

namespace List

/-! ### Counting ordered pairs satisfying a predicate -/

/--
Counts the number of pairs `(j, k)` with `j < k` in the list `xs` such that
the boolean predicate `p` holds on the elements at those positions.
Uses `List.get!` with default value for out-of-bounds indexing (safe since
`j` and `k` range over valid indices).
-/
def countPairsWhere {α : Type} [Inhabited α] (xs : List α) (p : α → α → Bool) : Nat :=
  (List.range xs.length).foldl (fun acc j =>
    (List.range xs.length).foldl (fun acc' k =>
      if j < k then
        if p (xs[j]!) (xs[k]!) then acc' + 1 else acc'
      else acc'
    ) acc) 0

/-! ### Counting index pairs satisfying a predicate -/

/--
Counts the number of pairs of indices `(i, j)` with `0 ≤ i, j < n` such that
the boolean predicate `pred` holds on the indices.
Counts *all* pairs (including `i = j` and `j < i`), in contrast to
`countPairsWhere` which only counts `j < k` on list elements.
-/
def countIndexPairs (n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i =>
    acc + (List.range n).foldl (fun acc' j =>
      if pred i j then acc' + 1 else acc'
    ) 0
  ) 0

/-- Counts the number of index pairs `(i, j)` with `0 ≤ i < j < n` such that
the boolean predicate `pred` holds on the indices. Only counts strictly ordered
pairs (`i < j`), in contrast to `countIndexPairs` which counts all pairs.

This generalizes the common pattern of counting ordered index pairs in a list
without materializing the full Cartesian product. -/
def countOrderedIndexPairs (n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i =>
    acc + (List.range n).foldl (fun acc' j =>
      if i < j ∧ pred i j then acc' + 1 else acc'
    ) 0
  ) 0


lemma countOrderedIndexPairs_zero (pred : Nat → Nat → Bool) : countOrderedIndexPairs 0 pred = 0 := rfl

/-! ### Folding over all index pairs -/

/-- Left-fold a binary function `f` over all index pairs `(i, j)` with `0 ≤ i, j < n`.
This iterates over the full `n × n` Cartesian product of index positions:
`foldlIndexPairs n f init = f n-1 n-1 (… (f 0 1 (f 0 0 init)) …)`,
with the inner `j` loop varying fastest.

This generalizes `countIndexPairs` (which counts pairs satisfying a predicate)
and `countOrderedIndexPairs` (which counts ordered pairs). For any fold-based
computation over all index pairs, use this combinator directly instead of
materializing the Cartesian product as an intermediate list. -/
def foldlIndexPairs {α : Type} (n : Nat) (f : Nat → Nat → α → α) (init : α) : α :=
  (List.range n).foldl
    (fun acc i =>
      (List.range n).foldl
        (fun acc j => f i j acc)
        acc)
    init

/-! ### Counting all ordered pairs of list elements satisfying a predicate -/

/--
Counts the number of ordered pairs `(a, b)` with `a, b ∈ xs` such that
the boolean predicate `pred a b` holds. Uses `List.product xs xs` to
generate the full Cartesian product of `xs` with itself, filters by `pred`,
and returns the length.

This generalizes various pair-counting algorithms: the problem-specific
predicate is supplied as `pred`. Contrast with `countPairsWhere` which
only counts `j < k` pairs by position, and `countIndexPairs` which works
on index ranges `0..n-1`.
-/
def countFilteredPairs {α : Type} (xs : List α) (pred : α → α → Bool) : Nat :=
  List.length (List.filter (fun (a, b) => pred a b) (List.product xs xs))


theorem countFilteredPairs_def {α : Type} (xs : List α) (pred : α → α → Bool) :
    countFilteredPairs xs pred =
    List.length (List.filter (fun (a, b) => pred a b) (List.product xs xs)) :=
  rfl

/--
Counts all ordered pairs `(a, b)` drawn from `xs` (with replacement) such
that the boolean predicate `pred a b` holds. Uses nested `foldl` for efficient
O(n²) time / O(1) space computation, avoiding the intermediate `List.product xs xs`.

This is semantically equivalent to `countFilteredPairs` — it computes the same
result — but uses `foldl` which is more convenient for proofs that rely on
foldl induction.
-/
def countAllPairsWhere {α : Type} (xs : List α) (pred : α → α → Bool) : Nat :=
  xs.foldl (fun acc a => acc + xs.foldl (fun cnt b => if pred a b then cnt + 1 else cnt) 0) 0

/-! ### Counting pairs between two lists

`sumCountWhere pred xs ys` counts the total number of pairs `(x, y)` with
`x ∈ xs` and `y ∈ ys` such that `pred x y` holds. For each `x` in `xs`, it
counts how many `y` in `ys` satisfy `pred x y`, then sums those counts.

This generalizes `countFilteredPairs` to heterogeneous element types `α` and `β`,
and differs from `countPairsWhere` (above) which counts position-based pairs `j < k`
within a single list. -/

/--
`sumCountWhere pred xs ys` returns the total number of pairs `(x, y)` where
`x ∈ xs`, `y ∈ ys`, and `pred x y` is true. More precisely, for each `x` in `xs`,
it counts how many `y` in `ys` satisfy `pred x y`, then sums those counts.
-/
def sumCountWhere {α β : Type} (pred : α → β → Bool) : List α → List β → Nat
  | [], _ => 0
  | x :: xs, ys => (List.length (List.filter (pred x) ys)) + sumCountWhere pred xs ys


theorem sumCountWhere_nil {α β : Type} (pred : α → β → Bool) (ys : List β) :
    sumCountWhere pred [] ys = 0 := rfl


theorem sumCountWhere_cons {α β : Type} (pred : α → β → Bool) (x : α) (xs : List α) (ys : List β) :
    sumCountWhere pred (x :: xs) ys =
      (List.length (List.filter (pred x) ys)) + sumCountWhere pred xs ys := rfl

/--
`sumCountWhere` distributes over list concatenation in the first argument:
counting over `xs ++ xs'` equals the sum of counting over `xs` and `xs'` separately.
-/
theorem sumCountWhere_append {α β : Type} (pred : α → β → Bool) (xs xs' : List α) (ys : List β) :
    sumCountWhere pred (xs ++ xs') ys = sumCountWhere pred xs ys + sumCountWhere pred xs' ys := by
  induction xs with
  | nil => simp [sumCountWhere]
  | cons x xs ih => simp [sumCountWhere, ih, Nat.add_assoc]

/-! ### Collecting values from a 2D index grid with `Option` filtering -/

/-- Given two list lengths and a function from index pairs to optional values,
collect all values for index pairs `(i, j)` with `i < len1` and `j < len2`
where `f i j` returns `some v`.

This is a general combinator for iterating over a rectangular index grid
and collecting the results of a function that may return `none` for some pairs.
See `allIndexPairs_of_f` and `f_of_mem_allIndexPairs` for the membership
characterization. -/
def allIndexPairs (len1 len2 : Nat) (f : Nat → Nat → Option β) : List β :=
  (List.range len1).flatMap (λ i =>
    (List.range len2).filterMap (λ j => f i j))

/-- If `f i j = some v` and the indices are in bounds, `v` is in the collection. -/
lemma mem_allIndexPairs_of_f {len1 len2 : Nat} {f : Nat → Nat → Option β}
    {i j : Nat} {v : β} (hi : i < len1) (hj : j < len2) (hf : f i j = some v) :
    v ∈ allIndexPairs len1 len2 f := by
  unfold allIndexPairs
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨j, List.mem_range.mpr hj, ?_⟩
  rw [hf]

/-- If `v` is in the collection, there exist in-bounds indices `i`, `j` with `f i j = some v`. -/
lemma f_of_mem_allIndexPairs {len1 len2 : Nat} {f : Nat → Nat → Option β} {v : β}
    (h : v ∈ allIndexPairs len1 len2 f) : ∃ i j, i < len1 ∧ j < len2 ∧ f i j = some v := by
  unfold allIndexPairs at h
  rcases List.mem_flatMap.mp h with ⟨i, hi_mem, h_filter⟩
  have hi_bound : i < len1 := List.mem_range.mp hi_mem
  rcases List.mem_filterMap.mp h_filter with ⟨j, hj_mem, h_eq⟩
  have hj_bound : j < len2 := List.mem_range.mp hj_mem
  exact ⟨i, j, hi_bound, hj_bound, h_eq⟩

/-! ### All ordered index pairs -/

/-- Generate all ordered pairs of indices `(i, j)` with `0 ≤ i < n` and `0 ≤ j < n`.
This produces the full `n × n` Cartesian product as a flat `List (Nat × Nat)`.
For example, `indexPairs 2` yields `[(0,0),(0,1),(1,0),(1,1)]`.

Contrast with `subarrayIndexPairs` which filters to `i < j ≤ n`, and
`allIndexPairs` which maps index pairs through an `Option`-returning function. -/
def indexPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i =>
    (List.range n).map (fun j => (i, j))
  )

/-- Generate all strictly ordered index pairs `(i, j)` with `0 ≤ i < j < n`.
For example, `strictIndexPairs 3` yields `[(0,1),(0,2),(1,2)]`.

Contrast with `indexPairs` which produces the full `n × n` Cartesian product
(including `i = j` and `j < i`), and `subarrayIndexPairs` which allows `j = n`
(`i < j ≤ n` instead of `i < j < n`). -/
def strictIndexPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (λ i =>
    (List.range n).filter (λ j => i < j) |>.map (λ j => (i, j)))

/-- Membership characterization for `strictIndexPairs`:
`(i, j) ∈ strictIndexPairs n` iff `i < n ∧ j < n ∧ i < j`. -/

lemma mem_strictIndexPairs_iff {n i j : Nat} :
    (i, j) ∈ strictIndexPairs n ↔ i < n ∧ j < n ∧ i < j := by
  simp [strictIndexPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]

/-- Generate all ordered pairs `(i, j)` with both components in `[start, start+len-1]`.
This is `indexPairs len` shifted by `start`: each pair `(a, b)` from `indexPairs len`
becomes `(a + start, b + start)`.
For example, `orderedPairsFrom 1 3` yields `[(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]`. -/
def orderedPairsFrom (start len : Nat) : List (Nat × Nat) :=
  (List.range len).flatMap (fun i =>
    (List.range len).map (fun j => (i + start, j + start)))


lemma orderedPairsFrom_zero : orderedPairsFrom 0 n = indexPairs n := by
  unfold orderedPairsFrom indexPairs; simp

/-! ### Subarray index pairs -/

/-- Generate all index pairs `(i, j)` with `0 ≤ i < j ≤ n`, representing subarray intervals.
For example, `subarrayIndexPairs 2` yields `[(0,1),(0,2),(1,2)]`. -/
def subarrayIndexPairs (n : Nat) : List (Nat × Nat) :=
  let idxs : List Nat := List.range (n + 1)
  let pairs : List (Nat × Nat) :=
    idxs.flatMap (fun i => idxs.map (fun j => (i, j)))
  pairs.filter (fun ⟨i, j⟩ => i < j ∧ j ≤ n)

lemma subarrayIndexPairs_zero : subarrayIndexPairs 0 = [] := by
  unfold subarrayIndexPairs; simp

/-! ### Non-adjacent index pairs -/

/-- Generate all ordered index pairs `(i, j)` with `0 ≤ i < n`, `0 ≤ j < n`, and `i + 1 < j`.
This means `i` and `j` are not adjacent and there is at least one index strictly between them.
Useful for enumerating 3-part array split points where the middle segment must be non-empty.

For example, `nonAdjacentPairs 4` yields `[(0,2),(0,3),(1,3)]`.
Contrast with `allPairs` (List.lean) which only requires `i < j`, and `subarrayIndexPairs`
which requires `i < j ≤ n`. -/
def nonAdjacentPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i =>
    ((List.range n).filter (fun j => decide (i + 1 < j ∧ j < n))).map (fun j => (i, j)))


lemma nonAdjacentPairs_zero : nonAdjacentPairs 0 = [] := by
  simp [nonAdjacentPairs]

/-- Membership characterization: `(i, j) ∈ nonAdjacentPairs n` iff `i < n`, `j < n`, and `i + 1 < j`. -/
lemma mem_nonAdjacentPairs_iff (n i j : Nat) :
    (i, j) ∈ nonAdjacentPairs n ↔ i < n ∧ j < n ∧ i + 1 < j := by
  unfold nonAdjacentPairs
  constructor
  · intro h
    rcases List.mem_flatMap.mp h with ⟨i', hi, hmem⟩
    rcases List.mem_map.mp hmem with ⟨j', hj, hp⟩
    rcases List.mem_filter.mp hj with ⟨hj_range, hcond⟩
    have hi_range : i' < n := List.mem_range.mp hi
    have hj_range_val : j' < n := List.mem_range.mp hj_range
    have hcond_val : i' + 1 < j' ∧ j' < n := by
      simpa using hcond
    rcases hcond_val with ⟨hlt, hltn⟩
    rcases Prod.mk.inj hp with ⟨hi_eq, hj_eq⟩
    subst hi_eq; subst hj_eq
    exact ⟨hi_range, hj_range_val, hlt⟩
  · intro ⟨hi, hj, hcond⟩
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    apply List.mem_map.mpr
    refine ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, ?_⟩, rfl⟩
    simp [hcond, hj]

/-! ### All interval pairs (inclusive) -/

/-- Generate all interval pairs `(l, r)` such that `0 ≤ l ≤ r < n`.
Includes singleton intervals (`l = r`). For example, `allIntervals 2 = [(0,0),(0,1),(1,1)]`.
Contrast with `subarrayIndexPairs` which requires `l < r` (excludes singletons)
and allows `r = n`. -/
def allIntervals (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun l =>
    (List.range (n - l)).map (fun k => (l, l + k)))

/-! ### Pairwise distances between elements -/

/-- All pairwise distances (as natural numbers) between elements of a list.
For each element `i`, computes `j - i` for all later elements `j > i`, and
concatenates all these differences. This is useful for computing distances
between indices in a sorted (and nodup) list.

Example: `pairwiseDistances [1, 3, 6] = [2, 5, 3]` (differences: 3-1=2, 6-1=5, 6-3=3). -/
def pairwiseDistances (l : List Nat) : List Nat :=
  l.foldr (fun i acc =>
    let later := l.filter (fun j => j > i)
    let dists := later.map (fun j => j - i)
    dists ++ acc) []

/-! ### Unordered distinct pairs from list elements -/

/-- Generate all unordered distinct pairs `(a, b)` from a list, where each pair has `a` appearing
before `b` in the list. The pairs are unordered in the sense that only one of `(a,b)` and `(b,a)`
appears (the one where `a` comes first in the original list). For example:
`allDistinctPairs [1, 2, 3] = [(1, 2), (1, 3), (2, 3)]`. -/
def allDistinctPairs {α : Type} (xs : List α) : List (α × α) :=
  match xs with
  | [] => []
  | a :: rest =>
    (rest.map (λ b => (a, b))) ++ allDistinctPairs rest

/-- Every pair in `allDistinctPairs xs` consists of elements from `xs`. -/
lemma allDistinctPairs_mem {α : Type} (xs : List α) (p : α × α)
    (hp : p ∈ allDistinctPairs xs) : p.1 ∈ xs ∧ p.2 ∈ xs := by
  induction xs with
  | nil => exfalso; simp [allDistinctPairs] at hp
  | cons x xs ih =>
    unfold allDistinctPairs at hp
    rcases List.mem_append.mp hp with (hleft | hright)
    · rcases List.mem_map.mp hleft with ⟨b, hb, rfl⟩
      constructor
      · exact List.mem_cons_self x xs
      · exact List.mem_cons_of_mem x hb
    · rcases ih hright with ⟨hp1, hp2⟩
      constructor
      · exact List.mem_cons_of_mem x hp1
      · exact List.mem_cons_of_mem x hp2

/-- If `xs` has at least 2 elements, then `allDistinctPairs xs` is nonempty. -/
lemma allDistinctPairs_nonempty_of_length_ge_two {α : Type} (xs : List α) (h : xs.length ≥ 2) :
    allDistinctPairs xs ≠ [] := by
  cases xs with
  | nil => simp at h
  | cons x xs' =>
    cases xs' with
    | nil => simp at h
    | cons y rest => simp [allDistinctPairs]

/-! ### Maximum of a binary function over distinct pairs -/

/-- Maximum of `f a b` over all distinct pairs `(a, b)` drawn from a list, where `a` appears
before `b` in the list. Only one of `(a, b)` and `(b, a)` is considered (the one preserving
the original list order). Returns `0` for lists with fewer than 2 elements.

For example, `maxOverUnorderedPairs (fun a b => a + b) [1, 2, 3] = max (1+2) (max (1+3) (2+3)) = 5`. -/
def maxOverUnorderedPairs {α : Type} (f : α → α → Nat) : List α → Nat
  | [] => 0
  | [_] => 0
  | x :: rest => max ((rest.map (f x)).foldl Nat.max 0) (maxOverUnorderedPairs f rest)


lemma maxOverUnorderedPairs_nil {α : Type} (f : α → α → Nat) :
    maxOverUnorderedPairs f [] = 0 := rfl


lemma maxOverUnorderedPairs_singleton {α : Type} (f : α → α → Nat) (x : α) :
    maxOverUnorderedPairs f [x] = 0 := rfl

/-! ### All ordered triples from a domain list -/

/-- Generate all ordered triples `(a, b, c)` drawn from a domain list.
This is the 3-fold Cartesian product `domain × domain × domain` flattened to a `List`.
For example, `allTriples [0, 1]` yields
`[(0,0,0),(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0),(1,1,1)]`.

To generate all triples of indices `0..n-1`, use `allTriples (List.range n)`. -/
def allTriples (domain : List α) : List (α × α × α) :=
  domain.flatMap (fun i =>
    domain.flatMap (fun j =>
      domain.map (fun k => (i, j, k))))

/-- Membership in `allTriples domain`: `(a, b, c) ∈ allTriples domain` iff
each of `a`, `b`, `c` belongs to `domain`. -/
lemma mem_allTriples_iff {α : Type} [DecidableEq α] {domain : List α} {a b c : α} :
    (a, b, c) ∈ allTriples domain ↔ a ∈ domain ∧ b ∈ domain ∧ c ∈ domain := by
  constructor
  · intro h
    unfold allTriples at h
    rcases List.mem_flatMap.mp h with ⟨i, hi, h_mem⟩
    rcases List.mem_flatMap.mp h_mem with ⟨j, hj, h_mem'⟩
    rcases List.mem_map.mp h_mem' with ⟨k, hk, h_eq⟩
    -- h_eq : (i, (j, k)) = (a, (b, c)) since × is right-associative
    rcases Prod.mk.inj h_eq with ⟨hi_eq, hjk_eq⟩
    rcases Prod.mk.inj hjk_eq with ⟨hj_eq, hk_eq⟩
    subst hi_eq; subst hj_eq; subst hk_eq
    exact ⟨hi, hj, hk⟩
  · intro ⟨ha, hb, hc⟩
    unfold allTriples
    apply List.mem_flatMap.mpr
    refine ⟨a, ha, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨b, hb, ?_⟩
    apply List.mem_map.mpr
    exact ⟨c, hc, rfl⟩

/-! ### Existence of a triple satisfying a ternary predicate -/

/-- Check whether any triple `(a, b, c)` drawn from `lst` (allowing the same element to be picked multiple times) satisfies the ternary predicate `p a b c`.
This is a nested `List.any` over the same list, checking all `|lst|³` combinations. -/
def existsTripleSatisfying {α : Type} (lst : List α) (p : α → α → α → Bool) : Bool :=
  lst.any (fun a => lst.any (fun b => lst.any (fun c => p a b c)))

/-- Expand `existsTripleSatisfying` into an existential over list elements:
`existsTripleSatisfying lst p = true` iff there exist `a, b, c ∈ lst` with `p a b c = true`. -/
lemma existsTripleSatisfying_iff {α : Type} (lst : List α) (p : α → α → α → Bool) :
    existsTripleSatisfying lst p = true ↔
    ∃ a b c, a ∈ lst ∧ b ∈ lst ∧ c ∈ lst ∧ p a b c = true := by
  constructor
  · intro h
    unfold existsTripleSatisfying at h
    rw [List.any_eq_true] at h
    rcases h with ⟨a, ha, hrest⟩
    rw [List.any_eq_true] at hrest
    rcases hrest with ⟨b, hb, hrest⟩
    rw [List.any_eq_true] at hrest
    rcases hrest with ⟨c, hc, h⟩
    exact ⟨a, b, c, ha, hb, hc, h⟩
  · intro ⟨a, b, c, ha, hb, hc, h⟩
    unfold existsTripleSatisfying
    rw [List.any_eq_true]
    exact ⟨a, ha, by
      rw [List.any_eq_true]
      exact ⟨b, hb, by
        rw [List.any_eq_true]
        exact ⟨c, hc, h⟩⟩⟩

/-! ### Mapping a binary function over all unordered pairs -/

/-- Apply a binary function `f` to all unordered pairs (earlier element, later element)
in a list. For `[x₁, x₂, …, xₙ]` this yields `[f x₁ x₂, f x₁ x₃, …, f x₁ xₙ, f x₂ x₃, …]`.

This generalizes `allDistinctPairs` by directly applying `f` instead of constructing
`(a, b)` tuples. Equivalent to `(allDistinctPairs l).map (fun (a, b) => f a b)` but more
efficient since it avoids building the intermediate pair list. -/
def allPairsAux (f : α → α → β) : List α → List β
  | []        => []
  | x :: xs   => (xs.map (f x)) ++ allPairsAux f xs

theorem allPairsAux_nil (f : α → α → β) : allPairsAux f [] = [] := rfl

theorem allPairsAux_singleton (f : α → α → β) (a : α) : allPairsAux f [a] = [] := rfl

/-- If `z` is a "zero" element such that `f a b = z` iff `a = b`, then `z` does not appear in
`allPairsAux f l` when `l` has no duplicates. This is because `allPairsAux` only applies `f` to
distinct pairs (earlier element, later element), and `z` is only produced for equal pairs. -/
lemma allPairsAux_no_val_of_nodup {α β : Type} (f : α → α → β) (z : β)
    (hzero : ∀ a b, f a b = z ↔ a = b) (l : List α) (hnodup : List.Nodup l) :
    z ∉ allPairsAux f l := by
  induction l with
  | nil => simp [allPairsAux]
  | cons x xs ih =>
    have hx_nmem : x ∉ xs := List.Nodup.not_mem hnodup
    have hnodup_xs : List.Nodup xs := List.Nodup.of_cons hnodup
    simp only [allPairsAux, List.mem_append, List.mem_map]
    rw [not_or]
    constructor
    · simp only [List.mem_map, not_exists, not_and]
      intro y hy heq
      have hxy : x = y := ((hzero x y).mp heq)
      subst hxy
      exact hx_nmem hy
    · exact ih hnodup_xs

/-! ### Merge overlapping intervals with configurable gap -/

/-- One-step merge: given a current interval `(curL, curR)`, process the remaining
sorted list `lst`, accumulating merged intervals in `acc`. Intervals with start ≤ `curR + gap`
are merged; otherwise the current interval is finalized and a new one begins. -/
def mergeIntervalsAux (gap : Int) (curL curR : Int) (lst : List (Int × Int))
    (acc : List (Int × Int)) : List (Int × Int) :=
  match lst with
  | [] => (curL, curR) :: acc
  | (l', r') :: tl =>
    if l' ≤ curR + gap then
      let newR := if r' > curR then r' else curR
      mergeIntervalsAux gap curL newR tl acc
    else
      mergeIntervalsAux gap l' r' tl ((curL, curR) :: acc)

/-- Merge a sorted list of intervals, with a configurable gap tolerance.
Two intervals `(l₁, r₁)` and `(l₂, r₂)` with `l₁ ≤ l₂` are merged when `l₂ ≤ r₁ + gap`. -/
def mergeIntervalsWithGap (gap : Int) (xs : List (Int × Int)) : List (Int × Int) :=
  match xs with
  | [] => []
  | (l, r) :: rest => (mergeIntervalsAux gap l r rest []).reverse

/-- Merge sorted intervals where adjacent or overlapping intervals (gap ≤ 1) are combined. -/
def mergeIntervals (xs : List (Int × Int)) : List (Int × Int) :=
  mergeIntervalsWithGap 1 xs

/-! ### Collecting filtered pairs from two lists -/

/-- Collect results by taking the Cartesian product of `as` and `bs`, filtering by binary
predicate `p`, mapping via `f`, and deduplicating. This is the "list comprehension"
pattern: `{ f a b | a ∈ as, b ∈ bs, p a b }` without duplicates.

Generalized over any types `α`, `β`, `γ` with `DecidableEq γ` (needed for deduplication).
Only `DecidableEq γ` is required — `DecidableEq α` and `DecidableEq β` are not needed
since `List.product`, `List.filter` (with `Bool` predicate), and `List.map` are decidable-free. -/
def collectFilteredPairs {α β γ : Type} [DecidableEq γ]
    (as : List α) (bs : List β) (p : α → β → Bool) (f : α → β → γ) : List γ :=
  List.dedup (((List.product as bs).filter (λ ⟨a, b⟩ => p a b)).map (λ ⟨a, b⟩ => f a b))

/-- Membership in `collectFilteredPairs as bs p f` is equivalent to the existence of
`a ∈ as` and `b ∈ bs` such that `p a b` holds and `f a b = z`. This characterizes
the collected results as exactly the images under `f` of pairs satisfying the predicate. -/
theorem mem_collectFilteredPairs_iff {α β γ : Type} [DecidableEq γ]
    (as : List α) (bs : List β) (p : α → β → Bool) (f : α → β → γ) (z : γ) :
    z ∈ collectFilteredPairs as bs p f ↔
    (∃ a ∈ as, ∃ b ∈ bs, p a b ∧ f a b = z) := by
  dsimp [collectFilteredPairs]
  rw [List.mem_dedup]
  constructor
  · intro h
    rcases (List.mem_map (f := λ (x : α × β) => f x.1 x.2)).mp h with
      ⟨⟨a, b⟩, hmem, hz⟩
    rcases (List.mem_filter (p := λ (x : α × β) => p x.1 x.2)).mp hmem with ⟨hprod, hp⟩
    rcases (List.mem_product (l₁ := as) (l₂ := bs)).mp hprod with ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, hp, hz⟩
  · intro h
    rcases h with ⟨a, ha, b, hb, hp, hz⟩
    have hprod : (a, b) ∈ List.product as bs :=
      (List.mem_product (l₁ := as) (l₂ := bs)).mpr ⟨ha, hb⟩
    have hfilt : (a, b) ∈ ((List.product as bs).filter (λ ⟨a', b'⟩ => p a' b')) :=
      (List.mem_filter (p := λ (x : α × β) => p x.1 x.2)).mpr ⟨hprod, hp⟩
    exact (List.mem_map (f := λ (x : α × β) => f x.1 x.2)).mpr ⟨(a, b), hfilt, hz⟩

/-- `collectFilteredPairs as bs p f` always returns a list with no duplicates,
since it applies `List.dedup` as its final step. -/
theorem nodup_collectFilteredPairs {α β γ : Type} [DecidableEq γ]
    (as : List α) (bs : List β) (p : α → β → Bool) (f : α → β → γ) :
    List.Nodup (collectFilteredPairs as bs p f) := by
  dsimp [collectFilteredPairs]
  exact List.nodup_dedup _

/-! ### Non-overlapping consecutive pair grouping -/

/-- Group consecutive elements of a list into non-overlapping pairs.
`pairChunks [a, b, c, d] = [(a, b), (c, d)]`. A trailing element (if the list
has odd length) is dropped.

Contrast with `adjacentPairs` (from `List/Adjacent.lean`) which produces
*overlapping* adjacent pairs: `adjacentPairs [a, b, c] = [(a, b), (b, c)]`.
Contrast with `pairwiseMap` (from `List.lean`) which also slides by one. -/
def pairChunks {α : Type u} : List α → List (α × α)
  | a :: b :: xs => (a, b) :: pairChunks xs
  | _ => []


theorem pairChunks_nil {α : Type u} : pairChunks ([] : List α) = [] := rfl


theorem pairChunks_singleton {α : Type u} (a : α) : pairChunks [a] = [] := rfl


theorem pairChunks_cons {α : Type u} (a b : α) (xs : List α) :
    pairChunks (a :: b :: xs) = (a, b) :: pairChunks xs := rfl

/-- Length of `pairChunks l` is `l.length / 2` (floor division). -/
theorem pairChunks_length {α : Type u} : ∀ (l : List α), (pairChunks l).length = l.length / 2
  := by
  intro l
  match l with
  | [] => simp [pairChunks]
  | [_] => simp [pairChunks]
  | a :: b :: xs =>
    simp only [pairChunks_cons, List.length_cons, pairChunks_length xs]
    omega

/-- If `(a, b) ∈ pairChunks l`, then `a` and `b` both belong to `l`. -/
theorem mem_pairChunks {α : Type u} : ∀ {l : List α} {p : α × α},
    p ∈ pairChunks l → p.1 ∈ l ∧ p.2 ∈ l := by
  intro l p h
  match l with
  | [] => simp [pairChunks] at h
  | [_] => simp [pairChunks] at h
  | a :: b :: xs =>
    simp only [pairChunks_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have ih := mem_pairChunks h
      exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-! ### All unordered index pair values -/

/-- Generate `f i j` for all unordered index pairs `0 ≤ i < j < n`.
This is a general-purpose combinator: different problems supply different `f`.

For example, `allStrictPairValues (fun i j => i + j) 3 = [0+1, 0+2, 1+2]` (computed values
in the order `(0,1), (0,2), (1,2)`).

Contrast with `allPairsAux` which applies `f` to unordered pairs of **list elements**.
`allStrictPairValues` enumerates index positions `0 ≤ i < j < n` and applies `f` to the indices. -/
def allStrictPairValues (f : Nat → Nat → α) (n : Nat) : List α :=
  (List.range n).flatMap fun i =>
    (List.range (n - i - 1)).map fun d =>
      f i (i + 1 + d)

/-- For `0 ≤ i < j < n`, the value `f i j` is in `allStrictPairValues f n`.
This is the membership characterization: every unordered index pair is covered. -/
lemma allStrictPairValues_contains (f : Nat → Nat → α) (n : Nat) (i j : Nat) (hi : i < j) (hj : j < n) [BEq α] [LawfulBEq α] :
    (allStrictPairValues f n).contains (f i j) = true := by
  have hi_n : i < n := lt_trans hi hj
  have hmem : f i j ∈ allStrictPairValues f n := by
    unfold allStrictPairValues
    simp [List.mem_flatMap, List.mem_map, List.mem_range, hi_n]
    refine ⟨i, hi_n, j - i - 1, ?_, ?_⟩
    · omega
    · have hij : i + 1 + (j - i - 1) = j := by omega
      rw [hij]
  simpa [List.contains_eq_mem] using hmem

/-- The sum of `n - i - 1` for `i = 0..n-1` equals `n*(n-1)/2`.
This counts the number of unordered pairs `(i,j)` with `0 ≤ i < j < n`,
and is used to prove the length property of `allStrictPairValues`. -/
lemma sum_range_sub_identity (n : Nat) : ((List.range n).map fun i => n - i - 1).sum = n * (n - 1) / 2 := by
  induction' n with k ih
  · simp
  · rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    have hzero : (k + 1 - k - 1) = 0 := by omega
    rw [hzero, add_zero]
    have hsub : ∀ i, i ∈ List.range k → (k + 1) - i - 1 = (k - i - 1) + 1 := by
      intro i hi
      rw [List.mem_range] at hi
      omega
    rw [List.map_congr_left hsub, List.sum_map_add]
    simp [List.length_range, ih]
    calc
      k * (k - 1) / 2 + k = (Nat.choose k 2) + k := by rw [Nat.choose_two_right]
      _ = k + (Nat.choose k 2) := by omega
      _ = (Nat.choose k 1) + (Nat.choose k 2) := by simp [Nat.choose_one_right]
      _ = Nat.choose (k + 1) 2 := by rw [Nat.choose_succ_succ k 1]
      _ = (k + 1) * ((k + 1) - 1) / 2 := by rw [Nat.choose_two_right]
      _ = (k + 1) * k / 2 := by
        have hsub : (k + 1) - 1 = k := by omega
        rw [hsub]

/-! ### `allOrderedPairs` — all ordered pairs from a list

`allOrderedPairs xs` generates all ordered pairs `(x, y)` where `x, y ∈ xs`.
This is the full Cartesian product of `xs` with itself (including `(x, x)` and reversed pairs).

Contrast with `allPairs` (in `List.lean`) which only generates `(i, j)` with `0 ≤ i < j < n`,
and `allPairsLE` / `allPairsLT` (in `List.lean`) which filter by comparison. -/

/-- Generate all ordered pairs `(x, y)` where `x, y ∈ xs`.
This is the Cartesian product of `xs` with itself. -/
def allOrderedPairs {α : Type} (xs : List α) : List (α × α) :=
  xs.flatMap (fun x => xs.map (fun y => (x, y)))

/-- If `x, y ∈ xs`, then `(x, y) ∈ allOrderedPairs xs`. -/
lemma mem_allOrderedPairs {α : Type} (xs : List α) (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) :
    (x, y) ∈ allOrderedPairs xs := by
  unfold allOrderedPairs
  apply List.mem_flatMap.mpr
  refine ⟨x, hx, ?_⟩
  apply List.mem_map.mpr
  exact ⟨y, hy, rfl⟩

/-- If `p ∈ allOrderedPairs xs`, then `p.1 ∈ xs`. -/
lemma fst_allOrderedPairs_mem {α : Type} (xs : List α) (p : α × α) (hp : p ∈ allOrderedPairs xs) :
    p.1 ∈ xs := by
  unfold allOrderedPairs at hp
  rcases List.mem_flatMap.mp hp with ⟨x, hx, hx'⟩
  rcases List.mem_map.mp hx' with ⟨y, hy, rfl⟩
  exact hx

/-- If `p ∈ allOrderedPairs xs`, then `p.2 ∈ xs`. -/
lemma snd_allOrderedPairs_mem {α : Type} (xs : List α) (p : α × α) (hp : p ∈ allOrderedPairs xs) :
    p.2 ∈ xs := by
  unfold allOrderedPairs at hp
  rcases List.mem_flatMap.mp hp with ⟨x, hx, hx'⟩
  rcases List.mem_map.mp hx' with ⟨y, hy, rfl⟩
  exact hy

/-! ### Pair area: distance-weighted minimum of two elements

Given a list of values (heights, costs, etc.) and two indices `i`, `j`,
`pairArea vals i j` computes `(j - i) * min(vals[i], vals[j])`.
This is the core formula for the "container with most water" problem and
related two-pointer optimization problems where the objective is to maximize
`width × bounded(height_i, height_j)`.

`getD` with default `0` ensures out-of-bounds indices are handled safely,
though callers should ensure `i, j < vals.length`. -/

/-- Compute the area formed by two indices in a list:
`(j - i) * min(vals[i], vals[j])`. Uses `List.getD` with default `0`
for safe out-of-bounds access. When `j ≤ i`, the result is `0`
(since truncated subtraction gives `0`). -/
def pairArea (vals : List Nat) (i j : Nat) : Nat :=
  (j - i) * Nat.min (vals.getD i 0) (vals.getD j 0)

end List

namespace List

/-! ### `countOrderedPairsWhere` — count ordered pairs satisfying a predicate -/

/-- Count the number of ordered index pairs `(i, j)` with `i < j < xs.length`
such that the binary boolean predicate `p` holds on the list elements at those
positions: `p xs[i] xs[j]` is `true`.

This is a common pattern in algorithmic problems that ask "how many good pairs
are there?" where "good" means a relation on two distinct elements of an array
(considering ordered pairs, not just subsets). -/
def countOrderedPairsWhere {α : Type} (p : α → α → Bool) (xs : List α) : Nat :=
  let n := xs.length
  (((Finset.range n).product (Finset.range n)).filter (fun (i, j) =>
    checkPairWith p xs i j)).card

end List


namespace List

/-! ### Map on pairs -/

/-- If `p` is in the image of `fun a => (a, f a)` over `l`, then `p.2 = f p.1`. -/
lemma map_snd_eq_f_fst {α β : Type} (f : α → β) (l : List α) (p : α × β)
    (hp : p ∈ l.map (fun a => (a, f a))) : p.2 = f p.1 := by
  rcases List.mem_map.mp hp with ⟨a, _, rfl⟩
  simp

/-- `List.map Prod.fst (l.map (fun a => (f a, g a))) = l.map f`. -/
lemma map_fst_map_pair_eq_map_fst {α β γ : Type} (f : α → β) (g : α → γ) (l : List α) :
    List.map Prod.fst (l.map (fun a => (f a, g a))) = l.map f := by
  simp

/-- A value `a` appears as the first component of some pair in `l` iff `a` is in the
    image of `Prod.fst` over `l`. This characterizes key membership in an association list:
    `(∃ b, (a, b) ∈ l) ↔ a ∈ l.map Prod.fst`. -/
lemma mem_map_fst_iff {α β : Type} (l : List (α × β)) (a : α) :
    a ∈ l.map Prod.fst ↔ ∃ b, (a, b) ∈ l := by
  simp

/-- `(a, b) ∈ l.map (fun x => (x, f x)) ↔ a ∈ l ∧ b = f a`.
This characterizes membership in the image of `fun x => (x, f x)`,
a common pattern when building association lists or frequency maps. -/
lemma mem_map_mk_fun_iff {α β : Type} (l : List α) (f : α → β) (a : α) (b : β) :
    (a, b) ∈ l.map (fun x => (x, f x)) ↔ a ∈ l ∧ b = f a := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨x, hx, h_eq⟩
    have ha : x = a := (Prod.mk.inj h_eq).1
    have hb : f x = b := (Prod.mk.inj h_eq).2
    subst ha
    exact ⟨hx, hb.symm⟩
  · intro ⟨ha, hb⟩
    subst hb
    exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- If `s ∈ l`, then `(s, f s) ∈ l.dedup.map (fun x => (x, f x))`.
This is a dedup-aware version of the forward direction of `mem_map_mk_fun_iff`:
the deduplicated list still contains the pair for each element of the original list. -/
lemma mem_dedup_map_mk_fun {α β : Type} [DecidableEq α] (l : List α) (f : α → β)
    {s : α} (hs : s ∈ l) : (s, f s) ∈ l.dedup.map (fun x => (x, f x)) := by
  rw [mem_map_mk_fun_iff]
  exact ⟨by rw [List.mem_dedup]; exact hs, rfl⟩

/-- `(l.map (fun x => (x, f x))).map Prod.fst = l`.
Special case of `map_fst_map_pair_eq_map_fst` with `f := id`. -/

lemma map_fst_map_mk_fun {α β : Type} (l : List α) (f : α → β) :
    (l.map (fun x => (x, f x))).map Prod.fst = l := by
  rw [List.map_map]
  have h : Prod.fst ∘ (fun (x : α) => (x, f x)) = id := by
    ext x; simp
  rw [h, List.map_id]

/-- In a list of pairs `(x, f x)` built by mapping over `xs`,
equality of first components implies equality of the whole pair.
This holds because each first component `x` uniquely determines the pair `(x, f x)`. -/
lemma map_mk_fun_fst_eq_imp_eq [DecidableEq α] {β : Type u} (xs : List α) (f : α → β) :
    ∀ p ∈ xs.map (λ x => (x, f x)), ∀ q ∈ xs.map (λ x => (x, f x)), p.1 = q.1 → p = q := by
  intro p hp q hq heq
  rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
  rcases List.mem_map.mp hq with ⟨y, hy, rfl⟩
  have hxy : x = y := by simpa using heq
  subst hxy
  rfl

/-! ### `tagAll` — tag every element with a constant -/

/-- Tag every element of a list with a constant second component.
`tagAll tag xs = xs.map (λ x => (x, tag))`.
This is a common pattern when building association lists where each key gets the same value. -/
def tagAll {α β : Type} (tag : β) (xs : List α) : List (α × β) :=
  xs.map (λ x => (x, tag))

/-- Mapping `Prod.fst` over a `tagAll` recovers the original list.
This is a specialization of `map_fst_map_mk_fun` with a constant function. -/

lemma map_fst_tagAll {α β : Type} (tag : β) (xs : List α) :
    (tagAll tag xs).map Prod.fst = xs := by
  unfold tagAll
  exact map_fst_map_mk_fun xs (λ _ => tag)

/-- If an element is in the result of `tagAll`, its second component equals the tag.
This is a specialization of `map_snd_eq_f_fst` with a constant function. -/
lemma mem_tagAll_snd_eq {α β : Type} {tag : β} {xs : List α} {p : α × β}
    (hp : p ∈ tagAll tag xs) : p.snd = tag := by
  unfold tagAll at hp
  have := map_snd_eq_f_fst (λ _ : α => tag) xs p hp
  simpa using this

end List


namespace List

/-! ### All ordered pairs of indices -/

/-- Generate all ordered pairs `(i, j)` such that `0 ≤ i < j < n`. -/
def allPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i =>
    ((List.range n).filter (fun j => i < j)).map (fun j => (i, j)))

/-- Generate all ordered pairs `(i,j)` with `lo ≤ i < j ≤ hi`.
This generalizes `allPairs hi` (which is the special case `lo = 0`).
For `lo > hi`, returns `[]`. -/
def pairsInRange (lo hi : Nat) : List (Nat × Nat) :=
  (List.range (hi + 1)).flatMap (fun i =>
    if lo ≤ i then
      ((List.range (hi + 1)).filter (fun j => i < j)).map (fun j => (i, j))
    else [])

/-! ### All pairwise values (cartesian square of indices, mapped through `f`) -/

/-- Generate all values `f i j` for `0 ≤ i < n` and `0 ≤ j < n` in row-major order.
This is `[f 0 0, f 0 1, ..., f 0 (n-1), f 1 0, ..., f (n-1) (n-1)]`. -/
def allPairValues {α : Type} (n : Nat) (f : Nat → Nat → α) : List α :=
  let indices : List Nat := List.range n
  indices.flatMap (fun (i : Nat) =>
    (indices.map (fun (j : Nat) => f i j)))

/-- Membership in `allPairValues`: `f i j` is in the list iff `i < n` and `j < n`. -/
lemma mem_allPairValues {α : Type} {n : Nat} {f : Nat → Nat → α} {i j : Nat}
    (hi : i < n) (hj : j < n) : f i j ∈ allPairValues n f := by
  unfold allPairValues
  have hi_range : i ∈ List.range n := by
    rw [List.mem_range]
    exact hi
  have hj_range : j ∈ List.range n := by
    rw [List.mem_range]
    exact hj
  apply List.mem_flatMap.mpr
  refine ⟨i, hi_range, ?_⟩
  apply List.mem_map.mpr
  exact ⟨j, hj_range, rfl⟩

/-- If `n > 0`, then `allPairValues n f` is nonempty (its length is positive). -/
lemma allPairValues_length_pos {α : Type} {n : Nat} {f : Nat → Nat → α} (hn : 0 < n) :
    0 < (allPairValues n f).length := by
  have hmem : f 0 0 ∈ allPairValues n f := mem_allPairValues hn hn
  exact List.length_pos_of_mem hmem

/-- Membership in `allPairs`: `(i, j)` is in the list iff `i < j < n`. -/
lemma mem_allPairs_iff (i j n : Nat) : (i, j) ∈ allPairs n ↔ i < j ∧ j < n := by
  constructor
  · intro h
    unfold allPairs at h
    rcases List.mem_flatMap.mp h with ⟨i', hi', h_mem⟩
    rcases List.mem_map.mp h_mem with ⟨j', hj_filter, h_eq⟩
    rcases Prod.mk_inj.mp h_eq with ⟨rfl, rfl⟩
    have hi_len : i' < n := by
      simpa [List.mem_range] using hi'
    have hj_len : j' < n := by
      have : j' ∈ List.range n := (List.mem_filter.mp hj_filter).1
      simpa [List.mem_range] using this
    have hij : i' < j' := by
      simpa using (List.mem_filter.mp hj_filter).2
    exact ⟨hij, hj_len⟩
  · intro ⟨hij, hj⟩
    have hi : i < n := lt_trans hij hj
    unfold allPairs
    have hi_range : i ∈ List.range n := List.mem_range.mpr hi
    have hj_range : j ∈ List.range n := List.mem_range.mpr hj
    have hij_filter : j ∈ (List.range n).filter (fun k => i < k) := by
      simp [hj, hij]
    exact List.mem_flatMap.mpr ⟨i, hi_range, List.mem_map.mpr ⟨j, hij_filter, rfl⟩⟩

/-! ### All ordered pairs (non-strict, includes reflexive pairs) -/

/-- Generate all ordered pairs `(a, b)` from list `l` such that `a ≤ b`.
Includes reflexive pairs `(a, a)`.
Contrast with `allPairs` which requires `a < b` (strict). -/
def allPairsLE {α : Type _} [LinearOrder α] (l : List α) : List (α × α) :=
  (l ×ˢ l).filter (λ (a, b) => decide (a ≤ b))

/-- Membership in `allPairsLE`: `(a, b)` is in the list iff both `a` and `b` are in `l` and `a ≤ b`. -/
lemma mem_allPairsLE_iff {α : Type _} [LinearOrder α] {l : List α} {a b : α} :
    (a, b) ∈ allPairsLE l ↔ a ∈ l ∧ b ∈ l ∧ a ≤ b := by
  simp [allPairsLE, decide_eq_true_iff, and_assoc]

/-- `allPairsLE` preserves nodup: if `l` has no duplicates, neither does `allPairsLE l`. -/
lemma nodup_allPairsLE {α : Type _} [LinearOrder α] {l : List α} (h : List.Nodup l) :
    List.Nodup (allPairsLE l) := by
  dsimp [allPairsLE]
  apply List.Nodup.filter
  apply List.Nodup.product h h

/-! ### All ordered strict pairs from a list -/

/-- Generate all unordered pairs `(a, b)` from list `l` such that `a < b` (strict).
Contrast with `allPairsLE` which includes reflexive pairs `(a, a)`.
This is the element-level counterpart; see `allPairs` for index-level pairs. -/
def allPairsLT {α : Type} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (l : List α) : List (α × α) :=
  (List.product l l).filterMap (λ ⟨a,b⟩ => if a < b then some (a,b) else none)

/-- Membership in `allPairsLT`: `(x, y) ∈ allPairsLT l` iff both `x` and `y` are in `l` and `x < y`. -/
lemma mem_allPairsLT_iff {α : Type} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] {l : List α} {x y : α} :
    ((x, y) ∈ allPairsLT l) ↔ x ∈ l ∧ y ∈ l ∧ x < y := by
  simp [allPairsLT, List.mem_filterMap, List.mem_product, and_assoc]

end List


namespace List

/-! ### `allIntervalsUpTo` — all pairs (i, j) with i, j ≤ n -/

/-- Generate all pairs `(i, j)` where `0 ≤ i, j ≤ n`.
Useful for enumerating candidate intervals in list-based search problems. -/
def allIntervalsUpTo (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (n + 1)).map fun j => (i, j)

end List

namespace List

/-! ### Range-check predicate for lists of pairs -/

/-- `allPairsInRange pairs n` holds iff every pair `(a, b)` in `pairs` satisfies:
`a < n`, `b < n`, and `a ≠ b`. This is a common precondition for graph problems
where `n` is the number of nodes and pairs represent directed edges (no self-loops). -/
def allPairsInRange (pairs : List (Nat × Nat)) (n : Nat) : Prop :=
  ∀ p ∈ pairs, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2

end List
