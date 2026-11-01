import Mathlib

open List

namespace List

/-- Returns `1` if `as[i]` and `bs[j]` are both defined and equal, `0` otherwise.
This is the primitive building block for counting positional matches between two lists. -/
def matchCount {α : Type u} [DecidableEq α] (as bs : List α) (i j : Nat) : Nat :=
  match as[i]?, bs[j]? with
  | some a, some b => if a = b then 1 else 0
  | _, _ => 0

/-- For a fixed index `i`, sum `matchCount as bs i j` over all `j < j_end` with `j ≠ i`.
This is the inner loop of `countCrossMatches`: given one position `i` in the first list,
count how many distinct positions `j` in the second list have matching elements. -/
def countMatchesForI {α : Type u} [DecidableEq α] (as bs : List α) (i j_end : Nat) : Nat :=
  match j_end with
  | 0 => 0
  | j'+1 =>
    countMatchesForI as bs i j' +
    (if i ≠ j' then matchCount as bs i j' else 0)

/-- Count `matchCount as bs i j` for all ordered pairs with `i < i_end`, `j < n`, and `i ≠ j`.
Equivalently: the number of pairs of distinct indices where `as[i] = bs[j]`.

This appears in problems like CF 268A ("Games"): given home and away uniform colors,
count how many times a host wears a guest's away color (`home[i] = away[j]` for `i ≠ j`).

Example: `countCrossMatches [1,2,3] [3,1,2] 3 3 = 2` (matches at (0→1) and (1→2)). -/
def countCrossMatches {α : Type u} [DecidableEq α] (as bs : List α) (i_end n : Nat) : Nat :=
  match i_end with
  | 0 => 0
  | i'+1 =>
    countCrossMatches as bs i' n +
    countMatchesForI as bs i' n

/-- Count indices `i < len` where `s[i]? = some a` and `f[i]? = some b`.
Generalizes `count_add` (with `a=0, b=1`) and `count_remove` (with `a=1, b=0`)
from CF 1921B ("Arranging Cats").

Example: `countPairsEq [0,0,1,0] [1,1,0,0] 0 1 4 = 2` (indices 0 and 1 have `0→1`). -/
def countPairsEq {α : Type u} [DecidableEq α] (s f : List α) (a b : α) (len : Nat) : Nat :=
  match len with
  | 0 => 0
  | n + 1 => countPairsEq s f a b n +
    match s[n]?, f[n]? with
    | some sa, some fb => if sa = a ∧ fb = b then 1 else 0
    | _, _ => 0

/-- Swapping the lists and target values preserves the count:
`countPairsEq s f a b len = countPairsEq f s b a len`.
This generalizes `count_remove s f len = count_add f s len` from CF 1921B. -/
theorem countPairsEq_swap {α : Type u} [DecidableEq α] (s f : List α) (a b : α) (len : Nat) :
    countPairsEq s f a b len = countPairsEq f s b a len := by
  induction' len with n ih
  · rfl
  · rw [countPairsEq, countPairsEq]
    rw [ih]
    congr 1
    cases h₁ : s[n]? <;> cases h₂ : f[n]?
    · rfl
    · simp
    · simp
    · rename_i sa fb
      simp [h₁, h₂]
      by_cases ha : sa = a
      · subst ha
        by_cases hb : fb = b
        · subst hb; simp
        · simp [hb]
      · by_cases hb : fb = b
        · subst hb; simp [ha]
        · simp [ha, hb]

/-! ### Counting occurrences in nested lists

`countNestedEqInPrefix ls idx target k` counts how many times `target` appears at
inner index `idx` among the first `k` entries of the nested list `ls`. This generalizes
row/column counting in a list of index pairs (e.g., LeetCode 1252).

Example: `countNestedEqInPrefix [[1,0], [0,1], [1,1]] 0 1 3 = 2` (rows with `1` at
column 0 in the first 3 entries). -/

/-- Counts how many times `target` appears at position `idx` in the inner lists of
the first `k` entries of `ls`. -/
def countNestedEqInPrefix {α : Type u} [DecidableEq α] (ls : List (List α)) (idx : Nat) (target : α) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    countNestedEqInPrefix ls idx target k +
    if ((ls[k]?).bind fun inner => inner[idx]?) = some target then 1 else 0

/-- Count how many elements of `s` are strictly less than `val`.
Requires `LT α` and a decidable `<` relation.

Example: `countLessThan [3, 1, 4, 1, 5] 4 = 3` (1, 3, 1 are < 4). -/
def countLessThan {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (s : List α) (val : α) : Nat :=
  s.countP (· < val)

/-- Count how many elements of `s` are at least `val`.
Requires `LE α` and a decidable `≤` relation.

This appears in problems like LeetCode 274 ("H-Index"), where you count how many
papers have at least `h` citations.

Example: `countAtLeast [3, 1, 4, 1, 5] 4 = 2` (4 and 5 are ≥ 4). -/
def countAtLeast {α : Type u} [LE α] [DecidableRel (α := α) (· ≤ ·)] (s : List α) (val : α) : Nat :=
  s.countP (val ≤ ·)

/-- `countAtLeast s val ≤ s.length`. Each element contributes at most 1 to the count. -/
lemma countAtLeast_le_length {α : Type u} [LE α] [DecidableRel (α := α) (· ≤ ·)] (s : List α) (val : α) :
    countAtLeast s val ≤ s.length := by
  unfold countAtLeast
  exact List.countP_le_length (val ≤ ·) (l := s)

/-! ### Counting predicate matches in a range

`countPInRange p s l r` counts how many elements in `s[l..r)` (inclusive-exclusive)
satisfy the boolean predicate `p`. Uses `s[i]?` for safe indexed access; out-of-bounds
indices return `none` and contribute `0`. Returns `0` when `l ≥ r`.

This generalizes `count_zeros` (counting zeros in a list segment) to any boolean
predicate. Useful for sliding-window algorithms where you need to count elements
meeting a condition within a variable-length window. -/

/-- Count elements in `s[l..r)` satisfying predicate `p`.
Uses `s[i]?` for safe indexed access; out-of-bounds indices return `none` and contribute `0`.
Returns `0` when `l ≥ r`. -/
def countPInRange {α : Type u} (p : α → Bool) (s : List α) (l r : ℕ) : ℕ :=
  if l < r then
    (match s[l]? with | some a => (if p a then 1 else 0) | none => 0) + countPInRange p s (l + 1) r
  else
    0
termination_by r - l
decreasing_by
  omega

/-! ### Counting occurrences in a prefix

`countPrefix xs a d n` counts how many times `a` appears in the first `n` elements
of `xs`, using `d` as the default value for out-of-bounds access (via `getD`). -/

/-- Count occurrences of value `a` in the first `n` elements of list `xs`,
    using `d` for out-of-bounds index access. -/
def countPrefix {α : Type} [DecidableEq α] (xs : List α) (a d : α) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => countPrefix xs a d k + (if (xs[k]?).getD d = a then 1 else 0)

/-- Recurrence: `countPrefix` for `n+1` decomposes into the count for `n`
    plus a match check at position `n`. -/
lemma countPrefix_succ {α : Type} [DecidableEq α] (xs : List α) (a d : α) (n : Nat) :
    countPrefix xs a d (n + 1) = countPrefix xs a d n + (if (xs[n]?).getD d = a then 1 else 0) := rfl

/-! ### `countVal` — counting occurrences up to index `n`

`countVal val s n` counts how many times `val` appears in the first `n` elements
of `s` (i.e., `s[0]`, `s[1]`, …, `s[n-1]`). Uses direct `Option` comparison with
`s[i]?` instead of `getD`; this avoids the need for a dummy default value.

Unlike `countPrefix`, which requires a default value `d` for out-of-bounds access
via `getD`, `countVal` uses `Option` equality (`s[i]? = some val`), which is more
idiomatic Lean. For indices `i < s.length` the two definitions are equivalent. -/

/-- Count occurrences of `val` in the first `n` elements of `s`.
Returns `0` for `n = 0`. Each step checks `s[n-1]? = some val`. -/
def countVal {α : Type} [DecidableEq α] (val : α) (s : List α) : ℕ → ℕ
  | 0 => 0
  | n+1 => countVal val s n + (if s[n]? = some val then 1 else 0)

/-- The count up to index `n` is bounded by `n`: `countVal val s n ≤ n`.
This is immediate since each of the `n` elements contributes at most `1`. -/
lemma countVal_le {α : Type} [DecidableEq α] (val : α) (s : List α) (n : ℕ) :
    countVal val s n ≤ n := by
  induction' n with n ih
  · simp [countVal]
  · unfold countVal
    have hterm : (if s[n]? = some val then 1 else 0) ≤ 1 := by
      split <;> omega
    omega

/-! ### `countBetween` — counting elements in a prefix between two bounds

`countBetween s lo hi e` counts how many of the first `e` elements of `s` are
strictly between `lo` and `hi`. Uses `s[i]?` for safe indexed access; out-of-bounds
indices return `none` and contribute `0`.

This pattern appears in problems like LeetCode 2148 ("Count Elements With Strictly
Smaller and Greater Elements"), where you count elements that are strictly between
the minimum and maximum of a list.

Example: `countBetween [1, 2, 3, 4, 5] 2 5 4 = 2` (3 and 4 are between 2 and 5). -/

/-- Count how many of the first `e` elements of `s` are strictly between `lo` and `hi`.
That is, count `i < e` such that `lo < s[i] < hi`. -/
def countBetween {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (s : List α) (lo hi : α) : ℕ → ℕ
  | 0 => 0
  | e+1 =>
    countBetween s lo hi e +
    (match s[e]? with
     | some cur => if lo < cur ∧ cur < hi then 1 else 0
     | none => 0)

/-- `countBetween` is always nonnegative (trivial since the return type is `ℕ`). -/
lemma countBetween_nonneg {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (s : List α) (lo hi : α) (e : ℕ) :
    0 ≤ countBetween s lo hi e := Nat.zero_le _

/-- `countBetween` is bounded above by the number of elements considered:
`countBetween s lo hi e ≤ e`. -/
lemma countBetween_le {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (s : List α) (lo hi : α) (e : ℕ) :
    countBetween s lo hi e ≤ e := by
  induction e with
  | zero => simp [countBetween]
  | succ e ih =>
    rw [countBetween]
    have hterm : (match s[e]? with
      | some cur => if lo < cur ∧ cur < hi then 1 else 0
      | none => 0) ≤ 1 := by
      cases h : s[e]?
      · simp
      · simp
        split <;> omega
    omega

/-- Combined bounds for `countBetween`: it is between `0` and `e` inclusive. -/
lemma countBetween_bounds {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (s : List α) (lo hi : α) (e : ℕ) :
    0 ≤ countBetween s lo hi e ∧ countBetween s lo hi e ≤ e :=
  ⟨countBetween_nonneg s lo hi e, countBetween_le s lo hi e⟩

/-! ### `countFrom` — counting occurrences in a suffix

`countFrom xs target idx` counts how many times `target` appears in the suffix
`xs[idx..]`, i.e., in `List.drop idx xs`. This is the suffix counterpart of
`countVal`/`countPrefix`, which count in prefixes.

Useful when you need to count occurrences of a value starting from a given position
(e.g., checking how many of a certain element appear after the current index). -/

/-- Count occurrences of `target` in the suffix of `xs` starting at index `idx`.
Equivalent to `List.count target (List.drop idx xs)`. -/
def countFrom {α : Type u} [DecidableEq α] (xs : List α) (target : α) (idx : Nat) : Nat :=
  List.count target (List.drop idx xs)

/-- Counting from an empty list always returns `0`, regardless of `target` and `idx`. -/
@[simp]
theorem countFrom_nil {α : Type u} [DecidableEq α] (target : α) (idx : Nat) :
    countFrom [] target idx = 0 := by
  simp [countFrom]

/-! ### Counting ordered triples

`countTriples`, `countTriplesJK`, and `countTriplesK` form a nested family
for counting ordered triples of indices `(i, j, k)` with `i < j < k` such that
a ternary predicate `p` holds on the corresponding list elements. The three
functions represent the three nested loops: outermost `i`, middle `j`, innermost `k`.

These appear in problems like LeetCode 2367 ("Number of Arithmetic Triplets")
where you count triples satisfying arithmetic difference constraints.
-/

/-- Innermost loop: for fixed `(i, j)`, count triples with index `k` ranging from
`start_k` to the end of `s` where `p` holds on `(s[i], s[j], s[k])`.

Typically called with `start_k = j + 1` to enforce `i < j < k`. -/
def countTriplesK {α : Type u} (s : List α) (default : α) (p : α → α → α → Prop)
    [∀ a b c, Decidable (p a b c)] (i j start_k : Nat) : Nat :=
  if _ : start_k < s.length then
    (if p ((s[i]?).getD default) ((s[j]?).getD default) ((s[start_k]?).getD default) then 1 else 0) +
    countTriplesK s default p i j (start_k + 1)
  else 0
termination_by s.length - start_k
decreasing_by omega

/-- Middle loop: for a fixed `i`, count triples with `j` ranging from `start_j`
and for each `j`, count triples with `k > j` via `countTriplesK`.

Typically called with `start_j = i + 1` to enforce `i < j`. -/
def countTriplesJK {α : Type u} (s : List α) (default : α) (p : α → α → α → Prop)
    [∀ a b c, Decidable (p a b c)] (i start_j : Nat) : Nat :=
  if _ : start_j < s.length then
    countTriplesK s default p i start_j (start_j + 1) +
    countTriplesJK s default p i (start_j + 1)
  else 0
termination_by s.length - start_j
decreasing_by omega

/-- Outermost loop: count all ordered triples `(i, j, k)` with `i < j < k` in `s`
satisfying the ternary predicate `p`. Iterates `i` from `start_i`, for each `i`
delegates to `countTriplesJK` with `j` starting from `i + 1`.

Typically called with `start_i = 0` to count all triples in the whole list. -/
def countTriples {α : Type u} (s : List α) (default : α) (p : α → α → α → Prop)
    [∀ a b c, Decidable (p a b c)] (start_i : Nat) : Nat :=
  if _ : start_i < s.length then
    countTriplesJK s default p start_i (start_i + 1) +
    countTriples s default p (start_i + 1)
  else 0
termination_by s.length - start_i
decreasing_by omega

/-! ### `countLtInPrefix` — counting elements less than `x` in a prefix

`countLtInPrefix xs x n` counts how many elements among the first `n` elements
of `xs` are strictly less than `x`. Uses `xs[i]?` for safe indexed access;
out-of-bounds indices return `none` and contribute `0`.

This generalizes the `count_lt` pattern that appears in problems like LeetCode 2860
("Happy Students"), where you need to count how many numbers in a prefix are less
than a target value. Unlike `countLessThan` which counts the entire list,
`countLtInPrefix` is bounded to a prefix, making it useful for algorithms that
iterate through prefixes of a list.
-/

/-- Count how many elements among the first `n` elements of `xs` are less than `x`.
Uses `xs[i]?` for safe indexed access; out-of-bounds indices contribute `0`. -/
def countLtInPrefix {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (xs : List α) (x : α) : ℕ → ℕ
  | 0 => 0
  | n+1 => countLtInPrefix xs x n + (match xs[n]? with | some y => if y < x then 1 else 0 | none => 0)

/-- Base case: counting in an empty prefix returns `0`. -/
@[simp]
theorem countLtInPrefix_zero {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (xs : List α) (x : α) :
    countLtInPrefix xs x 0 = 0 := rfl

/-- Recurrence unfolding for `countLtInPrefix` at `n+1`. -/
theorem countLtInPrefix_succ {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (xs : List α) (x : α) (n : ℕ) :
    countLtInPrefix xs x (n+1) = countLtInPrefix xs x n +
    (match xs[n]? with | some y => if y < x then 1 else 0 | none => 0) := rfl

/-- `countLtInPrefix` is bounded above by the number of elements considered:
    `countLtInPrefix xs x n ≤ n`. -/
theorem countLtInPrefix_le {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (xs : List α) (x : α) (n : ℕ) :
    countLtInPrefix xs x n ≤ n := by
  induction' n with n ih
  · simp [countLtInPrefix]
  · rw [countLtInPrefix_succ]
    have hterm : (match xs[n]? with | some y => if y < x then 1 else 0 | none => 0) ≤ 1 := by
      cases xs[n]? <;> simp
      split <;> omega
    omega

/-- `countLtInPrefix` is monotone in the prefix length: if `i ≤ j` then
    `countLtInPrefix xs x i ≤ countLtInPrefix xs x j`. -/
theorem countLtInPrefix_mono {α : Type u} [LT α] [DecidableRel (α := α) (· < ·)] (xs : List α) (x : α) (i j : ℕ)
    (h : i ≤ j) : countLtInPrefix xs x i ≤ countLtInPrefix xs x j := by
  induction' h with k h ih
  · rfl
  · rw [countLtInPrefix_succ]
    exact le_trans ih (Nat.le_add_right _ _)

/-! ### `countGtAccum` — counting elements exceeding a running counter

`countGtAccum bp tested` starts with counter `tested` and walks through `bp`.
For each element `x`, if `x > tested`, the counter increments by `1`.
Returns the final counter value.

This captures the core logic of LeetCode 2960 ("Count Tested Devices After Test
Operations") where a device can be tested if its battery percentage exceeds the
number of devices already tested. The generalization to any `LinearOrderedRing α`
makes it reusable across numeric domains (ℤ, ℚ, ℝ, etc.).

Example:
  `countGtAccum [1, 1, 2, 1, 3] 0 = 3` — elements > 0: 1 (now 1), 2 > 1 (now 2),
  3 > 2 (now 3), but the second 1 ≤ 2 and the third 1 ≤ 3 are skipped.
-/

/-- Walk through `bp` with a running counter `tested`. For each element `x`,
if `x > tested` then increment the counter (`tested := tested + 1`).
Returns the final counter value. -/
def countGtAccum {α : Type} [LinearOrderedRing α] (bp : List α) (tested : α) : α :=
  match bp with
  | [] => tested
  | x :: xs =>
    if x > tested then
      countGtAccum xs (tested + 1)
    else
      countGtAccum xs tested

/-- `countGtAccum [] tested = tested`. -/
@[simp]
lemma countGtAccum_nil {α : Type} [LinearOrderedRing α] (tested : α) :
    countGtAccum [] tested = tested := rfl

/-- Recurrence for `countGtAccum` on a cons list. -/
lemma countGtAccum_cons {α : Type} [LinearOrderedRing α] (x : α) (xs : List α) (tested : α) :
    countGtAccum (x :: xs) tested =
    (if x > tested then countGtAccum xs (tested + 1) else countGtAccum xs tested) := rfl

/-- Uniqueness lemma: any function `f` satisfying the same recurrence as `countGtAccum`
is equal to `countGtAccum`. Useful for proving equivalence with alternative
definitions (e.g., a specification written with explicit `if`/`else` branches
like `spec_count_tested` from LeetCode 2960). -/
lemma countGtAccum_eq_of_rec_eq {α : Type} [LinearOrderedRing α]
    (f : List α → α → α)
    (h_nil : ∀ t, f [] t = t)
    (h_cons : ∀ x xs t, f (x :: xs) t = (if x > t then f xs (t + 1) else f xs t))
    (bp : List α) (tested : α) :
    countGtAccum bp tested = f bp tested := by
  induction bp generalizing tested with
  | nil => rw [countGtAccum_nil, h_nil tested]
  | cons x xs ih =>
    rw [countGtAccum_cons, h_cons x xs tested]
    split <;> apply ih

/-- Convenience: `countGtAccum` starting from `0`. This is the most common use case:
count how many elements are strictly greater than the running count of
previously-selected elements. -/
def countGtAccumFromZero {α : Type} [LinearOrderedRing α] (bp : List α) : α :=
  countGtAccum bp 0

/-! ### `countBy_specificDuplicate` — counting elements satisfying a `Prop` predicate

`countBy_specificDuplicate p xs` counts how many elements of `xs` satisfy the decidable
proposition `p`. This is the `Prop`-based counterpart of mathlib's `List.countP`
(which takes a `Bool` predicate). Equivalent to `List.countP (fun x => decide (p x)) xs`.

This pattern appears across many LeetCode problems (often under the name `count_filter`)
where counting elements meeting a decidable proposition is needed, avoiding the need
to manually convert between `Prop` and `Bool` via `decide`. -/

/-- Count the number of elements in `xs` that satisfy the decidable proposition `p`.
Equivalent to `List.countP (fun x => decide (p x)) xs`. -/
def countBy_specificDuplicate {α : Type} (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countBy_specificDuplicate p xs

/-- `countBy_specificDuplicate` on the empty list returns `0`. -/
@[simp]
lemma countBy_nil_specificDuplicate {α : Type} {p : α → Prop} [DecidablePred p] :
    countBy_specificDuplicate p [] = 0 := rfl

/-- `countBy_specificDuplicate` on `x :: xs` decomposes into a check on `x` plus the count on `xs`. -/
lemma countBy_cons_specificDuplicate {α : Type} {p : α → Prop} [DecidablePred p] (x : α) (xs : List α) :
    countBy_specificDuplicate p (x :: xs) = (if p x then 1 else 0) + countBy_specificDuplicate p xs := rfl

/-- If `x ∈ xs` and `p x` holds, then `countBy_specificDuplicate p xs ≥ 1`.
Generalizes `count_pos_of_mem` (the special case where `p := (· = a)`). -/
lemma countBy_pos_of_mem {α : Type} {p : α → Prop} [DecidablePred p] {xs : List α} {x : α}
    (hx : x ∈ xs) (hp : p x) : countBy_specificDuplicate p xs ≥ 1 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rw [countBy_cons_specificDuplicate]
    rcases eq_or_ne x y with (rfl | hne)
    · simp [hp]
    · have hmem : x ∈ ys := by
        simpa [hne] using hx
      have hrest : countBy_specificDuplicate p ys ≥ 1 := ih hmem
      have hhead : (if p y then 1 else 0) ≥ 0 := by split <;> omega
      omega

/-! ### `countWhere_specificDuplicate` — boolean predicate count in prefix

`countWhere_specificDuplicate xs d p k` counts how many elements among the first `k` elements
(indexed via `getD` with default `d`) of `xs` satisfy the boolean predicate `p`.
This is a prefix counter like `countPrefix` and `countVal`, but generalized to an
arbitrary `Bool` predicate rather than a single target value.

Unlike `countPrefix` (which checks equality to a specific value `a`), `countWhere_specificDuplicate`
accepts `p : α → Bool`, making it suitable for any computable condition
(e.g., evenness, primality, property checks). Equivalent to
`(List.take k xs).countP p` when `k ≤ xs.length` and `d` is irrelevant.
-/

/-- Count how many elements among the first `k` elements of `xs` satisfy predicate `p`.
Uses `getD` with default `d` for safe indexed access; indices `≥ xs.length` return `d`
and `p d` determines whether they contribute. Returns `0` when `k = 0`. -/
def countWhere_specificDuplicate {α : Type} (xs : List α) (d : α) (p : α → Bool) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k'+1 => countWhere_specificDuplicate xs d p k' + (if p (xs.getD k' d) then 1 else 0)

/-- Base case: `countWhere_specificDuplicate xs d p 0 = 0`. -/
@[simp]
theorem countWhere_zero {α : Type} (xs : List α) (d : α) (p : α → Bool) :
    countWhere_specificDuplicate xs d p 0 = 0 := rfl

/-- Recurrence for `countWhere_specificDuplicate`: `countWhere_specificDuplicate xs d p (k+1)` adds the check at position `k`. -/
theorem countWhere_succ {α : Type} (xs : List α) (d : α) (p : α → Bool) (k : Nat) :
    countWhere_specificDuplicate xs d p (k + 1) = countWhere_specificDuplicate xs d p k + (if p (xs.getD k d) then 1 else 0) := rfl

/-- `countWhere_specificDuplicate xs d p k ≤ k` — each of the `k` positions contributes at most `1`. -/
theorem countWhere_le {α : Type} (xs : List α) (d : α) (p : α → Bool) (k : Nat) :
    countWhere_specificDuplicate xs d p k ≤ k := by
  induction' k with k ih
  · simp [countWhere_specificDuplicate]
  · rw [countWhere_specificDuplicate]
    have h : (if p (xs.getD k d) then (1 : Nat) else 0) ≤ 1 := by
      split <;> omega
    omega

end List
