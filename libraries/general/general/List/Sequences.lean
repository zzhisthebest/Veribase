import Mathlib
import general.List.Gcd
import general.List.IndexedAccess
import general.List.Pairs
import general.Nat.Distances

/-!
# `List.generateUntil` — bounded list generation with a stopping condition

`generateUntil f stop bound k` generates at most `bound` elements of the sequence
`f k, f (k+1), f (k+2), …`, stopping as soon as `f i > stop` (so the generated
elements are all `≤ stop` except possibly when the bound is exhausted).

This is a general-purpose utility for "generate until threshold" patterns,
commonly used with Fibonacci-like sequences but applicable to any `f : Nat → Int`.
-/

namespace List

/-- Generate at most `bound` values of `f i` for `i` starting at `k`, stopping
when `f i > stop`. Returns the list of values (all `≤ stop` by construction,
unless `bound` runs out first).

Example: `generateUntil (fun i => i) 5 10 0` produces `[0,1,2,3,4,5]` (stops at 6 > 5). -/
def generateUntil (f : Nat → Int) (stop : Int) (bound : Nat) (k : Nat) : List Int :=
  match bound with
  | 0 => []
  | bound' + 1 =>
    if f k > stop then [] else f k :: generateUntil f stop bound' (k+1)

/-- The length of `generateUntil` is at most `bound`. -/
lemma generateUntil_length_le (f : Nat → Int) (stop : Int) (bound : Nat) (k : Nat) :
    (generateUntil f stop bound k).length ≤ bound := by
  induction bound generalizing k with
  | zero => simp [generateUntil]
  | succ bound ih =>
    simp [generateUntil]
    by_cases h : f k > stop
    · simp [h]
    · simp [h]
      have h_inner := ih (k+1)
      omega

/-- Index correctness: the `i`-th element of `generateUntil f stop bound k`
(if it exists within bounds) is `f (k + i)`. -/
lemma generateUntil_index (f : Nat → Int) (stop : Int) (bound : Nat) (k : Nat) :
    ∀ i, i < (generateUntil f stop bound k).length →
    (generateUntil f stop bound k)[i]? = some (f (k + i)) := by
  induction bound generalizing k with
  | zero =>
    intro i hi
    simp [generateUntil] at hi
  | succ bound ih =>
    simp [generateUntil]
    by_cases h : f k > stop
    · simp [h]
    · simp [h]
      intro i hi
      cases i with
      | zero => simp
      | succ i' =>
        simp
        have hi' : i' < (generateUntil f stop bound (k+1)).length := by
          simpa [List.length_cons] using hi
        have h_ih := ih (k+1) i' hi'
        simpa [add_comm, add_left_comm, add_assoc] using h_ih

/-- If the result list is shorter than `bound`, then the next element
(after the last included one) exceeds `stop`. -/
lemma generateUntil_next_gt_lt_bound (f : Nat → Int) (stop : Int) (bound : Nat) (k : Nat)
    (h_lt : (generateUntil f stop bound k).length < bound) :
    f (k + (generateUntil f stop bound k).length) > stop := by
  induction bound generalizing k with
  | zero =>
    simp [generateUntil] at h_lt
  | succ bound ih =>
    simp [generateUntil] at h_lt ⊢
    by_cases h : f k > stop
    · simp [h]
    · simp [h] at h_lt ⊢
      have h_inner_lt : (generateUntil f stop bound (k+1)).length < bound := by omega
      have h_ih := ih (k+1) h_inner_lt
      simpa [add_comm, add_left_comm, add_assoc] using h_ih

/-- If the result list is non-empty, the last element is `≤ stop`. -/
lemma generateUntil_last_le (f : Nat → Int) (stop : Int) (bound : Nat) (k : Nat) :
    (generateUntil f stop bound k).length > 0 →
    f (k + (generateUntil f stop bound k).length - 1) ≤ stop := by
  induction bound generalizing k with
  | zero =>
    simp [generateUntil]
  | succ bound ih =>
    simp [generateUntil]
    by_cases h : f k > stop
    · simp [h]
    · rw [if_neg h]
      have h_fle : f k ≤ stop := by omega
      intro hposlen
      let inner := generateUntil f stop bound (k+1)
      have hlen : (f k :: inner).length = inner.length + 1 := by simp
      rw [hlen] at hposlen ⊢
      have hcalc : k + (inner.length + 1) - 1 = k + inner.length := by omega
      rw [hcalc]
      by_cases h_inner_empty : inner.length = 0
      · simp [h_inner_empty]
        exact h_fle
      · have hpos_inner : inner.length > 0 := Nat.pos_of_ne_zero h_inner_empty
        have h_ih := ih (k+1) hpos_inner
        have hcalc_inner : (k+1) + inner.length - 1 = k + inner.length := by omega
        rw [hcalc_inner] at h_ih
        exact h_ih

/-- For a function `f` with an index-bound property `h_bound`, and `n ≥ 0`,
using `bound := Int.toNat n + 2`, either the result is empty or the next
element exceeds `n`. The hypothesis `h_bound` says that whenever
`f k ≤ n` we must have `k ≤ Int.toNat n + 1`.

This is typically instantiated with `f := λ k => (Nat.fib k : Int)` and the
corresponding index-bound lemma for Fibonacci numbers. -/
lemma generateUntil_next_gt (f : Nat → Int)
    (h_bound : ∀ (n : Int), 0 ≤ n → ∀ (k : Nat), f k ≤ n → k ≤ Int.toNat n + 1)
    (n : Int) (hn : 0 ≤ n) (k : Nat) :
    (generateUntil f n (Int.toNat n + 2) k).length = 0 ∨
    f (k + (generateUntil f n (Int.toNat n + 2) k).length) > n := by
  let bound := Int.toNat n + 2
  let result := generateUntil f n bound k
  have h_len_le : result.length ≤ bound := generateUntil_length_le f n bound k
  by_cases h_empty : result.length = 0
  · left; exact h_empty
  · by_cases h_lt : result.length < bound
    · right; exact generateUntil_next_gt_lt_bound f n bound k h_lt
    · have h_eq : result.length = bound := by omega
      by_cases h_fle : f (k + result.length) ≤ n
      · have h_idx_bound : k + result.length ≤ Int.toNat n + 1 :=
          h_bound n hn (k + result.length) h_fle
        rw [h_eq] at h_idx_bound
        omega
      · right; exact lt_of_not_ge h_fle

end List

namespace List

/-! ### `tabulateNat` — building a list from `Nat → α` -/

/-- Build a list of length `n` by applying `f` to each index `0, 1, …, n-1`.
Equivalent to `(List.range n).map f`, but defined via `List.ofFn` for better
interoperability with `Fin`-based indexing lemmas. -/
def tabulateNat {α : Type} (f : Nat → α) (n : Nat) : List α :=
  List.ofFn (λ (i : Fin n) => f i.val)

/-- The length of `tabulateNat f n` is `n`. -/
lemma length_tabulateNat {α : Type} (f : Nat → α) (n : Nat) : (tabulateNat f n).length = n := by
  simp [tabulateNat]

/-- If `i < n`, then `(tabulateNat f n)[i]! = f i`.
This gives a `Nat → α` result directly (not `Fin n → α`), making it simpler to use
in contexts where the index is a plain `Nat`. -/
lemma getElem!_tabulateNat_eq {α : Type} [Inhabited α] (f : Nat → α) (n i : Nat) (h : i < n) :
    (tabulateNat f n)[i]! = f i := by
  unfold tabulateNat
  rw [getElem!_ofFn_eq (λ (i' : Fin n) => f i'.val) i h]

/-- `tabulateNat f n` is the same as `map f (range n)`.
This bridges `List.ofFn`-based construction with `map`-based construction over `range`. -/
lemma tabulateNat_eq_map_range {α : Type} (f : Nat → α) (n : Nat) :
    tabulateNat f n = List.map f (List.range n) := by
  unfold tabulateNat
  apply List.ext_getElem?
  intro i
  simp [List.getElem?_ofFn, List.getElem?_map]
  by_cases hi : i < n
  · simp [List.getElem?_range hi, hi]
  · have hge : n ≤ i := Nat.le_of_not_gt hi
    have h_range_none : (List.range n)[i]? = none := by
      rw [List.getElem?_eq_none_iff]
      simp [hge]
    simp [hi, h_range_none]

/-- If `i < n`, then `(tabulateNat f n)[i]? = some (f i)`.
This is the `getElem?` version of `getElem!_tabulateNat_eq`, and does not require
an `Inhabited` instance. -/
lemma getElem?_tabulateNat_eq {α : Type} (f : ℕ → α) (n i : ℕ) (hi : i < n) :
    (tabulateNat f n)[i]? = some (f i) := by
  simp [tabulateNat, List.getElem?_ofFn, hi]

/-- The canonical specification for `tabulateNat`: its length equals `n` and each
element at index `i < n` is `f i`. This is the combined property that any
consumer of `tabulateNat` typically needs. -/
lemma tabulateNat_spec {α : Type} (f : ℕ → α) (n : ℕ) :
    (tabulateNat f n).length = n ∧ ∀ i : ℕ, i < n → (tabulateNat f n)[i]? = some (f i) := by
  constructor
  · exact length_tabulateNat f n
  · intro i hi; exact getElem?_tabulateNat_eq f n i hi

/-! ### `sequenceUpTo` — generating a list from the first values of a sequence

`sequenceUpTo f n` generates the list `[f 0, f 1, …, f n]` when `n ≥ 0`,
and `[]` when `n < 0`. This is a convenience wrapper around `tabulateNat`
that handles `Int` bounds, common in programming problems where input indices
may be negative. -/

/-- Generate the list `[f 0, f 1, …, f n]` when `n ≥ 0`, empty otherwise. -/
def sequenceUpTo {α : Type _} (f : Nat → α) (n : Int) : List α :=
  if n < 0 then
    []
  else
    tabulateNat f (n.toNat + 1)


lemma sequenceUpTo_of_neg {α : Type _} (f : Nat → α) {n : Int} (hn : n < 0) :
    sequenceUpTo f n = [] := by
  unfold sequenceUpTo; simp [hn]

lemma sequenceUpTo_of_nonneg {α : Type _} (f : Nat → α) {n : Int} (hn : 0 ≤ n) :
    sequenceUpTo f n = tabulateNat f (n.toNat + 1) := by
  unfold sequenceUpTo; simp [not_lt.mpr hn]

lemma length_sequenceUpTo_of_nonneg {α : Type _} (f : Nat → α) {n : Int} (hn : 0 ≤ n) :
    (sequenceUpTo f n).length = n.toNat + 1 := by
  rw [sequenceUpTo_of_nonneg f hn, length_tabulateNat]

lemma getElem?_sequenceUpTo_of_nonneg {α : Type _} (f : Nat → α) {n : Int} (hn : 0 ≤ n)
    (i : Nat) (hi : i < n.toNat + 1) :
    (sequenceUpTo f n)[i]? = some (f i) := by
  rw [sequenceUpTo_of_nonneg f hn]
  exact getElem?_tabulateNat_eq f (n.toNat + 1) i hi

end List

namespace List

/-! ## Association list lookup

`lookupReplace t d` looks up `t` in the association list `d`. If `t` is found as a key
(with value `v`), returns `v`; otherwise returns `t` unchanged.

This generalizes the pattern "replace a token with its value from a dictionary,
or keep it if not found", which appears in string replacement and token mapping problems.
-/


/-- Look up a key in an association list. If the key is found, return the associated
value; otherwise return the key unchanged. Works for any type with `DecidableEq`. -/
def lookupReplace {α : Type} [DecidableEq α] (t : α) (d : List (α × α)) : α :=
  match d with
  | [] => t
  | (k, v) :: rest => if t = k then v else lookupReplace t rest

/-- If the key equals the first key in the list, `lookupReplace` returns the associated value. -/
lemma lookupReplace_of_eq {α : Type} [DecidableEq α] (t k v : α) (rest : List (α × α)) (h : t = k) :
    lookupReplace t ((k, v) :: rest) = v := by
  simp [lookupReplace, h]

/-! ### Generate all lists of a given length from a set of atoms -/

/-- Generate all lists of length exactly `n` whose elements are drawn from `choices`.
For `n = 0`, returns `[[]]` (just the empty list).
For `n+1`, returns all lists from `allListsOfLength n choices` each extended by one choice.

This is the cartesian product of `n` copies of `choices`.
See `listsUpTo` for the variant that generates all lists of length ≤ `n`. -/
def allListsOfLength {α : Type} (n : Nat) (choices : List α) : List (List α) :=
  Nat.rec (motive := fun _ => List (List α))
    [[]]
    (fun _ rec => rec.flatMap (fun as => choices.map (fun c => c :: as)))
    n

/-! ### Generate all lists up to a given length from a set of atoms -/

/-- Generate all lists of length ≤ `n` whose elements are drawn from `atoms`.
For `n = 0`, returns `[[]]` (just the empty list).
For `n+1`, returns all lists from `listsUpTo atoms n` plus all one-element extensions.

This is useful for bounded exhaustive search over a finite alphabet, e.g., generating
all possible operation sequences in constraint solving problems. -/
def listsUpTo {α : Type} (atoms : List α) : Nat → List (List α)
  | 0     => [[]]
  | n + 1 =>
      let prev := listsUpTo atoms n
      prev ++ (prev.flatMap (fun xs => atoms.map (fun a => xs ++ [a])))

end List


/-!
# `List.iterate` with `map`

Lemmas about `List.iterate` composed with `List.map`. These combine the existing
mathlib primitives (`List.length_iterate`, `List.getElem?_iterate`) with `List.map`
to give direct access to elements of mapped iterate sequences.

Useful for verifying algorithms that generate sequences via `List.iterate` and then
transform them via `map`.
-/

namespace List

/-- The length of a mapped `iterate` equals the iteration count `n`.
In particular, `(List.iterate f a n).map g` has exactly `n` elements. -/
theorem length_map_iterate {α β : Type} (f : α → α) (a : α) (g : α → β) (n : Nat) :
    ((iterate f a n).map g).length = n := by
  simp

/-- Accessing the `i`-th element (`i < n`) of a mapped `iterate` yields `some (g (f^[i] a))`.
The element at position `i` of `(iterate f a n).map g` is `g` applied to the `i`-th iterate
of `f` starting from `a`. -/
theorem getElem?_map_iterate {α β : Type} (f : α → α) (a : α) (g : α → β)
    (n i : Nat) (hi : i < n) : ((iterate f a n).map g)[i]? = some (g (f^[i] a)) := by
  rw [List.getElem?_map, List.getElem?_iterate f a n i hi]
  simp

/-! ### `iterate_aux` — collecting intermediate results of function iteration

`iterate_aux f a k` applies `f` repeatedly starting from `a` for `k` steps,
returning a list of the `k` intermediate results (excluding the initial value `a`).

Example: `iterate_aux (fun x => x+1) 0 3 = [1, 2, 3]`.

Note: `iterate_aux f a k = List.iterate f (f a) k`. -/

/-- Iterate a function `k` times, collecting all intermediate results (excluding the initial value).
`iterate_aux f a 3` returns `[f a, f (f a), f (f (f a))]`. -/
def iterate_aux (f : α → α) (prev : α) (k : Nat) : List α :=
  match k with
  | 0 => []
  | k'+1 =>
    let next := f prev
    next :: iterate_aux f next k'

lemma iterate_aux_length (f : α → α) (prev : α) (k : Nat) :
    (iterate_aux f prev k).length = k := by
  induction' k with k ih generalizing prev
  · rfl
  · simp [iterate_aux, ih]

/-! ### `iterate_inclusive` — collecting intermediate results including the initial value

`iterate_inclusive f n a` is the inclusive variant of `iterate_aux`: it includes the
initial value `a` in the result. It returns `[a, f a, f² a, ..., fⁿ a]` (length `n+1`).

This is equivalent to `List.iterate f a (n+1)`. -/

/-- Iterate a function `n` times, collecting all intermediate results **including** the
initial seed value. `iterate_inclusive f 2 a` returns `[a, f a, f (f a)]`. -/
def iterate_inclusive (f : α → α) (n : Nat) (a : α) : List α :=
  match n with
  | 0 => [a]
  | n+1 => a :: iterate_inclusive f n (f a)

/-- The length of `iterate_inclusive f n a` is `n + 1` (the initial value plus `n` iterates). -/
lemma iterate_inclusive_length (f : α → α) (n : Nat) (a : α) :
    (iterate_inclusive f n a).length = n + 1 := by
  induction' n with k IH generalizing a
  · simp [iterate_inclusive]
  · simp [iterate_inclusive, IH]

end List

/-!
# `List.recurList` — list generation from two-term recurrence

Given a step function `f` and initial values `a`, `b`, `recurList f a b n` generates `n` elements
where the first two are `a` and `b`, and each subsequent element is `f` applied to the two
preceding elements.

For Fibonacci: `recurList Nat.add 0 1 n` gives the first `n` Fibonacci numbers.
-/

namespace List

/-- Generate a list from a two-term recurrence. Given step function `f` and initial values `a`, `b`,
`recurList f a b n` generates `n` elements where the first two are `a` and `b`,
and each subsequent element is `f` applied to the two preceding elements.

For Fibonacci: `recurList Nat.add 0 1 n` gives the first `n` Fibonacci numbers. -/
def recurList (f : α → α → α) (a b : α) : Nat → List α
  | 0 => []
  | n + 1 => a :: recurList f b (f a b) n


lemma recurList_length (f : α → α → α) (a b : α) (n : Nat) : (recurList f a b n).length = n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [recurList, ih]

/-- If a sequence `s : Nat → α` satisfies the same two-term recurrence as `recurList`,
then `recurList` correctly computes `s i` at each index `i < n`. -/
lemma recurList_get (f : α → α → α) (a b : α) (n : Nat)
    (s : Nat → α) (h0 : s 0 = a) (h1 : s 1 = b) (hrec : ∀ i, s (i+2) = f (s i) (s (i+1)))
    (i : Nat) (hi : i < n) : (recurList f a b n)[i]? = some (s i) := by
  induction n generalizing a b s i with
  | zero => omega
  | succ n ih =>
    simp [recurList]
    match i with
    | 0 => simp [h0]
    | i + 1 =>
      have hi' : i < n := by omega
      have h2 : s 2 = f a b := by
        rw [hrec 0, h0, h1]
      let s' : Nat → α := λ j => s (j+1)
      have h0' : s' 0 = b := by simp [s', h1]
      have h1' : s' 1 = f a b := by simp [s', h2]
      have hrec' : ∀ j, s' (j+2) = f (s' j) (s' (j+1)) := by
        intro j
        simp [s']
        simpa [add_comm, add_left_comm, add_assoc] using hrec (j+1)
      have h_ih := ih b (f a b) s' h0' h1' hrec' i hi'
      simpa [s'] using h_ih

end List

namespace List


/-! ### Consecutive differences from an initial value -/

/-- Compute consecutive differences of a list starting from `init`.
`differencesFrom [a, b, c] i = [a - i, b - a, c - b]`. -/
def differencesFrom : List Nat → Nat → List Nat
  | [], _ => []
  | (x :: xs), prev => (x - prev) :: differencesFrom xs x


lemma differencesFrom_nil (init : Nat) : differencesFrom [] init = [] := rfl


lemma differencesFrom_singleton (x init : Nat) : differencesFrom [x] init = [x - init] := rfl

lemma differencesFrom_cons (x y : Nat) (xs : List Nat) (init : Nat) :
    differencesFrom (x :: y :: xs) init = (x - init) :: differencesFrom (y :: xs) x := rfl

lemma length_differencesFrom (l : List Nat) (init : Nat) : (differencesFrom l init).length = l.length := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp [differencesFrom, ih]


/-! ### Product of consecutive differences -/

/-- Computes the product of consecutive differences in a list of naturals.
    For `[a₀, a₁, …, aₙ]`, returns `∏_{i=0}^{n-1} (a_{i+1} - aᵢ)`,
    with the empty and singleton lists both yielding `1`. -/
def consecutiveDiffProduct : List Nat → Nat
  | [] => 1
  | [_] => 1
  | a :: b :: rest => (b - a) * consecutiveDiffProduct (b :: rest)


end List

namespace List

/-! ### Consecutive differences of a list -/

/-- Compute consecutive differences of a list. `diffs [a,b,c] = [b-a, c-b]`.
Generalized over any additive group. -/
def diffs {α : Type} [AddGroup α] : List α → List α
  | [] | [_] => []
  | x :: y :: rest => (y - x) :: diffs (y :: rest)

variable {α : Type} [AddGroup α]

theorem diffs_nil : diffs ([] : List α) = [] := rfl

end List

namespace List

/-! # Forward difference (maximum increase) in a list

This module defines `forwardDiff`, `maxForwardDiffAt`, and `maxForwardDiff`:
functions that compute the maximum forward difference (increase)
`l[j] - l[i]` where `i < j` — the classic "best time to buy and sell stock"
problem.

These use `Finset.sup` over `Fin` indices to compute the direct formula
`max_{i<j} (l[j] - l[i])`, which is convenient for specification proofs.
For an efficient single-pass algorithm over `Array`, see
`Array.maxForwardDiff` in `general/Array.lean`.
-/

/-- Forward difference `xs[j] - xs[i]` when `i < j` as natural numbers, otherwise `0`.
This computes the profit from buying at index `i` and selling at index `j`. -/
def forwardDiff {n : Nat} (xs : Fin n → Nat) (i j : Fin n) : Nat :=
  if (i : Nat) < (j : Nat) then
    xs j - xs i
  else
    0

/-- Maximum forward difference achievable when the sell index is `j`,
considering all earlier buy indices `i`. -/
def maxForwardDiffAt {n : Nat} (xs : Fin n → Nat) (j : Fin n) : Nat :=
  (Finset.univ : Finset (Fin n)).sup (fun i => forwardDiff xs i j)

/-- Maximum forward difference `l[j] - l[i]` over all `i < j` in the list.
Returns `0` for empty/singleton lists or when all differences are non-positive.
This is the classic "best time to buy and sell stock" maximum profit. -/
def maxForwardDiff (l : List Nat) : Nat :=
  (Finset.univ : Finset (Fin l.length)).sup (maxForwardDiffAt l.get)

end List


namespace List

/-! # Consecutive runs of a given value

This module provides functions for computing the maximum length of consecutive
occurrences of a target value in a list.
-/

/-- Auxiliary function: fold over `l` computing the max consecutive run of `target`.
`cur` is the current run length, `best` is the best seen so far. -/
def maxConsecutiveOfValAux {α : Type} [DecidableEq α] (l : List α) (target : α)
    (cur : Nat) (best : Nat) : Nat :=
  match l with
  | [] => max best cur
  | h :: t =>
    if h = target then
      maxConsecutiveOfValAux t target (cur + 1) best
    else
      maxConsecutiveOfValAux t target 0 (max best cur)

/-! ### Run-length encoding: group consecutive equal elements -/

/-- Auxiliary: group consecutive equal elements in a list into `(count, value)` pairs,
starting from a current element `curVal` with count `curLen`.

For a complete run-length encoding of a list `l`, call `groupConsecutiveAux (l.head! 0) (l.head? 1 l.head!) l.tail`
or use a wrapper that handles the empty-list case.

For example:
* `groupConsecutiveAux 'a' 0 ['a','a','b','b','a'] = [(2,'a'), (2,'b'), (1,'a')]`
* `groupConsecutiveAux x 0 [] = [(0,x)]` (empty input returns just the initial pair) -/
def groupConsecutiveAux {α : Type} [DecidableEq α] (curVal : α) (curLen : Nat) : List α → List (Nat × α)
  | [] => [(curLen, curVal)]
  | d :: ds => if d = curVal then groupConsecutiveAux curVal (curLen + 1) ds
               else (curLen, curVal) :: groupConsecutiveAux d 1 ds

/-! ### Split by predicate into consecutive groups

Split a list into groups of consecutive elements satisfying a predicate `p`.
Elements not satisfying `p` act as separators and are discarded. -/

/-- Split a list into groups of consecutive elements satisfying predicate `p`.
Separators (elements not satisfying `p`) are discarded.
`acc` accumulates the current group in reverse order.

For example:
* `splitByPred (· == '1') ['0','1','1','0','1'] [] = [['1','1'], ['1']]`
* `splitByPred (·.isAlpha) ['a','b',' ','c'] [] = [['a','b'], ['c']]`
* `splitByPred (λ _ => true) [1,2,3] [] = [[1,2,3]]`
* `splitByPred (λ _ => false) [1,2,3] [] = []` -/
def splitByPred {α : Type} (p : α → Bool) (xs : List α) (acc : List α) : List (List α) :=
  match xs with
  | [] =>
    match acc.reverse with
    | [] => []
    | a => [a]
  | x :: xs' =>
    if p x then
      splitByPred p xs' (x :: acc)
    else
      let rest := splitByPred p xs' []
      match acc.reverse with
      | [] => rest
      | a => a :: rest
termination_by xs.length

/-- Group consecutive elements satisfying predicate `p` into sublists,
discarding elements that do not satisfy `p`.
This is a convenience wrapper around `splitByPred` that starts with an empty accumulator.
`groupByConsecutive p l` is equivalent to `splitByPred p l []`.

For example:
* `groupByConsecutive (· == '1') ['0','1','1','0','1'] = [['1','1'], ['1']]`
* `groupByConsecutive Char.isAlpha ['a','b',' ','c','d'] = [['a','b'], ['c','d']]`
* `groupByConsecutive (λ _ => true) [1,2,3] = [[1,2,3]]`
* `groupByConsecutive (λ _ => false) [1,2,3] = []` -/
def groupByConsecutive {α : Type} (p : α → Bool) (l : List α) : List (List α) :=
  splitByPred p l []

/-! #### Theorems about `splitByPred` -/

/-- When the predicate fails on the next element, flush the accumulator and restart. -/
theorem splitByPred_cons_of_neg {α : Type} (p : α → Bool) (x : α) (xs acc : List α) (h : p x = false) :
    splitByPred p (x :: xs) acc =
      let rest := splitByPred p xs []
      match acc.reverse with
      | [] => rest
      | a => a :: rest := by
  simp [splitByPred, h]

/-! ### Collapse consecutive runs of a given element -/

/-- Collapse consecutive runs of element `a` in a list, keeping only one representative per run.

For example:
* `collapseConsecutive '_' ['a','_','_','b'] = ['a','_','b']`
* `collapseConsecutive 1 [1,1,1,2,1] = [1,2,1]`
* `collapseConsecutive 'x' ['y','z'] = ['y','z']` (no runs to collapse)

Note: this collapses only runs of the given element `a`. Other consecutive duplicates
are left unchanged. -/
def collapseConsecutive [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      if x = a ∧ y = a then collapseConsecutive a (y :: xs)
      else x :: collapseConsecutive a (y :: xs)

/-- Collapsing a run that starts with at least two copies of `a` drops the first copy. -/

theorem collapseConsecutive_cons_cons [DecidableEq α] (a : α) (xs : List α) :
    collapseConsecutive a (a :: a :: xs) = collapseConsecutive a (a :: xs) := by
  rw [collapseConsecutive]
  simp

/-- If the first element differs from `a`, it is preserved regardless of what follows. -/

theorem collapseConsecutive_cons_ne [DecidableEq α] {a x y : α} (h : x ≠ a) (xs : List α) :
    collapseConsecutive a (x :: y :: xs) = x :: collapseConsecutive a (y :: xs) := by
  rw [collapseConsecutive]
  simp [h]

end List

namespace List

/-! ### Consecutive runs -/

/-- Compute the length of the longest consecutive run of element `a` in `xs`.
For example, `maxRun 1 [1,1,2,1,1,1] = 3` (the three consecutive `1`s at the end),
and `maxRun 'a' "baaab".data = 3`. -/
def maxRun {α : Type} [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | xs =>
    let rec go : List α → Nat → Nat → Nat
      | [], _, maxSoFar => maxSoFar
      | x :: cs, cur, maxSoFar =>
          if x = a then
            let cur' := cur + 1
            go cs cur' (Nat.max maxSoFar cur')
          else
            go cs 0 (Nat.max maxSoFar cur)
    go xs 0 0

/-- Maximum length of a run of *any* consecutive equal elements in a list.
For example, `longestConsecutiveRun [1,1,2,2,2,3] = 3` (three consecutive `2`s),
and `longestConsecutiveRun [1,2,1] = 1` (all runs have length 1).

This differs from `maxRun a l` which finds runs of a specific element `a`;
`longestConsecutiveRun l` finds the overall maximum run length regardless of element. -/
def longestConsecutiveRun {α : Type} [DecidableEq α] (lst : List α) : Nat :=
  let rec aux (lst : List α) (curr max : Nat) : Nat :=
    match lst with
    | [] => max
    | [_] => Nat.max (curr + 1) max
    | c :: d :: rest =>
      if c = d then aux (d :: rest) (curr + 1) max
      else aux (d :: rest) 1 (Nat.max (curr + 1) max)
  aux lst 0 0

/-- The maximum run length of an empty list is 0. -/

lemma longestConsecutiveRun_nil {α : Type} [DecidableEq α] : longestConsecutiveRun ([] : List α) = 0 := rfl

/-- The maximum run length of a singleton list is 1. -/

lemma longestConsecutiveRun_singleton {α : Type} [DecidableEq α] (x : α) : longestConsecutiveRun [x] = 1 := rfl

/-! ### Maximum of a function over prefixes -/

/-- The maximum value of `f` over all prefixes of `s`, computed via a single `foldl`
that tracks the running prefix. `init` is the initial value against which prefix values
are compared. -/
def maxOverPrefixes {α : Type} (f : List α → Nat) (init : Nat) (s : List α) : Nat :=
  (s.foldl
    (fun (maxSoFar, pref) ch =>
      let newPref := pref ++ [ch]
      (Nat.max maxSoFar (f newPref), newPref))
    (init, ([] : List α))).1

/-- `minCost cost xs` computes the minimum value of `cost x` over all `x ∈ xs`.
Returns `0` for the empty list. Uses the first element's cost as the initial
accumulator (to avoid `Nat.min 0 x = 0` making the result always 0). -/
def minCost {α : Type} (cost : α → Nat) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | p :: ps => ps.foldl (λ acc q => min acc (cost q)) (cost p)

/-- If `xs` is nonempty, then there exists `a ∈ xs` such that `minCost cost xs = cost a`.
In other words, the minimum value achieved by `cost` over `xs` is attained at some element. -/
lemma minCost_eq_of_mem {α : Type} (cost : α → Nat) (xs : List α) (hne : xs ≠ []) :
    ∃ a ∈ xs, minCost cost xs = cost a := by
  have aux (l : List α) (a : α) :
      ∃ b ∈ a :: l, l.foldl (fun acc q => min acc (cost q)) (cost a) = cost b := by
    induction l generalizing a with
    | nil => exact ⟨a, by simp, rfl⟩
    | cons x xs ih =>
      by_cases h : cost a ≤ cost x
      · obtain ⟨b, hb, he⟩ := ih a
        exact ⟨b, by simp only [List.mem_cons] at hb ⊢; tauto,
          by simpa only [List.foldl_cons, min_eq_left h] using he⟩
      · obtain ⟨b, hb, he⟩ := ih x
        exact ⟨b, List.mem_cons_of_mem a hb,
          by simpa only [List.foldl_cons, min_eq_right (le_of_not_ge h)] using he⟩
  cases xs with
  | nil => contradiction
  | cons a xs => exact aux xs a

end List


namespace List


/-! ### Longest run (consecutive streak) of a given value -/

/-- Maximum length of consecutive (contiguous) elements equal to `v` in `xs`.
Returns `0` for the empty list. Uses a tail-recursive helper `go` with
current run length `cur` and best-so-far `max`.

Example: `longestRunOf [1,1,0,1,1,1] 1 = 3`. -/
def longestRunOf {α : Type u} [DecidableEq α] (xs : List α) (v : α) : Nat :=
  let rec go (l : List α) (cur max : Nat) : Nat :=
    match l with
    | []      => max
    | x::xs' =>
        if x = v then
          let cur' := cur + 1
          go xs' cur' (Nat.max cur' max)
        else
          go xs' 0 max
  go xs 0 0

end List

namespace List

/-! # Balanced scanning over lists

This module provides `balancedScan`, a generic algorithm for checking whether
a sequence of weighted elements is "balanced": the running sum never goes negative
and ends at zero.

This generalizes the classic balanced-parentheses check (where `(` has weight `+1`
and `)` has weight `-1`) to arbitrary integer weights.
-/

/-- Scan a list with a weight function `w : α → Int`, checking that the running sum
(initialized to `cnt`) never becomes negative and ends at zero.
This is the core algorithm for checking balanced parentheses sequences,
generalized to arbitrary integer weights.

For example, with `w = λ c => if c = '(' then 1 else -1` and `cnt = 0`,
`balancedScan w "(()())".data 0 = true` and `balancedScan w "())(".data 0 = false`. -/
def balancedScan {α : Type} (w : α → Int) (l : List α) (cnt : Int) : Bool :=
  match l with
  | [] => cnt == 0
  | a :: as =>
    let cnt' := cnt + w a
    cnt' ≥ 0 && balancedScan w as cnt'

/-- A convenient lemma about `foldl` of `(+)` over `take`: folding addition over
`(x :: xs).take (i + 1)` starting from `0` equals `x` plus the fold over `xs.take i`.
This is used in the correctness proof of `scanlAdd`. -/
lemma foldl_take_succ_cons {α : Type _} [AddMonoid α] (x : α) (xs : List α) (i : Nat) :
    ((x :: xs).take (i + 1)).foldl (· + ·) 0 = x + ((xs.take i).foldl (· + ·) 0) := by
  have aux (l : List α) (a b : α) : l.foldl (· + ·) (a + b) = a + l.foldl (· + ·) b := by
    induction l generalizing b with
    | nil => rfl
    | cons y ys ih => simpa only [List.foldl_cons, add_assoc] using ih (b + y)
  simpa using aux (xs.take i) x 0

/-- Compute running (prefix) sums of a list, starting from an accumulator.
`scanlAdd [a, b, c] acc = [acc + a, acc + a + b, acc + a + b + c]`.
This is like `List.scanl (· + ·)` but without the initial accumulator in the result.
Equivalent to `(List.scanl (· + ·) acc xs).drop 1`. -/
def scanlAdd {α : Type _} [Add α] (xs : List α) (acc : α) : List α :=
  match xs with
  | [] => []
  | x :: xs' =>
    let newAcc := acc + x
    newAcc :: scanlAdd xs' newAcc

/-- `scanlAdd` preserves the length of the input list. -/
theorem scanlAdd_length {α : Type _} [Add α] (xs : List α) (acc : α) :
    (scanlAdd xs acc).length = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [scanlAdd, ih]

/-- The `i`-th element (with `0` as default) of `scanlAdd xs acc` equals
`acc + (xs.take (i + 1)).foldl (· + ·) 0`, provided `i < xs.length`. -/
theorem scanlAdd_getD {α : Type _} [AddMonoid α] (xs : List α) (acc : α) (i : Nat)
    (h : i < xs.length) :
    (scanlAdd xs acc).getD i 0 = acc + ((xs.take (i + 1)).foldl (· + ·) 0) := by
  induction xs generalizing acc i with
  | nil =>
    exfalso; exact Nat.not_lt_zero _ h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [scanlAdd]
    | succ i' =>
      have hi' : i' < xs.length := by
        simpa using h
      rw [scanlAdd]
      rw [List.getD_cons_succ]
      rw [ih (acc + x) i' hi']
      rw [foldl_take_succ_cons x xs (i' + 1)]
      rw [add_assoc]

/-- The `i`-th element (via `get?`) of `scanlAdd xs acc` equals
`some (acc + (xs.take (i + 1)).foldl (· + ·) 0)`, provided `i < xs.length`.
This is the `Option`-valued counterpart of `scanlAdd_getD`. -/
theorem scanlAdd_get? {α : Type _} [AddMonoid α] (xs : List α) (acc : α) (i : Nat)
    (h : i < xs.length) :
    (scanlAdd xs acc)[i]? = some (acc + ((xs.take (i + 1)).foldl (· + ·) 0)) := by
  induction xs generalizing acc i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [scanlAdd]
    | succ i =>
      have hi : i < xs.length := by simpa using h
      rw [scanlAdd, List.getElem?_cons_succ, ih (acc + x) i hi,
        foldl_take_succ_cons]
      simp [add_assoc]

/-! ### Multiplicative scan (prefix products) -/

/-- Compute running (prefix) products of a list, starting from an accumulator.
`scanlMul [a, b, c] acc = [acc * a, acc * a * b, acc * a * b * c]`.
This is like `List.scanl (· * ·)` but without the initial accumulator in the result.
Equivalent to `(List.scanl (· * ·) acc xs).drop 1`.
This is the multiplicative counterpart of `scanlAdd`. -/
def scanlMul {α : Type _} [Mul α] (xs : List α) (acc : α) : List α :=
  match xs with
  | [] => []
  | x :: xs' =>
    let newAcc := acc * x
    newAcc :: scanlMul xs' newAcc

/-- `scanlMul` preserves the length of the input list. -/
theorem scanlMul_length {α : Type _} [Mul α] (xs : List α) (acc : α) :
    (scanlMul xs acc).length = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [scanlMul, ih]

/-- A helper lemma: folding multiplication via `take` factors out the head element.
`(x :: xs).take (i+1)` folded with multiplication from `1` equals `x` times the fold
over `xs.take i`. This is the multiplicative counterpart of `foldl_take_succ_cons`. -/
lemma foldl_mul_one_take_succ_cons {α : Type _} [Monoid α] (x : α) (xs : List α) (i : Nat) :
    ((x :: xs).take (i + 1)).foldl (· * ·) 1 = x * ((xs.take i).foldl (· * ·) 1) := by
  have aux (l : List α) (a b : α) : l.foldl (· * ·) (a * b) = a * l.foldl (· * ·) b := by
    induction l generalizing b with
    | nil => rfl
    | cons y ys ih => simpa only [List.foldl_cons, mul_assoc] using ih (b * y)
  simpa using aux (xs.take i) x 1

/-- The `i`-th element (via `get?`) of `scanlMul xs acc` equals
`some (acc * (xs.take (i + 1)).foldl (· * ·) 1)`, provided `i < xs.length`.
This is the multiplicative counterpart of `scanlAdd_get?`. -/
theorem scanlMul_get? {α : Type _} [Monoid α] (xs : List α) (acc : α) (i : Nat)
    (h : i < xs.length) :
    (scanlMul xs acc)[i]? = some (acc * ((xs.take (i + 1)).foldl (· * ·) 1)) := by
  induction xs generalizing acc i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [scanlMul]
    | succ i =>
      have hi : i < xs.length := by simpa using h
      rw [scanlMul, List.getElem?_cons_succ, ih (acc * x) i hi,
        foldl_mul_one_take_succ_cons]
      simp [mul_assoc]

/-- Fold over a list with a weight function `w : α → Int`, tracking the running sum.
Returns `some final_cnt` if the running sum never goes negative,
or `none` if it does.

This is the `Option`-valued counterpart of `balancedScan`:
`balancedScan w l cnt = true ↔ balanceFold w l cnt = some 0`. -/
def balanceFold {α : Type} (w : α → Int) (l : List α) (cnt : Int) : Option Int :=
  match l with
  | [] => some cnt
  | a :: as =>
    let cnt' := cnt + w a
    if cnt' < 0 then none else balanceFold w as cnt'

/-- If `balancedScan` succeeds (returns `true`), then `balanceFold` returns `some 0`. -/
lemma balanceFold_of_balancedScan {α : Type} (w : α → Int) (l : List α) (cnt : Int)
    (h : balancedScan w l cnt = true) : balanceFold w l cnt = some 0 := by
  induction l generalizing cnt with
  | nil =>
    simp [balancedScan, balanceFold] at h ⊢
    exact h
  | cons a as ih =>
    simp only [balancedScan] at h
    simp only [balanceFold]
    by_cases hneg : cnt + w a < 0
    · have hge_false : (cnt + w a ≥ 0 : Bool) = false :=
        decide_eq_false_iff_not.mpr (by omega)
      rw [hge_false] at h
      simp at h
    · have h_nonneg : 0 ≤ cnt + w a := by omega
      have hge_true : (cnt + w a ≥ 0 : Bool) = true :=
        decide_eq_true h_nonneg
      rw [hge_true] at h
      simp at h
      simp [hneg]
      exact ih _ h

/-- If `balanceFold` returns `some 0`, then `balancedScan` succeeds (returns `true`). -/
lemma balancedScan_of_balanceFold {α : Type} (w : α → Int) (l : List α) (cnt : Int)
    (h : balanceFold w l cnt = some 0) : balancedScan w l cnt = true := by
  induction l generalizing cnt with
  | nil =>
    simp [balancedScan, balanceFold] at h ⊢
    exact h
  | cons a as ih =>
    simp only [balanceFold] at h
    simp only [balancedScan]
    by_cases hneg : cnt + w a < 0
    · simp [hneg] at h
    · have h_nonneg : 0 ≤ cnt + w a := by omega
      have hge_true : (cnt + w a ≥ 0 : Bool) = true :=
        decide_eq_true h_nonneg
      simp [hneg] at h
      have hscan : balancedScan w as (cnt + w a) = true := ih _ h
      rw [hge_true]
      simp [hscan]

/-- The key equivalence: `balancedScan` returns `true` iff `balanceFold` returns `some 0`,
for any list and starting count. -/
theorem balancedScan_iff_balanceFold {α : Type} (w : α → Int) (l : List α) (cnt : Int) :
    balancedScan w l cnt = true ↔ balanceFold w l cnt = some 0 :=
  ⟨balanceFold_of_balancedScan w l cnt, balancedScan_of_balanceFold w l cnt⟩

end List

namespace List

/-! ### `scanrPairs` — right-to-left scan with pairs -/

/-- Process a list from right to left, building `(element, computed-value)` pairs.
For each element `x`, the value is computed by `f x tail` where `tail` is the
already-processed result for the suffix.

This is the right-to-left analog of `scanr` that also passes the accumulated
list of pairs (rather than just the accumulated value) to the function `f`.
Useful for algorithms that need to look ahead at suffix results (e.g., longest
increasing subsequence). -/
def scanrPairs (f : α → List (α × β) → β) : List α → List (α × β)
  | [] => []
  | x :: xs =>
    let tail := scanrPairs f xs
    (x, f x tail) :: tail

/-- `scanrPairs` preserves the length of the input list. -/
lemma scanrPairs_length (f : α → List (α × β) → β) (l : List α) : (scanrPairs f l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [scanrPairs, ih]

/-! ### `prefixScan` — apply a function to every nonempty prefix -/

/-- Apply `f` to every nonempty prefix of `xs`, returning results ordered by increasing prefix
length.  `prefixScan f [a, b, c] = [f [a], f [a, b], f [a, b, c]]`.

This is a general-purpose building block for problems that need to compute a value
for each cumulative prefix of an input list (cumulative sums, running maximums,
connected‑component counts, etc.). -/
def prefixScan (xs : List α) (f : List α → β) : List β :=
  (List.range xs.length).map (fun i => f (xs.take (i + 1)))


lemma prefixScan_length (xs : List α) (f : List α → β) : (prefixScan xs f).length = xs.length := by
  simp [prefixScan]

end List

namespace List

/-! ### Modular scan: Horner's method with remainder tracking -/

/-- Scan a list with Horner's method using given base and modulus, recording at each prefix
whether the accumulated remainder is zero.

Given `f : α → Nat` (digit-value function), `base` (the positional base), `m` (the modulus),
and an initial remainder `rem`, `scanRemainders f base m as rem` returns a list of the same
length as `as`, where the `i`-th entry is `1` if the prefix up to `as[i]` is divisible by `m`,
and `0` otherwise.

The accumulation uses `(rem * base + f a) % m` at each step.

This is useful for problems that ask which prefixes of a number (represented as a list
of digits) are divisible by a given modulus. -/
def scanRemainders {α : Type} (f : α → Nat) (base m : Nat) : List α → (rem : Nat) → List Nat
  | [], _ => []
  | a :: as, rem =>
    let new_rem := (rem * base + f a) % m
    (if new_rem = 0 then 1 else 0) :: scanRemainders f base m as new_rem

/-- The length of `scanRemainders f base m as rem` equals the length of `as`. -/

lemma length_scanRemainders {α : Type} (f : α → Nat) (base m : Nat) (as : List α) (rem : Nat) :
    (scanRemainders f base m as rem).length = as.length := by
  induction as generalizing rem with
  | nil => rfl
  | cons a as ih =>
    simp [scanRemainders, ih]

end List


namespace List

/-! ### Extracting adjacent pairs -/

/-- Extracts all adjacent pairs from a list. For example,
`adjacentPairs [a, b, c, d] = [(a, b), (b, c), (c, d)]`.
Equivalent to `pairwiseMap (fun a b => (a, b))` from `List.lean`. -/
def adjacentPairs {α : Type u} : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)


theorem adjacentPairs_nil {α : Type u} : adjacentPairs ([] : List α) = [] := rfl


theorem adjacentPairs_singleton {α : Type u} (a : α) : adjacentPairs [a] = [] := rfl


theorem adjacentPairs_cons {α : Type u} (a b : α) (rest : List α) :
    adjacentPairs (a :: b :: rest) = (a, b) :: adjacentPairs (b :: rest) := rfl

/-! ### Mapping a function over adjacent pairs with index -/

/-- Map a function over adjacent pairs in a list, threading an index.
Given a list `[a₀, a₁, …, aₙ]` and starting index `k`, produces
`[f k a₀ a₁, f (k+1) a₁ a₂, …, f (k+n-1) a_{n-1} aₙ]`.
Returns `[]` for lists of length < 2. -/
def adjacentPairMap {α β : Type} (f : Nat → α → α → β) : List α → Nat → List β
  | [], _ => []
  | [_], _ => []
  | s :: s' :: rest, k => f k s s' :: adjacentPairMap f (s' :: rest) (k+1)

lemma adjacentPairMap_length {α β : Type} (f : Nat → α → α → β) (row : List α) (k : Nat) :
    (adjacentPairMap f row k).length = max 0 (row.length - 1) := by
  induction row generalizing k with
  | nil => simp [adjacentPairMap]
  | cons s rest ih =>
    match rest with
    | [] => simp [adjacentPairMap]
    | s' :: rest' => simp [adjacentPairMap, ih]

/-- Relate elements of `adjacentPairMap` to the index and original list elements. -/
lemma adjacentPairMap_get_eq {α β : Type} [Inhabited α]
    (f : Nat → α → α → β) (row : List α) (k j : Nat)
    (hj : j < (adjacentPairMap f row k).length) :
    (adjacentPairMap f row k)[j]? =
      some (f (k + j) ((row[j]?).getD default) ((row[j+1]?).getD default)) := by
  revert k j
  induction row with
  | nil => intro k j hj; simp [adjacentPairMap] at hj
  | cons s rest ih =>
    match rest with
    | [] => intro k j hj; simp [adjacentPairMap] at hj
    | s' :: rest' =>
      intro k j
      match j with
      | 0 => simp [adjacentPairMap]
      | j'+1 =>
        intro hj
        have hj' : j' < (adjacentPairMap f (s' :: rest') (k+1)).length := by
          simpa [adjacentPairMap] using hj
        simpa [adjacentPairMap, add_assoc, add_comm, add_left_comm] using ih (k+1) j' hj'

/-! ### Checking predicate on adjacent pairs -/

/-- Check that a binary boolean predicate `p` holds for all adjacent pairs in a list.
Returns `true` for empty and singleton lists (vacuously).
For example, `allAdjacentPairs (· < ·) [1, 3, 5] = true`. -/
def allAdjacentPairs (p : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => p a b && allAdjacentPairs p (b :: t)


theorem allAdjacentPairs_nil (p : α → α → Bool) : allAdjacentPairs p [] = true := rfl

/-- Check that all adjacent elements in a list are pairwise distinct (disequal).
Returns `true` for empty and singleton lists (vacuously true).
This is `allAdjacentPairs` specialized to the disequality predicate `(· ≠ ·)`. -/
def allAdjacentDiff {α : Type} [DecidableEq α] : List α → Bool :=
  allAdjacentPairs (fun a b => decide (a ≠ b))


theorem allAdjacentDiff_nil {α : Type} [DecidableEq α] : allAdjacentDiff ([] : List α) = true := rfl


theorem allAdjacentDiff_singleton {α : Type} [DecidableEq α] (a : α) : allAdjacentDiff [a] = true := rfl


theorem allAdjacentDiff_cons {α : Type} [DecidableEq α] (a b : α) (rest : List α) :
    allAdjacentDiff (a :: b :: rest) = (decide (a ≠ b) && allAdjacentDiff (b :: rest)) := rfl

/-! ### Index-based characterization of `allAdjacentPairs` -/

/-- Auxiliary lemma for `allAdjacentPairs_iff`: shifts the index condition
from a cons-cell to its tail. -/
lemma allAdjacentPairs_iff_cons_shift {α : Type} [Inhabited α] (p : α → α → Bool) (a : α) (l : List α)
    (h : ∀ i : Nat, i + 1 < (a :: l).length → p ((a :: l).getD i default) ((a :: l).getD (i + 1) default) = true) :
    ∀ i : Nat, i + 1 < l.length → p (l.getD i default) (l.getD (i + 1) default) = true := by
  intro i hi
  have hi_succ : (i + 1) + 1 < (a :: l).length := by
    simpa using hi
  have h_res := h (i + 1) hi_succ
  simpa using h_res

/-- `allAdjacentPairs p l = true` iff for every valid adjacent index pair `(i, i+1)`,
the predicate `p` holds on the elements at those positions (accessed via `getD` with `default`).
The `[Inhabited α]` constraint is only needed for `getD`; the default value is never used
when the indices are in bounds. -/
lemma allAdjacentPairs_iff {α : Type} [Inhabited α] (p : α → α → Bool) (l : List α) :
    allAdjacentPairs p l = true ↔
    ∀ i : Nat, i + 1 < l.length → p (l.getD i default) (l.getD (i + 1) default) = true := by
  constructor
  · intro h i hi
    induction l generalizing i with
    | nil => simp at hi
    | cons a l' ih =>
        cases l' with
        | nil =>
            have hlen : (a :: []).length = 1 := by simp
            rw [hlen] at hi
            omega
        | cons b rest =>
            simp [allAdjacentPairs] at h
            rcases h with ⟨hR_ab, h_rest⟩
            cases i with
            | zero => simpa using hR_ab
            | succ i' =>
                have hi_len : i' + 1 < (b :: rest).length := by
                  simp at hi ⊢
                  omega
                have h_ih := ih h_rest
                have h_ind := h_ih i' hi_len
                simpa using h_ind
  · intro h
    induction l with
    | nil => rfl
    | cons a l' ih =>
        match l' with
        | [] => rfl
        | b :: rest =>
            have hR_ab : p a b = true := by
              have h0 := h 0 (by simp)
              simpa using h0
            have h_rest_cond : ∀ i : Nat, i + 1 < (b :: rest).length →
                p ((b :: rest).getD i default) ((b :: rest).getD (i + 1) default) = true :=
              allAdjacentPairs_iff_cons_shift p a (b :: rest) h
            have h_rest_true : allAdjacentPairs p (b :: rest) = true := ih h_rest_cond
            simp [allAdjacentPairs, hR_ab, h_rest_true]

/-! ### Counting adjacent predicate failures -/

/-- Counts the number of adjacent pairs `(a, b)` in a list where a given binary
predicate `p` does **not** hold (i.e., where there is a "change").

This is useful for problems that require counting boundaries between adjacent
elements satisfying some relation — key changes, group transitions, parity
alternations, etc. -/
def countAdjacentChanges {α : Type u} (p : α → α → Bool) : List α → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if ¬ p a b then 1 else 0) + countAdjacentChanges p (b :: rest)


theorem countAdjacentChanges_nil {α : Type u} (p : α → α → Bool) :
    countAdjacentChanges p [] = 0 := rfl


theorem countAdjacentChanges_singleton {α : Type u} (p : α → α → Bool) (a : α) :
    countAdjacentChanges p [a] = 0 := rfl

theorem countAdjacentChanges_cons {α : Type u} (p : α → α → Bool) (a b : α) (rest : List α) :
    countAdjacentChanges p (a :: b :: rest) =
      (if ¬ p a b then 1 else 0) + countAdjacentChanges p (b :: rest) := rfl

/-! ### Summing a binary function over adjacent pairs -/

/-- Sum a binary function `g : α → α → Nat` over all adjacent pairs in a list.
For `[a, b, c]`, returns `g a b + g b c`. For empty or singleton lists, returns `0`. -/
def sumAdjacentWith {α : Type u} (g : α → α → Nat) : List α → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => g a b + sumAdjacentWith g (b :: t)


theorem sumAdjacentWith_nil {α : Type u} (g : α → α → Nat) : sumAdjacentWith g [] = 0 := rfl


theorem sumAdjacentWith_singleton {α : Type u} (g : α → α → Nat) (a : α) :
    sumAdjacentWith g [a] = 0 := rfl

theorem sumAdjacentWith_cons {α : Type u} (g : α → α → Nat) (a b : α) (t : List α) :
    sumAdjacentWith g (a :: b :: t) = g a b + sumAdjacentWith g (b :: t) := rfl

/-- Sum of absolute differences between consecutive elements under a mapping `f : α → Nat`.
`sumAdjacentDiffs f [a, b, c] = |f a - f b| + |f b - f c|`.
This is `sumAdjacentWith` specialized to `Nat.absDiff (f a) (f b)`. -/
def sumAdjacentDiffs {α : Type u} (f : α → Nat) : List α → Nat :=
  sumAdjacentWith (fun a b => Nat.absDiff (f a) (f b))

lemma sumAdjacentDiffs_def {α : Type u} (f : α → Nat) (l : List α) :
    sumAdjacentDiffs f l = sumAdjacentWith (fun a b => Nat.absDiff (f a) (f b)) l := rfl


lemma sumAdjacentDiffs_nil {α : Type u} (f : α → Nat) : sumAdjacentDiffs f [] = 0 := by
  first
  | (solve
    | rfl
    | simp_all [sumAdjacentDiffs]
    | omega
    | aesop
    | simp_all [sumAdjacentDiffs, List.foldl, List.foldr]
    | simp_all [sumAdjacentDiffs, Nat.absDiff])


lemma sumAdjacentDiffs_singleton {α : Type u} (f : α → Nat) (a : α) :
    sumAdjacentDiffs f [a] = 0 := by
  first
  | (solve
    | rfl
    | simp_all [sumAdjacentDiffs]
    | omega
    | aesop
    | simp_all [sumAdjacentDiffs, List.foldl, List.foldr]
    | simp_all [sumAdjacentDiffs, Nat.absDiff])

lemma sumAdjacentDiffs_cons {α : Type u} (f : α → Nat) (a b : α) (t : List α) :
    sumAdjacentDiffs f (a :: b :: t) = Nat.absDiff (f a) (f b) + sumAdjacentDiffs f (b :: t) := by
  simp [sumAdjacentDiffs, sumAdjacentWith_cons]

/-! ### Alternating predicate check on consecutive pairs -/

/-- Check that a list satisfies two predicates alternating on consecutive
    pairs: the 1st element must satisfy `p`, 2nd must satisfy `q`,
    3rd must satisfy `p`, 4th `q`, etc. Returns `false` for a singleton list
    (an incomplete pair), and `true` for the empty list. -/
def pairwiseCheckB {α : Type} (p q : α → Bool) : List α → Bool
  | [] => true
  | [_] => false
  | x :: y :: zs => p x && q y && pairwiseCheckB p q zs

/-! ### Boundary-protected neighbor access by index -/

/-- Get the element to the left of index `i` in list `l`, or `default` if `i` is the first element. -/
def boundaryLeft {α : Type} [Inhabited α] (default : α) (l : List α) (i : Nat) : α :=
  if i = 0 then default else l[i - 1]!

/-- Get the element to the right of index `i` in list `l`, or `default` if `i` is the last element. -/
def boundaryRight {α : Type} [Inhabited α] (default : α) (l : List α) (i : Nat) : α :=
  if i + 1 = l.length then default else l[i + 1]!

lemma boundaryLeft_pos {α : Type} [Inhabited α] (default : α) (l : List α) (i : Nat) (h : i ≠ 0) :
    boundaryLeft default l i = l[i - 1]! := by
  unfold boundaryLeft
  split_ifs with h0
  · exact absurd h0 h
  · rfl

/-! ### Adjacent difference by index -/

/-- Absolute difference between adjacent elements at positions `i` and `i+1` in a
list of integers, accessed via `getD` with default `0` for out-of-bounds indices.
`adjDiff l i = Int.natAbs (l[i+1] - l[i])`.

This is the index-based counterpart of structural adjacent operations like
`adjacentPairs` and `sumAdjacentDiffs`. -/
def adjDiff (l : List Int) (i : Nat) : Nat :=
  let a := l.getD i 0
  let b := l.getD (i + 1) 0
  Int.natAbs (b - a)

/-! ### Consecutive triples (sliding windows of size 3) -/

/-- Check that a ternary boolean predicate `p` holds for all consecutive triples
in a list. Returns `true` for lists of length `≤ 2` (vacuously, since no triples exist).

For example, `allTriplesSatisfy [a, b, c, d] (fun x y z => decide (x ≤ y ∧ y ≤ z))`
returns `true` iff `a ≤ b ≤ c` and `b ≤ c ≤ d`.

This is the 3-element analog of `allAdjacentPairs` (which checks adjacent pairs). -/
def allTriplesSatisfy {α : Type} (seq : List α) (p : α → α → α → Bool) : Bool :=
  match seq with
  | [] | [_] => true
  | a :: b :: c :: rest => p a b c && allTriplesSatisfy (b :: c :: rest) p
  | _ => true

lemma allTriplesSatisfy_nil {α : Type} (p : α → α → α → Bool) :
    allTriplesSatisfy ([] : List α) p = true := rfl

/-- Check whether **any** consecutive triple in a list satisfies the predicate `p`.
Returns `false` for lists of length `≤ 2` (since no triples exist).

This is the existential counterpart of `allTriplesSatisfy`: instead of requiring
*all* triples to satisfy `p`, it checks whether *at least one* triple does.

For example, `anyTriple (fun x y z => decide (x + y + z = 10)) [1, 2, 3, 1, 5] = true`
because `2 + 3 + 5 = 10`. -/
def anyTriple (p : α → α → α → Bool) : List α → Bool
  | [] | [_] => false
  | a :: b :: c :: rest => p a b c || anyTriple p (b :: c :: rest)
  | _ => false

lemma anyTriple_nil {α : Type} (p : α → α → α → Bool) :
    anyTriple p ([] : List α) = false := rfl

lemma anyTriple_singleton {α : Type} (p : α → α → α → Bool) (a : α) :
    anyTriple p [a] = false := rfl

lemma anyTriple_doubleton {α : Type} (p : α → α → α → Bool) (a b : α) :
    anyTriple p [a, b] = false := rfl

lemma anyTriple_cons_cons_cons {α : Type} (p : α → α → α → Bool) (a b c : α) (rest : List α) :
    anyTriple p (a :: b :: c :: rest) = (p a b c || anyTriple p (b :: c :: rest)) := rfl

/-! ### Counting consecutive triples (sliding windows of size 3) -/

/-- Count the number of consecutive triples `(xs[i], xs[i+1], xs[i+2])` in a list
for which the ternary predicate `p` holds. Returns `0` for lists of length `≤ 2`
(since no consecutive triple exists).

This is the counting analogue of `allTriplesSatisfy`: instead of returning `true`
iff *all* triples satisfy `p`, it returns *how many* triples satisfy `p`.

For example, `countSatisfyingTriples [a, b, c, d] p = (if p a b c then 1 else 0) + (if p b c d then 1 else 0)`. -/
def countSatisfyingTriples {α : Type} (xs : List α) (p : α → α → α → Bool) : Nat :=
  match xs with
  | [] | [_] => 0
  | a :: b :: c :: rest => (if p a b c then 1 else 0) + countSatisfyingTriples (b :: c :: rest) p
  | _ => 0


theorem countSatisfyingTriples_nil {α : Type} (p : α → α → α → Bool) :
    countSatisfyingTriples ([] : List α) p = 0 := rfl


theorem countSatisfyingTriples_singleton {α : Type} (p : α → α → α → Bool) (a : α) :
    countSatisfyingTriples [a] p = 0 := rfl

/-- A two-element list has no consecutive triples, so the count is zero. -/

theorem countSatisfyingTriples_doubleton {α : Type} (p : α → α → α → Bool) (a b : α) :
    countSatisfyingTriples [a, b] p = 0 := rfl

/-! ### Finding the first adjacent pair satisfying a predicate -/

/-- Find the first index `i` in a list such that adjacent elements `xs[i]` and
    `xs[i+1]` satisfy a binary predicate `p`. Returns `none` if no such adjacent
    pair exists.

    For example:
    * `findFirstAdjacentIdx [1, 2, 3, 4] (fun a b => a + b = 5) = some 1` (since `2 + 3 = 5`)
    * `findFirstAdjacentIdx [1, 2, 3] (fun a b => a = b) = none` (all adjacent pairs differ) -/
def findFirstAdjacentIdx {α : Type} [Inhabited α] (xs : List α) (p : α → α → Bool) : Option Nat :=
  let n := xs.length
  (List.range (n - 1)).find? (fun i => p (xs[i]!) (xs[i + 1]!))

/-- Expansion lemma for three-or-more element lists. This is the main computational reduction. -/
theorem countSatisfyingTriples_cons_cons_cons {α : Type} (p : α → α → α → Bool) (a b c : α) (rest : List α) :
    countSatisfyingTriples (a :: b :: c :: rest) p =
    (if p a b c then 1 else 0) + countSatisfyingTriples (b :: c :: rest) p := rfl

/-! ### Maximum consecutive run length of a given element -/

/-- Maximum length of a consecutive run of elements equal to `a` in `lst`.
Scans the list linearly and returns the length of the longest contiguous segment
where every element equals `a`.

For example, `maxConsecutive 1 [0, 1, 1, 0, 1] = 2` (the run `[1, 1]` has length 2). -/
def maxConsecutive {α : Type} [DecidableEq α] (a : α) (lst : List α) : Nat :=
  let rec aux (l : List α) (cur max : Nat) : Nat :=
    match l with
    | [] => max
    | x :: xs =>
        if x = a then
          aux xs (cur + 1) (Nat.max (cur + 1) max)
        else
          aux xs 0 max
  aux lst 0 0

/-- Base case: no consecutive runs in an empty list. -/
lemma maxConsecutive_nil {α : Type} [DecidableEq α] (a : α) :
    maxConsecutive a [] = 0 := rfl

/-! ### Sum of capped adjacent gaps (interval union total duration)

For a sorted list of starting points and a fixed interval duration, this computes
the total length of the union of all intervals without double-counting overlaps.
This is the core computation in LeetCode 495 (Teemo Attacking) and similar
overlapping-interval problems. -/

/-- Sum adjacent gaps, each capped at `dur`, plus `dur` for the last element.
Returns 0 for the empty list.

`sumMinGaps [a₁, …, aₙ] dur = (Σᵢ₌₁ⁿ⁻¹ min (aᵢ₊₁ - aᵢ) dur) + dur`
(for a nonempty list; 0 for the empty list). -/
def sumMinGaps (ts : List Nat) (dur : Nat) : Nat :=
  match ts with
  | [] => 0
  | _ :: _ => sumAdjacentWith (fun a b => min (b - a) dur) ts + dur


theorem sumMinGaps_nil (dur : Nat) : sumMinGaps [] dur = 0 := rfl


theorem sumMinGaps_single (t dur : Nat) : sumMinGaps [t] dur = dur := by
  simp [sumMinGaps, sumAdjacentWith]

theorem sumMinGaps_cons_two (t t' : Nat) (ts : List Nat) (dur : Nat) :
    sumMinGaps (t :: t' :: ts) dur = min (t' - t) dur + sumMinGaps (t' :: ts) dur := by
  simp [sumMinGaps, sumAdjacentWith_cons, add_assoc]

/-! ### Chunking into non-overlapping pairs -/

/-- Chunk a list into consecutive non-overlapping pairs, dropping the last element
if the list has odd length.

Example: `chunkPairs [a, b, c, d] = [(a, b), (c, d)]`

Contrast with `adjacentPairs` which produces sliding overlapping pairs
(e.g. `[(a, b), (b, c), (c, d)]`). -/
def chunkPairs {α : Type u} : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: chunkPairs rest


theorem chunkPairs_nil {α : Type u} : chunkPairs ([] : List α) = [] := rfl


theorem chunkPairs_singleton {α : Type u} (a : α) : chunkPairs [a] = [] := rfl


theorem chunkPairs_cons {α : Type u} (a b : α) (rest : List α) :
    chunkPairs (a :: b :: rest) = (a, b) :: chunkPairs rest := rfl

/-- The length of `chunkPairs l` is `l.length / 2` (integer division).
For example, a list of 5 elements produces 2 pairs, 6 elements produce 3 pairs. -/
theorem chunkPairs_length {α : Type u} (l : List α) : (chunkPairs l).length = l.length / 2 := by
  match l with
  | [] => simp [chunkPairs]
  | [_] => simp [chunkPairs]
  | a :: b :: xs =>
    simp only [chunkPairs_cons, List.length_cons, chunkPairs_length xs]
    omega
termination_by l

end List

namespace List

/-! ### `countAdj` — count adjacent equal elements -/

/-- Count the number of adjacent equal pairs in a list.
`countAdj [a, b, c, c, d] = 1` (the pair `(c, c)`).
Returns `0` for lists of length 0 or 1. -/
def countAdj {α : Type} [DecidableEq α] : List α → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a = b then 1 else 0) + countAdj (b :: rest)


lemma countAdj_nil {α : Type} [DecidableEq α] : countAdj ([] : List α) = 0 := rfl


lemma countAdj_singleton {α : Type} [DecidableEq α] (x : α) : countAdj [x] = 0 := rfl


lemma countAdj_cons_cons {α : Type} [DecidableEq α] (a b : α) (rest : List α) :
    countAdj (a :: b :: rest) = (if a = b then 1 else 0) + countAdj (b :: rest) := rfl

end List

namespace List

/-! ### `pathSum` — sum of a pairwise function over consecutive elements -/

/-- Sum of a pairwise function `d` over consecutive pairs in a list.
`pathSum d [a, b, c] = d a b + d b c`.
Returns `0` for lists of length < 2. -/
def pathSum {α : Type} (d : α → α → Nat) : List α → Nat
  | [] => 0
  | [_] => 0
  | (p :: q :: rest) => d p q + pathSum d (q :: rest)

theorem pathSum_nil {α : Type} (d : α → α → Nat) : pathSum d [] = 0 := rfl

theorem pathSum_singleton {α : Type} (d : α → α → Nat) (x : α) : pathSum d [x] = 0 := rfl

theorem pathSum_cons_cons {α : Type} (d : α → α → Nat) (x y : α) (rest : List α) :
    pathSum d (x :: y :: rest) = d x y + pathSum d (y :: rest) := rfl

/-! ### `pairwiseMap` — sliding-window transform over adjacent pairs -/

/-- Map each adjacent pair `(a, b)` in the list using `f`, sliding by one.
The output list has length `max(0, length xs - 1)`.
For `[x₁, x₂, …, xₙ]` with `n ≥ 2`, produces `[f x₁ x₂, f x₂ x₃, …, f xₙ₋₁ xₙ]`.
Returns `[]` for lists with fewer than 2 elements. -/
def pairwiseMap (f : α → α → β) : List α → List β
  | [] => []
  | [_] => []
  | a :: b :: rest => f a b :: pairwiseMap f (b :: rest)


theorem pairwiseMap_nil (f : α → α → β) : pairwiseMap f [] = [] := rfl


theorem pairwiseMap_singleton (f : α → α → β) (a : α) : pairwiseMap f [a] = [] := rfl


theorem pairwiseMap_cons (f : α → α → β) (a b : α) (rest : List α) :
    pairwiseMap f (a :: b :: rest) = f a b :: pairwiseMap f (b :: rest) := rfl

/-- `pairwiseMap` never makes the list longer. -/
theorem pairwiseMap_length_le (f : α → α → β) (l : List α) :
    (pairwiseMap f l).length ≤ l.length := by
  match l with
  | [] => simp [pairwiseMap]
  | [_] => simp [pairwiseMap]
  | a :: b :: xs =>
    simp only [pairwiseMap_cons, List.length_cons]
    exact Nat.succ_le_succ (pairwiseMap_length_le f (b :: xs))

/-- The exact length of `pairwiseMap f l` is `l.length - 1` (using truncated subtraction,
so empty and singleton lists correctly yield `0`). This is a stronger version of
`pairwiseMap_length_le`. -/
theorem pairwiseMap_length (f : α → α → β) (l : List α) : (pairwiseMap f l).length = l.length - 1 := by
  induction' l with a tail ih
  · simp [pairwiseMap]
  · cases' tail with b rest
    · simp [pairwiseMap]
    · simp [pairwiseMap, ih]

/-- If `i < l.length - 1`, then `i` and `i+1` are valid indices into `l`, and
`(pairwiseMap f l)[i]? = some (f a b)` where `a = l[i]` and `b = l[i+1]`.
In other words, the `i`-th element of `pairwiseMap f l` is `f` applied to the
`i`-th and `(i+1)`-th elements of the original list. -/
lemma pairwiseMap_getElem? (f : α → α → β) (l : List α) (i : Nat) (h : i < l.length - 1) :
    ∃ a b, l[i]? = some a ∧ l[i+1]? = some b ∧ (pairwiseMap f l)[i]? = some (f a b) := by
  induction' l with a tail ih generalizing i
  · exfalso; exact Nat.not_lt_zero _ h
  · cases' tail with b rest
    · exfalso; exact Nat.not_lt_zero _ h
    · cases' i with i'
      · refine ⟨a, b, by simp, by simp, by simp [pairwiseMap]⟩
      · have h_i' : i' < (b :: rest).length - 1 := by
          simp at h ⊢
          omega
        have h_res := ih i' h_i'
        rcases h_res with ⟨a', b', ha', hb', hr⟩
        refine ⟨a', b', ?_, ?_, ?_⟩
        · simpa using ha'
        · simpa using hb'
        · simpa [pairwiseMap] using hr

/-- If `i < (pairwiseMap f l).length`, then the `i`-th element of `pairwiseMap f l`
using `!` indexing equals `f (l[i]!) (l[i+1]!)`. This is the `!`-based version of
`pairwiseMap_getElem?` for code that uses `Inhabited` defaults. -/
lemma pairwiseMap_getElem! {α β : Type _} [Inhabited α] [Inhabited β] (f : α → α → β) (l : List α) (i : Nat)
    (h : i < (pairwiseMap f l).length) : (pairwiseMap f l)[i]! = f (l[i]!) (l[i+1]!) := by
  induction' l with a l ih generalizing i
  · simp [pairwiseMap] at h
  · cases' l with b rest
    · simp [pairwiseMap] at h
    · cases' i with i
      · simp [pairwiseMap]
      · have hlen : i < (pairwiseMap f (b :: rest)).length := by
          simp [pairwiseMap] at h
          omega
        have ih_res := ih i hlen
        simp [pairwiseMap] at ih_res
        simp [pairwiseMap]
        simpa using ih_res

/-! ### `allAdjacent` — check that every consecutive pair satisfies a predicate -/

/-- Check that every consecutive pair of elements in a list satisfies the given
`Bool`-valued predicate `stepValid`. Returns `true` for lists of length ≤ 1.

`allAdjacent [a, b, c] stepValid = stepValid a b && stepValid b c`. -/
def allAdjacent {α : Type} (l : List α) (stepValid : α → α → Bool) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    stepValid a b && allAdjacent (b :: rest) stepValid


theorem allAdjacent_nil {α : Type} (stepValid : α → α → Bool) :
    allAdjacent ([] : List α) stepValid = true := rfl


theorem allAdjacent_singleton {α : Type} (a : α) (stepValid : α → α → Bool) :
    allAdjacent [a] stepValid = true := rfl

theorem allAdjacent_cons {α : Type} (a b : α) (rest : List α) (stepValid : α → α → Bool) :
    allAdjacent (a :: b :: rest) stepValid =
    (stepValid a b && allAdjacent (b :: rest) stepValid) := rfl

/-- `allAdjacent` is equivalent to checking that every adjacent pair in the list
satisfies the predicate. This connects `allAdjacent` with `pairwiseMap`. -/
theorem allAdjacent_iff_pairwiseMap_all {α : Type} (l : List α) (stepValid : α → α → Bool) :
    allAdjacent l stepValid = (pairwiseMap stepValid l).all id := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs =>
      simp [allAdjacent, pairwiseMap, List.all_cons, ih]

/-! ### `allAdjacentInRange` — check adjacent pairs within an index range -/

/-- Check that every adjacent pair `(i, i+1)` with `i ∈ [l, r-1]` in a list `xs` satisfies
a `Bool`-valued predicate `p`. Returns `false` if any index in `[l, r]` is out of bounds
(for `xs`), or if any such pair fails `p`.

Special cases:
- If `r ≤ l`, the range is empty and returns `true` (vacuously true).
- If `l` or `r` index `xs` out of bounds, returns `false`.

This generalizes `allAdjacent` (which checks consecutive pairs across the *entire* list)
by allowing a sub-range `[l, r]`. -/
def allAdjacentInRange {α : Type} (xs : List α) (l r : Nat) (p : α → α → Bool) : Bool :=
  List.all (List.range (r - l)) fun k =>
    let i := l + k
    match xs[i]?, xs[i+1]? with
    | some a, some b => p a b
    | _, _ => false

/-! ### Sorted properties of mapped `List.range` -/

/-- If `f : Nat → α` is monotone (i.e., `a ≤ b` implies `f a ≤ f b`), then mapping `f`
    over `List.range n` produces a list sorted by `(· ≤ ·)`. -/
lemma sorted_map_range_of_monotone {α : Type u} [Preorder α] (f : Nat → α)
    (h_mono : ∀ a b, a ≤ b → f a ≤ f b) (n : Nat) :
    List.Sorted (· ≤ ·) ((List.range n).map f) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton]
      dsimp [List.Sorted]
      rw [List.pairwise_append]
      refine ⟨ih, ?_, ?_⟩
      · simp
      · intro a ha b hb
        simp at hb
        subst hb
        rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
        have hi_lt : i < k := (List.mem_range.mp hi)
        exact h_mono i k (Nat.le_of_lt hi_lt)

/-- `List.range n` is sorted by `(· ≤ ·)` for all `n : Nat`.
This follows from `sorted_map_range_of_monotone` with `f := id`. -/
lemma range_sorted (n : Nat) : List.Sorted (· ≤ ·) (List.range n) := by
  simpa using sorted_map_range_of_monotone (fun a => a) (fun a b h => h) n

end List


namespace List

/-! ### Sum of adjacent products -/

/-- Sum of products of adjacent elements in a list.
`sumAdjProducts [a, b, c] = a*b + b*c`, and returns `0` for lists of length 0 or 1.
Useful for problems involving pairwise interactions of consecutive elements. -/
def sumAdjProducts : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => a * b + sumAdjProducts (b :: t)


lemma sumAdjProducts_nil : sumAdjProducts [] = 0 := rfl


lemma sumAdjProducts_singleton (a : Nat) : sumAdjProducts [a] = 0 := rfl


lemma sumAdjProducts_cons_cons (a b : Nat) (t : List Nat) :
    sumAdjProducts (a :: b :: t) = a * b + sumAdjProducts (b :: t) := rfl

/-- `sumAdjProducts` is equivalent to summing the zipWith product of `l` and its tail. -/
lemma sumAdjProducts_eq_zipWith_sum (l : List Nat) :
    sumAdjProducts l = (List.zipWith (· * ·) l (l.drop 1)).sum := by
  match l with
  | [] => simp [sumAdjProducts]
  | [_] => simp [sumAdjProducts]
  | a :: b :: xs =>
    simpa [sumAdjProducts, List.zipWith] using congrArg (a * b + ·) (sumAdjProducts_eq_zipWith_sum (b :: xs))

end List

namespace List

/-! ### Twin pairs — pair elements from opposite ends of the list -/

/-- Pair each element with its symmetric counterpart from the end of the list.
For a list of length `n`, the `i`-th element is paired with the `(n-1-i)`-th element
for `i` in `[0, n/2)`. For example, `listTwinPairs [1,2,3,4] = [(1,4),(2,3)]`. -/
def listTwinPairs (xs : List α) : List (α × α) :=
  let half := xs.length / 2
  List.zip (xs.take half) (xs.reverse.take half)


theorem listTwinPairs_nil : listTwinPairs ([] : List α) = [] := by
  simp [listTwinPairs]

end List

namespace List

/-! ### Folding over adjacent pairs -/

/-- Fold a binary operation `f` over adjacent pairs in a list:
`foldPairs f [a, b, c, d] = d + f c d + f b c + f a b`.
Handles empty list (returns 0) and singleton (returns the element). -/
def foldPairs {α : Type} [AddMonoid α] (f : α → α → α) : List α → α
  | [] => 0
  | [x] => x
  | a :: b :: xs => foldPairs f (b :: xs) + f a b


lemma foldPairs_nil {α : Type} [AddMonoid α] (f : α → α → α) : foldPairs f [] = 0 := rfl


lemma foldPairs_single {α : Type} [AddMonoid α] (f : α → α → α) (x : α) : foldPairs f [x] = x := rfl

lemma foldPairs_cons {α : Type} [AddMonoid α] (f : α → α → α) (a b : α) (xs : List α) :
    foldPairs f (a :: b :: xs) = foldPairs f (b :: xs) + f a b := rfl

end List
