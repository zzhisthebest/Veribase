import Mathlib

/-! # Combinatorics
Basic combinatorial functions and sequences.
-/

namespace Combinatorics

/-! ### Unsigned Stirling numbers of the first kind (modular) -/

/-- Unsigned Stirling numbers of the first kind, computed modulo `mod`.
The recurrence is:
  `s(0,0) = 1`, `s(0,k) = 0` for `k > 0`, `s(n,0) = 0` for `n > 0`,
  `s(n+1,k+1) = (s(n,k) + n·s(n,k+1)) % mod`. -/
def stirlingFirstUnsignedMod (mod : Nat) : Nat → Nat → Nat
| 0, 0 => 1
| 0, _+1 => 0
| _, 0 => 0
| (n+1), (k+1) => (stirlingFirstUnsignedMod mod n k + n * stirlingFirstUnsignedMod mod n (k+1)) % mod

/-! ### String generation from a character alphabet -/

/-- Generate all strings of length `n` whose characters are drawn from `alphabet`.
For example, `allStringsOfLength ['a','b'] 2 = ["aa","ab","ba","bb"]`. -/
def allStringsOfLength (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 =>
      let prev := allStringsOfLength alphabet n
      alphabet.flatMap (fun c => prev.map (fun s => s.push c))

/-! ### Enumerating all lists of a given length -/

/-- Generate all lists of length `k` over the alphabet `xs`.
This is the `k`-fold Cartesian product of `xs` with itself, returned as a flat `List (List α)`.
Elements are prepended (via `::`) at each step, so for `xs = [a, b]` and `k = 2`, the result is
`[[a,a],[b,a],[a,b],[b,b]]` (lexicographic order with rightmost index varying fastest).

For example, `listsOfLength [1, 2] 2 = [[1,1],[2,1],[1,2],[2,2]]`. -/
def listsOfLength {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | Nat.succ k =>
      (listsOfLength xs k).flatMap (fun ys =>
        xs.map (fun x => x :: ys)
      )

/-! ### Enumerating all lists up to a given length -/

/-- Generate all lists over the alphabet `xs` with length at most `n` (i.e., lengths 0 through n).
This flattens `listsOfLength xs k` for `k ∈ range (n+1)`. The result is returned as a flat
`List (List α)`, ordered by increasing length then by the order produced by `listsOfLength`.

For example, `listsUpToLength ['a','b'] 1 = [[], ['a'], ['b']]`. -/
def listsUpToLength {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  (List.range (n + 1)).flatMap (listsOfLength xs)

/-! ### Enumerating all lists over `[0, bound]` of a given length -/

/-- Generate all lists of length `len` where each element is in `[0, bound]` (inclusive).
This is the Cartesian product of `[0, bound]` with itself `len` times, returned as a flat
`List (List Nat)`. Elements are prepended (via `::`) at each step, so the rightmost index
varies fastest.

For example, `listsOfLengthRange 2 1 = [[0,0],[1,0],[0,1],[1,1]]`.
Equivalent to `listsOfLength (List.range (bound + 1)) len` but with a different iteration order. -/
def listsOfLengthRange (len bound : Nat) : List (List Nat) :=
  match len with
  | 0 => [[]]
  | Nat.succ len' =>
      let tails := listsOfLengthRange len' bound
      (List.range (bound + 1)).flatMap (fun c => tails.map (fun t => c :: t))

/-! ### Counting triples satisfying a predicate -/

/-- Count the number of index pairs `(i, j)` in `[0, m) × [0, n)` for which
`pred i j` evaluates to `true`. Uses nested iteration over `List.range`.
This is the 2D analogue of `countTriplesWhere`. -/
def countPairsWhere (m n : Nat) (pred : Nat → Nat → Bool) : Nat :=
  (List.range m).foldl (fun cnt i =>
    cnt + ((List.range n).filter (pred i)).length
  ) 0

/-- Count the number of triples `(i, j, k)` with `i, j, k ∈ {0, …, n-1}`
satisfying a boolean predicate `P`. Uses triple nested iteration over
`List.range n` and runs in O(n³). -/
def countTriplesWhere (n : Nat) (P : Nat → Nat → Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i =>
    (List.range n).foldl (fun acc' j =>
      (List.range n).foldl (fun acc'' k =>
        if P i j k then acc'' + 1 else acc''
      ) acc') acc) 0

/-- Predicate: indices `i, j, k` are in strictly increasing order (`i < j < k`). -/
def orderedTriple (i j k : Nat) : Bool :=
  decide (i < j) && decide (j < k)

/-! ### `combinations` — enumerate all k-element combinations from {0, …, n-1} -/

/-- Generate all k-element combinations (subsets without repetition) from the set
`{0, 1, ..., n-1}`. Each combination is returned as a list in decreasing order.

For example, `combinations 3 2 = [[1,0],[2,0],[2,1]]`.

The base cases are:
- `combinations n 0 = [[]]` (the empty subset, for any `n`)
- `combinations 0 (k+1) = []` (no subsets of positive size from an empty set)

The recursive case separates subsets that include `n` from those that do not. -/
def combinations (n k : Nat) : List (List Nat) :=
  match n, k with
  | _, 0 => [[]]
  | 0, _+1 => []
  | n+1, k+1 =>
      let with_n := (combinations n k).map (fun l => n :: l)
      let without_n := combinations n (k+1)
      with_n ++ without_n

/-! ### `insertEverywhere` — insert an element at all positions in a list -/

/-- Insert an element `c` at every possible position in list `l`.
Returns all lists formed by inserting `c` somewhere in `l`. -/
def insertEverywhere {α : Type u} (c : α) : List α → List (List α)
  | [] => [[c]]
  | h :: t => (c :: h :: t) :: ((h :: ·) <$> insertEverywhere c t)

/-- Prepend `c` to `l` is trivially in `insertEverywhere c l`. -/
lemma mem_insertEverywhere_self {α : Type u} (c : α) (l : List α) : (c :: l) ∈ insertEverywhere c l := by
  induction l with
  | nil => simp [insertEverywhere]
  | cons hd tl ih => simp [insertEverywhere, ih]

/-- Inserting `c` at any position in `l` yields a permutation of `c :: l`. -/
lemma insertEverywhere_perm {α : Type u} (c : α) (l : List α) (p : List α) (h : p ∈ insertEverywhere c l) :
    List.Perm p (c :: l) := by
  induction l generalizing p with
  | nil =>
    simp [insertEverywhere] at h
    subst h; exact List.Perm.refl _
  | cons hd tl ih =>
    simp [insertEverywhere, List.mem_map] at h
    rcases h with (rfl | ⟨q, hq, rfl⟩)
    · exact List.Perm.refl _
    · have h_perm : List.Perm q (c :: tl) := ih q hq
      have h_cons : List.Perm (hd :: q) (hd :: c :: tl) := List.Perm.cons hd h_perm
      have h_swap : List.Perm (hd :: c :: tl) (c :: hd :: tl) := List.Perm.swap c hd tl
      exact List.Perm.trans h_cons h_swap

/-- For any split of a list, inserting `c` at the split point is in the result.
That is, `as ++ c :: bs ∈ insertEverywhere c (as ++ bs)`. -/
lemma insertEverywhere_split {α : Type u} (c : α) (as bs : List α) :
    as ++ c :: bs ∈ insertEverywhere c (as ++ bs) := by
  induction as with
  | nil => simp [insertEverywhere, mem_insertEverywhere_self]
  | cons a as' ih =>
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨as' ++ c :: bs, ih, rfl⟩

/-- Move a single element from after `as` to the front:
`as ++ x :: bs` is a permutation of `x :: (as ++ bs)`. -/
lemma perm_move_cons_middle {α : Type u} (as bs : List α) (x : α) :
    List.Perm (as ++ x :: bs) (x :: (as ++ bs)) := by
  induction as with
  | nil =>
    exact List.Perm.refl _
  | cons a as' ih =>
    have h_cons : List.Perm (a :: (as' ++ x :: bs)) (a :: (x :: (as' ++ bs))) :=
      List.Perm.cons a ih
    have h_swap : List.Perm (a :: (x :: (as' ++ bs))) (x :: a :: (as' ++ bs)) :=
      List.Perm.symm (List.Perm.swap a x (as' ++ bs))
    have h_chain : List.Perm (a :: (as' ++ x :: bs)) (x :: a :: (as' ++ bs)) :=
      List.Perm.trans h_cons h_swap
    simpa [List.append] using h_chain

/-! ### `allPermutations` — generate all permutations of a list -/

/-- Generate all permutations of a list.
Uses a recursive insertion approach: for each element, insert it
at every position in all permutations of the remaining elements. -/
def allPermutations {α : Type u} : List α → List (List α)
  | [] => [[]]
  | c :: cs => (allPermutations cs).flatMap (insertEverywhere c)

/-- Every list generated by `allPermutations` is a permutation of the input. -/
lemma allPermutations_perm {α : Type u} (l : List α) : ∀ p ∈ allPermutations l, List.Perm p l := by
  induction l with
  | nil =>
    intro p hp
    simp [allPermutations] at hp
    subst hp
    exact List.Perm.refl _
  | cons x xs ih =>
    intro p hp
    simp [allPermutations, List.mem_flatMap] at hp
    rcases hp with ⟨q, hq, hp'⟩
    have hq_perm : List.Perm q xs := ih q hq
    have hp_perm : List.Perm p (x :: q) := insertEverywhere_perm x q p hp'
    have hcons : List.Perm (x :: q) (x :: xs) := List.Perm.cons x hq_perm
    exact List.Perm.trans hp_perm hcons

/-- Every permutation of `l` is generated by `allPermutations`. -/
lemma allPermutations_perm_complete {α : Type u} [DecidableEq α] (l : List α) (p : List α) (h : List.Perm p l) :
    p ∈ allPermutations l := by
  induction l generalizing p with
  | nil => have : p = [] := List.perm_nil.mp h; subst p; simp [allPermutations]
  | cons x xs ih =>
    have hx : x ∈ p := h.mem_iff.mpr (by simp)
    obtain ⟨as, bs, rfl⟩ := List.append_of_mem hx
    have htail : List.Perm (as ++ bs) xs :=
      List.Perm.cons_inv ((perm_move_cons_middle as bs x).symm.trans h)
    exact List.mem_flatMap.mpr ⟨as ++ bs, ih _ htail, insertEverywhere_split x as bs⟩

end Combinatorics
