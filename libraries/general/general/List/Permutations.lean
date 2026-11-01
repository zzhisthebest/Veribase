import Mathlib
import general.List.Filter
import general.List.Find
import general.List.Sequences

namespace List

/-! ### `permutations` -/

/-- For any list `xs`, `List.permutations xs` is nonempty.
This is useful when using lemmas like `maxOver_achieved` that require `xs ≠ []`. -/
lemma permutations_ne_nil {α : Type} (xs : List α) : List.permutations xs ≠ [] := by
  have h : xs ∈ List.permutations xs :=
    List.mem_permutations.mpr (List.Perm.refl xs)
  intro h_empty
  rw [h_empty] at h
  simp at h

/-- Return the deduplicated list of all permutations of `xs`. -/
def uniquePermutations {α : Type} [DecidableEq α] (xs : List α) : List (List α) :=
  (List.permutations xs).dedup

/-- If `l` is a permutation of `xs`, then `l` belongs to the deduplicated list
of permutations of `xs`. -/
lemma mem_uniquePermutations_of_perm {α : Type} [DecidableEq α] {l xs : List α}
    (h : List.Perm l xs) : l ∈ uniquePermutations xs :=
  List.mem_dedup.mpr (List.mem_permutations.mpr h)

/-- If `l` belongs to the deduplicated list of permutations of `xs`, then `l` is
a permutation of `xs`. -/
lemma perm_of_mem_uniquePermutations {α : Type} [DecidableEq α] {l xs : List α}
    (h : l ∈ uniquePermutations xs) : List.Perm l xs :=
  List.mem_permutations.mp (List.mem_dedup.mp h)

/-- A list belongs to the deduplicated permutations of `xs` iff it is a permutation of `xs`.
This combines `mem_uniquePermutations_of_perm` and `perm_of_mem_uniquePermutations`
into a single equivalence. -/
lemma mem_uniquePermutations_iff {α : Type} [DecidableEq α] {l xs : List α} :
    l ∈ uniquePermutations xs ↔ List.Perm l xs := by
  dsimp [uniquePermutations]
  rw [List.mem_dedup, List.mem_permutations]

end List

namespace List

/-! ### Permutation identities on lists -/

/-- A permutation identity: `a :: a :: l` is a permutation of `a :: l ++ [a]`.
This is useful in palindrome-related reasoning where two occurrences of an element
at the front can be rearranged to one at the front and one at the back.
For example, in checking whether a list's characters can form a palindrome,
this identity bridges the parity-based characterization and the structural one. -/
lemma perm_aa_l_to_a_l_a {α : Type} [DecidableEq α] (a : α) (l : List α) :
    Perm (a :: a :: l) (a :: l ++ [a]) := by
  calc
    a :: a :: l = [a] ++ [a] ++ l := by simp
    _ ~ ([a] ++ l) ++ [a] := by
      rw [List.append_assoc]
      apply Perm.append (Perm.refl [a])
      exact perm_append_comm
    _ = a :: l ++ [a] := by simp

/-- Formula for `filter (· < x)` length when consing an element `y` with `y < x`. -/
lemma length_filter_lt_cons_of_lt {y x : Nat} {ys : List Nat} (h : y < x) :
    ((y :: ys).filter (· < x)).length = 1 + (ys.filter (· < x)).length := by
  have hdec : decide (y < x) = true := decide_eq_true h
  simp [hdec, add_comm]

/-- Formula for `filter (· < x)` length when consing an element `y` with `¬ y < x`. -/
lemma length_filter_lt_cons_of_not_lt {y x : Nat} {ys : List Nat} (h : ¬ y < x) :
    ((y :: ys).filter (· < x)).length = (ys.filter (· < x)).length := by
  have hdec : decide (y < x) = false := decide_eq_false h
  simp [hdec]

/-- Formula for `filter (· ≤ x)` length when consing an element `y` with `y ≤ x`. -/
lemma length_filter_le_cons_of_le {y x : Nat} {ys : List Nat} (h : y ≤ x) :
    ((y :: ys).filter (· ≤ x)).length = 1 + (ys.filter (· ≤ x)).length := by
  have hdec : decide (y ≤ x) = true := decide_eq_true h
  simp [hdec, add_comm]

/-! ### Boolean membership (decidable `∈`) -/

/-- Boolean membership for a list: returns `true` iff `a` appears in `xs`.
Uses `decide (b = a)` which requires `DecidableEq α`; the `BEq` constraint
allows `List.any` to work but is otherwise harmless.
This is the decidable, computation-friendly alternative to the `Prop`-level `a ∈ xs`. -/
def memArray [BEq α] [DecidableEq α] (xs : List α) (a : α) : Bool :=
  xs.any (fun b => decide (b = a))

/-- `memArray` correctly reflects `Prop`-level membership:
`a ∈ xs` implies `memArray xs a = true`. -/
lemma memArray_of_mem [BEq α] [DecidableEq α] {xs : List α} {a : α} (h : a ∈ xs) :
    memArray xs a = true := by
  induction' xs with y ys ih
  · exact absurd h (by simp)
  · cases h with
    | head _ =>
      unfold memArray; simp
    | tail _ hmem =>
      have hmem' : memArray ys a = true := ih hmem
      unfold memArray at hmem' ⊢
      rw [List.any_cons, hmem']
      simp

/-! ### Boolean permutation check -/

/-- A decidable proxy for `List.Perm`, using `List.isPerm` (boolean).
Generalized to any type with `BEq` and `LawfulBEq`.
This is `@[reducible]` so it simplifies to `List.isPerm` when expanded,
serving as a convenient, readable alias for postcondition specifications. -/
@[reducible]
def permBool [BEq α] [LawfulBEq α] (xs ys : List α) : Bool :=
  xs.isPerm ys

end List

namespace List

/-! ### `powerset` — all subsets of a list -/

/-- Enumerate all subsets of a list (finite, computable).
`powerset [a, b] = [[], [b], [a], [a, b]]`. -/
def powerset {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let ps := powerset xs
      ps ++ ps.map (fun s => x :: s)

/-- The empty list is always in the powerset of any list. -/
lemma mem_powerset_nil {α : Type} (l : List α) : [] ∈ powerset l := by
  induction' l with x xs ih
  · simp [powerset]
  · simp [powerset, ih]

end List

namespace List

/-! ### All sublists (subsequences) -/

/-- Generate all sublists (subsequences) of a list.
`allSublists [1,2,3]` yields `[[], [3], [2], [2,3], [1], [1,3], [1,2], [1,2,3]]`. -/
def allSublists {α : Type} : List α → List (List α)
  | []      => [[]]
  | x :: xs =>
      let r := allSublists xs
      r ++ r.map (fun ys => x :: ys)

/-- The empty list is always a member of `allSublists l`. -/
lemma allSublists_nil_mem {α : Type} (l : List α) : [] ∈ allSublists l := by
  induction l with
  | nil => simp [allSublists]
  | cons x xs ih =>
    unfold allSublists
    simp [ih]

/-- The original list is always a member of its own `allSublists`. -/
lemma allSublists_self_mem {α : Type} (l : List α) : l ∈ allSublists l := by
  induction l with
  | nil => simp [allSublists]
  | cons x xs ih =>
    unfold allSublists
    apply List.mem_append_right
    simp [ih]

/-- The `allSublists` of the empty list is the singleton list containing `[]`. -/

theorem allSublists_nil {α : Type} : allSublists ([] : List α) = [[]] := rfl

/-- If `S` is a sublist of `L`, then `S` is a member of `allSublists L`. -/
lemma mem_allSublists_of_sublist {α : Type} {L S : List α} (h : List.Sublist S L) :
    S ∈ allSublists L := by
  induction h with
  | slnil => simp [allSublists]
  | cons a h IH =>
    simp [allSublists, IH]
  | cons₂ a h IH =>
    simp [allSublists, IH]

/-- If `S` is a member of `allSublists L`, then `S` is a sublist of `L`. -/
lemma sublist_of_mem_allSublists {α : Type} {L S : List α} (h : S ∈ allSublists L) :
    List.Sublist S L := by
  induction L generalizing S with
  | nil =>
    simp [allSublists] at h
    subst h; exact List.Sublist.slnil
  | cons x xs IH =>
    rw [allSublists] at h
    simp [List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨T, hT, rfl⟩)
    · -- S ∈ allSublists xs
      have hsub := IH h
      exact List.Sublist.cons x hsub
    · -- S = x :: T, T ∈ allSublists xs
      have hsub := IH hT
      exact List.Sublist.cons₂ x hsub

/-- The length of any sublist in `allSublists L` is bounded by `L.length`. -/
lemma mem_allSublists_length_le {α : Type} (s l : List α) (h : s ∈ allSublists l) :
    s.length ≤ l.length := by
  induction' l with x xs ih generalizing s
  · simp [allSublists] at h; subst h; simp
  · simp [allSublists, List.mem_map] at h
    rcases h with (h | ⟨t, ht, rfl⟩)
    · exact Nat.le_trans (ih _ h) (by simp)
    · simp [List.length_cons]; exact ih _ ht

/-- Membership in `allSublists L` is equivalent to being a `Sublist` of `L`. -/
lemma mem_allSublists_iff {α : Type} {L S : List α} :
    S ∈ allSublists L ↔ List.Sublist S L :=
  ⟨sublist_of_mem_allSublists, mem_allSublists_of_sublist⟩

/-! ### `subseqsOfLength` — all subsequences of a given length -/

/-- All subsequences (non-contiguous) of `nums` of length `k`.
General over any element type. -/
def subseqsOfLength {α : Type u} (nums : List α) (k : Nat) : List (List α) :=
  match nums, k with
  | _, 0 => [[]]
  | [], _ => []
  | x :: xs, k'+1 =>
    (subseqsOfLength xs k').map (λ s => x :: s) ++ subseqsOfLength xs (k'+1)


theorem subseqsOfLength_nil_zero : subseqsOfLength ([] : List α) 0 = [[]] := rfl


theorem subseqsOfLength_nil_succ (n : Nat) : subseqsOfLength ([] : List α) (n+1) = [] := rfl


theorem subseqsOfLength_cons_zero (x : α) (xs : List α) : subseqsOfLength (x :: xs) 0 = [[]] := rfl

/-! ### `List.sublists` (mathlib) lemmas

Mathlib's `List.sublists` is a different function from general's `allSublists`;
lemmas here bridge the mathlib API. -/

/-- The empty list is always a member of `l.sublists` (mathlib's sublist generator). -/
lemma empty_mem_sublists (l : List α) : [] ∈ l.sublists := by
  rw [List.mem_sublists]
  exact List.nil_sublist _

/-- `List.sublists l` is never empty, since `[]` is always a sublist of `l`. -/
lemma sublists_ne_nil (l : List α) : List.sublists l ≠ [] :=
  List.ne_nil_of_mem (empty_mem_sublists l)

/-- If `n ≤ l.length`, then `List.sublistsLen n l` is nonempty. This follows
from the fact that the number of sublists of length `n` is `Nat.choose n l.length`,
which is positive when `n ≤ l.length`. -/
lemma sublistsLen_ne_nil_of_length_ge {α : Type _} {l : List α} {n : Nat} (h : n ≤ l.length) :
    List.sublistsLen n l ≠ [] := by
  have hpos : 0 < (List.sublistsLen n l).length := by
    rw [List.length_sublistsLen]
    exact Nat.choose_pos h
  exact List.length_pos_iff_ne_nil.mp hpos

/-! ### Conditionally take the length of a list -/

/-- `condLength p l` returns `l.length` if `p l` is true, otherwise `0`.
This is useful for folding max over filtered lists: instead of filtering then
mapping length, we fold with a conditional that conditionally contributes the length. -/
def condLength (p : List α → Bool) (l : List α) : Nat :=
  if p l then l.length else 0


lemma condLength_nil (p : List α → Bool) : condLength p ([] : List α) = 0 := by
  simp [condLength]

lemma condLength_le_length (p : List α → Bool) (l : List α) : condLength p l ≤ l.length := by
  unfold condLength; split <;> simp

/-- Folding with a conditional max (if `p l` then `max acc l.length` else `acc`)
is equivalent to first mapping `condLength p` and then folding `Nat.max`. -/
lemma foldl_max_cond_eq_map_foldl_max (p : List α → Bool) (acc : Nat) (ls : List (List α)) :
    ls.foldl (fun a l => if p l then Nat.max a l.length else a) acc =
    (ls.map (condLength p)).foldl Nat.max acc := by
  induction' ls with l ls ih generalizing acc
  · rfl
  · simp [List.foldl, condLength, ih]
    split <;> simp

/-! ### Maximum length among filtered sublists -/

/-- Maximum length among sublists of `xs` that satisfy predicate `p`.
Returns `0` if no sublist satisfies `p` (since `foldl Nat.max 0` of `[]` is `0`).
Generic over any list type, parameterized by a `Bool` predicate. -/
def maxFilteredSublistLength {α : Type u} (xs : List α) (p : List α → Bool) : Nat :=
  let ks : List Nat := (xs.sublists.filter p).map List.length
  ks.foldl Nat.max 0

/-! ### Subsequence check lemmas for `List.isSublist` (from Std) -/

/-- `List.isSublist` of `[]` against any list is `true`. -/

theorem isSublist_nil_left {α : Type} [BEq α] (ys : List α) : isSublist ([] : List α) ys = true := by
  simp [isSublist]

/-- `List.isSublist` of a nonempty list against `[]` is `false`. -/

theorem isSublist_cons_nil {α : Type} [BEq α] (x : α) (xs : List α) : isSublist (x :: xs) [] = false := by
  simp [isSublist]

/-! ### `isSubseq` — non-contiguous subsequence check -/

/-- Predicate: `as` is a (possibly non-contiguous) subsequence of `bs`.
General over any `α` with decidable equality.
Returns a `Bool` for decidable/computational use. -/
def isSubseq {α : Type u} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x = y then
      isSubseq xs ys
    else
      isSubseq (x :: xs) ys

/-- The empty list is a subsequence of any list. -/

theorem isSubseq_nil {α : Type u} [DecidableEq α] (l : List α) : isSubseq [] l = true := by
  simp [isSubseq]

/-! ### `isSubseqListB` — BEq-based subsequence check with Sublist equivalence -/

/-- If `a :: l1 <+ l2`, then dropping the first element, `l1 <+ l2`. -/
theorem sublist_drop_first {α : Type _} {a : α} {l1 l2 : List α} (h : a :: l1 <+ l2) : l1 <+ l2 := by
  induction l2 generalizing l1 a with
  | nil => cases h
  | cons b l2' ih =>
    rcases sublist_cons_iff.mp h with (h' | ⟨r, hr_eq, hr_sub⟩)
    · have h_tail : l1 <+ l2' := ih h'
      exact Sublist.cons b h_tail
    · have ⟨_ha_eq, hl1_eq⟩ := List.cons.inj hr_eq
      rcases hl1_eq
      exact Sublist.cons b hr_sub

/-- Decidable subsequence check by scanning the target list once.
Uses `BEq` / `LawfulBEq` for equality, avoiding the need for `DecidableEq`. -/
def isSubseqListB {α : Type u} [BEq α] (sub str : List α) : Bool :=
  let rec go : List α → List α → Bool
    | [], _ => true
    | _ :: _, [] => false
    | a :: as, b :: bs =>
        if a == b then go as bs else go (a :: as) bs
  go sub str

/-- Forward direction: if `isSubseqListB` returns true, it's a `Sublist`. -/
theorem isSubseqListB_sublist {α : Type _} [BEq α] [LawfulBEq α] (sub str : List α)
    (h : isSubseqListB sub str = true) : sub <+ str := by
  induction sub generalizing str with
  | nil => exact nil_sublist _
  | cons a as ih_outer =>
    induction str with
    | nil =>
      unfold isSubseqListB at h
      rw [isSubseqListB.go.eq_2] at h
      simp at h
    | cons b bs ih_inner =>
      unfold isSubseqListB at h
      rw [isSubseqListB.go.eq_3] at h
      by_cases heq : (a == b) = true
      · simp [heq] at h
        have hsub : as <+ bs := ih_outer bs (by unfold isSubseqListB; exact h)
        have ha_eq_b : a = b := (beq_iff_eq (α := α)).mp heq
        rw [ha_eq_b]
        exact Sublist.cons₂ b hsub
      · simp [heq] at h
        have hsub_bs : a :: as <+ bs := ih_inner (by unfold isSubseqListB; exact h)
        exact Sublist.trans hsub_bs (Sublist.cons b (Sublist.refl bs))

/-- Reverse direction: if it's a `Sublist`, the scanning algorithm returns true. -/
theorem sublist_isSubseqListB {α : Type _} [BEq α] [LawfulBEq α] (sub str : List α)
    (h : sub <+ str) : isSubseqListB sub str = true := by
  induction str generalizing sub with
  | nil =>
    cases h
    unfold isSubseqListB; rw [isSubseqListB.go.eq_1]
  | cons b bs ih =>
    rcases sublist_cons_iff.mp h with (h_sub_bs | ⟨r, hr_eq, hr_sub⟩)
    · cases sub with
      | nil => unfold isSubseqListB; rw [isSubseqListB.go.eq_1]
      | cons x xs =>
        unfold isSubseqListB
        rw [isSubseqListB.go.eq_3]
        by_cases heq : (x == b) = true
        · simp [heq]
          have h_xs_bs : xs <+ bs := sublist_drop_first h_sub_bs
          exact ih xs h_xs_bs
        · simp [heq]
          exact ih (x::xs) h_sub_bs
    · rcases hr_eq with rfl
      have h_r_bs : isSubseqListB r bs = true := ih r hr_sub
      unfold isSubseqListB
      rw [isSubseqListB.go.eq_3]
      simp
      unfold isSubseqListB at h_r_bs
      exact h_r_bs

/-- Equivalence between the scanning subsequence check and `List.Sublist`. -/
theorem isSubseqListB_iff_sublist {α : Type _} [BEq α] [LawfulBEq α] (sub str : List α) :
    isSubseqListB sub str = true ↔ sub <+ str := by
  constructor
  · exact isSubseqListB_sublist sub str
  · exact sublist_isSubseqListB sub str

end List


namespace List

/-- Generate all subset sums of a list.
Returns a list containing the sum of every subset of `l`,
including the empty subset (sum = 0).

Generalized over any `AddMonoid α` — for `Int` it produces all integer subset sums,
for `Nat` it produces all natural subset sums. -/
def subsetSums [AddMonoid α] : List α → List α
  | [] => [0]
  | x :: xs =>
    let rest := subsetSums xs
    rest ++ (rest.map (fun s => x + s))

/-- The empty list generates exactly one subset sum: zero. -/

lemma subsetSums_nil [AddMonoid α] : subsetSums ([] : List α) = [0] := rfl

/-- Recursive decomposition of subset sums: each element is either excluded
    or included (added to all sums of the tail). -/

lemma subsetSums_cons [AddMonoid α] (x : α) (xs : List α) :
    subsetSums (x :: xs) = subsetSums xs ++ (subsetSums xs).map (fun s => x + s) := rfl

/-! ### Sum of a specific subset given a boolean selector -/

/-- Sum of elements of `l` selected by the boolean selector `s`.
Given a list `l` and a function `s : Fin l.length → Bool` indicating which
elements to include, `subsetSum l s` computes the sum of the selected elements.

For example, `subsetSum [1, 2, 3] (λ i => i.val ≠ 1)` = `1 + 0 + 3 = 4`
(skipping index 1, which holds `2`).

Generalized to any `AddCommMonoid α`. -/
def subsetSum [AddCommMonoid α] (l : List α) (s : Fin l.length → Bool) : α :=
  (Finset.univ : Finset (Fin l.length)).sum fun i => if s i then l.get i else 0

/-- `subsetSum` on the empty list is always `0`. -/

lemma subsetSum_nil [AddCommMonoid α] (s : Fin 0 → Bool) : subsetSum ([] : List α) s = 0 := by
  simp [subsetSum]

/-! ### Reachable sums with unbounded repetition (unbounded knapsack DP) -/

/-- Compute reachable sums up to bound `target` via DP, allowing unbounded reuse of elements.
Returns the `Finset` of all sums ≤ `target` that can be formed from `nums`,
where each element of `nums` may be used any number of times.

In contrast to `subsetSums` (each element used at most once), `reachableSums` solves the
unbounded knapsack / coin change problem. The DP builds the set incrementally:
for each `k` from `0` to `target`, `k` is reachable iff `k - n` was reachable at step `k`
for some `n ∈ nums` with `n ≤ k`. -/
def reachableSums (nums : List Nat) (target : Nat) : Finset Nat :=
  match target with
  | 0 => {0}
  | m+1 =>
    let prev := reachableSums nums m
    if ∃ n ∈ nums, n ≤ m+1 ∧ ((m+1) - n) ∈ prev then
      insert (m+1) prev
    else
      prev

/-- Zero is always in the reachable sums set (empty sum). -/
lemma reachableSums_contains_zero (nums : List Nat) (target : Nat) : (0 : Nat) ∈ reachableSums nums target := by
  induction' target with m ih
  · simp [reachableSums]
  · rw [reachableSums]
    split
    · simp [ih]
    · exact ih

/-- All elements in `reachableSums nums target` are bounded by `target`. -/
lemma reachableSums_le (nums : List Nat) (target j : Nat) (h : j ∈ reachableSums nums target) :
    j ≤ target := by
  induction' target with m ih generalizing j
  · simp [reachableSums] at h; subst h; omega
  · rw [reachableSums] at h
    split at h
    · simp at h
      rcases h with (rfl | h')
      · omega
      · exact Nat.le_trans (ih _ h') (by omega)
    · exact Nat.le_trans (ih _ h) (by omega)

/-- At DP step `k+1`, the value `k+1` is inserted into `reachableSums nums (k+1)`
if there exists `n ∈ nums` with `n ≤ k+1` such that `(k+1) - n` was already reachable
at the previous step `k`. -/
lemma reachableSums_step_insert (nums : List Nat) (n k : Nat) (hn : n ∈ nums)
    (hnle : n ≤ k+1) (hprev : ((k+1) - n) ∈ reachableSums nums k) :
    (k+1) ∈ reachableSums nums (k+1) := by
  dsimp [reachableSums]
  have h_exists : ∃ n' ∈ nums, n' ≤ k+1 ∧ ((k+1) - n') ∈ reachableSums nums k := by
    refine ⟨n, hn, hnle, ?_⟩
    simpa using hprev
  simp [h_exists]

/-! ### Reachable sums: inductive characterization

While `reachableSums` is the computational DP that returns a `Finset`,
`ReachableSum` is the inductive `Prop` that characterizes which targets can be
formed as a sum of elements from `nums` (allowing arbitrary repetitions).
The equivalence theorem `reachableSum_iff_subset_sum` bridges this inductive
definition to the `∃ s, s ⊆ nums ∧ s.sum = target` formulation. -/

/-- Inductive characterization of reachable sums: `target` can be formed
as a sum of elements from `nums` (allowing arbitrary repetitions). -/
inductive ReachableSum (nums : List Nat) : Nat → Prop
  | base : ReachableSum nums 0
  | step (t x : Nat) : ReachableSum nums t → x ∈ nums → ReachableSum nums (t + x)

/-- Forward direction: `ReachableSum nums target` implies there exists a subset of `nums`
whose sum equals `target`. -/
lemma reachableSum_subset_sum (nums : List Nat) {target : Nat} (h : ReachableSum nums target) :
    ∃ s : List Nat, s ⊆ nums ∧ s.sum = target := by
  induction h with
  | base => exact ⟨[], by simp, by simp⟩
  | step t x hreach hx_mem ih =>
    rcases ih with ⟨s, hs_sub, hs_sum⟩
    refine ⟨x :: s, ?_, ?_⟩
    · intro a ha
      simp at ha
      rcases ha with (rfl | ha)
      · exact hx_mem
      · exact hs_sub ha
    · simp [hs_sum, add_comm]

/-- Reverse direction: if there exists a subset of `nums` whose sum equals `target`,
then `ReachableSum nums target`. -/
lemma subset_sum_reachableSum (nums : List Nat) (target : Nat)
    (h : ∃ s : List Nat, s ⊆ nums ∧ s.sum = target) : ReachableSum nums target := by
  rcases h with ⟨s, hs_sub, hs_sum⟩
  induction s generalizing target with
  | nil =>
    simp at hs_sum
    subst hs_sum
    exact ReachableSum.base
  | cons hd tl ih =>
    have hhd_in : hd ∈ nums := hs_sub (a := hd) (by simp)
    have htl_sub : tl ⊆ nums := by
      intro a ha
      apply hs_sub (a := a)
      simp [ha]
    simp at hs_sum
    have h_reach_tl : ReachableSum nums tl.sum := ih tl.sum htl_sub rfl
    rw [← hs_sum, add_comm]
    exact ReachableSum.step _ _ h_reach_tl hhd_in

/-- `ReachableSum nums target` iff there exists a list `s` whose elements are all
in `nums` and whose sum equals `target`. This bridges the inductive definition
to the `List.Subset`-based formulation. -/
lemma reachableSum_iff_subset_sum (nums : List Nat) (target : Nat) :
    ReachableSum nums target ↔ (∃ s : List Nat, s ⊆ nums ∧ s.sum = target) := by
  constructor
  · exact reachableSum_subset_sum nums
  · exact subset_sum_reachableSum nums target

/-! ### Partition problem

The classic partition problem: can a multiset of natural numbers be partitioned
into two subsets of equal sum? This uses `reachableSums` (allowing unbounded
repetition of elements in the DP) and returns a `Bool`. -/

/-- Core partition-checking algorithm: given a list of natural numbers,
determine whether it can be partitioned into two subsets of equal sum
(the classic "partition problem").

Uses `reachableSums` for the DP — if the total sum is even and
`total / 2` is reachable, then the list can be evenly partitioned. -/
def canEvenPartition (nums : List Nat) : Bool :=
  let total := nums.sum
  if total % 2 != 0 then false
  else (total / 2) ∈ reachableSums nums (total / 2)

end List

namespace List

/-! ### Membership in `take` under permutation -/

/-- If `l₁` is a permutation of `l₂` and `x` belongs to the first `k` elements of `l₁`,
then `x` belongs to `l₂`. This is useful when reasoning about a sorted version of a list:
any element among the first `k` of the sorted list is still in the original list. -/
lemma mem_take_perm_subset {α : Type u} {l₁ l₂ : List α} (h_perm : List.Perm l₁ l₂) (k : Nat) (x : α)
    (h : x ∈ l₁.take k) : x ∈ l₂ :=
  (List.Perm.mem_iff h_perm).mp (List.mem_of_mem_take h)

end List
