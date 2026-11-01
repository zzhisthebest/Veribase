import Mathlib

namespace List


/-! ### `lengthInRange` — bounded list length predicate -/

/-- A predicate asserting that the length of a list is bounded between `lo` and `hi` inclusive.
Useful for preconditions like "the list has between 1 and 100 elements". -/
def lengthInRange {α : Type u} (lo hi : Nat) (xs : List α) : Prop :=
  lo ≤ xs.length ∧ xs.length ≤ hi



/-! ### `Nat.max` and list length -/

/-- The maximum of the lengths of two cons lists equals the successor of the maximum
of the lengths of the tails: `max (|a::l₁|) (|b::l₂|) = (max |l₁| |l₂|) + 1`. -/
lemma max_length_cons_cons {α : Type u} (a b : α) (l1 l2 : List α) :
    Nat.max (a :: l1).length (b :: l2).length = (Nat.max l1.length l2.length).succ := by
  simp [Nat.succ_max_succ]



/-! ### Basic length lemmas -/

/-- If a list has length at least 1, then it has positive length. -/
lemma length_pos_of_one_le_length {α : Type u} {l : List α} (h : 1 ≤ l.length) : 0 < l.length := by
  omega

/-- For a nonempty list, `length - 1` is strictly less than `length`. -/
lemma length_sub_one_lt_length {α : Type u} {l : List α} (h : 0 < l.length) : l.length - 1 < l.length := by
  omega

/-- The length of `a :: b :: l` equals `l.length + 2`. -/
lemma length_cons_cons {α : Type _} (a b : α) (l : List α) : (a :: b :: l).length = l.length + 2 := by
  simp

/-- The length of the rotated list `(l.drop k ++ l.take k)` equals the length of `l`.
Useful for problems involving circular shifts or rotations of lists. -/
lemma length_drop_append_take {α : Type u} (l : List α) (k : Nat) :
    (l.drop k ++ l.take k).length = l.length := by
  rw [List.length_append, List.length_drop, List.length_take]
  omega

/-- If an element is in the concatenation of the drop and take of a list,
it is in the original list. This is the membership counterpart of
`length_drop_append_take` — any element in a rotation `l.drop n ++ l.take n`
was present in the original list `l`. -/
lemma mem_of_mem_append_drop_take {α : Type u} {l : List α} {x : α} {n : Nat}
    (h : x ∈ (l.drop n) ++ (l.take n)) : x ∈ l := by
  rcases List.mem_append.mp h with (h' | h')
  · exact List.mem_of_mem_drop h'
  · exact List.mem_of_mem_take h'

/-- Predicate: the length of list `l` is at most `n`. Useful as a precondition
for problems requiring input length bounds (e.g., LeetCode constraints). -/
def lengthLe {α : Type _} (l : List α) (n : Nat) : Prop :=
  l.length ≤ n

/-- If a list is nonempty, then mapping any function over it yields a nonempty list. -/
lemma map_ne_nil_of_ne_nil {α β : Type} (f : α → β) {l : List α} (h : l ≠ []) : l.map f ≠ [] := by
  intro hmap
  apply h
  have hlen := congrArg List.length hmap
  simpa using hlen



/-! ### Length predicates -/

/-- A `Prop` predicate asserting that a list has length at most `n`.
This is useful for writing preconditions (e.g., "the input list has at most 10000 elements"). -/
def lenLe {α : Type} (l : List α) (n : Nat) : Prop :=
  l.length ≤ n


end List

namespace List


/-! ### `allProp` — universal quantification over lists -/

/-- A predicate stating that all elements of a list satisfy `p`.
This is the `Prop`-valued counterpart of `List.all` (which returns a `Bool`). -/
def allProp (xs : List α) (p : α → Prop) : Prop :=
  ∀ x, x ∈ xs → p x

/-- `List.allProp` is preserved under `List.take`: if all elements of `xs` satisfy `p`,
then all elements of `xs.take n` also satisfy `p`. -/
lemma allProp_of_take {α : Type} (xs : List α) (p : α → Prop) (n : Nat)
    (h : allProp xs p) : allProp (xs.take n) p := by
  intro x hx
  apply h
  exact List.mem_of_mem_take hx

/-- `List.all` is preserved under `List.take` (Bool version): if `p` holds for all elements of `L`,
then it holds for all elements of the first `k` elements. -/
lemma all_of_take {α : Type} (p : α → Bool) (L : List α) (k : Nat) (h : L.all p = true) :
    (List.take k L).all p = true := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  exact h x (List.mem_of_mem_take hx)

/-! ### `allLt` — all elements less than a bound -/

/-- Boolean predicate: all elements of `xs` are strictly less than `bound`. -/
def allLt (bound : Nat) (xs : List Nat) : Bool :=
  xs.all (fun i => decide (i < bound))


lemma allLt_nil (bound : Nat) : allLt bound [] = true := rfl

/-! ### Take membership lemmas -/

/-- The head of a nonempty list is in the first `n` elements when `n > 0`. -/
lemma head_mem_take {α : Type} {xs : List α} (hne : xs ≠ []) (n : Nat) (hn : 0 < n) :
    xs.head hne ∈ xs.take n := by
  rcases List.exists_cons_of_ne_nil hne with ⟨a, as, rfl⟩
  induction n with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ m ih => simp

/-- If `x` is in the first `n` elements of `L.filter p`, then `x` is in `L` and `p x` holds. -/
lemma mem_of_mem_take_filter {α : Type} {L : List α} {p : α → Bool} {x : α} {n : Nat}
    (h : x ∈ (L.filter p).take n) : x ∈ L ∧ p x := by
  have hmem_filter : x ∈ L.filter p := List.mem_of_mem_take h
  exact List.mem_filter.mp hmem_filter

/-- If a property `P` holds for all elements of a list, it also holds for all elements of
any prefix obtained via `take n`. This is a direct `∀` version of `allProp_of_take`. -/
lemma forall_mem_take_of_forall_mem {α : Type u} {P : α → Prop} {xs : List α} (n : Nat)
    (h : ∀ x, x ∈ xs → P x) : ∀ x, x ∈ xs.take n → P x := by
  intro x hx
  apply h x
  exact List.mem_of_mem_take hx

/-- If a binary relation `R` holds for all pairs of elements in a list, it also holds for
all pairs in any prefix obtained via `take n`. This is the binary version of
`forall_mem_take_of_forall_mem`. -/
lemma pairwise_forall_mem_take {α : Type u} {R : α → α → Prop} {xs : List α} (n : Nat)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, R a b) : ∀ a ∈ xs.take n, ∀ b ∈ xs.take n, R a b := by
  intro a ha b hb
  apply h a (List.mem_of_mem_take ha) b (List.mem_of_mem_take hb)

/-- An element is in `(List.range n).filter p` iff it is below `n` and satisfies `p`. -/
lemma mem_filter_range_iff {p : Nat → Bool} {n a : Nat} :
    a ∈ (List.range n).filter p ↔ a < n ∧ p a = true := by
  simp [List.mem_filter, List.mem_range]

/-- Filter a list using a `Prop` predicate via `decide`.
`filterByDecidable P l` is syntactic sugar for `l.filter (λ x => decide (P x))`,
bridging `Prop` predicates to the `Bool`-based `List.filter`. -/
def filterByDecidable {α : Type u} (P : α → Prop) [DecidablePred P] (l : List α) : List α :=
  l.filter (λ x => decide (P x))

/-- Membership in a list filtered by `decide` of a `Prop` predicate is equivalent
to membership in the original list together with the proposition holding.
This bridges `List.mem_filter` (which uses `Bool` predicates) to `Prop` predicates
via `decide`. -/
lemma mem_filter_decide_iff {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (x : α) :
    x ∈ List.filter (λ a => decide (p a)) l ↔ x ∈ l ∧ p x := by
  simp

/-- Filtering a `Nodup` list with a decidable predicate via `decide` preserves `Nodup`.
This lifts `List.Nodup.filter` from `Bool` predicates to `Prop` predicates with `DecidablePred`. -/
lemma nodup_filter_decide {α : Type u} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p]
    (h : List.Nodup l) : List.Nodup (l.filter (λ x => decide (p x))) :=
  List.Nodup.filter (λ x => decide (p x)) h

/-- If `x ∈ l` and `p x` holds, then `x` belongs to the list filtered by `decide (p ·)`.
This is the forward direction of `mem_filter_decide_iff`. -/
lemma mem_filter_decide {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (x : α)
    (hl : x ∈ l) (hp : p x) : x ∈ List.filter (λ a => decide (p a)) l :=
  ((mem_filter_decide_iff l p x).mpr ⟨hl, hp⟩)

/-- If `x` belongs to a list filtered by `decide (p ·)`, then `p x` holds.
This is the elimination lemma for `decide`-based filters. -/
lemma of_mem_filter_decide {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (x : α)
    (h : x ∈ List.filter (λ a => decide (p a)) l) : p x :=
  ((mem_filter_decide_iff l p x).mp h).right

/-- A list filtered by `decide (p ·)` is empty iff no element satisfies `p`.
This is the `Prop`/`decide` companion to `List.filter_eq_nil_iff`, bridging from
`Bool`-predicate filters to `Prop`-predicate filters via `decide`. -/
lemma filter_decide_eq_nil_iff {α : Type} {l : List α} {p : α → Prop} [DecidablePred p] :
    l.filter (fun x => decide (p x)) = [] ↔ ∀ x ∈ l, ¬ p x := by
  simp

/-- An element is in `filter (λ x => decide (p x)) (List.range n)` iff it is below `n`
and satisfies the `Prop` predicate `p`. This is the `Prop`-based version of `mem_filter_range_iff`. -/
lemma mem_range_decide_filter_iff (p : Nat → Prop) [DecidablePred p] (a n : Nat) :
    a ∈ List.filter (λ x => decide (p x)) (List.range n) ↔ a < n ∧ p a := by
  rw [mem_filter_decide_iff (List.range n) p a, List.mem_range]

/-- Filter membership can be rewritten when the filter condition is equivalent to a `Prop`.
This generalizes `List.mem_filter` to cases where the `Bool` predicate `p` is known to be
equivalent to a `Prop` `q` at the specific element `a`. -/
lemma mem_filter_iff_of_iff {α : Type} {l : List α} {p : α → Bool} {q : α → Prop} {a : α}
    (hpq : p a ↔ q a) : a ∈ l.filter p ↔ a ∈ l ∧ q a := by
  rw [List.mem_filter, hpq]

/-- If an element is not present in a list, filtering the list for elements equal to that
element yields the empty list. This is the specialization of `List.filter_eq_nil_iff`
to the predicate `(· = a)`. -/
lemma filter_eq_nil_of_not_mem {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∉ l) :
    l.filter (fun x => x = a) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  intro hbeq_true
  have heq : x = a := of_decide_eq_true hbeq_true
  subst heq
  exact h hx

/-! ### Filter-empty lemmas for natural numbers -/

/-- If every element of `l` is at least `1`, then filtering `l` for elements equal to `0`
yields the empty list. Useful in problems where arrays contain only positive integers:
knowing `∀ x ∈ l, 1 ≤ x` allows us to deduce that no element is `0`. -/
lemma filter_eq_nil_of_all_pos (l : List Nat) (h : ∀ x ∈ l, 1 ≤ x) :
    l.filter (fun x => decide (x = 0)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  rcases List.mem_filter.mp hx with ⟨hx_mem, hx_eq⟩
  have hx0 : x = 0 := by simpa using hx_eq
  subst hx0
  have hpos := h 0 hx_mem
  omega

/-- `allPos l` asserts that every element of `l` is positive (`> 0`).
This is equivalent to `∀ x ∈ l, 1 ≤ x`. -/
def allPos (l : List Nat) : Prop :=
  ∀ n ∈ l, n > 0

/-- Boolean decidable version of `allPos`. Returns `true` iff every element of `l` is strictly positive. -/
def allPosBool (l : List Nat) : Bool :=
  l.all (fun x => decide (0 < x))

/-- The `Bool` predicate `allPosBool` coincides with the `Prop` condition `allPos`.
This lemma allows converting between decidable checks and propositional reasoning. -/
lemma allPosBool_eq_true_iff (l : List Nat) :
    allPosBool l = true ↔ allPos l := by
  unfold allPosBool allPos
  rw [List.all_eq_true]
  simp

/-- When every element of a nonempty `List Nat` is positive, the sum is also positive. -/
lemma sum_pos_of_all_pos_of_nonempty (l : List Nat) (hne : l ≠ []) (hall : ∀ x ∈ l, 0 < x) :
    0 < l.sum := by
  induction' l with h t ih
  · exact absurd rfl hne
  · simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at hall ⊢
    rcases hall with ⟨hh, ht⟩
    have hsum : 0 ≤ t.sum := Nat.zero_le _
    nlinarith

/-- `List.any` with `decide` over `List.range n` is equivalent to the existence
of an index `i < n` satisfying the `Prop` predicate `P`. This bridges the `Bool`-based
`List.any` API with the `Prop`-based `∃` quantifier via `decide`. -/
lemma range_any_decide_iff {n : Nat} (P : Nat → Prop) [DecidablePred P] :
    ((List.range n).any (fun i => decide (P i))) = true ↔ ∃ i, i < n ∧ P i := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    rcases h with ⟨i, hi, hd⟩
    rw [decide_eq_true_iff] at hd
    rw [List.mem_range] at hi
    exact ⟨i, hi, hd⟩
  · intro ⟨i, hi, hP⟩
    rw [List.any_eq_true]
    exact ⟨i, by rw [List.mem_range]; exact hi, by rw [decide_eq_true_iff]; exact hP⟩

/-- `List.any` over `range n` with a `Bool` predicate is equivalent to the existence
of an index `i < n` with `p i = true`. This is the `Bool`-predicate companion of
`range_any_decide_iff` (which uses a `Prop` predicate via `decide`). -/
lemma range_any_iff (n : Nat) (p : Nat → Bool) :
    (List.range n).any p = true ↔ ∃ i, i < n ∧ p i = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi_mem, hi_p⟩
    rw [List.mem_range] at hi_mem
    exact ⟨i, hi_mem, hi_p⟩
  · rintro ⟨i, hi, hi_p⟩
    exact ⟨i, List.mem_range.mpr hi, hi_p⟩

/-! ### Nested `any` — existential characterization -/

/-- Double-nested `List.any` on the same list is equivalent to the existence of a pair
of elements (both in `l`) satisfying the boolean predicate `p`.

Formally: `l.any (λ a => l.any (λ b => p a b)) = true ↔ ∃ a b, a ∈ l ∧ b ∈ l ∧ p a b = true`. -/
lemma any_any_iff {α : Type} (l : List α) (p : α → α → Bool) :
    l.any (fun a => l.any (fun b => p a b)) = true ↔ ∃ a b, a ∈ l ∧ b ∈ l ∧ p a b = true := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    rcases h with ⟨a, ha, h_any⟩
    rw [List.any_eq_true] at h_any
    rcases h_any with ⟨b, hb, hp⟩
    exact ⟨a, b, ha, hb, hp⟩
  · intro ⟨a, b, ha, hb, hp⟩
    rw [List.any_eq_true]
    exact ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, hp⟩⟩

/-- A non-empty list satisfies `.any (fun _ => true) = true`.
This is useful when a precondition checks that a list is non-empty
via `!l.isEmpty`, and you need to propagate that to an `any` expression. -/
lemma any_const_true_of_ne_nil {α : Type u} {l : List α} (h : l ≠ []) : l.any (fun _ : α => true) = true := by
  cases l with
  | nil => contradiction
  | cons _ _ => simp


end List

namespace List

/-! ### `allDigits` — check if all characters in a list are digits -/

/-- Check whether every character in a list is a digit.
Uses `Char.isDigit` (Unicode-aware). Returns `true` for the empty list. -/
def allDigits (cs : List Char) : Bool :=
  cs.all (·.isDigit)

end List

namespace List

/-! ### Binary list predicate -/

/-- A list of natural numbers is binary if every element is either `0` or `1`. -/
def isBinary (l : List Nat) : Prop :=
  ∀ x ∈ l, x = 0 ∨ x = 1

/-- Bool (computable) version of `isBinary`: checks whether every element of `l` is
either `0` or `1`. Uses `List.all` with `BEq` comparison for efficient computation. -/
def isBinaryB (l : List Nat) : Bool :=
  l.all (fun x => x == 0 || x == 1)


lemma isBinaryB_eq_true_iff (l : List Nat) : isBinaryB l = true ↔ isBinary l := by
  simp [isBinaryB, isBinary, List.all_eq_true]


end List


namespace List

/-! ### `allEq` — check if all elements equal a given value -/

/-- Check whether all elements of `l` equal `a`. Returns `true` for the empty list.
`allEq a [x₁, …, xₙ] ↔ ∀ i, xᵢ = a`. -/
def allEq [BEq α] (a : α) : List α → Bool
  | [] => true
  | x :: xs => (x == a) && allEq a xs

/-- `allEq a l = true` iff every element of `l` equals `a`. -/
lemma allEq_iff [BEq α] [LawfulBEq α] (a : α) (l : List α) : allEq a l = true ↔ ∀ x ∈ l, x = a := by
  induction l with
  | nil => simp [allEq]
  | cons hd tl ih =>
    simp only [allEq, Bool.and_eq_true, beq_iff_eq, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨h0, ht⟩ x (rfl | hx)
      · exact h0
      · exact ht x hx
    · intro hall
      exact ⟨hall hd (Or.inl rfl), fun x hx => hall x (Or.inr hx)⟩

end List

namespace List

open List

/-! ### Lemmas about `List.Chain` with transitive / irreflexive relations -/

/-- If `R` is transitive and irreflexive, and `List.Chain R a l`, then `a` is not in `l`. -/
lemma Chain.not_mem [IsTrans α R] [IsIrrefl α R] {a : α} {l : List α}
    (h : List.Chain R a l) : a ∉ l := by
  intro ha
  have hR := h.rel ha
  exact irrefl a hR

/-- If `R` is transitive, `List.Chain R a l`, `R a x`, and every element of `l` is related
    to `x` by `R`, then `List.Chain R a (l ++ [x])`. -/
lemma Chain.append_singleton [IsTrans α R] {a x : α} {l : List α}
    (hchain : List.Chain R a l) (hax : R a x) (hall : ∀ y ∈ l, R y x) :
    List.Chain R a (l ++ [x]) := by
  induction l generalizing a with
  | nil =>
    exact List.Chain.cons hax List.Chain.nil
  | cons b l' ih =>
    cases hchain
    case cons hab hchain_b =>
      have hbx : R b x := hall b (by simp)
      have hall' : ∀ y ∈ l', R y x := by
        intro y hy; apply hall y; simp [hy]
      have ih_b := ih hchain_b hbx hall'
      exact List.Chain.cons hab ih_b

end List

namespace List

/-! ### `filterByDecide` — filter a list by a `DecidablePred`

`filterByDecide l p` applies a `Prop` predicate `p` to filter `l`,
using `decide` to convert it to a `Bool` predicate for `List.filter`.

This is a convenience wrapper around `l.filter (fun x => decide (p x))`. -/

/-- Filter a list by a `Prop` predicate, applying `decide` to convert it to a `Bool`. -/
def filterByDecide {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : List α :=
  l.filter (fun x => decide (p x))

/-- Membership in `filterByDecide l p` is equivalent to being in `l` and satisfying `p`. -/
lemma mem_filterByDecide_iff {α : Type} {l : List α} {p : α → Prop} [DecidablePred p] {x : α} :
    x ∈ filterByDecide l p ↔ x ∈ l ∧ p x := by
  simp [filterByDecide, decide_eq_true_iff]

/-- `List.any` with `decide` over an arbitrary list `l` is equivalent to the existence
of an element in `l` satisfying the `Prop` predicate `p`. This lifts `List.any_eq_true`
through the `decide` boundary. -/
lemma any_decide_eq_true {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.any (fun x => decide (p x))) = true ↔ ∃ x ∈ l, p x := by
  simp [List.any_eq_true, decide_eq_true_iff]

end List

namespace List

/--
If `R a (f a)` holds for every `a : α`, then `List.Forall₂ R l (List.map f l)`.
Useful for establishing that a list of results computed by `f` matches a relational specification.
-/
lemma forall₂_map_right {α β : Type _} (R : α → β → Prop) (l : List α) (f : α → β)
    (h : ∀ a, R a (f a)) : List.Forall₂ R l (List.map f l) := by
  rw [List.forall₂_map_right_iff]
  refine List.forall₂_same.2 ?_
  intro a _
  exact h a

/-- If `f` maps each `a : α` to a `List β`, and `List.Forall (R a) (f a)` holds for all `a`,
then `Forall₂` relates `l` and `l.map f` with a nested `Forall` condition.
This is the list-valued analogue of `forall₂_map_right` — each element on the right
side is expanded to a list and the relation wraps `List.Forall`. -/
lemma forall₂_map_of_forall {α β : Type} {f : α → List β} {R : α → β → Prop} {l : List α}
    (h : ∀ a, List.Forall (R a) (f a)) :
    List.Forall₂ (fun (a : α) (bs : List β) => List.Forall (R a) bs) l (l.map f) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a as ih =>
    rw [List.map_cons]
    exact List.Forall₂.cons (h a) ih

end List
