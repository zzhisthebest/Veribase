import Mathlib

namespace Fin

/-! ### All ordered pairs of `Fin n` indices

The Finset of all ordered pairs `(i, j)` of `Fin n` indices, i.e. the full
Cartesian product `Finset.univ ×ˢ Finset.univ`. This is equivalent to
`Finset.univ : Finset (Fin n × Fin n)` but is more explicit about the
construction and useful as a building block for combinatorial filtering
problems (e.g., "find all index pairs satisfying a predicate").
-/

/-- The Finset of all ordered pairs `(i, j)` of `Fin n` indices. -/
def allPairs_specificDuplicate (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.product Finset.univ Finset.univ

/-! ### Basic `Fin` decomposition lemmas -/

/-- Any `Fin (Nat.succ n)` whose value is nonzero can be expressed as `Fin.succ k`
    for some `k : Fin n`. This is a fundamental splitting lemma for Fin indices:
    every element of `Fin (n+1)` is either `0` or the successor of an element of `Fin n`. -/
lemma exists_eq_succ_of_ne_zero {n : ℕ} {i : Fin (Nat.succ n)} (h : i.val ≠ 0) :
    ∃ (k : Fin n), i = Fin.succ k := by
  rcases Nat.exists_eq_succ_of_ne_zero h with ⟨m, hm⟩
  have hm_lt_n : m < n := by
    have : i.val < n + 1 := i.isLt
    have : m + 1 < n + 1 := by simpa [hm] using this
    omega
  refine ⟨⟨m, hm_lt_n⟩, ?_⟩
  apply Fin.ext
  simpa using hm

/-- Zero is never the successor of any `Fin n` index:
`(0 : Fin (Nat.succ n)) ≠ Fin.succ i`. This is the symmetric counterpart of
mathlib's `Fin.succ_ne_zero` (which states `Fin.succ i ≠ 0`).

This lemma is frequently used in induction proofs over `Fin` indices where one
needs to distinguish the `0` case from successor cases, e.g., when proving
properties about list elements accessed via `Fin` indices. -/
lemma zero_ne_succ {n : ℕ} (i : Fin n) : (0 : Fin (Nat.succ n)) ≠ Fin.succ i :=
  (Fin.succ_ne_zero i).symm

/-! ### Relational check over all `Fin n` indices except one

`allFinExceptCheck rel idx` returns `true` iff `rel idx j` holds for every `j ≠ idx` in
`Fin n`. It is a `Bool`-valued computable check for "the relation `rel` holds from `idx`
to all other indices." Together with `allFinExceptProperty` and
`allFinExceptProperty_apply`, it provides a complete interface for proving universal
properties over all-but-one indices of a `Fin n`.

Common in competitive programming for dominance/stronger-than-everyone-else checks
(e.g., LeetCode 747 "Largest Number At Least Twice of Others" where we need to verify
`nums[idx] ≥ 2 * nums[j]` for all `j ≠ idx`). -/

/-- `allFinExceptCheck rel idx` checks that `rel idx j` holds for every
`j : Fin n` such that `j ≠ idx`. Returns a `Bool`. -/
def allFinExceptCheck {n : Nat} (rel : Fin n → Fin n → Prop)
    [∀ i j, Decidable (rel i j)] (idx : Fin n) : Bool :=
  (List.finRange n).all fun j =>
    decide (j = idx) || decide (rel idx j)

/-- `allFinExceptProperty rel idx` is the `Prop` version of `allFinExceptCheck`:
it holds when `rel idx j` holds for all `j ≠ idx`. -/
def allFinExceptProperty {n : Nat} (rel : Fin n → Fin n → Prop)
    [∀ i j, Decidable (rel i j)] (idx : Fin n) : Prop :=
  allFinExceptCheck rel idx = true

/-- If `allFinExceptProperty rel idx` holds and `j ≠ idx`, then `rel idx j`. -/
lemma allFinExceptProperty_apply {n : Nat} {rel : Fin n → Fin n → Prop}
    [∀ i j, Decidable (rel i j)] {idx j : Fin n}
    (h_all : allFinExceptProperty rel idx) (h_ne : j ≠ idx) :
    rel idx j := by
  unfold allFinExceptProperty allFinExceptCheck at h_all
  have h_item := (List.all_eq_true.mp h_all) j (List.mem_finRange j)
  rcases Bool.or_eq_true_iff.mp h_item with h_eq | h_rel
  · exact (h_ne (decide_eq_true_iff.mp h_eq)).elim
  · exact decide_eq_true_iff.mp h_rel

/-- `DecidablePred` instance for `allFinExceptProperty rel`, enabling `if`/`decide`
on `allFinExceptProperty rel idx`. -/
instance allFinExceptPropertyDecidable {n : Nat} (rel : Fin n → Fin n → Prop)
    [∀ i j, Decidable (rel i j)] :
    DecidablePred (allFinExceptProperty rel) := by
  intro idx
  unfold allFinExceptProperty
  infer_instance

/-! ### All ordered pairs check

`allFinPairsBool n p` checks whether the proposition `p i j` holds for every
ordered pair `(i, j)` of indices of `Fin n`.  Returns a `Bool`.

This is a universal quantifier over the full Cartesian product `Fin n × Fin n`,
useful for combinatorial checks like "every element is comparable to every other
element" or "the array is strictly monotonic." -/

/-- `allFinPairsBool n p` returns `true` iff `p i j` holds for all `i j : Fin n`.

Uses `List.finRange` to iterate over all indices, and `decide` to convert the
`Prop` to `Bool`. Requires `Decidable` for all pairs. -/
def allFinPairsBool (n : Nat) (p : Fin n → Fin n → Prop) [∀ a b, Decidable (p a b)] : Bool :=
  (List.finRange n).all fun a =>
    (List.finRange n).all fun b =>
      decide (p a b)

/-- `allFinPairsBool n p = true` iff `p i j` holds for all `i j : Fin n`. -/
lemma allFinPairsBool_eq_true_iff (n : Nat) (p : Fin n → Fin n → Prop)
    [∀ a b, Decidable (p a b)] :
    allFinPairsBool n p = true ↔ ∀ a b, p a b := by
  unfold allFinPairsBool
  simp

end Fin
