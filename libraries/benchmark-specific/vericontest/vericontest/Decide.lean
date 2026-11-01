import Mathlib

/-! # Decide

Lemmas about `decide` and `Decidable` relating `Bool` and `Prop`.
-/

/-- `decide p` coerce-equals `p` as propositions. This is a concise form of `propext decide_eq_true_iff`. -/
lemma decide_eq_prop {p : Prop} [Decidable p] : decide p = p :=
  propext decide_eq_true_iff

/-- Membership in a `filter` with a `decide`-based predicate is equivalent to membership
in the original list and satisfaction of the predicate. This bridges `List.mem_filter`
(which uses `Bool` predicates directly) to `Prop`-valued predicates via `decide`. -/
lemma mem_filter_decide_iff {α : Type} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p] (x : α) :
    x ∈ l.filter (λ a => decide (p a)) ↔ x ∈ l ∧ p x := by
  simp [List.mem_filter, decide_eq_true]
