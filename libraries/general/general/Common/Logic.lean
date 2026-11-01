import Mathlib

/-! # General `Prop`-level logical lemmas

This module collects reusable logical equivalences and inference rules
at the `Prop` level. Unlike `Bool.lean` (which deals with `Bool` values
and `decide`), this file contains lemmas about `→`, `↔`, `True`, `False`,
`∧`, `∨`, and other propositional connectives. -/

namespace Logic

/-! ### Implication simplifications -/

/-- For any proposition `p`, we have `p ↔ (True → p)`.
    This is a general logical equivalence used to simplify postcondition proofs
    where the precondition is `True`. -/
lemma true_imp_iff {p : Prop} : p ↔ (True → p) := by
  simp

/-! ### `dite` / `ite` case analysis -/

/-- If a value is chosen by `ite` on a decidable proposition, then it satisfies
the natural case disjunction: either the proposition holds and the value equals
the true branch, or it does not hold and the value equals the false branch.

This generalizes `ite_eq_or_eq` by bundling the decision `c` / `¬c` with the
equality, which simplifies case-analysis proofs.

For the `dite` version see `dite_cases`. -/
theorem ite_cases {α : Sort u} (c : Prop) [d : Decidable c] (t e : α) :
    (c ∧ (if c then t else e) = t) ∨ (¬c ∧ (if c then t else e) = e) := by
  by_cases h : c
  · left; exact ⟨h, by simp [h]⟩
  · right; exact ⟨h, by simp [h]⟩

/-- `dite` version of `ite_cases`. If a value is chosen by `dite` on a decidable
proposition, then either the proposition holds and the value equals the true branch,
or it does not hold and the value equals the false branch. -/
theorem dite_cases {α : Sort u} (c : Prop) [d : Decidable c] (t e : α) :
    (c ∧ (if h : c then t else e) = t) ∨ (¬c ∧ (if h : c then t else e) = e) := by
  by_cases h : c
  · left; exact ⟨h, by simp [h]⟩
  · right; exact ⟨h, by simp [h]⟩

/-- Predicate-generalized version of `ite_cases`. If `Pt t` holds and `Pe e` holds,
then the `ite` result satisfies either `Pt` (when the condition holds) or `Pe` (otherwise).
This is useful for specification-based verification where branches have separate postconditions
modeled as predicates `Pt` and `Pe` on the result. -/
theorem ite_pred_cases {α : Sort u} (c : Prop) [d : Decidable c] (t e : α) (Pt Pe : α → Prop)
    (ht : Pt t) (he : Pe e) : (c ∧ Pt (if c then t else e)) ∨ (¬c ∧ Pe (if c then t else e)) := by
  by_cases h : c
  · left; simp [h, ht]
  · right; simp [h, he]

/-- Distribute an equality over an `ite`: if `x = (if c then t else e)`, then
`(if c then x = t else x = e)`. This is useful for rewriting `ite`-goals when the
hypothesis relates `x` to an `ite` expression. -/
lemma eq_ite_imp_ite_eq {α : Type} (c : Prop) [Decidable c] (x t e : α) (h : x = (if c then t else e)) :
    (if c then x = t else x = e) := by
  by_cases hc : c
  · simp [hc, h]
  · simp [hc, h]

/-- If a result equals a conditional `if c then t else e`, then it satisfies the
natural disjunctive specification: either `c` holds and the result equals `t`,
or `c` fails and the result equals `e`.

This is a convenience wrapper around `ite_cases` for forward reasoning: given a
hypothesis `result = (if c then t else e)`, it directly yields the case analysis
on `result` rather than on the `ite` expression itself. -/
lemma result_of_ite {α : Type} {c : Prop} [Decidable c] {t e : α} (result : α)
    (h_eq : result = (if c then t else e)) : (c ∧ result = t) ∨ (¬ c ∧ result = e) := by
  subst h_eq
  exact ite_cases c t e

/-- Elimination principle for `dite`: to prove a predicate `P` on the result of a `dite`,
it suffices to prove `P t` assuming `c` and `P e` assuming `¬c`.
This is the `Prop`-valued counterpart of `dite.rec` and a forward-reasoning
analogue of the `split` tactic. -/
theorem dite_elim {α : Sort u} (c : Prop) [d : Decidable c] (t e : α)
    (P : α → Prop) (h_pos : c → P t) (h_neg : ¬ c → P e) : P (if h : c then t else e) := by
  split
  · rename_i h; exact h_pos h
  · rename_i h; exact h_neg h

/-! ### Extending universal implications over `Nat` -/

/-- Extend a universal implication from `i+1` to `i`: if `P j → Q j` holds for all `j ≥ i+1`
and also for `j = i`, then it holds for all `j ≥ i`. Useful for linear-scan invariants. -/
lemma forall_ge_extend_left_imp {P Q : Nat → Prop} (i : Nat)
    (h_rest : ∀ j, i + 1 ≤ j → P j → Q j) (h_i : P i → Q i) :
    ∀ j, i ≤ j → P j → Q j := by
  intro j hij hpj
  by_cases h_eq : j = i
  · subst j; exact h_i hpj
  · have h_gt : i + 1 ≤ j := by omega
    exact h_rest j h_gt hpj

/-! ### Equality with three elements -/

/-- If `a = c` holds and `¬(a = b ∧ b = c)`, then `a ≠ b`.
This is useful in three-element equality case analysis: when you know two elements
are equal and the three-way equality fails, you can deduce the third pair is unequal. -/
lemma ne_of_eq_of_not_and_eq {α : Type} {a b c : α} (h_eq : a = c) (h_not : ¬(a = b ∧ b = c)) :
    a ≠ b := by
  intro h_ab
  apply h_not
  exact ⟨h_ab, h_ab.symm.trans h_eq⟩

end Logic

