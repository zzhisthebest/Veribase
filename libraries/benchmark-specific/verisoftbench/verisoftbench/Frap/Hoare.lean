import Frap.Hoare

/-!
# Hoare Logic Rules for Conditionals

Provides the missing `hoare_if` rule (the Hoare logic rule for `c_if`) and its
supporting lemma `hoare_if_cases`, complementing the proof rules already provided
by `Frap.Hoare` (`hoare_skip`, `hoare_seq`, `hoare_asgn`, `hoare_consequence`, etc.).

Also includes a helper lemma `not_beval_of_beval_false` for converting a `beval`
equality to a negation.
-/

set_option quotPrecheck false

namespace Imp
open AExp
open BExp
open Com
open CEval

/-- If `beval st b` evaluates to `false`, then `beval st b` is not true. -/
theorem not_beval_of_beval_false {st : State} {b : BExp} (h : beval st b = false) :
    ¬ beval st b := by
  simp [h]

/--
Case analysis lemma for Hoare triples of `c_if`: if both branches satisfy their
respective Hoare triples and the conditional `c_if b c₁ c₂` evaluates from `st`
to `st'` with the precondition `P st`, then the postcondition `Q st'` holds.

This is the core elimination lemma underlying the `hoare_if` proof rule.
-/
theorem hoare_if_cases (P Q : State → Prop) (b : BExp) (c₁ c₂ : Com) (st st' : State)
    (hTrue : {* fun st => P st ∧ beval st b *} c₁ {* Q *})
    (hFalse : {* fun st => P st ∧ ¬(beval st b) *} c₂ {* Q *})
    (hPre : P st) (hEval : CEval (c_if b c₁ c₂) st st') : Q st' := by
  cases hEval
  case e_ifTrue hb hEval₁ =>
    exact hTrue st st' ⟨hPre, hb⟩ hEval₁
  case e_ifFalse hb hEval₂ =>
    exact hFalse st st' ⟨hPre, not_beval_of_beval_false hb⟩ hEval₂

/--
Hoare logic rule for conditionals: if `c₁` satisfies
`{P ∧ b} c₁ {Q}` and `c₂` satisfies `{P ∧ ¬b} c₂ {Q}`,
then `c_if b c₁ c₂` satisfies `{P} c_if b c₁ c₂ {Q}`.
-/
theorem hoare_if P Q b c₁ c₂ :
    {* fun st => P st ∧ beval st b *} c₁ {* Q *}
    → {* fun st => P st ∧ ¬(beval st b) *} c₂ {* Q *}
    → {* P *} c_if b c₁ c₂ {* Q *} := by
  intro h₁ h₂ st st' hPre hEval
  exact hoare_if_cases P Q b c₁ c₂ st st' h₁ h₂ hPre hEval

end Imp
