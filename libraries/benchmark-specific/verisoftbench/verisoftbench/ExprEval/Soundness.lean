import ExprEval.Expr
import ExprEval.Steps
import Mathlib.Tactic

/-!
# Soundness of the step relations for `ArExpr` and `BoolExpr`

Theorems showing that the step relations `ArStep` and `BoolStep` preserve evaluation:
evaluating the result of a step always yields the same value as evaluating the original expression.
-/

/-- If `e₁` steps to `e₂` via `BoolStep`, they evaluate to the same boolean. -/
theorem eval_bool_eq_of_boolStep {V : Type} {val : V → Int} {e₁ e₂ : BoolExpr V} :
    BoolStep V val e₁ e₂ → eval_bool V val e₁ = eval_bool V val e₂ := by
  intro h
  refine @BoolStep.rec V val
    (fun e e' _ => eval V val e = eval V val e')
    (fun e e' _ => eval_bool V val e = eval_bool V val e')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    e₁ e₂ h
  · intro var; rfl
  · intro n₁ n₂; rfl
  · intro n₁ n₂; rfl
  · intro n₁ n₂; rfl
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro e e' a b hb ih; simp [eval, ih]
  · intro a b; simp [eval, eval_bool]
  · intro a b; simp [eval, eval_bool]
  · intro b; simp [eval_bool]
  · intro e; simp [eval_bool]
  · intro e; simp [eval_bool]
  · intro e; simp [eval_bool]
  · intro e; simp [eval_bool]
  · intro n₁ n₂ hlt; simp [eval, eval_bool, hlt]
  · intro n₁ n₂ hge; simp [eval, eval_bool]; exact mod_cast (by omega)
  · intro n₁ n₂ heq; simp [eval, eval_bool, heq]
  · intro n₁ n₂ hne
    simp [eval, eval_bool]
    intro heq
    have h : (n₁ != n₂) = false := by simp [heq]
    rw [h] at hne
    simp at hne
  · intro e₁ e₁' e₂ a ih; simp [eval_bool, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval_bool, ih]
  · intro e₁ e₂ e₂' a ih; simp [eval_bool, ih]
  · intro e₁ e₂ e₂' a ih; simp [eval_bool, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval_bool, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval_bool, ih]
  · intro e e' a ih; simp [eval_bool, ih]

/-- If `e₁` steps to `e₂` via `ArStep`, they evaluate to the same integer. -/
theorem eval_eq_of_arStep {V : Type} {val : V → Int} {e₁ e₂ : ArExpr V} :
    ArStep V val e₁ e₂ → eval V val e₁ = eval V val e₂ := by
  intro h
  refine @ArStep.rec V val
    (fun e e' _ => eval V val e = eval V val e')
    (fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    e₁ e₂ h
  · intro var; rfl
  · intro n₁ n₂; rfl
  · intro n₁ n₂; rfl
  · intro n₁ n₂; rfl
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro e₁ e₁' e₂ a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro n e₂ e₂' a ih; simp [eval, ih]
  · intro e e' a b hb _; simp [eval, eval_bool_eq_of_boolStep hb]
  · intro a b; simp [eval, eval_bool]
  · intro a b; simp [eval, eval_bool]
  · intro b; trivial
  · intro e; trivial
  · intro e; trivial
  · intro e; trivial
  · intro e; trivial
  · intro n₁ n₂ hlt; trivial
  · intro n₁ n₂ hge; trivial
  · intro n₁ n₂ heq; trivial
  · intro n₁ n₂ hne; trivial
  · intro e₁ e₁' e₂ a ih; trivial
  · intro e₁ e₁' e₂ a ih; trivial
  · intro e₁ e₂ e₂' a ih; trivial
  · intro e₁ e₂ e₂' a ih; trivial
  · intro e₁ e₁' e₂ a ih; trivial
  · intro e₁ e₁' e₂ a ih; trivial
  · intro e e' a ih; trivial

/-- If `e` steps to `e'` via `BoolStepStar`, they evaluate to the same boolean. -/
theorem eval_bool_eq_of_boolStepStar {V : Type} {val : V → Int} {e e' : BoolExpr V} :
    BoolStepStar V val e e' → eval_bool V val e = eval_bool V val e' := by
  intro hstar
  induction hstar with
  | refl => rfl
  | trans _ _ _ hstep _ ih =>
    rw [eval_bool_eq_of_boolStep hstep, ih]
