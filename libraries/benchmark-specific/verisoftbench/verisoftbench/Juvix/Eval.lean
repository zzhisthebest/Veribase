import Juvix.Core.Main.Semantics.Eval

open Juvix.Core.Main

namespace Juvix.Core.Main

/-! Lemmas about `Eval.Defined` (termination) harvested from solved training problems. -/

/--
If `env ⊢ e ↦ v` (e evaluates to v), then `env ⊢ e ↓` (e terminates).
This is the introduction rule for `Eval.Defined`.
-/
lemma Eval.Defined.intro {env e v} (h : env ⊢ e ↦ v) : env ⊢ e ↓ := ⟨v, h⟩

/--
If both operands of a binary operation evaluate to integer constants,
then the binary operation terminates (i.e. is defined).
-/
lemma Eval.Defined.binop {env op e₁ e₂ c₁ c₂} :
    env ⊢ e₁ ↦ Value.const (Constant.int c₁) →
    env ⊢ e₂ ↦ Value.const (Constant.int c₂) →
    env ⊢ Expr.binop op e₁ e₂ ↓ := by
  intro h₁ h₂
  apply Eval.Defined.intro
  exact Eval.binop h₁ h₂

/--
If the matching branch body `e` evaluates to `v` under the environment
extended with the constructor arguments, then `Expr.branch name vnames e e'`
evaluates to `v` under the environment extended with the constructor value
`Value.constr_app name args_rev`.

This is a convenience wrapper around the `Eval.branch_matches` constructor
that makes `v`, `vnames`, and `e'` explicit.
-/
lemma Eval.branch_matches_eval {env name vnames args_rev e e' v}
    (h : (args_rev.map Object.value ++ env) ⊢ e ↦ v) :
    (Value.constr_app name args_rev ∷ env) ⊢ Expr.branch name vnames e e' ↦ v :=
  Eval.branch_matches h

/--
If the matching branch body `e` terminates under the extended environment,
then `Expr.branch name vnames e e'` terminates under the constructor-extended
environment.
-/
lemma Eval.Defined.branch_matches {env name vnames args_rev e e'}
    (h : (args_rev.map Object.value ++ env) ⊢ e ↓) :
    (Value.constr_app name args_rev ∷ env) ⊢ Expr.branch name vnames e e' ↓ := by
  rcases h with ⟨v, h_eval⟩
  exact ⟨v, Eval.branch_matches_eval h_eval⟩

end Juvix.Core.Main
