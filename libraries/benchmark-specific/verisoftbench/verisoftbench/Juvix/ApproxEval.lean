import Juvix.Core.Main.Semantics.Approx.Congruence

open Juvix.Core.Main

namespace Juvix.Core.Main

/-! Lemmas about approximation preserving evaluation, harvested from solved training problems. -/

/--
If `e₁ ≲⟨env₁, env₂⟩ e₂` (parameterized approximation) and `e₁` evaluates to `v₁`
under `env₁`, then `e₂` evaluates to some `v₂` under `env₂` such that `v₁ ≲ᵥ v₂`.
-/
lemma Expr.Approx.Param.eval {e₁ e₂ : Expr} {env₁ env₂ : Env} {v₁ : Value}
    (h : e₁ ≲⟨env₁, env₂⟩ e₂) (heval : env₁ ⊢ e₁ ↦ v₁) :
    ∃ v₂, env₂ ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ :=
  h v₁ heval

/--
If `e₁ ≲ e₂` (non-parameterized expression approximation) and the environments
are related (`env₁ ≲ₑ env₂`), then evaluating `e₁` under `env₁` yields a value
that is approximated by the value obtained from evaluating `e₂` under `env₂`.
-/
lemma Expr.Approx.eval_preserved {e₁ e₂ : Expr} (h : e₁ ≲ e₂)
    (env₁ env₂ : Env) (henv : env₁ ≲ₑ env₂) (v₁ : Value) (heval : env₁ ⊢ e₁ ↦ v₁) :
    ∃ v₂, env₂ ⊢ e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ :=
  Expr.Approx.Param.eval (h env₁ env₂ henv) heval

/--
Soundness of the approximation relation under context substitution:
if `e₁ ≲ e₂`, then for any context `C` and approximating environments,
evaluating `C.subst e₁` yields a value that is approximated by evaluating
`C.subst e₂`.
-/
lemma Expr.Approx.Context.preserved (e₁ e₂ : Expr) :
  e₁ ≲ e₂ →
  ∀ (C : Context) env₁ env₂ v₁,
  env₁ ≲ₑ env₂ → env₁ ⊢ C.subst e₁ ↦ v₁ →
  ∃ v₂, env₂ ⊢ C.subst e₂ ↦ v₂ ∧ v₁ ≲ᵥ v₂ := by
  intro h C env₁ env₂ v₁ henv heval
  have h_cong : C.subst e₁ ≲ C.subst e₂ := Expr.Approx.congruence C h
  exact Expr.Approx.eval_preserved h_cong env₁ env₂ henv v₁ heval

end Juvix.Core.Main
