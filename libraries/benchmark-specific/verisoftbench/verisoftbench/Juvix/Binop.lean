import Juvix.Core.Main.Semantics.Equiv

open Juvix.Core.Main

namespace Juvix.Core.Main

/-! Lemmas about binary operations (`Expr.binop`) and approximation/equivalence relations,
harvested from solved training problems. -/

/--
If `Value.const c₁` approximates `Value.const c₂`, then the constants are equal.
Injection lemma for `Value.Approx` on `Value.const` values.
-/
lemma Value.Approx.const_inj {c₁ c₂ : Constant} (h : Value.const c₁ ≲ᵥ Value.const c₂) : c₁ = c₂ := by
  have h_eq := (Value.Approx.const_left.mp h)
  injection h_eq

/--
If `a₁` approximates `Expr.const (Constant.int i₁)` and `a₂` approximates
`Expr.const (Constant.int i₂)`, then `Expr.binop op a₁ a₂` approximates
`Expr.const (Constant.int (eval_binop_int op i₁ i₂))`.
This is the left-to-constant direction for binary operations.
-/
lemma Expr.Approx.binop_const_approx_left {op a₁ a₂ i₁ i₂}
    (ha₁L : a₁ ≲ Expr.const (Constant.int i₁)) (ha₂L : a₂ ≲ Expr.const (Constant.int i₂)) :
    Expr.binop op a₁ a₂ ≲ Expr.const (Constant.int (eval_binop_int op i₁ i₂)) := by
  intro env₁ env₂ henv v₁ heval
  cases heval
  case binop val₁ val₂ heval_a₁ heval_a₂ =>
    rcases ha₁L env₁ env₂ henv (Value.const (Constant.int val₁)) heval_a₁ with
      ⟨v₂₁, hconst_eval₁, happrox₁⟩
    cases hconst_eval₁
    case const =>
      have hval₁ : val₁ = i₁ := by
        have htemp : Constant.int val₁ = Constant.int i₁ := Value.Approx.const_inj happrox₁
        injection htemp
      rcases ha₂L env₁ env₂ henv (Value.const (Constant.int val₂)) heval_a₂ with
        ⟨v₂₂, hconst_eval₂, happrox₂⟩
      cases hconst_eval₂
      case const =>
        have hval₂ : val₂ = i₂ := by
          have htemp : Constant.int val₂ = Constant.int i₂ := Value.Approx.const_inj happrox₂
          injection htemp
        rw [hval₁, hval₂]
        exact ⟨Value.const (Constant.int (eval_binop_int op i₁ i₂)),
          Eval.const, by rw [Value.Approx.const_right]⟩

/--
If `Expr.const (Constant.int i₁)` approximates `a₁` and `Expr.const (Constant.int i₂)`
approximates `a₂`, then `Expr.const (Constant.int (eval_binop_int op i₁ i₂))`
approximates `Expr.binop op a₁ a₂`.
This is the constant-to-right direction for binary operations.
-/
lemma Expr.Approx.const_binop_approx_right {op a₁ a₂ i₁ i₂}
    (ha₁R : Expr.const (Constant.int i₁) ≲ a₁) (ha₂R : Expr.const (Constant.int i₂) ≲ a₂) :
    Expr.const (Constant.int (eval_binop_int op i₁ i₂)) ≲ Expr.binop op a₁ a₂ := by
  intro env₁ env₂ henv v₁ heval
  cases heval
  case const =>
    rcases ha₁R env₁ env₂ henv (Value.const (Constant.int i₁)) Eval.const with
      ⟨v₂₁, heval_a₁, happrox₁⟩
    rw [Value.Approx.const_right] at happrox₁
    subst happrox₁
    rcases ha₂R env₁ env₂ henv (Value.const (Constant.int i₂)) Eval.const with
      ⟨v₂₂, heval_a₂, happrox₂⟩
    rw [Value.Approx.const_right] at happrox₂
    subst happrox₂
    refine ⟨Value.const (Constant.int (eval_binop_int op i₁ i₂)),
      Eval.binop heval_a₁ heval_a₂, ?_⟩
    rw [Value.Approx.const_right]

/--
If `a₁ ≈ Expr.const (Constant.int i₁)` and `a₂ ≈ Expr.const (Constant.int i₂)`, then
`Expr.binop op a₁ a₂ ≈ Expr.const (Constant.int (eval_binop_int op i₁ i₂))`.

This combines the left and right approximation directions to obtain a full
equivalence result.
-/
lemma Expr.Equiv.eval_const {op a₁ a₂ i₁ i₂} :
    a₁ ≈ Expr.const (Constant.int i₁) →
    a₂ ≈ Expr.const (Constant.int i₂) →
    Expr.binop op a₁ a₂ ≈
      Expr.const (Constant.int (eval_binop_int op i₁ i₂)) := by
  intro ha₁ ha₂
  have ha₁L := Expr.Equiv.toApprox₁ ha₁
  have ha₂L := Expr.Equiv.toApprox₁ ha₂
  have ha₁R := Expr.Equiv.toApprox₂ ha₁
  have ha₂R := Expr.Equiv.toApprox₂ ha₂
  have h_left := Expr.Approx.binop_const_approx_left (op := op) ha₁L ha₂L
  have h_right := Expr.Approx.const_binop_approx_right (op := op) ha₁R ha₂R
  exact ⟨h_left, h_right⟩

end Juvix.Core.Main
