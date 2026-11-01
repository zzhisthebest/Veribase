import ExprEval.Expr
import ExprEval.Steps
import ExprEval.Lemmas
import verisoftbench.ExprEval.StepStar

/-!
# Completeness theorems for arithmetic and boolean expressions

Every expression can be reduced to its constant value using the step relation.
These are the mutual completeness theorems for `ArExpr` and `BoolExpr`.
-/

mutual
  /--
  Completeness for arithmetic expressions: every `ArExpr` steps to its
  evaluated constant via `ArStepStar`.
  -/
  theorem arith_completeness (V : Type) (val : V → Int) (e : ArExpr V) :
      ArStepStar V val e (ArExpr.Const (eval V val e)) := by
    match e with
    | .Const x => exact StepStar.refl _ _
    | .Var x => exact from_step V val (ArStep.getVarValue x)
    | .Add l r =>
      exact stepstar_binary_op V val ArExpr.Add
        (fun h => ArStep.addLeft _ _ _ h)
        (fun h => ArStep.addRight _ _ _ h)
        (arith_completeness V val l) (arith_completeness V val r)
        (from_step V val (ArStep.addConstConst _ _))
    | .Sub l r =>
      exact stepstar_binary_op V val ArExpr.Sub
        (fun h => ArStep.subLeft _ _ _ h)
        (fun h => ArStep.subRight _ _ _ h)
        (arith_completeness V val l) (arith_completeness V val r)
        (from_step V val (ArStep.subConstConst _ _))
    | .Mul l r =>
      exact stepstar_binary_op V val ArExpr.Mul
        (fun h => ArStep.mulLeft _ _ _ h)
        (fun h => ArStep.mulRight _ _ _ h)
        (arith_completeness V val l) (arith_completeness V val r)
        (from_step V val (ArStep.mulConstConst _ _))
    | .If c t e =>
      refine stepstar_concat V val
        (stepstar_map_cross V val (fun c => ArExpr.If c t e)
          (fun h => ArStep.ifStep _ _ _ _ h) (bool_completeness V val c)) ?_
      cases hc : eval_bool V val c with
      | false =>
        simpa [eval, hc] using
          StepStar.trans _ _ _ (ArStep.ifCondFalse t e) (arith_completeness V val e)
      | true =>
        simpa [eval, hc] using
          StepStar.trans _ _ _ (ArStep.ifCondTrue t e) (arith_completeness V val t)

  /--
  Completeness for boolean expressions: every `BoolExpr` steps to its
  evaluated constant via `BoolStepStar`.
  -/
  theorem bool_completeness (V : Type) (val : V → Int) (e : BoolExpr V) :
      BoolStepStar V val e (BoolExpr.Const (eval_bool V val e)) := by
    match e with
    | .Const b => exact StepStar.refl _ _
    | .Less l r =>
      refine stepstar_binary_op V val BoolExpr.Less
        (fun h => BoolStep.lessArStepLeft _ _ _ h)
        (fun h => BoolStep.lessArStepRight _ _ _ h)
        (arith_completeness V val l) (arith_completeness V val r) ?_
      by_cases h : eval V val l < eval V val r
      · simpa [eval_bool, h] using from_step V val (BoolStep.lessConstConstTrue _ _ h)
      · have hn : eval V val l ≥ eval V val r := Int.le_of_not_gt h
        simpa [eval_bool, h] using from_step V val (BoolStep.lessConstConstFalse _ _ hn)
    | .Eq l r =>
      refine stepstar_binary_op V val BoolExpr.Eq
        (fun h => BoolStep.eqArStepLeft _ _ _ h)
        (fun h => BoolStep.eqArStepRight _ _ _ h)
        (arith_completeness V val l) (arith_completeness V val r) ?_
      by_cases h : eval V val l = eval V val r
      · simpa [eval_bool, h] using from_step V val (BoolStep.eqConstConstTrue _ _ h)
      · simpa [eval_bool, beq_eq_false_iff_ne.mpr h] using from_step V val
          (BoolStep.eqConstConstFalse _ _ (by simpa using h))
    | .Not e =>
      exact stepstar_unary_op V val BoolExpr.Not
        (fun h => BoolStep.notStep _ _ h) (bool_completeness V val e)
        (from_step V val (BoolStep.notIsBoolNot _))
    | .And l r =>
      refine stepstar_concat V val
        (stepstar_map V val (fun l => BoolExpr.And l r)
          (fun h => BoolStep.andStepLeft _ _ _ h) (bool_completeness V val l)) ?_
      cases hl : eval_bool V val l with
      | false => simpa [eval_bool, hl] using from_step V val (BoolStep.andLeftShortCircuit r)
      | true => simpa [eval_bool, hl] using
          StepStar.trans _ _ _ (BoolStep.andLeftTrue r) (bool_completeness V val r)
    | .Or l r =>
      refine stepstar_concat V val
        (stepstar_map V val (fun l => BoolExpr.Or l r)
          (fun h => BoolStep.orStepLeft _ _ _ h) (bool_completeness V val l)) ?_
      cases hl : eval_bool V val l with
      | false => simpa [eval_bool, hl] using
          StepStar.trans _ _ _ (BoolStep.orLeftFalse r) (bool_completeness V val r)
      | true => simpa [eval_bool, hl] using from_step V val (BoolStep.orLeftShortCircuit r)
end
