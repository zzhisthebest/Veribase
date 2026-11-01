import Clean.Gadgets.Xor.Xor32

/-!
Lemmas about `Inputs`, `U32`, and the circuit `eval` function from
`Clean.Gadgets.Xor.Xor32`.
-/

set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Xor32

omit p_large_enough in
/-- Given that `eval env e = v` for a `U32` variable, extract the four component equalities
    at the `Expression.eval` level. -/
lemma eval_u32_components_eq {env : Environment (F p)} {e : Var U32 (F p)} {v : U32 (F p)}
    (h : eval env e = v) :
    Expression.eval env e.x0 = v.x0 ∧
    Expression.eval env e.x1 = v.x1 ∧
    Expression.eval env e.x2 = v.x2 ∧
    Expression.eval env e.x3 = v.x3 := by
  have h0 := congrArg (fun (u : U32 (F p)) => u.x0) h
  have h1 := congrArg (fun (u : U32 (F p)) => u.x1) h
  have h2 := congrArg (fun (u : U32 (F p)) => u.x2) h
  have h3 := congrArg (fun (u : U32 (F p)) => u.x3) h
  simpa [circuit_norm, explicit_provable_type] using And.intro h0 (And.intro h1 (And.intro h2 h3))

omit p_large_enough in
/-- From an `Inputs` evaluation equality, extract the equality for its `.x` field. -/
lemma eval_inputs_x {env : Environment (F p)} {e : Var Inputs (F p)} {v : Inputs (F p)}
    (h : eval env e = v) : eval env e.x = v.x := by
  have h' := congrArg (fun (s : Inputs (F p)) => s.x) h
  simpa [eval, circuit_norm, explicit_provable_type] using h'

omit p_large_enough in
/-- From an `Inputs` evaluation equality, extract the equality for its `.y` field. -/
lemma eval_inputs_y {env : Environment (F p)} {e : Var Inputs (F p)} {v : Inputs (F p)}
    (h : eval env e = v) : eval env e.y = v.y := by
  have h' := congrArg (fun (s : Inputs (F p)) => s.y) h
  simpa [eval, circuit_norm, explicit_provable_type] using h'

end Gadgets.Xor32
