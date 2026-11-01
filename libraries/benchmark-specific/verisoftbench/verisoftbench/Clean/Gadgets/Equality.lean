import Clean.Gadgets.Equality
import Clean.Utils.Field

/-!
Lemmas about `HasAssignEq.assignEq` and the equality gadget from `Clean.Gadgets.Equality`.
-/

variable {p : ℕ} [Fact p.Prime]

namespace HasAssignEq

/-- The soundness constraint for `assignEq x` implies the output equals the evaluated expression. -/
theorem assign_eq_soundness_extract (x : Expression (F p)) (offset : ℕ)
    (env : Environment (F p))
    (h_hold : Circuit.ConstraintsHold.Soundness env ((assignEq x).operations offset)) :
    env ((assignEq x).output offset) = Expression.eval env x := by
  simpa only [circuit_norm, Gadgets.Equality.circuit] using h_hold

end HasAssignEq
