import Clean.Gadgets.And.And8

/-!
Lemmas about the AND8 gadget from `Clean.Gadgets.And.And8`.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And8

/-- Completeness of the AND8 elaborated circuit: for any input satisfying `Assumptions`
(that `x.val < 256` and `y.val < 256`), there exists a satisfying witness assignment
that makes the constraints hold. -/
theorem completeness : Completeness (F p) elaborated Assumptions := by
  have eval_components {α : Type → Type} [ProvableStruct α]
      (env : Environment (F p)) (x : Var α (F p)) :
      ProvableType.eval env x = ProvableStruct.eval env x := by
    have aux : ∀ (cs : List ProvableStruct.WithProvableType)
        (as : ProvableStruct.ProvableTypeList (Expression (F p)) cs),
        ProvableStruct.eval.go env cs as =
          ProvableStruct.componentsFromElements cs
            ((ProvableStruct.componentsToElements cs as).map (Expression.eval env)) := by
      intro cs
      induction cs with
      | nil => intro as; cases as; rfl
      | cons c cs ih =>
        intro as
        cases as with
        | cons a as =>
          simp only [ProvableStruct.componentsToElements, ProvableStruct.componentsFromElements,
            ProvableStruct.eval.go, ProvableType.eval, toVars]
          rw [Vector.map_append, Vector.cast_take_append_of_eq_length,
            Vector.cast_drop_append_of_eq_length]
          congr 1
          exact ih as
    symm
    simp only [ProvableStruct.eval, ProvableType.eval, fromElements, toVars, toElements, size]
    congr 1
    apply aux
  have and_xor_sum {x y : ℕ} (hx : x < 256) (hy : y < 256) :
      x + y = (x ^^^ y) + 2 * (x &&& y) := by
    have h : ∀ a b : Fin 256, a.val + b.val = (a.val ^^^ b.val) + 2 * (a.val &&& b.val) := by
      native_decide
    exact h ⟨x, hx⟩ ⟨y, hy⟩
  simp only [Completeness, ↓eval_components, circuit_norm, main, Assumptions]
  intro offset env input_var hw input he hbounds
  subst input
  rcases input_var with ⟨x, y⟩
  simp only [eval_components, circuit_norm, explicit_provable_type] at hbounds
  change _ ∧ _ ∧ _
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  rw [hw]
  have hsum := and_xor_sum hbounds.1 hbounds.2
  have hfield : env x + env y - 2 * (↑((env x).val &&& (env y).val) : F p) =
      ↑((env x).val ^^^ (env y).val) := by
    have h := congrArg (fun n : ℕ => (n : F p)) hsum
    push_cast at h
    simp only [F, ZMod.natCast_zmod_val] at h ⊢
    exact sub_eq_iff_eq_add.mpr h
  simpa only [sub_eq_add_neg] using congrArg ZMod.val hfield |>.trans (by
    apply ZMod.val_natCast_of_lt
    exact lt_trans (Nat.xor_lt_two_pow (n := 8) hbounds.1 hbounds.2)
      (by have := p_large_enough.elim; omega))

end Gadgets.And.And8
