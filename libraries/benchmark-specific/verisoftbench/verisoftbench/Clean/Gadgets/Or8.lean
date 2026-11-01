import Clean.Gadgets.Or.Or8

/-!
Lemmas about the OR8 gadget from `Clean.Gadgets.Or.Or8`.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Or.Or8

/-- For bytes (x, y < 256), the identity: `2 * (x ||| y) = x + y + (x ^^^ y)`. -/
lemma or_times_two_sub_xor {x y : ℕ} (hx : x < 256) (hy : y < 256) :
    2 * (x ||| y) = x + y + (x ^^^ y) := by
  have h_all : ∀ (a : Fin 256) (b : Fin 256),
      2 * ((a.val : ℕ) ||| (b.val : ℕ)) = (a.val : ℕ) + (b.val : ℕ) + ((a.val : ℕ) ^^^ (b.val : ℕ)) := by
    native_decide
  exact h_all ⟨x, hx⟩ ⟨y, hy⟩

/-- Completeness of the OR8 elaborated circuit: for any input satisfying `Assumptions`
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
  simp only [Completeness, ↓eval_components, circuit_norm, main, Assumptions]
  intro offset env input_var hw input he hbounds
  subst input
  rcases input_var with ⟨x, y⟩
  simp only [circuit_norm, explicit_provable_type] at hbounds
  change _ ∧ _ ∧ _
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  rw [hw]
  have hsum := or_times_two_sub_xor hbounds.1 hbounds.2
  have hfield : 2 * (↑((env x).val ||| (env y).val) : F p) - env x - env y =
      ↑((env x).val ^^^ (env y).val) := by
    have h := congrArg (fun n : ℕ => (n : F p)) hsum
    push_cast at h
    simp only [F, ZMod.natCast_zmod_val] at h
    rw [h]
    ring
  simpa only [sub_eq_add_neg] using congrArg ZMod.val hfield |>.trans (by
    apply ZMod.val_natCast_of_lt
    exact lt_trans (Nat.xor_lt_two_pow (n := 8) hbounds.1 hbounds.2)
      (by have := p_large_enough.elim; omega))

/-- Soundness of the OR8 elaborated circuit: any witness satisfying the constraints
and `Assumptions` also satisfies the `Spec`. -/
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
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
  simp only [Soundness, ↓eval_components, circuit_norm, main, Assumptions, Spec]
  intro offset env input_var input he hbounds hx
  subst input
  rcases input_var with ⟨x, y⟩
  simp only [circuit_norm, explicit_provable_type] at hbounds
  change _ ∧ _ ∧ _ at hx
  have hx' : (2 * env.get offset - env x - env y).val =
      (env x).val ^^^ (env y).val := by
    simpa only [sub_eq_add_neg] using hx.2.2
  change (env.get offset).val = (env x).val ||| (env y).val ∧ (env.get offset).val < 256
  have hsum := or_times_two_sub_xor hbounds.1 hbounds.2
  have hfield : 2 * (↑((env x).val ||| (env y).val) : F p) =
      env x + env y + ↑((env x).val ^^^ (env y).val) := by
    have h := congrArg (fun n : ℕ => (n : F p)) hsum
    simpa only [F, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val] using h
  have hxfield := congrArg (fun n : ℕ => (n : F p)) hx'
  simp only [F, ZMod.natCast_zmod_val] at hxfield
  have heq : env.get offset = (↑((env x).val ||| (env y).val) : F p) := by
    apply mul_left_cancel₀ (two_non_zero (p := p))
    rw [hfield, ← hxfield]
    ring
  have hor : (env x).val ||| (env y).val < 256 := Nat.or_lt_two_pow (n := 8) hbounds.1 hbounds.2
  rw [heq, ZMod.val_natCast_of_lt (lt_trans hor (by have := p_large_enough.elim; omega))]
  exact ⟨rfl, hor⟩

end Gadgets.Or.Or8
