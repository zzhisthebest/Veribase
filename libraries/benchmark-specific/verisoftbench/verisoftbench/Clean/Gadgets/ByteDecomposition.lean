import Clean.Gadgets.ByteDecomposition.ByteDecomposition

/-!
Lemmas about byte decomposition gadget from `Clean.Gadgets.ByteDecomposition`.
-/

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

open Circuit

namespace Gadgets.ByteDecomposition

/-- Soundness of the byte decomposition circuit: for any offset in Fin 8,
the elaborated circuit decomposes a field element into its low and high parts
according to `Spec`. -/
theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
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
  have bounded_split (A B : ℕ) (ha : 0 < A) (hb : 0 < B)
      (hab : A * B = 256) (hA : A ≤ 256) (hB : B ≤ 256)
      (x low high : F p) (hx : x.val < 256)
      (hl : ((A : F p) * low).val < 256) (hh : high.val < 256)
      (he : x = low + high * (B : F p)) :
      (low.val = x.val % B ∧ high.val = x.val / B) ∧ low.val < B ∧ high.val < A := by
    have hp : 65792 < p := by have := p_large_enough.elim; norm_num at this; omega
    have hs : (A : F p) * x = (A : F p) * low + high * 256 := by
      rw [he]
      have hc : (A : F p) * (B : F p) = 256 := by
        have h := congrArg (fun n : ℕ => (n : F p)) hab
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
      calc
        (A : F p) * (low + high * (B : F p)) =
            (A : F p) * low + high * ((A : F p) * (B : F p)) := by ring
        _ = _ := by rw [hc]
    have hs_cast : ((A * x.val : ℕ) : F p) =
        ((((A : F p) * low).val + high.val * 256 : ℕ) : F p) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, F, ZMod.natCast_zmod_val] using hs
    have hxprod : A * x.val < p := by nlinarith
    have hrprod : ((A : F p) * low).val + high.val * 256 < p := by omega
    have hnat : A * x.val = ((A : F p) * low).val + high.val * 256 := by
      have hz := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hs_cast
      simpa only [Nat.mod_eq_of_lt hxprod, Nat.mod_eq_of_lt hrprod] using hz
    have hprod : high.val * B ≤ x.val := by nlinarith
    have hlo : low = ((x.val - high.val * B : ℕ) : F p) := by
      have hc := congrArg (fun n : ℕ => (n : F p)) (Nat.sub_add_cancel hprod)
      simp only [Nat.cast_add, Nat.cast_mul, F, ZMod.natCast_zmod_val] at hc
      apply add_right_cancel (b := high * (B : F p))
      exact he.symm.trans hc.symm
    have hloval : low.val = x.val - high.val * B := by
      rw [hlo, ZMod.val_natCast_of_lt]
      omega
    have hlole : low.val ≤ x.val := by rw [hloval]; omega
    have hscaled : ((A : F p) * low).val = A * low.val := by
      have hc : (A : F p) * low = ((A * low.val : ℕ) : F p) := by
        simp only [Nat.cast_mul, F, ZMod.natCast_zmod_val]
      rw [hc, ZMod.val_natCast_of_lt]
      nlinarith
    have hlbound : low.val < B := by rw [hscaled] at hl; nlinarith
    have hhbound : high.val < A := by nlinarith
    have hdecomp : x.val = low.val + high.val * B := by omega
    refine ⟨⟨?_, ?_⟩, hlbound, hhbound⟩
    · rw [hdecomp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlbound]
    · rw [hdecomp, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hlbound, zero_add]
  simp only [Soundness, ↓eval_components, elaborated, circuit_norm, main, Assumptions, Spec]
  intro start env input_var input he hbounds hc
  subst input
  have heq := hc.2.2 (by trivial)
  change Expression.eval env input_var = env.get start + env.get (start + 1) * 2 ^ offset.val at heq
  have hl := hc.1
  have hh := hc.2.1
  change (2 ^ (8 - offset.val) * env.get start).val < 256 at hl
  change (env.get (start + 1)).val < 256 at hh
  apply bounded_split (2 ^ (8 - offset.val)) (2 ^ offset.val)
    (by positivity) (by positivity) ?_ ?_ ?_ _ _ _ hbounds
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hl) hh
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using heq)
  all_goals fin_cases offset <;> norm_num

end Gadgets.ByteDecomposition
