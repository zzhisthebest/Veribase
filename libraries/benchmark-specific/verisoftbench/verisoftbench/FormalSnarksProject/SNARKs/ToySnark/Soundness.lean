import FormalSnarksProject.SNARKs.ToySnark
import verisoftbench.Common.Algebra.Ring
import Mathlib.Algebra.MvPolynomial.Equiv

open scoped BigOperators Classical
open MvPolynomial Option List

set_option maxHeartbeats 0

namespace ToySnark

local notation "Vars_α" => some Vars.α
local notation "Vars_β" => some Vars.β
local notation "Vars_x" => none

/--
Soundness of the ToySnark proof system for the simple 2-witness, 3-statement-variable relation:
`(w_A * s_y = s_z) ∨ (w_B * s_x = s_z)`.

Here the extractor maps the prover's proof element to either witness A or B depending on which side
of the disjunction holds.
-/
lemma soundness_1
    {F : Type} [Field F] :
    (AGMProofSystemInstantiation.soundness
      F
      (ToySnark
        (F := F))
      (WitEntries -> F)
      (fun (stmt : StmtEntries → F) (wit : WitEntries -> F) =>
        wit WitEntries.A * stmt StmtEntries.y = stmt StmtEntries.z -- - wit WitEntries.I
        ∨
        wit WitEntries.B * stmt StmtEntries.x = stmt StmtEntries.z -- - wit WitEntries.I
      )
      (fun prover i => prover.fst Proof_G1_Idx.Pf (if i = WitEntries.A then .α else .β))

    ) := by
  intro stmt prover h_verify
  rcases h_verify with ⟨h_check, h_identified⟩
  have h_poly_zero : (ToySnark (F := F)).check_poly prover stmt () = 0 := h_check ()
  dsimp [ToySnark] at h_poly_zero
  simp [AGMProofSystemInstantiation.check_poly, AGMProofSystemInstantiation.pairing_poly,
    AGMProofSystemInstantiation.proof_element_G1_as_poly,
    AGMProofSystemInstantiation.proof_element_G2_as_poly] at h_poly_zero
  have h_ax_zero : (prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.α) * (stmt StmtEntries.x) = 0 := by
    have h_eval := congrArg (MvPolynomial.eval (λ | some Vars.α => (1 : F) | _ => (0 : F))) h_poly_zero
    simpa using h_eval
  have h_by_zero : (prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.β) * (stmt StmtEntries.y) = 0 := by
    have h_eval := congrArg (MvPolynomial.eval (λ | some Vars.β => (1 : F) | _ => (0 : F))) h_poly_zero
    simpa using h_eval
  have h_mul_sub : (prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.α
      + prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.β) *
      (stmt StmtEntries.x + stmt StmtEntries.y) - stmt StmtEntries.z = 0 := by
    have h_eval := congrArg
      (MvPolynomial.eval (λ | some Vars.α => (1 : F) | some Vars.β => (1 : F) | _ => (0 : F)))
      h_poly_zero
    simpa [sub_eq_add_neg] using h_eval
  have h_ay_bx_eq_z : (prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.α) * (stmt StmtEntries.y)
    + (prover.fst Proof_G1_Idx.Pf SRS_Elements_G1_Idx.β) * (stmt StmtEntries.x) = (stmt StmtEntries.z) :=
    expand_mul_add_sub_eq h_ax_zero h_by_zero h_mul_sub
  rcases disj_of_mul_zero_or_and_sum (eq_zero_or_eq_zero_of_mul_eq_zero h_ax_zero) h_ay_bx_eq_z with
    (h_right | h_left)
  · right; simpa using h_right
  · left; simpa using h_left

end ToySnark
