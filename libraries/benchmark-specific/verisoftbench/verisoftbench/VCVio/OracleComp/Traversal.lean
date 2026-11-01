import VCVio.OracleComp.Traversal
import verisoftbench.Common.Set

set_option quotPrecheck false
open OracleSpec

universe u v w
variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}
variable (Q : {α : Type v} → OracleQuery spec α → Prop)
    (F : Prop) (oa : OracleComp spec α)
    (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)

namespace OracleComp

@[simp] lemma allWhen_bind_iff_1 (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allWhen Q F possible_outputs ↔ oa.allWhen Q F possible_outputs ∧
      ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q F possible_outputs := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp
  | query_bind i t r hr =>
      have h_bind_assoc : ((query i t : OracleComp spec (spec.range i)) >>= r) >>= ob =
          (query i t : OracleComp spec (spec.range i)) >>= (λ u => r u >>= ob) := by
        simp [bind_assoc]
      rw [h_bind_assoc]
      simp only [allWhen_query_bind, supportWhen_query_bind]
      exact iff_forall_union (λ u _ => hr u)

end OracleComp
