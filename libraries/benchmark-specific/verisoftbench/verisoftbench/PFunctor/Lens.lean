import ToMathlib.PFunctor.Lens.Basic
import verisoftbench.Common.Sum

open PFunctor

universe uA₁ uA₂ uB₁

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}

namespace PFunctor.Lens

/-- The sum of the left and right injections with `sumPair` yields the identity lens. -/
@[simp]
theorem sumPair_inl_inr :
    Lens.sumPair Lens.inl Lens.inr = Lens.id.{max uA₁ uA₂, uB₁} (P + Q) := by
  dsimp [Lens.sumPair, Lens.id, Lens.inl, Lens.inr]
  have hA : (Sum.elim Sum.inl Sum.inr : (P.A ⊕ Q.A) → (P.A ⊕ Q.A)) = id :=
    sum_elim_inl_inr_eq_id
  simp [hA]
  refine Function.hfunext rfl ?_
  intro a a' ha_heq
  have ha_eq : a = a' := eq_of_heq ha_heq
  subst ha_eq
  cases a
  · rfl
  · rfl

end PFunctor.Lens
