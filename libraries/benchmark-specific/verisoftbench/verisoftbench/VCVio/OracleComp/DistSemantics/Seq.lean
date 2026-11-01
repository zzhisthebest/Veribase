import VCVio.OracleComp.DistSemantics.Seq
import verisoftbench.Common.Topology.ENNReal
import verisoftbench.VCVio.OracleComp.Basic

set_option quotPrecheck false

namespace OracleComp

universe u v w
variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}
variable (oa : OracleComp spec α) (ob : OracleComp spec β) (f : α → β → γ)

/-- If `(x', y') ≠ (x, y)` and the hypothesis `h` uniquely identifies `(x, y)` as the pair
satisfying `z = f x' y'` in the support, then the conditional term at `(x', y')` is zero. -/
lemma ite_probOutput_mul_eq_zero_of_ne [spec.FiniteRange] [DecidableEq γ] {x' x : α} {y' y : β}
    {z : γ} (h : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, z = f x' y' ↔ x' = x ∧ y' = y)
    (hne : (x', y') ≠ (x, y)) :
    (if z = f x' y' then [= x' | oa] * [= y' | ob] else 0) = 0 := by
  simp only [ite_eq_right_iff]
  rw [probOutput_mul_eq_zero_iff oa ob, ← not_and_or]
  intro hz ⟨hx', hy'⟩
  have ⟨hx_eq, hy_eq⟩ := (h x' hx' y' hy').1 hz
  exact hne (Prod.ext hx_eq hy_eq)

/-- If `z = f x y` must hold when `x` and `y` are in their respective supports, then
the conditional term at `(x, y)` simplifies to the product of the probOutputs. -/
lemma ite_probOutput_mul_self [spec.FiniteRange] [DecidableEq γ] {x : α} {y : β} {z : γ}
    (h : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, z = f x' y' ↔ x' = x ∧ y' = y) :
    (if z = f x y then [= x | oa] * [= y | ob] else 0) = [= x | oa] * [= y | ob] := by
  simp only [ite_eq_left_iff, zero_eq_mul, probOutput_eq_zero_iff, ← not_and_or]
  intro hz ⟨hx, hy⟩
  exact hz ((h x hx y hy).2 ⟨rfl, rfl⟩)

/-- If there exists unique `x` and `y` such that `f x y = z` (given as explicit arguments),
then the probability of getting `z` as an output of `f <$> oa <*> ob`
is the product of probabilities of getting `x` and `y` from `oa` and `ob` respectively. -/
lemma probOutput_seq_map_eq_mul_of_unique_pair [spec.FiniteRange] (x : α) (y : β) (z : γ)
    (h : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, z = f x' y' ↔ x' = x ∧ y' = y) :
    [= z | f <$> oa <*> ob] = [= x | oa] * [= y | ob] := by
  classical
    rw [probOutput_seq_map_eq_tsum_ite oa ob f z]
    refine (tsum_prod_eq_single (λ x' y' =>
      if z = f x' y' then [= x' | oa] * [= y' | ob] else 0) x y ?_).trans ?_
    · exact λ x' y' hne ↦ ite_probOutput_mul_eq_zero_of_ne oa ob (f := f) h hne
    · exact ite_probOutput_mul_self oa ob (f := f) h

end OracleComp
