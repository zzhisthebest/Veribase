import Mathlib.Order.WellFounded
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Well-foundedness helper theorems

Convenience lemmas combining `InvImage`, `Subrelation`, and `Nat.lt`
for well-foundedness proofs.

These allow establishing well-foundedness of a relation `R` by mapping
elements to `ℕ` and showing that `R` decreases the image under the mapping.
-/

universe u

/--
`InvImage Nat.lt f` is well-founded for any function `f : β → ℕ`.

This is the `Nat`-specialized version of `InvImage.wf`.
-/
theorem Nat_invImage_wf {β : Sort u} (f : β → ℕ) : WellFounded (InvImage Nat.lt f) :=
  InvImage.wf f Nat.lt_wfRel.wf

/--
If `R` is a subrelation of `InvImage Nat.lt f`, then `R` is well-founded.

This is a common pattern: to prove `WellFounded R`, find a measure `f`
such that `R` decreases `f` (i.e., `R x y → f x < f y`), then use
`lt_to_subrelation_invImage_nat_lt` to get the `Subrelation` hypothesis.
-/
theorem subrelation_invImage_nat_lt_wf {α : Sort u} (f : α → ℕ) {R : α → α → Prop}
    (h : Subrelation R (InvImage Nat.lt f)) : WellFounded R :=
  Subrelation.wf h (Nat_invImage_wf f)

/--
If `R x y` implies `f x < f y`, then `R` is a subrelation of `InvImage Nat.lt f`.

Together with `subrelation_invImage_nat_lt_wf`, this gives a simple recipe
for proving well-foundedness: provide a measure `f` and a proof that
`R x y → f x < f y`.
-/
theorem lt_to_subrelation_invImage_nat_lt {α : Sort u} {R : α → α → Prop} (f : α → ℕ)
    (h : ∀ x y, R x y → f x < f y) : Subrelation R (InvImage Nat.lt f) := by
  intro x y hR
  unfold InvImage
  simpa using h x y hR
