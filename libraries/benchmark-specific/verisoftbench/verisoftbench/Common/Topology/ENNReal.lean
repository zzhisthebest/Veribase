import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Finset.Basic

open BigOperators ENNReal

/-!
# ENNReal tsum lemmas

Lemmas about infinite sums (`∑'`) of `ENNReal` expressions involving indicator functions
(`ite` as Kronecker delta / characteristic function on `Finset`).
-/

/-- For a tsum of the form `∑' y, f y * ite (y = x) 1 0`, only the term at `y = x`
contributes. This generalizes `tsum_eq_single` for indicator-weighted sums. -/
lemma tsum_indicator_eq [DecidableEq α] (f : α → ENNReal) (x : α) :
    (∑' y, f y * ite (y = x) 1 0) = f x := by
  refine (tsum_eq_single x (λ y hy => ?_)).trans ?_
  · simp [hy]
  · simp

/-- Specialization of `tsum_indicator_eq` where `f y = a * ite (y ∈ s) 1 0`.
Useful for computing expectations over uniform distributions on finsets. -/
lemma tsum_uniform_indicator_eq [DecidableEq α] (s : Finset α) (a : ENNReal) (x : α) :
    (∑' y, (a * ite (y ∈ s) 1 0) * ite (y = x) 1 0) = a * ite (x ∈ s) 1 0 :=
  tsum_indicator_eq (λ y => a * ite (y ∈ s) 1 0) x

/-- When the `simp` normal form produces nested `ite` instead of the multiplicative form,
this lemma directly handles the tsum of a "Kronecker delta" style indicator.
Useful in conjunction with `PMF.bind_apply` expansions. -/
lemma tsum_ite_ite_eq [DecidableEq α] (s : Finset α) (a : ENNReal) (x : α) :
    (∑' y, ite (x = y) (ite (y ∈ s) a 0) 0) = ite (x ∈ s) a 0 := by
  refine (tsum_eq_single x (λ y hy => ?_)).trans ?_
  · simp only [ite_eq_right_iff]
    intro h
    exfalso
    exact hy h.symm
  · simp

/-!
## ENNReal algebraic identities
-/

/-- Algebraic identity for ENNReal values in [0, 1]:
`1 - (1 - r) * (1 - p) = p + r - p * r`.
Useful for simplifying failure probability expressions involving sequential/bind operations. -/
lemma one_sub_mul_sub_eq_add_sub_mul (p r : ENNReal) (hp_ne_top : p ≠ ∞) (hr_ne_top : r ≠ ∞)
    (hp_le_one : p ≤ 1) (hr_le_one : r ≤ 1) : 1 - (1 - r) * (1 - p) = p + r - p * r := by
  have hprod_le_one : (1 - r) * (1 - p) ≤ 1 :=
    calc
      (1 - r) * (1 - p) ≤ 1 * 1 := mul_le_mul' tsub_le_self tsub_le_self
      _ = 1 := by simp
  have hmul_le_sum : p * r ≤ p + r := by
    have h1 : p * r ≤ p := by
      calc
        p * r ≤ p * 1 := mul_le_mul' (le_refl p) hr_le_one
        _ = p := mul_one _
    have h2 : p ≤ p + r := by
      calc
        p = p + 0 := by simp
        _ ≤ p + r := add_le_add_left (zero_le r) p
    exact le_trans h1 h2
  have h_one_ne_top : (1 : ENNReal) ≠ ∞ := by simp
  have hsubr : (1 - r) ≠ ∞ := ENNReal.sub_ne_top h_one_ne_top
  have hsubp : (1 - p) ≠ ∞ := ENNReal.sub_ne_top h_one_ne_top
  have hprod_ne_top : (1 - r) * (1 - p) ≠ ∞ := ENNReal.mul_ne_top hsubr hsubp
  have hsum_ne_top : p + r ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hp_ne_top, hr_ne_top⟩
  have hmul_ne_top : p * r ≠ ∞ := ENNReal.mul_ne_top hp_ne_top hr_ne_top
  have hL_ne_top : (1 - (1 - r) * (1 - p)) ≠ ∞ := ENNReal.sub_ne_top h_one_ne_top
  have hR_ne_top : (p + r - p * r) ≠ ∞ := ENNReal.sub_ne_top hsum_ne_top
  apply (ENNReal.toReal_eq_toReal hL_ne_top hR_ne_top).mp
  simp [ENNReal.toReal_sub_of_le hprod_le_one h_one_ne_top,
    ENNReal.toReal_sub_of_le hmul_le_sum hsum_ne_top,
    ENNReal.toReal_sub_of_le hr_le_one h_one_ne_top,
    ENNReal.toReal_sub_of_le hp_le_one h_one_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_add hp_ne_top hr_ne_top]
  ring

/-!
## Tsum over product types
-/

/-- A product tsum over two variables equals the value at a single pair if it is zero elsewhere. -/
lemma tsum_prod_eq_single {α β : Type _} (f : α → β → ENNReal) (x : α) (y : β)
    (hzero : ∀ (x' : α) (y' : β), (x', y') ≠ (x, y) → f x' y' = 0) :
    ∑' (x' : α) (y' : β), f x' y' = f x y := by
  rw [← ENNReal.tsum_prod]
  exact tsum_eq_single (x, y) (λ ⟨x', y'⟩ h ↦ hzero x' y' h)
