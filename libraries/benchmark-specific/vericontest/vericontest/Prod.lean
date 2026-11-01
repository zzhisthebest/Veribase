import Mathlib

/-! # Prod

Lexicographic relations and other utilities for product types (`α × β`).
-/

/-- Lexicographic order on pairs: `p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)`.
This is the standard lexicographic ordering comparing first by the first component
using `<`, then by the second component using `≤`. -/
def pair_lex {α : Type} [LT α] [LE α] (p q : α × α) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- `pair_lex` is transitive when `α` is a `LinearOrder`. -/
instance pair_lex_isTrans [LinearOrder α] : IsTrans (α × α) (pair_lex (α := α)) := by
  constructor
  intro a b c hab hbc
  rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
  · exact Or.inl (lt_trans hab hbc)
  · exact Or.inl (lt_of_lt_of_le hab (le_of_eq hbc))
  · exact Or.inl (lt_of_le_of_lt (le_of_eq hab) hbc)
  · exact Or.inr ⟨hab.trans hbc, hab'.trans hbc'⟩

/-- `pair_lex` is antisymmetric when `α` is a `LinearOrder`. -/
instance pair_lex_isAntisymm [LinearOrder α] : IsAntisymm (α × α) (pair_lex (α := α)) := by
  constructor
  intro a b hab hba
  rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hba with hba | ⟨hba, hba'⟩
  · exact False.elim (lt_asymm hab hba)
  · have : a.1 < a.1 := by simpa [hba] using hab
    exact False.elim (lt_irrefl _ this)
  · have : b.1 < b.1 := by simpa [hab] using hba
    exact False.elim (lt_irrefl _ this)
  · exact Prod.ext hab (le_antisymm hab' hba')

/-- `pair_lex` is total when `α` is a `LinearOrder`. -/
instance pair_lex_isTotal [LinearOrder α] : IsTotal (α × α) (pair_lex (α := α)) := by
  constructor
  intro a b
  by_cases h : a.1 < b.1
  · exact Or.inl (Or.inl h)
  · by_cases h' : a.1 = b.1
    · by_cases h'' : a.2 ≤ b.2
      · exact Or.inl (Or.inr ⟨h', h''⟩)
      · exact Or.inr (Or.inr ⟨h'.symm, le_of_not_ge h''⟩)
    · exact Or.inr (Or.inl (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h')))

/-- `pair_lex` is decidable when `α` has decidable `<` and `≤`. -/
instance pair_lex_decidableRel [LinearOrder α] : DecidableRel (pair_lex (α := α)) := by
  intro a b
  unfold pair_lex
  infer_instance
