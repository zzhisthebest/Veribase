import PCF.Flat

/-!
# PCF Flat — Flat domain supremum lemmas

Theorems about `flat_sup`, the supremum operation on `Chain (Flat α)`.
-/

open Classical

/-- If some activation in the chain yields a `.some`, then `flat_sup` is that chosen value. -/
theorem flat_sup_dif_pos {c : Chain (Flat α)}
    (h : ∃ a n, c.act n = .some a) : flat_sup c = .some h.choose := by
  dsimp [flat_sup]
  rw [dif_pos h]

/-- If no activation yields a `.some`, then `flat_sup` is `.none`. -/
theorem flat_sup_dif_neg {c : Chain (Flat α)}
    (h : ¬ ∃ a n, c.act n = .some a) : flat_sup c = .none := by
  dsimp [flat_sup]
  rw [dif_neg h]

/-- In a chain of `Flat α`, if an activation yields `.some a`, then `a` equals
the chosen representative of any existential witness of a `.some` activation. -/
theorem flat_chain_some_choose {c : Chain (Flat α)} {a : α}
    (h : ∃ k, c.act k = .some a) (p : ∃ a' n, c.act n = .some a') : a = p.choose :=
  Flat.chain_some h p.choose_spec

/-- `flat_sup c = .some a` iff the chain contains the activation `.some a`. -/
theorem Flat.sup_eq_some_iff {c : Chain _} {a : α} :
    (∃ k, c.act k = .some a) ↔ (flat_sup c = .some a) := by
  constructor
  · intro h
    have p : ∃ a' n, c.act n = .some a' := ⟨a, h⟩
    have hsurp : flat_sup c = .some p.choose := flat_sup_dif_pos p
    have h_eq : a = p.choose := flat_chain_some_choose h p
    rw [hsurp, h_eq]
  · intro h
    by_cases p : ∃ a' n, c.act n = .some a'
    · have hsurp : flat_sup c = .some p.choose := flat_sup_dif_pos p
      rw [hsurp] at h
      injection h with h_eq
      subst h_eq
      exact p.choose_spec
    · have hsurp : flat_sup c = .none := flat_sup_dif_neg p
      rw [hsurp] at h
      injection h

/-!
## Basic ordering properties on `Flat α`
-/

/-- `Flat.some a` is never equal to `Flat.none`. -/
theorem Flat.some_ne_none {a : α} : Flat.some a ≠ Flat.none := by
  simp

/-- If a `Flat` value is under both `.some a` and `.some b`, then either it is `.none`
or `a = b`. This captures the key disjointness property of the flat domain ordering:
below any `.some`, the only distinct elements are `.none` and `.some` of the same value. -/
theorem Flat.under_some_disjoint {x : Flat α} (h1 : x ⊑ .some a) (h2 : x ⊑ .some b) :
    x = .none ∨ a = b := by
  cases x with
  | none => exact Or.inl rfl
  | some k =>
    have ha : Flat.some k = Flat.some a := Flat.some_leq h1
    have hb : Flat.some k = Flat.some b := Flat.some_leq h2
    have hab : a = b := by
      injection (ha.symm.trans hb)
    exact Or.inr hab

/-- If a `Flat` value is under two distinct `.some` values, it must be `.none`. -/
theorem Flat.under_some_disjoint_of_ne {x : Flat α} (h1 : x ⊑ .some a) (h2 : x ⊑ .some b)
    (hne : a ≠ b) : x = .none := by
  have h := Flat.under_some_disjoint h1 h2
  cases h with
  | inl hnone => exact hnone
  | inr heq => exact (hne heq).elim

/-- `.none` is the least element: it is below every `Flat α` value. -/
theorem Flat.none_leq (b : Flat α) : (.none : Flat α) ⊑ b := by
  intro hne
  exact (hne rfl).elim

/-- If `a` is not `.none`, then it is not below `.none`. -/
theorem Flat.not_leq_none_of_ne_none {a : Flat α} (hne : a ≠ .none) : ¬ (a ⊑ .none) := by
  intro h
  exact hne (h hne)

/-- The only element below `.none` is `.none` itself. -/
theorem Flat.leq_none_1 {a : Flat α} (h : a ⊑ .none) : a = .none := by
  by_cases hne : a = .none
  · exact hne
  · exact absurd h (Flat.not_leq_none_of_ne_none hne)
