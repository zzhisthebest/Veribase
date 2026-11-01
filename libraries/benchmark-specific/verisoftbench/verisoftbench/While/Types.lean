import Hoare.While.Types

/-!
# Type inversion lemmas for `While.Expr`

Theorems characterizing the behavior of `Expr.ty` on compound expressions:
if the computed type is `some ty`, the subexpressions must have specific types
and `ty` must be the expected result type.

Also provides the reverse direction of `WellTyped.ty`: if `e.ty = some ty`, then
`WellTyped e ty`.
-/

set_option quotPrecheck false
namespace While

/-- If `Expr.add e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.num`. -/
theorem Expr.add_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.add e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.num := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.sub e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.num`. -/
theorem Expr.sub_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.sub e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.num := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.mul e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.num`. -/
theorem Expr.mul_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.mul e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.num := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.lt e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.bool`. -/
theorem Expr.lt_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.lt e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.gt e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.bool`. -/
theorem Expr.gt_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.gt e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.le e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.bool`. -/
theorem Expr.le_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.le e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.ge e1 e2` has type `some ty`, both subexpressions are numeric and `ty` is `Ty.bool`. -/
theorem Expr.ge_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.ge e1 e2).ty = some ty → e1.ty = some Ty.num ∧ e2.ty = some Ty.num ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.num ∧ e2.ty = some Ty.num
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.and e1 e2` has type `some ty`, both subexpressions are boolean and `ty` is `Ty.bool`. -/
theorem Expr.and_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.and e1 e2).ty = some ty → e1.ty = some Ty.bool ∧ e2.ty = some Ty.bool ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.bool ∧ e2.ty = some Ty.bool
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.or e1 e2` has type `some ty`, both subexpressions are boolean and `ty` is `Ty.bool`. -/
theorem Expr.or_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.or e1 e2).ty = some ty → e1.ty = some Ty.bool ∧ e2.ty = some Ty.bool ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  by_cases hcond : e1.ty = some Ty.bool ∧ e2.ty = some Ty.bool
  · rcases hcond with ⟨h1, h2⟩
    simp [h1, h2] at h
    cases h
    exact ⟨h1, h2, rfl⟩
  · simp [hcond] at h

/-- If `Expr.eq e1 e2` has type `some ty`, both subexpressions have the same type,
that type is `isSome`, and `ty` is `Ty.bool`. -/
theorem Expr.eq_ty_some {e1 e2 : Expr} {ty : Ty} :
    (Expr.eq e1 e2).ty = some ty → e1.ty = e2.ty ∧ e1.ty.isSome ∧ ty = Ty.bool := by
  intro h
  simp [Expr.ty] at h
  rcases h with ⟨⟨heq, his⟩, hty⟩
  subst hty
  exact ⟨heq, his, rfl⟩

/-- If `e.ty = some ty`, then `WellTyped e ty`.
This is the reverse direction of `WellTyped.ty`. -/
theorem WellTyped.of_ty_some {e ty} : e.ty = some ty → WellTyped e ty := by
  intro h
  induction e generalizing ty with
  | num n =>
      simp [Expr.ty] at h
      cases h
      exact WellTyped.num
  | bool b =>
      simp [Expr.ty] at h
      cases h
      exact WellTyped.bool
  | var s =>
      simp [Expr.ty] at h
  | add e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.add_ty_some h
      subst hty
      exact WellTyped.add e1 e2 (ih1 h1) (ih2 h2)
  | sub e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.sub_ty_some h
      subst hty
      exact WellTyped.sub e1 e2 (ih1 h1) (ih2 h2)
  | mul e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.mul_ty_some h
      subst hty
      exact WellTyped.mul e1 e2 (ih1 h1) (ih2 h2)
  | eq e1 e2 ih1 ih2 =>
      have ⟨heq, his, hty⟩ := Expr.eq_ty_some h
      subst hty
      cases htemp : e1.ty
      case none =>
        rw [htemp] at his
        simp at his
      case some t =>
        have ht2 : e2.ty = some t := by rw [← heq, htemp]
        exact WellTyped.eq e1 e2 t (ih1 htemp) (ih2 ht2)
  | lt e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.lt_ty_some h
      subst hty
      exact WellTyped.lt e1 e2 (ih1 h1) (ih2 h2)
  | gt e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.gt_ty_some h
      subst hty
      exact WellTyped.gt e1 e2 (ih1 h1) (ih2 h2)
  | le e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.le_ty_some h
      subst hty
      exact WellTyped.le e1 e2 (ih1 h1) (ih2 h2)
  | ge e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.ge_ty_some h
      subst hty
      exact WellTyped.ge e1 e2 (ih1 h1) (ih2 h2)
  | and e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.and_ty_some h
      subst hty
      exact WellTyped.and e1 e2 (ih1 h1) (ih2 h2)
  | or e1 e2 ih1 ih2 =>
      have ⟨h1, h2, hty⟩ := Expr.or_ty_some h
      subst hty
      exact WellTyped.or e1 e2 (ih1 h1) (ih2 h2)

/-- If an expression is well-typed at two different types, those types must be equal.
This is the uniqueness of typing property. -/
theorem WellTyped.unique {e : Expr} {t1 t2 : Ty} (h1 : WellTyped e t1)
    (h2 : WellTyped e t2) : t1 = t2 := by
  cases h1 <;> cases h2 <;> rfl

/-- If `Expr.eq e1 e2` is well-typed at `t`, then `t` must be `Ty.bool`. -/
theorem WellTyped.eq_inv_type {e1 e2 : Expr} {t : Ty}
    (h : WellTyped (Expr.eq e1 e2) t) : t = Ty.bool := by
  cases h; rfl

/-- Inversion lemma: if `Expr.eq e1 e2` is well-typed at any type,
then both subexpressions are well-typed at some common type. -/
theorem WellTyped.eq_inv {e1 e2 : Expr} {t : Ty}
    (h : WellTyped (Expr.eq e1 e2) t) : ∃ s : Ty, WellTyped e1 s ∧ WellTyped e2 s := by
  cases h
  case eq s h1 h2 => exact ⟨s, h1, h2⟩

/-- If `Expr.eq e1 e2` is well-typed and `e1` is well-typed at `t`,
then `e2` is also well-typed at `t`. -/
theorem WellTyped.eq_imp_right {e1 e2 : Expr} {t t' : Ty}
    (heq : WellTyped (Expr.eq e1 e2) t') (h1 : WellTyped e1 t) : WellTyped e2 t := by
  rcases WellTyped.eq_inv heq with ⟨s, h1', h2'⟩
  have hts : t = s := WellTyped.unique h1 h1'
  rw [hts]
  exact h2'

/-- If `e1` is well-typed at `t` but `e2` is not, then `Expr.eq e1 e2` is not well-typed
at any type. -/
theorem WellTyped.not_welltyped_not_eq_ty {e1 e2 : Expr} {t : Ty} :
    WellTyped e1 t → ¬ WellTyped e2 t → ∀ t', ¬ (WellTyped (Expr.eq e1 e2) t') := by
  intro h1 hn2 t' heq
  have h2 : WellTyped e2 t := WellTyped.eq_imp_right heq h1
  exact hn2 h2

end While
