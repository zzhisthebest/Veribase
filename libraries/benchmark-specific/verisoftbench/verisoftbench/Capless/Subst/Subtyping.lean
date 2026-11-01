import Capless.Subst.Basic
import Capless.Subst.Type.Subtyping
import Capless.Subst.Term.Subtyping
import Capless.Subtyping
import Capless.Subcapturing
import verisoftbench.Capless.Renaming.Basic
import verisoftbench.Capless.Renaming.Subtyping
import verisoftbench.Capless.Basic

/-!
# Type Variable Substitution Preserves Subtyping

This module proves that subtyping, subcapturing, and subbounding relations
are preserved under type variable substitution. If two types are in a subtyping
relation in context `Γ`, then after renaming type variables via a valid
`TVarSubst`, they remain in the same subtyping relation in the target context `Δ`.
-/

namespace Capless

/-! ## `Subcapt` is preserved under type variable substitution -/

/--
Subcapturing is preserved under type variable substitution.
If `Γ ⊢ C1 <:c C2` and `σ : TVarSubst Γ f Δ`, then `Δ ⊢ C1 <:c C2`.
Note: capture sets are unchanged since type-variable renaming does not affect them.
-/
theorem Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  Subcapt Δ C1 C2 := by
  induction h with
  | trans h1 h2 ih1 ih2 => exact Subcapt.trans (ih1 σ) (ih2 σ)
  | subset h => exact Subcapt.subset h
  | union h1 h2 ih1 ih2 => exact Subcapt.union (ih1 σ) (ih2 σ)
  | var hb => exact Subcapt.var (σ.map _ _ hb)
  | cinstl hb => exact Subcapt.cinstl (σ.cmap _ _ hb)
  | cinstr hb => exact Subcapt.cinstr (σ.cmap _ _ hb)
  | cbound hb => exact Subcapt.cbound (σ.cmap _ _ hb)

/-! ## `Subbound` is preserved under type variable substitution -/

/--
Subbounding is preserved under type variable substitution.
If `Γ ⊢ B1 <:b B2` and `σ : TVarSubst Γ f Δ`, then `Δ ⊢ B1 <:b B2`.
-/
theorem Subbound.tsubst
  (h : Subbound Γ B1 B2)
  (σ : TVarSubst Γ f Δ) :
  Subbound Δ B1 B2 := by
  cases h with
  | set hc => exact Subbound.set (Subcapt.tsubst hc σ)
  | star => exact Subbound.star

/-! ## `SSubtyp` is preserved under type variable substitution -/

/--
`SSubtyp` is preserved under type variable substitution.
If `Γ ⊢ S1 <:s S2` and `σ : TVarSubst Γ f Δ`, then `Δ ⊢ S1.trename f <:s S2.trename f`.
-/
theorem SSubtyp.tsubst
  (h : SSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := by
  refine (h.rec
    (motive_1 := fun Γ' E1 E2 _ => SSubtyp.tsubst_motive1 Γ' E1 E2)
    (motive_2 := fun Γ' C1 C2 _ => SSubtyp.tsubst_motive2 Γ' C1 C2)
    (motive_3 := fun Γ' S1' S2' _ => SSubtyp.tsubst_motive3 Γ' S1' S2')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) f Δ σ
  · -- exist
    intro n m k Γ' T1 T2 hc ih
    unfold SSubtyp.tsubst_motive1
    intro m' g Δ' ρ'
    simp [EType.trename]
    apply ESubtyp.exist
    apply ih g (Δ'.cvar (CBinding.bound CBound.star))
      (TVarSubst.cext (b := CBinding.bound CBound.star) ρ')
  · -- type
    intro n m k Γ' T1 T2 hc ih
    unfold SSubtyp.tsubst_motive1
    intro m' g Δ' ρ'
    simp [EType.trename]
    apply ESubtyp.type
    apply ih g Δ' ρ'
  · -- capt
    intro n m k Γ' C1 C2 S1' S2' hc hs ih_s
    unfold SSubtyp.tsubst_motive2
    intro m' g Δ' ρ'
    simp [CType.trename]
    apply CSubtyp.capt (Subcapt.tsubst hc ρ') (ih_s g Δ' ρ')
  · -- top
    intro n m k Γ' S'
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.top
  · -- refl
    intro n m k Γ' S'
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    apply SSubtyp.refl
  · -- trans
    intro n m k Γ' Sx Sy Sz hs1 hs2 ih1 ih2
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    exact SSubtyp.trans (ih1 g Δ' ρ') (ih2 g Δ' ρ')
  · -- tvar
    intro n m k Γ' X S' hb
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply ρ'.tmap _ _ hb
  · -- tinstl
    intro n m k Γ' X S' hb
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tinstl (ρ'.tmap_inst _ _ hb)
  · -- tinstr
    intro n m k Γ' X S' hb
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tinstr (ρ'.tmap_inst _ _ hb)
  · -- boxed
    intro n m k Γ' T1 T2 hc ih
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.boxed (ih g Δ' ρ')
  · -- label
    intro n m k Γ' Sa Sb hs ih
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.label (ih g Δ' ρ')
  · -- xforall
    intro n m k Γ' Ea Eb F1 F2 hc he ih_c ih_e
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.xforall (ih_c g Δ' ρ')
      (ih_e g (Δ'.var (Ea.trename g)) (TVarSubst.ext ρ' Ea))
  · -- tforall
    intro n m k Γ' Sc Sd E1 E2 hs he ih_s ih_e
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.tforall (ih_s g Δ' ρ')
      (ih_e g.ext (Δ'.tvar (TBinding.bound (Sc.trename g)))
        (TVarSubst.text ρ' (TBinding.bound Sc)))
  · -- cforall
    intro n m k Γ' Ba Bb E1 E2 hb he ih_e
    unfold SSubtyp.tsubst_motive3
    intro m' g Δ' ρ'
    simp [SType.trename]
    apply SSubtyp.cforall (Subbound.tsubst hb ρ')
      (ih_e g (Δ'.cvar (CBinding.bound Ba))
        (TVarSubst.cext (b := CBinding.bound Ba) ρ'))

/-! ## `CSubtyp` is preserved under type variable substitution -/

/--
`CSubtyp` is preserved under type variable substitution.
If `Γ ⊢ C1 <: C2` and `σ : TVarSubst Γ f Δ`, then `Δ ⊢ C1.trename f <: C2.trename f`.
-/
theorem CSubtyp.tsubst
  (h : CSubtyp Γ C1 C2)
  (σ : TVarSubst Γ f Δ) :
  CSubtyp Δ (C1.trename f) (C2.trename f) := by
  cases h
  case capt hc hs =>
    simp [CType.trename]
    exact CSubtyp.capt (Subcapt.tsubst hc σ) (SSubtyp.tsubst hs σ)

/-! ## `ESubtyp` is preserved under type variable substitution -/

/--
`ESubtyp` is preserved under type variable substitution.
If `Γ ⊢ E1 <:e E2` and `σ : TVarSubst Γ f Δ`, then `Δ ⊢ E1.trename f <:e E2.trename f`.
-/
theorem ESubtyp.tsubst
  (h : ESubtyp Γ E1 E2)
  (σ : TVarSubst Γ f Δ) :
  ESubtyp Δ (E1.trename f) (E2.trename f) := by
  cases h
  case exist hc =>
    simp [EType.trename]
    apply ESubtyp.exist
    apply CSubtyp.tsubst hc (TVarSubst.cext (b := CBinding.bound CBound.star) σ)
  case type hc =>
    simp [EType.trename]
    apply ESubtyp.type
    apply CSubtyp.tsubst hc σ

/-! ## `Subcapt` is preserved under term variable substitution -/

/--
Subcapturing is preserved under term variable substitution.
If `Γ ⊢ C1 <:c C2` and `σ : VarSubst Γ f Δ`, then `Δ ⊢ C1.rename f <:c C2.rename f`.
-/
theorem Subcapt.subst
    (h : Subcapt Γ C1 C2)
    (σ : VarSubst Γ f Δ) :
    Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans h1 h2 ih1 ih2 =>
    exact Subcapt.trans (ih1 σ) (ih2 σ)
  case subset hsub =>
    apply Subcapt.subset
    apply CaptureSet.Subset.rename hsub f
  case union h1 h2 ih1 ih2 =>
    simp
    apply Subcapt.union (ih1 σ) (ih2 σ)
  case var =>
    rename_i x C S hb
    have htyp := σ.map x (CType.capt C S) hb
    simpa using Typing.inv_subcapt htyp
  case cinstl =>
    rename_i c C hb
    simpa using Subcapt.cinstl (σ.cmap c (CBinding.inst C) hb)
  case cinstr =>
    rename_i c C hb
    simpa using Subcapt.cinstr (σ.cmap c (CBinding.inst C) hb)
  case cbound =>
    rename_i c C hb
    simpa using Subcapt.cbound (σ.cmap c (CBinding.bound (CBound.upper C)) hb)

/-! ## `Subbound` is preserved under term variable substitution -/

/--
Subbounding is preserved under term variable substitution.
If `Γ ⊢ B1 <:b B2` and `σ : VarSubst Γ f Δ`, then `Δ ⊢ B1.rename f <:b B2.rename f`.
-/
theorem Subbound.subst
    (h : Subbound Γ B1 B2)
    (σ : VarSubst Γ f Δ) :
    Subbound Δ (B1.rename f) (B2.rename f) := by
  cases h
  case set h_subcapt =>
    simp [CBound.rename]
    apply Subbound.set
    apply Subcapt.subst h_subcapt σ
  case star =>
    simp [CBound.rename]
    apply Subbound.star

/-! ## `SSubtyp` is preserved under term variable substitution -/

/--
`SSubtyp` is preserved under term variable substitution.
If `Γ ⊢ S1 <:s S2` and `σ : VarSubst Γ f Δ`, then `Δ ⊢ S1.rename f <:s S2.rename f`.

This is the main substitution theorem for shape types.
The proof uses mutual induction on the subtyping relation, simultaneously
proving preservation for `ESubtyp` and `CSubtyp`.
-/
theorem SSubtyp.subst
  (h : SSubtyp Γ S1 S2)
  (σ : VarSubst Γ f Δ) :
  SSubtyp Δ (S1.rename f) (S2.rename f) := by
  refine SSubtyp.rec
    (motive_1 := λ Γ E1 E2 _ => SSubtyp.subst_motive1 Γ E1 E2)
    (motive_2 := λ Γ C1 C2 _ => SSubtyp.subst_motive2 Γ C1 C2)
    (motive_3 := λ Γ S1 S2 _ => SSubtyp.subst_motive3 Γ S1 S2)
    (by
      intro n m k Γ T1 T2 hc ih n' g Δ' ρ'
      simp [EType.rename]
      constructor
      apply ih g (Δ'.cvar (CBinding.bound CBound.star)) (VarSubst.cext ρ'))
    (by
      intro n m k Γ T1 T2 hc ih n' g Δ' ρ'
      simp [EType.rename]
      constructor
      apply ih g Δ' ρ')
    (by
      intro n m k Γ C1 C2 S1 S2 hc hs ih n' g Δ' ρ'
      simp [CType.rename]
      constructor
      · exact Subcapt.subst hc ρ'
      · exact ih g Δ' ρ')
    (by
      intro n m k Γ S n' g _ _
      simp [SType.rename]
      exact SSubtyp.top)
    (by
      intro n m k Γ S _ _ _ _
      exact SSubtyp.refl)
    (by
      intro n m k Γ S1m S2m S3m h1 h2 ih1 ih2 n' g Δ' ρ'
      apply SSubtyp.trans
      · exact ih1 g Δ' ρ'
      · exact ih2 g Δ' ρ')
    (by
      intro n m k Γ X S hb n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.tvar
      have h' := ρ'.tmap X (TBinding.bound S) hb
      simp [TBinding.rename] at h'
      exact h')
    (by
      intro n m k Γ X S hb n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.tinstl
      have h' := ρ'.tmap X (TBinding.inst S) hb
      simp [TBinding.rename] at h'
      exact h')
    (by
      intro n m k Γ X S hb n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.tinstr
      have h' := ρ'.tmap X (TBinding.inst S) hb
      simp [TBinding.rename] at h'
      exact h')
    (by
      intro n m k Γ T1 T2 hc ih n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.boxed
      exact ih g Δ' ρ')
    (by
      intro n m k Γ S1m S2m hs ih n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.label
      exact ih g Δ' ρ')
    (by
      intro n m k Γ E2 E1 F1 F2 hc hes ihc ihes n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.xforall
      · exact ihc g Δ' ρ'
      · exact ihes g.ext (Δ'.var (E2.rename g)) (VarSubst.ext ρ' E2))
    (by
      intro n m k Γ S2 S1 E1 E2 hs hes ihs ihes n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.tforall
      · exact ihs g Δ' ρ'
      · exact ihes g (Δ'.tvar ((TBinding.bound S2).rename g)) (VarSubst.text ρ'))
    (by
      intro n m k Γ B2 B1 E1 E2 hb hes ihes n' g Δ' ρ'
      simp [SType.rename]
      apply SSubtyp.cforall
      · exact Subbound.subst hb ρ'
      · exact ihes g (Δ'.cvar ((CBinding.bound B2).rename g)) (VarSubst.cext ρ'))
    h
    (f := f) (Δ := Δ) (ρ := σ)

end Capless
