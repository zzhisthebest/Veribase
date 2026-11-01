import Capless.Subst.Capture.Subtyping
import Capless.Subst.Capture.Subcapturing
import verisoftbench.Capless.Basic

/-!
# Capture Variable Substitution Preserves Subtyping

This module proves that subcapturing, subbounding, and subtyping relations
are preserved under capture variable substitution. If two types are in a subtyping
relation in context `Γ`, then after substituting capture variables via a valid
`CVarSubst`, they remain in the same subtyping relation in the target context `Δ`.

These are the capture-substitution analog of the capture-variable renaming (`crename`)
theorems in `verisoftbench.Capless.Renaming.Subtyping`, using `CVarSubst` (which additionally
handles capture-variable substitution with bound → open capture-set conversion)
instead of `CVarMap` (pure renaming).
-/

set_option quotPrecheck false
namespace Capless

/-! ## `Subcapt` is preserved under capture variable substitution -/

/--
Subcapturing is preserved under capture variable substitution.
If `Γ ⊢ C1 <:c C2` and `ρ : CVarSubst Γ f Δ`, then `Δ ⊢ C1.crename f <:c C2.crename f`.
-/
theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (ρ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h with
  | trans h1 h2 ih1 ih2 =>
      apply Subcapt.trans
      · apply ih1 ρ
      · apply ih2 ρ
  | subset h =>
      apply Subcapt.subset
      apply CaptureSet.crename_monotone h
  | union h1 h2 ih1 ih2 =>
      apply Subcapt.union
      · apply ih1 ρ
      · apply ih2 ρ
  | var h =>
      apply Subcapt.var
      apply ρ.map _ _ h
  | cinstl h =>
      apply Subcapt.cinstl
      apply ρ.cmap _ _ h
  | cinstr h =>
      apply Subcapt.cinstr
      apply ρ.cmap _ _ h
  | @cbound Γ c C h =>
      have hbound : Subbound Δ (CBound.upper (CaptureSet.csingleton (f c)))
        (CBound.upper (C.crename f)) :=
        ρ.cmap_bound c (CBound.upper C) h
      cases hbound with
      | set hsc => exact hsc

/-! ## `Subbound` is preserved under capture variable substitution -/

/--
Subbounding is preserved under capture variable substitution.
If `Γ ⊢ B1 <:b B2` and `ρ : CVarSubst Γ f Δ`, then `Δ ⊢ B1.crename f <:b B2.crename f`.
-/
theorem Subbound.csubst
  (h : Subbound Γ B1 B2)
  (ρ : CVarSubst Γ f Δ) :
  Subbound Δ (B1.crename f) (B2.crename f) := by
  induction h using Subbound.rec with
  | set h =>
      simp [CBound.crename]
      apply Subbound.set
      apply Subcapt.csubst h ρ
  | star =>
      apply Subbound.star

/-! ## `SSubtyp` is preserved under capture variable substitution

The proof uses mutual induction on the subtyping relation, simultaneously
proving preservation for `ESubtyp` and `CSubtyp`.

Note: This is the main theorem for shape types. `CSubtyp.csubst` and
`ESubtyp.csubst` (defined below) use simpler case analysis, delegating to
this theorem or to `Subcapt.csubst`/`Subbound.csubst`.
-/

/--
`SSubtyp` is preserved under capture variable substitution.
If `Γ ⊢ S1 <:s S2` and `σ : CVarSubst Γ f Δ`, then `Δ ⊢ S1.crename f <:s S2.crename f`.
-/
theorem SSubtyp.csubst
  (h : SSubtyp Γ S1 S2)
  (σ : CVarSubst Γ f Δ) :
  SSubtyp Δ (S1.crename f) (S2.crename f) := by
  refine SSubtyp.rec
    (motive_1 := fun {n m k} Γ' E1' E2' _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarSubst Γ' f' Δ'),
        ESubtyp Δ' (E1'.crename f') (E2'.crename f'))
    (motive_2 := fun {n m k} Γ' C1' C2' _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarSubst Γ' f' Δ'),
        CSubtyp Δ' (C1'.crename f') (C2'.crename f'))
    (motive_3 := fun {n m k} Γ' S1' S2' _ =>
      ∀ {k'} (f' : FinFun k k') (Δ' : Context n m k') (ρ' : CVarSubst Γ' f' Δ'),
        SSubtyp Δ' (S1'.crename f') (S2'.crename f'))
    (fun {n m k Γ' T1 T2 hC ih k' f' Δ' ρ'} => by
      simp [EType.crename]
      apply ESubtyp.exist
      apply ih (k' := k' + 1) f'.ext (Δ'.cvar (CBinding.bound CBound.star))
        (ρ'.cext (b := CBinding.bound CBound.star)))
    (fun {n m k Γ' T1 T2 hC ih k' f' Δ' ρ'} => by
      simp [EType.crename]
      apply ESubtyp.type
      apply ih f' Δ' ρ')
    (fun {n m k Γ' C1' C2' S1' S2' hSc hS ih k' f' Δ' ρ'} => by
      simp [CType.crename]
      apply CSubtyp.capt
      · apply Subcapt.csubst hSc ρ'
      · apply ih f' Δ' ρ')
    (fun {n m k Γ' S' k' f' Δ' ρ'} =>
      SSubtyp.top (S := S'.crename f'))
    (fun {n m k Γ' S' k' f' Δ' ρ'} =>
      SSubtyp.refl (S := S'.crename f'))
    (fun {n m k Γ' S1' S2' S3' h12 h23 ih12 ih23 k' f' Δ' ρ'} =>
      SSubtyp.trans (ih12 f' Δ' ρ') (ih23 f' Δ' ρ'))
    (fun {n m k Γ' X S' hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tvar
      apply ρ'.tmap X (TBinding.bound S') hb)
    (fun {n m k Γ' X S' hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tinstl
      apply ρ'.tmap X (TBinding.inst S') hb)
    (fun {n m k Γ' X S' hb k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tinstr
      apply ρ'.tmap X (TBinding.inst S') hb)
    (fun {n m k Γ' T1 T2 hc ih k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.boxed
      apply ih f' Δ' ρ')
    (fun {n m k Γ' S2' S1' hs ih k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.label
      apply ih f' Δ' ρ')
    (fun {n m k Γ' E2' E1' F1 F2 hc he ihc ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.xforall
      · apply ihc f' Δ' ρ'
      · apply ihe f' (Δ'.var (E2'.crename f')) (ρ'.ext E2'))
    (fun {n m k Γ' S2' S1' E1' E2' hs he ihs ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.tforall
      · apply ihs f' Δ' ρ'
      · apply ihe f' (Δ'.tvar (TBinding.bound (S2'.crename f'))) (ρ'.text (T := TBinding.bound S2')))
    (fun {n m k Γ' B2' B1' E1' E2' hb he ihe k' f' Δ' ρ'} => by
      simp [SType.crename]
      apply SSubtyp.cforall
      · apply Subbound.csubst hb ρ'
      · apply ihe (f' := f'.ext) (k' := k' + 1) (Δ' := Δ'.cvar (CBinding.bound (B2'.crename f')))
          (ρ' := ρ'.cext (b := CBinding.bound B2')))
    h
    f Δ σ

/-! ## `CSubtyp` is preserved under capture variable substitution -/

/--
`CSubtyp` is preserved under capture variable substitution.
If `Γ ⊢ C1 <: C2` and `σ : CVarSubst Γ f Δ`, then `Δ ⊢ C1.crename f <: C2.crename f`.
-/
theorem CSubtyp.csubst
  (h : CSubtyp Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  CSubtyp Δ (C1.crename f) (C2.crename f) := by
  cases h
  case capt hSc hS =>
    simp [CType.crename]
    apply CSubtyp.capt
    · apply Subcapt.csubst hSc σ
    · apply SSubtyp.csubst hS σ

/-! ## `ESubtyp` is preserved under capture variable substitution -/

/--
`ESubtyp` is preserved under capture variable substitution.
If `Γ ⊢ E1 <:e E2` and `σ : CVarSubst Γ f Δ`, then `Δ ⊢ E1.crename f <:e E2.crename f`.
-/
theorem ESubtyp.csubst
  (h : ESubtyp Γ E1 E2)
  (σ : CVarSubst Γ f Δ) :
  ESubtyp Δ (E1.crename f) (E2.crename f) := by
  cases h
  case exist hC =>
    simp [EType.crename]
    apply ESubtyp.exist
    apply CSubtyp.csubst hC (σ.cext (b := CBinding.bound CBound.star))
  case type hC =>
    simp [EType.crename]
    apply ESubtyp.type
    apply CSubtyp.csubst hC σ

end Capless
