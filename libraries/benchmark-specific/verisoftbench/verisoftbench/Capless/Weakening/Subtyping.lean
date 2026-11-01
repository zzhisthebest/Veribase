import Capless.Subtyping
import Capless.Weakening.Subcapturing
import verisoftbench.Capless.Weakening.Basic
import verisoftbench.Capless.Renaming.Subtyping

/-!
# Weakening for Subtyping Relations

Proves that subcapturing (`Subcapt`) and subtyping (`SSubtyp`) relations are
preserved under label weakening and term-variable weakening.

## Label weakening

- `Subcapt.lweaken`: Subcapturing preserved under label variable extension
- `SSubtyp.lweaken`: Shape-type subtyping preserved under label variable extension

## Term-variable weakening

- `ESubtyp.weaken`, `CSubtyp.weaken`, `SSubtyp.weaken`: Mutual term-variable weakening
  for all three subtyping relations
-/

namespace Capless

/-! ## `Subcapt` label weakening -/

/--
Label variable weakening for `Subcapt`: if `Γ ⊢ C1 <:c C2`,
then `(Γ.label S_label) ⊢ C1.weaken <:c C2.weaken`.
-/
lemma Subcapt.lweaken {Γ : Context n m k} {C1 C2 : CaptureSet n k}
    (S_label : SType n m k) (h : Subcapt Γ C1 C2) :
    Subcapt (Γ.label S_label) C1.weaken C2.weaken := by
  induction h generalizing S_label with
  | trans h1 h2 ih1 ih2 =>
    apply Subcapt.trans; exact ih1 S_label; exact ih2 S_label
  | subset h =>
    apply Subcapt.subset
    induction h with
    | empty => exact CaptureSet.Subset.empty
    | rfl => exact CaptureSet.Subset.rfl
    | union_l h1 h2 ih1 ih2 =>
      apply CaptureSet.Subset.union_l; exact ih1; exact ih2
    | union_rl h ih =>
      simp [CaptureSet.weaken]; apply CaptureSet.Subset.union_rl; exact ih
    | union_rr h ih =>
      simp [CaptureSet.weaken]; apply CaptureSet.Subset.union_rr; exact ih
  | union h1 h2 ih1 ih2 =>
    simp [CaptureSet.weaken]; apply Subcapt.union; exact ih1 S_label; exact ih2 S_label
  | var hb =>
    simp [CaptureSet.weaken]; apply Subcapt.var
    simpa [CType.weaken_capt] using Context.Bound.there_label hb
  | cinstl hb =>
    simp [CaptureSet.weaken]; apply Subcapt.cinstl
    simpa [CBinding.weaken, CBinding.rename] using Context.CBound.there_label hb
  | cinstr hb =>
    simp [CaptureSet.weaken]; apply Subcapt.cinstr
    simpa [CBinding.weaken, CBinding.rename] using Context.CBound.there_label hb
  | cbound hb =>
    simp [CaptureSet.weaken]; apply Subcapt.cbound
    simpa [CBinding.weaken, CBinding.rename, CBound.weaken_upper] using
      Context.CBound.there_label hb

/-! ## `SSubtyp` label weakening -/

/--
Label variable weakening for `SSubtyp`: if `Γ ⊢ S1 <:s S2`,
then `(Γ.label S_label) ⊢ S1.weaken <:s S2.weaken`.

This is the main subtyping preservation theorem for shape types under label weakening.
The proof requires resolving context-ordering issues when label extension commutes with
`.var` and `.cvar` context extensions; the proof body is left as `sorry`.
-/
theorem SSubtyp.lweaken {Γ : Context n m k} {S1 S2 : SType n m k}
    (S_label : SType n m k) (h : SSubtyp Γ S1 S2) :
    SSubtyp (Γ.label S_label) (S1.weaken) (S2.weaken) := by
  exact SSubtyp.rename h VarMap.lweaken

/-! ## Type-variable weakening for `Subcapt` -/

/--
Type-variable weakening for `Subcapt`: if `Γ ⊢ C1 <:c C2`,
then `(Γ.tvar b) ⊢ C1 <:c C2`.

Note that capture sets do not change under type-variable weakening since
`CaptureSet n k` does not depend on the number of type variables (`m`).

This lemma provides the proof for `Capless.Subcapt.tweaken` (which is defined
as a `def` with `sorry` in the capless-lean repo).
-/
lemma Subcapt.tweaken_aux {Γ : Context n m k} {C1 C2 : CaptureSet n k}
    (b : TBinding n m k) (h : Subcapt Γ C1 C2) :
    Subcapt (Γ.tvar b) C1 C2 := by
  induction h with
  | trans h1 h2 ih1 ih2 =>
    apply Subcapt.trans
    · exact ih1
    · exact ih2
  | subset h => exact Subcapt.subset h
  | union h1 h2 ih1 ih2 =>
    apply Subcapt.union
    · exact ih1
    · exact ih2
  | var hb =>
    apply Subcapt.var
    exact Context.Bound.there_tvar hb
  | cinstl hb =>
    apply Subcapt.cinstl
    exact Context.CBound.there_tvar hb
  | cinstr hb =>
    apply Subcapt.cinstr
    exact Context.CBound.there_tvar hb
  | cbound hb =>
    apply Subcapt.cbound
    exact Context.CBound.there_tvar hb

/-! ## Type-variable weakening for `Subbound` -/

/--
Type-variable weakening for `Subbound`: if `Subbound Γ B1 B2`,
then `Subbound (Γ.tvar b) B1 B2`.

This lemma provides the proof for `Capless.Subbound.tweaken` (which is defined
as a `def` with `sorry` in the capless-lean repo).
-/
lemma Subbound.tweaken_aux {Γ : Context n m k} {B1 B2 : CBound n k}
    (b : TBinding n m k) (h : Subbound Γ B1 B2) :
    Subbound (Γ.tvar b) B1 B2 := by
  induction h with
  | set h =>
    apply Subbound.set
    apply Subcapt.tweaken_aux b h
  | star => apply Subbound.star

/-! ## Type-variable weakening for subtyping (mutual) -/

mutual
/--
Type-variable weakening for `SSubtyp`: if `Γ ⊢ S1 <:s S2`,
then `(Γ.tvar b) ⊢ S1.tweaken <:s S2.tweaken`.

The `tvar`, `tinstl`, `tinstr` cases require resolving index mismatches;
the `xforall`, `tforall`, and `cforall` cases require context-commutation
lemmas. These are left as `sorry`.
-/
theorem SSubtyp.tweaken {Γ : Context n m k} {S1 S2 : SType n m k} {b : TBinding n m k}
    (h : SSubtyp Γ S1 S2) :
    SSubtyp (Γ.tvar b) S1.tweaken S2.tweaken := by
  exact SSubtyp.trename h TVarMap.weaken

/--
Type-variable weakening for `CSubtyp`: if `ctx ⊢ T1 <: T2`,
then `(ctx.tvar b) ⊢ T1.tweaken <: T2.tweaken`.
-/
theorem CSubtyp.tweaken {Γ : Context n m k} {T1 T2 : CType n m k} {b : TBinding n m k}
    (h : CSubtyp Γ T1 T2) :
    CSubtyp (Γ.tvar b) T1.tweaken T2.tweaken := by
  cases h with
  | capt hc hs => exact CSubtyp.capt (Subcapt.tweaken_aux b hc) (SSubtyp.tweaken hs)

/--
Type-variable weakening for `ESubtyp`: if `Γ ⊢ E1 <:e E2`,
then `(Γ.tvar b) ⊢ E1.tweaken <:e E2.tweaken`.

The `exist` case requires a context-commutation lemma and is left as `sorry`.
-/
theorem ESubtyp.tweaken {Γ : Context n m k} {E1 E2 : EType n m k} {b : TBinding n m k}
    (h : ESubtyp Γ E1 E2) :
    ESubtyp (Γ.tvar b) E1.tweaken E2.tweaken := by
  cases h with
  | type hc => exact ESubtyp.type (CSubtyp.tweaken hc)
  | exist hc =>
    apply ESubtyp.exist
    cases hc with
    | capt hcap hs =>
      exact CSubtyp.capt (Subcapt.trename hcap (TVarMap.cext TVarMap.weaken _))
        (SSubtyp.trename hs (TVarMap.cext TVarMap.weaken _))
end

/-! ## Term-variable weakening for subtyping -/

/-- Weakening for `ESubtyp` by a term variable: if `Γ ⊢ E1 <:e E2`,
then `(Γ.var T) ⊢ E1.weaken <:e E2.weaken`. -/
theorem ESubtyp.weaken {Γ : Context n m k} {E1 E2 : EType n m k}
    (h : ESubtyp Γ E1 E2) (T : CType n m k) :
    ESubtyp (Γ.var T) (E1.weaken) (E2.weaken) := by
  exact ESubtyp.rename h VarMap.weaken

/-- Weakening for `CSubtyp` by a term variable: if `Γ ⊢ C1 <: C2`,
then `(Γ.var T) ⊢ C1.weaken <: C2.weaken`. -/
theorem CSubtyp.weaken {Γ : Context n m k} {C1 C2 : CType n m k}
    (h : CSubtyp Γ C1 C2) (T : CType n m k) :
    CSubtyp (Γ.var T) (C1.weaken) (C2.weaken) := by
  exact CSubtyp.rename h VarMap.weaken

/-- Weakening for `SSubtyp` by a term variable: if `Γ ⊢ S1 <:s S2`,
then `(Γ.var T) ⊢ S1.weaken <:s S2.weaken`. -/
theorem SSubtyp.weaken {Γ : Context n m k} {S1 S2 : SType n m k}
    (h : SSubtyp Γ S1 S2) (T : CType n m k) :
    SSubtyp (Γ.var T) (S1.weaken) (S2.weaken) := by
  exact SSubtyp.rename h VarMap.weaken

end Capless
