import Capless.Typing
import Capless.Subst.Basic
import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
import Capless.Subst.Capture.Typing
import verisoftbench.Capless.Basic
import verisoftbench.Capless.Renaming.Basic
import verisoftbench.Capless.Subst.Subtyping
import verisoftbench.Capless.Subst.Capture.Subtyping

/-!
# Substitution for Typing

Renaming/substitution theorems for the `Typed` relation.

## Term Variable Substitution

`Typed.subst_1` shows that if `Γ ⊢ t : E @ Ct` and we have a valid variable
substitution morphism `σ : VarSubst Γ f Δ`, then after renaming we get
`Δ ⊢ t.rename f : E.rename f @ Ct.rename f`.

## Capture Variable Substitution

`Typed.csubst_1` is the analogous theorem for capture variable renaming:
if `Γ ⊢ t : E @ Ct` and `σ : CVarSubst Γ f Δ`, then
`Δ ⊢ t.crename f : E.crename f @ Ct.crename f`.
-/

namespace Capless

/--
**Term variable substitution lemma for typing**: If a term `t` is typed in context `Γ` with
type `E` and capture set `Ct`, and `σ` is a valid variable substitution from
`Γ` to `Δ` via renaming `f`, then the renamed term `t.rename f` is typed in
`Δ` with appropriately renamed type and capture set.

This lemma is the core renaming/substitution theorem for the Capless type system.
It handles all typing rules including abstraction (where bound variables require
special handling of capture sets), type application, capture application,
invocation, and subsumption.
-/
theorem Typed.subst_1
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : Typed Γ t E Ct)
  (σ : VarSubst Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) (Ct.rename f) := by
  have tighten {n m k : Nat} {Γ : Context n m k} {x : Fin n}
      {C C0 : CaptureSet n k} {S : SType n m k}
      (h : Typed Γ (Term.var x) (EType.type (CType.capt C S)) C0) :
      Typed Γ (Term.var x) (EType.type (CType.capt {x=x} S)) {x=x} := by
    generalize ht : Term.var x = t at h
    generalize he : EType.type (CType.capt C S) = E at h
    induction h with
    | var hb => cases ht; cases he; exact .var hb
    | label hb => cases ht; cases he; exact .label hb
    | sub h hc hs ih =>
      cases hs with
      | exist hs => cases he
      | type hs =>
        cases hs with
        | capt hc' hs =>
          cases he
          exact .sub (ih ht rfl) (.subset .rfl) (.type (.capt (.subset .rfl) hs))
    | _ => cases ht
  have effect {n m k n' : Nat} {Γ : Context n m k} {Δ : Context n' m k}
      {f : FinFun n n'} {E1 E2 : EType n m k}
      (h : ESubtyp Γ E1 E2) (σ : VarSubst Γ f Δ) :
      ESubtyp Δ (E1.rename f) (E2.rename f) := by
    cases h with
    | exist h =>
      cases h with
      | capt hc hs => exact .exist (.capt (Subcapt.subst hc σ.cext) (SSubtyp.subst hs σ.cext))
    | type h =>
      cases h with
      | capt hc hs => exact .type (.capt (Subcapt.subst hc σ) (SSubtyp.subst hs σ))
  let rec typing {n m k n' : Nat} {Γ : Context n m k} {Δ : Context n' m k} {f : FinFun n n'} {t : Term n m k} {E : EType n m k} {Ct : CaptureSet n k}
      (h : Typed Γ t E Ct) (ρ : VarSubst Γ f Δ) :
      Typed Δ (t.rename f) (E.rename f) (Ct.rename f) := by
    match h with
    | .var hb => exact tighten (ρ.map _ _ hb)
    | .label hb => exact .label (ρ.lmap _ _ hb)
    | .pack h => exact .pack (typing h (VarSubst.cext ρ))
    | .sub h hc hs => exact .sub (typing h ρ) (Subcapt.subst hc ρ) (effect hs ρ)
    | .abs h =>
      apply Typed.abs
      simpa [CaptureSet.weaken, CaptureSet.rename, CaptureSet.rename_rename,
        FinFun.weaken_comp_crename, FinFun.ext_zero] using typing h (VarSubst.ext ρ _)
    | .tabs h => exact .tabs (typing h (VarSubst.text ρ))
    | .cabs h =>
      apply Typed.cabs
      simpa [CaptureSet.cweaken, ← CaptureSet.rename_crename_comm] using
        typing h (VarSubst.cext ρ)
    | .app h1 h2 =>
      simpa [EType.open, EType.rename_rename, ← FinFun.open_comp] using
        Typed.app (typing h1 ρ) (typing h2 ρ)
    | .invoke h1 h2 => exact .invoke (typing h1 ρ) (typing h2 ρ)
    | .tapp h =>
      simpa [EType.topen, EType.trename_rename_comm] using Typed.tapp (typing h ρ)
    | .capp h =>
      simpa [EType.copen, ← EType.rename_crename_comm] using Typed.capp (typing h ρ)
    | .letin h1 h2 =>
      apply Typed.letin (typing h1 ρ)
      simpa [EType.weaken, CaptureSet.weaken, EType.rename_rename,
        CaptureSet.rename_rename, FinFun.weaken_comp_crename] using
        typing h2 (VarSubst.ext ρ _)
    | .letex h1 h2 =>
      apply Typed.letex (typing h1 ρ)
      simpa [EType.weaken, CaptureSet.weaken, EType.rename_rename,
        CaptureSet.rename_rename, FinFun.weaken_comp_crename, EType.cweaken,
        CaptureSet.cweaken, ← EType.rename_crename_comm, ← CaptureSet.rename_crename_comm] using
        typing h2 (VarSubst.ext (VarSubst.cext ρ) _)
    | .bindt h =>
      apply Typed.bindt
      simpa [EType.tweaken, EType.trename_rename_comm] using typing h (VarSubst.text ρ)
    | .bindc h =>
      apply Typed.bindc
      simpa [EType.cweaken, CaptureSet.cweaken, ← EType.rename_crename_comm,
        ← CaptureSet.rename_crename_comm] using typing h (VarSubst.cext ρ)
    | .boundary h =>
      apply Typed.boundary
      simpa [EType.rename, CType.rename, SType.rename, SType.weaken, CaptureSet.weaken,
        SType.rename_rename, CaptureSet.rename_rename, FinFun.weaken_comp_crename,
        SType.cweaken, CaptureSet.cweaken, ← SType.rename_crename_comm,
        ← CaptureSet.rename_crename_comm, CaptureSet.rename, FinFun.ext_zero,
        CBinding.rename, CBound.rename] using typing h (VarSubst.ext (VarSubst.cext ρ) _)
  exact typing h σ

/--
**Capture variable substitution lemma for typing**: If a term `t` is typed in context `Γ`
with type `E` and capture set `Ct`, and `σ` is a valid capture variable substitution from
`Γ` to `Δ` via crenaem function `f`, then the renamed term `t.crename f` is typed in
`Δ` with appropriately crenamed type and capture set.

This is the capture-level analogue of `Typed.subst_1` and `Typed.tsubst_1`, handling
the `CVarSubst` context morphism which renames capture variables.
-/
theorem Typed.csubst_1
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : Typed Γ t E Ct)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) (Ct.crename f) := by
  let rec typing {n m k k' : Nat} {Γ : Context n m k} {Δ : Context n m k'} {f : FinFun k k'} {t : Term n m k} {E : EType n m k} {Ct : CaptureSet n k}
      (h : Typed Γ t E Ct)
      (ρ : CVarSubst Γ f Δ) :
      Typed Δ (t.crename f) (E.crename f) (Ct.crename f) :=
    match h with
    | Typed.var hb =>
      by
        simp [Term.crename]
        exact Typed.var (ρ.map _ _ hb)
    | Typed.label hb =>
      by
        simp [Term.crename]
        exact Typed.label (ρ.lmap _ _ hb)
    | Typed.pack h =>
      by
        simp [Term.crename, EType.crename]
        exact Typed.pack (typing h (CVarSubst.cext ρ))
    | Typed.sub h1 hc hs =>
      by
        exact Typed.sub (typing h1 ρ)
          (Subcapt.csubst hc ρ) (ESubtyp.csubst hs ρ)
    | Typed.abs h =>
      by
        simp [Term.crename, EType.crename]
        apply Typed.abs
        simpa [CaptureSet.crename, CaptureSet.weaken_crename_comm] using
          typing h (CVarSubst.ext ρ _)
    | Typed.tabs h =>
      by
        simp [Term.crename, EType.crename]
        apply Typed.tabs
        exact typing h (CVarSubst.text ρ)
    | Typed.cabs h =>
      by
        simp [Term.crename, EType.crename]
        apply Typed.cabs
        simpa [CaptureSet.cweaken_crename_comm] using typing h (CVarSubst.cext ρ)
    | Typed.app h1 h2 =>
      by
        simp [Term.crename, CaptureSet.crename]
        simpa [EType.open_crename_comm] using Typed.app (typing h1 ρ) (typing h2 ρ)
    | Typed.invoke h1 h2 =>
      by
        simp [Term.crename, CaptureSet.crename]
        exact Typed.invoke (typing h1 ρ) (typing h2 ρ)
    | Typed.tapp h =>
      by
        simp [Term.crename, CaptureSet.crename]
        simpa [EType.topen_crename] using Typed.tapp (typing h ρ)
    | Typed.capp h =>
      by
        simp [Term.crename, CaptureSet.crename]
        simpa [EType.copen_crename] using Typed.capp (typing h ρ)
    | Typed.letin h1 h2 =>
      by
        simp [Term.crename]
        apply Typed.letin
        · exact typing h1 ρ
        · simpa [EType.weaken_crename_comm, CaptureSet.weaken_crename_comm] using
            typing h2 (CVarSubst.ext ρ _)
    | Typed.letex h1 h2 =>
      by
        simp [Term.crename]
        apply Typed.letex
        · exact typing h1 ρ
        · simpa [EType.weaken_crename_comm, EType.cweaken_crename_comm,
            CaptureSet.weaken_crename_comm, CaptureSet.cweaken_crename_comm] using
            typing h2 (CVarSubst.ext (CVarSubst.cext ρ) _)
    | Typed.bindt h =>
      by
        simp [Term.crename]
        apply Typed.bindt
        simpa [EType.tweaken_crename_comm] using typing h (CVarSubst.text ρ)
    | Typed.bindc h =>
      by
        simp [Term.crename]
        apply Typed.bindc
        simpa [EType.cweaken_crename_comm, CaptureSet.cweaken_crename_comm] using
          typing h (CVarSubst.cext ρ)
    | Typed.boundary h =>
      by
        simp [Term.crename, EType.crename]
        apply Typed.boundary
        simpa [EType.crename, CType.crename, SType.weaken_crename_comm,
          SType.cweaken_crename_comm, CaptureSet.weaken_crename_comm,
          CaptureSet.cweaken_crename_comm, CaptureSet.crename, FinFun.ext_zero,
          SType.crename_label, CBinding.crename, CBound.crename] using
          typing h (CVarSubst.ext (CVarSubst.cext ρ) _)
  exact typing h σ

/--
**Type variable substitution lemma**: If a term `t` is typed in context `Γ` with
type `E` and capture set `Ct`, and `σ` is a valid type-variable substitution from
`Γ` to `Δ` via renaming `f` on type variables, then the trenamed term `t.trename f`
is typed in `Δ` with appropriately trenamed type. The capture set `Ct` is unchanged.
-/
theorem Typed.tsubst_1
  {Γ : Context n m k} {Δ : Context n m' k}
  (h : Typed Γ t E Ct)
  (σ : TVarSubst Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) Ct := by
  let rec typing {n m k m' : Nat} {Γ : Context n m k} {Δ : Context n m' k} {f : FinFun m m'} {t : Term n m k} {E : EType n m k} {Ct : CaptureSet n k}
      (h : Typed Γ t E Ct) (σ : TVarSubst Γ f Δ) :
      Typed Δ (t.trename f) (E.trename f) Ct :=
    match h with
    | .var hb => .var (σ.map _ _ hb)
    | .label hb => .label (σ.lmap _ _ hb)
    | .pack h => .pack (typing h σ.cext)
    | .sub h hc he => .sub (typing h σ) (Subcapt.tsubst hc σ) (ESubtyp.tsubst he σ)
    | .abs h => .abs (typing h (σ.ext _))
    | .tabs h => .tabs (typing h (σ.text _))
    | .cabs h => .cabs (typing h σ.cext)
    | .app h1 h2 => by
      simpa [Term.trename, EType.open, EType.trename_rename_comm] using
        Typed.app (typing h1 σ) (typing h2 σ)
    | .invoke h1 h2 => .invoke (typing h1 σ) (typing h2 σ)
    | .tapp h => by
      have hopen : ∀ X, FinFun.open (f X) ∘ f.ext = f ∘ FinFun.open X := by
        intro X; funext i; cases i using Fin.cases <;> rfl
      simpa [Term.trename, EType.topen, EType.trename_trename, hopen] using Typed.tapp (typing h σ)
    | .capp h => by
      simpa [Term.trename, EType.copen, EType.trename_crename_comm] using Typed.capp (typing h σ)
    | .letin h1 h2 => by
      apply Typed.letin (typing h1 σ)
      simpa [EType.weaken, EType.trename_rename_comm] using typing h2 (σ.ext _)
    | .letex h1 h2 => by
      apply Typed.letex (typing h1 σ)
      simpa [EType.weaken, EType.cweaken, EType.trename_rename_comm, EType.trename_crename_comm] using
        typing h2 (σ.cext.ext _)
    | .bindt h => by
      apply Typed.bindt
      simpa [EType.tweaken, EType.trename_trename] using typing h (σ.text _)
    | .bindc h => by
      apply Typed.bindc
      simpa [EType.cweaken, EType.trename_crename_comm] using typing h σ.cext
    | .boundary h => by
      apply Typed.boundary
      simpa [EType.trename, CType.trename, SType.trename, SType.cweaken, SType.weaken, SType.trename_crename_comm, SType.trename_rename_comm] using
        typing h (σ.cext.ext _)
  exact typing h σ

end Capless
