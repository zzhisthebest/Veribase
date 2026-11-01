import Capless.Store
import verisoftbench.Capless.Weakening.Subtyping
import verisoftbench.Capless.WellScoped.Basic
import verisoftbench.Capless.Renaming.Typing

/-!
# TypedCont Weakening

Proves that typed continuation judgments are preserved under term-variable,
type-variable, label-variable, and capture-variable context extension.

## Label weakening
- `TypedCont.lweaken`: Extending the context with a label variable binding

## Term-variable weakening
- `TypedCont.weaken`: Extending the context with a term variable binding

## Capture-variable weakening
- `TypedCont.cweaken`: Extending the context with a capture variable binding
-/

namespace Capless

/--
Label variable weakening for `TypedCont`: if `TypedCont Γ E cont E' Ct`,
then `TypedCont (Γ.label S) E.weaken cont.weaken E'.weaken Ct.weaken`.

The proof requires label weakening lemmas for `WellScoped` and `ESubtyp`
(not yet available) and is left as `sorry`.
-/
theorem TypedCont.lweaken
    {Γ : Context n m k} {E : EType n m k} {cont : Cont n m k}
    {E' : EType n m k} {Ct : CaptureSet n k}
    (S : SType n m k)
    (h : TypedCont Γ E cont E' Ct) :
    TypedCont (Γ.label S) E.weaken cont.weaken E'.weaken Ct.weaken := by
  have shift_ext_shift {n : Nat} :
      (FinFun.weaken : FinFun (n + 1) (n + 2)).ext ∘ FinFun.weaken =
        FinFun.weaken ∘ (FinFun.weaken : FinFun (n + 1) (n + 2)) := by
    funext i
    rfl
  have scoped_label {n m k : Nat} {Γ : Context n m k} {cont : Cont n m k}
      {Ct : CaptureSet n k} (h : WellScoped Γ cont Ct) (S : SType n m k) :
      WellScoped (Γ.label S) cont.weaken Ct.weaken := by
    induction h with
    | empty => exact .empty
    | union _ _ ih₁ ih₂ => exact .union ih₁ ih₂
    | singleton hb _ ih =>
      exact .singleton (Context.Bound.there_label hb) ih
    | csingleton hb _ ih =>
      exact .csingleton (Context.CBound.there_label hb) ih
    | cbound hb _ ih =>
      exact .cbound (Context.CBound.there_label hb) ih
    | label hb hl =>
      exact .label (Context.LBound.there_label hb) (Cont.HasLabel.weaken hl)
  induction h with
  | none hs => exact .none (ESubtyp.rename hs VarMap.lweaken)
  | cons ht hw hc ih =>
    simp only [Cont.weaken, EType.weaken, EType.rename, CaptureSet.weaken_union]
    refine TypedCont.cons ?_ (scoped_label hw S) (ih S)
    simpa [Term.weaken1, EType.weaken, CaptureSet.weaken,
      EType.rename_rename, CaptureSet.rename_rename, shift_ext_shift] using
      ht.rename (VarMap.lweaken_ext (P := S))
  | conse ht hw hc ih =>
    simp only [Cont.weaken, EType.weaken, EType.rename, CaptureSet.weaken_union]
    refine TypedCont.conse ?_ (scoped_label hw S) (ih S)
    simpa [Term.weaken1, EType.weaken, CaptureSet.weaken,
      EType.rename_rename, CaptureSet.rename_rename, shift_ext_shift,
      EType.cweaken, CaptureSet.cweaken, EType.rename_crename_comm,
      CaptureSet.rename_crename_comm, CBound.weaken, CBound.rename] using
      ht.rename (VarMap.lweaken_cext_ext (P := S))
  | scope hl hc hs ih =>
    apply TypedCont.scope (Context.LBound.there_label hl)
    · simpa [EType.weaken, EType.rename, CType.weaken, CType.rename,
        CaptureSet.weaken, CaptureSet.rename, SType.weaken] using ih S
    · simpa [CType.weaken, CType.rename, CaptureSet.weaken, CaptureSet.rename,
        SType.weaken] using CSubtyp.rename hs (VarMap.lweaken (S := S))

/--
Term-variable weakening for `TypedCont`: if `TypedCont Γ E t E' C0`,
then `TypedCont (Γ.var T) E.weaken t.weaken E'.weaken C0.weaken`.

The proof requires the mutual subtyping weakening theorems
(`ESubtyp.weaken` et al.) and is left as `sorry`.
-/
theorem TypedCont.weaken
    {Γ : Context n m k} {E : EType n m k} {t : Cont n m k}
    {E' : EType n m k} {C0 : CaptureSet n k}
    (T : CType n m k)
    (h : TypedCont Γ E t E' C0) :
    TypedCont (Γ.var T) E.weaken t.weaken E'.weaken C0.weaken := by
  have shift_ext_shift {n : Nat} :
      (FinFun.weaken : FinFun (n + 1) (n + 2)).ext ∘ FinFun.weaken =
        FinFun.weaken ∘ (FinFun.weaken : FinFun (n + 1) (n + 2)) := by
    funext i
    rfl
  induction h with
  | none hs => exact .none (ESubtyp.weaken hs T)
  | cons ht hw hc ih =>
    simp only [Cont.weaken, EType.weaken, EType.rename, CaptureSet.weaken_union]
    refine TypedCont.cons ?_ ?_ (ih T)
    · simpa [Term.weaken1, EType.weaken, CaptureSet.weaken,
        EType.rename_rename, CaptureSet.rename_rename, shift_ext_shift] using
        ht.rename (VarMap.weaken_ext (P := T))
    · exact WellScoped.weaken hw
  | conse ht hw hc ih =>
    simp only [Cont.weaken, EType.weaken, EType.rename, CaptureSet.weaken_union]
    refine TypedCont.conse ?_ ?_ (ih T)
    · simpa [Term.weaken1, EType.weaken, CaptureSet.weaken,
        EType.rename_rename, CaptureSet.rename_rename, shift_ext_shift,
        EType.cweaken, CaptureSet.cweaken, EType.rename_crename_comm,
        CaptureSet.rename_crename_comm, CBound.weaken, CBound.rename] using
        ht.rename (VarMap.weaken_cext_ext (P := T))
    · exact WellScoped.weaken hw
  | scope hl hc hs ih =>
    apply TypedCont.scope (Context.LBound.there_var hl)
    · simpa [EType.weaken, EType.rename, CType.weaken, CType.rename,
        CaptureSet.weaken, CaptureSet.rename, SType.weaken] using ih T
    · simpa [CType.weaken, CType.rename, CaptureSet.weaken, CaptureSet.rename, SType.weaken] using
        CSubtyp.weaken hs T

/--
Type-variable weakening for `TypedCont`: if `TypedCont Γ E t E' C0`,
then `TypedCont (Γ.tvar S) E.tweaken t.tweaken E'.tweaken C0`.

The proof uses type-variable weakening for `Typed`, `WellScoped`, `CSubtyp`,
and `ESubtyp`. The `cons` and `conse` cases require context commutation lemmas
and are left as `sorry`.
-/
theorem TypedCont.tweaken
    {Γ : Context n m k} {E : EType n m k} {t : Cont n m k}
    {E' : EType n m k} {C0 : CaptureSet n k}
    (S : TBinding n m k)
    (h : TypedCont Γ E t E' C0) :
    TypedCont (Γ.tvar S) E.tweaken t.tweaken E'.tweaken C0 := by
  have subc_trename {n m k m' : Nat} {Γ : Context n m k} {Δ : Context n m' k}
      {T U : CType n m k} {f : FinFun m m'} (h : CSubtyp Γ T U) (ρ : TVarMap Γ f Δ) :
      CSubtyp Δ (T.trename f) (U.trename f) := by
    cases h with
    | capt hc hs => exact .capt (Subcapt.trename hc ρ) (SSubtyp.trename hs ρ)
  have sube_trename {n m k m' : Nat} {Γ : Context n m k} {Δ : Context n m' k}
      {E E' : EType n m k} {f : FinFun m m'} (h : ESubtyp Γ E E') (ρ : TVarMap Γ f Δ) :
      ESubtyp Δ (E.trename f) (E'.trename f) := by
    cases h with
    | type h => exact .type (subc_trename h ρ)
    | exist h => exact .exist (subc_trename h (TVarMap.cext ρ _))
  let rec typed_trename {n m k m' : Nat} {Γ : Context n m k} {Δ : Context n m' k}
      {t : Term n m k} {E : EType n m k} {Ct : CaptureSet n k} {f : FinFun m m'}
      (h : Typed Γ t E Ct) (ρ : TVarMap Γ f Δ) :
      Typed Δ (t.trename f) (E.trename f) Ct := by
    match h with
    | .var hb => exact .var (ρ.map _ _ hb)
    | .label hb => exact .label (ρ.lmap _ _ hb)
    | .pack h => exact .pack (typed_trename h (TVarMap.cext ρ _))
    | .sub h hc hs => exact .sub (typed_trename h ρ) (Subcapt.trename hc ρ) (sube_trename hs ρ)
    | .abs h => exact .abs (typed_trename h (TVarMap.ext ρ _))
    | .tabs h => exact .tabs (typed_trename h (TVarMap.text ρ _))
    | .cabs h => exact .cabs (typed_trename h (TVarMap.cext ρ _))
    | .app h1 h2 =>
      simpa [EType.open, EType.trename_rename_comm] using
        Typed.app (typed_trename h1 ρ) (typed_trename h2 ρ)
    | .invoke h1 h2 => exact .invoke (typed_trename h1 ρ) (typed_trename h2 ρ)
    | .tapp h =>
      simpa [EType.topen, EType.trename_trename, ← FinFun.open_comp] using
        Typed.tapp (typed_trename h ρ)
    | .capp h =>
      simpa [EType.copen, EType.trename_crename_comm] using Typed.capp (typed_trename h ρ)
    | .letin h1 h2 =>
      apply Typed.letin (typed_trename h1 ρ)
      simpa [EType.weaken, EType.trename_rename_comm] using typed_trename h2 (TVarMap.ext ρ _)
    | .letex h1 h2 =>
      apply Typed.letex (typed_trename h1 ρ)
      simpa [EType.weaken, EType.cweaken, EType.trename_rename_comm,
        EType.trename_crename_comm] using typed_trename h2 (TVarMap.ext (TVarMap.cext ρ _) _)
    | .bindt h =>
      apply Typed.bindt
      simpa [EType.tweaken, EType.trename_trename, FinFun.weaken_comp_crename] using
        typed_trename h (TVarMap.text ρ _)
    | .bindc h =>
      apply Typed.bindc
      simpa [EType.cweaken, EType.trename_crename_comm] using typed_trename h (TVarMap.cext ρ _)
    | .boundary h =>
      apply Typed.boundary
      simpa [EType.trename, CType.trename, SType.weaken, SType.cweaken,
        SType.trename_rename_comm, SType.trename_crename_comm] using
        typed_trename h (TVarMap.ext (TVarMap.cext ρ _) _)
  induction h with
  | none h_sub =>
    apply TypedCont.none
    exact ESubtyp.tweaken (b := S) h_sub
  | cons h_ty h_ws h_cont ih =>
    refine TypedCont.cons ?_ ?_ (ih S)
    · simpa [Term.tweaken, EType.tweaken, EType.weaken,
        EType.trename_rename_comm] using typed_trename h_ty (TVarMap.weaken_ext (b := S))
    · exact WellScoped.tweaken S h_ws
  | conse h_ty h_ws h_cont ih =>
    refine TypedCont.conse ?_ ?_ (ih S)
    · simpa [Term.tweaken, EType.tweaken, EType.weaken, EType.cweaken,
        EType.trename_rename_comm, EType.trename_crename_comm] using
        typed_trename h_ty (TVarMap.weaken_cext_ext (b := S))
    · exact WellScoped.tweaken S h_ws
  | scope h_lb h_cont h_sub ih =>
    apply TypedCont.scope
    · exact Context.LBound.there_tvar h_lb
    · simpa using (ih S)
    · have h := CSubtyp.tweaken (b := S) h_sub
      simpa [CType.tweaken, CType.trename] using h

/--
Capture-variable weakening for `TypedCont`: if `TypedCont Γ E t E' Ct`,
then `TypedCont (Γ.cvar b) E.cweaken t.cweaken E'.cweaken Ct.cweaken`.

This extends `TypedCont.weaken` (term-variable weakening) and `TypedCont.lweaken`
(label weakening) to cover capture-variable context extensions.

The proof requires capture-variable weakening lemmas for `WellScoped`, `ESubtyp`,
`CSubtyp`, `SSubtyp`, and `Subcapt` and is left as `sorry`.
-/
theorem TypedCont.cweaken
    {Γ : Context n m k} {E : EType n m k} {t : Cont n m k}
    {E' : EType n m k} {Ct : CaptureSet n k}
    (b : CBinding n k)
    (h : TypedCont Γ E t E' Ct) :
    TypedCont (Γ.cvar b) E.cweaken t.cweaken E'.cweaken Ct.cweaken := by
  have scoped_capture {n m k : Nat} {Γ : Context n m k} {cont : Cont n m k}
      {Ct : CaptureSet n k} (h : WellScoped Γ cont Ct) (b : CBinding n k) :
      WellScoped (Γ.cvar b) cont.cweaken Ct.cweaken := by
    induction h with
    | empty => exact .empty
    | union _ _ ih₁ ih₂ => exact .union ih₁ ih₂
    | singleton hb _ ih => exact .singleton (Context.Bound.there_cvar hb) ih
    | csingleton hb _ ih => exact .csingleton (Context.CBound.there_cvar hb) ih
    | cbound hb _ ih => exact .cbound (Context.CBound.there_cvar hb) ih
    | label hb hl =>
      exact .label (Context.LBound.there_cvar hb) (Cont.HasLabel.cweaken hl)
  induction h with
  | none hs => exact .none (ESubtyp.crename hs CVarMap.weaken)
  | cons ht hw hc ih =>
    simp only [Cont.cweaken, EType.cweaken, EType.crename,
      CaptureSet.cweaken, CaptureSet.crename]
    refine TypedCont.cons ?_ (scoped_capture hw b) (ih b)
    simpa [Term.cweaken, EType.weaken_crename_comm, CaptureSet.weaken_crename_comm] using
      ht.crename (CVarMap.weaken_ext (b := b))
  | conse ht hw hc ih =>
    simp only [Cont.cweaken, EType.cweaken, EType.crename,
      CaptureSet.cweaken, CaptureSet.crename]
    refine TypedCont.conse ?_ (scoped_capture hw b) (ih b)
    simpa [Term.cweaken1, EType.weaken_crename_comm, CaptureSet.weaken_crename_comm,
      EType.cweaken_crename_comm, CaptureSet.cweaken_crename_comm,
      CBound.cweaken, CBound.crename] using
      ht.crename (CVarMap.weaken_cext_ext (b := b))
  | scope hl hc hs ih =>
    apply TypedCont.scope (Context.LBound.there_cvar hl)
    · simpa [EType.cweaken, EType.crename, CType.cweaken, CType.crename,
        CaptureSet.cweaken, CaptureSet.crename, SType.cweaken] using ih b
    · simpa [CType.cweaken, CType.crename, CaptureSet.cweaken, CaptureSet.crename,
        SType.cweaken] using CSubtyp.crename hs (CVarMap.weaken (b := b))

end Capless
