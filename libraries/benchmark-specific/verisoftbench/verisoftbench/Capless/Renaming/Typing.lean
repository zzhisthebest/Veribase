import Capless.Renaming.Basic
import Capless.Renaming.Capture.Typing
import Capless.Term
import verisoftbench.Capless.Renaming.Subtyping
import verisoftbench.Capless.Renaming.Basic

/-!
# Renaming Preserves Typing

This module proves that typing judgments are preserved under both term-variable
and capture-variable renaming.

## Capture Variable Renaming

If a term `t` has type `E` with capture set `Ct` in context `Γ`,
then after renaming capture variables via a valid `CVarMap`, the renamed term
`t.crename f` has type `E.crename f` with capture set `Ct.crename f` in the
target context `Δ`.

## Term Variable Renaming

If a term `t` has type `E` with capture set `Ct` in context `Γ`,
then after renaming term variables via a valid `VarMap`, the renamed term
`t.rename f` has type `E.rename f` with capture set `Ct.rename f` in the
target context `Δ`.
-/

namespace Capless

/--
Typing is preserved under capture variable renaming.
If `Γ ⊢ t : E @ Ct` and `ρ : CVarMap Γ f Δ`, then
`Δ ⊢ t.crename f : E.crename f @ Ct.crename f`.
-/
theorem Typed.crename {Γ : Context n m k} {Δ : Context n m k'}
    (h : Typed Γ t E Ct)
    (ρ : CVarMap Γ f Δ) :
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
      exact Typed.pack (Typed.crename h (CVarMap.cext ρ (CBinding.inst _)))
  | Typed.sub h1 hc hs =>
    by
      exact Typed.sub (Typed.crename h1 ρ)
        (Subcapt.crename hc ρ) (ESubtyp.crename hs ρ)
  | Typed.abs h =>
    by
      simp [Term.crename, EType.crename]
      apply Typed.abs
      simpa [CaptureSet.crename, CaptureSet.weaken_crename_comm] using
        Typed.crename h (CVarMap.ext ρ _)
  | Typed.tabs h =>
    by
      simp [Term.crename, EType.crename]
      apply Typed.tabs
      exact Typed.crename h (CVarMap.text ρ _)
  | Typed.cabs h =>
    by
      simp [Term.crename, EType.crename]
      apply Typed.cabs
      simpa [CaptureSet.cweaken_crename_comm] using Typed.crename h (CVarMap.cext ρ _)
  | Typed.app h1 h2 =>
    by
      simp [Term.crename, CaptureSet.crename]
      simpa [EType.open_crename_comm] using Typed.app (Typed.crename h1 ρ) (Typed.crename h2 ρ)
  | Typed.invoke h1 h2 =>
    by
      simp [Term.crename, CaptureSet.crename]
      exact Typed.invoke (Typed.crename h1 ρ) (Typed.crename h2 ρ)
  | Typed.tapp h =>
    by
      simp [Term.crename, CaptureSet.crename]
      simpa [EType.topen_crename] using Typed.tapp (Typed.crename h ρ)
  | Typed.capp h =>
    by
      simp [Term.crename, CaptureSet.crename]
      simpa [EType.copen_crename] using Typed.capp (Typed.crename h ρ)
  | Typed.letin h1 h2 =>
    by
      simp [Term.crename]
      apply Typed.letin
      · exact Typed.crename h1 ρ
      · simpa [EType.weaken_crename_comm, CaptureSet.weaken_crename_comm] using
          Typed.crename h2 (CVarMap.ext ρ _)
  | Typed.letex h1 h2 =>
    by
      simp [Term.crename]
      apply Typed.letex
      · exact Typed.crename h1 ρ
      · simpa [EType.weaken_crename_comm, EType.cweaken_crename_comm,
          CaptureSet.weaken_crename_comm, CaptureSet.cweaken_crename_comm] using
          Typed.crename h2 (CVarMap.ext (CVarMap.cext ρ _) _)
  | Typed.bindt h =>
    by
      simp [Term.crename]
      apply Typed.bindt
      simpa [EType.tweaken_crename_comm] using Typed.crename h (CVarMap.text ρ _)
  | Typed.bindc h =>
    by
      simp [Term.crename]
      apply Typed.bindc
      simpa [EType.cweaken_crename_comm, CaptureSet.cweaken_crename_comm] using
        Typed.crename h (CVarMap.cext ρ _)
  | Typed.boundary h =>
    by
      simp [Term.crename, EType.crename]
      apply Typed.boundary
      simpa [EType.crename, CType.crename, SType.weaken_crename_comm,
        SType.cweaken_crename_comm, CaptureSet.weaken_crename_comm,
        CaptureSet.cweaken_crename_comm, CaptureSet.crename, FinFun.ext_zero,
        SType.crename_label, CBinding.crename, CBound.crename] using
        Typed.crename h (CVarMap.ext (CVarMap.cext ρ _) _)

/--
Typing is preserved under term-variable renaming.
If `Γ ⊢ t : E @ Ct` and `ρ : VarMap Γ f Δ`, then
`Δ ⊢ t.rename f : E.rename f @ Ct.rename f`.
-/
theorem Typed.rename {Γ : Context n m k} {Δ : Context n' m k} {f : FinFun n n'}
    (h : Typed Γ t E Ct) (ρ : VarMap Γ f Δ) :
    Typed Δ (t.rename f) (E.rename f) (Ct.rename f) := by
  match h with
  | .var hb => exact .var (ρ.map _ _ hb)
  | .label hb => exact .label (ρ.lmap _ _ hb)
  | .pack h => exact .pack (Typed.rename h (VarMap.cext ρ _))
  | .sub h hc hs => exact .sub (Typed.rename h ρ) (Subcapt.rename hc ρ) (ESubtyp.rename hs ρ)
  | .abs h =>
    apply Typed.abs
    simpa [CaptureSet.weaken, CaptureSet.rename, CaptureSet.rename_rename,
      FinFun.weaken_comp_crename, FinFun.ext_zero] using Typed.rename h (VarMap.ext ρ _)
  | .tabs h => exact .tabs (Typed.rename h (VarMap.text ρ _))
  | .cabs h =>
    apply Typed.cabs
    simpa [CaptureSet.cweaken, ← CaptureSet.rename_crename_comm] using
      Typed.rename h (VarMap.cext ρ _)
  | .app h1 h2 =>
    simpa [EType.open, EType.rename_rename, ← FinFun.open_comp] using
      Typed.app (Typed.rename h1 ρ) (Typed.rename h2 ρ)
  | .invoke h1 h2 => exact .invoke (Typed.rename h1 ρ) (Typed.rename h2 ρ)
  | .tapp h =>
    simpa [EType.topen, EType.trename_rename_comm] using Typed.tapp (Typed.rename h ρ)
  | .capp h =>
    simpa [EType.copen, ← EType.rename_crename_comm] using Typed.capp (Typed.rename h ρ)
  | .letin h1 h2 =>
    apply Typed.letin (Typed.rename h1 ρ)
    simpa [EType.weaken, CaptureSet.weaken, EType.rename_rename,
      CaptureSet.rename_rename, FinFun.weaken_comp_crename] using
      Typed.rename h2 (VarMap.ext ρ _)
  | .letex h1 h2 =>
    apply Typed.letex (Typed.rename h1 ρ)
    simpa [EType.weaken, CaptureSet.weaken, EType.rename_rename,
      CaptureSet.rename_rename, FinFun.weaken_comp_crename, EType.cweaken,
      CaptureSet.cweaken, ← EType.rename_crename_comm, ← CaptureSet.rename_crename_comm] using
      Typed.rename h2 (VarMap.ext (VarMap.cext ρ _) _)
  | .bindt h =>
    apply Typed.bindt
    simpa [EType.tweaken, EType.trename_rename_comm] using Typed.rename h (VarMap.text ρ _)
  | .bindc h =>
    apply Typed.bindc
    simpa [EType.cweaken, CaptureSet.cweaken, ← EType.rename_crename_comm,
      ← CaptureSet.rename_crename_comm] using Typed.rename h (VarMap.cext ρ _)
  | .boundary h =>
    apply Typed.boundary
    simpa [EType.rename, CType.rename, SType.rename, SType.weaken, CaptureSet.weaken,
      SType.rename_rename, CaptureSet.rename_rename, FinFun.weaken_comp_crename,
      SType.cweaken, CaptureSet.cweaken, ← SType.rename_crename_comm,
      ← CaptureSet.rename_crename_comm, CaptureSet.rename, FinFun.ext_zero,
      CBinding.rename, CBound.rename] using Typed.rename h (VarMap.ext (VarMap.cext ρ _) _)

end Capless
