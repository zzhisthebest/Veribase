import Capless.Store
import Capless.Weakening.Basic

/-!
# Weakening for Well-Scoped Continuations

Proves weakening properties for the `WellScoped` predicate and `Cont.HasLabel`
relation under term-variable context extension (`Γ.var T`).

Includes context bound weakening lemmas that lift `VarMap.weaken` to the
individual context-binding predicates (`Bound`, `LBound`, `TBound`, `CBound`).
-/

namespace Capless

/-! ## CaptureSet.weaken distributes over union -/

/-- `CaptureSet.weaken` distributes over union. -/
lemma CaptureSet.weaken_union {n k} (C1 C2 : CaptureSet n k) :
    (C1 ∪ C2).weaken = C1.weaken ∪ C2.weaken := by
  simp [CaptureSet.weaken]

/-! ## Cont.HasLabel weakening -/

/-- If a continuation has a label `x`, then its term-variable weakening
has the label `x.succ`. -/
lemma Cont.HasLabel.weaken
    {cont : Cont n m k} {x : Fin n} {tail : Cont n m k}
    (h : Cont.HasLabel cont x tail) :
    Cont.HasLabel cont.weaken x.succ tail.weaken := by
  induction h with
  | here => apply Cont.HasLabel.here
  | there_val _ ih => apply Cont.HasLabel.there_val; exact ih
  | there_tval _ ih => apply Cont.HasLabel.there_tval; exact ih
  | there_cval _ ih => apply Cont.HasLabel.there_cval; exact ih
  | there_label _ ih => apply Cont.HasLabel.there_label; exact ih

/-- If a continuation has a label `x`, then its type-variable weakening also has
label `x`. The index is unchanged because type-variable weakening (`tweaken`) only
extends the type context dimension `m`. -/
lemma Cont.HasLabel.tweaken
    {cont : Cont n m k} {x : Fin n} {tail : Cont n m k}
    (h : Cont.HasLabel cont x tail) :
    Cont.HasLabel cont.tweaken x tail.tweaken := by
  induction h with
  | here => simpa [Cont.tweaken] using Cont.HasLabel.here
  | there_val _ ih => simpa [Cont.tweaken] using Cont.HasLabel.there_val ih
  | there_tval _ ih => simpa [Cont.tweaken] using Cont.HasLabel.there_tval ih
  | there_cval _ ih => simpa [Cont.tweaken] using Cont.HasLabel.there_cval ih
  | there_label _ ih => simpa [Cont.tweaken] using Cont.HasLabel.there_label ih

/-- If a continuation has a label `x`, then its capture-variable weakening also has
label `x`. The index is unchanged because capture-variable weakening (`cweaken`) only
extends the capture context dimension `k`. -/
lemma Cont.HasLabel.cweaken
    {cont : Cont n m k} {x : Fin n} {tail : Cont n m k}
    (h : Cont.HasLabel cont x tail) :
    Cont.HasLabel cont.cweaken x tail.cweaken := by
  induction h with
  | here => simpa [Cont.cweaken] using Cont.HasLabel.here
  | there_val _ ih => simpa [Cont.cweaken] using Cont.HasLabel.there_val ih
  | there_tval _ ih => simpa [Cont.cweaken] using Cont.HasLabel.there_tval ih
  | there_cval _ ih => simpa [Cont.cweaken] using Cont.HasLabel.there_cval ih
  | there_label _ ih => simpa [Cont.cweaken] using Cont.HasLabel.there_label ih

/-! ## WellScoped weakening helper lemmas -/

/-- Weakening lemma for `WellScoped.singleton`: the singleton capture set
of a term variable stays well-scoped under term-variable context extension. -/
lemma WellScoped.weaken_singleton {n m k : ℕ}
    {Γ : Context n m k} {x : Fin n} {S : SType n m k} {C : CaptureSet n k}
    {cont : Cont n m k} {T : CType n m k}
    (hb : Context.Bound Γ x (S ^ C))
    (ih : WellScoped (Γ.var T) cont.weaken C.weaken) :
    WellScoped (Γ.var T) cont.weaken ((CaptureSet.singleton x).weaken) := by
  have hb' := Context.Bound.there_var (E' := T) hb
  simpa [CaptureSet.weaken, CType.weaken_capt] using
    WellScoped.singleton (S := S.weaken) (C := C.weaken)
      (by simpa [CType.weaken_capt] using hb') ih

/-- Weakening lemma for `WellScoped.csingleton`: the capture-variable singleton
stays well-scoped under term-variable context extension. -/
lemma WellScoped.weaken_csingleton {n m k : ℕ}
    {Γ : Context n m k} {c : Fin k} {C : CaptureSet n k}
    {cont : Cont n m k} {T : CType n m k}
    (hcb : Context.CBound Γ c (CBinding.inst C))
    (ih : WellScoped (Γ.var T) cont.weaken C.weaken) :
    WellScoped (Γ.var T) cont.weaken ((CaptureSet.csingleton c).weaken) := by
  have hcb' := Context.CBound.there_var (E := T) hcb
  simpa [CaptureSet.weaken, CBinding.weaken_inst] using
    WellScoped.csingleton (C := C.weaken)
      (by simpa [CBinding.weaken_inst] using hcb') ih

/-- Weakening lemma for `WellScoped.cbound`: a bounded capture-variable singleton
stays well-scoped under term-variable context extension. -/
lemma WellScoped.weaken_cbound {n m k : ℕ}
    {Γ : Context n m k} {c : Fin k} {C : CaptureSet n k}
    {cont : Cont n m k} {T : CType n m k}
    (hcb : Context.CBound Γ c (CBinding.bound (CBound.upper C)))
    (ih : WellScoped (Γ.var T) cont.weaken C.weaken) :
    WellScoped (Γ.var T) cont.weaken ((CaptureSet.csingleton c).weaken) := by
  have hcb' := Context.CBound.there_var (E := T) hcb
  simpa [CaptureSet.weaken, CBinding.weaken, CBinding.rename,
    CBound.weaken_upper, CBound.weaken, CBound.rename] using
    WellScoped.cbound (C := C.weaken)
      (by
        simpa [CBinding.weaken, CBinding.rename, CBound.weaken_upper,
          CBound.weaken, CBound.rename] using hcb')
      ih

/-- Weakening lemma for `WellScoped.label`: a label singleton stays well-scoped
under term-variable context extension. -/
lemma WellScoped.weaken_label {n m k : ℕ}
    {Γ : Context n m k} {x : Fin n} {S : SType n m k}
    {cont tail : Cont n m k} {T : CType n m k}
    (hlb : Context.LBound Γ x S)
    (hhl : Cont.HasLabel cont x tail) :
    WellScoped (Γ.var T) cont.weaken ((CaptureSet.singleton x).weaken) := by
  have hlb' := Context.LBound.there_var (E := T) hlb
  have hhl' := Cont.HasLabel.weaken hhl
  simpa [CaptureSet.weaken] using WellScoped.label hlb' hhl'

/-! ## Main Weakening Theorem -/

/-- Well-scoping of a capture set is preserved under term-variable
weakening of the context and continuation. -/
theorem WellScoped.weaken {n m k : ℕ}
    {Γ : Context n m k} {cont : Cont n m k} {Ct : CaptureSet n k}
    {T : CType n m k}
    (h : WellScoped Γ cont Ct) :
    WellScoped (Γ.var T) cont.weaken Ct.weaken := by
  induction h
  case empty => exact WellScoped.empty
  case union C1 C2 hC1 hC2 ih1 ih2 =>
    rw [CaptureSet.weaken_union C1 C2]
    exact WellScoped.union ih1 ih2
  case singleton x S C cont' hb hC ih =>
    exact WellScoped.weaken_singleton hb ih
  case csingleton c C cont' hcb hC ih =>
    exact WellScoped.weaken_csingleton hcb ih
  case cbound c C cont' hcb hC ih =>
    exact WellScoped.weaken_cbound hcb ih
  case label x S cont' tail hlb hhl =>
    exact WellScoped.weaken_label hlb hhl

/-! ## Type-Variable Weakening -/

/-- Well-scoping of a capture set is preserved under type-variable weakening:
extending the context with a type variable binding and weakening the continuation
accordingly preserves well-scoping. The capture set `Ct` is unchanged because
type-variable weakening only extends the type variable dimension `m`. -/
theorem WellScoped.tweaken {n m k : ℕ}
    {Γ : Context n m k} {cont : Cont n m k} {Ct : CaptureSet n k}
    {b : TBinding n m k}
    (h : WellScoped Γ cont Ct) :
    WellScoped (Γ.tvar b) cont.tweaken Ct := by
  induction h with
  | empty => exact WellScoped.empty
  | union _ _ ih₁ ih₂ => exact WellScoped.union ih₁ ih₂
  | singleton hb _ ih =>
    exact WellScoped.singleton (Context.Bound.there_tvar hb) ih
  | csingleton hcb _ ih =>
    exact WellScoped.csingleton (Context.CBound.there_tvar hcb) ih
  | cbound hcb _ ih =>
    exact WellScoped.cbound (Context.CBound.there_tvar hcb) ih
  | label hlb hhl =>
    exact WellScoped.label (Context.LBound.there_tvar hlb) (Cont.HasLabel.tweaken hhl)

/-! ## Context binding weakening lemmas -/

/-- If `x` is bound to `E` in `Γ`, then `x.succ` is bound to `E.weaken` in `Γ.var T_ext`. -/
lemma Context.Bound.weaken {Γ : Context n m k} {x : Fin n} {E : CType n m k}
    (h : Context.Bound Γ x E) (T_ext : CType n m k) :
    Context.Bound (Γ.var T_ext) x.succ E.weaken :=
  (VarMap.weaken (Γ := Γ) (T := T_ext)).map x E h

/-- If `x` has label binding `S` in `Γ`, then `x.succ` has label binding `S.weaken` in `Γ.var T_ext`. -/
lemma Context.LBound.weaken {Γ : Context n m k} {x : Fin n} {S : SType n m k}
    (h : Context.LBound Γ x S) (T_ext : CType n m k) :
    Context.LBound (Γ.var T_ext) x.succ S.weaken :=
  (VarMap.weaken (Γ := Γ) (T := T_ext)).lmap x S h

/-- If `X` has type binding `b` in `Γ`, then `X` has type binding `b.weaken` in `Γ.var T_ext`. -/
lemma Context.TBound.weaken {Γ : Context n m k} {X : Fin m} {b : TBinding n m k}
    (h : Context.TBound Γ X b) (T_ext : CType n m k) :
    Context.TBound (Γ.var T_ext) X (b.weaken) :=
  (VarMap.weaken (Γ := Γ) (T := T_ext)).tmap X b h

/-- If `c` has capture binding `b` in `Γ`, then `c` has capture binding `b.weaken` in `Γ.var T_ext`. -/
lemma Context.CBound.weaken {Γ : Context n m k} {c : Fin k} {b : CBinding n k}
    (h : Context.CBound Γ c b) (T_ext : CType n m k) :
    Context.CBound (Γ.var T_ext) c (b.weaken) :=
  (VarMap.weaken (Γ := Γ) (T := T_ext)).cmap c b h

end Capless
