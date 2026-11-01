import Capless.Subcapturing
import Capless.Subtyping
import Capless.Weakening.Subcapturing

/-!
# Basic Properties of Subtyping and Subcapturing

Reflexivity and transitivity for the subcapturing (`Subcapt`) and subtyping
(`CSubtyp`, `ESubtyp`) relations of System Capless. These are foundational
properties expected of any subtyping relation.
-/

namespace Capless

/-! ## Subcapturing properties -/

/-- Subcapt is reflexive: `Γ ⊢ C <:c C` for any capture set `C`. -/
lemma Subcapt.refl (C : CaptureSet n k) : Subcapt Γ C C :=
  Subcapt.subset CaptureSet.Subset.rfl

/-- Combined capture-variable and term-variable weakening for subcapturing. -/
lemma Subcapt.cweaken_weaken {C1 C2 : CaptureSet n k}
    (h : Subcapt Γ C1 C2) : Subcapt ((Γ.cvar B).var T) (C1.cweaken.weaken) (C2.cweaken.weaken) :=
  Subcapt.weaken (Subcapt.cweaken h)

/-! ## CSubtyp properties -/

/-- CSubtyp is reflexive: `Γ ⊢ T <: T` for any `CType`. -/
lemma CSubtyp.refl (T : CType n m k) : CSubtyp Γ T T := by
  cases T
  case capt C S =>
    apply CSubtyp.capt
    · exact Subcapt.refl C
    · exact SSubtyp.refl

/-- CSubtyp is transitive. -/
lemma CSubtyp.trans {T1 T2 T3 : CType n m k}
    (h1 : CSubtyp Γ T1 T2) (h2 : CSubtyp Γ T2 T3) : CSubtyp Γ T1 T3 := by
  cases h1
  case capt hsc1 hs1 =>
    cases h2
    case capt hsc2 hs2 =>
      apply CSubtyp.capt
      · exact Subcapt.trans hsc1 hsc2
      · exact SSubtyp.trans hs1 hs2

/-! ## ESubtyp properties -/

/-- ESubtyp is reflexive: `Γ ⊢ E <:e E` for any `EType`. -/
lemma ESubtyp.refl (E : EType n m k) : ESubtyp Γ E E := by
  cases E
  case ex T =>
    apply ESubtyp.exist
    exact CSubtyp.refl T
  case type T =>
    apply ESubtyp.type
    exact CSubtyp.refl T

/-- ESubtyp is transitive. -/
lemma ESubtyp.trans {E1 E2 E3 : EType n m k}
    (h1 : ESubtyp Γ E1 E2) (h2 : ESubtyp Γ E2 E3) : ESubtyp Γ E1 E3 := by
  cases h1
  case exist hc1 =>
    cases h2
    case exist hc2 =>
      apply ESubtyp.exist
      exact CSubtyp.trans hc1 hc2
  case type hc1 =>
    cases h2
    case type hc2 =>
      apply ESubtyp.type
      exact CSubtyp.trans hc1 hc2

/-- Combine `ESubtyp.trans` with an `And` on the left: if `P` holds and `E1 <:e E2`,
    and also `E2 <:e E3`, then `P` still holds and `E1 <:e E3`. -/
lemma ESubtyp.trans_and {P : Prop} {E1 E2 E3 : EType n m k}
    (h : P ∧ ESubtyp Γ E1 E2) (hs : ESubtyp Γ E2 E3) : P ∧ ESubtyp Γ E1 E3 :=
  ⟨h.1, ESubtyp.trans h.2 hs⟩

/-! ## Inversion lemmas -/

/-- Inversion lemma for `CSubtyp` where the right-hand side is a concrete `CType.capt`.
    Extracts the subcapturing and `SSubtyp` judgments. -/
theorem CSubtyp.capt_inv_right {n m k : Nat} {Γ : Context n m k} {T1 : CType n m k}
    {C2 : CaptureSet n k} {S2 : SType n m k}
    (h : CSubtyp Γ T1 (CType.capt C2 S2)) :
    ∃ (C1 : CaptureSet n k) (S1 : SType n m k),
    T1 = CType.capt C1 S1 ∧ Subcapt Γ C1 C2 ∧ SSubtyp Γ S1 S2 := by
  cases h
  case capt hc hs => exact ⟨_, _, rfl, hc, hs⟩

/-- Inversion lemma for existential subtyping targeting a type.
    If `E <:ₑ EType.type T`, then `E` must also be of the form `EType.type T'`
    for some `T'` with `T' <: T`. -/
theorem ESubtyp.type_inv {n m k : Nat} {Γ : Context n m k} {E : EType n m k} {T : CType n m k}
    (h : ESubtyp Γ E (EType.type T)) :
    ∃ (T' : CType n m k), E = EType.type T' ∧ CSubtyp Γ T' T := by
  cases h
  case type hc => exact ⟨_, rfl, hc⟩

end Capless
