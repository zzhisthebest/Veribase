import Capless.Store
import Capless.Subcapturing
import Capless.CaptureSet
import Capless.Context

/-!
# Basic Properties of Well-Scoped Capture Sets

Properties of the `WellScoped` predicate from System Capless, including
closure under subcapturing.
-/

namespace Capless

/-! ## Determinism of Context CBound Lookups -/

/--
Lookup of a capture variable binding is deterministic:
if both `h1` and `h2` are derivations of `Context.CBound Γ c b`,
then `b1 = b2`.
-/
theorem Context.cbound_injective {Γ : Context n m k} {c : Fin k} {b1 b2 : CBinding n k}
    (h1 : Context.CBound Γ c b1) (h2 : Context.CBound Γ c b2) : b1 = b2 := by
  have cbound_succ_inv {n m k : Nat} {Γ : Context n m k}
      {p : CBinding n k} {Γ0 : Context n m (k + 1)}
      {x0 : Fin (k + 1)} {x : Fin k} {b : CBinding n (k + 1)}
      (he1 : Γ0 = Γ.cvar p) (he2 : x0 = Fin.succ x)
      (hb : Context.CBound Γ0 x0 b) :
      ∃ b0, Context.CBound Γ x b0 ∧ b = b0.cweaken := by
    cases hb <;> try (solve | cases he1 | cases he2)
    case there_cvar hb0 =>
      rw [Fin.succ_inj] at he2
      cases he1
      subst he2
      exact ⟨_, hb0, rfl⟩
  induction h1 with
  | here => cases h2; rfl
  | there_var h ih => cases h2; congr 1; exact ih ‹_›
  | there_tvar h ih => cases h2; exact ih ‹_›
  | there_cvar h ih =>
    obtain ⟨b, hb, rfl⟩ := cbound_succ_inv rfl rfl h2
    rw [ih hb]
  | there_label h ih => cases h2; congr 1; exact ih ‹_›

/--
Injectivity for `CBinding.inst`: if both lookups give `CBinding.inst`,
then the capture sets are equal.
-/
lemma Context.cbound_inst_inj {Γ : Context n m k} {c : Fin k} {C1 C2 : CaptureSet n k}
    (h1 : Context.CBound Γ c (CBinding.inst C1))
    (h2 : Context.CBound Γ c (CBinding.inst C2)) : C1 = C2 := by
  have h := Context.cbound_injective h1 h2
  injection h

/-! ## Closure under Subset -/

/--
A subset of a well-scoped capture set is also well-scoped.
-/
lemma well_scoped_of_subset {C' C : CaptureSet n k} (hsub : C' ⊆ C)
    (hsc : WellScoped Γ cont C) : WellScoped Γ cont C' := by
  induction hsub with
  | empty => exact WellScoped.empty
  | rfl => exact hsc
  | union_l h1 h2 ih1 ih2 =>
    exact WellScoped.union (ih1 hsc) (ih2 hsc)
  | union_rl h1 ih =>
    cases hsc
    case union hsc1 _hsc2 =>
      exact ih hsc1
  | union_rr h2 ih =>
    cases hsc
    case union _hsc1 hsc2 =>
      exact ih hsc2

/-! ## Closure under Continuation Extension -/

/--
If a capture set is well-scoped, pushing a `Cont.cons` frame
(an unevaluated term `t` in the body of a `letin`) preserves well-scoping.
-/
lemma WellScoped.cons
    (h : WellScoped Γ cont C) :
    WellScoped Γ (Cont.cons t cont) C := by
  induction h with
  | empty => exact WellScoped.empty
  | union h1 h2 ih1 ih2 => exact WellScoped.union (ih1) (ih2)
  | singleton hb h ih => exact WellScoped.singleton hb (ih)
  | csingleton hb h ih => exact WellScoped.csingleton hb (ih)
  | cbound hb h ih => exact WellScoped.cbound hb (ih)
  | label hl hlabel => exact WellScoped.label hl (Cont.HasLabel.there_val hlabel)

/--
If a capture set is well-scoped, pushing a `Cont.conse` frame
(an unevaluated term `t` existentially binding a capture variable)
preserves well-scoping.
-/
lemma WellScoped.conse
    (h : WellScoped Γ cont C) :
    WellScoped Γ (Cont.conse t cont) C := by
  induction h with
  | empty => exact WellScoped.empty
  | union h1 h2 ih1 ih2 => exact WellScoped.union (ih1) (ih2)
  | singleton hb h ih => exact WellScoped.singleton hb (ih)
  | csingleton hb h ih => exact WellScoped.csingleton hb (ih)
  | cbound hb h ih => exact WellScoped.cbound hb (ih)
  | label hl hlabel => exact WellScoped.label hl (Cont.HasLabel.there_tval hlabel)

/--
If a capture set is well-scoped, pushing a `Cont.scope` frame
(introducing a label scope) preserves well-scoping.
-/
lemma WellScoped.scope
    (h : WellScoped Γ cont C) :
    WellScoped Γ (Cont.scope l cont) C := by
  induction h with
  | empty => exact WellScoped.empty
  | union h1 h2 ih1 ih2 => exact WellScoped.union (ih1) (ih2)
  | singleton hb h ih => exact WellScoped.singleton hb (ih)
  | csingleton hb h ih => exact WellScoped.csingleton hb (ih)
  | cbound hb h ih => exact WellScoped.cbound hb (ih)
  | label hl hlabel => exact WellScoped.label hl (Cont.HasLabel.there_label hlabel)

/-! ## Closure under Subcapturing -/

/--
Well-scopedness is downward-closed under subcapturing:
if `C` is well-scoped and `C'` is a subcapture of `C` (`Γ ⊢ C' <:c C`),
then `C'` is also well-scoped.
-/
theorem WellScoped.subcapt
    (hsc : WellScoped Γ cont C)
    (hs : Γ ⊢ C' <:c C) :
    WellScoped Γ cont C' := by
  induction hs with
  | trans h1 h2 ih1 ih2 =>
    exact ih1 (ih2 hsc)
  | subset h_sub =>
    exact well_scoped_of_subset h_sub hsc
  | union h1 h2 ih1 ih2 =>
    have hsc1 := ih1 hsc
    have hsc2 := ih2 hsc
    exact WellScoped.union hsc1 hsc2
  | var hb =>
    exact WellScoped.singleton hb hsc
  | cinstl hcb =>
    -- hcb : Context.CBound Γ c (CBinding.inst C')
    -- hsc : WellScoped Γ cont {c=c}
    -- goal: WellScoped Γ cont C'
    -- Relies on CBound determinism; see Context.cbound_inst_inj
    cases hsc with
    | csingleton hb hw =>
      have he := Context.cbound_inst_inj hcb hb
      subst he
      exact hw
    | cbound hb hw =>
      have he := Context.cbound_injective hcb hb
      cases he
  | cinstr hcb =>
    exact WellScoped.csingleton hcb hsc
  | cbound hcb =>
    exact WellScoped.cbound hcb hsc

/-! ## Type-variable weakening -/

/--
Type-variable weakening for `WellScoped`: if `WellScoped Γ cont Ct`,
then `WellScoped (Γ.tvar b) cont.tweaken Ct`.

Note that the capture set `Ct` does not change under type-variable weakening since
`CaptureSet n k` does not depend on the number of type variables (`m`).
-/
theorem WellScoped.tweaken {Γ : Context n m k} {cont : Cont n m k}
    {Ct : CaptureSet n k} (b : TBinding n m k)
    (h : WellScoped Γ cont Ct) :
    WellScoped (Γ.tvar b) cont.tweaken Ct := by
  induction h with
  | empty => exact WellScoped.empty
  | union h1 h2 ih1 ih2 =>
    apply WellScoped.union
    · exact ih1
    · exact ih2
  | singleton hb hw ih =>
    apply WellScoped.singleton
    · simpa [CType.tweaken, CType.trename] using Context.Bound.there_tvar hb
    · exact ih
  | csingleton hb hw ih =>
    apply WellScoped.csingleton
    · apply Context.CBound.there_tvar hb
    · exact ih
  | cbound hb hw ih =>
    apply WellScoped.cbound
    · apply Context.CBound.there_tvar hb
    · exact ih
  | label hb hl =>
    have liftLabel {cont : Cont n m k} {x : Fin n} {tail : Cont n m k}
        (h : Cont.HasLabel cont x tail) : Cont.HasLabel cont.tweaken x tail.tweaken := by
      induction h with
      | here => exact Cont.HasLabel.here
      | there_val h ih => exact Cont.HasLabel.there_val ih
      | there_tval h ih => exact Cont.HasLabel.there_tval ih
      | there_cval h ih => exact Cont.HasLabel.there_cval ih
      | there_label h ih => exact Cont.HasLabel.there_label ih
    exact WellScoped.label (Context.LBound.there_tvar hb) (liftLabel hl)

end Capless
