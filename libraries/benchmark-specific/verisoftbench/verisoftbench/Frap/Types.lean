import Frap.Types

/-!
# Type Safety for TM (Typed Arithmetic/Boolean Expressions)

Theorems about the `TM` language from `Frap.Types` (the typed language of booleans and
natural numbers from Software Foundations' _Programming Language Foundations_).

These theorems collectively prove the progress property: a well-typed term either is a
value or can take a step.  The main theorem is `progress`; the others are helper lemmas
that decompose the inductive cases.
-/

namespace TM

open Tm
open BValue
open NValue
open Step
open Ty
open HasType

/--
When `prd` is applied to a numeric value, it can take a step.
-/
theorem pred_nvalue_step {v : Tm} (hn : NValue v) : ∃ t', Step (prd v) t' := by
  cases hn with
  | nv_0 => exact ⟨zro, Step.st_pred0⟩
  | nv_succ _ hn' => exact ⟨_, Step.st_predSucc _ hn'⟩

/--
When `iszero` is applied to a numeric value, it can take a step.
-/
theorem iszero_nvalue_step {v : Tm} (hn : NValue v) : ∃ t', Step (iszero v) t' := by
  cases hn with
  | nv_0 => exact ⟨tru, Step.st_iszero0⟩
  | nv_succ _ hn' => exact ⟨fls, Step.st_iszeroSucc _ hn'⟩

/--
When the condition of an `ite` is a boolean value, the whole expression can take a step.
-/
theorem if_bvalue_step {t₁ t₂ t₃ : Tm} (hb : BValue t₁) : ∃ t', Step (ite t₁ t₂ t₃) t' := by
  rcases hb with (htrue | hfalse)
  · exact ⟨t₂, Step.st_ifTrue t₂ t₃⟩
  · exact ⟨t₃, Step.st_ifFalse t₂ t₃⟩

/--
Progress lemma for `scc` (successor) expressions.
-/
theorem progress_succ {t : Tm} (h : HasType t nat) (progress_t : value t ∨ ∃ t', Step t t') :
    value (scc t) ∨ ∃ t', Step (scc t) t' := by
  rcases progress_t with (hv | ⟨t', hstep⟩)
  · have hn : NValue t := nat_canonical t h hv
    exact Or.inl (Or.inr (NValue.nv_succ t hn))
  · exact Or.inr ⟨scc t', Step.st_succ t t' hstep⟩

/--
Progress lemma for `prd` (predecessor) expressions.
-/
theorem progress_pred {t : Tm} (h : HasType t nat) (progress_t : value t ∨ ∃ t', Step t t') :
    value (prd t) ∨ ∃ t', Step (prd t) t' := by
  rcases progress_t with (hv | ⟨t', hstep⟩)
  · have hn : NValue t := nat_canonical t h hv
    have hstep' : ∃ t'', Step (prd t) t'' := pred_nvalue_step hn
    exact Or.inr hstep'
  · exact Or.inr ⟨prd t', Step.st_pred t t' hstep⟩

/--
Progress lemma for `iszero` expressions.
-/
theorem progress_iszero {t : Tm} (h : HasType t nat) (progress_t : value t ∨ ∃ t', Step t t') :
    value (iszero t) ∨ ∃ t', Step (iszero t) t' := by
  rcases progress_t with (hv | ⟨t', hstep⟩)
  · have hn : NValue t := nat_canonical t h hv
    have hstep' : ∃ t'', Step (iszero t) t'' := iszero_nvalue_step hn
    exact Or.inr hstep'
  · exact Or.inr ⟨iszero t', Step.st_iszero t t' hstep⟩

/--
Progress lemma for `ite` (if-then-else) expressions.
-/
theorem progress_if {t₁ t₂ t₃ : Tm} (h1 : HasType t₁ bool)
    (progress_t₁ : value t₁ ∨ ∃ t', Step t₁ t') :
    value (ite t₁ t₂ t₃) ∨ ∃ t', Step (ite t₁ t₂ t₃) t' := by
  rcases progress_t₁ with (hv | ⟨t', hstep⟩)
  · have hb : BValue t₁ := bool_canonical t₁ h1 hv
    have hstep' : ∃ t'', Step (ite t₁ t₂ t₃) t'' := if_bvalue_step hb
    exact Or.inr hstep'
  · exact Or.inr ⟨ite t' t₂ t₃, Step.st_if t₁ t' t₂ t₃ hstep⟩

/--
**Progress**: If `t` has type `T`, then either `t` is a value or `t` can take a step.

This is one of the two fundamental properties of a type system (the other being
`preservation`).  Together they establish type soundness: well-typed terms never
get stuck.
-/
theorem progress (t : Tm) (T : Ty) : HasType t T → value t ∨ ∃ t', Step t t' := by
  intro ht
  induction ht with
  | t_true => exact Or.inl (Or.inl BValue.bv_true)
  | t_false => exact Or.inl (Or.inl BValue.bv_false)
  | t_0 => exact Or.inl (Or.inr NValue.nv_0)
  | t_succ _ h ih => exact progress_succ h ih
  | t_pred _ h ih => exact progress_pred h ih
  | t_iszero _ h ih => exact progress_iszero h ih
  | t_if _ _ _ _ h1 _ _ ih => exact progress_if h1 ih

  /--
  **Progress (not stuck)**: A well-typed term is never stuck.
  -/
  theorem progress_not_stuck (t : Tm) (T : Ty) (ht : HasType t T) : ¬ stuck t := by
    unfold stuck step_normal_form normal_form
    intro ⟨hnf, hnv⟩
    rcases progress t T ht with (hv | hstep)
    · exact hnv hv
    · exact hnf hstep

  /--
  **Multistep preservation**: If `t` is well-typed at `T` and `t` reduces to `t'` in zero
  or more steps, then `t'` is also well-typed at `T`.

  This lifts the single-step `preservation` theorem to the reflexive-transitive closure
  `multistep` (a.k.a. `Multi Step`).
  -/
  theorem multistep_preservation (t t' : Tm) (T : Ty)
      (ht : HasType t T) (hm : multistep t t') : HasType t' T := by
    revert ht
    induction hm generalizing T with
    | multi_refl => exact id
    | multi_step _ u _ hStep hMult' ih =>
      intro hT
      have hT_u : HasType u T := preservation _ _ T hT hStep
      apply ih
      exact hT_u

  /--
  **Type soundness**: If a well-typed term `t` can take zero or more steps to `t'`,
  then `t'` is not stuck.

  This follows directly from `multistep_preservation` and `progress_not_stuck` and
  is the fundamental type-safety guarantee of the TM language.
  -/
  theorem soundness (t t' : Tm) (T : Ty)
      (ht : HasType t T) (hm : multistep t t') : ¬ stuck t' := by
    have hT' : HasType t' T := multistep_preservation t t' T ht hm
    exact progress_not_stuck t' T hT'

end TM
