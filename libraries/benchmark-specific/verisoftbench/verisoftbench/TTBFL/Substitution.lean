import src.typing

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-!
  # Substitution lemmas for the TTBFL type theory

  These theorems establish fundamental properties of the substitution
  operation, including composition identities, interactions with
  renaming and context lifting, preservation of typing (morphism),
  and preservation of definitional equality.
-/

/-- Extensionality for substitutions: if `σ` and `τ` agree on all variables,
    then `subst σ s = subst τ s` for all terms `s`. -/
theorem subst_ext (σ τ : Nat → Term) (h : ∀ n, σ n = τ n) : ∀ s, subst σ s = subst τ s := by
  intro s
  induction s generalizing σ τ with
  | var n => exact h n
  | 𝒰 a ih => simp [subst, ih σ τ h]
  | pi a b =>
    rename_i ih_a ih_b
    simp [subst, ih_a σ τ h]
    have h_up : ∀ n, (⇑ σ) n = (⇑ τ) n := by
      intro n; cases n <;> simp [up, h]
    simpa [up] using ih_b (⇑ σ) (⇑ τ) h_up
  | abs a b =>
    rename_i ih_a ih_b
    simp [subst, ih_a σ τ h]
    have h_up : ∀ n, (⇑ σ) n = (⇑ τ) n := by
      intro n; cases n <;> simp [up, h]
    simpa [up] using ih_b (⇑ σ) (⇑ τ) h_up
  | app b a =>
    rename_i ih_b ih_a
    simp [subst, ih_b σ τ h, ih_a σ τ h]
  | mty => simp
  | exf a b =>
    rename_i ih_a ih_b
    simp [subst, ih_a σ τ h, ih_b σ τ h]
  | lvl a ih => simp [subst, ih σ τ h]
  | lof k => simp

/-- Well-typed substitution predicate:
    `WSubst σ Γ Δ` means for all `x`, `A`, if `Γ ∋ x ∶ A` then `Δ ⊢ σ x ∶ subst σ A` -/
abbrev WSubst (σ : ℕ → Term) (Γ Δ : Ctxt) : Prop :=
  ∀ x A, Γ ∋ x ∶ A → Δ ⊢ σ x ∶ subst σ A

/-- Weakening for typing judgments (extracted from TTBFL safety module) -/
theorem wtWeaken_subst {Γ k} {a A B : Term}
    (hΓ : ⊢ Γ) (hB : Γ ⊢ B ∶ 𝒰 k) (h : Γ ⊢ a ∶ A) :
    Γ ∷ B ⊢ rename succ a ∶ rename succ A := by
  have rename_comp_local (ξ ζ : ℕ → ℕ) (t : Term) :
      rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
    induction t generalizing ξ ζ <;> simp_all only [rename]
    all_goals
      congr 1
    all_goals
      apply congrArg (fun f => rename f _)
      funext n
      cases n <;> rfl
  have rename_lift_succ (ξ : ℕ → ℕ) (t : Term) :
      rename (lift ξ) (rename succ t) = rename succ (rename ξ t) := by
    rw [rename_comp_local, rename_comp_local]
    rfl
  have rename_open_local (ξ : ℕ → ℕ) (a b : Term) :
      rename ξ (subst (a +: var) b) =
        subst (rename ξ a +: var) (rename (lift ξ) b) := by
    rw [renameSubst, substRename]
    congr 1
    funext n
    cases n <;> rfl
  have eqv_rename_local (ξ : ℕ → ℕ) {a b : Term} (h : a ≈ b) :
      rename ξ a ≈ rename ξ b := by
    induction h generalizing ξ with
    | β => simpa only [rename, rename_open_local] using (Eqv.β (b := rename (lift ξ) _) (a := rename ξ _) (c := rename ξ _))
    | refl => exact .refl
    | sym _ ih => exact .sym (ih ξ)
    | trans _ _ ih1 ih2 => exact .trans (ih1 ξ) (ih2 ξ)
    | 𝒰 _ ih => exact .𝒰 (ih ξ)
    | pi _ _ ih1 ih2 => exact .pi (ih1 ξ) (ih2 (lift ξ))
    | abs _ _ ih1 ih2 => exact .abs (ih1 ξ) (ih2 (lift ξ))
    | app _ _ ih1 ih2 => exact .app (ih1 ξ) (ih2 ξ)
    | exf _ _ ih1 ih2 => exact .exf (ih1 ξ) (ih2 ξ)
    | lvl _ ih => exact .lvl (ih ξ)
  have wRename_lift_local {ξ : ℕ → ℕ} {Γ Δ : Ctxt} {A : Term}
      (hξ : wRename ξ Γ Δ) : wRename (lift ξ) (Γ ∷ A) (Δ ∷ rename ξ A) := by
    intro x T hx
    cases hx with
    | here => simpa only [rename_lift_succ] using (In.here (Γ := Δ) (A := rename ξ A))
    | there hx => simpa only [rename_lift_succ] using In.there (hξ _ _ hx)
  have wt_rename_local {Γ : Ctxt} {a A : Term} (h : Γ ⊢ a ∶ A)
      {Δ : Ctxt} (hΔ : ⊢ Δ) (ξ : ℕ → ℕ) (hξ : wRename ξ Γ Δ) :
      Δ ⊢ rename ξ a ∶ rename ξ A := by
    induction h generalizing Δ ξ with
    | var _ mem => exact .var hΔ (hξ _ _ mem)
    | 𝒰 _ ih => exact .𝒰 (ih hΔ ξ hξ)
    | pi hA _ ihA ihB =>
      have hA' := ihA hΔ ξ hξ
      apply Wt.pi hA'
      simpa only [rename, rename_lift_succ] using ihB (.cons hΔ hA') (lift ξ) (wRename_lift_local hξ)
    | abs _ _ _ ihPi ihA ihB =>
      exact .abs (ihPi hΔ ξ hξ) (ihA hΔ ξ hξ)
        (ihB (.cons hΔ (ihA hΔ ξ hξ)) (lift ξ) (wRename_lift_local hξ))
    | app _ _ ihB ihA =>
      simpa only [rename, rename_open_local] using Wt.app (ihB hΔ ξ hξ) (ihA hΔ ξ hξ)
    | mty _ ih => exact .mty (ih hΔ ξ hξ)
    | exf _ _ ihA ihB => exact .exf (ihA hΔ ξ hξ) (ihB hΔ ξ hξ)
    | lvl _ _ ihA ihU => exact .lvl (ihA hΔ ξ hξ) (ihU hΔ ξ hξ)
    | lof _ hlt => exact .lof hΔ hlt
    | trans _ _ ih1 ih2 => exact .trans (ih1 hΔ ξ hξ) (ih2 hΔ ξ hξ)
    | conv heq _ _ ihA ihB => exact .conv (eqv_rename_local ξ heq) (ihA hΔ ξ hξ) (ihB hΔ ξ hξ)
    | sub _ _ ih1 ih2 => exact .sub (ih1 hΔ ξ hξ) (ih2 hΔ ξ hξ)
  exact wt_rename_local h (.cons hΓ hB) succ (fun _ _ hx => .there hx)

/-- Composition identity for lifted substitutions:
    `subst (subst σ a +: var) ∘ subst (⇑ σ) = subst σ ∘ subst (a +: var)` -/
theorem substUp_subst_cons_eq {σ : ℕ → Term} {a t : Term} :
    subst (subst σ a +: var) (subst (⇑ σ) t) = subst σ (subst (a +: var) t) := by
  have h1 : ∀ x, (subst σ ∘ (a +: var)) x = (subst σ a +: σ) x := by
    intro x; cases x <;> simp [cons]
  have h2 : ∀ x, (subst (subst σ a +: var) ∘ (⇑ σ)) x = (subst σ a +: σ) x := by
    intro x
    cases x with
    | zero => simp [cons, up]
    | succ n =>
      calc
        (subst (subst σ a +: var) ∘ (⇑ σ)) (succ n)
            = subst (subst σ a +: var) ((⇑ σ) (succ n)) := rfl
        _ = subst (subst σ a +: var) (rename succ (σ n)) := rfl
        _ = subst ((subst σ a +: var) ∘ succ) (σ n) := by
          simpa using substRename succ (subst σ a +: var) (σ n)
        _ = subst var (σ n) := by
          have h_comp : ((subst σ a +: var) ∘ succ) = var := by
            funext x; simp
          rw [h_comp]
        _ = σ n := by simpa using substId (σ n)
        _ = (subst σ a +: σ) (succ n) := by simp
  have h_eq1 := substComp' σ (a +: var) (subst σ a +: σ) h1
  have h_eq2 := substComp' (subst σ a +: var) (⇑ σ) (subst σ a +: σ) h2
  calc
    subst (subst σ a +: var) (subst (⇑ σ) t)
        = subst (subst σ a +: σ) t := by
      simpa using h_eq2 t
    _ = subst σ (subst (a +: var) t) := by
      simpa using (h_eq1 t).symm

/-- `subst (⇑ σ)` commutes with `rename succ` over a `subst σ` -/
theorem substUp_rename_subst_eq {σ : ℕ → Term} (A : Term) :
    subst (⇑ σ) (rename succ A) = rename succ (subst σ A) := by
  have h_comp : (⇑ σ) ∘ succ = rename succ ∘ σ := by
    funext x; simp [up, Function.comp]
  calc
    subst (⇑ σ) (rename succ A) = subst ((⇑ σ) ∘ succ) A := by
      simpa using substRename succ (⇑ σ) A
    _ = subst (rename succ ∘ σ) A := by rw [h_comp]
    _ = rename succ (subst σ A) := by
      simpa using (renameSubst succ σ A).symm

/-- Lifting a well-typed substitution under a context extension -/
theorem wSubstUp_helper {σ : ℕ → Term} {Γ Δ : Ctxt} {A K : Term}
    (hσ : WSubst σ Γ Δ) (hΔ : ⊢ Δ) (hA_type : Δ ⊢ subst σ A ∶ 𝒰 K) :
    WSubst (⇑ σ) (Γ ∷ A) (Δ ∷ subst σ A) := by
  intro x T mem'
  cases x with
  | zero =>
    cases mem' with
    | here =>
      have hwf : ⊢ Δ ∷ subst σ A := Wf.cons hΔ hA_type
      have hvar0 : (⇑ σ) 0 = var 0 := by simp
      have heq : subst (⇑ σ) (rename succ A) = rename succ (subst σ A) :=
        substUp_rename_subst_eq A
      rw [hvar0, heq]
      exact Wt.var hwf (In.here (Γ := Δ) (A := subst σ A))
  | succ n =>
    cases mem' with
    | there mem'' =>
      rename_i T'
      have hmem := hσ n T' mem''
      have h_weaken : (Δ ∷ subst σ A) ⊢ rename succ (σ n) ∶
          rename succ (subst σ T') :=
        wtWeaken_subst hΔ hA_type hmem
      have hvar_succ : (⇑ σ) (succ n) = rename succ (σ n) := by simp
      have heq : subst (⇑ σ) (rename succ T') = rename succ (subst σ T') :=
        substUp_rename_subst_eq T'
      rw [hvar_succ, heq]
      exact h_weaken

/-- Substitution preserves definitional equality -/
theorem substEqv (σ : ℕ → Term) {a b : Term} (h : a ≈ b) : subst σ a ≈ subst σ b := by
  match h with
  | Eqv.refl => apply Eqv.refl
  | Eqv.sym h' => exact Eqv.sym (substEqv σ h')
  | Eqv.trans h1 h2 => exact Eqv.trans (substEqv σ h1) (substEqv σ h2)
  | @Eqv.β _ b a c =>
    simp [subst]
    have h_β : app (abs (subst σ c) (subst (⇑ σ) b)) (subst σ a) ≈
        subst (subst σ a +: var) (subst (⇑ σ) b) := Eqv.β
    have h_eq : subst (subst σ a +: var) (subst (⇑ σ) b) =
        subst σ (subst (a +: var) b) := substUp_subst_cons_eq (t := b)
    exact h_eq ▸ h_β
  | Eqv.𝒰 h' => simp [subst]; apply Eqv.𝒰; apply substEqv σ h'
  | Eqv.pi h1 h2 => simp [subst]; apply Eqv.pi; apply substEqv σ h1; apply substEqv (⇑ σ) h2
  | Eqv.abs h1 h2 =>
    simp [subst]; apply Eqv.abs; apply substEqv σ h1; apply substEqv (⇑ σ) h2
  | Eqv.app h1 h2 => simp [subst]; apply Eqv.app; apply substEqv σ h1; apply substEqv σ h2
  | Eqv.exf h1 h2 => simp [subst]; apply Eqv.exf; apply substEqv σ h1; apply substEqv σ h2
  | Eqv.lvl h' => simp [subst]; apply Eqv.lvl; apply substEqv σ h'

/-- Typing morphism: substitution preserves typing -/
theorem wtMorph_1 {σ : ℕ → Term} {Γ Δ} {a A : Term}
    (hσ : WSubst σ Γ Δ) (hΔ : ⊢ Δ) (h : Γ ⊢ a ∶ A) :
    Δ ⊢ subst σ a ∶ subst σ A := by
  induction h generalizing Δ σ with
  | var hΓ' mem =>
    exact hσ _ _ mem
  | 𝒰 h' ih =>
    simp [subst]; apply Wt.𝒰; apply ih hσ hΔ
  | @pi Γ' A' B' k' hA hB ihA ihB =>
    simp [subst]
    apply Wt.pi
    · apply ihA hσ hΔ
    · have hA_type : Δ ⊢ subst σ A' ∶ 𝒰 (subst σ k') := by
        simpa [subst] using ihA hσ hΔ
      have hσ_up : WSubst (⇑ σ) (Γ' ∷ A') (Δ ∷ subst σ A') :=
        wSubstUp_helper hσ hΔ hA_type
      have hwf' : ⊢ Δ ∷ subst σ A' := Wf.cons hΔ hA_type
      have hB' : (Δ ∷ subst σ A') ⊢ subst (⇑ σ) B' ∶
          subst (⇑ σ) (𝒰 (rename succ k')) :=
        ihB (σ := ⇑ σ) (Δ := Δ ∷ subst σ A') hσ_up hwf'
      have hB'_simp : (Δ ∷ subst σ A') ⊢ subst (⇑ σ) B' ∶
          𝒰 (subst (⇑ σ) (rename succ k')) := by
        simpa [subst] using hB'
      have h_rhs_eq : 𝒰 (subst (⇑ σ) (rename succ k')) =
          𝒰 (rename succ (subst σ k')) := by
        rw [substUp_rename_subst_eq k']
      exact h_rhs_eq ▸ hB'_simp
  | @abs Γ' A' B' b' k' hpi hA hb ih_pi ih_A ih_b =>
    simp [subst]
    apply Wt.abs
    · apply ih_pi hσ hΔ
    · apply ih_A hσ hΔ
    · have hA_type : Δ ⊢ subst σ A' ∶ 𝒰 (subst σ k') := by
        simpa [subst] using ih_A hσ hΔ
      have hσ_up : WSubst (⇑ σ) (Γ' ∷ A') (Δ ∷ subst σ A') :=
        wSubstUp_helper hσ hΔ hA_type
      have hwf' : ⊢ Δ ∷ subst σ A' := Wf.cons hΔ hA_type
      have hb' : (Δ ∷ subst σ A') ⊢ subst (⇑ σ) b' ∶ subst (⇑ σ) B' :=
        ih_b (σ := ⇑ σ) (Δ := Δ ∷ subst σ A') hσ_up hwf'
      simpa [subst] using hb'
  | @app Γ' A' B' b' a' hb ha ih_b ih_a =>
    have hb' : Δ ⊢ subst σ b' ∶ pi (subst σ A') (subst (⇑ σ) B') := by
      simpa [subst] using ih_b hσ hΔ
    have ha' : Δ ⊢ subst σ a' ∶ subst σ A' := by
      simpa [subst] using ih_a hσ hΔ
    have happ : Δ ⊢ app (subst σ b') (subst σ a') ∶
        subst (subst σ a' +: var) (subst (⇑ σ) B') :=
      Wt.app hb' ha'
    have h_eq : subst (subst σ a' +: var) (subst (⇑ σ) B') =
        subst σ (subst (a' +: var) B') :=
      substUp_subst_cons_eq (t := B')
    exact h_eq ▸ happ
  | mty h' ih =>
    simp [subst]; apply Wt.mty; apply ih hσ hΔ
  | exf hA hb ih_A ih_b =>
    simp [subst]; apply Wt.exf; apply ih_A hσ hΔ; apply ih_b hσ hΔ
  | lvl ha hU ih_a ih_U =>
    simp [subst]; apply Wt.lvl; apply ih_a hσ hΔ; apply ih_U hσ hΔ
  | @lof _ j k hΓ' hlt ih =>
    simp [subst]; apply Wt.lof hΔ hlt
  | trans hi hj ih_i ih_j =>
    simp [subst]; apply Wt.trans; apply ih_i hσ hΔ; apply ih_j hσ hΔ
  | @conv _ A' B' a' k' heq ha hB ih_a ih_B =>
    have ha' : Δ ⊢ subst σ a' ∶ subst σ A' := ih_a hσ hΔ
    have hB' : Δ ⊢ subst σ B' ∶ 𝒰 (subst σ k') := by
      simpa [subst] using ih_B hσ hΔ
    apply Wt.conv
    · exact substEqv σ heq
    · exact ha'
    · exact hB'
  | @sub _ j k A' hj hA ih_j ih_A =>
    simp [subst]; apply Wt.sub; apply ih_j hσ hΔ; apply ih_A hσ hΔ

/-!
  # Fundamental substitution lemmas

  These theorems establish the algebraic properties of substitution:
  identity, composition, interaction with cons, and lifting.
-/

/-- The up-lifted identity substitution is pointwise equal to `var`. -/
lemma up_var_eq_var : ∀ x, (⇑ (var : ℕ → Term)) x = var x := by
  intro n; cases n <;> simp [up]

/-- Substituting with `var` is the identity: `subst var s = s`. -/
theorem subst_id : ∀ s, subst var s = s := by
  intro s
  induction s with
  | var n => simp
  | 𝒰 a iha => simp only [subst]; rw [iha]
  | pi a b iha ihb =>
    simp only [subst]
    rw [iha, subst_ext (⇑ (var : ℕ → Term)) var up_var_eq_var b, ihb]
  | abs a b iha ihb =>
    simp only [subst]
    rw [iha, subst_ext (⇑ (var : ℕ → Term)) var up_var_eq_var b, ihb]
  | app a b iha ihb => simp only [subst]; rw [iha, ihb]
  | mty => simp
  | exf a b iha ihb => simp only [subst]; rw [iha, ihb]
  | lvl a iha => simp only [subst]; rw [iha]
  | lof k => simp

/-- Substituting with the lifted identity substitution is also the identity:
    `subst (⇑ var) s = s`. -/
theorem subst_up_var_eq_var (s : Term) : subst (⇑ var) s = s := by
  calc
    subst (⇑ var) s = subst var s := subst_ext (⇑ var) var up_var_eq_var s
    _ = s := subst_id s

/-- Lifting commutes with substitution composition at the pointwise level:
    if `subst ρ ∘ σ = τ` pointwise, then `subst (⇑ ρ) ∘ (⇑ σ) = ⇑ τ` pointwise. -/
theorem up_subst (ρ σ τ : ℕ → Term) (h : ∀ x, (subst ρ ∘ σ) x = τ x) :
    ∀ x, (subst (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Function.comp_apply]
    have h_sigma : (⇑ σ) (succ n) = rename succ (σ n) := by simp [up]
    have h_tau : (⇑ τ) (succ n) = rename succ (τ n) := by simp [up]
    rw [h_sigma, h_tau]
    rw [substUp_rename_subst_eq (σ := ρ) (A := σ n)]
    simpa [Function.comp_apply] using congrArg (rename succ) (h n)

/-- Substitution composition: `subst σ (subst τ s) = subst (subst σ ∘ τ) s`. -/
theorem subst_comp (σ τ : ℕ → Term) : ∀ s, (subst σ ∘ subst τ) s = subst (subst σ ∘ τ) s := by
  intro s
  induction s generalizing σ τ with
  | var n => simp
  | 𝒰 a iha => simpa [subst, Function.comp_apply] using congrArg 𝒰 (iha σ τ)
  | pi a b iha ihb =>
    simp only [subst, Function.comp_apply]
    apply congrArg₂ pi
    · simpa [Function.comp_apply] using iha σ τ
    · calc
        subst (⇑ σ) (subst (⇑ τ) b) = (subst (⇑ σ) ∘ subst (⇑ τ)) b := rfl
        _ = subst (subst (⇑ σ) ∘ (⇑ τ)) b := ihb (⇑ σ) (⇑ τ)
        _ = subst (⇑ (subst σ ∘ τ)) b := by
          have h_up := up_subst σ τ (subst σ ∘ τ) (by intro x; rfl)
          rw [subst_ext (subst (⇑ σ) ∘ ⇑ τ) (⇑ (subst σ ∘ τ)) h_up b]
  | abs a b iha ihb =>
    simp only [subst, Function.comp_apply]
    apply congrArg₂ abs
    · simpa [Function.comp_apply] using iha σ τ
    · calc
        subst (⇑ σ) (subst (⇑ τ) b) = (subst (⇑ σ) ∘ subst (⇑ τ)) b := rfl
        _ = subst (subst (⇑ σ) ∘ (⇑ τ)) b := ihb (⇑ σ) (⇑ τ)
        _ = subst (⇑ (subst σ ∘ τ)) b := by
          have h_up := up_subst σ τ (subst σ ∘ τ) (by intro x; rfl)
          rw [subst_ext (subst (⇑ σ) ∘ ⇑ τ) (⇑ (subst σ ∘ τ)) h_up b]
  | app a b iha ihb =>
    simpa [subst, Function.comp_apply] using congrArg₂ app (iha σ τ) (ihb σ τ)
  | mty => simp
  | exf a b iha ihb =>
    simpa [subst, Function.comp_apply] using congrArg₂ exf (iha σ τ) (ihb σ τ)
  | lvl a iha => simpa [subst, Function.comp_apply] using congrArg lvl (iha σ τ)
  | lof k => simp

/-- Commutation of lifted substitutions on a term:
    `subst (⇑ σ) (subst (⇑ τ) b) = subst (⇑ (subst σ ∘ τ)) b`. -/
lemma subst_up_up_comp (σ τ : ℕ → Term) (b : Term) :
    subst (⇑ σ) (subst (⇑ τ) b) = subst (⇑ (subst σ ∘ τ)) b := by
  calc
    subst (⇑ σ) (subst (⇑ τ) b) = (subst (⇑ σ) ∘ subst (⇑ τ)) b := rfl
    _ = subst (subst (⇑ σ) ∘ (⇑ τ)) b := by rw [subst_comp (⇑ σ) (⇑ τ) b]
    _ = subst (⇑ (subst σ ∘ τ)) b := by
      have h_up := up_subst σ τ (subst σ ∘ τ) (by intro x; rfl)
      rw [subst_ext (subst (⇑ σ) ∘ ⇑ τ) (⇑ (subst σ ∘ τ)) h_up b]

/-- Under substitution, `var ∘ lift ξ` and `⇑ (var ∘ ξ)` produce equal results.
    Follows from `upVar`. -/
theorem subst_var_lift_eq_subst_up_var (ξ : ℕ → ℕ) (s : Term) :
    subst (var ∘ lift ξ) s = subst (⇑ (var ∘ ξ)) s :=
  subst_ext (var ∘ lift ξ) (⇑ (var ∘ ξ)) (upVar ξ) s

/-- Decomposing a composite substitution: `subst (subst σ ∘ τ) s` equals
    applying `τ` then `σ`. This is the reverse direction of `subst_comp`. -/
theorem subst_comp_decomp (σ τ : ℕ → Term) (s : Term) :
    subst (subst σ ∘ τ) s = subst σ (subst τ s) :=
  (subst_comp σ τ s).symm

/-- Substituting `(a +: σ)` after a `succ`-rename cancels the head,
    leaving `subst σ`. Generalizes `subst_cons_rename_succ_eq` to any tail substitution. -/
theorem subst_cons_succ (a : Term) (σ : ℕ → Term) (t : Term) :
    subst (a +: σ) (rename succ t) = subst σ t := by
  calc
    subst (a +: σ) (rename succ t) = subst ((a +: σ) ∘ succ) t := by
      simpa using substRename succ (a +: σ) t
    _ = subst σ t := by
      apply subst_ext ((a +: σ) ∘ succ) σ ?_ t
      intro x; simp

/-- Pointwise equality connecting `subst (subst σ a +: var) ∘ (⇑ σ)` and
    `subst σ ∘ (a +: var)`. Used as a building block for commutation lemmas. -/
lemma subst_cons_up_pointwise_eq (σ : ℕ → Term) (a : Term) (x : ℕ) :
    (subst (subst σ a +: var) ∘ (⇑ σ)) x = (subst σ ∘ (a +: var)) x := by
  cases x with
  | zero => simp
  | succ n =>
    simp
    rw [subst_cons_succ (subst σ a) var (σ n), subst_id (σ n)]

/-- Substituting with `(a +: var)` after `rename succ` recovers the original term:
    `subst (a +: var) (rename succ b) = b`. -/
theorem subst_cons_rename_succ_eq (a b : Term) : b = subst (a +: var) (rename succ b) := by
  have h_rename := substRename succ (a +: var) b
  rw [h_rename]
  have h : ∀ x, ((a +: var) ∘ succ) x = var x := by
    intro n; simp
  rw [subst_ext ((a +: var) ∘ succ) var h b]
  exact (subst_id b).symm

/-- Pointwise equality relating `(a +: σ)` and `(subst (a +: var) ∘ ⇑ σ)`. -/
lemma subst_cons_pointwise_eq (a : Term) (σ : ℕ → Term) (x : ℕ) :
    (a +: σ) x = (subst (a +: var) ∘ (⇑ σ)) x := by
  cases x with
  | zero => simp
  | succ n => simpa using subst_cons_rename_succ_eq a (σ n)

/-- Substitution over a cons distributes:
    `subst (a +: σ) s = subst (a +: var) (subst (⇑ σ) s)`. -/
theorem subst_cons_distrib (σ : ℕ → Term) (a s : Term) :
    subst (a +: σ) s = subst (a +: var) (subst (⇑ σ) s) := by
  calc
    subst (a +: σ) s
        = subst (subst (a +: var) ∘ (⇑ σ)) s := by
      rw [subst_ext (a +: σ) (subst (a +: var) ∘ (⇑ σ)) (subst_cons_pointwise_eq a σ) s]
    _ = (subst (a +: var) ∘ subst (⇑ σ)) s := by
      rw [← subst_comp (a +: var) (⇑ σ) s]
    _ = subst (a +: var) (subst (⇑ σ) s) := rfl
