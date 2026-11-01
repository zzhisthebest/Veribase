import src.typing
import verisoftbench.TTBFL.Reduction

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false
set_option linter.unusedSectionVars false

variable [LevelClass]

/-!
  # Typing inversion and regularity lemmas for the TTBFL type theory

  These theorems establish fundamental properties of the typing judgment
  (`Wt`), including inversion lemmas for universe constructors and the
  regularity theorem (every well-typed term's type is well-typed at a universe level).
-/

/-- In any `Preorder` with `NoMaxOrder`, given an element `k`,
    there exist `l` and `m` such that `k < l` and `l < m`. -/
lemma exists_gt_two {α} [Preorder α] [NoMaxOrder α] (k : α) : ∃ l m : α, k < l ∧ l < m := by
  have ⟨l, hkl⟩ := exists_gt k
  have ⟨m, hlm⟩ := exists_gt l
  exact ⟨l, m, hkl, hlm⟩

/-- Inversion lemma for `lvl`: if `lvl a` is well-typed at type `A`,
    then `a` is well-typed at some `lvl b`. -/
lemma wt_lvl_inv {Γ a A} (h : Γ ⊢ lvl a ∶ A) : ∃ b, Γ ⊢ a ∶ lvl b := by
  generalize h_eq : lvl a = t at h
  induction h generalizing a
  case var hΓ mem ih_wf => injection h_eq
  case 𝒰 hj ih => injection h_eq
  case pi hA hB ihA ihB => injection h_eq
  case abs hpi hA hb ihpi ihA ihb => injection h_eq
  case app hb ha ihb iha => injection h_eq
  case mty hU ih => injection h_eq
  case exf hA hb ihA ihb => injection h_eq
  case lvl ha hUj iha ihUj =>
    injection h_eq with eq_a
    subst eq_a
    exact ⟨_, ha⟩
  case lof hΓ hlt ih_wf => injection h_eq
  case trans hi hj ihi ihj => exact ihi h_eq
  case conv heq h_inner h_U ih_inner ih_U => exact ih_inner h_eq
  case sub hj h_inner ihj ih_inner => exact ih_inner h_eq

/-- Inversion lemma for `lvl`: if `lvl a` is well-typed at type `A`,
    then `a` is well-typed at some `lvl b` and `A` is convertible to `𝒰 k` for some `k`. -/
lemma wt_lvl_inv' {Γ a A} (h : Γ ⊢ lvl a ∶ A) : ∃ b k, Γ ⊢ a ∶ lvl b ∧ 𝒰 k ≈ A := by
  have join_step {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction r generalizing c with
    | refl => exact ⟨c, .trans s (.refl _), .refl _⟩
    | trans r _ ih =>
      obtain ⟨e, re, se⟩ := diamond r s
      obtain ⟨d, bd, ed⟩ := ih re
      exact ⟨d, bd, .trans se ed⟩
  have join_steps {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒⋆ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction s generalizing b with
    | refl => exact ⟨b, .refl _, r⟩
    | trans s _ ih =>
      obtain ⟨e, be, ce⟩ := join_step r s
      obtain ⟨d, ed, cd⟩ := ih ce
      exact ⟨d, pars_trans be ed, cd⟩
  have conv_map_local (f : Term → Term)
      (hf : ∀ {a b}, a ⇒ b → f a ⇒ f b) {a b} (h : a ⇔ b) : f a ⇔ f b := by
    obtain ⟨c, ac, bc⟩ := h
    exact ⟨f c, pars_map f hf ac, pars_map f hf bc⟩
  have conv_binary_local (f : Term → Term → Term)
      (hf : ∀ {a b c d}, a ⇒ b → c ⇒ d → f a c ⇒ f b d)
      {a b c d} (h1 : a ⇔ b) (h2 : c ⇔ d) : f a c ⇔ f b d := by
    obtain ⟨e, ae, be⟩ := h1
    obtain ⟨g, cg, dg⟩ := h2
    exact ⟨f e g,
      pars_trans (pars_map (fun x => f x c) (fun h => hf h (parRefl _)) ae)
        (pars_map (f e) (fun h => hf (parRefl _) h) cg),
      pars_trans (pars_map (fun x => f x d) (fun h => hf h (parRefl _)) be)
        (pars_map (f e) (fun h => hf (parRefl _) h) dg)⟩
  have eqv_conv_local {a b : Term} (h : a ≈ b) : a ⇔ b := by
    induction h with
    | β => exact ⟨_, .trans (.β (parRefl _) (parRefl _)) (.refl _), .refl _⟩
    | refl => exact ⟨_, .refl _, .refl _⟩
    | sym _ ih => obtain ⟨c, ac, bc⟩ := ih; exact ⟨c, bc, ac⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨c, ac, bc⟩ := ih1
      obtain ⟨d, bd, ed⟩ := ih2
      obtain ⟨f, cf, df⟩ := join_steps bc bd
      exact ⟨f, pars_trans ac cf, pars_trans ed df⟩
    | 𝒰 _ ih => exact conv_map_local 𝒰 Par.𝒰 ih
    | lvl _ ih => exact conv_map_local lvl Par.lvl ih
    | pi _ _ ih1 ih2 => exact conv_binary_local pi Par.pi ih1 ih2
    | abs _ _ ih1 ih2 => exact conv_binary_local abs Par.abs ih1 ih2
    | app _ _ ih1 ih2 => exact conv_binary_local app Par.app ih1 ih2
    | exf _ _ ih1 ih2 => exact conv_binary_local exf Par.exf ih1 ih2
  let canonical_tag : Term → ℕ := fun
    | .𝒰 _ => 1
    | .pi _ _ => 2
    | .lvl _ => 3
    | _ => 0
  have par_tag {a b : Term} (r : a ⇒ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    cases r <;> simp_all [canonical_tag]
  have pars_tag {a b : Term} (r : a ⇒⋆ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    induction r with
    | refl => rfl
    | trans r _ ih =>
      have e := par_tag r h
      exact (ih (by simpa [e] using h)).trans e
  have eqv_tag {a b : Term} (h : a ≈ b)
      (ha : canonical_tag a ≠ 0) (hb : canonical_tag b ≠ 0) :
      canonical_tag a = canonical_tag b := by
    obtain ⟨c, ac, bc⟩ := eqv_conv_local h
    exact (pars_tag ac ha).symm.trans (pars_tag bc hb)
  generalize he : lvl a = t at h
  induction h generalizing a
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case lvl => exact ⟨_, _, by assumption, .refl⟩
  case trans ih =>
    obtain ⟨_, _, _, e⟩ := ih
    have := eqv_tag e (by simp [canonical_tag]) (by simp [canonical_tag])
    simp [canonical_tag] at this
  case conv e _ _ _ ih =>
    obtain ⟨b, k, ha, hk⟩ := ih
    exact ⟨b, k, ha, .trans hk e⟩
  case sub ih =>
    obtain ⟨b, _, ha, _⟩ := ih
    exact ⟨b, _, ha, .refl⟩

/-- Inversion lemma for `pi`: if `pi A B` is well-typed at type `U`,
    then `A` is well-typed at some universe level and `B` (under `Γ ∷ A`)
    is well-typed at some universe level. -/
lemma wt_pi_inv {Γ A B U} (h : Γ ⊢ pi A B ∶ U) : (∃ k, Γ ⊢ A ∶ 𝒰 k) ∧ (∃ k, Γ ∷ A ⊢ B ∶ 𝒰 k) := by
  generalize h_eq : pi A B = t at h
  induction h generalizing A B
  case var hΓ mem ih_wf => injection h_eq
  case 𝒰 hj ih => injection h_eq
  case pi hA hB ihA ihB =>
    injection h_eq with eq_A eq_B
    subst eq_A; subst eq_B
    exact ⟨⟨_, hA⟩, ⟨_, hB⟩⟩
  case abs hpi hA hb ihpi ihA ihb => injection h_eq
  case app hb ha ihb iha => injection h_eq
  case mty hU ih => injection h_eq
  case exf hA hb ihA ihb => injection h_eq
  case lvl ha hUj iha ihUj => injection h_eq
  case lof hΓ hlt ih_wf => injection h_eq
  case trans hi hj ihi ihj => exact ihi h_eq
  case conv heq h_inner h_U ih_inner ih_U => exact ih_inner h_eq
  case sub hj h_inner ihj ih_inner => exact ih_inner h_eq

/-- Typing lemma for `lvl (lof k)` at `𝒰 (lof l)`, given `k < l < m`. -/
lemma wt_lvl_lof {Γ} (hΓ : ⊢ Γ) {k l m : LevelClass.L} (hkl : k < l) (hlm : l < m) :
    Γ ⊢ lvl (lof k) ∶ 𝒰 (lof l) := by
  apply Wt.lvl (Wt.lof hΓ hkl)
  apply Wt.𝒰 (Wt.lof hΓ hlm)

/-- If `lvl a` is well-typed at `A`, then `𝒰 a` is well-typed at some `𝒰 b`. -/
lemma wt_univ_of_lvl {Γ a A} (h : Γ ⊢ lvl a ∶ A) : ∃ b, Γ ⊢ 𝒰 a ∶ 𝒰 b := by
  let ⟨b, hk⟩ := wt_lvl_inv h
  exact ⟨b, Wt.𝒰 hk⟩

/-- Inversion lemma for `mty`: if `mty` is well-typed at type `A`,
    then `A` is convertible to `𝒰 k` for some `k`. -/
lemma wt_mty_inv {Γ A} (h : Γ ⊢ mty ∶ A) : ∃ k, 𝒰 k ≈ A := by
  have join_step {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction r generalizing c with
    | refl => exact ⟨c, .trans s (.refl _), .refl _⟩
    | trans r _ ih =>
      obtain ⟨e, re, se⟩ := diamond r s
      obtain ⟨d, bd, ed⟩ := ih re
      exact ⟨d, bd, .trans se ed⟩
  have join_steps {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒⋆ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction s generalizing b with
    | refl => exact ⟨b, .refl _, r⟩
    | trans s _ ih =>
      obtain ⟨e, be, ce⟩ := join_step r s
      obtain ⟨d, ed, cd⟩ := ih ce
      exact ⟨d, pars_trans be ed, cd⟩
  have conv_map_local (f : Term → Term)
      (hf : ∀ {a b}, a ⇒ b → f a ⇒ f b) {a b} (h : a ⇔ b) : f a ⇔ f b := by
    obtain ⟨c, ac, bc⟩ := h
    exact ⟨f c, pars_map f hf ac, pars_map f hf bc⟩
  have conv_binary_local (f : Term → Term → Term)
      (hf : ∀ {a b c d}, a ⇒ b → c ⇒ d → f a c ⇒ f b d)
      {a b c d} (h1 : a ⇔ b) (h2 : c ⇔ d) : f a c ⇔ f b d := by
    obtain ⟨e, ae, be⟩ := h1
    obtain ⟨g, cg, dg⟩ := h2
    exact ⟨f e g,
      pars_trans (pars_map (fun x => f x c) (fun h => hf h (parRefl _)) ae)
        (pars_map (f e) (fun h => hf (parRefl _) h) cg),
      pars_trans (pars_map (fun x => f x d) (fun h => hf h (parRefl _)) be)
        (pars_map (f e) (fun h => hf (parRefl _) h) dg)⟩
  have eqv_conv_local {a b : Term} (h : a ≈ b) : a ⇔ b := by
    induction h with
    | β => exact ⟨_, .trans (.β (parRefl _) (parRefl _)) (.refl _), .refl _⟩
    | refl => exact ⟨_, .refl _, .refl _⟩
    | sym _ ih => obtain ⟨c, ac, bc⟩ := ih; exact ⟨c, bc, ac⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨c, ac, bc⟩ := ih1
      obtain ⟨d, bd, ed⟩ := ih2
      obtain ⟨f, cf, df⟩ := join_steps bc bd
      exact ⟨f, pars_trans ac cf, pars_trans ed df⟩
    | 𝒰 _ ih => exact conv_map_local 𝒰 Par.𝒰 ih
    | lvl _ ih => exact conv_map_local lvl Par.lvl ih
    | pi _ _ ih1 ih2 => exact conv_binary_local pi Par.pi ih1 ih2
    | abs _ _ ih1 ih2 => exact conv_binary_local abs Par.abs ih1 ih2
    | app _ _ ih1 ih2 => exact conv_binary_local app Par.app ih1 ih2
    | exf _ _ ih1 ih2 => exact conv_binary_local exf Par.exf ih1 ih2
  let canonical_tag : Term → ℕ := fun
    | .𝒰 _ => 1
    | .pi _ _ => 2
    | .lvl _ => 3
    | _ => 0
  have par_tag {a b : Term} (r : a ⇒ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    cases r <;> simp_all [canonical_tag]
  have pars_tag {a b : Term} (r : a ⇒⋆ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    induction r with
    | refl => rfl
    | trans r _ ih =>
      have e := par_tag r h
      exact (ih (by simpa [e] using h)).trans e
  have eqv_tag {a b : Term} (h : a ≈ b)
      (ha : canonical_tag a ≠ 0) (hb : canonical_tag b ≠ 0) :
      canonical_tag a = canonical_tag b := by
    obtain ⟨c, ac, bc⟩ := eqv_conv_local h
    exact (pars_tag ac ha).symm.trans (pars_tag bc hb)
  generalize hd : mty = t at h
  induction h
  case var hΓ mem => injection hd
  case 𝒰 hj ih => injection hd
  case pi hA hB ihA ihB => injection hd
  case abs hpi hA hb ihpi ihA ihb => injection hd
  case app hb ha ihb iha => injection hd
  case mty hU ih =>
    injection hd
    exact ⟨_, Eqv.refl⟩
  case exf hA hb ihA ihb => injection hd
  case lvl ha hUj iha ihUj => injection hd
  case lof hΓ hlt => injection hd
  case trans hi hj ihi ihj =>
    -- If `t` equals `mty`, then the premise `hi : Γ ⊢ t ∶ lvl j` would give
    -- `Γ ⊢ mty ∶ lvl j`. Can `mty` be typed at `lvl j`? Only through
    -- `conv`/`sub`/`trans`, which would require `𝒰 X ≈ lvl j` for some `X`,
    -- impossible by structural properties of `Eqv`. Thus this case is impossible.
    obtain ⟨k, hk⟩ := ihi hd
    have := eqv_tag hk (by simp [canonical_tag]) (by simp [canonical_tag])
    simp [canonical_tag] at this
  case conv heq h_inner h_U ih_inner ih_U =>
    let ⟨k, hk⟩ := ih_inner hd
    exact ⟨k, Eqv.trans hk heq⟩
  case sub hj h_inner ihj ih_inner =>
    -- `sub` changes the type index from `𝒰 j` to `𝒰 k`.
    -- The conclusion `Γ ⊢ t ∶ 𝒰 k` means the original `A` is `𝒰 k`,
    -- so we can directly provide `k` as the witness.
    exact ⟨_, Eqv.refl⟩

/-- (Restated from `src.safety`) Weakening for typing judgments -/
theorem wtWeaken {Γ k} {a A B : Term}
    (hΓ : ⊢ Γ) (hB : Γ ⊢ B ∶ 𝒰 k) (h : Γ ⊢ a ∶ A) :
    Γ ∷ B ⊢ rename succ a ∶ rename succ A := by
  exact wtWeaken_subst hΓ hB h

/-- (Restated from `src.safety`) Well-typed lookup implies well-typed type -/
theorem wtMem {Γ x A} (mem : Γ ∋ x ∶ A) (h : ⊢ Γ) : ∃ k, Γ ⊢ A ∶ 𝒰 k := by
  induction mem
  case here =>
    cases h with
    | cons hΓ hB =>
      exact ⟨rename succ _, wtWeaken hΓ hB hB⟩
  case there ih =>
    cases h with
    | cons hΓ hB =>
      let ⟨k, hA⟩ := ih hΓ
      exact ⟨rename succ k, wtWeaken hΓ hB hA⟩

/-- (Restated from `src.safety`) Substitution preserves typing -/
theorem wtSubst {Γ} {a A b B : Term}
    (hb : Γ ⊢ b ∶ B) (h : Γ ∷ B ⊢ a ∶ A) :
    Γ ⊢ subst (b +: var) a ∶ subst (b +: var) A := by
  have hΓ : ⊢ Γ := by
    clear h
    induction hb <;> assumption
  apply wtMorph_1 (hΔ := hΓ) (h := h)
  intro x T hx
  cases hx with
  | here => simpa [← subst_cons_rename_succ_eq] using hb
  | there hx =>
    simpa [← subst_cons_rename_succ_eq] using Wt.var hΓ hx

/-- Regularity: every well-typed term has a well-typed type.
    If `Γ ⊢ a ∶ A`, then there exists a level `k` such that `Γ ⊢ A ∶ 𝒰 k`. -/
theorem wt_regularity {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : ∃ k, Γ ⊢ A ∶ 𝒰 k := by
  induction h
  case var hΓ mem ih_wf => exact wtMem mem hΓ
  case 𝒰 hj ih =>
    let ⟨k, h_lvl⟩ := ih
    exact wt_univ_of_lvl h_lvl
  case pi hA hB ihA ihB => exact ihA
  case abs hpi hA hb ihpi ihA ihb => exact ⟨_, hpi⟩
  case app a_arg hb ha ihb iha =>
    let ⟨k, h_pi⟩ := ihb
    let ⟨k', h_B⟩ := (wt_pi_inv h_pi).right
    refine ⟨subst (a_arg +: var) k', ?_⟩
    simpa using wtSubst ha h_B
  case mty hU ih => exact ⟨_, hU⟩
  case exf hA hb ihA ihb => exact ⟨_, hA⟩
  case lvl ha hUj iha ihUj => exact ⟨_, hUj⟩
  case lof j k hΓ hlt ih_wf =>
    let ⟨l, m, hkl, hlm⟩ := exists_gt_two k
    exact ⟨lof l, wt_lvl_lof hΓ hkl hlm⟩
  case trans hi hj ihi ihj => exact ihj
  case conv heq ha hB iha ihB => exact ⟨_, hB⟩
  case sub hj hA ihj ihA =>
    let ⟨k, h_lvl⟩ := ihj
    exact wt_univ_of_lvl h_lvl

/-- Inversion lemma for `abs`: if `abs A' b` is well-typed at type `C`,
    then there exist types `A` and `B` such that `Γ ∷ A ⊢ b ∶ B`,
    `A ≈ A'`, and `pi A B ≈ C`. -/
lemma wt_abs_inv {Γ A' b C} (h : Γ ⊢ abs A' b ∶ C) :
    ∃ A B, Γ ∷ A ⊢ b ∶ B ∧ A ≈ A' ∧ pi A B ≈ C := by
  have join_step {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction r generalizing c with
    | refl => exact ⟨c, .trans s (.refl _), .refl _⟩
    | trans r _ ih =>
      obtain ⟨e, re, se⟩ := diamond r s
      obtain ⟨d, bd, ed⟩ := ih re
      exact ⟨d, bd, .trans se ed⟩
  have join_steps {a b c : Term} (r : a ⇒⋆ b) (s : a ⇒⋆ c) :
      ∃ d, b ⇒⋆ d ∧ c ⇒⋆ d := by
    induction s generalizing b with
    | refl => exact ⟨b, .refl _, r⟩
    | trans s _ ih =>
      obtain ⟨e, be, ce⟩ := join_step r s
      obtain ⟨d, ed, cd⟩ := ih ce
      exact ⟨d, pars_trans be ed, cd⟩
  have conv_map_local (f : Term → Term)
      (hf : ∀ {a b}, a ⇒ b → f a ⇒ f b) {a b} (h : a ⇔ b) : f a ⇔ f b := by
    obtain ⟨c, ac, bc⟩ := h
    exact ⟨f c, pars_map f hf ac, pars_map f hf bc⟩
  have conv_binary_local (f : Term → Term → Term)
      (hf : ∀ {a b c d}, a ⇒ b → c ⇒ d → f a c ⇒ f b d)
      {a b c d} (h1 : a ⇔ b) (h2 : c ⇔ d) : f a c ⇔ f b d := by
    obtain ⟨e, ae, be⟩ := h1
    obtain ⟨g, cg, dg⟩ := h2
    exact ⟨f e g,
      pars_trans (pars_map (fun x => f x c) (fun h => hf h (parRefl _)) ae)
        (pars_map (f e) (fun h => hf (parRefl _) h) cg),
      pars_trans (pars_map (fun x => f x d) (fun h => hf h (parRefl _)) be)
        (pars_map (f e) (fun h => hf (parRefl _) h) dg)⟩
  have eqv_conv_local {a b : Term} (h : a ≈ b) : a ⇔ b := by
    induction h with
    | β => exact ⟨_, .trans (.β (parRefl _) (parRefl _)) (.refl _), .refl _⟩
    | refl => exact ⟨_, .refl _, .refl _⟩
    | sym _ ih => obtain ⟨c, ac, bc⟩ := ih; exact ⟨c, bc, ac⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨c, ac, bc⟩ := ih1
      obtain ⟨d, bd, ed⟩ := ih2
      obtain ⟨f, cf, df⟩ := join_steps bc bd
      exact ⟨f, pars_trans ac cf, pars_trans ed df⟩
    | 𝒰 _ ih => exact conv_map_local 𝒰 Par.𝒰 ih
    | lvl _ ih => exact conv_map_local lvl Par.lvl ih
    | pi _ _ ih1 ih2 => exact conv_binary_local pi Par.pi ih1 ih2
    | abs _ _ ih1 ih2 => exact conv_binary_local abs Par.abs ih1 ih2
    | app _ _ ih1 ih2 => exact conv_binary_local app Par.app ih1 ih2
    | exf _ _ ih1 ih2 => exact conv_binary_local exf Par.exf ih1 ih2
  let canonical_tag : Term → ℕ := fun
    | .𝒰 _ => 1
    | .pi _ _ => 2
    | .lvl _ => 3
    | _ => 0
  have par_tag {a b : Term} (r : a ⇒ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    cases r <;> simp_all [canonical_tag]
  have pars_tag {a b : Term} (r : a ⇒⋆ b) (h : canonical_tag a ≠ 0) :
      canonical_tag b = canonical_tag a := by
    induction r with
    | refl => rfl
    | trans r _ ih =>
      have e := par_tag r h
      exact (ih (by simpa [e] using h)).trans e
  have eqv_tag {a b : Term} (h : a ≈ b)
      (ha : canonical_tag a ≠ 0) (hb : canonical_tag b ≠ 0) :
      canonical_tag a = canonical_tag b := by
    obtain ⟨c, ac, bc⟩ := eqv_conv_local h
    exact (pars_tag ac ha).symm.trans (pars_tag bc hb)
  generalize he : abs A' b = t at h
  induction h
  all_goals injections <;> subst_eqs <;> specialize_rfls
  case abs hb _ => exact ⟨_, _, hb, .refl, .refl⟩
  case trans ih =>
    obtain ⟨_, _, _, _, e⟩ := ih
    have := eqv_tag e (by simp [canonical_tag]) (by simp [canonical_tag])
    simp [canonical_tag] at this
  case conv e _ _ _ ih =>
    obtain ⟨A, B, hb, hA, hB⟩ := ih
    exact ⟨A, B, hb, hA, .trans hB e⟩
  case sub ih =>
    obtain ⟨_, _, _, _, e⟩ := ih
    have := eqv_tag e (by simp [canonical_tag]) (by simp [canonical_tag])
    simp [canonical_tag] at this
