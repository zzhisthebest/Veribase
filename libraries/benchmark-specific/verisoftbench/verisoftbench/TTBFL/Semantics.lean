import src.semantics
import verisoftbench.TTBFL.Reduction

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-!
  # Semantics of the TTBFL type theory: interpretation lemmas
-/

/-- Forward preservation of interpretation: if `a ⇒ b` and `⟦a⟧ ↘ P`, then `⟦b⟧ ↘ P`. -/
theorem interpFwd {i I a b P} (r : a ⇒ b) (h : ⟦ a ⟧ i , I ↘ P) : ⟦ b ⟧ i , I ↘ P := by
  induction h generalizing b with
  | pi a body Pa Pf ha hPf hb iha ihb =>
    cases r with
    | pi ra rb =>
      apply Interp.pi _ _ Pa Pf (iha ra) hPf
      intro x Pb hx
      exact ihb x Pb hx (parSubst (fun n => parRefl _) rb)
  | 𝒰 j lt => cases r with | 𝒰 r => cases r; exact .𝒰 j lt
  | mty => cases r; exact .mty
  | lvl k => cases r with | lvl r => cases r; exact .lvl k
  | step a c P s hc ih =>
    obtain ⟨d, cd, bd⟩ := diamond s r
    exact .step _ _ _ bd (ih cd)

/-- Inversion lemma for `lvl`. -/
theorem interpLvlInv {i I a P} (h : ⟦ lvl a ⟧ i , I ↘ P) :
    ∃ k, a ⇒⋆ lof k ∧ P = (λ a ↦ ∃ j, a ⇒⋆ lof j ∧ j < k) := by
  generalize e : lvl a = c at h
  induction h generalizing a
  case lvl k =>
    injection e with e; subst e
    exact ⟨k, Pars.refl _, rfl⟩
  case step r _ ih =>
    subst e; cases r
    rename_i r1 h'
    let ⟨k, r2, e2⟩ := ih rfl
    refine ⟨k, Pars.trans r1 r2, e2⟩
  all_goals contradiction

/-- Determinism of interpretation: if `⟦a⟧ ↘ P` and `⟦a⟧ ↘ Q`, then `P = Q`. -/
theorem interpDet'_1 {i I a P Q} (hP : ⟦ a ⟧ i , I ↘ P) (hQ : ⟦ a ⟧ i , I ↘ Q) : P = Q := by
  have interp_pi_inv_local {i I a b P} (h : ⟦ pi a b ⟧ i , I ↘ P) :
      ∃ (Pa : Term → Prop) (Pf : Term → (Term → Prop) → Prop),
        (⟦ a ⟧ i , I ↘ Pa) ∧
        (∀ x, Pa x → ∃ Pb, Pf x Pb) ∧
        (∀ x Pb, Pf x Pb → ⟦ subst (x +: var) b ⟧ i, I ↘ Pb) ∧
        P = (fun f => ∀ x Pb, Pa x → Pf x Pb → Pb (app f x)) := by
    generalize he : pi a b = t at h
    induction h generalizing a b with
    | pi a' b' Pa Pf ha hPf hb _ _ =>
      cases he
      exact ⟨Pa, Pf, ha, hPf, hb, rfl⟩
    | step t c P r hc ih =>
      subst t
      cases r with
      | pi ra rb =>
        obtain ⟨Pa, Pf, ha, hPf, hb, e⟩ := ih rfl
        exact ⟨Pa, Pf, .step _ _ _ ra ha, hPf,
          fun x Pb hx => .step _ _ _ (parSubst (fun _ => parRefl _) rb) (hb x Pb hx), e⟩
    | 𝒰 => cases he
    | mty => cases he
    | lvl => cases he
  induction hP generalizing Q with
  | pi a b Pa Pf ha hPf hb iha ihb =>
    obtain ⟨Pa', Pf', ha', hPf', hb', rfl⟩ := interp_pi_inv_local hQ
    have e : Pa = Pa' := iha ha'
    subst Pa'
    funext f
    apply propext
    constructor
    · intro h x Pb hx hp
      obtain ⟨Pb', hp'⟩ := hPf x hx
      have e : Pb' = Pb := ihb x Pb' hp' (hb' x Pb hp)
      subst Pb'
      exact h x Pb hx hp'
    · intro h x Pb hx hp
      obtain ⟨Pb', hp'⟩ := hPf' x hx
      have e : Pb = Pb' := ihb x Pb hp (hb' x Pb' hp')
      subst Pb'
      exact h x Pb hx hp'
  | 𝒰 j lt =>
    obtain ⟨j', lt', r, e⟩ := interp𝒰Inv hQ
    have hj := parsLofInv r
    cases hj
    exact e.symm
  | mty => exact (interpMtyInv hQ).symm
  | lvl k =>
    obtain ⟨k', r, e⟩ := interpLvlInv hQ
    have hk := parsLofInv r
    cases hk
    exact e.symm
  | step a b P r hb ih => exact ih (interpFwd r hQ)

/-!
  # Multi-step backward interpretation lemmas
-/

/-- Backward preservation of interpretation under multi-step parallel reduction:
if `a ⇒⋆ b` and `⟦b⟧ ↘ P`, then `⟦a⟧ ↘ P`. -/
theorem interpsBwds {i a b P} (r : a ⇒⋆ b) (h : ⟦ b ⟧ i ↘ P) : ⟦ a ⟧ i ↘ P :=
  pars_backward (α := Term → Prop) (R := λ a' P' => ⟦ a' ⟧ i ↘ P')
    (λ r h => interpsBwd r h) r h

/-- If `⟦a⟧ ↘ P` and `x ⇒⋆ y`, then the interpretation predicate `P` is backward-closed
under multi-step reduction: `P y` implies `P x`. -/
theorem interps_pred_backward {i a x y P} (r : x ⇒⋆ y) (h : ⟦ a ⟧ i ↘ P) : P y → P x := by
  have one_step {i I a P} (h : ⟦ a ⟧ i , I ↘ P)
      (hI : ∀ j lt x y, x ⇒ y → I j lt y → I j lt x) :
      ∀ x y, x ⇒ y → P y → P x := by
    induction h with
    | pi a b Pa Pf ha hPf hb iha ihb =>
      intro x y r hy z Pb hz hp
      exact ihb z Pb hp (app x z) (app y z)
        (by exact Par.app r (parRefl z)) (hy z Pb hz hp)
    | 𝒰 j lt => exact hI j lt
    | mty => intro _ _ _ h; exact h
    | lvl k =>
      intro x y r hy
      obtain ⟨j, rj, hj⟩ := hy
      exact ⟨j, .trans r rj, hj⟩
    | step _ _ _ _ _ ih => exact ih
  have closed : ∀ x y, x ⇒ y → P y → P x := by
    unfold Interps at h
    apply one_step h
    intro j lt x y r hy
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨Q, interpsBwd r hQ⟩
  induction r with
  | refl => exact id
  | trans r _ ih => exact fun hy => closed _ _ r (ih hy)
