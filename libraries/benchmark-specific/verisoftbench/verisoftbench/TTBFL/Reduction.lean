import src.reduction
import verisoftbench.TTBFL.Substitution

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [LevelClass]

/-!
  # Renaming and substitution commutation lemmas for parallel reduction

  These theorems establish fundamental properties of renaming and substitution
  with respect to parallel reduction (`Par`) in the TTBFL type theory.

  Includes:
  - Renaming-substitution commutation with `cons`/`lift`
  - Renaming preserves the `Par` relation
  - Anti-renaming: `rename ξ a ⇒ b'` implies existence of `b` such
    that `b' = rename ξ b` and `a ⇒ b`
-/

section Rename

/-- Renaming distributes over cons with var:
    `rename ξ ∘ (a +: var) = (rename ξ a +: var) ∘ lift ξ` -/
lemma rename_cons_var_eq {ξ : ℕ → ℕ} {a : Term} :
    rename ξ ∘ (a +: var) = (rename ξ a +: var) ∘ lift ξ := by
  ext n; cases n <;> simp

/-- Renaming distributes over substitution into cons:
    `rename ξ (subst (a +: var) b) = subst (rename ξ a +: var) (rename (lift ξ) b)` -/
lemma rename_subst_cons {ξ : ℕ → ℕ} {a b : Term} :
    rename ξ (subst (a +: var) b) = subst (rename ξ a +: var) (rename (lift ξ) b) := by
  calc
    rename ξ (subst (a +: var) b) = subst (rename ξ ∘ (a +: var)) b := by
      simpa using (renameSubst ξ (a +: var) b)
    _ = subst ((rename ξ a +: var) ∘ lift ξ) b := by simp [rename_cons_var_eq]
    _ = subst (rename ξ a +: var) (rename (lift ξ) b) := by
      simpa using (substRename (lift ξ) (rename ξ a +: var) b).symm

/-- Symmetric form of `rename_subst_cons` -/
lemma subst_rename_cons {ξ : ℕ → ℕ} {a b : Term} :
    subst (rename ξ a +: var) (rename (lift ξ) b) = rename ξ (subst (a +: var) b) :=
  (rename_subst_cons (ξ := ξ) (a := a) (b := b)).symm

/-- Composition of `lift` with `lift`: `lift ξ ∘ lift ζ = lift (ξ ∘ ζ)`. -/
lemma lift_comp (ξ ζ : ℕ → ℕ) : ∀ n, lift ξ (lift ζ n) = lift (ξ ∘ ζ) n := by
  intro n; cases n <;> simp [lift, Function.comp]

/-- `lift ξ ∘ Nat.succ = Nat.succ ∘ ξ`. -/
lemma lift_succ_comp (ξ : ℕ → ℕ) : lift ξ ∘ Nat.succ = Nat.succ ∘ ξ := by
  ext n; simp [lift, Function.comp]


/-- Renaming is functorial: `rename ξ (rename ζ t) = rename (ξ ∘ ζ) t`. -/
lemma rename_rename (ξ ζ : ℕ → ℕ) (t : Term) : rename ξ (rename ζ t) = rename (ξ ∘ ζ) t := by
  induction t generalizing ξ ζ with
  | var n => simp
  | 𝒰 a ih => simp [rename, ih]
  | pi a b iha ihb =>
      have hlc_eq : (lift ξ ∘ lift ζ) = lift (ξ ∘ ζ) := by
        funext n; exact lift_comp ξ ζ n
      have ihb' : rename (lift ξ) (rename (lift ζ) b) = rename (lift ξ ∘ lift ζ) b := ihb (lift ξ) (lift ζ)
      calc
        rename ξ (rename ζ (pi a b))
            = rename ξ (pi (rename ζ a) (rename (lift ζ) b)) := by dsimp [rename]
        _ = pi (rename ξ (rename ζ a)) (rename (lift ξ) (rename (lift ζ) b)) := by dsimp [rename]
        _ = pi (rename (ξ ∘ ζ) a) (rename (lift ξ) (rename (lift ζ) b)) := by rw [iha]
        _ = pi (rename (ξ ∘ ζ) a) (rename (lift ξ ∘ lift ζ) b) := by rw [ihb']
        _ = pi (rename (ξ ∘ ζ) a) (rename (lift (ξ ∘ ζ)) b) := by rw [hlc_eq]
        _ = rename (ξ ∘ ζ) (pi a b) := by dsimp [rename]
  | abs a b iha ihb =>
      have hlc_eq : (lift ξ ∘ lift ζ) = lift (ξ ∘ ζ) := by
        funext n; exact lift_comp ξ ζ n
      have ihb' : rename (lift ξ) (rename (lift ζ) b) = rename (lift ξ ∘ lift ζ) b := ihb (lift ξ) (lift ζ)
      calc
        rename ξ (rename ζ (abs a b))
            = rename ξ (abs (rename ζ a) (rename (lift ζ) b)) := by dsimp [rename]
        _ = abs (rename ξ (rename ζ a)) (rename (lift ξ) (rename (lift ζ) b)) := by dsimp [rename]
        _ = abs (rename (ξ ∘ ζ) a) (rename (lift ξ) (rename (lift ζ) b)) := by rw [iha]
        _ = abs (rename (ξ ∘ ζ) a) (rename (lift ξ ∘ lift ζ) b) := by rw [ihb']
        _ = abs (rename (ξ ∘ ζ) a) (rename (lift (ξ ∘ ζ)) b) := by rw [hlc_eq]
        _ = rename (ξ ∘ ζ) (abs a b) := by dsimp [rename]
  | app b a ihb iha => simp [rename, ihb, iha]
  | mty => simp
  | exf a b iha ihb => simp [rename, iha, ihb]
  | lvl a ih => simp [rename, ih]
  | lof k => simp

/-- Proof that `rename ξ (subst σ s) = subst (rename ξ ∘ σ) s`
    (proves the repo's `renameSubst` axiom). -/
theorem renameSubst_proved (ξ : ℕ → ℕ) (σ : ℕ → Term) : ∀ s,
    rename ξ (subst σ s) = subst (rename ξ ∘ σ) s := by
  intro s
  induction s generalizing ξ σ with
  | var n => simp
  | 𝒰 a ih => simp [rename, subst, ih]
  | pi a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a]
    rw [ih_b (0 +: Nat.succ ∘ ξ) (var 0 +: rename Nat.succ ∘ σ)]
    apply subst_ext (rename (0 +: Nat.succ ∘ ξ) ∘ (var 0 +: rename Nat.succ ∘ σ))
      (var 0 +: rename Nat.succ ∘ (rename ξ ∘ σ))
    intro n
    cases n with
    | zero => simp [cons]
    | succ n =>
      simp [cons, Function.comp]
      calc
        rename (0 +: Nat.succ ∘ ξ) (rename Nat.succ (σ n))
            = rename ((0 +: Nat.succ ∘ ξ) ∘ Nat.succ) (σ n) := by
              rw [rename_rename (0 +: Nat.succ ∘ ξ) Nat.succ (σ n)]
        _ = rename (Nat.succ ∘ ξ) (σ n) := rfl
        _ = rename Nat.succ (rename ξ (σ n)) := by
          rw [← rename_rename Nat.succ ξ (σ n)]
  | abs a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a]
    rw [ih_b (0 +: Nat.succ ∘ ξ) (var 0 +: rename Nat.succ ∘ σ)]
    apply subst_ext (rename (0 +: Nat.succ ∘ ξ) ∘ (var 0 +: rename Nat.succ ∘ σ))
      (var 0 +: rename Nat.succ ∘ (rename ξ ∘ σ))
    intro n
    cases n with
    | zero => simp [cons]
    | succ n =>
      simp [cons, Function.comp]
      calc
        rename (0 +: Nat.succ ∘ ξ) (rename Nat.succ (σ n))
            = rename ((0 +: Nat.succ ∘ ξ) ∘ Nat.succ) (σ n) := by
              rw [rename_rename (0 +: Nat.succ ∘ ξ) Nat.succ (σ n)]
        _ = rename (Nat.succ ∘ ξ) (σ n) := rfl
        _ = rename Nat.succ (rename ξ (σ n)) := by
          rw [← rename_rename Nat.succ ξ (σ n)]
  | app b a =>
    rename_i ih_b ih_a
    simp [rename, subst, ih_b, ih_a]
  | mty => simp
  | exf a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a, ih_b]
  | lvl a ih => simp [rename, subst, ih]
  | lof k => simp

/-- Proof that `subst σ (rename ξ s) = subst (σ ∘ ξ) s`
    (proves the repo's `substRename` axiom). -/
theorem substRename_proved (ξ : ℕ → ℕ) (σ : ℕ → Term) : ∀ s,
    subst σ (rename ξ s) = subst (σ ∘ ξ) s := by
  intro s
  induction s generalizing ξ σ with
  | var n => simp
  | 𝒰 a ih => simp [rename, subst, ih]
  | pi a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a]
    rw [ih_b (0 +: Nat.succ ∘ ξ) (var 0 +: rename Nat.succ ∘ σ)]
    apply subst_ext ((var 0 +: rename Nat.succ ∘ σ) ∘ (0 +: Nat.succ ∘ ξ))
      (var 0 +: rename Nat.succ ∘ (σ ∘ ξ))
    intro n
    cases n <;> simp [cons, Function.comp]
  | abs a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a]
    rw [ih_b (0 +: Nat.succ ∘ ξ) (var 0 +: rename Nat.succ ∘ σ)]
    apply subst_ext ((var 0 +: rename Nat.succ ∘ σ) ∘ (0 +: Nat.succ ∘ ξ))
      (var 0 +: rename Nat.succ ∘ (σ ∘ ξ))
    intro n
    cases n <;> simp [cons, Function.comp]
  | app b a =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_b, ih_a]
  | mty => simp
  | exf a b =>
    rename_i ih_a ih_b
    simp [rename, subst, ih_a, ih_b]
  | lvl a ih => simp [rename, subst, ih]
  | lof k => simp

/-- Extensionality for `lift`: if `ξ` and `ζ` agree on all arguments, their lifts do too. -/
lemma rename_ext_lift {ξ ζ : ℕ → ℕ} (h : ∀ x, ξ x = ζ x) : ∀ x, lift ξ x = lift ζ x := by
  intro n; cases n <;> simp [h, lift]

/-- Extensionality for `rename`: if `ξ` and `ζ` agree on all arguments,
    then `rename ξ t = rename ζ t` for all `t`. -/
theorem rename_ext {ξ ζ : ℕ → ℕ} (h : ∀ x, ξ x = ζ x) : ∀ t, rename ξ t = rename ζ t := by
  intro t
  induction t generalizing ξ ζ with
  | var n => simp [h n]
  | 𝒰 a iha => simp only [rename]; rw [iha h]
  | pi a b iha ihb =>
    simp only [rename]
    rw [iha h]
    exact congrArg (pi (rename ζ a)) (ihb (rename_ext_lift h))
  | abs a b iha ihb =>
    simp only [rename]
    rw [iha h]
    exact congrArg (abs (rename ζ a)) (ihb (rename_ext_lift h))
  | app a b iha ihb => simp only [rename]; rw [iha h, ihb h]
  | mty => simp
  | exf a b iha ihb => simp only [rename]; rw [iha h, ihb h]
  | lvl a iha => simp only [rename]; rw [iha h]
  | lof k => simp

/-- `rename (lift ξ)` commutes with `rename Nat.succ`. -/
lemma rename_lift_succ_comp (ξ : ℕ → ℕ) (s : Term) :
    rename (lift ξ) (rename Nat.succ s) = rename Nat.succ (rename ξ s) := by
  calc
    rename (lift ξ) (rename Nat.succ s) = rename (lift ξ ∘ Nat.succ) s := by rw [rename_rename]
    _ = rename (Nat.succ ∘ ξ) s := by
      refine rename_ext (by intro m; simp) s
    _ = rename Nat.succ (rename ξ s) := by rw [← rename_rename]

/-- Lifting commutes with renaming-substitution at the pointwise level:
    if `rename ξ ∘ σ = τ` pointwise, then `rename (lift ξ) ∘ (⇑ σ) = ⇑ τ` pointwise. -/
theorem up_rename (ξ : ℕ → ℕ) (σ τ : ℕ → Term)
    (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ x, (rename (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Function.comp_apply]
    have h_sigma : (⇑ σ) (Nat.succ n) = rename Nat.succ (σ n) := by simp [up]
    have h_tau : (⇑ τ) (Nat.succ n) = rename Nat.succ (τ n) := by simp [up]
    rw [h_sigma, h_tau]
    rw [rename_lift_succ_comp ξ (σ n)]
    simpa [Function.comp_apply] using congrArg (rename Nat.succ) (h n)

/-- Renaming preserves the `abs` constructor:
    `rename ξ a` is of the form `abs _ _` iff `a` is. -/
lemma rename_eq_abs_iff {ξ : ℕ → ℕ} {a : Term} :
    (∃ x y, rename ξ a = abs x y) ↔ (∃ x y, a = abs x y) := by
  constructor
  · intro h
    rcases h with ⟨x, y, h⟩
    cases a <;> simp [rename] at h ⊢
  · intro h
    rcases h with ⟨x, y, rfl⟩
    simp [rename]

/-- Renaming preserves parallel reduction -/
lemma rename_par {ξ : ℕ → ℕ} {a b : Term} (h : a ⇒ b) : rename ξ a ⇒ rename ξ b := by
  match h with
  | Par.var s =>
      simpa using Par.var (ξ s)
  | Par.𝒰 h1 =>
      have ih := rename_par h1 (ξ := ξ)
      simpa using Par.𝒰 ih
  | Par.pi h1 h2 =>
      have ih1 := rename_par h1 (ξ := ξ)
      have ih2 := rename_par h2 (ξ := lift ξ)
      simpa using Par.pi ih1 ih2
  | Par.abs h1 h2 =>
      have ih1 := rename_par h1 (ξ := ξ)
      have ih2 := rename_par h2 (ξ := lift ξ)
      simpa using Par.abs ih1 ih2
  | Par.app h1 h2 =>
      have ih1 := rename_par h1 (ξ := ξ)
      have ih2 := rename_par h2 (ξ := ξ)
      simpa using Par.app ih1 ih2
  | Par.β h1 h2 =>
      have ih1 := rename_par h1 (ξ := lift ξ)
      have ih2 := rename_par h2 (ξ := ξ)
      simpa [rename_subst_cons] using Par.β ih1 ih2
  | Par.mty =>
      simpa using Par.mty
  | Par.exf h1 h2 =>
      have ih1 := rename_par h1 (ξ := ξ)
      have ih2 := rename_par h2 (ξ := ξ)
      simpa using Par.exf ih1 ih2
  | Par.lvl h1 =>
      have ih := rename_par h1 (ξ := ξ)
      simpa using Par.lvl ih
  | Par.lof k =>
      simpa using Par.lof k

set_option hygiene false in
/-- Anti-renaming for parallel reduction:
    if `rename ξ a ⇒ b'`, then there exists `b` such that
    `b' = rename ξ b` and `a ⇒ b`. This is the inverse direction
    of `rename_par`. -/
theorem par_of_rename_par {ξ : ℕ → ℕ} {a b' : Term}
    (r : rename ξ a ⇒ b') : ∃ b, b' = rename ξ b ∧ a ⇒ b := by
  cases a with
  | var s =>
      cases r
      · exact ⟨var s, rfl, Par.var s⟩
  | 𝒰 a' =>
      cases r
      · rename_i ra
        rcases par_of_rename_par ra with ⟨b, hb, ha⟩
        exact ⟨𝒰 b, by simp [hb], Par.𝒰 ha⟩
  | pi A B =>
      cases r
      · rename_i ra rb
        rcases par_of_rename_par ra with ⟨A', hA', ha⟩
        rcases par_of_rename_par rb with ⟨B', hB', hb⟩
        exact ⟨pi A' B', by simp [hA', hB'], Par.pi ha hb⟩
  | abs A B =>
      cases r
      · rename_i ra rb
        rcases par_of_rename_par ra with ⟨A', hA', ha⟩
        rcases par_of_rename_par rb with ⟨B', hB', hb⟩
        exact ⟨abs A' B', by simp [hA', hB'], Par.abs ha hb⟩
  | mty =>
      cases r
      · exact ⟨mty, rfl, Par.mty⟩
  | exf A B =>
      cases r
      · rename_i ra rb
        rcases par_of_rename_par ra with ⟨A', hA', ha⟩
        rcases par_of_rename_par rb with ⟨B', hB', hb⟩
        exact ⟨exf A' B', by simp [hA', hB'], Par.exf ha hb⟩
  | lvl a' =>
      cases r
      · rename_i ra
        rcases par_of_rename_par ra with ⟨b, hb, ha⟩
        exact ⟨lvl b, by simp [hb], Par.lvl ha⟩
  | lof k =>
      cases r
      · exact ⟨lof k, rfl, Par.lof k⟩
  | app f arg =>
      cases f with
      | var n =>
          have r' : app (var (ξ n)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := var n) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | 𝒰 u =>
          have r' : app (rename ξ (𝒰 u)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := 𝒰 u) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | pi u v =>
          have r' : app (rename ξ (pi u v)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := pi u v) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | app u v =>
          have r' : app (rename ξ (app u v)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := app u v) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | mty =>
          have r' : app (rename ξ mty) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := mty) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | exf u v =>
          have r' : app (rename ξ (exf u v)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := exf u v) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | lvl u =>
          have r' : app (rename ξ (lvl u)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := lvl u) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | lof l =>
          have r' : app (rename ξ (lof l)) (rename ξ arg) ⇒ b' := by simpa [rename] using r
          cases r' with
          | app rb ra =>
            rcases par_of_rename_par (a := lof l) rb with ⟨b0, hb0, hb⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨app b0 a0, by simp [hb0, ha0], Par.app hb ha⟩
      | abs x y =>
          have r' : app (abs (rename ξ x) (rename (lift ξ) y)) (rename ξ arg) ⇒ b' := by
            simpa [rename] using r
          cases r' with
          | app rb ra =>
            cases rb with
            | abs rx ry =>
              rcases par_of_rename_par (a := x) rx with ⟨x0, hx0, hx⟩
              rcases par_of_rename_par (a := y) ry with ⟨y0, hy0, hy⟩
              rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
              exact ⟨app (abs x0 y0) a0, by simp [hx0, hy0, ha0],
                Par.app (Par.abs hx hy) ha⟩
          | β rb ra =>
            rcases par_of_rename_par (a := y) rb with ⟨y0, hy0, hy⟩
            rcases par_of_rename_par ra with ⟨a0, ha0, ha⟩
            exact ⟨subst (a0 +: var) y0, by
              simpa [hy0, ha0] using (subst_rename_cons (ξ := ξ) (a := a0) (b := y0))
            , Par.β hy ha⟩
termination_by a

end Rename

/-!
  # Parallel reduction basic properties

  Reflexivity, substitution, Takahashi complete development,
  diamond property, and inversion lemmas for multi-step reduction.
-/

/-- Reflexivity of parallel reduction: every term reduces to itself. -/
theorem parRefl : ∀ a : Term, a ⇒ a := by
  intro a; induction a with
  | var s => exact Par.var s
  | 𝒰 a ih => exact Par.𝒰 ih
  | pi a b iha ihb => exact Par.pi iha ihb
  | abs a b iha ihb => exact Par.abs iha ihb
  | app b a ihb iha => exact Par.app ihb iha
  | mty => exact Par.mty
  | exf a b iha ihb => exact Par.exf iha ihb
  | lvl a ih => exact Par.lvl ih
  | lof k => exact Par.lof k

/-- Lifting of parallel reduction: if `σ n ⇒ τ n` for all `n`,
    then `(⇑ σ) n ⇒ (⇑ τ) n` for all `n`. -/
lemma parLift {σ τ : ℕ → Term} (h : ∀ n, σ n ⇒ τ n) : ∀ n, (⇑ σ) n ⇒ (⇑ τ) n := by
  intro n
  unfold up
  cases n with
  | zero => exact Par.var 0
  | succ n =>
    simp
    exact rename_par (ξ := Nat.succ) (h n)

/-- Substitution respects parallel reduction.
    If `σ n ⇒ τ n` for all `n` and `a ⇒ b`, then `subst σ a ⇒ subst τ b`. -/
theorem parSubst {σ τ : ℕ → Term} (hστ : ∀ n, σ n ⇒ τ n) {a b : Term}
    (hab : a ⇒ b) : subst σ a ⇒ subst τ b := by
  induction hab generalizing σ τ with
  | @β b b' a a' c rb ra ihb iha =>
    have hb' : subst (⇑ σ) b ⇒ subst (⇑ τ) b' := ihb (σ := ⇑ σ) (τ := ⇑ τ) (hστ := parLift hστ)
    have ha' : subst σ a ⇒ subst τ a' := iha (σ := σ) (τ := τ) (hστ := hστ)
    have h_comp1 : subst (subst τ a' +: var) (subst (⇑ τ) b') =
        subst (fun n => subst (subst τ a' +: var) ((⇑ τ) n)) b' := by
      simpa [Function.comp] using substComp (subst τ a' +: var) (⇑ τ) b'
    have h_comp2 : (fun (n : ℕ) => subst (subst τ a' +: var) ((⇑ τ) n)) = (subst τ a' +: τ) := by
      funext n
      cases n with
      | zero => simp [cons, up]
      | succ n =>
        simp [up, cons]
        have h_rename := substRename Nat.succ (subst τ a' +: var) (τ n)
        -- h_rename : subst (subst τ a' +: var) (rename Nat.succ (τ n)) = subst ((subst τ a' +: var) ∘ Nat.succ) (τ n)
        have h_func : ((subst τ a' +: var) ∘ Nat.succ) = var := by
          funext x; simp [cons]
        calc
          subst (subst τ a' +: var) (rename Nat.succ (τ n))
              = subst ((subst τ a' +: var) ∘ Nat.succ) (τ n) := by
                simpa [Function.comp] using h_rename
          _ = subst var (τ n) := by rw [h_func]
          _ = τ n := by rw [substId]
    have h_comp3 : subst τ (subst (a' +: var) b') =
        subst (fun n => subst τ ((a' +: var) n)) b' := by
      simpa [Function.comp] using substComp τ (a' +: var) b'
    have h_ext : (fun (n : ℕ) => subst τ ((a' +: var) n)) = (subst τ a' +: τ) := by
      funext n
      cases n with
      | zero => simp [cons]
      | succ n => simp [cons]
    have h_eq : subst (subst τ a' +: var) (subst (⇑ τ) b') = subst τ (subst (a' +: var) b') := by
      calc
        _ = subst (fun n => subst (subst τ a' +: var) ((⇑ τ) n)) b' := h_comp1
        _ = subst (subst τ a' +: τ) b' := by rw [h_comp2]
        _ = subst (fun n => subst τ ((a' +: var) n)) b' := by rw [h_ext]
        _ = subst τ (subst (a' +: var) b') := by rw [h_comp3]
    have hβ := Par.β (c := subst σ c) hb' ha'
    -- hβ : app (abs (subst σ c) (subst (⇑ σ) b)) (subst σ a) ⇒ subst (subst τ a' +: var) (subst (⇑ τ) b')
    -- Goal: subst σ (app (abs c b) a) ⇒ subst τ (subst (a' +: var) b')
    -- Use h_eq to transport hβ's RHS to the goal's RHS
    simpa [subst] using (h_eq ▸ hβ)
  | var s => simpa using hστ s
  | 𝒰 r ih => simpa [subst] using Par.𝒰 (ih (σ := σ) (τ := τ) (hστ := hστ))
  | pi ra rb iha ihb =>
    simpa [subst] using Par.pi (iha (σ := σ) (τ := τ) (hστ := hστ))
      (ihb (σ := ⇑ σ) (τ := ⇑ τ) (hστ := parLift hστ))
  | abs ra rb iha ihb =>
    simpa [subst] using Par.abs (iha (σ := σ) (τ := τ) (hστ := hστ))
      (ihb (σ := ⇑ σ) (τ := ⇑ τ) (hστ := parLift hστ))
  | app rb ra ihb iha =>
    simpa [subst] using Par.app (ihb (σ := σ) (τ := τ) (hστ := hστ)) (iha (σ := σ) (τ := τ) (hστ := hστ))
  | mty => exact Par.mty
  | exf ra rb iha ihb =>
    simpa [subst] using Par.exf (iha (σ := σ) (τ := τ) (hστ := hστ)) (ihb (σ := σ) (τ := τ) (hστ := hστ))
  | lvl r ih => simpa [subst] using Par.lvl (ih (σ := σ) (τ := τ) (hστ := hστ))
  | lof k => exact Par.lof k

/-- Congruence of parallel reduction for single-term substitution:
    if `a ⇒ a'` and `b ⇒ b'`, then `subst (a +: var) b ⇒ subst (a' +: var) b'`. -/
lemma parCong {a a' b b'} (ra : a ⇒ a') (rb : b ⇒ b') :
    subst (a +: var) b ⇒ subst (a' +: var) b' :=
  parSubst (by
    intro x
    cases x
    · exact ra
    · exact Par.var _) rb

/-- Every term parallel-reduces to its Takahashi complete development. -/
private def takaReflDef : ∀ (a : Term), a ⇒ taka a
  | var s => Par.var s
  | 𝒰 a => Par.𝒰 (takaReflDef a)
  | pi a b => Par.pi (takaReflDef a) (takaReflDef b)
  | abs a b => Par.abs (takaReflDef a) (takaReflDef b)
  | app (abs c d) a =>
    have hd : d ⇒ taka d := takaReflDef d
    have ha : a ⇒ taka a := takaReflDef a
    Par.β hd ha
  | app (var s) a => Par.app (takaReflDef (var s)) (takaReflDef a)
  | app (𝒰 u) a => Par.app (takaReflDef (𝒰 u)) (takaReflDef a)
  | app (pi c d) a => Par.app (takaReflDef (pi c d)) (takaReflDef a)
  | app (app c d) a => Par.app (takaReflDef (app c d)) (takaReflDef a)
  | app mty a => Par.app (takaReflDef mty) (takaReflDef a)
  | app (exf c d) a => Par.app (takaReflDef (exf c d)) (takaReflDef a)
  | app (lvl v) a => Par.app (takaReflDef (lvl v)) (takaReflDef a)
  | app (lof k) a => Par.app (takaReflDef (lof k)) (takaReflDef a)
  | mty => Par.mty
  | exf a b => Par.exf (takaReflDef a) (takaReflDef b)
  | lvl a => Par.lvl (takaReflDef a)
  | lof k => Par.lof k
termination_by a => sizeOf a

theorem takaRefl (a : Term) : a ⇒ taka a := takaReflDef a

/-- Squashing property of the Takahashi complete development:
    if `a ⇒ b`, then `b ⇒ taka a`. -/
theorem takaSq {a b : Term} (h : a ⇒ b) : b ⇒ taka a := by
  induction h with
  | β rb ra ihb iha =>
    simpa [taka] using parCong iha ihb
  | var s => exact parRefl (var s)
  | 𝒰 r ih => simpa [taka] using Par.𝒰 ih
  | pi ra rb iha ihb => simpa [taka] using Par.pi iha ihb
  | abs ra rb iha ihb => simpa [taka] using Par.abs iha ihb
  | @app b b' a a' rb ra ihb iha =>
    -- rb : b ⇒ b', ra : a ⇒ a'
    -- ihb : b' ⇒ taka b, iha : a' ⇒ taka a
    -- Goal: app b' a' ⇒ taka (app b a)
    match b with
    | abs c d =>
      -- rb : abs c d ⇒ b'. Only Par.abs can match.
      cases rb with
      | abs rc rd =>
        -- b' = abs c_res d_res
        -- ihb : abs c_res d_res ⇒ abs (taka c) (taka d)
        cases ihb with
        | abs hc hd =>
          -- hc : c_res ⇒ taka c, hd : d_res ⇒ taka d
          simpa [taka] using Par.β hd iha
    | var _ => simpa [taka] using Par.app ihb iha
    | 𝒰 _ => simpa [taka] using Par.app ihb iha
    | pi _ _ => simpa [taka] using Par.app ihb iha
    | app _ _ => simpa [taka] using Par.app ihb iha
    | mty => simpa [taka] using Par.app ihb iha
    | exf _ _ => simpa [taka] using Par.app ihb iha
    | lvl _ => simpa [taka] using Par.app ihb iha
    | lof _ => simpa [taka] using Par.app ihb iha
  | mty => exact Par.mty
  | exf ra rb iha ihb => simpa [taka] using Par.exf iha ihb
  | lvl r ih => simpa [taka] using Par.lvl ih
  | lof k => exact Par.lof k

/-- Diamond property of parallel reduction: if `a ⇒ b` and `a ⇒ c`,
    then there exists `d` such that `b ⇒ d` and `c ⇒ d`. -/
theorem diamond {a b c : Term} (h1 : a ⇒ b) (h2 : a ⇒ c) :
    ∃ d, b ⇒ d ∧ c ⇒ d := by
  refine ⟨taka a, takaSq h1, takaSq h2⟩

/-- Inversion for `lof` in multi-step parallel reduction:
    if `lof j ⇒⋆ t`, then `t = lof j`. -/
theorem parsLofInv {j t} (r : lof j ⇒⋆ t) : t = lof j := by
  generalize heq : lof j = u at r
  induction r generalizing j
  case refl a => subst heq; rfl
  case trans r' _ ih =>
    subst heq
    cases r' with
    | lof k => exact ih rfl

/-!
  # Multi-step parallel reduction basic properties

  Transitivity, congruence, and backward preservation.
-/

/-- Transitivity of multi-step parallel reduction. -/
theorem pars_trans {a b c : Term} (r₁ : a ⇒⋆ b) (r₂ : b ⇒⋆ c) : a ⇒⋆ c := by
  induction r₁
  case refl => exact r₂
  case trans r₁' r₂' ih =>
    apply Pars.trans r₁'
    exact ih r₂

/-- Compatibility of multi-step parallel reduction with a `Par`-compatible function. -/
theorem pars_map {a a' : Term} (f : Term → Term) (h : ∀ {x y : Term}, x ⇒ y → f x ⇒ f y)
    (r : a ⇒⋆ a') : f a ⇒⋆ f a' := by
  induction r
  case refl => exact Pars.refl _
  case trans r₁ r₂ ih =>
    apply Pars.trans (h r₁)
    exact ih

/-- Multi-step parallel reduction is compatible with application on the right side. -/
theorem pars_app_right {a b b' : Term} (s : b ⇒⋆ b') : app a b ⇒⋆ app a b' :=
  pars_map (λ t => app a t) (λ s => Par.app (parRefl a) s) s

/-- Multi-step parallel reduction is compatible with application on the left side. -/
theorem pars_app_left {a a' b : Term} (r : a ⇒⋆ a') : app a b ⇒⋆ app a' b :=
  pars_map (λ t => app t b) (λ r => Par.app r (parRefl b)) r

/-- Multi-step parallel reduction is compatible with application on both sides. -/
theorem pars_app {a a' b b' : Term} (r : a ⇒⋆ a') (s : b ⇒⋆ b') : app a b ⇒⋆ app a' b' :=
  pars_trans (pars_app_left r) (pars_app_right s)

/-- Backward preservation of a relation under multi-step parallel reduction.
If a relation `R` is backward-preserved by `⇒`, then it is backward-preserved by `⇒⋆`. -/
theorem pars_backward {α : Type _} {R : Term → α → Prop}
    (h : ∀ {a b : Term} {c : α}, a ⇒ b → R b c → R a c) {a b : Term} {c : α}
    (r : a ⇒⋆ b) (hR : R b c) : R a c := by
  induction r
  case refl => exact hR
  case trans r₁ r₂ ih =>
    apply h r₁
    exact ih hR

/-- Anti-renaming for multi-step parallel reduction:
    if `rename ξ a ⇒⋆ b'`, then there exists `b` such that
    `b' = rename ξ b` and `a ⇒⋆ b`. Multi-step version of `par_of_rename_par`. -/
theorem pars_of_rename_par {ξ a b'} (r : rename ξ a ⇒⋆ b') : ∃ b, b' = rename ξ b ∧ a ⇒⋆ b := by
  generalize ha : rename ξ a = x at r
  induction r generalizing a with
  | refl x' =>
    subst ha
    exact ⟨a, rfl, Pars.refl a⟩
  | trans h₁ h₂ ih =>
    subst ha
    rcases par_of_rename_par h₁ with ⟨a', hy, hpar⟩
    rcases ih (a := a') hy.symm with ⟨b, hb', hpars⟩
    refine ⟨b, hb', Pars.trans hpar hpars⟩
