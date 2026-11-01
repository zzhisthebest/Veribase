import PCF.Substitution

/-!
# PCF Renaming — Composition and keep properties

Theorems about renaming (`Tm.ren`) in PCF:
composition distributes over the term structure, and
`keep` interacts properly with renaming composition.
-/

/-- Renaming through `keep` commutes with composition of renamings. -/
theorem Tm.ren_keep_comp {e : (Γ₀ ∷ τ) ⊢ υ} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂} :
    e.ren ((σ₀₁ ⬝ σ₁₂) ∷ᵣ τ) = e.ren ((σ₀₁ ∷ᵣ τ) ⬝ (σ₁₂ ∷ᵣ τ)) := by
  rw [Ren.keep_comp]

/-- Renaming a `succ` term distributes over renaming composition. -/
theorem Tm.ren_comp_succ {e : Γ₀ ⊢ .nat} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (h : e.ren (σ₀₁ ⬝ σ₁₂) = (e.ren σ₀₁).ren σ₁₂) :
    (e.succ).ren (σ₀₁ ⬝ σ₁₂) = ((e.succ).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, h]

/-- Renaming a `pred` term distributes over renaming composition. -/
theorem Tm.ren_comp_pred {e : Γ₀ ⊢ .nat} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (h : e.ren (σ₀₁ ⬝ σ₁₂) = (e.ren σ₀₁).ren σ₁₂) :
    (e.pred).ren (σ₀₁ ⬝ σ₁₂) = ((e.pred).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, h]

/-- Renaming a `zero?` term distributes over renaming composition. -/
theorem Tm.ren_comp_zero? {e : Γ₀ ⊢ .nat} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (h : e.ren (σ₀₁ ⬝ σ₁₂) = (e.ren σ₀₁).ren σ₁₂) :
    (e.zero?).ren (σ₀₁ ⬝ σ₁₂) = ((e.zero?).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, h]

/-- Renaming a `cond` term distributes over renaming composition. -/
theorem Tm.ren_comp_cond {s : Γ₀ ⊢ .bool} {t f : Γ₀ ⊢ τ}
    {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (hs : s.ren (σ₀₁ ⬝ σ₁₂) = (s.ren σ₀₁).ren σ₁₂)
    (ht : t.ren (σ₀₁ ⬝ σ₁₂) = (t.ren σ₀₁).ren σ₁₂)
    (hf : f.ren (σ₀₁ ⬝ σ₁₂) = (f.ren σ₀₁).ren σ₁₂) :
    (s.cond t f).ren (σ₀₁ ⬝ σ₁₂) = ((s.cond t f).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, hs, ht, hf]

/-- Renaming a `fn` term distributes over renaming composition. -/
theorem Tm.ren_comp_fn {e : (Γ₀ ∷ τ) ⊢ υ} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (h : ∀ {Γ₁' Γ₂'} {σ' : Ren (Γ₀ ∷ τ) Γ₁'} {σ'' : Ren Γ₁' Γ₂'},
      e.ren (σ' ⬝ σ'') = (e.ren σ').ren σ'') :
    (e.fn).ren (σ₀₁ ⬝ σ₁₂) = ((e.fn).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, Tm.ren_keep_comp, h]

/-- Renaming an `app` term distributes over renaming composition. -/
theorem Tm.ren_comp_app {f : Γ₀ ⊢ τ ⇒ υ} {a : Γ₀ ⊢ τ}
    {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (hf : f.ren (σ₀₁ ⬝ σ₁₂) = (f.ren σ₀₁).ren σ₁₂)
    (ha : a.ren (σ₀₁ ⬝ σ₁₂) = (a.ren σ₀₁).ren σ₁₂) :
    (f.app a).ren (σ₀₁ ⬝ σ₁₂) = ((f.app a).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, hf, ha]

/-- Renaming a `fix` term distributes over renaming composition. -/
theorem Tm.ren_comp_fix {f : Γ₀ ⊢ τ ⇒ τ} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}
    (h : f.ren (σ₀₁ ⬝ σ₁₂) = (f.ren σ₀₁).ren σ₁₂) :
    (f.fix).ren (σ₀₁ ⬝ σ₁₂) = ((f.fix).ren σ₀₁).ren σ₁₂ := by
  simp [Tm.ren, h]

/-- Renaming composes: applying a composite renaming to a term
is the same as applying them sequentially. -/
theorem Tm.ren_comp_eq {t : Γ₀ ⊢ τ}
  : ∀ {Γ₁ Γ₂} {σ₀₁ : Ren Γ₀ Γ₁} {σ₁₂ : Ren Γ₁ Γ₂}, t.ren (σ₀₁ ⬝ σ₁₂) = (t.ren σ₀₁).ren σ₁₂ := by
  induction t with
  | var τ x => intro Γ₁ Γ₂ σ₀₁ σ₁₂; rfl
  | true => intro Γ₁ Γ₂ σ₀₁ σ₁₂; rfl
  | false => intro Γ₁ Γ₂ σ₀₁ σ₁₂; rfl
  | zero => intro Γ₁ Γ₂ σ₀₁ σ₁₂; rfl
  | succ e ih => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_succ ih
  | pred e ih => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_pred ih
  | zero? e ih => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_zero? ih
  | cond s t f ihs iht ihf =>
    intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_cond ihs iht ihf
  | fn e ih => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_fn ih
  | app f a ihf iha => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_app ihf iha
  | fix f ih => intro Γ₁ Γ₂ σ₀₁ σ₁₂; exact Tm.ren_comp_fix ih
