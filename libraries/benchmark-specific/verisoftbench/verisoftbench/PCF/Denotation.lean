import PCF.Denotation
import verisoftbench.PCF.Domain

/-!
# PCF Denotation — Denotational semantics lemmas

Theorems about the denotational semantics of PCF:
how renaming interacts with environment extension,
and naturality of term denotation with respect to renaming.
-/

/-- Renaming `keep` commutes with `Ev.from` in the denotational semantics. -/
theorem Ren.keep_den_from_eq {Γ Δ : Cx} (r : Ren Γ Δ) (τ : Ty) :
    Ren.den (r ∷ᵣ τ) ∘' Ev.from =
    Ev.from ∘' Cont.pair (Ren.den r ∘' Cont.fst) Cont.snd := by
  apply (Cont.mk.injEq _ _ _ _).mpr
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext; intro x
  apply funext; intro υ; apply funext; intro v
  rcases x with ⟨ρ, d⟩
  cases v with
  | z => rfl
  | s υ y => rfl

/-- The denotation of a term is natural with respect to renaming. -/
theorem Tm.ren_den_eq_1 (e : Γ ⊢ τ) : ∀ {Δ}, (r : Ren Γ Δ) → ⟦e.ren r⟧ = (⟦e⟧) ∘' (⟦r⟧) := by
  induction e with
  | var τ x =>
      intro Δ r
      apply (Cont.mk.injEq _ _ _ _).mpr
      apply (Mono.mk.injEq _ _ _ _).mpr
      apply funext; intro ρ; rfl
  | true =>
      intro Δ r; rfl
  | false =>
      intro Δ r; rfl
  | zero =>
      intro Δ r; rfl
  | succ e ih =>
      intro Δ r
      have h := ih r
      calc
        ⟦(e.ren r).succ⟧ = Cont.flat (Nat.succ) ∘' (⟦e.ren r⟧) := rfl
        _ = Cont.flat (Nat.succ) ∘' ((⟦e⟧) ∘' (⟦r⟧)) := by rw [h]
        _ = (Cont.flat (Nat.succ) ∘' (⟦e⟧)) ∘' (⟦r⟧) := by rw [← Cont.comp'_assoc]
        _ = (⟦e.succ⟧) ∘' (⟦r⟧) := rfl
  | pred e ih =>
      intro Δ r
      have h := ih r
      calc
        ⟦(e.ren r).pred⟧ = Cont.pred ∘' (⟦e.ren r⟧) := rfl
        _ = Cont.pred ∘' ((⟦e⟧) ∘' (⟦r⟧)) := by rw [h]
        _ = (Cont.pred ∘' (⟦e⟧)) ∘' (⟦r⟧) := by rw [← Cont.comp'_assoc]
        _ = (⟦e.pred⟧) ∘' (⟦r⟧) := rfl
  | zero? e ih =>
      intro Δ r
      have h := ih r
      calc
        ⟦(e.ren r).zero?⟧ = Cont.flat (Nat.zero?) ∘' (⟦e.ren r⟧) := rfl
        _ = Cont.flat (Nat.zero?) ∘' ((⟦e⟧) ∘' (⟦r⟧)) := by rw [h]
        _ = (Cont.flat (Nat.zero?) ∘' (⟦e⟧)) ∘' (⟦r⟧) := by rw [← Cont.comp'_assoc]
        _ = (⟦e.zero?⟧) ∘' (⟦r⟧) := rfl
  | cond s t f ihs iht ihf =>
      intro Δ r
      have hs := ihs r; have ht := iht r; have hf := ihf r
      calc
        ⟦(s.ren r).cond (t.ren r) (f.ren r)⟧
            = Cont.uncurry Cont.cond ∘' Cont.pair (⟦s.ren r⟧)
                (Cont.pair (⟦t.ren r⟧) (⟦f.ren r⟧)) := rfl
        _ = Cont.uncurry Cont.cond ∘' Cont.pair ((⟦s⟧) ∘' (⟦r⟧))
                (Cont.pair ((⟦t⟧) ∘' (⟦r⟧)) ((⟦f⟧) ∘' (⟦r⟧))) := by rw [hs, ht, hf]
        _ = Cont.uncurry Cont.cond ∘' (Cont.pair (⟦s⟧) (Cont.pair (⟦t⟧) (⟦f⟧)) ∘' (⟦r⟧)) := by
          rw [Cont.pair_comp', Cont.pair_comp']
        _ = (Cont.uncurry Cont.cond ∘' Cont.pair (⟦s⟧) (Cont.pair (⟦t⟧) (⟦f⟧))) ∘' (⟦r⟧) := by
          rw [← Cont.comp'_assoc]
        _ = (⟦s.cond t f⟧) ∘' (⟦r⟧) := rfl
  | app f a ihf iha =>
      intro Δ r
      have hf := ihf r; have ha := iha r
      calc
        ⟦(f.ren r).app (a.ren r)⟧ = Cont.eval ∘' Cont.pair (⟦f.ren r⟧) (⟦a.ren r⟧) := rfl
        _ = Cont.eval ∘' Cont.pair ((⟦f⟧) ∘' (⟦r⟧)) ((⟦a⟧) ∘' (⟦r⟧)) := by rw [hf, ha]
        _ = Cont.eval ∘' (Cont.pair (⟦f⟧) (⟦a⟧) ∘' (⟦r⟧)) := by rw [Cont.pair_comp']
        _ = (Cont.eval ∘' Cont.pair (⟦f⟧) (⟦a⟧)) ∘' (⟦r⟧) := by rw [← Cont.comp'_assoc]
        _ = (⟦f.app a⟧) ∘' (⟦r⟧) := rfl
  | fix f ih =>
      intro Δ r
      have h := ih r
      calc
        ⟦(f.ren r).fix⟧ = Cont.fix' ∘' (⟦f.ren r⟧) := rfl
        _ = Cont.fix' ∘' ((⟦f⟧) ∘' (⟦r⟧)) := by rw [h]
        _ = (Cont.fix' ∘' (⟦f⟧)) ∘' (⟦r⟧) := by rw [← Cont.comp'_assoc]
        _ = (⟦f.fix⟧) ∘' (⟦r⟧) := rfl
  | @fn Γ' τ' υ' e ih =>
      intro Δ r
      have h := ih (r ∷ᵣ τ')
      calc
        ⟦(e.ren (r ∷ᵣ τ')).fn⟧ = Cont.curry ((⟦e.ren (r ∷ᵣ τ')⟧) ∘' Ev.from) := rfl
        _ = Cont.curry (((⟦e⟧) ∘' Ren.den (r ∷ᵣ τ')) ∘' Ev.from) := by rw [h]
        _ = Cont.curry ((⟦e⟧) ∘' (Ren.den (r ∷ᵣ τ') ∘' Ev.from)) := by
          rw [← Cont.comp'_assoc]
        _ = Cont.curry ((⟦e⟧) ∘'
              (Ev.from ∘' Cont.pair (Ren.den r ∘' Cont.fst) Cont.snd)) := by
          rw [Ren.keep_den_from_eq r τ']
        _ = Cont.curry (((⟦e⟧) ∘' Ev.from) ∘'
              Cont.pair (Ren.den r ∘' Cont.fst) Cont.snd) := by rw [Cont.comp'_assoc]
        _ = (Cont.curry ((⟦e⟧) ∘' Ev.from)) ∘' (⟦r⟧) := by rw [Cont.curry_pair_comp']
        _ = (⟦e.fn⟧) ∘' (⟦r⟧) := rfl
