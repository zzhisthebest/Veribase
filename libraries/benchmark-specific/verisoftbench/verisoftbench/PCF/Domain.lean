import PCF.Domain

/-!
# PCF Domain — Continuous function properties

Theorems about continuous functions (`Cont`) between domains:
composition associativity, pairing distributivity, currying interaction,
and extensionality for monotone and continuous functions.
-/

/-- Equality of monotone functions from pointwise equality of their actions. -/
theorem Mono.ext [Order α] [Order β] {f g : Mono α β} (h : ∀ x, f x = g x) : f = g := by
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext h

/-- Equality of continuous functions from pointwise equality of their underlying functions. -/
theorem Cont.ext [Order α] [Domain α] [Order β] [Domain β] {f g : Cont α β}
    (h : ∀ x, f x = g x) : f = g := by
  have h_fn : f.fn = g.fn := Mono.ext h
  cases f; cases g
  cases h_fn
  simp

/-- Composition of continuous functions is associative. -/
theorem Cont.comp'_assoc [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ]
    [Order δ] [Domain δ] (f : Cont β γ) (g : Cont α β) (h : Cont δ α) :
    (f ∘' g) ∘' h = f ∘' (g ∘' h) := by
  apply (Cont.mk.injEq _ _ _ _).mpr
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext; intro ρ; simp [Cont.comp']

/-- Pairing distributes over composition: `pair (f ∘ h) (g ∘ h) = (pair f g) ∘ h`. -/
theorem Cont.pair_comp' [Order α] [Domain α] [Order β] [Domain β] [Order γ] [Domain γ]
    [Order δ] [Domain δ] (f : Cont γ α) (g : Cont γ β) (h : Cont δ γ) :
    Cont.pair (f ∘' h) (g ∘' h) = (Cont.pair f g) ∘' h := by
  apply (Cont.mk.injEq _ _ _ _).mpr
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext; intro ρ; simp [Cont.comp', Cont.pair]

/-- Currying lifts through the pair-domain renaming:
    `curry (f ∘ pair (r ∘ fst) snd) = (curry f) ∘ r`. -/
theorem Cont.curry_pair_comp' [Order α] [Domain α] [Order α'] [Domain α']
    [Order β] [Domain β] [Order γ] [Domain γ] (f : Cont (α × β) γ) (r : Cont α' α) :
    Cont.curry (f ∘' Cont.pair (r ∘' Cont.fst) Cont.snd) = (Cont.curry f) ∘' r := by
  apply (Cont.mk.injEq _ _ _ _).mpr
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext; intro ρ
  apply (Cont.mk.injEq _ _ _ _).mpr
  apply (Mono.mk.injEq _ _ _ _).mpr
  apply funext; intro d
  simp [Cont.comp', Cont.pair, Cont.fst, Cont.snd]
