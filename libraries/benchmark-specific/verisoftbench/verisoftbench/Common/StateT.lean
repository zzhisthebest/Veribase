/-!
## `StateT` Theorems

Basic properties of the `StateT` monad transformer from the core Lean library.
These provide pointwise expansion lemmas and interaction properties between
`StateT.get`, `StateT.set`, `StateT.pure`, and `StateT.bind`.
-/

set_option linter.unusedSectionVars false

universe u v

namespace StateT

variable {sigma : Type u} {m : Type u -> Type v} {alpha : Type u}

section monad
variable [Monad m] [LawfulMonad m]

theorem bind_get_apply (f : sigma -> StateT sigma m alpha) (s : sigma) :
    ((@StateT.get sigma m _) >>= f) s = f s s := by
  unfold StateT.instMonad
  dsimp
  unfold StateT.bind StateT.get
  simp

theorem bind_set_apply (s0 : sigma) (f : PUnit -> StateT sigma m alpha) (s : sigma) :
    ((StateT.set s0) >>= f) s = f PUnit.unit s0 := by
  unfold StateT.instMonad
  dsimp
  unfold StateT.bind StateT.set
  simp

theorem pure_apply (a : alpha) (s : sigma) : (StateT.pure a) s = (pure (a, s) : m (alpha × sigma)) := by
  rfl

theorem set_apply (s0 s : sigma) : (StateT.set s0) s = (pure (PUnit.unit, s0) : m (PUnit × sigma)) := by
  rfl

theorem set_apply_eq_pure_apply (s : sigma) : (StateT.set s) s = (pure PUnit.unit : StateT sigma m PUnit) s := by
  have h_pure_def : (pure PUnit.unit : StateT sigma m PUnit) = StateT.pure PUnit.unit := rfl
  rw [h_pure_def]
  dsimp [StateT.set, StateT.pure]

theorem set_get_1 : (do let s ← @StateT.get sigma m _; StateT.set s) = pure PUnit.unit := by
  funext s
  rw [bind_get_apply (fun s' => StateT.set s') s, set_apply_eq_pure_apply s]

end monad

end StateT
