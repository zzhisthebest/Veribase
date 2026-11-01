import Veil.DSL.Action.Theory

namespace Veil

/-- If `act.toBigStep s r' s'` (the BigStep semantics say the action transitions from `s`
to `s'` producing result `r'`) and `act s post` (the Wp semantics say postcondition `post`
holds), then the postcondition must hold at the BigStep result `(r', s')`.

This is a fundamental consistency lemma connecting BigStep and Wp semantics for lawful
actions: any postcondition provable in the Wp calculus must be satisfied by the BigStep
result. -/
theorem post_of_toBigStep {m : Mode} {σ ρ : Type} (act : Wp m σ ρ) [LawfulAction act] {post : RProp σ ρ}
    {s : σ} {r' : ρ} {s' : σ} (hbig : act.toBigStep s r' s') (hpost : act s post) : post r' s' := by
  apply big_step_sound' (act := act) (req := (· = s)) (ens := post)
      (fun t ht => by subst t; exact hpost) s r' s' rfl hbig

/-- If `pre s` holds, `act` always terminates from any state satisfying `pre`,
`act.bind act'` always terminates from any state satisfying `pre`,
and `act.toBigStep s r' s'`, then `act' r'` always terminates from state `s'`. -/
theorem bind_alwaysSuccessfullyTerminates {m : Mode} {σ ρ ρ' : Type} (act : Wp m σ ρ)
    (act' : ρ → Wp m σ ρ') {pre : σ → Prop} {s : σ} {r' : ρ} {s' : σ} [LawfulAction act] :
    pre s →
    act.alwaysSuccessfullyTerminates pre →
    (act.bind act').alwaysSuccessfullyTerminates pre →
    act.toBigStep s r' s' →
    (act' r').alwaysSuccessfullyTerminates (· = s') := by
  intro hpre _ hbind hbig t ht
  subst t
  exact post_of_toBigStep act hbig (hbind s hpre)

/-- If an action always successfully terminates, then soundness holds for
`toBigStep` without the non-trivial-postcondition requirement. -/
theorem big_step_always_terminating_sound {m : Mode} {σ ρ : Type} {act : Wp m σ ρ}
    [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ) :
    act.alwaysSuccessfullyTerminates req →
    act.toBigStep.triple req ens → act.triple req ens := by
  intro hterm htriple s hreq
  by_cases h : (¬ ∀ r s, ens r s)
  · solve_by_elim [big_step_sound]
  · apply LawfulAction.impl (post := fun _ _ => True) <;> try simp_all

/-- Under the `alwaysSuccessfullyTerminates` condition, `act` coincides with
`act.toBigStep.toWp` at any `req`-satisfying state. -/
theorem big_step_to_wp {m : Mode} {σ ρ : Type} (act : Wp m σ ρ) [LawfulAction act]
    (req : SProp σ) {s : σ} :
    act.alwaysSuccessfullyTerminates req →
    req s →
    act s = act.toBigStep.toWp s := by
  intro hterm hreq; ext post; constructor
  · simp [BigStep.toWp]; intro _ _ _
    solve_by_elim [big_step_sound']
  · simp [BigStep.toWp]
    intro h
    apply big_step_always_terminating_sound (σ := σ) (ρ := ρ)
      (req := (s = ·)) (ens := post)
    · intro s₁ heq; subst heq; exact hterm s hreq
    · intro s₁ r' s' heq hbig; subst heq; exact h r' s' hbig
    · rfl

/-- When an action always terminates at the substate projection, lifting its big-step
semantics through `toWp` then converting back to big-step is the same as converting to
big-step then lifting. This is used to relate `r.lift.toBigStep` and
`r.toBigStep.lift` under a termination condition. -/
theorem lift_toBigStep_eq {m : Mode} {σ ρ : Type} {σ' : Type} [IsSubStateOf σ σ']
    (act : Wp m σ ρ) [LawfulAction act] (st : σ') :
    act.alwaysSuccessfullyTerminates (· = getFrom st) →
    act.lift.toBigStep st = (act.toBigStep.toWp.lift).toBigStep st := by
  intro hterm
  unfold Wp.lift Wp.toBigStep Wp.toWlp; ext; simp
  rw [big_step_to_wp (act := act) (req := (fun x => x = getFrom st))] <;> try simp [*]
  unfold Wp.toBigStep Wp.toWlp; simp

/-- Specialized version of `lift_transition_big_step` for `LawfulAction`s
using `Wp` directly (not a `BigStep.toWp`), using `big_step_to_wp` to bridge the gap. -/
theorem lift_transition_big_step' {σ σ'} [IsSubStateOf σ σ'] (m : Mode) (r : Wp m σ ρ)
    [LawfulAction r] (st : σ') :
    r.alwaysSuccessfullyTerminates (· = getFrom st) →
    (@Wp.lift _  m σ σ' _ r).toBigStep st =
    fun r' st' =>
      r.toBigStep (getFrom st) r' (getFrom st') ∧
      st' = (setIn (@getFrom σ σ' _ st') st) := by
  intro term
  have hlift := lift_toBigStep_eq (m := m) (σ := σ) (ρ := ρ) (act := r) (st := st) term
  rw [hlift, lift_transition_big_step]

/-- If `ens r s` holds for all `r, s`, then the always-true relation
`(fun _ _ => True)` entails `ens`.  This is a trivial but useful rewriting
lemma for postcondition reasoning. -/
theorem trueRProp_entails_of_forall {σ ρ : Type} {ens : RProp σ ρ} (h : ∀ r s, ens r s) :
    ∀ r s, (fun (_ : ρ) (_ : σ) => True) r s → ens r s := by
  intro r s _
  exact h r s

/-- If an action's postcondition is `True` from state `s` and `ens` holds
universally (for all results and final states), then the action also
satisfies `ens` from `s`. -/
theorem always_successful_impl_postcondition {m : Mode} {σ ρ : Type} {act : Wp m σ ρ}
    [LawfulAction act] (s : σ) (ens : RProp σ ρ)
    (hterm : act s (fun (_ : ρ) (_ : σ) => True)) (hens : ∀ r s, ens r s) : act s ens := by
  apply LawfulAction.impl (fun (_ : ρ) (_ : σ) => True) ens
  · exact trueRProp_entails_of_forall hens
  · exact hterm

/-- If an action always successfully terminates from any state satisfying
`req` and the postcondition `ens` holds for all results and final states,
then `act.triple req ens` holds.

This lemma handles the special case where the postcondition is universally
true, which simplifies triple reasoning. -/
theorem universally_true_postcondition_implies_triple {m : Mode} {σ ρ : Type}
    {act : Wp m σ ρ} [LawfulAction act] (req : SProp σ) (ens : RProp σ ρ)
    (hterms : act.alwaysSuccessfullyTerminates req) (hens : ∀ r s, ens r s) :
    act.triple req ens := by
  intro s hreq
  have htrue : act s (fun (_ : ρ) (_ : σ) => True) := hterms s hreq
  exact always_successful_impl_postcondition s ens htrue hens

end Veil
