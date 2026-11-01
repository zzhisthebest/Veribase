/-
Copyright (c) 2025. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.

# Weakest Precondition (WP) calculus theorems for monadic programs

This module provides reusable theorems for the weakest precondition calculus
from `Loom.MonadAlgebras.WP.Basic`. It imports the loom repo definitions
(`wp`, `triple`, etc.) and proves standard laws about them.
-/

import Loom.MonadAlgebras.WP.Basic
import Mathlib.Order.CompleteLattice.Basic

open Lean.Order

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β : Type u} {l : Type u}

section WP

variable [_root_.CompleteLattice l]

section
variable [MAlgOrdered (m := m) l]

/-- WP of `pure a` is the postcondition applied to `a`. -/
lemma wp_pure (a : α) (post : α → l) : wp (m := m) (l := l) (pure a) post = post a := by
  simp [wp, liftM]; rfl

/-- Hoare triple for `pure a`: `{pre} pure a {post}` iff `pre ≤ post a`. -/
lemma triple_pure (pre : l) (a : α) (post : α → l) :
    triple pre (pure (f := m) a) post ↔ pre ≤ post a := by
  rw [triple, wp_pure]

end

variable [MAlgOrdered (m := m) l]

/-- WP of `x >>= f` telescopes: the WP of the continuation `wp (f a) post` becomes the
    postcondition for the first computation. -/
lemma wp_bind {β'} (x : m α) (f : α → m β') (post : β' → l) :
    wp (m := m) (l := l) (x >>= f) post =
    wp (m := m) (l := l) x (fun a => wp (m := m) (l := l) (f a) post) := by
  simp [wp, liftM]; rfl

/-- WP is monotone in the postcondition: if `post₁ ≤ post₂` pointwise,
    then `wp c post₁ ≤ wp c post₂`. -/
lemma wp_mono_post (c : m α) (post₁ post₂ : α → l) (h : ∀ x, post₁ x ≤ post₂ x) :
    wp (m := m) (l := l) c post₁ ≤ wp (m := m) (l := l) c post₂ := by
  unfold wp liftM
  let f₁ : α → m l := fun x => pure (post₁ x)
  let f₂ : α → m l := fun x => pure (post₂ x)
  have h_mu : MAlgOrdered.μ ∘ f₁ ≤ MAlgOrdered.μ ∘ f₂ := by
    intro x
    calc
      (MAlgOrdered.μ ∘ f₁) x = MAlgOrdered.μ (pure (post₁ x)) := rfl
      _ = post₁ x := MAlgOrdered.μ_ord_pure (m := m) (l := l) (post₁ x)
      _ ≤ post₂ x := h x
      _ = MAlgOrdered.μ (pure (post₂ x)) :=
        (MAlgOrdered.μ_ord_pure (m := m) (l := l) (post₂ x)).symm
      _ = (MAlgOrdered.μ ∘ f₂) x := rfl
  have h_bind := MAlgOrdered.μ_ord_bind (m := m) (l := l) f₁ f₂ h_mu c
  simpa [MAlg.lift, f₁, f₂] using h_bind

/-- The bind/sequencing rule for Hoare triples: if `{pre} x {cut}` and
    `∀a, {cut a} f a {post}`, then `{pre} x >>= f {post}`. -/
lemma triple_bind {β'} (pre : l) (x : m α) (cut : α → l) (f : α → m β') (post : β' → l)
    (hx : triple pre x cut) (hf : ∀ a, triple (cut a) (f a) post) :
    triple pre (x >>= f) post := by
  rw [triple, wp_bind]
  rw [triple] at hx
  refine le_trans hx (wp_mono_post x (fun a => cut a)
    (fun a => wp (m := m) (l := l) (f a) post) ?_)
  intro a
  have ha := hf a
  rw [triple] at ha
  exact ha

omit [LawfulMonad m] in
/-- `MAlg.lift` is equivalent to `wp`: both represent a continuation-passing
    embedding of a computation into the assertion language. -/
lemma MAlg.lift_wp (c : m α) (post : α → l) : MAlg.lift c post = wp (m := m) (l := l) c post := by
  simp [wp, MAlg.lift, liftM, MonadLiftT.monadLift]

end WP

section StateTLift

variable {σ : Type u}
variable [_root_.CompleteLattice l] [MAlgOrdered (m := m) l]

/-- WP of a lifted computation in `StateT`: the postcondition receives the state as an
    additional argument, and the WP reduces to the underlying monad `wp` on that state. -/
lemma StateT.wp_lift (c : m α) (post : α → σ → l) :
    wp (m := StateT σ m) (l := σ → l) (liftM (n := StateT σ m) c) post =
    fun s => wp (m := m) (l := l) c (post · s) := by
  ext s
  simp [wp, MAlg.lift, liftM, MonadLiftT.monadLift, MAlg.μ, MAlgOrdered.μ,
    MonadLift.monadLift, StateT.lift, StateT.map, Functor.map]

/-- `MAlg.lift` version of `StateT.wp_lift`:
    `MAlg.lift (liftM c) f = λ s => MAlg.lift c (λ x => f x s)`. -/
lemma MAlg.lift_liftM_StateT (c : m α) (f : α → σ → l) :
    MAlg.lift (liftM (n := StateT σ m) c) f = fun s => MAlg.lift c (fun x => f x s) := by
  ext s
  simp [MAlg.lift, liftM, MonadLiftT.monadLift, MAlg.μ, MAlgOrdered.μ,
    MonadLift.monadLift, StateT.lift, StateT.map, Functor.map]

/-- Functor `map` over a lifted computation in `StateT` simplifies by pushing the map
    into the underlying monad, pairing the result with the state. -/
lemma StateT.fmap_lift (f : α → β) (c : m α) (s : σ) :
    (f <$> liftM (n := StateT σ m) c) s = (fun x => (f x, s)) <$> c := by
  dsimp [Functor.map, StateT.map, liftM, MonadLiftT.monadLift]
  simp [MonadLift.monadLift, StateT.lift, Functor.map_map]

end StateTLift

section PartialCorrectness

variable [_root_.CompleteLattice l] [MAlgOrdered (m := m) l]
variable [∀ α, CCPO (m α)] [MonoBind m] [MAlgPartial m]

omit [LawfulMonad m] [MonoBind m] in
/-- Admissibility of a triple for partial correctness: if a triple holds pointwise on a chain,
    it holds for the supremum of the chain. -/
lemma admissible_triple (pre : l) (post : α → l) :
    admissible (fun (c : m α) => triple pre c post) := by
  rw [admissible]
  intro cs hc h
  rw [triple]
  refine le_trans (le_iInf₂ h) ?_
  apply PartialCorrectness.wp_csup cs post hc

/-- Loop invariant rule for partial correctness.
    If `f` preserves the invariant `inv`, then the loop preserves it.
    The invariant `inv` is indexed by the `ForInStep` state (yield or done). -/
lemma repeat_inv (f : Unit → β → m (ForInStep β))
    (inv : ForInStep β → l) (init : β) :
    (∀ b, triple (inv (.yield b)) (f () b) (inv)) →
    triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
  intro hstep
  revert init
  apply Loop.forIn.loop.fixpoint_induct (f := f)
    (motive := fun loop => ∀ init, triple (inv (.yield init)) (loop init) (fun b => inv (.done b)))
  · apply admissible_pi_apply
      (P := fun init loop => triple (inv (.yield init)) (loop) (fun b => inv (.done b)))
    intro init
    apply admissible_triple
  · intro loop ih init
    rw [triple, wp_bind]
    have hbody : inv (.yield init) ≤ wp (m := m) (l := l) (f () init) inv := hstep init
    refine le_trans hbody ?_
    apply wp_mono_post (f () init) inv
    intro step
    match step with
    | ForInStep.done b' =>
        rw [wp_pure]
    | ForInStep.yield b' =>
        have hih := ih b'
        unfold triple at hih
        exact hih

end PartialCorrectness
