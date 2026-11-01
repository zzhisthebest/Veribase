/-
Copyright (c) 2025. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.

# Refinement theorems for NonDetT extraction

This module provides theorems about the extraction of `NonDetT` computations
to the base monad via `.run`, establishing that the weakest precondition
semantics is refined (i.e., `wp s post ≤ wp s.run post`).
-/

import Loom.MonadAlgebras.NonDetT.Basic
import Loom.MonadAlgebras.NonDetT.Extract
import verisoftbench.Loom.GuardHimp
import verisoftbench.Loom.WP

open Lean.Order

universe u v w

variable {m : Type u → Type v} [Monad m] [CCPOBot m] [_root_.CompleteBooleanAlgebra l]
variable [MAlgOrdered (m := m) l] [LawfulMonad m]
variable [∀ α, CCPO (m α)] [MonoBind m]

namespace TotalCorrectness
namespace DemonicChoice

/-- Relate `wp` and `NonDetT.wp` via the `μ` isomorphism for `NonDetT m`. -/
lemma wp_eq_NonDetT_wp_id (x : NonDetT m α) (post : α → l) : wp x post = NonDetT.wp (post <$> x) id := by
  rfl

/-- The weakest precondition of a `NonDetT` computation is at most the
    weakest precondition of its `.run` extraction into the base monad.
    This is a soundness/refinement theorem for the NonDetT extraction. -/
lemma wp_extract_refines (s : NonDetT m α) (post : α → l) : wp s post ≤ wp s.run post := by
  have wp_eq_direct {α : Type u} (x : NonDetT m α) (post : α → l) :
      wp x post = NonDetT.wp x post := by
    rw [wp_eq_NonDetT_wp_id, map_eq_pure_bind]
    erw [NonDetT.wp_bind]
    rfl
  induction s with
  | pure x => simp [NonDetT.run, wp_pure]
  | vis x f ih =>
    simp only [NonDetT.wp_vis, NonDetT.run, wp_bind]
    exact wp_mono_post x _ _ (fun a => ih a post)
  | @pickCont _ τ pred _ f ih =>
    change (⌜∃ a, pred a⌝ ⊓ ⨅ a, ⨅ (_ : pred a), wp (f a) post) ≤ _
    simp only [NonDetT.run]
    split
    · rename_i hf
      have hnone := Findable.find_none (p := pred) (by simpa using hf)
      simp [hnone, LE.pure]
    · rename_i a hf
      have ha := Findable.find_some_p (p := pred) hf
      exact le_trans (le_trans inf_le_right (iInf_le_of_le a (iInf_le _ ha))) (ih a post)
  | repeatCont init f cont ihf ihc =>
    rw [NonDetT.wp_repeatCont, NonDetT.run, wp_bind]
    simp only [iSup_le_iff]
    intro inv measure
    simp only [← wp_eq_direct]
    by_cases hi : ∀ b, inv (.yield b) ≤ wp (f b) (fun
      | .yield b' => inv (.yield b') ⊓ ⌜measure b' < measure b⌝
      | .done b' => inv (.done b'))
    · simp only [LE.pure] at hi
      simp only [LE.pure]
      erw [if_pos hi]
      simp only [top_inf_eq, spec]
      by_cases hc : (fun b => inv (.done b)) ≤ (fun b => wp (cont b) post)
      · simp only [LE.pure, hc, if_true, inf_top_eq]
        have hloop : ∀ b, inv (.yield b) ≤
            wp (Loop.forIn.loop (fun _ b => (f b).run) b) (fun b => inv (.done b)) := by
          intro b
          induction hn : measure b using Nat.strong_induction_on generalizing b with
          | h n ih =>
            rw [Loop.forIn.loop.eq_def, wp_bind]
            refine le_trans (le_trans (hi b) (ihf b _)) (wp_mono_post _ _ _ ?_)
            intro step
            cases step with
            | done b' => simp [wp_pure]
            | yield b' =>
              by_cases hlt : measure b' < measure b
              · simpa [LE.pure, hlt] using ih (measure b') (by omega) b' rfl
              · simp [LE.pure, hlt]
        exact le_trans (hloop init) (wp_mono_post _ _ _ (fun b => le_trans (hc b) (ihc b post)))
      · simp [LE.pure, hc]
    · simp only [LE.pure] at hi
      simp only [LE.pure]
      erw [if_neg hi]
      simp only [bot_inf_eq, _root_.bot_le]

/-- Hoare triple soundness for `NonDetT.run`: if a triple holds for a `NonDetT`
    computation, it also holds after extraction via `.run`. -/
lemma extract_refines (pre : l) (s : NonDetT m α) (post : α → l) :
    triple pre s post → triple pre s.run post := by
  intro h
  unfold triple at h ⊢
  exact le_trans h (wp_extract_refines s post)

end DemonicChoice
end TotalCorrectness

namespace PartialCorrectness
namespace DemonicChoice

/-- WP of `NonDetT.pickCont` reduces to a guarded infimum over `Findable` predicates. -/
@[simp]
lemma NonDetT.wp_pickCont_1 {τ : Type u} p (f : τ → NonDetT m α) [Findable p] post :
    _root_.wp (NonDetT.pickCont τ p f) post = ⨅ a, ⌜p a⌝ ⇨ _root_.wp (f a) post := by
  change (⨅ a, ⨅ (_ : p a), NonDetT.wp (post <$> f a) id) = _
  simp only [iInf_prop_eq_guard_himp]
  rfl

end DemonicChoice
end PartialCorrectness
