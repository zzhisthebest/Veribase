/-
Copyright (c) 2025. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.

# Guarded Heyting implication lemmas

Lemmas relating `LE.pure` / `⌜·⌝` from Loom with the Heyting implication
`⇨` from `CompleteBooleanAlgebra`.
-/

import Loom.MonadAlgebras.Defs
import verisoftbench.Common.Algebra.CompleteBooleanAlgebra

open Classical in
/-- The guarded implication `⌜p⌝ ⇨ x` reduces to `if p then x else ⊤`.
Holds in any `CompleteBooleanAlgebra`. -/
lemma guard_himp_eq_cond {α : Type u} [CompleteBooleanAlgebra α] {x : α} (p : Prop) :
    ⌜p⌝ ⇨ x = (if p then x else ⊤) := by
  by_cases h : p
  · simp [h, LE.pure]
  · simp [h, LE.pure]

/-- The indexed infimum over a proposition equals the guarded implication.
Combines `iInf_prop_eq_cond` and `guard_himp_eq_cond`. -/
lemma iInf_prop_eq_guard_himp {α : Type u} [CompleteBooleanAlgebra α] {x : α} (p : Prop) :
    (⨅ (_h : p), x) = ⌜p⌝ ⇨ x := by
  rw [iInf_prop_eq_cond, guard_himp_eq_cond]
