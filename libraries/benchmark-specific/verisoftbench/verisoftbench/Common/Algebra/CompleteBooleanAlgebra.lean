/-
Copyright (c) 2025. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.

# CompleteBooleanAlgebra lemmas

General-purpose lemmas about `CompleteBooleanAlgebra`.
-/

import Mathlib.Order.CompleteBooleanAlgebra

open Classical in
/-- The indexed infimum over a proposition `p` where the index does not appear
in the body reduces to `if p then x else ⊤`. Holds in any `CompleteBooleanAlgebra`. -/
lemma iInf_prop_eq_cond {α : Type u} [CompleteBooleanAlgebra α] {x : α} (p : Prop) :
    (⨅ (_h : p), x) = (if p then x else ⊤) := by
  by_cases h : p
  · simp [h]
  · simp [h]
