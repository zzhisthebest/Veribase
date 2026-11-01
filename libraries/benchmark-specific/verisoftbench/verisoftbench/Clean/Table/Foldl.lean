import Clean.Table.Basic

/-!
Lemmas about `TableConstraintsHold.foldl`, the inner fold function used to check
that all table constraints hold over a trace.
-/

namespace TableConstraintsHold

variable {F : Type} [Field F] {S : Type → Type} [ProvableType S]

lemma foldl_boundary_fromEnd {N : ℕ} (cs : List (TableOperation S F × (ℕ → Environment F)))
    (trace : Trace F S) (row : Row F S) (constraint : SingleRowConstraint S F)
    (env_fn : ℕ → Environment F) (rest : List (TableOperation S F × (ℕ → Environment F))) :
    foldl N cs (trace +> row)
      ((⟨.boundary (.fromEnd 0) constraint, env_fn⟩) :: rest) →
    (trace.len = N - 1 → constraint.ConstraintsHoldOnWindow ⟨<+> +> row, rfl⟩ (env_fn trace.len)) := by
  intro h hlen_eq
  have h' := (by simpa [foldl, hlen_eq] using h : constraint.ConstraintsHoldOnWindow _ _ ∧ _)
  simpa [hlen_eq] using h'.left

lemma foldl_boundary_fromStart {N : ℕ} (cs : List (TableOperation S F × (ℕ → Environment F)))
    (trace : Trace F S) (row : Row F S) (constraint : SingleRowConstraint S F)
    (env_fn : ℕ → Environment F) (rest : List (TableOperation S F × (ℕ → Environment F))) :
    foldl N cs (trace +> row)
      ((⟨.boundary (.fromStart 0) constraint, env_fn⟩) :: rest) →
    (trace.len = 0 → constraint.ConstraintsHoldOnWindow ⟨<+> +> row, rfl⟩ (env_fn trace.len)) := by
  intro h hlen_eq
  have h' := (by simpa [foldl, hlen_eq] using h : constraint.ConstraintsHoldOnWindow _ _ ∧ _)
  simpa [hlen_eq] using h'.left

lemma foldl_everyRowExceptLast {N : ℕ} (cs : List (TableOperation S F × (ℕ → Environment F)))
    (trace : Trace F S) (curr next : Row F S) (constraint : TwoRowsConstraint S F)
    (env_fn : ℕ → Environment F) (rest : List (TableOperation S F × (ℕ → Environment F))) :
    foldl N cs (trace +> curr +> next)
      ((⟨.everyRowExceptLast constraint, env_fn⟩) :: rest) →
    constraint.ConstraintsHoldOnWindow ⟨<+> +> curr +> next, rfl⟩ (env_fn (trace.len + 1)) := by
  intro h
  have h' := (by simpa [foldl] using h : constraint.ConstraintsHoldOnWindow _ _ ∧ _)
  exact h'.left

lemma foldl_everyRowExceptLast_skip {N : ℕ} (cs : List (TableOperation S F × (ℕ → Environment F)))
    (trace_val : Trace F S) (constraint : TwoRowsConstraint S F)
    (env_fn : ℕ → Environment F) (rest : List (TableOperation S F × (ℕ → Environment F))) :
    foldl N cs trace_val
      ((⟨.everyRowExceptLast constraint, env_fn⟩) :: rest) →
    foldl N cs trace_val rest := by
  intro h
  induction trace_val with
  | empty =>
    simpa [foldl] using h
  | cons tl hd =>
    cases tl with
    | empty =>
      simpa [foldl] using h
    | cons tl' hd' =>
      -- h : foldl N cs (tl' +> hd' +> hd) ((everyRowExceptLast constraint, env_fn) :: rest)
      -- Goal: foldl N cs (tl' +> hd' +> hd) rest
      have h_and := h
      -- The first pattern of foldl for everyRowExceptLast fires
      have h_extract : constraint.ConstraintsHoldOnWindow (⟨<+> +> hd' +> hd, rfl⟩ : TraceOfLength F S 2) (env_fn (tl'.len + 1)) ∧
          foldl N cs (tl' +> hd' +> hd) rest := by
        simpa [foldl] using h_and
      exact h_extract.right

end TableConstraintsHold
