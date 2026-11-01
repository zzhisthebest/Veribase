import Clean.Circuit.Theorems

/-!
Theorems about `Environment.ExtendsVector`, `Environment.UsesLocalWitnessesFlat`,
and their relation to `FlatOperation.localWitnesses`.
-/

open FlatOperation (localLength localWitnesses)

namespace Environment

/-- `ExtendsVector` distributes over vector concatenation:
  extending with `v1 ++ v2` at offset `off` is equivalent to extending with `v1` at offset `off`
  and extending with `v2` at offset `off + v1.size`. -/
lemma extendsVector_append_iff {F : Type} [Field F] {env : Environment F} {m n : ℕ} {v1 : Vector F m}
    {v2 : Vector F n} (offset : ℕ) :
    env.ExtendsVector (v1 ++ v2) offset ↔
      (env.ExtendsVector v1 offset ∧ env.ExtendsVector v2 (offset + m)) := by
  simp only [ExtendsVector, Vector.getElem_append]
  constructor
  · intro h
    constructor
    · intro i
      specialize h ⟨i.val, by
        have : i.val < m := i.2
        omega
      ⟩
      simpa using h
    · intro i
      have hi : m + i.val < m + n := by
        have : i.val < n := i.2
        omega
      specialize h ⟨m + i.val, hi⟩
      simp at h
      simpa [add_assoc] using h
  · intro ⟨h1, h2⟩ i
    by_cases h_lt : i.val < m
    · have hi : i.val < m := h_lt
      have h := h1 ⟨i.val, hi⟩
      simpa [h_lt] using h
    · have : m ≤ i.val := by omega
      have h_ge : i.val - m < n := by
        have : i.val < m + n := i.2
        omega
      have h := h2 ⟨i.val - m, h_ge⟩
      simp [h_lt] at *
      have h_add : offset + m + (i.val - m) = offset + i.val := by omega
      rw [h_add] at h
      exact h

/-- Splitting `ExtendsVector` at `.witness` boundary using `extendsVector_append_iff`. -/
lemma extendsVector_localWitnesses_witness {F : Type} [Field F] {n : ℕ} {ops : List (FlatOperation F)}
    {env : Environment F} {m : ℕ} {c : Environment F → Vector F m} :
    env.ExtendsVector (localWitnesses env (.witness m c :: ops)) n ↔
      (env.ExtendsVector (c env) n ∧ env.ExtendsVector (localWitnesses env ops) (m + n)) := by
  rw [localWitnesses, extendsVector_append_iff n]
  simp [add_comm]

/-- `UsesLocalWitnessesFlat` is equivalent to the `ExtendsVector` condition on `localWitnesses`. -/
theorem usesLocalWitnessesFlat_iff_extendsVector_localWitnesses {F : Type} [Field F] {env : Environment F} (n : ℕ)
    {ops : List (FlatOperation F)} :
    env.UsesLocalWitnessesFlat n ops ↔ env.ExtendsVector (localWitnesses env ops) n := by
  induction ops using FlatOperation.induct generalizing n with
  | empty =>
    simp [UsesLocalWitnessesFlat, FlatOperation.forAll, FlatOperation.localWitnesses, ExtendsVector]
    intro i; exact i.elim0
  | witness m _ _ ih =>
    rw [UsesLocalWitnessesFlat, FlatOperation.forAll, extendsVector_localWitnesses_witness, ← ih (m + n)]
    trivial
  | assert _ _ ih =>
    simp [UsesLocalWitnessesFlat, FlatOperation.forAll]
    exact ih n
  | lookup _ _ ih =>
    simp [UsesLocalWitnessesFlat, FlatOperation.forAll]
    exact ih n

end Environment
