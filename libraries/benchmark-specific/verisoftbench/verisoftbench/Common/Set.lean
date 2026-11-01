import Mathlib

lemma Set.inter_ne_empty_of_subset_inter {α : Type _} {A B C : Set α}
    (h_sub : A ⊆ B) (h_ne : C ∩ A ≠ ∅) : C ∩ B ≠ ∅ := by
  have hne : (C ∩ A).Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
  rcases hne with ⟨x, ⟨hxC, hxA⟩⟩
  exact Set.nonempty_iff_ne_empty.mp ⟨x, ⟨hxC, h_sub hxA⟩⟩

lemma iff_forall_union {σ τ : Type _} {P : Prop} {S : Set σ} {A B : σ → Prop}
    {supp : σ → Set τ} {C : τ → Prop}
    (h : ∀ u ∈ S, A u ↔ B u ∧ ∀ y ∈ supp u, C y) :
    (P ∧ ∀ u ∈ S, A u) ↔ (P ∧ ∀ u ∈ S, B u) ∧ ∀ z ∈ (⋃ u ∈ S, supp u), C z := by
  constructor
  · rintro ⟨hP, hA⟩
    constructor
    · refine ⟨hP, λ u hu => ((h u hu).mp (hA u hu)).1⟩
    · intro z hz
      rcases Set.mem_iUnion₂.1 hz with ⟨u, hu, hzu⟩
      exact ((h u hu).mp (hA u hu)).2 z hzu
  · rintro ⟨⟨hP, hB⟩, hC⟩
    refine ⟨hP, λ u hu => ?_⟩
    apply (h u hu).mpr
    refine ⟨hB u hu, λ z hz => hC z ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨u, hu, hz⟩
