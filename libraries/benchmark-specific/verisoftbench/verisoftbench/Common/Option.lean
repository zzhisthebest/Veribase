import Mathlib.Data.Set.Basic

open Set

universe v

/-- The preimage of `some '' s` under `Option.map g` equals `some '' (g ⁻¹' s)`. -/
lemma option_map_preimage_some_image {α β : Type v} (g : α → β) (s : Set β) :
    (Option.map g)⁻¹' (some '' s) = some '' (g ⁻¹' s) := by
  ext x; cases x <;> simp
