import VCVio.OracleComp.QueryTracking.Structures

set_option quotPrecheck false
open OracleSpec OracleComp

universe u
variable {ι : Type u} {spec : OracleSpec ι}

namespace OracleSpec
namespace QuerySeed

variable [DecidableEq ι]

/-- If `seed = seed'.takeAtIndex idx n`, then at the modified index `idx` the value is
the truncated version of the original. -/
lemma takeAtIndex_apply_eq (seed seed' : QuerySeed spec) (idx : ι) (n : ℕ)
    (h : seed = seed'.takeAtIndex idx n) : seed idx = (seed' idx).take n := by
  simpa [takeAtIndex_apply] using congrArg (· idx) h

/-- If `seed = seed'.takeAtIndex idx n`, then at any other index the values match the original. -/
lemma takeAtIndex_apply_eq_of_ne (seed seed' : QuerySeed spec) (idx j : ι) (n : ℕ)
    (hne : j ≠ idx) (h : seed = seed'.takeAtIndex idx n) : seed j = seed' j := by
  simpa [hne, takeAtIndex_apply] using congrArg (· j) h

/-- If `seed' = seed.addValues xs`, then at the modified index `idx` the value is the original
with `xs` appended. -/
lemma addValues_apply_eq (seed seed' : QuerySeed spec) (idx : ι) (xs : List (spec.range idx))
    (h : seed' = seed.addValues xs) : seed' idx = seed idx ++ xs := by
  simpa [addValues_apply] using congrArg (· idx) h

/-- If `seed' = seed.addValues xs`, then at any other index the values match the original. -/
lemma addValues_apply_eq_of_ne (seed seed' : QuerySeed spec) (idx j : ι)
    (xs : List (spec.range idx)) (hne : j ≠ idx) (h : seed' = seed.addValues xs) :
    seed' j = seed j := by
  simpa [hne, addValues_apply] using congrArg (· j) h

/-- If `seed = seed'.takeAtIndex idx (seed idx).length`, then adding the dropped suffix of
`seed' idx` to `seed` recovers `seed'`. This is the forward direction of the equivalence
between `takeAtIndex` and `addValues` with drop. -/
lemma addValues_eq_of_takeAtIndex_eq (seed seed' : QuerySeed spec) (idx : ι)
    (h : seed = seed'.takeAtIndex idx (seed idx).length) :
    seed' = seed.addValues ((seed' idx).drop (seed idx).length) := by
  apply QuerySeed.ext; intro j
  by_cases hji : j = idx
  · have h_at_i := takeAtIndex_apply_eq seed seed' idx (seed idx).length h
    rw [hji, addValues_apply, Function.update_self]
    calc
      seed' idx = (seed' idx).take (seed idx).length ++ (seed' idx).drop (seed idx).length :=
        (List.take_append_drop (seed idx).length (seed' idx)).symm
      _ = seed idx ++ (seed' idx).drop (seed idx).length := by rw [← h_at_i]
  · have h_eq_at_j := takeAtIndex_apply_eq_of_ne seed seed' idx j (seed idx).length hji h
    simpa [hji, addValues_apply] using h_eq_at_j.symm

/-- If `seed' = seed.addValues ((seed' idx).drop (seed idx).length)`, then taking the first
`(seed idx).length` values from `seed'` at index `idx` recovers `seed`. This is the reverse
direction of the equivalence between `takeAtIndex` and `addValues` with drop. -/
lemma takeAtIndex_eq_of_addValues_eq (seed seed' : QuerySeed spec) (idx : ι)
    (h : seed' = seed.addValues ((seed' idx).drop (seed idx).length)) :
    seed = seed'.takeAtIndex idx (seed idx).length := by
  apply QuerySeed.ext; intro j
  by_cases hji : j = idx
  · have h_at_i := addValues_apply_eq seed seed' idx ((seed' idx).drop (seed idx).length) h
    rw [hji, takeAtIndex_apply, Function.update_self]
    calc
      seed idx = ((seed idx ++ (seed' idx).drop (seed idx).length).take (seed idx).length) := by
        simp
      _ = (seed' idx).take (seed idx).length := by rw [← h_at_i]
  · have h_eq_at_j := addValues_apply_eq_of_ne seed seed' idx j
      ((seed' idx).drop (seed idx).length) hji h
    simpa [hji, takeAtIndex_apply] using h_eq_at_j.symm

/-- Equivalence between extending a seed by dropping from another seed's values
and truncating the other seed's values at the original length. -/
lemma eq_takeAtIndex_length_iff_addValues_drop (seed seed' : QuerySeed spec) (idx : ι) :
    seed = seed'.takeAtIndex idx (seed idx).length ↔
      seed' = seed.addValues ((seed' idx).drop (seed idx).length) :=
  ⟨addValues_eq_of_takeAtIndex_eq seed seed' idx,
   takeAtIndex_eq_of_addValues_eq seed seed' idx⟩

end QuerySeed
end OracleSpec
