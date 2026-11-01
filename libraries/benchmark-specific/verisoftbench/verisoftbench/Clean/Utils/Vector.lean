import Clean.Utils.Vector

/-! Theorems about `Vector.flatten` and `Vector.toChunks`, harvested from solved
    training problems. These are placed in `Clean.Utils.Vector` to match the repo. -/

namespace Vector

/-- `flatten` is injective on nested vectors: equal flattened vectors imply equal
    vectors of chunks. -/
lemma flatten_inj {α : Type} {m n : ℕ} {v w : Vector (Vector α m) n}
    (h : v.flatten = w.flatten) : v = w :=
  eq_iff_flatten_eq.mpr h

/-- Equality of vectors of chunks implies equality of their flattened vectors. -/
lemma flatten_eq_of_eq {α : Type} {m n : ℕ} {v w : Vector (Vector α m) n}
    (h : v = w) : v.flatten = w.flatten :=
  congrArg Vector.flatten h

/-- Flattening a vector of chunks, then calling `toChunks` and flattening again
    yields the original flattened vector. -/
lemma flatten_toChunks_flatten_eq (m : ℕ+) {α : Type}
    (v : Vector (Vector α m) n) : (v.flatten.toChunks m).flatten = v.flatten := by
  rw [toChunks_flatten]

/-- `toChunks m` is a left inverse of `flatten` for nested vectors of chunk size `m`. -/
theorem flatten_toChunks {α : Type} (m : ℕ+) (v : Vector (Vector α m) n) :
    v.flatten.toChunks m = v :=
  flatten_inj (flatten_toChunks_flatten_eq m v)

end Vector
