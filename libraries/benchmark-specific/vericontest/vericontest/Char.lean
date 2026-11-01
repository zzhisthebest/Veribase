import Mathlib

-- Character predicates useful for string/word constraints in competitive programming

/-- A word (list of characters) consists entirely of lowercase English letters (`a` through `z`). -/
def is_lowercase_word (s : List Char) : Prop :=
  ∀ c ∈ s, 'a' ≤ c ∧ c ≤ 'z'

/-- A `Bool`-valued predicate checking that a word (list of characters) consists
entirely of lowercase English letters (`a` through `z`). Uses `List.all` with
`decide`, making it computationally efficient. For the `Prop` version, see
`is_lowercase_word`. -/
def is_lowercase_string (s : List Char) : Bool :=
  s.all (fun c => decide ('a' ≤ c ∧ c ≤ 'z'))

/-- The `Bool` version `is_lowercase_string` is equivalent to the `Prop` version
`is_lowercase_word`: `is_lowercase_string s = true ↔ is_lowercase_word s`. -/
lemma is_lowercase_string_iff (s : List Char) :
    is_lowercase_string s = true ↔ is_lowercase_word s := by
  simp [is_lowercase_string, is_lowercase_word]
