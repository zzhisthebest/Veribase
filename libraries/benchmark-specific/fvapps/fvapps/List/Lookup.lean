import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Key-value lookup with default

A specialisation of `List.lookup` that returns a default value instead of `Option β`.
When the key is found in the association list, returns the associated value; otherwise
returns the fallback. -/

/-- Look up `key` in an association list of pairs `(key, value)`, returning the
associated value if found, or `fallback` if not. -/
def lookupDefault {α β : Type} [DecidableEq α] (key : α) (fallback : β) : List (α × β) → β
  | [] => fallback
  | (candidate, value) :: rest =>
      if key = candidate then value else lookupDefault key fallback rest

@[simp]
theorem lookupDefault_nil {α β : Type} [DecidableEq α] (key : α) (fallback : β) :
    lookupDefault key fallback [] = fallback := rfl

@[simp]
theorem lookupDefault_cons_hit {α β : Type} [DecidableEq α] (key : α) (value fallback : β)
    (rest : List (α × β)) :
    lookupDefault key fallback ((key, value) :: rest) = value := by
  simp [lookupDefault]

@[simp]
theorem lookupDefault_cons_miss {α β : Type} [DecidableEq α] (key candidate : α) (value fallback : β)
    (rest : List (α × β)) (h : key ≠ candidate) :
    lookupDefault key fallback ((candidate, value) :: rest) =
      lookupDefault key fallback rest := by
  simp [lookupDefault, h]

/-- A singleton list containing the target key: lookup returns the value. -/
@[simp]
theorem lookupDefault_singleton_hit {α β : Type} [DecidableEq α] (key : α) (fallback value : β) :
    lookupDefault key fallback [(key, value)] = value := by
  simp [lookupDefault]

/-- A singleton list NOT containing the target key: lookup returns the fallback. -/
theorem lookupDefault_singleton_miss {α β : Type} [DecidableEq α] {key candidate : α}
    (fallback value : β) (h : key ≠ candidate) :
    lookupDefault key fallback [(candidate, value)] = fallback := by
  simp [lookupDefault, h]

/-- `lookupDefault` is equivalent to `List.lookup` followed by `Option.getD`. -/
theorem lookupDefault_eq_getD {α β : Type} [DecidableEq α] (key : α) (fallback : β)
    (entries : List (α × β)) :
    lookupDefault key fallback entries = (entries.lookup key).getD fallback := by
  haveI : LawfulBEq α := inferInstanceAs (LawfulBEq α)
  induction' entries with p rest ih
  · rfl
  · rcases p with ⟨k, v⟩
    dsimp [lookupDefault, List.lookup]
    by_cases h : key = k
    · subst h; simp
    · have hbeq : (key == k) = false := by simp [h]
      simp [h, hbeq, ih]

/-- If `List.lookup` returns `some value` for a key, then `lookupDefault` also
returns that value (ignoring the fallback). -/
theorem lookupDefault_eq_of_lookup_eq_some {α β : Type} [DecidableEq α] {key : α} {value fallback : β}
    {entries : List (α × β)} (h : entries.lookup key = some value) :
    lookupDefault key fallback entries = value := by
  rw [lookupDefault_eq_getD, h]; rfl

/-- Lower bound for the result of a singleton `lookupDefault` when values are `Int`.
If both the fallback and the singleton's value are at least `lower`, then the
lookup result is also at least `lower`. -/
theorem lookupDefault_singleton_int_lower_bound {α : Type} [DecidableEq α]
    (lower fallback value : Int) (key candidate : α)
    (hfallback : lower ≤ fallback) (hvalue : lower ≤ value) :
    lower ≤ lookupDefault key fallback [(candidate, value)] := by
  by_cases h : key = candidate
  · simpa [lookupDefault, h] using hvalue
  · simpa [lookupDefault, h] using hfallback

/-! ## Key-value lookup with fallback function

A more general version of `lookupDefault` where the fallback is a function
of the key rather than a constant value. When the key is not found in the
association list, calls `fallback key` to produce the result. -/

/-- Look up `key` in an association list, calling `fallback key` if the key is
not found. Unlike `lookupDefault` which takes a constant fallback value,
`lookupOrElse` takes a fallback function, allowing the fallback to depend on
the key being searched for. -/
def lookupOrElse {α β : Type} [DecidableEq α] (fallback : α → β) : List (α × β) → α → β
  | [], key => fallback key
  | (entryKey, value) :: entries, key =>
      if key = entryKey then value else lookupOrElse fallback entries key

@[simp]
theorem lookupOrElse_nil {α β : Type} [DecidableEq α] (fallback : α → β) (key : α) :
    lookupOrElse fallback [] key = fallback key := rfl

@[simp]
theorem lookupOrElse_cons_eq {α β : Type} [DecidableEq α] {fallback : α → β}
    {entries : List (α × β)} {key : α} {value : β} :
    lookupOrElse fallback ((key, value) :: entries) key = value := by
  simp [lookupOrElse]

/-- `lookupOrElse` is equivalent to `List.lookup` followed by `Option.getD`
applied to `fallback key`. -/
theorem lookupOrElse_eq_getD {α β : Type} [DecidableEq α] (fallback : α → β)
    (entries : List (α × β)) (key : α) :
    lookupOrElse fallback entries key = (entries.lookup key).getD (fallback key) := by
  haveI : LawfulBEq α := inferInstanceAs (LawfulBEq α)
  induction' entries with p rest ih generalizing key
  · rfl
  · rcases p with ⟨k, v⟩
    dsimp [lookupOrElse, List.lookup]
    by_cases h : key = k
    · subst h; simp
    · have hbeq : (key == k) = false := by simp [h]
      simp [h, hbeq, ih]

/-- If `List.lookup` returns `some value` for a key, then `lookupOrElse` also
returns that value (ignoring the fallback function). -/
theorem lookupOrElse_eq_of_lookup_eq_some {α β : Type} [DecidableEq α] {fallback : α → β}
    {entries : List (α × β)} {key : α} {value : β}
    (h : entries.lookup key = some value) :
    lookupOrElse fallback entries key = value := by
  rw [lookupOrElse_eq_getD, h]; rfl

@[simp]
theorem lookupOrElse_cons_ne {α β : Type} [DecidableEq α] {fallback : α → β}
    {entries : List (α × β)} {query entryKey : α} {value : β}
    (h : query ≠ entryKey) :
    lookupOrElse fallback ((entryKey, value) :: entries) query =
      lookupOrElse fallback entries query := by
  simp [lookupOrElse, h]

end List

end Specific
