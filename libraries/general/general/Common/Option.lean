import Mathlib

/-!
# Option utilities

Generic utilities for working with `Option α`.
-/

namespace Option

variable {α : Type}

/-- If an `Option` value equals `none`, it cannot be expressed as `some a` for any `a`. -/
lemma eq_none_not_exists_some {x : Option α} (hx : x = none) : ¬ ∃ a : α, x = some a := by
  rintro ⟨a, ha⟩
  rw [hx] at ha
  exact Option.noConfusion ha

/-- Return the smaller of two optional values, using `Min` for the inner comparison. -/
def minOption [Min α] (o₁ o₂ : Option α) : Option α :=
  match o₁, o₂ with
  | none, _ => o₂
  | _, none => o₁
  | some a, some b => some (min a b)


lemma minOption_none_left [Min α] (o : Option α) : minOption none o = o := by
  simp [minOption]


lemma minOption_some_some [Min α] (a b : α) :
    minOption (some a) (some b) = some (min a b) := by
  simp [minOption]

/-- For any type with `BEq`, `LawfulBEq`, and `DecidableEq`,
`(o == some a)` is the same `Bool` as matching on `o` to check equality. -/
lemma beq_some_eq_match_decide {α : Type u} [BEq α] [LawfulBEq α] [DecidableEq α]
    (o : Option α) (a : α) :
    (o == some a) = (match o with | some a' => decide (a' = a) | none => false) := by
  cases o with
  | none => rfl
  | some val =>
    simp
    by_cases h : val = a
    · simp [h, beq_iff_eq]
    · simp [h, beq_iff_eq]

/--
  Convert an `Option Nat` to `Int`, using `-1` as the sentinel for `none`.
  This is a general-purpose combinator: any algorithm that searches for an index
  and returns `-1` on failure can use this mapping.
-/

def toIntDefault (o : Option Nat) : Int :=
  match o with
  | none => -1
  | some n => (n : Int)

/-! ### Case analysis for `Option.map` -/

/-- Case analysis on `Option.map f s`: either `s` is `none` and the result is `none`,
or `s` is `some a` and the result is `some (f a)`. Useful for verifying postconditions
that are stated as a disjunction over optional inputs. -/
theorem map_cases {α β : Type u} (f : α → β) (s : Option α) :
    (s = none ∧ Option.map f s = none) ∨ (∃ a : α, s = some a ∧ Option.map f s = some (f a)) := by
  cases s <;> simp

/-- Case analysis on `(o.map g).getD d`: either `o` is `none` and we get the default `d`,
or `o` is `some v` and we get `g v`. Useful for verifying postconditions expressed as a
disjunction over the result of a chained `map`/`getD` operation. -/
lemma map_getD_cases {α β : Type} (g : α → β) (d : β) (o : Option α) :
    (o = none ∧ (o.map g).getD d = d) ∨ (∃ v, o = some v ∧ (o.map g).getD d = g v) := by
  cases o <;> simp

/-! ### Matching vs `map`/`getD` -/

/-- Pattern-matching on an `Option` is equivalent to `Option.map` followed by `getD`.
This lemma allows rewriting explicit `match`-style processing into the more composable
`map`/`getD` form, which is useful when chaining `Option` transformations. -/
lemma match_eq_map_getD {α β : Type} (f : α → β) (d : β) (o : Option α) :
    (match o with | none => d | some x => f x) = (Option.map f o).getD d := by
  cases o <;> simp

/-! ### `BEq` bridges to propositional equality -/

/-- `(o == some t) = true` iff `o = some t`, under `LawfulBEq`.
This bridges `Bool`-valued `BEq` equality to propositional equality,
a common pattern when verifying postconditions that compare optional values. -/
lemma beq_some_iff [BEq α] [LawfulBEq α] (o : Option α) (t : α) :
    (o == some t) = true ↔ o = some t := by
  cases o <;> simp [beq_iff_eq]

/-! ### Arithmetic on optional naturals -/

/-- `(Option.map Nat.succ o).getD (n + 1) = Nat.succ (o.getD n)`.
This lemma simplifies the common pattern of mapping `Nat.succ` over an `Option Nat`
and then using `getD`. -/
lemma getD_map_succ (o : Option Nat) (n : Nat) :
    (Option.map Nat.succ o).getD (n + 1) = Nat.succ (o.getD n) := by
  cases o <;> simp

/-- `Option.map` commutes with `getD` when the mapped function fixes the default value.
For example, `(o.map (· * k)).getD 0 = (o.getD 0) * k` for `Int` with default `0`. -/

lemma getD_map_eq {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (o : Option α)
    (h : f default = default) : (o.map f).getD default = f (o.getD default) := by
  cases o <;> simp [h]

end Option

