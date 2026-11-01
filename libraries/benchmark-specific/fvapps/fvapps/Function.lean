namespace Specific

open _root_.List

/-! ## Propositional indicator function -/

/-- Returns `1` if the proposition `p` is true, `0` otherwise.
A `Nat`-valued indicator for decidable propositions. -/
def indicator (p : Prop) [Decidable p] : Nat :=
  if p then 1 else 0

@[simp]
theorem indicator_eq_zero_of_not {p : Prop} [Decidable p] (h : ¬ p) :
    indicator p = 0 := by
  simp [indicator, h]

@[simp]
theorem indicator_eq_one_of_true {p : Prop} [Decidable p] (h : p) :
    indicator p = 1 := by
  simp [indicator, h]

namespace Function

/-! ## Constant function combinators -/

universe u v w

/-- A one-argument constant function: ignores the input and returns `value`.
This is equivalent to `Function.const` but with the value placed first
for more convenient partial application. -/
def constantOn {α : Sort u} {β : Sort v} (value : β) (_ : α) : β :=
  value

@[simp]
theorem constantOn_apply {α : Sort u} {β : Sort v} (value : β) (a : α) :
    constantOn value a = value := by
  rfl

theorem constantOn_nat_nonnegative {α : Sort u} (value : Nat) (a : α) :
    constantOn value a ≥ 0 :=
  Nat.zero_le _

theorem constantOn_nat_le {α : Sort u} (value bound : Nat) (a : α) (h : value ≤ bound) :
    constantOn value a ≤ bound := by
  simpa [constantOn] using h

/-- A two-argument constant function that ignores both arguments
and returns the given `value`. -/
def const2 {α : Sort u} {β : Sort v} {γ : Sort w}
    (value : γ) (_ : α) (_ : β) : γ :=
  value

@[simp]
theorem const2_apply {α : Sort u} {β : Sort v} {γ : Sort w}
    (value : γ) (a : α) (b : β) :
    const2 value a b = value := by
  rfl

theorem const2_nat_nonnegative {α : Sort u} {β : Sort v}
    (value : Nat) (a : α) (b : β) :
    const2 value a b ≥ 0 :=
  Nat.zero_le _

theorem const2_nat_le {α : Sort u} {β : Sort v}
    (value bound : Nat) (a : α) (b : β) (h : value ≤ bound) :
    const2 value a b ≤ bound := by
  simpa [const2] using h

/-- If `value < upper`, then both `const2 value a b ≥ 0` and `const2 value a b < upper`. -/
theorem const2_nat_bounds {α : Sort u} {β : Sort v}
    {value upper : Nat} (a : α) (b : β) (h : value < upper) :
    const2 value a b ≥ 0 ∧ const2 value a b < upper := by
  have hl : const2 value a b ≥ 0 := const2_nat_nonnegative value a b
  have hu : const2 value a b < upper := by simpa [const2] using h
  exact ⟨hl, hu⟩

/-- If `0 < value < upper`, then both `const2 value a b > 0` and `const2 value a b < upper`. -/
theorem const2_nat_pos_bounds {α : Sort u} {β : Sort v}
    {value upper : Nat} (a : α) (b : β) (hpos : value > 0) (hupper : value < upper) :
    const2 value a b > 0 ∧ const2 value a b < upper := by
  have hp : const2 value a b > 0 := by simpa [const2] using hpos
  have hu : const2 value a b < upper := by simpa [const2] using hupper
  exact ⟨hp, hu⟩

/-- A three-argument constant function that ignores all arguments
and returns the given `value`. -/
def const3 {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (value : δ) (_ : α) (_ : β) (_ : γ) : δ :=
  value

@[simp]
theorem const3_apply {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (value : δ) (a : α) (b : β) (c : γ) :
    const3 value a b c = value :=
  rfl

universe s t

/-- A four-argument constant function that ignores all arguments
and returns the given `value`. -/
def const4 {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} {ε : Sort s}
    (value : ε) (_ : α) (_ : β) (_ : γ) (_ : δ) : ε :=
  value

@[simp]
theorem const4_apply {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} {ε : Sort s}
    (value : ε) (a : α) (b : β) (c : γ) (d : δ) :
    const4 value a b c d = value :=
  rfl

theorem const4_apply_eq_or {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} {ε : Sort s}
    (value other : ε) (a : α) (b : β) (c : γ) (d : δ) :
    const4 value a b c d = value ∨ const4 value a b c d = other :=
  Or.inl rfl

/-- For `Function.const` (single-argument constant function), if `value ≤ bound`
in `ℕ`, the result is also `≤ bound`. -/
theorem const_nat_le {α : Sort u} (value bound : Nat) (input : α) (h : value ≤ bound) :
    (Function.const α value) input ≤ bound := by
  simpa using h

/-! ## Equality predicate and indicator function -/

/-- Returns `true` iff `x` equals `target`. A `Bool`-valued equality predicate
useful as a filter/condition combinator. -/
def sameAs {α : Type u} [DecidableEq α] (target : α) (x : α) : Bool :=
  decide (x = target)

@[simp] theorem sameAs_self {α : Type u} [DecidableEq α] (a : α) :
    sameAs a a = true := by
  simp [sameAs]

theorem sameAs_ne {α : Type u} [DecidableEq α] {a b : α} (h : a ≠ b) :
    sameAs a b = false := by
  simp [sameAs, h.symm]

/-- Returns `1` if `x` equals `target`, `0` otherwise. A `Nat`-valued
indicator function for decidable equality. -/
def indicator {α : Type u} [DecidableEq α] (target : α) (x : α) : Nat :=
  if x = target then 1 else 0

@[simp] theorem indicator_self {α : Type u} [DecidableEq α] (a : α) :
    indicator a a = 1 := by
  simp [indicator]

theorem indicator_ne {α : Type u} [DecidableEq α] {a b : α} (h : a ≠ b) :
    indicator a b = 0 := by
  simp [indicator, h.symm]

/-! ## Overlap size under a measure -/

/-- The overlap size of two objects under a measure `f`. Returns `min (f x) (f y)`.
This is the theoretical upper bound on any shared substructure between `x` and `y`
when measured by `f`. For example, `overlapSize String.length s1 s2` is an upper
bound on the length of the longest common subsequence of two strings. -/
def overlapSize {α : Type} (f : α → Nat) (x y : α) : Nat :=
  min (f x) (f y)

/-- The overlap size is bounded above by both individual measurements. -/
theorem overlapSize_bounds {α : Type} (f : α → Nat) (x y : α) :
    overlapSize f x y ≤ f x ∧ overlapSize f x y ≤ f y :=
  ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

/-! ## Equality-based conditional -/

/-- Returns `same` if `x = y`, and `different` otherwise. A generic
equality-test combinator for decidable equality types. -/
def valueWhenEqual {α β : Type u} [DecidableEq α] (same different : β) (x y : α) : β :=
  if x = y then same else different

@[simp]
theorem valueWhenEqual_self {α β : Type u} [DecidableEq α] (same different : β) (x : α) :
    valueWhenEqual same different x x = same := by
  simp [valueWhenEqual]

end Function

end Specific
