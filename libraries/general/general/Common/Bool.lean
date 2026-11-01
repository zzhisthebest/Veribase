import Mathlib

namespace Bool

/-! ### Basic simplifications -/

/-- For any boolean `b`, `(b = true) = b`. This `@[simp]` lemma is useful for rewriting
    postconditions that test whether a `Bool`-valued result equals `true`. -/

lemma eq_true_eq_self (b : Bool) : (b = true) = b := by
  cases b <;> simp

/-- For any boolean `b`, `¬ (b = true) ↔ (!b) = true`.
This bridges the propositional negation of a boolean truth test to the boolean NOT operator.
Useful when converting between `¬ (p a = true)` and `(!p a) = true` in filter membership proofs. -/
lemma not_eq_true_iff (b : Bool) : ¬ (b = true) ↔ (!b) = true := by
  cases b <;> simp

/-- Two booleans `a` and `b` are equal iff their truth conditions are logically equivalent:
`(a = true) ↔ (b = true)`. This reduces boolean equality to logical equivalence,
useful when a postcondition expresses "the result is true iff some expected value is true." -/
lemma eq_iff_eq_true_iff (a b : Bool) : (a = true ↔ b = true) ↔ a = b := by
  cases a <;> cases b <;> simp

/-- For any two booleans `a` and `b`, if `(a && b)` is not true but `a` is true,
then `b` must be false. This captures the common pattern: in a conjunction that
is false, if the left-hand side is known to be true, the right-hand side must be false. -/
lemma eq_false_of_and_not_true_of_left_true {a b : Bool} (h_and : ¬ ((a && b) = true)) (ha : a = true) : b = false := by
  by_contra hb
  have hb' : b = true := Bool.eq_true_of_not_eq_false hb
  apply h_and
  simp [ha, hb']

/-- Boolean identity: `(b == true) = b` for any boolean `b`.
    Comparing a `Bool` with `true` via `==` gives back the `Bool` itself.
    This is the `BEq` version of `eq_true_eq_self`, useful for rewriting
    `BEq`-based postcondition checks to simple boolean values. -/

lemma beq_true_eq_self (b : Bool) : (b == true) = b := by
  cases b <;> simp

/-- For any boolean `b`, `((b == true) == b) = true`.
This captures the fact that `Bool` equality with `true` is idempotent under `==`.
This is a direct corollary of `beq_true_eq_self` and reflexivity of `==`, but it
matches the exact shape of common postcondition checks like
`(result == true) == expected`. -/
lemma beq_true_beq_self_eq_true (b : Bool) : ((b == true) == b) = true := by
  cases b <;> simp

/-- `(a && b && c) = true` is equivalent to `a = true ∧ b = true ∧ c = true`. -/
lemma and3_true_iff (a b c : Bool) : (a && b && c) = true ↔ a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp

/-- `(a || b || c) = true` is equivalent to `a = true ∨ b = true ∨ c = true`. -/
lemma or3_true_iff (a b c : Bool) : (a || b || c) = true ↔ (a = true ∨ b = true ∨ c = true) := by
  simp [or_assoc]

/-- If we know that `P` implies `b = true` and `¬ P` implies `b = false`,
then `(b = true) ↔ P`. This bridges boolean results and their propositional
counterparts, useful when a boolean decision procedure is known to be correct. -/
lemma eq_true_iff_of_cases {P : Prop} {b : Bool} (h_true : P → b = true)
    (h_false : ¬ P → b = false) : (b = true) ↔ P := by
  constructor
  · intro hb
    by_contra hn
    rw [h_false hn] at hb
    exact Bool.noConfusion hb
  · intro hP
    rw [h_true hP]

/-- Given `(b = true) ↔ P`, derive `(b = false) ↔ ¬ P`.
This factors the pattern that appears in many postconditions: if a boolean
result's true case is equivalent to a property `P`, its false case is
equivalent to the negation.
See also `Bool.eq_false_iff` for the basic equivalence `b = false ↔ b ≠ true`. -/
lemma eq_false_iff_not_of_eq_true_iff {b : Bool} {P : Prop} (h : (b = true) ↔ P) : (b = false) ↔ ¬ P := by
  constructor
  · intro hfalse hp
    have htrue : b = true := h.mpr hp
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · intro hnP
    have h_not_true : ¬ (b = true) := by
      intro htrue
      apply hnP
      exact h.mp htrue
    exact Bool.eq_false_of_not_eq_true h_not_true

/-- For any boolean `b`, `decide (b = true)` simplifies to `b`.
This is the `decide`-wrapped version of `eq_true_eq_self`, useful when a `Bool` result is
wrapped in a `decide` for comparison (e.g., postcondition checks like `decide (result = true)`). -/

lemma decide_eq_true_self (b : Bool) : decide (b = true) = b := by
  cases b <;> simp

/-- For any boolean `b`, `(decide (b = true) == b) = true`.
This combines `decide_eq_true_self` with `BEq` reflexivity, useful when a boolean postcondition
checks that a `decide`-wrapped result equals the original result via `==`. -/
lemma decide_beq_true_self (b : Bool) : (decide (b = true) == b) = true := by
  cases b <;> simp

/-- If a `Bool` proposition is false, the boolean equals `false`.
This bridges the `Prop`-level negation `¬ b` (using the `Bool → Prop` coercion)
to the `Bool`-level equality `b = false`. Useful when a hypothesis is `¬ b`
and you need to `simp` or substitute `b := false`. -/
lemma eq_false_of_not {b : Bool} (h : ¬ b) : b = false := by
  cases b
  · rfl
  · exfalso; exact h rfl

/-! ### `BEq` / `LawfulBEq` / `ReflBEq` lemmas -/

/-- For any type with a reflexive `BEq` instance, `(x == x) = true`.
    This is a named lemma for `ReflBEq.refl`, useful for `simp` rewrite chains.
    Unlike `beq_eq_true_iff_eq` which requires full `LawfulBEq`, this only needs `ReflBEq`. -/
theorem beq_refl_eq_true [BEq α] [ReflBEq α] (x : α) : (x == x) = true :=
  ReflBEq.refl (a := x)

/-- `(a == b) = true` is equivalent to `a = b` for any lawful `BEq` type. -/
lemma beq_eq_true_iff_eq [BEq α] [LawfulBEq α] {a b : α} : (a == b) = true ↔ a = b := by
  constructor
  · apply eq_of_beq
  · apply beq_of_eq

/-- If `b₁ = b₂`, then `(b₁ = true) ↔ (b₂ = true)`.
This is the forward direction of `eq_iff_eq_true_iff`: given boolean equality,
we can lift it to logical equivalence of the truth conditions.
Useful for rewriting in `↔` goals when two booleans are known to be equal. -/
lemma iff_eq_true_of_eq {b₁ b₂ : Bool} (h : b₁ = b₂) : (b₁ = true ↔ b₂ = true) := by
  subst h; rfl

/-! ### `decide` basic lemmas -/

/-- `decide (x = x)` is always `true`. This is a frequently-used `rw` lemma
for simplifying `decide` on reflexive equality. While `by simp` can also prove it,
having a named lemma is useful for rewriting in larger expressions. -/
theorem decide_self_eq_true {α : Type} [DecidableEq α] (x : α) : decide (x = x) = true := by
  simp

/-- If `a ≠ b`, then `decide (a = b) = false`. The companion to `decide_self_eq_true`
for the negative case. While `by simp [h]` can also prove it, having a named lemma
is useful for rewriting in larger expressions. -/
theorem decide_eq_false_of_ne {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) : decide (a = b) = false := by
  simp [h]

/-- `(a == b) = false` when `a ≠ b`, using `DecidableEq`.
This is the `BEq` counterpart of `decide_eq_false_of_ne`. -/
lemma beq_eq_false_of_ne {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) : (a == b) = false := by
  simp [h]

/-! ### `decide (a = b) = true` equivalence variants -/

/-- `decide (a = b) = true` is equivalent to `a = b`.
This is a direct specialization of `decide_eq_true_iff` for equality,
commonly used in palindrome checks and other `decide`-wrapped equality comparisons. -/
lemma decide_eq_true_iff_eq {α : Type u} [DecidableEq α] {a b : α} :
    (decide (a = b) = true) ↔ (a = b) := by
  simp

/-- `decide (a = b) = true` is equivalent to `b = a` (symmetric equality).
This is a convenient wrapper around `decide_eq_true_iff` combined with `eq_comm`.
Useful when a postcondition or lemma expects the symmetric form `b = a` rather than `a = b`. -/
lemma decide_eq_true_iff_eq_symm {α : Type u} [DecidableEq α] {a b : α} :
    (decide (a = b) = true) ↔ (b = a) := by
  simp [decide_eq_true, eq_comm]

/-- If `decide P` is `false`, then `¬ P`.
    This is the converse direction of `decide_eq_false_iff` specialized for
    rewriting `decide` results in minimality proofs. -/
lemma not_of_decide_eq_false {P : Prop} [Decidable P] (h : decide P = false) : ¬ P := by
  intro hp
  have h_true := decide_eq_true_iff.mpr hp
  rw [h] at h_true
  simp at h_true

/-- `decide (a = b)` equals `(a == b)` for any type with `DecidableEq` and `LawfulBEq`.
This bridges the propositional equality decision with the boolean equality `BEq`.
For example, `decide (3 = 5) = false` and `(3 == 5) = false`, while `decide (3 = 3) = true`
and `(3 == 3) = true`. -/
lemma decide_eq_beq {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    decide (a = b) = (a == b) := by
  by_cases h : a = b <;> simp [h]

/-! ### `decide` chains -/

/-- Chaining `decide` with `||` is equivalent to chaining the propositions with `∨`.
This is useful when a boolean decision procedure uses multiple `decide`s OR'd
together, and you need to convert to the propositional form for reasoning. -/
lemma decide_ors_iff {a b c : Prop} [Decidable a] [Decidable b] [Decidable c] :
    (decide a || decide b || decide c) = true ↔ (a ∨ b ∨ c) := by
  simp [or_assoc]

/-- If `b = false` and `(b = true) ↔ P`, then `¬ P`.
This is a convenience lemma derived from `eq_false_iff_not_of_eq_true_iff`. -/
lemma not_of_eq_false_of_eq_true_iff {b : Bool} {P : Prop} (hb : b = false) (hiff : (b = true) ↔ P) :
    ¬ P :=
  ((eq_false_iff_not_of_eq_true_iff hiff).mp hb)

/-! ### `decide` with `Bool` operations -/

/-- Convert a `decide`-wrapped decidable proposition combined with a `Bool`
via `&&` into an equivalent `Prop` conjunction.  Useful when a function
mixes `decide` with native `Bool` operations and the postcondition is
stated as a `Prop` conjunction. -/
lemma decide_and_bool_eq_true_iff {p : Prop} [Decidable p] {b : Bool} :
    (decide p && b = true) ↔ (p ∧ b = true) := by
  simp

/-- A three-way boolean conjunction where the third operand is a `decide`-wrapped proposition.
`(a && b && decide p) = true` iff all three hold: `a = true`, `b = true`, and `p`.
This generalizes `and3_true_iff` (which requires all three operands to be `Bool`)
by allowing the third operand to be a `decide`-wrapped proposition.
For example, `(s ≠ "" && isDigitString s && decide (s.length = 5)) = true`
is equivalent to `s ≠ "" ∧ isDigitString s = true ∧ s.length = 5`. -/
lemma andb_andb_decide_eq_true_iff {a b : Bool} {p : Prop} [Decidable p] :
    ((a && b && decide p) = true) ↔ (a = true ∧ b = true ∧ p) := by
  simp [and_assoc]

/-! ### `decide` with nested quantifiers -/

/-- Convert `decide (∀ i < m, ∀ j < n, P i j) = true` into the corresponding `∀` proposition.
Useful when a `Bool` postcondition on a 2D grid (or similar nested forall) needs to be
used for pointwise reasoning. This is a convenience wrapper around `of_decide_eq_true`. -/
lemma decide_forall₂_eq_true {m n : Nat} {P : Nat → Nat → Prop} [Decidable (∀ i, i < m → ∀ j, j < n → P i j)]
    (h : decide (∀ i, i < m → ∀ j, j < n → P i j) = true) :
    ∀ i, i < m → ∀ j, j < n → P i j :=
  of_decide_eq_true h

/-! ### `allTrue` — boolean AND over a `List Bool` -/

/-- `allTrue bs` is `true` iff every element of `bs` is `true`.
This is `List.foldl (· && ·) true bs`, i.e., Boolean AND over a list of booleans.
Equivalent to `List.all bs id`. -/
def allTrue (bs : List Bool) : Bool :=
  bs.foldl (· && ·) true

/-- Expanding `foldl` of `&&` by factoring out the initial accumulator:
`foldl (· && ·) b bs = b && foldl (· && ·) true bs`. -/
lemma foldl_and_eq (b : Bool) (bs : List Bool) :
    List.foldl (· && ·) b bs = (b && List.foldl (· && ·) true bs) := by
  induction bs generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, Bool.true_and, ih (b && x), ih x, Bool.and_assoc]

/-- `List.foldl (· && ·) a bs = true` iff `a = true` and every `b ∈ bs` is `true`. -/
lemma foldl_and_eq_true_iff (a : Bool) (bs : List Bool) :
    List.foldl (· && ·) a bs = true ↔ a = true ∧ ∀ b ∈ bs, b = true := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih (a && b), Bool.and_eq_true]
    have hmem : (∀ x, x ∈ (b :: bs) → x = true) ↔ (b = true ∧ ∀ x, x ∈ bs → x = true) := by
      simp
    rw [hmem]
    exact ⟨λ ⟨⟨ha, hb⟩, hall⟩ => ⟨ha, hb, hall⟩, λ ⟨ha, hb, hall⟩ => ⟨⟨ha, hb⟩, hall⟩⟩

/-- `allTrue (l.map f) = true` iff `f x = true` for every `x ∈ l`. -/
lemma allTrue_map_iff {α : Type} (f : α → Bool) (l : List α) :
    allTrue (l.map f) = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allTrue]
  | cons x xs ih =>
    rw [List.map_cons, allTrue, List.foldl_cons, Bool.true_and, foldl_and_eq_true_iff]
    simp [List.mem_map, List.mem_cons, forall_eq_or_imp]

/-! ### `List.all` ↔ `List.Forall` bridge -/

/-- If `f x = true ↔ P x` for all `x`, then `l.all f = true ↔ List.Forall P l`.
This bridges the boolean `List.all` combinator and the propositional `List.Forall`
predicate via a pointwise boolean-to-prop equivalence. Useful for converting between
`Bool`-valued and `Prop`-valued formulations of "every element satisfies a condition". -/
lemma all_eq_true_iff_forall {α : Type} {f : α → Bool} {P : α → Prop}
    (h : ∀ x, f x = true ↔ P x) (l : List α) : l.all f = true ↔ List.Forall P l := by
  rw [List.all_eq_true, List.forall_iff_forall_mem]
  constructor
  · intro hall x hx; exact (h x).mp (hall x hx)
  · intro hmem x hx; exact (h x).mpr (hmem x hx)

end Bool

/-! ### Conditional `Option` equality -/

/-- A conditional wrapping `some v` under a decidable condition `c`
equals `some x` iff `c` holds and `v = x`. -/
lemma cond_option_some_iff {α : Type} {c : Prop} [Decidable c] {v x : α} :
    ((if c then some v else none) = some x) ↔ (c ∧ v = x) := by
  by_cases h : c
  · simp [h]
  · simp [h]

/-- Eager evaluation of an `Option` via `casesOn` with `decide` and a `false` default
yields `true` iff the option contains a value satisfying the predicate.

This connects the boolean decision view (`Option.casesOn o false (λ a => decide (p a))`)
to the existential/propositional view (`∃ a, o = some a ∧ p a`). -/
lemma option_casesOn_decide_eq_true_iff_exists {α : Type u} (o : Option α) (p : α → Prop) [∀ a, Decidable (p a)] :
    (Option.casesOn o false (λ a => decide (p a)) = true) ↔ (∃ a, o = some a ∧ p a) := by
  cases o <;> simp

/-! ### `ite` with `decide` -/

/-- `(if _ : P then b else false) = true` iff `P ∧ b = true`.
This is the fundamental lemma for conditional boolean guards:
turns an `ite` with `false` in the else branch into a conjunction.
Useful for postcondition proofs of validation functions that branch
on a decidable proposition and return a `Bool`. -/
lemma ite_eq_true_iff {b : Bool} {P : Prop} [Decidable P] :
    (if _ : P then b else false) = true ↔ (P ∧ b = true) := by
  by_cases hP : P
  · simp [hP]
  · simp [hP]

/-- A boolean conditional with `decide`: `(if b then decide p else false) = true` iff `b ∧ p`.
This is useful when a `decide`-wrapped proposition is guarded by a boolean condition,
e.g., in postcondition verification of conditional checks. -/
lemma ite_decide_eq_true_iff {b : Prop} [Decidable b] {p : Prop} [Decidable p] :
    ((if b then decide p else false) = true) ↔ (b ∧ p) := by
  by_cases hb : b
  · simp [hb, decide_eq_true_iff]
  · simp [hb]

/-- `(if decide p then a else b) = (if p then a else b)`.
Bridges `ite` on `decide p` (a `Bool`) to `dite` on the proposition `p`.
Useful when a `Bool`-level conditional needs to be converted to the `Prop` level. -/
lemma ite_decide_eq_dite {p : Prop} [Decidable p] (a b : α) :
    (if decide p then a else b) = (if p then a else b) := by
  by_cases h : p
  · simp [h]
  · simp [h]

/-! ### Nested `ite` case analysis -/

/-- A conditional where the true branch is `false`: `(if c then false else b) = true` iff
    the condition `c` fails and `b` is `true`.
    This is the dual of `ite_eq_true_iff` — where `ite_eq_true_iff` covers the case
    `(if P then b else false)` (else branch is `false`), this covers the symmetric case
    `(if c then false else b)` (true branch is `false`). -/
lemma ite_false_eq_true_iff {c : Prop} [Decidable c] {b : Bool} :
    (if c then false else b) = true ↔ ¬ c ∧ b = true := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

/-- A nested if-then-else on two boolean predicates always equals one of its three branch values.
That is, `(if p x then a else if q x then b else c)` must equal `a`, `b`, or `c`, depending on
the boolean values of `p x` and `q x`. This is useful for case-analysis proofs where a
classification function (two boolean checks → three labels) returns one of three expected outputs.

For example, if `classifyByWordLists s` is defined as `if p s then "X" else if q s then "Y" else "Z"`,
then `ite_ite_eq_or_eq_or_eq p q "X" "Y" "Z" s` gives `classifyByWordLists s = "X" ∨ ... = "Y" ∨ ... = "Z"`. -/
lemma ite_ite_eq_or_eq_or_eq {α β : Type} (p q : α → Bool) (a b c : β) (x : α) :
    (if p x then a else if q x then b else c) = a ∨
    (if p x then a else if q x then b else c) = b ∨
    (if p x then a else if q x then b else c) = c := by
  by_cases hp : p x
  · simp [hp]
  · by_cases hq : q x
    · simp [hp, hq]
    · simp [hp, hq]

